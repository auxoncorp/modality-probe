use crate::events::{Event, EventId, Events};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take, take_till1, take_until},
    character::complete::{char, line_ending, multispace0},
    combinator::opt,
    sequence::delimited,
    IResult,
};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;
use walkdir::WalkDir;

mod events;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "ekotrace-event-manifest-gen",
    about = "Generate event id manifest file from tracer event recording invocations."
)]
pub struct Opt {
    /// Event ID offset
    #[structopt(long)]
    event_id_offset: Option<u32>,

    /// Limit the source code searching to files with matching extensions
    #[structopt(long = "file-extension")]
    file_extensions: Option<Vec<String>>,

    /// Event ID manifest CSV file
    #[structopt(short = "o", long, parse(from_os_str), default_value = "events.csv")]
    events_csv_file: PathBuf,

    /// Source code path to search
    #[structopt(parse(from_os_str))]
    source_path: PathBuf,
}

impl Opt {
    pub fn validate(&self) {
        assert!(
            self.source_path.exists(),
            "Source path \"{}\" does not exist",
            self.source_path.display()
        );
    }
}

fn main() {
    let opt = Opt::from_args();
    opt.validate();

    // Read in existing events CSV if one exists
    let mut csv_events = Events::from_csv(&opt.events_csv_file);

    // Check existing events
    csv_events.validate_nonzero_ids();
    csv_events.validate_unique_ids();
    csv_events.validate_unique_names();

    // Collect event names and occurances of tacing call expressions
    // in each source file
    let mut event_tokens = HashMap::new();
    for entry in WalkDir::new(&opt.source_path)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| !e.file_type().is_dir())
    {
        // Filter by file extensions, if provided
        if opt.file_extensions.as_ref().map_or(true, |exts| {
            exts.iter()
                .find(|&ext| Some(OsStr::new(ext)) == entry.path().extension())
                .is_some()
        }) {
            // Skips binary/invalid data
            if let Ok(input) = fs::read_to_string(entry.path()) {
                let tokens_in_file = find_event_identifiers(&input);
                for token in &tokens_in_file {
                    let occurances = event_tokens.entry(token.clone()).or_insert(0);
                    *occurances += 1;
                }
            }
        }
    }

    // Generate event IDs for new events, with offset if provided
    let event_id_offset = opt.event_id_offset.unwrap_or(0);
    let mut next_available_event_id: u32 = match csv_events.next_available_event_id() {
        id @ _ if event_id_offset > id => event_id_offset,
        id @ _ => id,
    };

    // Add new events to the CSV data
    event_tokens.iter().for_each(|token| {
        if csv_events
            .0
            .iter()
            .find(|event| event.name == token.0.to_lowercase())
            .is_none()
        {
            csv_events.0.push(Event {
                id: EventId(next_available_event_id),
                name: token.0.to_lowercase(),
                description: String::new(),
            });
            next_available_event_id += 1;
        }
    });

    // Write out the new events CSV
    csv_events.into_csv(&opt.events_csv_file);
}

fn find_event_identifiers(input: &str) -> Vec<String> {
    let mut events = vec![];
    let mut cursor = input;
    let min_len = "ekotrace_record_event".len();
    while cursor.len() > min_len {
        match parse_call_expression(cursor) {
            Ok((rem, token)) => {
                events.push(token);
                cursor = rem;
            }
            Err(e) => match e {
                nom::Err::Incomplete(_) => break,
                nom::Err::Error((rem, _)) => {
                    let res: IResult<&str, &str> = take(1usize)(rem);
                    if let Ok((rem, _)) = res {
                        cursor = rem;
                    } else {
                        break;
                    }
                }
                nom::Err::Failure(_) => break,
            },
        }
    }
    events
}

fn parse_call_expression(input: &str) -> IResult<&str, String> {
    // Eat C/C++/Rust single line comments
    let (input, maybe_comment) = opt(alt((tag("///"), tag("//"))))(input)?;
    let input = if maybe_comment.is_some() {
        let (input, _) = take_till1(|c| c == '\n')(input)?;
        input
    } else {
        input
    };

    // Eat C/C++/Rust multi-line comments
    let (input, maybe_comment) = opt(tag("/*"))(input)?;
    let input = if maybe_comment.is_some() {
        let (input, _) = take_until("*/")(input)?;
        input
    } else {
        input
    };

    // Find symbol name, extract parameters
    let (input, _) = alt((tag("ekotrace_record_event"), tag("record_event")))(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;

    // Extract the function parameter(s)
    let (input, params) = delimited(char('('), is_not(")"), char(')'))(input)?;

    let mut param_exp = String::from(params).replace("\n", "").replace(" ", "");
    if param_exp.ends_with(',') {
        param_exp.pop();
    }

    let split_params: Vec<&str> = param_exp.split(',').collect();

    // Eat the first tracer pointer parameter if present
    // C/C++ style has two parameters, Rust has one
    let params = if split_params.len() != 1 {
        let (params, _) = take_till1(|c| c == ',')(params)?;
        let (params, _) = tag(",")(params)?;
        params
    } else {
        params
    };

    // With C++/Rust, possible namespace tokens up to right most "::"
    let (params, maybe_ns) = opt(take_until("::"))(params)?;
    let params = if maybe_ns.is_some() {
        let (params, _) = tag("::")(params)?;
        params
    } else {
        params
    };

    // Trim any remaining whitespace and ',' characters (Rust)
    let token = String::from(params).replace(",", "");
    let trimmed_token = token.trim();

    Ok((input, String::from(trimmed_token)))
}

#[cfg(test)]
mod tests {
    use super::*;

    const MIXED_INPUT: &'static str = r#"
    // A comment
    // ekotrace_record_event is a function
    // ekotrace_record_event(my_tracer, COMMENTED_EVENT);
    result = ekotrace_record_event(
            t,
            EVENT_A);

    /* A comment */
    /* ekotrace_record_event() is a function */
    result = ekotrace_record_event(
            t,
            EVENT_A
            );

    /* A comment
     * here
     * and there*/
    result = ekotrace_record_event(  t  ,   EVENT_B  );

    // Comments
    /* More comments
     * ekotrace_record_event(my_tracer, COMMENTED_EVENT);
     * */
    result = ekotrace_record_event(t,EVENT_C);

    /* More comments */
    result = ekotrace_record_event
    (
    t
    ,
    EVENT_C);

    // Rusty
    super::ekotrace_record_event(tracer, events::MY_EV_0);

    /******** More Rust ******/
    /// ekotrace_record_event(my_tracer, COMMENTED_EVENT);
    super::ekotrace_record_event(
        tracer,
        events::MY_EV_1,
    ),

    super::duper:ekotrace_record_event(
        my::tracer,
        events::MY_EV_2,
    ),

    // Rust library usage
    tracer.record_event(events::EVENT0);

    /// More Rust
    /// tracer.record_event(events::R_COMMENTED_EVENT);
    tracer.try_record_event(EVENT1).unwrap();
"#;

    #[test]
    fn identifiers_in_mixed_input() {
        let tokens = find_event_identifiers(MIXED_INPUT);
        assert_eq!(
            tokens,
            vec![
                "EVENT_A", "EVENT_A", "EVENT_B", "EVENT_C", "EVENT_C", "MY_EV_0", "MY_EV_1",
                "MY_EV_2", "EVENT0", "EVENT1",
            ]
        );
    }
}
