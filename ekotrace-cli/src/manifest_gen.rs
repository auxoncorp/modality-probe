use crate::events::{Event, EventId, Events};
use crate::tracers::{Tracer, TracerId, Tracers};
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
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use walkdir::WalkDir;

#[derive(Debug)]
pub struct Opt {
    pub event_id_offset: Option<u32>,
    pub tracer_id_offset: Option<u32>,
    pub file_extensions: Option<Vec<String>>,
    pub events_csv_file: PathBuf,
    pub tracers_csv_file: PathBuf,
    pub no_events: bool,
    pub no_tracers: bool,
    pub source_path: PathBuf,
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

pub fn run(opt: Opt) {
    opt.validate();

    // Read in existing CSVs if they exists
    let mut csv_events = Events::from_csv(&opt.events_csv_file);
    let mut csv_tracers = Tracers::from_csv(&opt.tracers_csv_file);

    // Check existing events and tracers
    csv_events.validate_nonzero_ids();
    csv_events.validate_unique_ids();
    csv_events.validate_unique_names();

    csv_tracers.validate_nonzero_ids();
    csv_tracers.validate_unique_ids();
    csv_tracers.validate_unique_names();

    // Collect event and tracer id identifiers in each source file
    let mut event_id_tokens = HashMap::new();
    let mut tracer_id_tokens = HashMap::new();
    let mut buffer = String::new();
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
            let mut f = File::open(entry.path()).expect("Can't open source path file");
            buffer.clear();

            // Skips binary/invalid data
            if f.read_to_string(&mut buffer).is_ok() {
                if !opt.no_events {
                    let event_tokens_in_file = find_event_identifiers(&buffer);
                    for token in &event_tokens_in_file {
                        let occurances = event_id_tokens.entry(token.clone()).or_insert(0);
                        *occurances += 1;
                    }
                }

                if !opt.no_tracers {
                    let tracer_tokens_in_file = find_tracer_identifiers(&buffer);
                    for token in &tracer_tokens_in_file {
                        let occurances = tracer_id_tokens.entry(token.clone()).or_insert(0);
                        *occurances += 1;
                    }
                }
            }
        }
    }

    // Generate event IDs for new events, with offset if provided
    let event_id_offset = opt.event_id_offset.unwrap_or(0);
    let mut next_available_event_id: u32 = match csv_events.next_available_event_id() {
        id if event_id_offset > id => event_id_offset,
        id @ _ => id,
    };

    // Add new events to the CSV data
    event_id_tokens.iter().for_each(|token| {
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

    // Generate tracer IDs for new tracers, with offset if provided
    let tracer_id_offset = opt.tracer_id_offset.unwrap_or(0);
    let mut next_available_tracer_id: u32 = match csv_tracers.next_available_tracer_id() {
        id if tracer_id_offset > id => tracer_id_offset,
        id @ _ => id,
    };

    // Add new tracers to the CSV data
    tracer_id_tokens.iter().for_each(|token| {
        if csv_tracers
            .0
            .iter()
            .find(|tracer| tracer.name == token.0.to_lowercase())
            .is_none()
        {
            csv_tracers.0.push(Tracer {
                id: TracerId(next_available_tracer_id),
                name: token.0.to_lowercase(),
                description: String::new(),
            });
            next_available_tracer_id += 1;
        }
    });

    // Write out the new events and tracers CSV files
    if !opt.no_events {
        csv_events.into_csv(&opt.events_csv_file);
    }

    if !opt.no_tracers {
        csv_tracers.into_csv(&opt.tracers_csv_file);
    }
}

fn find_event_identifiers(input: &str) -> Vec<String> {
    let mut events = vec![];
    let mut cursor = input;
    let min_len = "ekotrace_record_event".len();
    while cursor.len() > min_len {
        match parse_record_event_call_expression(cursor) {
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

fn find_tracer_identifiers(input: &str) -> Vec<String> {
    let mut tracers = vec![];
    let mut cursor = input;
    let min_len = "initialize_at".len();
    while cursor.len() > min_len {
        match parse_init_call_expression(cursor) {
            Ok((rem, token)) => {
                tracers.push(token);
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
    tracers
}

fn parse_record_event_call_expression(input: &str) -> IResult<&str, String> {
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

fn parse_init_call_expression(input: &str) -> IResult<&str, String> {
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
    let (input, _) = alt((
        tag("Ekotrace::try_initialize_at"),
        tag("Ekotrace::initialize_at"),
        tag("Ekotrace::new_with_storage"),
        tag("ekotrace_initialize"),
    ))(input)?;
    let (input, _) = opt(line_ending)(input)?;
    let (input, _) = multispace0(input)?;

    // Extract the function parameter(s)
    let (input, params) = delimited(char('('), is_not(")"), char(')'))(input)?;

    let mut param_exp = String::from(params).replace("\n", "").replace(" ", "");
    if param_exp.ends_with(',') {
        param_exp.pop();
    }

    let split_params: Vec<&str> = param_exp.split(',').collect();

    // Extract tracer ID from parameters, Rust has two, C/C++ has four
    let params = match split_params.len() {
        2 => {
            let (params, _) = take_till1(|c| c == ',')(params)?;
            let (params, _) = tag(",")(params)?;
            params
        }
        4 => {
            let (params, _) = take_till1(|c| c == ',')(params)?;
            let (params, _) = tag(",")(params)?;
            let (params, _) = take_till1(|c| c == ',')(params)?;
            let (params, _) = tag(",")(params)?;

            let (params, _) = multispace0(params)?;

            params
        }
        len @ _ => panic!(
            "Encountered ekotrace initialization method with an unexpected number of parameters ({})",
            len,
        ),
    };

    // With C++/Rust, possible namespace tokens up to right most "::"
    let (params, maybe_ns) = opt(take_until("::"))(params)?;
    let params = if maybe_ns.is_some() {
        let (params, _) = tag("::")(params)?;
        params
    } else {
        params
    };

    // Trim any remaining whitespace and ',' characters
    let split: Vec<&str> = params.split(',').collect();
    let token = String::from(split[0]).replace(",", "");
    let trimmed_token = token.trim();

    Ok((input, String::from(trimmed_token)))
}

#[cfg(test)]
mod tests {
    use super::*;

    const MIXED_EVENT_ID_INPUT: &'static str = r#"
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

    const MIXED_TRACER_ID_INPUT: &'static str = r#"
    let ekotrace_foo = Ekotrace::try_initialize_at(&mut storage_bytes, LOCATION_ID_FOO)?;

    // A comment
    let bar = Ekotrace::initialize_at(&mut storage_bytes, my_ids::LOCATION_ID_BAR)?;

    /* More comments
     * on more lines
     */
    let tracer = Ekotrace::new_with_storage(storage, LOCATION_ID_A).unwrap();

    /* C/C++ style */
    ekotrace_result result = ekotrace_initialize(
        destination,
        DEFAULT_TRACER_SIZE,
        DEFAULT_TRACER_ID,
        &t);

    // One line
    ekotrace_initialize(dest,TRACER_SIZE,MY_TRACER_ID,&t);
"#;

    #[test]
    fn event_identifiers_in_mixed_input() {
        let tokens = find_event_identifiers(MIXED_EVENT_ID_INPUT);
        assert_eq!(
            tokens,
            vec![
                "EVENT_A", "EVENT_A", "EVENT_B", "EVENT_C", "EVENT_C", "MY_EV_0", "MY_EV_1",
                "MY_EV_2", "EVENT0", "EVENT1",
            ]
        );
    }

    #[test]
    fn tracer_identifiers_in_mixed_input() {
        let tokens = find_tracer_identifiers(MIXED_TRACER_ID_INPUT);
        assert_eq!(
            tokens,
            vec![
                "LOCATION_ID_FOO",
                "LOCATION_ID_BAR",
                "LOCATION_ID_A",
                "DEFAULT_TRACER_ID",
                "MY_TRACER_ID",
            ]
        );
    }
}
