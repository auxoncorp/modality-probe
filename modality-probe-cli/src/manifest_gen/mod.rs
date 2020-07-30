use crate::{
    component::{Component, ComponentHasher, ComponentHasherExt, ComponentUuid},
    error::GracefulExit,
    events::Events,
    exit_error,
    lang::Lang,
    probes::Probes,
};
use core::num::NonZeroU32;
use id_gen::{IdGen, NonZeroIdRange};
use invocations::{Config, Invocations};
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;
use structopt::StructOpt;

pub mod c_parser;
pub mod event_metadata;
pub mod file_path;
pub mod id_gen;
pub mod in_source_event;
pub mod in_source_probe;
pub mod invocations;
pub mod parser;
pub mod probe_metadata;
pub mod rust_parser;
pub mod source_location;
pub mod type_hint;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, StructOpt)]
pub struct ManifestGen {
    /// Language (C or Rust), if not specified then guess based on file extensions
    #[structopt(short, long, parse(try_from_str))]
    pub lang: Option<Lang>,

    /// Limit the source code searching to files with matching extensions
    #[structopt(long = "file-extension")]
    pub file_extensions: Option<Vec<String>>,

    /// Component name used when generating a component manifest
    #[structopt(long, default_value = "component")]
    pub component_name: String,

    /// Event ID offset, starts at 1 if not specified
    #[structopt(long)]
    pub event_id_offset: Option<u32>,

    /// Constrain the generated probe ID to an specific range.
    ///
    /// This can be either `<inclusive_start>..<exclusive_end>`
    /// or `<inclusive_start>..=<inclusive_end>`.
    ///
    /// The range values are unsigned 32-bit integers and must be non-zero.
    #[structopt(long, parse(try_from_str = NonZeroIdRange::from_str))]
    pub probe_id_range: Option<NonZeroIdRange>,

    /// Regenerate the component IDs instead of using existing IDs (if present)
    #[structopt(long)]
    pub regen_component_id: bool,

    /// Output path where component files are generated
    #[structopt(short = "-o", long, parse(from_os_str), default_value = "component")]
    pub output_path: PathBuf,

    /// Source code path to search
    #[structopt(parse(from_os_str))]
    pub source_path: PathBuf,
}

impl Default for ManifestGen {
    fn default() -> Self {
        ManifestGen {
            lang: None,
            file_extensions: None,
            component_name: String::from("component"),
            event_id_offset: None,
            probe_id_range: None,
            regen_component_id: false,
            output_path: PathBuf::from("component"),
            source_path: PathBuf::from("."),
        }
    }
}

impl ManifestGen {
    pub fn validate(&self) {
        if !self.source_path.exists() {
            exit_error!(
                "manifest-gen",
                "The source path '{}' does not exist",
                self.source_path.display()
            );
        }
    }
}

pub fn run(opt: ManifestGen) {
    opt.validate();

    // TODO - any reason to read in the component manifest?
    // seems like it can be a only-write thing
    let component_directory = opt.output_path;
    let component_manifest_path = Component::component_manifest_path(&component_directory);
    let probes_manifest_path = Component::probes_manifest_path(&component_directory);
    let events_manifest_path = Component::events_manifest_path(&component_directory);

    let mut probes = Probes::from_csv(&probes_manifest_path);
    let mut events = Events::from_csv(&events_manifest_path);

    probes.validate_ids();
    probes.validate_unique_ids();
    probes.validate_unique_names();

    events.validate_ids();
    events.validate_unique_ids();
    events.validate_unique_names();

    let config = Config {
        lang: opt.lang,
        file_extensions: opt.file_extensions,
        ..Default::default()
    };

    let invocations =
        Invocations::from_path(config, opt.source_path).unwrap_or_exit("manifest-gen");

    invocations.check_probes().unwrap_or_exit("manifest-gen");
    invocations.check_events().unwrap_or_exit("manifest-gen");

    let probe_id_range = opt.probe_id_range.unwrap_or_else(|| {
        NonZeroIdRange::new(
            NonZeroU32::new(1).unwrap(),
            NonZeroU32::new(modality_probe::ProbeId::MAX_ID)
                .unwrap_or_exit("Can't make a NonZeroU32 from ProbeId::MAX_ID"),
        )
        .unwrap_or_exit("Can't make a NonZeroIdRange from the given inclusive start and end values")
    });
    let probe_id_gen = IdGen::new(probe_id_range);

    invocations.merge_probes_into(probe_id_gen, &mut probes);
    invocations.merge_events_into(opt.event_id_offset, &mut events);

    let instrumentation_hash = {
        let mut hasher = ComponentHasher::new();
        for p in probes.iter() {
            p.instrumentation_hash(&mut hasher);
        }
        for e in events.iter() {
            e.instrumentation_hash(&mut hasher);
        }
        let hash_bytes: [u8; 32] = *(hasher.finalize().as_ref());
        hash_bytes.into()
    };

    let mut component_manifest = if component_manifest_path.exists() {
        let mut c = Component::from_toml(&component_manifest_path);
        c.code_hash = Some(invocations.code_hash());
        c.instrumentation_hash = Some(instrumentation_hash);
        c
    } else {
        Component {
            name: opt.component_name,
            id: ComponentUuid::new(),
            code_hash: Some(invocations.code_hash()),
            instrumentation_hash: Some(instrumentation_hash),
        }
    };

    if opt.regen_component_id {
        component_manifest.id = ComponentUuid::new();
    }

    for p in probes.iter_mut() {
        p.component_id = component_manifest.id;
    }
    for e in events.iter_mut() {
        e.component_id = component_manifest.id;
    }

    fs::create_dir_all(&component_directory).unwrap_or_exit("Can't create component directory");

    component_manifest.write_toml(&component_manifest_path);
    events.write_csv(&events_manifest_path);
    probes.write_csv(&probes_manifest_path);
}
