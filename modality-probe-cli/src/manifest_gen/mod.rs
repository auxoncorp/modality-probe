use crate::{
    component::{Component, ComponentHasher, ComponentHasherExt, ComponentUuId},
    error::GracefulExit,
    events::Events,
    exit_error,
    lang::Lang,
    probes::Probes,
};
use invocations::{Config, Invocations};
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

pub mod c_parser;
pub mod event_metadata;
pub mod file_path;
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

    /// Event ID offset
    #[structopt(long)]
    pub event_id_offset: Option<u32>,

    /// Probe ID offset
    #[structopt(long)]
    pub probe_id_offset: Option<u32>,

    /// Limit the source code searching to files with matching extensions
    #[structopt(long = "file-extension")]
    pub file_extensions: Option<Vec<String>>,

    /// Component name used when generating a component manifest and
    /// containing directory
    #[structopt(long, default_value = "component")]
    pub component_name: String,

    /// Output path where component, event and probe manifests are generated
    #[structopt(short = "-o", long, parse(from_os_str), default_value = "component")]
    pub output_path: PathBuf,

    /// Regenerate the component UUID instead of using an existing one (if present)
    #[structopt(long)]
    pub regen_component_uuid: bool,

    /// Source code path to search
    #[structopt(parse(from_os_str))]
    pub source_path: PathBuf,
}

impl Default for ManifestGen {
    fn default() -> Self {
        ManifestGen {
            lang: None,
            event_id_offset: None,
            probe_id_offset: None,
            file_extensions: None,
            component_name: String::from("component"),
            output_path: PathBuf::from("."),
            regen_component_uuid: false,
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

    let component_manifest_dir = opt.output_path;
    let component_manifest_path = component_manifest_dir.join("Component.toml");
    let probes_manifest_path = component_manifest_dir.join("probes.csv");
    let events_manifest_path = component_manifest_dir.join("events.csv");

    let mut probes_manifest = Probes::from_csv(&probes_manifest_path);
    let mut events_manifest = Events::from_csv(&events_manifest_path);

    probes_manifest.validate_ids();
    probes_manifest.validate_unique_ids();
    probes_manifest.validate_unique_names();

    events_manifest.validate_ids();
    events_manifest.validate_unique_ids();
    events_manifest.validate_unique_names();

    let config = Config {
        lang: opt.lang,
        file_extensions: opt.file_extensions,
        ..Default::default()
    };

    let invocations =
        Invocations::from_path(config, opt.source_path).unwrap_or_exit("manifest-gen");

    invocations.check_probes().unwrap_or_exit("manifest-gen");
    invocations.check_events().unwrap_or_exit("manifest-gen");

    invocations.merge_probes_into(opt.probe_id_offset, &mut probes_manifest);
    invocations.merge_events_into(opt.event_id_offset, &mut events_manifest);

    let instrumentation_hash = {
        let mut hasher = ComponentHasher::new();
        for p in probes_manifest.probes.iter() {
            p.instrumentation_hash(&mut hasher);
        }
        for e in events_manifest.events.iter() {
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
            uuid: ComponentUuId::new(),
            code_hash: Some(invocations.code_hash()),
            instrumentation_hash: Some(instrumentation_hash),
        }
    };

    if opt.regen_component_uuid {
        component_manifest.uuid = ComponentUuId::new();
    }

    for p in probes_manifest.probes.iter_mut() {
        p.uuid = component_manifest.uuid;
    }
    for e in events_manifest.events.iter_mut() {
        e.uuid = component_manifest.uuid;
    }

    fs::create_dir_all(&component_manifest_dir)
        .unwrap_or_exit("Can't create component manifest path");

    component_manifest.write_toml(&component_manifest_path);
    events_manifest.write_csv(&events_manifest_path);
    probes_manifest.write_csv(&probes_manifest_path);
}
