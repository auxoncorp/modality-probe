use crate::{
    component::{Component, ComponentHasher, ComponentHasherExt, ComponentUuid},
    component_dir::ComponentDir,
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

    /// Regenerate the component UUIDs instead of using existing UUIDs (if present)
    #[structopt(long)]
    pub regen_component_uuid: bool,

    /// Output path where component directories are generated
    #[structopt(short = "-o", long, parse(from_os_str), default_value = "components")]
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
            event_id_offset: None,
            probe_id_range: None,
            regen_component_uuid: false,
            output_path: PathBuf::from("."),
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

    let components_path = opt.output_path;
    let mut components = ComponentDir::collect_from_path(&components_path);

    for component in components.iter() {
        component.probes.validate_ids();
        component.probes.validate_unique_ids();
        component.probes.validate_unique_names();

        component.events.validate_ids();
        component.events.validate_unique_ids();
        component.events.validate_unique_names();
    }

    let config = Config {
        lang: opt.lang,
        file_extensions: opt.file_extensions,
        ..Default::default()
    };

    let invocations =
        Invocations::from_path(config, opt.source_path).unwrap_or_exit("manifest-gen");

    invocations.check_probes().unwrap_or_exit("manifest-gen");
    invocations.check_events().unwrap_or_exit("manifest-gen");

    let parsed_component_names = invocations.component_names();

    for comp_name in parsed_component_names.iter() {
        let is_present = components
            .iter()
            .any(|c| c.component.name == comp_name.as_str());
        if !is_present {
            let comp_dir = components_path.join(comp_name);
            components.push(ComponentDir {
                directory: comp_dir.to_path_buf(),
                component: Component {
                    name: comp_name.to_string(),
                    uuid: ComponentUuid::nil(),
                    code_hash: None,
                    instrumentation_hash: None,
                },
                probes: Probes::from_csv(ComponentDir::probes_manifest_path(&comp_dir)),
                events: Events::from_csv(ComponentDir::events_manifest_path(&comp_dir)),
            });
        }
    }

    let probe_id_range = opt.probe_id_range.unwrap_or_else(|| {
        NonZeroIdRange::new(
            NonZeroU32::new(1).unwrap(),
            NonZeroU32::new(modality_probe::ProbeId::MAX_ID)
                .unwrap_or_exit("Can't make a NonZeroU32 from ProbeId::MAX_ID"),
        )
        .unwrap_or_exit("Can't make a NonZeroIdRange from the given inclusive start and end values")
    });
    let mut probe_id_gen = IdGen::new(probe_id_range);
    invocations.merge_components_into(opt.event_id_offset, &mut probe_id_gen, &mut components);

    for comp in components.iter_mut() {
        let instrumentation_hash = {
            let mut hasher = ComponentHasher::new();
            for p in comp.probes.probes.iter() {
                p.instrumentation_hash(&mut hasher);
            }
            for e in comp.events.events.iter() {
                e.instrumentation_hash(&mut hasher);
            }
            let hash_bytes: [u8; 32] = *(hasher.finalize().as_ref());
            hash_bytes.into()
        };

        comp.component.code_hash = Some(invocations.code_hash());
        comp.component.instrumentation_hash = Some(instrumentation_hash);

        let component_manifest_path = ComponentDir::component_manifest_path(&comp.directory);

        let needs_uuid = opt.regen_component_uuid
            || comp.component.uuid == ComponentUuid::nil()
            || !component_manifest_path.exists();

        if needs_uuid {
            comp.component.uuid = ComponentUuid::new();
        }

        for p in comp.probes.probes.iter_mut() {
            p.uuid = comp.component.uuid;
        }
        for e in comp.events.events.iter_mut() {
            e.uuid = comp.component.uuid;
        }

        fs::create_dir_all(&comp.directory).unwrap_or_exit("Can't create component directory");

        comp.write_manifest_files();
    }
}
