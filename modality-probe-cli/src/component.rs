use crate::error::GracefulExit;
use serde::{Deserialize, Serialize};
use sha3::Sha3_256;
use std::hash::Hash;
use std::path::{Path, PathBuf};
use std::{fmt, fs, str};
use uuid::Uuid;

pub use sha3::Digest as ComponentHasherExt;

pub type ComponentHasher = Sha3_256;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct Component {
    pub name: String,
    pub id: ComponentUuid,
    #[serde(default, skip_serializing_if = "Option::is_none", with = "serde_hex")]
    pub code_hash: Option<ComponentHash>,
    #[serde(default, skip_serializing_if = "Option::is_none", with = "serde_hex")]
    pub instrumentation_hash: Option<ComponentHash>,
    #[serde(default)]
    pub tags: Vec<String>,
}

impl Component {
    pub fn component_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("Component.toml")
    }

    pub fn probes_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("probes.csv")
    }

    pub fn events_manifest_path<P: AsRef<Path>>(component_directory: P) -> PathBuf {
        component_directory.as_ref().join("events.csv")
    }

    pub fn from_toml<P: AsRef<Path>>(path: P) -> Self {
        let content =
            &fs::read_to_string(path).unwrap_or_exit("Can't open component manifest file");
        toml::from_str(content).unwrap_or_exit("Can't deserialize component")
    }

    pub fn write_toml<P: AsRef<Path>>(&self, path: P) {
        let content = toml::to_string(self).unwrap_or_exit("Can't serialize component");
        fs::write(path.as_ref(), &content).unwrap_or_exit("Can't create component manifest path");
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct ComponentUuid(pub Uuid);

impl ComponentUuid {
    pub fn new() -> Self {
        ComponentUuid(Uuid::new_v4())
    }

    pub fn nil() -> Self {
        ComponentUuid(Uuid::nil())
    }
}

impl Default for ComponentUuid {
    fn default() -> Self {
        ComponentUuid::nil()
    }
}

impl fmt::Display for ComponentUuid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// SHA3-256 hash
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Deserialize, Serialize)]
pub struct ComponentHash(pub [u8; 32]);

impl From<[u8; 32]> for ComponentHash {
    fn from(hash: [u8; 32]) -> Self {
        ComponentHash(hash)
    }
}

impl fmt::Display for ComponentHash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        hex::encode(&self.0).fmt(f)
    }
}

mod serde_hex {
    use super::ComponentHash;
    use serde::{de, Deserialize, Serialize};

    pub fn serialize<S>(value: &Option<ComponentHash>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if let Some(hash) = value {
            hex::encode(hash.0).serialize(serializer)
        } else {
            ().serialize(serializer)
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Option<ComponentHash>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s: Option<&str> = Deserialize::deserialize(deserializer)?;
        match s {
            Some(s) => {
                let mut out = [0u8; 32];
                hex::decode_to_slice(s, &mut out).map_err(de::Error::custom)?;
                Ok(Some(out.into()))
            }
            None => Ok(None),
        }
    }
}
