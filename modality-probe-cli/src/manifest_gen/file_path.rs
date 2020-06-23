use std::path::{Path, PathBuf};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    NotRegularFile(PathBuf),
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct FilePath {
    pub full_path: String,
    pub path: String,
}

impl FilePath {
    pub fn from_path_file<P: AsRef<Path>>(search_path: P, file: P) -> Result<FilePath, Error> {
        let search_path = search_path.as_ref();
        let file = file.as_ref();

        if file == search_path {
            // Can't resolve past the file name
            Ok(FilePath {
                full_path: file
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
                path: file
                    .file_name()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
            })
        } else if file.starts_with(search_path) {
            let mut path = PathBuf::new();
            if let Some(p) = search_path.iter().last() {
                path.push(p)
            }
            let mut sp_iter = search_path.iter();
            for c in file.iter() {
                let sp_c = sp_iter.next();
                if Some(c) != sp_c {
                    path.push(c);
                }
            }
            let path: PathBuf = if path.has_root() {
                path.iter().skip(1).collect()
            } else {
                path
            };

            Ok(FilePath {
                full_path: file
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
                path: path
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
            })
        } else {
            // Default to file name
            Ok(FilePath {
                full_path: file
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
                path: file
                    .file_name()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_str()
                    .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                    .to_string(),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn sane_file_paths() {
        assert_eq!(
            FilePath::from_path_file("/path/proj/src/main.c", "/path/proj/src/main.c"),
            Ok(FilePath {
                full_path: "/path/proj/src/main.c".to_string(),
                path: "main.c".to_string()
            })
        );
        assert_eq!(
            FilePath::from_path_file("/path/proj/", "/path/proj/src/main.c"),
            Ok(FilePath {
                full_path: "/path/proj/src/main.c".to_string(),
                path: if cfg!(target_os = "windows") {
                    "proj\\src\\main.c".to_string()
                } else {
                    "proj/src/main.c".to_string()
                }
            })
        );
        assert_eq!(
            FilePath::from_path_file("/path/to/my/proj/", "/path/to/my/proj/src/main.c"),
            Ok(FilePath {
                full_path: "/path/to/my/proj/src/main.c".to_string(),
                path: if cfg!(target_os = "windows") {
                    "proj\\src\\main.c".to_string()
                } else {
                    "proj/src/main.c".to_string()
                }
            })
        );
        assert_eq!(
            FilePath::from_path_file("proj/", "proj/src/main.c"),
            Ok(FilePath {
                full_path: "proj/src/main.c".to_string(),
                path: if cfg!(target_os = "windows") {
                    "proj\\src\\main.c".to_string()
                } else {
                    "proj/src/main.c".to_string()
                }
            })
        );
        assert_eq!(
            FilePath::from_path_file("./proj/", "./proj/src/main.c"),
            Ok(FilePath {
                full_path: "./proj/src/main.c".to_string(),
                path: if cfg!(target_os = "windows") {
                    "proj\\src\\main.c".to_string()
                } else {
                    "proj/src/main.c".to_string()
                }
            })
        );
        assert_eq!(
            FilePath::from_path_file("/", "/proj/src/main.c"),
            Ok(FilePath {
                full_path: "/proj/src/main.c".to_string(),
                path: if cfg!(target_os = "windows") {
                    "proj\\src\\main.c".to_string()
                } else {
                    "proj/src/main.c".to_string()
                }
            })
        );
    }
}
