use std::path::{Path, PathBuf};

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Error {
    NotRegularFile(PathBuf),
}

pub struct FilePath;

impl FilePath {
    pub fn resolve<P: AsRef<Path>>(search_path: P, file: P) -> Result<String, Error> {
        let search_path = search_path.as_ref();
        let file = file.as_ref();

        if file == search_path {
            // Can't resolve past the file name
            Ok(file
                .file_name()
                .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                .to_str()
                .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                .to_string())
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
            Ok(path
                .to_str()
                .ok_or_else(|| Error::NotRegularFile(path.clone()))?
                .to_string())
        } else {
            // Default to file name
            Ok(file
                .file_name()
                .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                .to_str()
                .ok_or_else(|| Error::NotRegularFile(file.to_path_buf()))?
                .to_string())
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
            FilePath::resolve("/path/proj/src/main.c", "/path/proj/src/main.c"),
            Ok("main.c".to_string())
        );
        assert_eq!(
            FilePath::resolve("/path/proj/", "/path/proj/src/main.c"),
            Ok("proj/src/main.c".to_string())
        );
        assert_eq!(
            FilePath::resolve("/path/to/my/proj/", "/path/to/my/proj/src/main.c"),
            Ok("proj/src/main.c".to_string())
        );
        assert_eq!(
            FilePath::resolve("proj/", "proj/src/main.c"),
            Ok("proj/src/main.c".to_string())
        );
        assert_eq!(
            FilePath::resolve("./proj/", "./proj/src/main.c"),
            Ok("proj/src/main.c".to_string())
        );
        assert_eq!(
            FilePath::resolve("/", "/proj/src/main.c"),
            Ok("proj/src/main.c".to_string())
        );
    }
}
