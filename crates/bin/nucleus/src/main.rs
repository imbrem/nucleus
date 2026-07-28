use std::{
    env,
    ffi::{OsStr, OsString},
    process::ExitCode,
};

use covalence_nucleus::Connection;

const USAGE: &str = "usage: nucleus [DATABASE]";

fn main() -> ExitCode {
    let path = match database_path(env::args_os().skip(1)) {
        Ok(path) => path,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        }
    };

    match open(path.as_deref()) {
        Ok(()) => {
            if let Some(path) = path {
                println!("opened Nucleus database {}", path.to_string_lossy());
            } else {
                println!("opened in-memory Nucleus database");
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("could not open Nucleus database: {error}");
            ExitCode::FAILURE
        }
    }
}

fn database_path(
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<Option<OsString>, String> {
    let mut arguments = arguments.into_iter();
    let path = arguments.next();
    if arguments.next().is_some() {
        return Err(String::from(USAGE));
    }
    Ok(path)
}

fn open(path: Option<&OsStr>) -> Result<(), covalence_nucleus::ConnectionError> {
    let _connection = match path {
        Some(path) => Connection::open(path)?,
        None => Connection::open_in_memory()?,
    };
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::{
        ffi::OsString,
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::{USAGE, database_path, open};

    #[test]
    fn defaults_to_an_in_memory_database() {
        let path = database_path([]).expect("parse empty arguments");
        assert_eq!(path, None);
        open(path.as_deref()).expect("open in-memory database");
    }

    #[test]
    fn opens_the_requested_database() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock follows Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!("nucleus-{unique}.sqlite3"));
        let parsed = database_path([path.clone().into_os_string()]).expect("parse path");

        open(parsed.as_deref()).expect("open file database");

        assert!(path.is_file());
        fs::remove_file(path).expect("remove temporary database");
    }

    #[test]
    fn rejects_more_than_one_database() {
        assert_eq!(
            database_path([OsString::from("one"), OsString::from("two")]),
            Err(String::from(USAGE))
        );
    }
}
