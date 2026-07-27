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
