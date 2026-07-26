use std::io::{self, BufRead, IsTerminal, Write};

mod session;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let interactive = io::stdin().is_terminal();
    let mut session = session::Session::new()?;
    let stdin = io::stdin();
    let mut stdout = io::stdout().lock();
    let mut processed_command = false;

    if interactive {
        write!(stdout, "nucleus> ")?;
        stdout.flush()?;
    }
    for line in stdin.lock().lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        processed_command = true;
        match session.eval(&line) {
            Ok(output) => writeln!(stdout, "{output}")?,
            Err(error) => writeln!(stdout, "(error \"{error}\")")?,
        }
        if interactive {
            write!(stdout, "nucleus> ")?;
            stdout.flush()?;
        }
    }
    if !interactive && !processed_command {
        writeln!(
            stdout,
            "hello from nucleus: SQLite returned {}",
            covalence_nucleus::smoke()
        )?;
    }
    Ok(())
}
