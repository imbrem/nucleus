use std::io::{self, BufRead, IsTerminal, Write};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let interactive = io::stdin().is_terminal();
    let mut session = covalence_nucleus::ReplSession::new()?;
    let stdin = io::stdin();
    let mut stdout = io::stdout().lock();

    if interactive {
        write!(stdout, "nucleus> ")?;
        stdout.flush()?;
    }
    for line in stdin.lock().lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        match session.eval(&line) {
            Ok(output) => writeln!(stdout, "{output}")?,
            Err(error) => writeln!(stdout, "(error \"{error}\")")?,
        }
        if interactive {
            write!(stdout, "nucleus> ")?;
            stdout.flush()?;
        }
    }
    Ok(())
}
