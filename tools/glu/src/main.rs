mod artifact;
mod buck;
mod cargo;
mod loc;
mod runner;

use std::{env, path::PathBuf, process::ExitCode};

use clap::{Parser, Subcommand};
use color_eyre::eyre::{Result, WrapErr};

use runner::Runner;

#[derive(Debug, Parser)]
#[command(version, about = "Nucleus repository tasks", propagate_version = true)]
struct Cli {
    /// Show commands; repeat to stream successful command output.
    #[arg(short, long, action = clap::ArgAction::Count, global = true)]
    verbose: u8,

    #[command(subcommand)]
    command: Task,
}

#[derive(Debug, Subcommand)]
enum Task {
    /// Check that required development tools are available.
    Doctor,
    /// Format the repository.
    Fmt,
    /// Run Rust and TypeScript linters.
    Lint,
    /// Run the test suites.
    Test {
        /// Run the tests inside the development container.
        #[arg(long)]
        container: bool,

        /// Also verify the Cargo-native test workflow.
        #[arg(long)]
        cargo: bool,
    },
    /// Build an artifact and all of its prerequisites.
    Build {
        /// Artifact to build; defaults to everything.
        #[arg(value_enum, default_value_t = BuildTarget::All)]
        target: BuildTarget,
    },
    /// Run local validation.
    Check,
    /// Run the complete CI validation.
    Ci,
    /// Validate Cargo dependency policy.
    Deps,
    /// Maintain and inspect the generated Buck2 build.
    Buck {
        #[command(subcommand)]
        command: BuckTask,
    },
    /// Build the Lean developments under `lean/`.
    ///
    /// These are a specification, not a build input, so this is deliberately
    /// separate: `glu build`, `glu check`, and `glu ci` never touch them. It
    /// shells out to `lake` rather than going through Buck.
    Lean {
        /// List the developments that would be built, without building.
        #[arg(long)]
        list: bool,

        /// Build without first fetching Mathlib's prebuilt artifacts.
        ///
        /// On a cold checkout this compiles Mathlib from source, which takes
        /// hours.
        #[arg(long)]
        no_cache: bool,

        /// Generate API documentation rather than just checking the sources.
        ///
        /// Collects doc-gen4's HTML tree and its `SQLite` database for every
        /// development that has a `docbuild` companion project.
        #[arg(long)]
        docs: bool,

        /// Directory to stage generated documentation into.
        #[arg(long, default_value = "lean-docs")]
        out: PathBuf,

        /// Cap Lake's build parallelism.
        ///
        /// Documentation generation holds an elaborated environment per
        /// worker, so peak memory scales with this. Lowering it is the way out
        /// of allocation failures on small machines.
        ///
        /// Lake has no parallelism flag of its own; it schedules on Lean's
        /// task pool, so this sets `LEAN_NUM_THREADS`.
        #[arg(long)]
        jobs: Option<u16>,
    },
    /// Report source line counts.
    Loc,
    /// Show the project status headline.
    Status,
    /// Build and serve the browser demo, with a kernel behind it.
    ///
    /// Builds both wasm modules, starts an HTTP kernel holding a database,
    /// prints its address, and serves the page. Ctrl-C stops everything.
    Demo {
        /// Databases the HTTP kernel should serve.
        ///
        /// Defaults to the committed fixture, so the demo works unattended.
        files: Vec<PathBuf>,

        /// Loopback port for the demo page.
        #[arg(long, default_value_t = 8000)]
        port: u16,

        /// Loopback port for the HTTP kernel.
        ///
        /// The page defaults to this, so changing it means changing the URL
        /// on the page too.
        #[arg(long, default_value_t = 8080)]
        kernel_port: u16,

        /// Open the demo in the default browser.
        #[arg(long)]
        open: bool,

        /// Serve what is already built rather than rebuilding first.
        #[arg(long)]
        no_build: bool,
    },
    /// Build or serve the documentation site.
    Docs {
        #[command(subcommand)]
        command: Option<DocsTask>,
    },
    /// Internal Buck action protocol; not a stable developer-facing interface.
    #[command(hide = true)]
    Artifact {
        #[command(subcommand)]
        command: ArtifactTask,
    },
}

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
enum BuildTarget {
    All,
    Native,
    Wasm,
    Component,
    Docs,
}

#[derive(Debug, Subcommand)]
enum BuckTask {
    /// Configure machine-local Buck tool paths.
    Configure,
    /// Regenerate committed Cargo-derived Buck files.
    Sync,
    /// Check that generated Buck files match Cargo metadata.
    Check,
}

#[derive(Debug, Subcommand)]
enum DocsTask {
    /// Build and serve the generated site locally.
    Serve {
        /// Open the preview in the default browser.
        #[arg(long)]
        open: bool,

        /// Loopback port to listen on.
        #[arg(long, default_value_t = 4173)]
        port: u16,
    },
}

/// Implementations of Buck actions.
///
/// These commands are invoked by checked-in `BUCK` rules. Developers should
/// use `glu build`, `glu test`, or `glu docs` instead.
#[derive(Debug, Subcommand)]
enum ArtifactTask {
    /// Internal: generate repository line-count metadata.
    Loc {
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: generate production Rustdoc.
    Rustdoc {
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: build the browser Wasm package.
    Wasm {
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: build the Nucleus WIT component.
    Component {
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: transpile the Nucleus WIT component to JavaScript.
    ComponentJs {
        #[arg(long)]
        component: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: build the WASI CLI component.
    CliComponent {
        #[arg(long)]
        out: PathBuf,
    },
    /// Internal: assemble the generated documentation site.
    Docs {
        #[arg(long)]
        production_crates: PathBuf,
        #[arg(long)]
        production_dependencies: PathBuf,
        #[arg(long)]
        loc: PathBuf,
        #[arg(long)]
        rustdoc: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
}

fn find_root() -> Result<PathBuf> {
    let mut directory = env::current_dir().wrap_err("could not read the current directory")?;
    loop {
        if directory.join("tools/glu/Cargo.toml").is_file()
            && directory.join("Cargo.toml").is_file()
        {
            return Ok(directory);
        }
        if !directory.pop() {
            color_eyre::eyre::bail!("not inside the Nucleus repository");
        }
    }
}

fn run() -> Result<()> {
    let cli = Cli::parse();
    let runner = Runner::new(find_root()?, cli.verbose);

    match cli.command {
        Task::Doctor => runner.doctor(),
        Task::Fmt => runner.fmt(false),
        Task::Lint => runner.lint(),
        Task::Test { container, cargo } => runner.test(container, cargo),
        Task::Build { target } => runner.build(target),
        Task::Check => runner.check(),
        Task::Ci => runner.ci(),
        Task::Deps => runner.deps_check(),
        Task::Buck {
            command: BuckTask::Configure,
        } => runner.buck_configure(),
        Task::Buck {
            command: BuckTask::Sync,
        } => runner.buck_sync(),
        Task::Buck {
            command: BuckTask::Check,
        } => runner.buck_check(),
        Task::Demo {
            files,
            port,
            kernel_port,
            open,
            no_build,
        } => runner.demo(&files, port, kernel_port, open, no_build),
        Task::Docs { command: None } => runner.docs(),
        Task::Docs {
            command: Some(DocsTask::Serve { open, port }),
        } => {
            runner.docs()?;
            runner.serve_docs(port, open)
        }
        Task::Artifact { command } => match command {
            ArtifactTask::Loc { out } => runner.artifact_loc(&out),
            ArtifactTask::Rustdoc { out } => runner.artifact_rustdoc(&out),
            ArtifactTask::Wasm { out } => runner.artifact_wasm(&out),
            ArtifactTask::Component { out } => runner.artifact_component(&out),
            ArtifactTask::ComponentJs { component, out } => {
                runner.artifact_component_js(&component, &out)
            }
            ArtifactTask::CliComponent { out } => runner.artifact_cli_component(&out),
            ArtifactTask::Docs {
                production_crates,
                production_dependencies,
                loc,
                rustdoc,
                out,
            } => runner.artifact_docs(
                [
                    (&production_crates, "crates.json"),
                    (&production_dependencies, "dependencies.json"),
                ],
                &loc,
                &rustdoc,
                &out,
            ),
        },
        Task::Lean {
            list,
            no_cache,
            docs,
            out,
            jobs,
        } => {
            if docs {
                runner.lean_docs(&out, !no_cache, jobs)
            } else {
                runner.lean(list, !no_cache, jobs)
            }
        }
        Task::Loc => runner.loc(),
        Task::Status => runner.status(),
    }
}

fn main() -> ExitCode {
    if let Err(error) = color_eyre::install() {
        eprintln!("error: could not install error reporter: {error}");
        return ExitCode::FAILURE;
    }

    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error:?}");
            ExitCode::FAILURE
        }
    }
}
