//! Command-line interface.

macro_rules! unwrap_command {
    ($global:expr, $type:path) => {
        if let $type(local) = $global.cmd {
            local
        } else {
            panic!("Invalid command {:?}", $global.cmd)
        }
    };
}

mod test;

use clap::{CommandFactory, Parser};
use clap_complete::Shell;

/// Run the CLI.
pub async fn run() -> Result<(), anyhow::Error> {
    let opts = GlobalOpts::parse();

    match &opts.cmd {
        SubCommand::Test(_) => test::run(opts).await?,
        SubCommand::GenCompletions(local) => {
            gen_completions(local.shell);
        }
    }

    Ok(())
}

/// Atmosphere build utility.
#[derive(Debug, Parser)]
struct GlobalOpts {
    #[clap(subcommand)]
    cmd: SubCommand,
}

#[derive(Debug, Parser)]
enum SubCommand {
    Test(test::Opts),

    #[clap(hide = true)]
    GenCompletions(GenCompletions),
}

#[derive(Debug, Parser)]
struct GenCompletions {
    #[clap(index = 1)]
    shell: Shell,
}

fn gen_completions(shell: Shell) {
    clap_complete::generate(
        shell,
        &mut GlobalOpts::command(),
        "atmo",
        &mut std::io::stdout(),
    )
}
