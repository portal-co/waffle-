//! WAFFLE command-line tool.

use anyhow::Result;
use log::debug;
use std::path::PathBuf;
use structopt::StructOpt;
use waffle::InterpContext;
use waffle::{entity::EntityRef, FrontendOptions, Func, Module, OptOptions};

#[derive(Debug, StructOpt)]
#[structopt(name = "waffle-util", about = "WAFFLE utility.")]
struct Options {
    #[structopt(short, long)]
    debug: bool,

    #[structopt(
        help = "Do basic optimizations: GVN and const-prop",
        long = "basic-opts"
    )]
    basic_opts: bool,

    #[structopt(
        help = "Enable parsing of debug-info from input",
        short = "g",
        long = "debug-info"
    )]
    debug_info: bool,

    #[structopt(help = "Transform to maximal SSA", long = "max-ssa")]
    max_ssa: bool,

    #[structopt(subcommand)]
    command: Command,
}

#[derive(Debug, StructOpt)]
enum Command {
    #[structopt(name = "print-ir", about = "Parse Wasm and print resulting IR")]
    PrintIR {
        #[structopt(help = "Wasm file to parse")]
        wasm: PathBuf,
    },
    #[structopt(name = "print-func", about = "Parse Wasm and print one function body")]
    PrintFunc {
        #[structopt(help = "Wasm file to parse")]
        wasm: PathBuf,
        #[structopt(help = "Index of Wasm function to print")]
        func: usize,
    },
    #[structopt(name = "roundtrip", about = "Round-trip Wasm through IR")]
    RoundTrip {
        #[structopt(help = "Wasm file to parse", short = "i")]
        input: PathBuf,
        #[structopt(help = "Wasm file to produce", short = "o")]
        output: PathBuf,
    },
    #[structopt(name = "interp", about = "Interpret Waffle IR from Wasm")]
    Interp {
        #[structopt(help = "Wasm file to parse", short = "i")]
        input: PathBuf,
    },
}

fn apply_options(opts: &Options, module: &mut Module) -> Result<()> {
    module.expand_all_funcs()?;
    if opts.basic_opts {
        module.per_func_body(|body| body.optimize(&OptOptions::default()));
    }
    if opts.max_ssa {
        module.per_func_body(|body| body.convert_to_max_ssa(None));
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Options::from_args();

    let mut logger = env_logger::Builder::from_default_env();
    if opts.debug {
        logger.filter_level(log::LevelFilter::Debug);
    }
    let _ = logger.try_init();

    let mut options = FrontendOptions::default();
    options.debug = opts.debug_info;

    match &opts.command {
        Command::PrintIR { wasm } => {
            let bytes = std::fs::read(wasm)?;
            debug!("Loaded {} bytes of Wasm data", bytes.len());
            let mut module = Module::from_wasm_bytes(&bytes[..], &options)?;
            apply_options(&opts, &mut module)?;
            println!("{}", module.display());
        }
        Command::PrintFunc { wasm, func } => {
            let bytes = std::fs::read(wasm)?;
            debug!("Loaded {} bytes of Wasm data", bytes.len());
            let mut module = Module::from_wasm_bytes(&bytes[..], &options)?;
            apply_options(&opts, &mut module)?;
            println!(
                "{}",
                module.funcs[Func::new(*func)]
                    .body()
                    .unwrap()
                    .display_verbose("", Some(&module))
            );
        }
        Command::RoundTrip { input, output } => {
            let bytes = std::fs::read(input)?;
            debug!("Loaded {} bytes of Wasm data", bytes.len());
            let mut module = Module::from_wasm_bytes(&bytes[..], &options)?;
            apply_options(&opts, &mut module)?;
            let produced = module.to_wasm_bytes()?;
            std::fs::write(output, &produced[..])?;
        }
        Command::Interp { input } => {
            let bytes = std::fs::read(input)?;
            debug!("Loaded {} bytes of Wasm data", bytes.len());
            let mut module = Module::from_wasm_bytes(&bytes[..], &options)?;
            apply_options(&opts, &mut module)?;
            // Ensure all functions are expanded -- this is necessary
            // for interpretation.
            module.expand_all_funcs()?;
            let mut ctx = InterpContext::new(&module)?;
            debug!("Calling start function");
            if let Some(start) = module.start_func {
                ctx.call(&mut module, start, &[]).ok().unwrap();
            }
            // Find a function called `_start`, if any.
            if let Some(waffle::Export {
                kind: waffle::ExportKind::Func(func),
                ..
            }) = module.exports.iter().find(|e| &e.name == "_start")
            {
                debug!("Calling _start");
                let func = *func;
                ctx.call(&mut module, func, &[]).ok().unwrap();
            }
        }
    }

    Ok(())
}
