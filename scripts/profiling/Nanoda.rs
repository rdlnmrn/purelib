//! Diagnostic driver for the pinned nanoda library. Serial mode records the
//! active declaration before checking. Parallel mode separates parser time from
//! checking with the same check_all_declars entry point as the stock CLI.
//! Individual parallel diagnosis mirrors the pinned worker scheduling and stacks.
//! Its output is deliberately not a production checker-success certificate.
use nanoda_lib::util::Config;
use std::error::Error;
use std::path::Path;
use std::time::Instant;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let path = args.next().ok_or("expected configuration path")?;
    let mode = match args.next().as_deref() {
        None => "serial",
        Some("--parallel") => "parallel",
        Some("--individual") => "individual",
        Some(_) => return Err("expected configuration path followed optionally by --parallel or --individual".into()),
    };
    if args.next().is_some() {
        return Err("unexpected additional arguments".into());
    }
    let config = Config::try_from(Path::new(&path))?;
    if config.num_threads > 1 && mode == "serial" {
        return Err("per-declaration diagnosis requires a serial configuration; use --parallel for phase timing".into());
    }
    if config.num_threads < 2 && mode == "individual" {
        return Err("--individual requires the normal parallel checker configuration".into());
    }
    let started = Instant::now();
    let (export, skipped) = config.to_export_file()?;
    if !skipped.is_empty() {
        return Err(format!("unpermitted exported axioms: {:?}", skipped).into());
    }
    eprintln!("nanoda profile: parse_ms={} declarations={}", started.elapsed().as_millis(), export.declars.len());
    let checking = Instant::now();
    if mode == "parallel" {
        export.check_all_declars();
        eprintln!("nanoda profile: complete declarations={} check_ms={}",
                  export.declars.len(), checking.elapsed().as_millis());
        return Ok(());
    }
    if mode == "individual" {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        let next = AtomicUsize::new(0);
        // Exact worker stack used by tc.rs at the pinned checker revision.
        // This does not alter the production checker or increase its limits.
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for worker in 0..export.config.num_threads {
                let export_ref = &export;
                let next_ref = &next;
                handles.push(std::thread::Builder::new().name(format!("profile_{worker}"))
                    .stack_size(16_777_216).spawn_scoped(scope, move || loop {
                        let index = next_ref.fetch_add(1, Relaxed);
                        let Some((_, declaration)) = export_ref.declars.get_index(index) else { break };
                        let name = export_ref.with_ctx(|ctx|
                            format!("{:?}", ctx.debug_print(declaration.info().name)));
                        eprintln!("nanoda profile: start {} {}", index, name);
                        let started = Instant::now();
                        export_ref.check_declar(declaration);
                        let elapsed = started.elapsed().as_millis();
                        if elapsed >= 100 {
                            eprintln!("nanoda profile: slow {} elapsed_ms={} {}", index, elapsed, name);
                        }
                    }).expect("cannot start diagnostic worker"));
            }
            for handle in handles {
                handle.join().expect("individual diagnostic worker failed");
            }
        });
        eprintln!("nanoda profile: complete declarations={} check_ms={}",
                  export.declars.len(), checking.elapsed().as_millis());
        return Ok(());
    }
    for (index, declaration) in export.declars.values().enumerate() {
        let name = export.with_ctx(|ctx| format!("{:?}", ctx.debug_print(declaration.info().name)));
        eprintln!("nanoda profile: start {} {}", index, name);
        let started = Instant::now();
        export.check_declar(declaration);
        eprintln!("nanoda profile: done {} elapsed_ms={}", index, started.elapsed().as_millis());
    }
    eprintln!("nanoda profile: complete declarations={} check_ms={}", export.declars.len(), checking.elapsed().as_millis());
    Ok(())
}
