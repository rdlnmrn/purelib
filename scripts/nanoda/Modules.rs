//! Check a shared export graph with the pinned kernel, scheduling by actual
//! compiled declaration owner. The kernel and normal worker stacks are unchanged.
use nanoda_lib::name::Name;
use nanoda_lib::util::Config;
use std::collections::{BTreeMap, HashMap};
use std::error::Error;
use std::io::BufRead;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::mpsc;
use std::time::{Duration, Instant};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 || args[1] != "--modules" {
        return Err("expected CONFIG --modules OWNERS".into());
    }
    let mut owners = HashMap::new();
    for row in std::io::BufReader::new(std::fs::File::open(&args[2])?).lines() {
        let row = row?;
        let (owner, name) = row.split_once('\t').ok_or("invalid owner record")?;
        if owner.is_empty() || name.is_empty() || owners.insert(name.to_owned(), owner.to_owned()).is_some() {
            return Err("empty or duplicate owner record".into());
        }
    }
    let config = Config::try_from(Path::new(&args[0]))?;
    if config.num_threads < 2 {
        return Err("module checking requires the normal parallel worker stacks (at least two threads)".into());
    }
    let mut pp_destination = config.get_pp_destination()?;
    let (export, skipped) = config.to_export_file()?;
    if !skipped.is_empty() {
        return Err("module checking cannot skip exported axioms".into());
    }
    let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, declaration) in export.declars.values().enumerate() {
        let key = export.with_ctx(|ctx| {
            let mut name = declaration.info().name;
            let mut parts = Vec::new();
            loop {
                match ctx.read_name(name) {
                    Name::Anon => break,
                    Name::Num(prefix, number, _) => {
                        parts.push(format!("n{number};"));
                        name = prefix;
                    }
                    Name::Str(prefix, text, _) => {
                        use std::fmt::Write;
                        let mut part = String::from("s");
                        for byte in ctx.read_string(text).as_bytes() {
                            write!(&mut part, "{byte:02x}").unwrap();
                        }
                        part.push(';');
                        parts.push(part);
                        name = prefix;
                    }
                }
            }
            parts.reverse();
            parts.concat()
        });
        let owner = owners.get(&key).ok_or_else(|| format!("exported declaration has no compiled owner: {key}"))?;
        groups.entry(owner.clone()).or_default().push(index);
    }
    // A watchdog is active only while checking one module. Parsing, owner
    // preparation and the aggregate run have no five-minute deadline.
    let (send, receive) = mpsc::channel::<bool>();
    let watchdog = std::thread::spawn(move || {
        let mut active = false;
        loop {
            let event = if active {
                receive.recv_timeout(Duration::from_secs(300))
            } else {
                receive.recv().map_err(|_| mpsc::RecvTimeoutError::Disconnected)
            };
            match event {
                Ok(value) => active = value,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    eprintln!("nanoda module exceeded 300s; terminating");
                    let pid = std::process::id().to_string();
                    let _ = std::process::Command::new("kill").args(["-TERM", &pid]).status();
                    std::thread::sleep(Duration::from_secs(15));
                    let _ = std::process::Command::new("kill").args(["-KILL", &pid]).status();
                    std::process::exit(124);
                }
            }
        }
    });
    let mut checked = 0;
    for (module, indices) in &groups {
        eprintln!("nanoda module start: {module} ({} declarations)", indices.len());
        send.send(true)?;
        let started = Instant::now();
        let next = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for worker in 0..export.config.num_threads {
                let export_ref = &export;
                let next_ref = &next;
                handles.push(std::thread::Builder::new().name(format!("thread_{worker}"))
                    .stack_size(16_777_216).spawn_scoped(scope, move || loop {
                        let offset = next_ref.fetch_add(1, Relaxed);
                        let Some(index) = indices.get(offset) else { break };
                        let (_, declaration) = export_ref.declars.get_index(*index).unwrap();
                        export_ref.check_declar(declaration);
                    }).expect("cannot start checker worker"));
            }
            for handle in handles {
                handle.join().expect("module checker worker failed");
            }
        });
        let elapsed = started.elapsed();
        send.send(false)?;
        println!("nanoda module\t{module}\t{}\t{}", elapsed.as_micros(), indices.len());
        if elapsed >= Duration::from_secs(30) {
            return Err(format!("nanoda module {module} took {:.3}s; profile and fix before integration into master", elapsed.as_secs_f64()).into());
        }
        checked += indices.len();
    }
    drop(send);
    watchdog.join().expect("module watchdog failed");
    if checked != export.declars.len() {
        return Err("module schedule did not check every declaration".into());
    }
    let errors = export.pp_selected_declars(pp_destination.as_mut());
    if !errors.is_empty() {
        return Err(format!("pretty printer errors: {errors:?}").into());
    }
    println!("Checked {checked} declarations with no errors");
    Ok(())
}
