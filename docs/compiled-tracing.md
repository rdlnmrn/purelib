# Compiled declaration tracing

`scripts/trace-axiom.sh [--axiom AXIOM] MODULE DECLARATION ...` reports closure
axioms, target-bearing immediate and type dependencies, and one shortest path.
`--use TARGET MODULE DECLARATION ...` reports every direct application in the
compiled type and body, including partial applications and repeated occurrences.
Arguments retain exact Expr Repr, clipped after 600 Unicode characters.

The implementation is the existing `project-module-data.py trace` host reader.
It checks the pinned compiled private, server, public and IR import inventory.
It retains imported precomputed axiom-extension entries, kernel constant kinds,
nominal names, dependency ordering and breadth-first path selection. It does not
execute module initialization, compiler callbacks or elaboration. Missing bodies,
unknown declarations, invalid artifacts and missing IR are explicit failures.

Types are now labeled `type (serialized Expr Repr)` and rendered from their exact
compiled Expr instead of the former contextual prettyprinter. This makes names,
binders, metadata and levels explicit; it is an intentional output format change.
Messages have no temporary Lean source position prelude. Declaration/target/body
errors retain their message, order, stdout stream and nonzero exit, with an
`error:` prefix; metadata-file errors are explicit host-reader failures. The former uncompiled
`#trace_axiom`/`#trace_use` command APIs and their raw-name variants are retired;
there are no active project command clients. Current source parser tests use isolated inputs.

Tracing is an observation tool. `check-axioms.sh` performs authoritative EMPTY
acceptance through its separately audited host backend, including compiled
private bodies and canonical controls. Trace output and stored extension entries
alone do not establish EMPTY acceptance, kernel type equivalence or nanoda
checking.

## Kernel type-change comparison

`scripts/project-module-data.py type-equivalence OLD_OLEAN NEW_OLEAN NAME...`
checks each old constant at the complete new compiled type. It uses the pinned
Lean 4.32.2 official kernel through a checked native adapter; structural type
equality is not the acceptance test. Old definitions, opaque declarations,
unsafe/partial filtering, complete inductive groups, quotient initialization and
private theorem headers retain the original replay behavior. New dependencies
are checked with their original safety and bodies. Errors and earlier successful
output keep the original argument order and bytes.

The adapter queries the actual checked environment, rewrites only the original
generated auxiliary names and discards each successful probe environment. Every
changed expression cache is compared with the original official factory. Native
errors use counted UTF8 transport, including embedded newlines.

Use `--toolchain PATH` to select the installed pinned toolchain,
`--kernel-cache PATH` to choose its content-addressed build cache and
`--receipt PATH` to retain the invocation binding. Otherwise receipts are written
under the kernel cache's `invocations` directory. The cache binds the actual
compiler, headers, source, linked libraries and regular native binary. Each
invocation binds selected public/server/private/IR parts and the complete actual
private import closure, then rechecks their bytes. Serialize writers against
these readers or supply immutable inputs; bindings do not permit concurrent
artifact replacement. There is no production timeout, heartbeat or RSS cap.

The former Lean helper and its archived source snapshot are retired. Current
regression controls compile isolated fixtures and exercise the native backend.


### Artifact-only declaration export

`scripts/check-nanoda.sh` uses the native
[artifact exporter](../scripts/nanoda/README.md). Complete private artifacts are
imported without target initializers, extension callbacks or plugins. Exact
scanned and defining owners, declaration names, universes, types, proof bodies,
opacity and mutual recursor groups are retained. Root selection and actual stream
coverage are validated independently through the pinned host artifact reader.
The exporter is untrusted; export completion establishes no checker success.

The complete raw compiled-record APIs remain available for contract comparison
and diagnostics. `python3 -m scripts.nanoda.graph_data` provides raw input-header
and declaration-graph queries. The old production host stream command is retired;
its bounded serializer is used only for complete-record comparison tests. Missing
or malformed artifacts fail explicitly; no alternate producer or placeholder
module data is a fallback.
