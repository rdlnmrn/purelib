# Native artifact exporter

`NativeExport.lean` adapts leanprover/lean4export at
`05d43a2bc773b40ecfdebb32294192a5ef756951`; its Apache 2.0 license is retained
beside the source. It imports complete private artifacts with `loadExts := false`
and no plugins, selects safe source roots and registered global compiler rewrites,
and exports their complete proof dependencies as one shared expression graph.
Standalone environments with colliding declaration names require separate graphs.

The ordinary verification entrypoint is `scripts/check-nanoda.sh`; it builds the
selected sources before invoking this package. Build the native tool alone from
the repository root:

```sh
python3 -m scripts.nanoda.build_exporter
```

The command prints a verified executable path under `.lake/nanoda-tools`.
Its receipt binds the source, compiler, native archives and complete compiled
Lean dependencies. Lean's generated standalone C main initializes only the
runtime phase. The builder changes that one call to the public full module
initializer so this meta tool's own constants are initialized too. A changed
bootstrap shape fails explicitly. This initializes the tool's own dependencies;
it does not execute initializers or extension callbacks from export targets.

The executable accepts `--metadata` or `--export MODULE_MANIFEST ROOT_INVENTORY`.
The manifest contains one module name per line. The root inventory retains each
scanned module, first defining owner, declaration name and kernel phase. The
stream goes to stdout; import, root selection and serialization timings go to
stderr. Empty or repeated module inventories and unresolved or unsafe proof
dependencies fail explicitly. Partial declarations retain their complete bodies.

The producer is untrusted. `root_inventory.py` independently selects roots using
the authoritative artifact predicate; `export_cache.py` compares complete root
records and verifies their presence in the actual stream before publishing its
completion receipt. Reload checks compiled input bytes, module resolution and
all retained export bytes. Export completion establishes no checker success.
Private/server parts and required IR files are included in input bindings.
Group inventories use a stable node listing. Older input protocols can be reused
after exact comparison of every field except that listing order; selected roots,
each module's ordered imports, artifact paths and bytes must still agree.

This module is entirely meta, including its generated recursors, projections and
match functions. The normal audit uses the existing source-facing policy. Its
strict helper audit still reports Lean reflection dependencies on `propext`,
`Classical.choice` and `Quot.sound`; independent checking of emitted mathematical
proofs does not certify the producer's own helper closure. The obligation to
restore strict checking remains a separate audit obligation.

Run the real native import, complete-record comparison, private artifact,
standalone-owner and cache recovery tests with:

```sh
scripts/run-lake.sh env python3 -m unittest scripts.test.nanoda.test_native_export
```

The tests require the pinned nanoda executable under `.external/nanoda`, or
`NANODA_BIN`. They compile fixtures into an isolated temporary library. Target
initializers and persisted extension import callbacks are tested with markers;
export must leave both markers absent. The complete mathematical fixture passes
the real checker for both native and reference exports. Dirty private proofs
must be rejected without a success receipt.

The production package uses `pipeline`, `worker`, `planning`, `export_cache` and
`check_stream`. It stores build receipts in `nanoda-tools`, input bindings in
`nanoda-inputs`, complete streams in `nanoda-native`, checker receipts in
`nanoda-checked`, and aggregate checked requests in `nanoda-runs` under the cache
root. A zero-declaration checker result requires explicit independently validated
zero coverage, as for this entirely meta module; empty module requests fail.

Run all controls from the repository root with `scripts/run-lake.sh env python3
-m unittest discover -s scripts/test/nanoda`; the main-style cache controls also require explicit
`python3 -m scripts.test.nanoda.test_check_cache`, `test_input_key`, and
`test_graph_cache` invocations. Raw graph diagnostics use `export_graph` and
`graph`; the bounded comparison serializer is confined to tooling tests and is
not a production export fallback.
