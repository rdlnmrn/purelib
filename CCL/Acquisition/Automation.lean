import CCL.Acquisition.Division
import CCL.Acquisition.Words

/-!
# First-pass automatic evidence selection

Construct an `AcquisitionAutomation.Expr` and compile it against annotated
or opaque atoms. Its constructors infer rational and square-root provenance
where supported, including cancellation of the same expression and squaring
the same certified root. `Expr.compile_channel` proves that the original
numerical process is unchanged. Unsupported operations forget provenance,
not numerical data.

`Division.start` and `Division.acquire` choose cached, symbolic, optional
candidate-gap, or numerical evidence in that order. Their typed report
distinguishes a quotient, operational zero, branch zero, and smallness.
`Words.start` and `Words.acquire` choose a cached all-row provider, supplied
separation, inferred nonreal rational provenance, or signed acquisition.
Both signs prepare whole words; near-boundary evidence remains inconclusive.

Reports retain state and evidence for `resume`. Successful word reports are
the existing separated-word reports, with braid invariance, reversal, and the
arbitrary closed-path dual period law. `Words.continueFrom` additionally
starts at the folded output using the cached final provider.

This is a supported finite front end, not automatic reification of arbitrary
Lean functions or a universal equality/termination decision procedure.
Callers still supply opaque evaluators, requested positive tolerances, and
any domain-specific gap not derived by the supported constructors. Numerical
small/near outcomes never invent the missing exact separation assumptions.
-/
