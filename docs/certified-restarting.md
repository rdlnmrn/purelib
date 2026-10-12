# Lessons learned: resumable certified restarting

These lessons come from the finite integration and period-observation replay
work. They describe requirements and observed failure modes, not a claim that
all period computations already support complete cold restart. In particular,
restart of a legacy numerical fixture does not certify restart of a different
canonical period construction.

## 1. A saved value is not yet a saved certified computation

Keep three claims separate:

1. **Numerical validity:** the decoded data satisfy the checked finite bounds.
2. **Artifact provenance:** the data have the expected format, input identity,
   source/dependency fingerprints and integrity checks.
3. **Mathematical ownership:** the reconstructed value is the value of the
   specified original constructor, or satisfies the precise comparison theorem
   required by the consumer.

Hashes and numerical agreement do not prove the third claim. Two cells can
have equal integrals while representing different integrands; two valid root
boxes can carry different root owners; two good period approximations can
integrate different cycles. The checkpoint regression rejecting replacement
of `1` by `2t` on `[0,1]` demonstrates why equality of integral values is too weak.

For exact execution replay, aim for a checked result of the form
`{ saved : Payload // saved = original inputs }`, or an equivalent structured
certificate with scalar ownership readbacks. For a mathematically equivalent
replacement algorithm, require its own proved comparison. Do not silently
substitute equivalence for equality of the original execution.

## 2. Design the loader with the producer

A trace or a large final JSON snapshot is not a restart mechanism. Before an
expensive stage runs, identify:

- its complete request and mathematical owners;
- the data that must survive a process exit;
- the finite checks that reconstruct its certificate;
- the first operation that can resume from those data;
- the generators that must never run again after a successful reload.

Implement that checked reload path before the long run. Save each expensive
result before proceeding to the next stage. Root proposals, selected depths,
rejected trials, prepared banks, centres, model coefficients, aggregate replies
and controller state can need separate checkpoints. Persisting only the last
observation loses preparation work if the run never reaches that observation.

Choose stage boundaries that are expensive enough to justify persistence and
small enough to finish and save before interruption. Repeated timeout-driven
runs that never cross a new durable boundary make no cumulative progress.

## 3. Preserve the actual construction choices

For these computations, ownership includes more than the polynomial and a
requested tolerance. Depending on the stage, retain and check:

- root enumeration, sheet labels, ambient boxes and clearance witnesses;
- the first accepted seed or depth, preceding rejected attempts and fallback;
- inherited root-refinement recipes and their original source histories;
- segment order, endpoints, stationary pieces and inter-cell bridges;
- the full prepared/centred state, its source allowance and refinement index;
- the differential, cycle, orientation, schedule, allocation policy and request;
- the control, ordered replies, emitted prefix and exact parser cursor.

An independently constructed valid state is not automatically the original
state. Replacing an inherited refinement procedure by a faster one requires a
proof; merely checking the new result's accuracy does not establish replay.
Stationary refinements also need the retained owner history. Equal endpoint
coordinates do not justify dropping the source's operational choices.

Prefer cached executable data together with defining equalities. A proposition
about a recomputed value is not a cache if consumers still rerun the calculation.

## 4. Reload must not secretly regenerate the source

A loader can look successful while forcing the original computation to rebuild
its request, recover a dependent owner, construct a control value or compare a
whole model. That defeats restarting even if the returned theorem is correct.

Keep expensive source construction lazy until its checkpoint is needed. Use
small retained request identities and checked local readbacks instead of
reconstructing a complete preparation to discover which checkpoint to open.
Derive control and aggregate evidence from restored samples where the existing
proofs permit it. Watch native initialization as well as explicit calls: merely
importing a module or constructing a closed client must not start a large run.

Checking saved arithmetic may still cost time. Distinguish validation work from
producer work and record both; “no producer reran” does not mean instantaneous
restart. Any acceleration of validation must preserve its actual obligations.

## 5. Treat the checkpoint store as a protocol

Write to a temporary file, complete and close the write, then atomically publish
it. Make dependencies available before publishing records that reference them.
A completion marker must not outrun the data needed to reconstruct completion.
Atomic rename alone is not a claim of power-loss durability; if that guarantee
is required, specify and test the additional storage protocol.

Reuse compatible artifacts across executable changes through a checked import
or migration. Validate the exact mathematical request, not just a directory
name. Separate identity changes that invalidate ownership from representation
changes that a proved decoder or migration can preserve.

Preserve older numerical-only receipts as historical evidence. If a later
loader reconstructs the missing source proof, write a new source-verified
receipt; do not copy a verification flag or rewrite history. Missing legacy
fields must be reported explicitly.

Sharing byte-equal immutable JSON records can reduce storage and write costs,
but byte identity is a storage fact. It does not replace decoding, mathematical
validation or the source-owner comparison. Referenced records must remain
available and immutable across restart and migration.

## 6. Return evidence for success and for unfinished attempts

A completed checkpoint should reconstruct certified success. Rejected data
should identify the failed equation or condition and retain the relevant
operands. An incomplete finite attempt should retain its budget, attempted
indices, available states, unresolved obligations and stopping reason.

A missing refinement-state loader is a limitation of that loader. A bounded
source attempt that misses is a fact about that attempt. Neither establishes
divergence, a pole, global non-certifiability or failure of the total theorem.
Do not convert an unsupported replay branch into a declined mathematical trial:
that can change which depth or fallback the original procedure selects.

Keep “saved-only replay” explicit. If required evidence is absent, stop with
that obstruction rather than silently generating it. Allow new work only in a
mode that distinguishes it from reuse and records the new durable stages.

## 7. Test cold restart by making regeneration fail

A warm in-memory cache is not a cold-restart test. Use separate processes and
small deterministic fixtures:

1. Establish an uninterrupted reference result and ownership contract.
2. Kill a run at a known write boundary, including intermediate stages before
   the final receipt exists.
3. Resume from disk and complete the same original computation.
4. Restart again in saved-only mode, with completed generators instrumented to
   fail if called. Verify that the saved stages are actually reused.
5. Check the output, allowance, ordered query trace, exact cursor and source
   certificate, not only the displayed bits.
6. Reject corrupt records, wrong-source substitutions, reordered or trailing
   replies, and missing referenced artifacts. Exercise partial writes and
   compatibility-checked import from an earlier executable.

Test successful first attempts and original fallbacks, including stationary
steps and nonuniform refinement. Record generated/reused counts and interruption
points beside the artifacts. A fixture proves that route works on that fixture;
only an actual-input run establishes acceptance for the large period client.

The observation controller may choose its next query adaptively. Do not replace
that trace by an easier hand-picked schedule and call it the original run.
Policy equivalence also need not mean identical output bits across policies.

## 8. Mathematical owner changes invalidate old acceptance claims

The corrected ordered standard periods and the former raw reference tours are
different owners. Likewise, the retained generated Legendre B connector is not
the standard B tour. Their checkpoints can remain valuable for testing replay,
but cannot be relabelled as standard-period acceptance evidence.

Reuse only the shared stages whose ownership remains proved, such as an
unchanged branch-isolation request. Keep raw-tour diagnostics separate from
corrected-period observations. Transporting larger checkpoints requires an
explicit comparison or a new loader for the corrected construction.

Keep the square-factor-normalized differential `dx/z` separate from the original
`dx/y`, and both separate from normalization of a period matrix. Similar names
must not obscure a change in the requested integral.

## 9. Engineering and acceptance discipline

Keep dependent interfaces compact with named type/proposition aliases and
small nonrecursive constructors. Preserve the certificates and cached data;
do not trade them away to improve elaboration. Check full artifact/code emission,
not just declaration checking, and use the repository profiling process for
slow changed modules. Never raise Lean's ordinary limits to conceal the problem.

Run bounded interruption regressions before another long execution. Reuse the
completed stages, fix the first missing restoration boundary, then continue.
Do not repeatedly restart the entire preparation to obtain a nicer log.

Report separately:

- theorem/proof and axiom-audit status;
- which reload paths are implemented;
- which interruption/corruption tests passed;
- which actual-input observations have complete source-verified receipts;
- remaining ownership or loader gaps and measured validation costs.

A successful build, an in-memory replay theorem, a numeric snapshot and an
end-to-end source-certified cold restart are four different achievements.

## References

- [Checkpoint reuse and bounded profiling](profiling.md#reuse-completed-work-not-just-logs).
- [Integration checkpoint implementation](../scripts/checkpoint/Integration.lean).
- [Root/refinement checkpoint implementation](../scripts/checkpoint/RootRefinement.lean).
- [Prepared bank checkpoint implementation](../scripts/checkpoint/PreparedBank.lean).
- [Observation and source-ownership regression harness](../Test/System/Checkpoint/Integration.lean).
- [Polynomial inverse interrupted-restart regression](../Test/LinearAlgebra/PolynomialMatrix/Checkpoint.lean): run `lake env lean --run Test/LinearAlgebra/PolynomialMatrix/Checkpoint.lean self-test FRESH_DIRECTORY`.
