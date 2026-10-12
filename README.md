# Finite constructive mathematics in Lean

This repository develops mathematics from finite, displayed, executable data.
Its basic objects are rational coefficients, finite lists and matrices, rational
boxes, bounded searches, finite paths and words, and proof-bearing refinement
states. A calculation may be refined as far as a caller asks, but the library
does not turn that open-ended protocol into a completed real or complex number.

The active Lean code uses neither `classical` nor `noncomputable`. It avoids
choice, completed infinite carriers, compactness, infinite series, and hidden
enumerations of all roots or field elements. The authoritative axiom audit
requires empty transitive axiom closures for its selected declarations. Full
validation includes retained proof dependencies, configured project scripts and
the independent nanoda check. Independent compiler-helper coverage is temporarily
optional; strict `--all-helpers` coverage remains a separate audit obligation.

Constructor injectivity and logical normalization certificates use direct
implications or equivalences (`↔`) rather than equalities between propositions.
These changes preserve the finite data, executable operations, and mathematical
claims while removing reliance on propositional extensionality.

The project began with a finite Fundamental Theorem of Algebra and complex
continued logarithms, but now also contains substantial developments in exact
approximation, finite measure theory, algebraic geometry, rational
trigonometry, rotations, monodromy, periods, and combinatorial knot theory.

Version 1.0.0 establishes the public Lean modules and declarations as the library's
compatibility contract for the pinned toolchain. Future incompatible public API
changes require a major version; compatible additions use a minor version, and
compatible fixes use a patch version. Private proof implementations and internal
tooling may evolve while preserving those public contracts.

## Why this work exists

The aim is to develop the arithmetic and analysis needed for applied
mathematics without requiring a belief in completed real or complex numbers.
We want the useful substance of “real-number arithmetic”: calculation,
refinement, algebraic laws, integration, roots, and quantitative estimates.
We want to develop this arithmetic without assuming completed infinite sets,
without inheriting the resulting distinction between computable and
noncomputable “real numbers”, and without relying on existence claims that
supply no construction.
Our starting point is what can actually be supplied and checked: finite
rational data, executable procedures, and proofs of what their outputs mean.
An instruction to produce more digits is a usable mathematical object; it
does not require treating the entire digit stream as an already existing thing.

Consider the familiar law `exp(x) * exp(y) = exp(x + y)`. An engineer needs to
know when this replacement is justified in a calculation, and how accurately
to evaluate it. Here the law can be expressed through finite requests: given
suitable input data and any positive rational error tolerance, compute finite
approximations to both expressions with a proved bound on their discrepancy.
The proof supplies a procedure that works for every such request; it is not
an observation that two numerical answers happened to agree in some tests.
Neither exponential has to be supplied as a completed infinite expansion.
When inputs themselves have uncertainty, their enclosures and the resulting
error must also be accounted for: requesting more computational precision
does not remove uncertainty in a measurement.

The broader ambition is to provide this kind of underpinning throughout
applied mathematics. A result should tell its caller what finite information
is required, what can be calculated from it, and what accuracy or other
guarantee the answer carries. This repository is a growing contribution to
that programme, not a claim that all of applied mathematics has already been
covered. The formal constructions also do not automatically certify an
unrelated floating-point implementation or a physical model.

A second aim is to recover results whose usual presentations invoke real
numbers or infinities, by finding the finite constructive arguments that
deliver their useful conclusions. A polynomial root is supplied operationally
as a certified refinement procedure returning rational boxes; integration can
return rational error bounds; a monodromy calculation can return a finite permutation of certified
root names. Where a familiar theorem needs a different formulation or extra
displayed evidence, that difference is part of the mathematics to explain.

This discipline has benefits beyond its foundational motivation. Existence
proofs provide witnesses and algorithms. Error bounds compose across
calculations. Conditions such as separation from zero become explicit inputs
to division, instead of hidden assumptions. Persistent refinement lets later
requests reuse earlier work. Formal verification makes dependencies and gaps
in arguments inspectable, and helps distinguish essential hypotheses from
assumptions that a stronger constructive proof can remove. The aim is a
mathematics whose conclusions can be used at a specified finite accuracy,
with the evidence for that use carried alongside the calculation.

## License

The project's original code, including the Lean formalizations and scripts,
is licensed under [Zero-Clause BSD (0BSD)](LICENSE-CODE.md).
The project's original TeX manuscripts and compiled papers are licensed under
[Creative Commons Attribution-ShareAlike 4.0 International](LICENSE-PAPERS.md).
Third-party material retains its existing license and copyright notices.

## Where to start

The most complete mathematical exposition is the
[RFAP-1 paper](papers/RFAP/RFAP.pdf), which gives a finite constructive FTA and
rational-function argument principle over displayed Gaussian-rational
polynomials. Its source is [RFAP.tex](papers/RFAP/RFAP.tex).

For a gentler introduction to complex continued logarithms, see the
[interactive CCL essay (standalone HTML)](docs/ccl/static.html). It is prose-led and includes
Mafs visualizations of finite cylinders, refinement, arithmetic, and the
measure layer. The application source and local development instructions are
in [docs/ccl/README.md](docs/ccl/README.md).
Download the HTML and open it in a browser, or serve it through Pages;
repository code viewers may display its source. The interactive demonstrations
have not been properly tested.

Engineering guides and the interactive introduction are collected in the
[documentation index](docs/README.md).

The main Lean facades are:

| Area | Facade |
| --- | --- |
| Finite FTA and rational-function argument principle | `papers.RFAP.Chapters.Paper` |
| Gaussian-rational approximation and best approximants | `papers.RFAP.Chapters.Approximation` |
| Complex continued logarithms | `papers.CCL.Chapters.Paper` |
| Finite constructive measure theory | `Purelib.Measure` |
| Hyperelliptic periods and Legendre monodromy | `Purelib.Riemann` |
| Finite braid and knot constructions | `Purelib.Topology.Knot` |
| *Divine Proportions* | [facade](formalisations/DivineProportions/DivineProportions.lean) |
| Euclidean rational rotations | [facade](formalisations/RationalRotations/RationalRotations.lean) |
| Minkowski rational rotations | [facade](formalisations/MinkowskiRotations/MinkowskiRotations.lean) |

## What has been formalized

### Finite algebra, FTA, and rational functions

`Purelib/` starts with constructive rational and Gaussian-rational arithmetic,
dense polynomial algorithms, extended gcd, squarefree factorization and
multiplicity data. Finite Sturm chains and Cauchy-index calculations compute
winding on rational polygonal boundaries.

For a displayed squarefree positive-degree polynomial, the FTA construction
computes a large safe rational square, proves that its winding is the degree,
and extracts exactly degree-many pairwise separated winding-one box tracks.
Each track has an executable refinement operation that returns a strictly
nested rational box at any requested positive rational squared diameter. A
general polynomial retains multiplicities as finite data. The rational-
function extension cancels common factors constructively, separates zero and
pole sites, and proves the signed winding and multiplicity totals.

The separate approximation layer proves exact lower and sufficient
denominator-height bounds, terminating Hurwitz expansions, the finite Lakein
comparison, and a stronger two-tier notion of best approximation. Bounded
selectors return all and only the best Gaussian-rational pairs for a displayed
source. A local executable successor returns exactly the next occupied best
denominator level—or reports the exact terminal case—so iterating it produces
only best approximants. Consecutive best pairs have determinant quadrance one
or two; two index-two transitions cannot occur successively. The development
also contains finite Dirichlet/Chevallier-style upper and sharpness bounds,
finite critical runs, and finite rational dynamical models.

Module placement follows mathematical ownership and useful reuse, as recorded
in the [repository instructions](AGENTS.md). Architectural import restrictions are
retired; module acyclicity, publication coverage and constructive proof-route
checks remain required.

### Complex continued logarithms

`Purelib/CCL/` implements complex continued logarithms as finite words and incremental
raw-bit parsing. Terminating encodings reconstruct displayed Gaussian
rationals exactly. Every completed block acts projectively and contracts its
compatible cylinder by an explicit rational factor at most one half. Thus a
finite prefix has a certified rational region, and longer compatible prefixes
give progressively smaller regions without postulating a completed point.

Persistent CCL names answer finite accuracy and prefix-length requests. The
library provides addition, subtraction, multiplication, apartness-certified
division, exponential, positive-real logarithm, charted complex logarithm,
finite divided differences, jets, Taylor bounds, integration, rational-
function evaluation, and finite root families. Operations carry explicit
coherence proofs, so their answers do not depend on a permitted refinement
schedule.

On a finitely certified simple-root chamber, an executable algebraic-closure
controller returns the displayed degree-many productive root names together
with unique owners, nested separated boxes, and residual bounds. Finite
Rouche-certified chamber paths transport those owners and compute monodromy
permutations; concatenation composes them, reversal inverts them, and a path
retained in one chamber acts trivially. For `Z^d-w`, one explicit rational
circuit of `w` is proved to induce a single `d`-cycle on the certified root
names.

### Finite measure theory

`Purelib/Measure/` develops exact rational content and integration over finite
displayed carriers. It includes event bounds, probability, pushforwards,
couplings, almost-everywhere equivalence, `L^p` quantities, essential bounds,
finite convergence certificates, uniform integrability and Vitali-style
results, signed content, Jordan and Lebesgue decompositions, total variation,
quantiles, moments, covariance and regression, conditioning, Radon--Nikodym
density, filtrations, martingales, maximal inequalities, optional-sampling
style results, finite dynamics, Markov return estimates, and sampling.

These are exact finite theorems, not restrictions of a hidden sigma-additive
measure space. There is no sigma-algebra, countable union, limiting random
variable, or completed integral. `Purelib/Adapters/Measure/RootIsolation/` applies the theory to
rational boxes, while `Purelib/CCL/Measure/` turns finite prefix cylinders into
probability, concentration, threshold, quantile, stability, and estimator
certificates.

### Finite topology, periods, monodromy, and knots

`Purelib/Riemann/` computes finite cell models for hyperelliptic curves, their
Euler characteristic `2 - 2g`, cellular homology, and an explicit symplectic
basis. Its prepared integration layer supplies persistent A- and B-period
programs, fraction-free normalization, operational symmetry, and a positive
rational witness for each displayed nonzero rational-vector request. Genus
zero is automatic, and the curve-only theorem constructs inverse separation
and surface-energy certificates internally in every genus. Efficient evaluation
of larger examples remains a separate task.

For the Legendre family, the repository constructs explicit rational loops
around zero and one, derives the infinity loop by reversal, and proves the
corresponding root transport, Picard--Lefschetz actions, integral symplectic
matrices, product relation, and dual action on period columns. It also proves
the fraction-free Gauss--Manin and Picard--Fuchs polynomial reductions and has
operational period-jet and modular-action layers.

`Purelib/Topology/Knot/` extracts Artin words from finite rational polynomial loops and
proves cancellation, far commutation, the braid relation, and invariance under
the represented finite moves. Explicit loops realize every Artin word. For
`Z^p=w^q`, the extracted word is the torus braid
`(sigma_1 ... sigma_(p-1))^q`; its closure has `gcd(p,q)` components and is a
knot when that gcd is one. The library computes finite crossing, writhe,
linking, genus, and Alexander-coefficient data. This is presently a theory of
combinatorial braid closures, not yet ambient isotopy of embedded curves in
three-dimensional space.

### *Divine Proportions*

`formalisations/DivineProportions/Chapters/` formalizes the source-numbered finite constructive content
of N. J. Wildberger's *Divine Proportions: Rational Trigonometry to Universal
Geometry*. The formalization accounts for
all 121 numbered theorems, the worked examples, exercises, solved Problems
1--25, Appendix A's curve catalogue, and Appendix B's ellipson geometry.

The development covers rational trigonometry, triangle and polygon identities,
centres, conics and curves, projective and finite-field geometry, isometries,
stars, applications, and higher-dimensional algebraic calculations. Printed
defects are recorded and corrected rather than assumed. Analytic volume
integrals, infinite limits, and completed constants are outside the agreed
finite boundary; all finite algebraic endpoint content used by them is
retained. Within that boundary the source coverage is complete and no further
formalization work is currently planned.

### Rational rotations

The revised Euclidean and Minkowski papers have complete finite algebraic
coverage through separate publication facades and claim-by-claim ledgers
linked above. Their full build, lint, configured-script axiom audit and nanoda
checks passed on 11 October 2026. The August-draft formalisation and all
reusable Purelib providers are retained.

`formalisations/RationalRotations/Chapters/` formalizes the finite algebraic content of Wildberger's
*Rational rotations of three dimensional Euclidean space*. It develops the
anchor, cap, reflection, quaternion, projective, finite-field, and general
ternary-form descriptions; exact finite-field counts and conjugacy; the
Clifford correspondence; rational Minkowski parabolics; and projective
point--plane duality.

The retained open-problem development includes the rational coefficient
classification, exact finite-field rotation strata and counts, the finite
`chi`-visible quotient, arbitrary-size separated kernel-coset packs,
finite-request kernel approximation, exact finite orders `1,2,3,4,6`, the
general ternary Clifford correspondence, and point--plane polarity. These
are discussed using the revised source's numbering in the new companions.
Internal classification of generally nonfinite generated subgroups and a
completed topological closure theorem remain outside the proved results.

Two companion papers present current source issues, constructive resolutions
and the remaining open questions:

- [Euclidean issues and open-problem resolutions](formalisations/RationalRotations/IssuesAndOpenProblems.pdf)
  ([TeX source](formalisations/RationalRotations/IssuesAndOpenProblems.tex)):
  Problems 80–83, finite-field counts and conjugacy, rational spinor images and
  finite orders, and the general ternary correspondence.
- [Minkowski issues and open-problem resolutions](formalisations/MinkowskiRotations/IssuesAndOpenProblems.pdf)
  ([TeX source](formalisations/MinkowskiRotations/IssuesAndOpenProblems.tex)):
  Problems 90–94, ray inverses, causal versus arithmetic classification, and
  an explicit projective Thomas–Wigner factorization.

The companions identify which results have existing Lean certificates and
which additional coordinate proofs are supplied only in the papers. They
replace the old August-draft corrections paper.

## Exposition status

The formal library is ahead of its papers. “Formal proof complete” below
means that the intended finite theorem surface is implemented and audited; it
does not mean that every later research module has already been turned into a
finished article.

| Work | Status |
| --- | --- |
| [RFAP-1](papers/RFAP/RFAP.pdf) | Formal proof and edited paper complete; this is the recommended paper entry point. |
| [RFAP-2](papers/RFAP/RFAP-2.pdf) | Formal proof complete; paper needs editorial revision to match the final best-approximation and finite sharpness results. |
| [CCL-1](papers/CCL/CCL-1.pdf) | Formal proof complete; paper needs editing. |
| [CCL-2](papers/CCL/CCL-2.pdf) | Formal proof complete; paper needs editing and expansion to cover the later arithmetic and calculus surface. |
| *Divine Proportions* | Finite constructive source coverage complete; the ledger is the current exposition. |
| Rational rotations (August draft) | Retained formalization and archived coverage ledger; companion exposition now uses the revised source numbering. |
| Revised Euclidean and Minkowski rotations | Finite algebraic assertion coverage complete and fully checked; two current companion papers explain issues, resolutions and remaining open problems. |

## Proved but still to be explained properly

Several sizeable developments have code, examples, and module documentation
but no dedicated finished paper:

| Result | What is already proved | Principal modules |
| --- | --- | --- |
| Finite measure theory | The broad exact rational theory described above, including integration, `L^p`, convergence, decomposition, conditioning, martingales, dynamics, and CCL-prefix applications. | `Purelib.Measure`, `Purelib.Measure.Box.*`, `Purelib.CCL.Measure.*` |
| Finite Riemann-period package | Automatic finite hyperelliptic topology and symplectic homology, prepared persistent periods, fraction-free normalized matrices, bilinear symmetry, and request-wise positive rational margins. | `Purelib.Riemann.Periods.PeriodTheorem`, `Purelib.Examples.Curves.Hyperelliptic.Periods.Worked` |
| Explicit Legendre monodromy | Rational standard loops, root transport, Picard--Lefschetz matrices, normalized A/B periods from the unconditional theorem at `lambda = 1/4 + 2i`, unconditional dual period transport, data-derived productive quotients, finite observations, symbolic Gauss--Manin connection, and Picard--Fuchs reduction. | `Purelib.Curves.Legendre.Monodromy`, `Purelib.Curves.Legendre.PeriodMonodromy`, `Purelib.Examples.Curves.Legendre.NormalizedMonodromy`, `Purelib.Curves.Legendre.PicardFuchs.Connection` |
| Power monodromy | One rational circuit in `Z^d-w` acts as a single `d`-cycle on the certified roots. | `Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Monodromy` |
| Polynomial braids and torus links | Exact polynomial realization of finite braid words and constructive torus-braid closure invariants. | `Purelib.Topology.Knot` |

### Closed generated Legendre client

The concrete normalized client is based at the Gaussian-rational parameter
`lambda = 1/4 + 2i`.  Its zero and one paths are assembled from rational
segments carrying explicit coefficient-chamber overlap, persistent root
owners, square-root sheet clearance, and certified braid extraction.  The
infinity path is the finite reversal of their product, and the full product
path has the identity homology matrix.

The normalized period clients now use the unconditional finite Riemann period
theorem on corrected standard cycles. The former generated Legendre fixture,
its replay templates and fixture-dependent harnesses have been removed: the
certificates were expensive to build and their B connector was not the standard
B tour. The retired witness generator was removed with its dedicated test;
Git history retains it for historical reproduction.

General certified replay, checkpoint restoration and prepared-period observation
remain available. Exact replay proves ownership of the retained construction;
matching numerical values alone do not identify an old fixture with corrected
standard periods. Algebraic endpoint matrix action also does not by itself
prove geometric transport or the differential Gauss--Manin connection.

At the generic level, `braidWord_foldReversal` proves cancellation for the
actual stepwise productive executions of an arbitrary finite braid word and
its inverse.  Its preparation package retains each local denominator at the
literal intermediate name where it is used; independently prepared folded
representatives are related by an explicit input-congruence theorem rather
than a definitional reindexing.  The dual-period layer now constructs
`periodBraidMatrices` by reversing that generator list and transposing every
matrix, proves that its fold is exactly `periodMatrix`, and proves both
productive reversal and arbitrary-path transport.  In particular,
`NormalizedData.periodWord_productive_transport` identifies the prepared
stepwise output with the ratio of the two actual `EndpointContinuation` period
coordinates for any certified closed finite Legendre path.

`LegendreAutomaticPreparation.prepareWord` constructs the final denominator
preparation for every finite dual braid word from one `PositiveEnclosure` of
the original ratio. It computes a rational lower bound for the nonzero first
row and uses one prescribed apartification refinement, without a fuel search.
`enclosureOfPeriodPositivity` obtains this reusable enclosure from the existing
finite `PointwisePositivity` interface. Positivity is an additional input to
this guarantee; normalized period data alone does not currently supply it.
`LegendreAutomaticTransport.guaranteed` uses that enclosure to return a cached
matrix, denominator preparation, and productive output. Its `attempt` API
instead runs the existing bounded acquisition and retains the exact state on
exhaustion. Both routes return `Ready`, whose `transport` witness identifies
the output with the actual transported period ratio and whose `respects`
witness makes the result independent of the acquisition schedule.
The single-matrix `attempt_add` law identifies split-and-resumed budgets with
one combined run. `currentRequirement` exposes the exact retained denominator
obligation, and `resume` consumes matching state-indexed evidence to return a
`Ready` directly; `resume_respects` compares it with automatically acquired
outputs.
For callers needing intermediate divisions, `LegendreAutomaticFold.attemptWord`
automatically acquires the complete `PeriodFoldPreparations`. Exhaustion
retains completed head/suffix preparations and the current denominator search;
`attempt_add` proves exact equality between split-and-resumed and combined
budgets. Combined matrices are cached when their searches begin.

`LegendreGuaranteedFold.prepareWord` also constructs the *entire* stepwise
preparation without search from the same initial positive enclosure. The
preparation provider is carried through each actual fractional output using
the apart combined/inner denominator quotient; no new positivity certificate
is required at intermediate names. The returned provider can prepare further
words at the final output. `transport` proves the continued-period equation,
`equivalent_single` proves agreement with the default single-matrix output,
and `reversal` automatically prepares both a word and its inverse and proves
their productive cancellation. `LegendreAutomaticTransport.guaranteedOfPeriodPositivity`
is the direct adapter from the finite period positivity interface to a cached
final output.
`Ready.respects_matrix` and `Ready.respects_braid` compare outputs from
different words with equal period matrices or certified Artin equivalence.
`LegendreGuaranteedFold.equivalent_words` and `equivalent_braids` extend this
to complete stepwise computations, including independently chosen positive
enclosures.

`LegendrePositivityAcquisition.attempt` can discover the initial positive
enclosure itself. It inspects a cached rational ball and, when the centre has
positive imaginary height and the squared radius is below the squared
half-height, certifies that the entire ball has a positive imaginary lower
bound. Otherwise it performs one canonical refinement. Exhaustion retains
the exact source state, cached ball, and next request index; `attempt_add`
certifies exact split-and-resume behaviour. `finishBy` turns a displayed
finite passing-state witness into a sufficient inspection budget, without
claiming unconditional termination. `attemptTransport` and `attemptFold`
feed successful discovery directly into the guaranteed final-matrix or full
stepwise preparation. Their budget bounds positivity inspections, not the
subsequent finite preparation cost. Regression clients cover delayed success,
resumption, both word evaluators, and exact zero remaining unresolved at
every finite budget.

There is an important type distinction in this result.  Ordinary continuation
along a changing Legendre fibre is represented by `EndpointContinuation`: its
endpoint periods are the actual target-fibre programs evaluated on the
transported homology basis, hence they carry the transposed homology matrix.
No changing-fibre endpoint equality is postulated: the closed generated
monodromy client specializes this dual action to actual base-fibre period
programs.

## Period theorem status and remaining comparison work

The curve-only period theorem and its named examples are implemented.
Efficient execution and the operational Legendre comparison estimates remain
separate work.

1. **The finite Riemann-period theorem in every genus.**
   `riemann_period_theorem curve` takes only the displayed squarefree
   hyperelliptic curve and returns its period result. It constructs topology,
   the symplectic cellular basis, inverse separation, the first bilinear
   relation and positive energy internally. `PreparedCertificate.ofCurve`
   constructs the required inverse-tail and surface-energy data; callers supply
   no additional prepared certificate. This theorem does not establish
   efficient numerical execution or comparison of periods on different fibres.

2. **The named cubic, quartic, quintic, sextic, and septic period examples.**
   The `*PeriodTheorem` declarations in `PeriodExamples` call the unconditional
   curve theorem with their displayed curves. Their only argument is a trivial
   `Unit` token, and their results use those curves' actual integration programs.
   They require no supplied prepared certificate. Efficient finite-request
   evaluation of these larger examples remains unestablished.

3. **Operational Legendre Gauss--Manin and Picard--Fuchs equations.**
   The fraction-free polynomial reductions are unconditional, but the period-
   jet conclusions still consume `ConnectionCertificate` or
   `PicardFuchsCertificate`; their `connection_samples_close` and
   `residual_samples_close` fields are the hard analytic comparison estimates.
   These estimates should be produced by the prepared integration and
   subdivision machinery rather than handed to the headline theorem.

Some nearby premises are not defects. A generic theorem must be told which
finite paths represent the standard loops; productive division genuinely
requires denominator apartness; and a comparison between periods on different
fibres must be proved by continuation rather than postulated as automatic.
Likewise, ambient isotopy for spatial knots and the full subgroup
classification in rational rotations are missing theories, not superfluous
assumptions on an otherwise completed theorem.

## Building and checking

The toolchain and Mathlib revision are pinned to Lean/Mathlib `v4.32.2`.
The repository wrapper reconstructs the tracked Core proof patches in
`.lake/core-toolchain` and selects their checked compiler and complete artifacts:

```sh
scripts/run-lake.sh --wfail build
```

Completed compiler and module emissions are checked and reused after an
interrupted preparation. Use the wrapper for Lean commands too, so that source
elaboration, native proof generation and audits use the same Core providers:

```sh
scripts/run-lake.sh env lean --version
```

The CLI template uses `import all Lean.Shell` to retain the private
`ShellOptions.process` handler and run the original shell with those bodies.

Default builds include every declared library and executable, including
examples, tests, publications and configured harnesses. Run the configured
Lean lint checks over every active module and configured script owner, or select
a module explicitly:

```sh
scripts/run-lake.sh --wfail lint
scripts/run-lake.sh --wfail lint Purelib.Data.Vector.Basic
```

The selected syntax linters also run during ordinary builds, including Core-only
sources, through native providers configured without additional source imports.
The line-length limit is 120 characters. The wrapper expands an unscoped lint
command to the full active inventory; explicit commands remain scoped. See
[linting](docs/linting.md) for the selected checks and constructive exclusions.

Run all completion checks with one command:

```sh
scripts/check-all.sh
```

This includes the full warning-fatal build, tooling regressions, all-source lint,
the full axiom audit with configured script owners, and nanoda. It retains the
existing checked caches and records per-stage logs and timings. See
[completion checks](docs/verification.md) for prerequisites and worker settings.

Useful focused checks are:

```sh
scripts/check-purelib-surfaces.py
scripts/check-source.sh
scripts/check-axioms.sh --configured-scripts --full
```

Audit the same explicit modules as a focused build (source paths also work):

```sh
scripts/check-axioms.sh Purelib.Data.Rat.Fraction.Basic
scripts/check-axioms.sh --no-build Purelib/Data/Rat/Fraction/Basic.lean
scripts/check-axioms.sh --configured-scripts --full
```

With targets, `check-axioms.sh` builds only those modules, their dependencies,
and the fixed canonical audit/regression prerequisites, with warnings fatal.
Normally it audits safe non-meta source-facing declarations, including private
declarations and registered compiler rewrites, with their complete transitive
axiom closures. Generated and compiler helpers remain checked whenever a selected
declaration depends on them. Add `--all-helpers` to also audit every retained
kernel helper as an independent root, including meta, unsafe and partial helpers.
The two selections have separate pass-cache identities. Select changed
modules and affected consumers explicitly; reverse dependencies are not
automatically added. A scoped pass is not a
repository-wide pass. `--configured-scripts --full` includes every
active project module and Lake-declared script owner. Full mode uses Lake's
ordinary incremental build; it does not force recompilation of current artifacts.

Both modes retain the strict canonical declaration audit and executable
regression. `--no-build` requires all selected and supporting artifacts to be
current and fails before auditing if any need compilation. Scoped runs preserve
unrelated successful cache records. Cache keys bind the actual transitive public,
server, private and IR artifact bytes, toolchain, reader policy and selected
boundary, so a dependency change invalidates a result even if its root object is
unchanged. Set
`AXIOM_AUDIT_CACHE=0` to recheck without cached audit results,
`AXIOM_AUDIT_CACHE_DIR` to move the cache, or `AXIOM_AUDIT_JOBS=1` for a serial
run. Test the shell orchestration with `python3 -m scripts.test.axioms.test_orchestration`;
those fixture tests do not replace the Lean audit.

Set `AXIOM_AUDIT_REPORT_DIR` to retain complete root and dirty-dependency records;
reporting disables pass-cache reuse so the records cover the actual selected
modules. Add `--report-ir-only` to include an optional inventory of compiled code
without kernel declarations. This flag requires a report directory and adds no
axiom-freedom or runtime-correctness guarantee for IR-only code. For example:

```sh
AXIOM_AUDIT_REPORT_DIR=/tmp/ccl-axiom-diagnostics \
  scripts/check-axioms.sh --report-ir-only Purelib.Data.Rat.Fraction.Basic
```

For a failure reported by the audit, `trace-axiom.sh` prints the complete axiom
closure, the immediate dependencies carrying the selected axiom, and a shortest
dependency path. Substitute the reported module and declaration:

```sh
scripts/trace-axiom.sh --axiom propext MODULE DECLARATION
scripts/trace-axiom.sh --axiom Classical.choice MODULE DECLARATION
```

The independent nanoda check for the active project module inventory is:

```sh
scripts/check-nanoda.sh
```

This entrypoint builds every active project module and configured script owner
with warnings fatal. The native exporter imports complete private artifacts
without target initializers, extension callbacks or plugins. It emits one shared
graph for compatible ordinary modules and separate graphs for standalone script
environments, preserving distinct declarations such as `main`. Independent root
selection checks exact scanned owners and declarations before publishing a stream.
Nanoda checks complete types and proof bodies with an empty axiom allowlist.

For a focused run, provide one module name per line:

```sh
NANODA_MODULE_MANIFEST=scripts/nanoda/benchmarks/control.modules \
  NANODA_JOBS=2 scripts/check-nanoda.sh
```

`NANODA_JOBS` sets checker threads (default 2). The pinned parallel path uses
normal worker stacks; serial checking can overflow the smaller main-thread stack
on the complete ordinary graph. `NANODA_EXPORT_JOBS` sets exporter concurrency
(default 3), and `NANODA_POST_EXPORT_CHECKS` bounds checker instances (default 3).
Ready graphs are checked concurrently during export. Set `NANODA_PIPELINE=0` for
sequential phases. Choose overrides from whole-worker memory measurements, not
CPU count; consult [profiling.md](docs/profiling.md#repeated-verification-of-shared-proof-closures).
The old shard and adaptive chunk limit options are retired and rejected.

Export caches bind exact roots, scanned and defining owners, compiled dependency
parts, producer bytes and validation policy. Complete groups survive interruptions
and scheduling changes. Reload verifies input and output content hashes; missing
or corrupt artifacts fail explicitly. Checker receipts separately bind exact
stream bytes, checker, configuration and validation code. Export completion alone
is not checker success. `NANODA_CACHE_ROOT` isolates all cache families; otherwise
keep `.lake/nanoda-*` to reuse completed work.

See [the native tool contract](scripts/nanoda/README.md). A targeted pass does not
establish a full-repository pass, and nanoda does not replace the authoritative
axiom audit. The native producer is meta code; its strict helper closures remain
a separate strict `--all-helpers` audit obligation.

For raw declaration graph diagnostics, use
`python3 -m scripts.nanoda.export_graph`, optionally with `--manifest` and
`--no-build` when artifacts are current. Compare one compatible graph with a
complete native stream using
`python3 -m scripts.nanoda.graph GRAPH --stream STREAM`. These diagnostics retain
the complete raw reader and establish no independent checker pass.

`NANODA_BIN` selects the checker; otherwise the wrapper looks under
`.external/nanoda` and then on `PATH`. `LEAN4EXPORT_BIN` and `NANODA_EXPORT_MODE`
are retired and rejected. CI pins the independent checker in
[.github/workflows/lean-ci.yml](.github/workflows/lean-ci.yml).

Build the four main manuscripts with:

```sh
scripts/build-papers.sh
```

That regenerates `RFAP.pdf` and `RFAP-2.pdf` under `papers/RFAP/`, and
`CCL-1.pdf` and `CCL-2.pdf` under `papers/CCL/`, using
Tectonic. Build the two rotation companions separately from the repository
root:

```sh
tectonic formalisations/RationalRotations/IssuesAndOpenProblems.tex
tectonic formalisations/MinkowskiRotations/IssuesAndOpenProblems.tex
```

The interactive essay is a separate Vite/React/TypeScript package:

```sh
cd docs/ccl
npm install
npm run build
npm run dev
```

## Source organization

- `Purelib/` contains the reusable finite algebra, measure, geometry,
  Riemann, knot, root-isolation, and CCL developments. Project-owned finite
  replacements for broad upstream algebra live here by subject.
- `Purelib/Examples/` contains worked examples and generated certificates;
  `Test/` contains regression modules. Every `Purelib/` Lean source belongs to
  ordinary build and proof-audit coverage.
- `papers/CCL/` and `papers/RFAP/` contain the paper sources, PDFs and
  top-level Lean facades. `formalisations/DivineProportions/` and
  `formalisations/RationalRotations/` contain their chapters, facades, coverage
  ledgers and associated papers.
- `Purelib/CCL/Adapters/` contains reusable finite bridges from Paper-I boxes
  to CCL data. The paper-only CCL-2 bridge lives in
  `papers/CCL/Chapters/Bridge.lean`. Their Part-2 destinations follow the
  surveyed mathematical subjects.
- `scripts/` contains discovery, coverage, source-policy, axiom, nanoda, build, and
  paper-generation tools.

## Constructive engineering rules

Committed Lean changes must preserve the following properties:

- no `noncomputable` declarations, sections, or instances;
- no `classical` tactics, local instances, or choice shortcuts;
- direct constructive witnesses in preference to contradiction where
  reasonably possible;
- no proof route through infinite carriers, cardinality, compactness,
  completion, infinite series, or global enumeration;
- narrow, audited imports, with local replacements where upstream dependency
  closures cross the project boundary;
- empty transitive axiom closures for selected mathematical declarations,
  including private and generated proof dependencies;
- no new `native_decide` trust boundary and no resource-limit overrides such
  as `maxRecDepth` or `maxHeartbeats`; and
- `scripts/run-lake.sh --wfail build` passes without warnings.

The repository-level policy is recorded in [AGENTS.md](AGENTS.md).
