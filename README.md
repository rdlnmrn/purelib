# Finite constructive mathematics in Lean

This repository develops mathematics from finite, displayed, executable data.
Its basic objects are rational coefficients, finite lists and matrices, rational
boxes, bounded searches, finite paths and words, and proof-bearing refinement
states. A calculation may be refined as far as a caller asks, but the library
does not turn that open-ended protocol into a completed real or complex number.

The active Lean code uses neither `classical` nor `noncomputable`. It avoids
choice, completed infinite carriers, compactness, infinite series, and hidden
enumerations of all roots or field elements. The repository-wide axiom audit
discovers the active modules and declarations automatically and accepts only
`propext`; its stricter surfaces also reject `Quot.sound`.

The project began with a finite Fundamental Theorem of Algebra and complex
continued logarithms, but now also contains substantial developments in exact
approximation, finite measure theory, algebraic geometry, rational
trigonometry, rotations, monodromy, periods, and combinatorial knot theory.

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
[RFAP-1 paper](RFAP.pdf), which gives a finite constructive FTA and
rational-function argument principle over displayed Gaussian-rational
polynomials. Its source is [RFAP.tex](RFAP.tex).

For a gentler introduction to complex continued logarithms, see the
[interactive CCL essay (standalone HTML)](docs/ccl/static.html). It is prose-led and includes
Mafs visualizations of finite cylinders, refinement, arithmetic, and the
measure layer. The application source and local development instructions are
in [docs/ccl/README.md](docs/ccl/README.md).
Download the HTML and open it in a browser, or serve it through Pages;
repository code viewers may display its source. The interactive demonstrations
have not been properly tested.

The main Lean facades are:

| Area | Facade or ledger |
| --- | --- |
| Finite FTA and rational-function argument principle | `RFAP.Paper` |
| Gaussian-rational approximation and best approximants | `RFAP.ApproximationPaper` |
| Complex continued logarithms | `CCL.Paper` |
| Finite constructive measure theory | `FiniteMeasure` |
| Hyperelliptic periods and Legendre monodromy | `CCL.Riemann` |
| Finite braid and knot constructions | `CCL.Knot` |
| *Divine Proportions* | `DivineProportions`; [coverage ledger](DivineProportions/COVERAGE.md) |
| Rational rotations | `RationalRotations`; [coverage ledger](RationalRotations/COVERAGE.md) |

## What has been formalized

### Finite algebra, FTA, and rational functions

`RFAP/` starts with constructive rational and Gaussian-rational arithmetic,
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

The Paper-I boundary is one-way: nothing under `RFAP/` imports or refers to a
`CCL.*` declaration. CCL bridge code may consume the RFAP rational-box
interface, but RFAP does not consume CCL encoders or prefixes.

### Complex continued logarithms

`CCL/` implements complex continued logarithms as finite words and incremental
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

`FiniteMeasure/` develops exact rational content and integration over finite
displayed carriers. It includes event bounds, probability, pushforwards,
couplings, almost-everywhere equivalence, `L^p` quantities, essential bounds,
finite convergence certificates, uniform integrability and Vitali-style
results, signed content, Jordan and Lebesgue decompositions, total variation,
quantiles, moments, covariance and regression, conditioning, Radon--Nikodym
density, filtrations, martingales, maximal inequalities, optional-sampling
style results, finite dynamics, Markov return estimates, and sampling.

These are exact finite theorems, not restrictions of a hidden sigma-additive
measure space. There is no sigma-algebra, countable union, limiting random
variable, or completed integral. `RFAP/Measure/` applies the theory to
rational boxes, while `CCL/Measure/` turns finite prefix cylinders into
probability, concentration, threshold, quantile, stability, and estimator
certificates.

### Finite topology, periods, monodromy, and knots

`CCL/Riemann/` computes finite cell models for hyperelliptic curves, their
Euler characteristic `2 - 2g`, cellular homology, and an explicit symplectic
basis. Its prepared integration layer supplies persistent A- and B-period
programs, fraction-free normalization, operational symmetry, and a positive
rational witness for each displayed nonzero rational-vector request. Genus
zero is automatic; higher-genus theorem interfaces currently retain explicit
analytic preparation, discussed below.

For the Legendre family, the repository constructs explicit rational loops
around zero and one, derives the infinity loop by reversal, and proves the
corresponding root transport, Picard--Lefschetz actions, integral symplectic
matrices, product relation, and dual action on period columns. It also proves
the fraction-free Gauss--Manin and Picard--Fuchs polynomial reductions and has
operational period-jet and modular-action layers.

`CCL/Knot/` extracts Artin words from finite rational polynomial loops and
proves cancellation, far commutation, the braid relation, and invariance under
the represented finite moves. Explicit loops realize every Artin word. For
`Z^p=w^q`, the extracted word is the torus braid
`(sigma_1 ... sigma_(p-1))^q`; its closure has `gcd(p,q)` components and is a
knot when that gcd is one. The library computes finite crossing, writhe,
linking, genus, and Alexander-coefficient data. This is presently a theory of
combinatorial braid closures, not yet ambient isotopy of embedded curves in
three-dimensional space.

### *Divine Proportions*

`DivineProportions/` formalizes the source-numbered finite constructive content
of N. J. Wildberger's *Divine Proportions: Rational Trigonometry to Universal
Geometry*. The [coverage ledger](DivineProportions/COVERAGE.md) accounts for
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

`RationalRotations/` formalizes the finite algebraic content of Wildberger's
*Rational rotations of three dimensional Euclidean space*. It develops the
anchor, cap, reflection, quaternion, projective, finite-field, and general
ternary-form descriptions; exact finite-field counts and conjugacy; the
Clifford correspondence; rational Minkowski parabolics; and projective
point--plane duality.

The open-problem development includes a corrected homogeneous classification
for Problem 68; exact finite-field rotation strata and counts for Problem 69;
the finite `chi`-visible quotient, arbitrary-size separated kernel-coset packs,
finite-request kernel density, and exact finite orders `1,2,3,4,6` for Problem
70; and constructive solutions of the finite content of Problems 71 and 72.
It does not claim an internal classification of the generally nonfinite
generated subgroups in Problem 70 or a topological closure theorem.

Confirmed source defects are listed in
[RationalRotations/ERRATA.md](RationalRotations/ERRATA.md). The companion
[Corrections and Further Results](RationalRotations/CorrectionsAndFurtherResults.pdf)
([TeX source](RationalRotations/CorrectionsAndFurtherResults.tex)) presents the repairs,
finite replacements for apparently infinite claims, and additional
strengthenings for the author.

## Exposition status

The formal library is ahead of its papers. “Formal proof complete” below
means that the intended finite theorem surface is implemented and audited; it
does not mean that every later research module has already been turned into a
finished article.

| Work | Status |
| --- | --- |
| [RFAP-1](RFAP.pdf) | Formal proof and edited paper complete; this is the recommended paper entry point. |
| [RFAP-2](RFAP-2.pdf) | Formal proof complete; paper needs editorial revision to match the final best-approximation and finite sharpness results. |
| [CCL-1](CCL-1.pdf) | Formal proof complete; paper needs editing. |
| [CCL-2](CCL-2.pdf) | Formal proof complete; paper needs editing and expansion to cover the later arithmetic and calculus surface. |
| *Divine Proportions* | Finite constructive source coverage complete; the ledger is the current exposition. |
| Rational rotations | Source formalization complete within its finite boundary; the corrections-and-results companion is the current author-facing account. |

The older papers
[Finite constructive FTA over the Gaussian rationals](finite_constructive_fta_gaussian_rationals.pdf)
and
[Complex continued logarithms as constructive boxed names](complex_continued_logarithms_constructive_boxed_names.pdf)
are retained as historical drafts, not as the primary description of the
current code.

## Proved but still to be explained properly

Several sizeable developments have code, examples, and module documentation
but no dedicated finished paper:

| Result | What is already proved | Principal modules |
| --- | --- | --- |
| Finite measure theory | The broad exact rational theory described above, including integration, `L^p`, convergence, decomposition, conditioning, martingales, dynamics, and CCL-prefix applications. | `FiniteMeasure`, `RFAP.Measure.*`, `CCL.Measure.*` |
| Finite Riemann-period package | Automatic finite hyperelliptic topology and symplectic homology, prepared persistent periods, fraction-free normalized matrices, bilinear symmetry, and request-wise positive rational margins. | `CCL.Riemann.FinitePeriodTheorem`, `CCL.Riemann.FinitePeriodExamples` |
| Explicit Legendre monodromy | Rational standard loops, root transport, Picard--Lefschetz matrices, generated and normalized A/B periods at `lambda = 1/4 + 2i`, unconditional dual period transport, data-derived productive quotients, finite observations, symbolic Gauss--Manin connection, and Picard--Fuchs reduction. | `CCL.Riemann.LegendreMonodromy`, `CCL.Riemann.LegendrePeriodMonodromy`, `CCL.Riemann.ExplicitLegendreGeneratedMonodromyObservations`, `CCL.Riemann.LegendrePicardFuchs` |
| Power monodromy | One rational circuit in `Z^d-w` acts as a single `d`-cycle on the certified roots. | `CCL.Progressive.PowerMonodromy` |
| Polynomial braids and torus links | Exact polynomial realization of finite braid words and constructive torus-braid closure invariants. | `CCL.Knot` |

### Closed generated Legendre client

The concrete normalized client is based at the Gaussian-rational parameter
`lambda = 1/4 + 2i`.  Its zero and one paths are assembled from rational
segments carrying explicit coefficient-chamber overlap, persistent root
owners, square-root sheet clearance, and certified braid extraction.  The
infinity path is the finite reversal of their product, and the full product
path has the identity homology matrix.

The generated A- and B-period certificate files contain only finite rational
data selected by `scripts/generate-legendre-certificate.py`.  Lean reconstructs
their exact cycle geometry and checks every coefficient, root, clearance, and
error inequality; the Python output is not trusted.  The shard-local row
proofs compose into `generatedClosedRun_positionCoverage` for both cycles:
these certify that the actual retained A-parent list contains canonical rows
`0` through `3839`, and the B-parent list rows `0` through `271`, exactly once
and in traversal order.  `generatedPeriodGeometryCertificate` then ties those
lists and their two stationary sheet switches to the exact cycles and programs
stored in `generatedPeriodData`; no caller is left to derive that provenance.
`generatedSymplecticBasisProvenance` continues the chain to the canonical
finite genus-one intersection table: it identifies the raw branch-cut A/B
representatives, their scheduled working-path subdivisions, the complete
generated leg lists and retained row intervals, and the sharp schedule states
used by the public programs.  Thus `LiftedSymplecticCycles` is not being used
as an unchecked pair of A/B labels in this client.

Uniform positive real lower bounds for both generated periods derive the
A-period scaled inverse and the two nonconstant dual denominator preparations.
`generatedNormalizationCertificate` records that the normalized object retains
exactly that period data and derived scaled inverse, while
`generatedLoopContinuationCertificate` identifies all four raw monodromy
columns with finite endpoint continuation along the certified standard loops.
Consequently
`generatedFractionFreeMonodromyCertificate` and
`generatedProductiveMonodromyCertificate` are closed values apart from a
`Unit` evaluation token: neither accepts a caller-supplied nonvanishing or
comparison certificate.

The productive result includes the final transported-coordinate statements,
not merely quotient equations.  In particular,
`generatedOneProductiveTransport` and
`generatedInfinityProductiveTransport` prove operationally that multiplying
the transported A-coordinate by the displayed productive transform gives the
transported B-coordinate.  The zero-loop analogue is
`generatedZeroProductiveTransport` and needs no denominator preparation.
`generatedEndToEndMonodromyCertificate` packages the geometry, canonical
symplectic-basis provenance, the complete topological monodromy certificate,
normalization, continuation, fraction-free and productive certificates, both
derived preparations, and all three transported-coordinate statements in one
closed client value.  The generic productive certificate itself now retains
the zero transported-ratio theorem alongside its one and infinity analogues.

`ExplicitLegendreGeneratedMonodromyObservations` exposes the concrete paths,
braid words, exact homology matrices, their transposed dual period matrices,
and one shared caller-bounded observation of the normalized ratio and all
three transformed outputs.  Each request returns a finite rational ball, a
rational semantic allowance strictly below the requested target, and an exact
productive-prefix/parser contract.  It does not print or postulate a completed
transcendental value.  The three `generated*Output_transport` theorems state
directly that these same public observation channels are the ratios of the
corresponding transported period coordinates.

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

## Theorems whose public form should be strengthened

This list is deliberately narrower than a list of unfinished subjects. It
records places where the mathematical conclusion should follow from more
intrinsic finite input than the current headline declaration accepts.

1. **The higher-genus finite Riemann-period theorem.**
   `finiteRiemannPeriodTheorem curve certificate` automatically constructs
   the topology, Euler characteristic, and symplectic cellular basis, but its
   `PreparedCertificate` still supplies compatible period programs, inverse
   separation, the first bilinear boundary reduction, and the positive-energy
   reduction. Those fields contain much of the analytic substance normally
   asserted by the Riemann bilinear-relations theorem. The stronger result
   should construct them from the displayed squarefree hyperelliptic curve and
   finite accuracy requests, or reduce the residual premise to a small,
   geometrically intrinsic nondegeneracy condition.

2. **The named cubic, quartic, quintic, sextic, and septic period examples.**
   Their final `*PeriodTheorem` declarations still accept prepared
   certificates. Many branch, cycle, subdivision, and local-energy pieces
   are already automatic or explicitly checked, but they have not all been
   assembled into closed curve-specific theorem values. The unconditional
   exact matrix witnesses in `FinitePeriodExamples` prove the desired matrix
   shape in isolation; they should ultimately be connected to the actual
   integration programs for the displayed curves.

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
The repository wrapper finds a project-local or installed Lake executable:

```sh
scripts/run-lake.sh --wfail build
```

The same build can be run directly when the pinned local Elan installation is
present:

```sh
ELAN_HOME="$PWD/.elan" .elan/bin/lake --wfail build
```

Useful focused checks are:

```sh
scripts/check-paper-i-imports.sh
scripts/check-paper-ii-imports.sh
scripts/check-finite-measure-source.sh
scripts/check-finite-measure-imports.sh
scripts/check-axioms.sh
```

`check-axioms.sh` performs a warning-fatal build, discovers every active
project module, scans every compiled declaration, and reports its counts
dynamically. It caches successful module results by compiled-object and audit
signature. Set `AXIOM_AUDIT_CACHE=0` for a cold run,
`AXIOM_AUDIT_CACHE_DIR` to move the cache, or `AXIOM_AUDIT_JOBS=1` for a serial
diagnostic run.

For one unexpected dependency, `trace-axiom.sh` prints the complete axiom
closure, the immediate dependencies carrying the selected axiom, and a
shortest dependency path:

```sh
scripts/trace-axiom.sh RFAP.Polynomial.Factorization \
  RFAP.Factorization.inserted_has_representative
scripts/trace-axiom.sh --axiom Classical.choice MODULE DECLARATION
```

The independent nanoda check for all active Lean code is:

```sh
scripts/check-nanoda.sh
```

This single entrypoint discovers every active project module, builds the exact
set with warnings treated as errors, and sends every kernel-checkable project
source declaration through one exporter stream and one nanoda process. Private
and generated proof dependencies are included transitively. Lean's
compiler-generated `_unsafe_rec` runtime implementations are not proof objects
and are reported but not exported; set `NANODA_VERBOSE=1` to list them. The
script uses all available processor cores by default; set `NANODA_JOBS=N` to
override that count. It uses `LEAN4EXPORT_BIN` and `NANODA_BIN`, or discovers
matching builds under `.external/`. The source revisions used by CI are pinned in
[.github/workflows/lean-ci.yml](.github/workflows/lean-ci.yml).

Build the four main manuscripts with:

```sh
scripts/build-papers.sh
```

That regenerates `RFAP.pdf`, `RFAP-2.pdf`, `CCL-1.pdf`, and `CCL-2.pdf` using
Tectonic. The rational-rotations companion is built separately:

```sh
cd RationalRotations
tectonic CorrectionsAndFurtherResults.tex
```

The interactive essay is a separate Vite/React/TypeScript package:

```sh
cd docs/ccl
npm install
npm run build
npm run dev
```

## Source organization

- `mathlib/` contains project-owned finite replacements for broad upstream
  algebra. The lowercase `mathlib.*` module prefix is distinct from upstream
  `Mathlib.*`.
- `RFAP/` contains finite coefficient, Sturm, winding, isolation, rational-
  function, and approximation code. It has no CCL dependency.
- `CCL/` contains encoding, persistent names, arithmetic, calculus, geometry,
  measure bridges, finite monodromy, Riemann-period, and knot developments.
- `FiniteMeasure/` contains the representation-independent finite rational
  measure theory. RFAP and CCL applications live in their own trees.
- `DivineProportions/` and `RationalRotations/` contain the two Wildberger
  source formalizations and their coverage records.
- `legacy/` preserves superseded implementations for reference and is not in
  the active facades or axiom audit.
- `scripts/` contains import-boundary, source-policy, axiom, nanoda, build, and
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
- no new `native_decide` trust boundary and no resource-limit overrides such
  as `maxRecDepth` or `maxHeartbeats`; and
- `scripts/run-lake.sh --wfail build` passes without warnings.

The repository-level policy is recorded in [AGENTS.md](AGENTS.md).
