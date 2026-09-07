import mathlib.Tactic.QuotientFreeOmega
import RFAP.Geometry.Boxes
import CCL.Encoding.Baseline
import CCL.Encoding.CCF.CoordinateFloor
import CCL.Encoding.CCF.Contraction
import CCL.Encoding.CCF.Encoder
import CCL.Encoding.Examples
import CCL.Encoding.SectorCovariance
import CCL.Encoding.RawParserSemantics
import CCL.Encoding.PrefixMinimax
import CCL.Encoding.PrefixTower
import CCL.Encoding.ScaleFold
import CCL.Geometry.BoxTransport
import CCL.Arithmetic.BoxedNames
import CCL.Encoding.Transducer
import CCL.Arithmetic.RedundantSectors
import CCL.Arithmetic.RedundantBlockContraction
import CCL.Encoding.TerminalPadding
import CCL.Arithmetic.Enclosures
import CCL.Arithmetic.RedundantOutput
import CCL.Arithmetic.Bihomographic
import CCL.Progressive.Bihomographic
import CCL.Arithmetic.ResidualDecision
import CCL.Progressive.Enclosures
import CCL.Arithmetic.Controller
import CCL.Progressive.Charts
import CCL.Progressive.Transducer
import CCL.Progressive.TransducerGrammar
import CCL.Progressive.TransducerSemantics
import CCL.Progressive.MachineSemantics
import CCL.Progressive.MachineContraction
import CCL.Arithmetic.BoxedNameProcess
import CCL.Bridge.TrackProcess
import CCL.Bridge.ApproximationSharpness
import CCL.Persistent.Progressive
import CCL.Persistent.Track
import CCL.Progressive.PolynomialRoots
import CCL.Progressive.FiniteMonodromy
import CCL.Progressive.PowerMonodromy
import CCL.Arithmetic.OperationalEquivalence
import CCL.Progressive.Coherence
import CCL.Transcendental.Coherence
import CCL.Arithmetic.OperationalFieldLaws
import CCL.Transcendental.Laws
import CCL.Calculus.DividedDifference
import CCL.Calculus.Exponential
import CCL.Calculus.Logarithmic
import CCL.Calculus.FirstOrderJet
import CCL.Calculus.Trigonometric
import CCL.Progressive.FirstJet
import CCL.Calculus.QuadraticJet
import CCL.Progressive.QuadraticJet
import CCL.Calculus.HigherJet
import CCL.Progressive.HigherJet
import CCL.Progressive.PersistentTable
import CCL.Progressive.QuadraticTrace
import CCL.Progressive.AutomaticQuadraticTrace
import CCL.Progressive.PartialCalculus
import CCL.Progressive.TraceProgram
import CCL.Progressive.CalculusCongruence
import CCL.Transcendental.LogBranchGeometry
import CCL.Progressive.TaylorError
import CCL.Calculus.FiniteIntegration
import CCL.Progressive.Integration
import CCL.Transcendental.ComplexLogCorrectness
import CCL.Transcendental.LogBranchCalculus
import CCL.Transcendental.LogExpInverse
import CCL.Arithmetic.CertifiedExpression
import CCL.Bridge.ProjectiveRationalEvaluation
import CCL.Transcendental.RootPowers
import CCL.Transcendental.RootPowerBitComplexity
import CCL.Transcendental.Output

/-!
# Public API for the constructive CCL-1 and CCL-2 papers

This is the intended human-facing import for both parts of the complex
continued-logarithm development.  CCL-1 presents finite encodings, parsing,
cylinders, and boxed names.  CCL-2 presents the RFAP bridge, arithmetic,
transcendental operations, and finite calculus.  Lean imports re-export
declarations transitively, so downstream users normally need only
`import CCL.Paper` rather than the implementation modules above.  The list
below uses the stable declaration namespaces; source files are grouped by
role under `CCL/Encoding`, `CCL/Arithmetic`, `CCL/Progressive`, and the
other domain directories.

## CCL-1 order

* `RFAP.ConstructiveFraction` and `RFAP.ConstructiveGaussian` -- executable
  rational and Gaussian-rational coordinates.
* `CCL.BaselineAlgorithms` -- terminating real continued-fraction
  and continued-logarithm encoders with exact projective reconstruction.
* `CCL.CoordinateFloor` -- the executable Cartesian CCF return
  map, half-open-square invariant, norm bound, and integer digit cone.
* `CCL.CCFContraction` -- the piecewise coarse bound, checked
  exceptional-digit coefficient table, crossed-pair exclusion, and exact
  three-step contraction theorem.
* `CCL.CCFEncoder` -- the terminating Gaussian-rational CCF
  encoder with strict three-clause denominator descent and exact integral and
  affine projective reconstruction.
* `CCL.Normalization` -- bounded normalization scans.
* `CCL.Sectors` -- the finite eight-sector table.
* `CCL.SectorCovariance` -- the exact four-quarter-unit by
  two-canonical-row covariance check, including every half-open boundary.
* `CCL.Decoder` and `CCL.BlockContraction` -- decoder
  blocks and their direct finite contraction proofs.
* `CCL.Cylinder` -- finite words, projective cylinders, and their
  shrinking squared-chordal bound.
* `CCL.Integral` -- explicit Gaussian-integer fractions without
  Mathlib's real/complex Gaussian-integer construction.
* `CCL.Encoder` -- the terminating encoder and exact
  reconstruction theorem.
* `CCL.Examples` -- kernel-checked completed blocks and raw words
  for the three exact CCL examples printed in the manuscript.
* `CCL.RawParser` and
  `CCL.RawParserSemantics` -- arbitrary finite raw-prefix states,
  affine transition semantics, and deterministic child ownership.
* `CCL.PrefixMinimax` -- longest-common-prefix gauges, the finite
  opposite-child two-witness minimax theorem, and its exact dyadic bit-budget
  corollary, entirely within the pure finite-word layer.
* `CCL.PrefixTower` -- monotone `take` prefixes of an exact finite
  encoder word, their pure cylinder predicates, and their exact pre-terminal
  gauge distance.
* `CCL.ScaleFold` -- exact right-scale action, determinant,
  denominator-weight, truncation, and two-tail invariance, including the
  quarter-unit angular folds.
* `CCL.BoxTransport` -- the optional quantitative conversion of
  completed projective cylinders to explicit witness-centred rational boxes,
  generic denominator-separated homographic box transport, and finite
  coordinatewise hulls.  It does not alter the pure CCL word or parser.
* `CCL.BoxedNames` -- finite raw-prefix/box/witness certificates,
  refinement traces, and the operational progressive boxed-name interface.
* `CCL.Transducer` -- coherent finite prefix extension and the
  certified terminal cursor for each complete rational encoding.

## CCL-2 order

* `CCL.RedundantSectors` and
  `CCL.RedundantBlockContraction` -- the overlapping safe-output
  layer used by arithmetic, including affine/`omega` tails and finite-list
  dyadic cylinder contraction, without changing canonical bitstream semantics.
* `CCL.TerminalPadding` -- projective non-return unary padding and
  its explicit dyadic squared-chordal estimate, together with a finite
  projective transport coefficient proving that any fixed decoder-prefix
  distortion is absorbed by later redundant half-contracting blocks.
* `CCL.ArithmeticEnclosures` -- finite squared-error transport for
  addition, subtraction, multiplication, and apartness-certified division.
* `CCL.RedundantOutput` -- the explicit finite-margin cover and
  bounded unary-or-sector decision used by arithmetic output.
* `CCL.Bihomographic` -- homogeneous `+`, `-`, `*`, and `/`
  states with exact left-input, right-input, and output substitution laws.
* `CCL.ProgressiveBihomographic` -- the proof that progressive
  process candidates have those four initial matrix semantics and that all
  three decoder substitutions compose exactly.
* `CCL.ResidualDecision` -- the finite small-residual-or-apart
  decision which selects unary padding or safe affine inversion.
* `CCL.ProgressiveEnclosures` -- finite-state progressive names,
  persistence, and closed rational accuracy budgets for `+`, `-`, `*`, and
  apartness-certified `/`.
* `CCL.ArithmeticController` -- the total one-refinement
  unary-or-sector and residual-padding-or-inversion decisions.
* `CCL.ProgressiveCharts` -- finite candidate witnesses and the
  calculated refinements which turn semantic lower norms into whole-ball
  apartness and normalized loop centres.
* `CCL.ProgressiveTransducer` -- the total overlapping initial,
  low, loop, and residual controller, exposed as a finite-request raw-bit
  cursor with elementary arithmetic entry points.
* `CCL.ProgressiveTransducerGrammar` -- the persistent proof that
  every whole buffered arithmetic chunk advances the unchanged pure raw CCL
  parser to the controller's recorded phase.
* `CCL.ProgressiveTransducerSemantics` -- exact reconstruction of
  total affine-or-`omega` safe redundant blocks through the unchanged ordinary
  decoder matrices, independently of canonical annulus membership, plus the
  homogeneous residual-tail form of their pairwise half contraction.
* `CCL.ProgressiveMachineSemantics` -- the exact projective cursor
  invariant through every quantitative transition, one-bit buffer operation,
  and finite arithmetic-name request, with the live normalized sector branch
  tied directly to that homogeneous half-contraction estimate.
* `CCL.ProgressiveMachineContraction` -- the optional quantitative
  sidecar, separate from the pure bit cursor: finite live traces of normalized
  blocks, transported `K * 2⁻ⁿ` bounds, and pairwise terminal-unary bounds for
  exact results which cannot be recognized from opaque names.
* `CCL.BoxedNameProcess` -- the one-way conversion of boxed CCL
  inputs into arithmetic enclosure processes and productive raw-grammar
  outputs for `+`, `-`, `*`, and apartness-certified `/`.
* `CCL.TrackProcess` -- direct conversion of Paper-I shrinking
  winding-one box tracks into exact progressive arithmetic cursors, with a
  direct squared-chordal diameter bound at every requested box accuracy and
  without extracting a completed root.
* `CCL.ApproximationSharpness` -- one-way conversion of an explicitly
  reserved finite robust RFAP sharpness run into coherent initial segments of
  its certified window list and of one displayed rational sample's finite CCL
  word; extensions preserve both prefixes and the common robust box.
* `CCL.ProgressivePolynomialRoots` -- effective algebraic closure on a
  finitely certified simple-root chamber: exactly degree-many uniquely owned,
  pairwise-separated persistent CCL root names, advanced by finite coherent
  coefficient refinements and derivative-separated rational Newton boxes.
* `CCL.FiniteMonodromy` -- finite chains of Rouché-certified chamber overlaps
  compute owner permutations; concatenation composes them, reversal inverts
  them, and a path retained inside one chamber has identity monodromy.
* `CCL.PowerMonodromy` -- an explicit rational unit circuit for `Z^d-w`,
  together with a finite returned-lift calculation proving that its computed
  owner permutation is one degree-cycle.
* `CCL.PolynomialRootStreams` -- the total `p / 1` specialization of the
  rational bridge: a finite displayed index for every exact or higher RAT
  root site, its multiplicity, and a persistent bitstream request carrying
  both nested-box and squared-chordal sidecar-error guarantees.
* `CCL.PersistentProgressive` and
  `CCL.PersistentTrack` -- accuracy refinement of an already
  running arithmetic cursor without changing its raw word, followed by the
  joint Paper-I request which returns nested boxes, exact prefix growth, and
  an arbitrarily small projective cylinder for the same finite site.
* `CCL.FiniteExp`, `CCL.FiniteLog`,
  `CCL.FiniteComplexLog`, and their sensitivity results -- finite
  real or Gaussian-rational Horner recurrences with displayed rational
  pairwise-error bounds, not completed exponential or logarithm values.
* `CCL.ProgressiveExpRange` -- bounded dyadic input scaling,
  local finite exponential sampling, and exactly repeated progressive
  squaring for arbitrary arithmetic CCL inputs; its `named` operation is the
  total CCL-to-CCL exponential transform, with the enclosure process retained
  as the accuracy sidechannel used by the raw output controller.
* `CCL.PositiveDyadic`,
  `CCL.ProgressiveLogRange`, and
  `CCL.ProgressiveLogPositive` -- bounded dyadic normalization,
  explicit logarithm branch certificates, finite `log 2` correction, and
  automatic charting from a positive-real rational lower bound.
* `CCL.ProgressiveComplexLog` and
  `CCL.ComplexLogChart` -- the Gaussian local recurrence and one
  explicit complex branch chart, carrying a Gaussian-rational scale,
  candidate-wise denominator clearance, reduced-disk proof, and progressive
  additive correction; candidate clearance is turned into whole-ball
  apartness by one finite preparation.
* `CCL.OperationalEquivalence`,
  `CCL.ProgressiveCoherence`,
  `CCL.TranscendentalCoherence`,
  `CCL.TranscendentalLaws`, and
  `CCL.ComplexLogCorrectness` -- finite-request equality of
  progressive CCL approximations, its constructive equivalence operations,
  the finite rational allowance certificate that makes independent process
  refinement branches operationally coherent,
  preservation of that certificate through arithmetic, global exponential
  range reduction, repeated squaring, and logarithmic correction arithmetic,
  the exact identification of every Horner sample with its bounded Taylor
  polynomial, the normalization `exp(0) = 1` at every depth, the operational
  local exponential addition law, the finite polynomial and remainder proof
  of the local exponential--logarithm inverse, and the additional
  correction-exponential certificate which distinguishes a semantically
  anchored complex-log branch from an arbitrary safe chart.  For displayed
  rational chart inputs, `exp_charted_log_equivalent` combines that anchor
  with the local inverse and returns a productive CCL name operationally
  equivalent to the input.
* `CCL.TranscendentalOutput` -- the paper-facing combined request:
  a displayed rational output ball below any positive squared-error target
  and exactly any requested finite number of CCL bits from the same refined
  state, together with exact ordinary raw-parser semantics tied to candidates
  explicitly possible at that state; `g_bitstream_and_error` gives the same
  contract for one certified positive-real `ExpName(x) - LogName(y)`
  composition, while `complex_log_bitstream_and_error` and
  `complex_g_bitstream_and_error` give the explicitly charted complex forms.
  In particular, `exp_ccl_computable` names the end-to-end theorem that the
  exponential output is computable in this CCL-with-sidechannel
  representation, rather than merely exposing unrelated Horner samples;
  `log_ccl_computable` and `complex_log_ccl_computable` state the same
  CCL-to-CCL contract for the automatic positive-real and explicitly charted
  complex logarithm domains.
* `CCL.CertifiedExpression`,
  `CCL.ProjectiveRationalEvaluation`, and
  `CCL.RootPowers` -- finite compositional expressions,
  projective rational-function evaluation, and the distinction between the
  degree-sharp finite family of roots of `T^q-y` and one explicitly
  branch-selected logarithmic root.  The special power form now bypasses
  generic Sylvester elimination: the sparse equation `S^q-N(y)` enumerates
  rational quadrances, and a finite Lucas recurrence supplies two sparse
  coordinate polynomials at each surviving quadrance.  Endpoint-divisor
  candidates are checked by finite exponentiation and promoted to terminating
  exact CCL states.  The list and work bounds
  `ConstructiveRationalRootCandidates.candidates_length_le`,
  `RootPowers.rawDerivedCandidates_length_le`,
  `RootPowers.derivedCandidates_length_le`, and
  `RootPowers.automaticExactRoots_length_le` bound every finite
  candidate pass.  `RootPowerBitComplexity.account` records
  binary-width-weighted clearance, sparse construction, endpoint-divisor,
  normalization, Horner, duplicate-removal, and exact-power work;
  `.searchCoefficientSlots_eq` and `.automaticExactRoots_bit_complexity`
  prove its sparse slot and test-count bounds.
* `CCL.Trigonometric`,
  `CCL.ProgressiveFirstJet`,
  `CCL.QuadraticJet`,
  `CCL.ProgressiveQuadraticJet`, `CCL.HigherJet`,
  `CCL.ProgressiveHigherJet`,
  `CCL.ProgressivePersistentTable`,
  `CCL.ProgressiveQuadraticTrace`,
  `CCL.ProgressiveAutomaticQuadraticTrace`,
  `CCL.ProgressivePartialCalculus`,
  `CCL.ProgressiveTraceProgram`,
  `CCL.ProgressiveCalculusCongruence`,
  `CCL.ProgressiveTaylorError`,
  `CCL.FiniteIntegration`,
  `CCL.ProgressiveIntegration`, and
  `CCL.LogExpInverse` -- sine and cosine as total certified
  exponential compositions; synchronized progressive value/slope requests;
  explicit quadratic factors propagated through finite composition; actual
  persistent cursors for finite channel tables; a common-index semantic trace
  whose five channels retain the exact quadratic identity, explicit rational
  remainder bound, and productive bitstream contract even for a genuinely
  changing input; finite failure data which identifies a missing apartness,
  chart, branch, or transport certificate rather than assuming it; one
  finite program indexed by the complete semantic trace, whose arithmetic,
  composition, exponential, reduced-logarithm, sine, and cosine nodes retain
  the five actual persistent CCL channels; operational congruence across
  equivalent inputs and independently scheduled redundant prefixes, including
  the principal arithmetic and exp/log laws at that bit-producing layer; finite
  higher, Taylor, directional, and multivariable coefficient tables with
  displayed evaluation, discarded-tail, and directional error budgets; the
  coefficient-defined integral, algebraic fundamental theorem, polynomial
  initial-value problems, and finite exponential ODE defect; finite
  rational-path refinement programs whose local polynomial allowances are
  transported to a productive coherent CCL integral, with exact-polynomial,
  orientation, concatenation, linearity, and supplied-antiderivative
  compatibility; and the reverse
  logarithm--exponential law on an explicitly zero-aligned local branch.
* `RFAP.Boxes` -- finite rational boxes for downstream isolation.

## Numbered manuscript result map

The paper-facing proof roots are audited executable declarations rather than
editorial promises:

### CCL-1 results

* continued-fraction substitution and finite normalization:
  `CCL.Mat2.cf_substitution`, `Normalization.high`, `.low`,
  `.loop`, and the three `exponent_eq_of_bounds` theorems;
* finite real CF and CL algorithms: `cfEncode_reconstruct` and
  `clEncode_reconstruct`;
* the CCF digit cone, three-step contraction, termination, and reconstruction:
  `CoordinateFloor.digit_cone`,
  `CCFContraction.three_step_contraction`, and
  `CCFEncoder.encode_reconstruct`;
* sector partition, contraction, and unit covariance:
  `Sector.select_spec`, `Sector.holds_unique`, `Sector.select_contraction`, and
  `SectorCovariance.holds_covariant`;
* inversion descent and finite exact CCL encoding:
  `Decoder.inversion_stage_descent`,
  `normalized_denominator_descent`, and
  `Encoder.encode_reconstruct`;
* finite minimax, dyadic bit budget, and prefix tower:
  `finite_twoWitness_minimax`, `bitGauge_twoWitness_radius`, and the four
  public theorems in `PrefixTower`;
* one-tail, two-tail, and scale-fold identities:
  `Mat2.chordalSq_truncation`, `Mat2.chordalSq_act_affine`, and the public
  equalities in `ScaleFold`;
* completed-block contraction and shrinking prefixes:
  `BlockContraction.Tail.contraction`,
  `Cylinder.completedPrefix_chordBound`, and
  `ProjectiveRealizes.chordalSq_le_half_pow`;
* explicit rational boxes, generic transport, and boxed-name processes:
  the paper-bound theorems in `BoxTransport` and
  `BoxedNameProcess.ProgressiveName.toProcess`;

### CCL-2 results

* CCL-wrapped FTA/RFAP: the public results imported by `CCL.Bridge.Paper`,
  including the
  signed zero/pole arithmetic-name interfaces;
* progressive-coefficient algebraic closure:
  `ProgressivePolynomialRoots.SimpleRootChamber.ofResult`,
  `.effectiveAlgebraicClosure`,
  `EffectiveAlgebraicClosure.roots_productive`, `.roots_exact`,
  `.refined_boxes_strict`, `.refined_boxes_accurate`,
  `.refined_boxes_pairwiseSeparated`, `.refined_anchor_residual_le`, and
  `.no_degree_succ_reference_family`;
* finite monodromy of persistent root owners:
  `FiniteMonodromy.ChamberPath.monodromy`, `.monodromy_append`,
  `.monodromy_reverse`, `.finalRootName_productive`,
  `.finalRootName_exact`, `FiniteMonodromy.LocalPath.monodromy_identity`, and
  `PowerMonodromy.unitCircuitMonodromy_isSingleCycle`;
* annulus-free redundant inversion and block contraction:
  `RedundantSectors.postInversion_norm_gt_one` and
  `RedundantBlockContraction.Tail.contraction_half`;
* arithmetic enclosure, chart sufficiency, exact cursor semantics, and
  productivity: the four `Process` operations, the loop/residual decisions,
  `ProgressiveMachineSemantics.step_exact`, and the four
  `Named.*_productive` theorems;
* finite exponential, positive-real logarithm, and explicitly charted complex
  logarithm output:
  `ProgressiveExpRange.productive`,
  `ProgressiveLogPositive.automaticLocalChart`, and
  `TranscendentalOutput.exp_bitstream_and_error` and
  `.exp_ccl_computable`, plus `.log_bitstream_and_error` and
  `.log_ccl_computable`, whose conclusions include the same-state exact
  cursor certificate, plus `.g_bitstream_and_error` for the certified
  exponential-minus-logarithm composition; the complex counterparts are
  `FiniteComplexLog.sample_later_close`,
  `FiniteComplexLog.sample_input_close`,
  `ComplexLogChart.reducedDiskOfBounds`, and
  `TranscendentalOutput.complex_log_bitstream_and_error` and
  `.complex_log_ccl_computable` and `.complex_g_bitstream_and_error`;
* finite operational equality and the proved local analytic laws:
  `OperationalEquivalence.Equivalent.refl`, `.symm`, and `.trans`,
  `ProgressiveCoherence.Coherent.namedEquivalent`, `.add`, `.sub`,
  `.mul`, `.apartify`, and `.div`,
  `TranscendentalCoherence.expNamedCoherent`,
  `.localExpNamed_respects`,
  `.mulToNamed_equivalent_pointwise`, and
  `.localExp_add_actual_named_equivalent`, together with the coherent actual
  arbitrary-input law `.coherentLocalExp_add_named_equivalent`, whose finite
  resampling step is `.dynamicExpSumReindexEquivalent`; the total automatic
  arbitrary-input law is `.automaticExp_add`, including independent finite
  range-exponent reconciliation, and `.automaticExp_respects` transports
  operational equality through that total transform; `.automaticExp_zero`
  identifies the total transform of exact zero with exact one; and the
  coherent actual
  self-multiplication bridge `.coherentSquare_toNamed` and fixed finite
  repeated-squaring congruence `.squareIterate_respects`,
  `FiniteExp.sample_zero`, and
  `TranscendentalLaws.sample_eq_truncatedExp` and
  `.exp_zero_equivalent_one`, `.exp_add_equivalent`, and the productive
  CCL-name lift `.exp_add_named_equivalent`, together with
  `FinitePolynomial.local_exp_log_equivalent`; a complex chart's
  additional branch anchor is the finite data type
  `ComplexLogCorrectness.BranchCertificate`, and its
  rational-input inverse law is `.exp_charted_log_equivalent` with productive
  CCL wrapper `.expChartedLogNamed_productive`; the wrapper's actual
  CCL-name equality to the exact input is
  `.exp_charted_log_named_equivalent`; for arbitrary inputs the actual outer
  exponential is split by `.actualExp_chartedLog_split`, and an anchored
  correction is consumed by `.actualExp_chartedLog_to_anchoredProduct`;
  `.dynamicLocalExpLogReindexEquivalent` connects the actual stateful local
  exponential to the diagonal finite exp--log program,
  `.dynamicLocalExpLog_chart_equivalent` identifies that program with exact
  finite Möbius reconstruction, and
  `.actualExp_chartedLog_to_scaledChart` reduces the arbitrary-input inverse
  to the rational chart-resampling equality isolated by
  `.actualExp_chartedLog_named_equivalent_of_scaledChart`; the sharp finite
  Möbius sensitivity theorem is
  `FinitePolynomial.localChart_input_close`, the denominator-aware
  scaled form is `.scaledReduced_input_close`; the independently sampled
  numerator/denominator estimate is
  `.asynchronousScaledReduced_input_close`; and the branch-scaled operational
  lift is
  `.scaledDynamicLocalExpLogChartNamed_respects`, and
  `ComplexLogCorrectness
  .actualExp_chartedLog_named_equivalent_of_reducedReference` permits the
  last arithmetic proof to use the constructed `.synchronizedReducedNamed`;
  `.synchronizedReducedDisk` supplies its local disk and
  `.synchronizedReducedSample_reconstructs` proves exact rational
  reconstruction sample by sample; the bounded finite-index theorem
  `.synchronizedReduced_reachesRequestedSourceIndex` lifts this to
  `.synchronizedScaledChart_reconstructsInput`;
  `.reduced_equivalent_synchronizedReduced` proves operational equality of
  the original stateful quotient with that reference using finite division
  scheduling and the asynchronous estimate; and the resulting full
  arbitrary-input anchored inverse is
  `.actualExp_chartedLog_named_equivalent`;
* operational arithmetic, exponential units, and finite non-vanishing:
  `OperationalFieldLaws.coherentAdd_comm`,
  `.coherentAdd_assoc`, `.coherentMul_add_left`, `.coherentAdd_mul_right`,
  the zero/unit/inverse laws, `.automaticExp_neg_mul`,
  `.automaticExp_mul_neg`, `.exactZero_not_equivalent_exactOne`, and
  `.automaticExp_not_equivalent_zero`;
* limit-free algebraic calculus:
  `DividedDifference.power_sub_power_factor`,
  `.powerKernel_diagonal`, `.eval_sub_factor`,
  `.polynomialKernel_diagonal`, `.product_kernel_factor`,
  `.composition_kernel_factor`, `.reciprocal_kernel_factor`,
  `.signedPower_sub_factor`, `.signedPowerKernel_diagonal`,
  `.LaurentPolynomial.eval_sub_factor`,
  `.LaurentPolynomial.kernel_diagonal`,
  `.RationalPolynomial.eval_sub_factor`, and
  `.RationalPolynomial.kernel_diagonal` construct the secant kernel before
  diagonal substitution, including negative powers and certified rational
  denominators, without a limit or division by `x-y`;
* executable exponential calculus:
  `ExponentialCalculus.expSample_sub_one_factor`,
  `.expRelSample_succ_sub_one_factor`, `.expSample_second_order_factor`,
  `.expSample_second_order_normSq_le`,
  `.expDifferentialSample_diagonal`, `.expProductSample_sub_base_factor`,
  `.expProductSample_second_order`,
  `.expProductSample_second_order_normSq_le`, and
  `.expDifferential_equivalent_direct` give exact finite first- and
  second-order factorizations for productive `exprel` and `exp2rel` CCL
  computations, then connect the translated product to direct `exp(x+h)`;
* executable logarithmic calculus:
  `LogarithmicCalculus.log1pRelNamed_productive`,
  `.log1pSecondRelNamed_productive`, `.log1pSample_factor`,
  `.log1pRelSample_succ_sub_one_factor`,
  `.log1pSample_second_order_factor`,
  `.log1pSample_second_order_normSq_le`,
  `.log1pSample_sub_factor`, `.log1pSecantKernel_diagonal`,
  `.log1pDerivative_geometric_remainder`,
  `.log1pDerivative_sub_inverse_bound`,
  `.log1p_derivative_equivalent_inverse`, and
  `.anchoredLogDerivative_inverse` give finite local first- and second-order
  logarithm programs, identify the diagonal of the constructed secant kernel
  with the finite geometric derivative program, prove its reciprocal law at
  arbitrary requested accuracy, and transport it to an anchored branch;
* executable first jets and forward differentiation:
  `FirstOrderJet.FirstJet.reciprocal_slope_mul_square`,
  `FirstJet.JetExpression.jet_value`, `.jet_mul_slope`,
  `.jet_reciprocal_slope`, `.jet_exponential_slope`,
  `.jet_logarithm1p_slope`, and
  `.logarithm1p_primitive_derivative_equivalent` evaluate a finite expression
  and its one-variable first-order coefficient together, with decidable
  displayed domain checks;
* extended finite operations and calculus:
  `Trigonometric.sine_bitstream_and_error` and
  `.cosine_bitstream_and_error`,
  `ProgressiveFirstJet.FirstJet.valueRequest_allowance_lt`,
  `.slopeRequest_allowance_lt`, and `.synchronized_bitstream`, together with
  `ProgressiveQuadraticJet.CertifiedCalculation.request_expansion`,
  `.request_remainder_le`, and `.synchronized_bitstream_and_quadratic_law`,
  `QuadraticJet.Certificate.add`, `.mul`, `.reciprocal`, `.div`,
  `.scale`, `.movement_le`, `.compose`, `.exponential`, and `.logarithm1p`,
  `HigherJet.TaylorJet.derivativeOrder`, `.coefficient_mul`,
  `.derivative_mul`, and the three multivariable directional laws,
  `ProgressiveFiniteTable.sharedName_bitstream_and_allowance`,
  `ProgressiveFiniteTable.Table.exact_requestCenters`,
  `ProgressiveHigherJet.TaylorJet.coefficient_bitstream_and_allowance`,
  `.truncated_coefficient_bitstream_and_allowance`,
  `.ofDisplayed_requestCenters`, and
  `ProgressiveHigherJet.MultivariableFirstJet.directional_bitstream_and_allowance`,
  `ProgressivePersistentTable.ChannelCursor.request_represents_origin`,
  `.request_pair_chordalSq_le`, `.request_one_grows`,
  `.schedules_compatible`, and
  `ProgressivePersistentTable.TableCursor.member_word_extends_and_grows`,
  `ProgressiveQuadraticTrace.Trace.root_expansion`,
  `.root_remainder_le`, `.bitstream_and_quadratic_law`,
  `.nonterminatingIdentity_changes`, `.nonterminatingIdentity_bitstream`,
  `.add` and `.neg`,
  `ProgressiveAutomaticQuadraticTrace.Trace.mulAutomatic`,
  `.reciprocalAutomatic`, `.divAutomatic`, `.composeAutomatic`,
  `.exponentialAutomatic`, `.reducedLogAutomatic`, `.sineAutomatic`, and
  `.cosineAutomatic`, which compute the common transport internally from
  finite moduli, centre bounds, and the displayed disk or positive lower
  quadrance certificates,
  `ProgressivePartialCalculus.reciprocal_missing_exposes_requirement`,
  `.division_missing_exposes_requirement`,
  `.logarithm_missing_chart_exposes_requirement`,
  `.traceReciprocal_missing_transport_exposes_requirement`, and
  `.automaticReciprocal_missing_base_exposes_requirement`,
  `.automaticExponential_missing_exposes_requirement`,
  `.automaticReducedLog_missing_exposes_requirement`, and
  `.transition_missing_overlap`,
  `ProgressiveTraceProgram.Calculation.persistent_bitstream_and_quadratic_law`,
  `.changingArithmetic_input_changes`, `.changingArithmetic_keeps_emitting`,
  and `.exactCalculation_certificate`,
  `ProgressiveCalculusCongruence.compatibleRequests_of_equivalent`,
  `.addition_respects`, `.subtraction_respects`, `.multiplication_respects`,
  `.exponential_respects`, `.exponential_addition`,
  `.exponential_logarithm`, and `.logarithm_exponential`,
  `LogBranchGeometry.localLogNamed_respects`,
  `.SafeOverlapExtension.transport`, `.transport_productive`,
  `.transport_bitstream_and_error`,
  `.logarithm_product_of_alignment`,
  `.SelectedLogarithm.ofOverlap`,
  `.SelectedLogarithm.logarithm_exponential_inverse`, and
  `.SelectedLogarithm.logarithm_exponential_bitLaw`,
  `ProgressiveTaylorError.progressive_eval_error_le`,
  `.truncation_error_le`, `.TaylorJet.mul_evaluation_error`,
  `.TaylorJet.compose_evaluation_error`, and
  `.MultivariableFirstJet.directional_evaluation_error`,
  `FiniteIntegration.derivative_antiderivative`,
  `.definiteIntegral_factor`, `.definiteIntegral_reverse`,
  `.definiteIntegral_concat`, `.definiteIntegral_add`,
  `.definiteIntegral_scale`, `.integralKernel_diagonal`,
  `.polynomialIVPSolution_initial`, `.polynomialIVPSolution_derivative`, and
  `.exponentialODE_defect`,
  `ProgressiveIntegration.CellModel.weighted_error_le`,
  `.PathModel.weightedErrorSum_le`, `.PathModel.integralSample_concat`,
  `.PathModel.integralSample_scaleIntegrand`,
  `.PathModel.reverse_integralSample`,
  `.RefinementProgram.scale_integralSample`,
  `.RefinementProgram.add_integralSample`,
  `.RefinementProgram.concat_integralSample`,
  `.RefinementProgram.reverse_integralSample`,
  `.RefinementProgram.finite_subdivision_accurate`,
  `.RefinementProgram.output_bitstream_and_error`,
  `.RefinementProgram.exactPolynomial_equivalent_finiteIntegral`, and
  `.RefinementProgram.AntiderivativeProcess.ftc_equivalent`, and
  `LogExpInverse.logarithm_exponential_inverse`;
* finite logarithm branch calculus and geometric selection:
  `LogBranchCalculus.AnchoredChart.exponential_inverse`,
  `.exp_transition_unit`, `.exp_productBranchDiscrepancy_unit`,
  `.transition_self_zero`, `.transition_compose`,
  `.transition_reverse_zero`, and `.exp_transitionChain_unit`;
* finite certified expression and projective rational-function interfaces:
  `CertifiedExpression.Expression.refined_allowance_lt`,
  `.bitstream_and_error`,
  `FiniteGeometric.firstQuarterBelow_le`,
  `ProjectiveRationalEvaluation.horner_respects`,
  `.polynomialExpression_exact`, `.evaluate`, `.evaluate_exact`,
  `.ProjectiveEvaluation.affine`, and `.ProjectiveEvaluation.reciprocalAffine`;
* finite root families and branch-selected rational powers:
  `RootPowers.roots`,
  `RootPowers.RootFamily.occurrenceCount_eq_degree`,
  `RootPowers.promoteIfExact`,
  `RootPowers.derivedCandidates`,
  `RootPowers.exactRoot_mem_derivedCandidates`,
  `RootPowers.automaticExactRoots`,
  `RootPowers.ExactRootFamily.ofCandidates?`,
  `RootPowers.ExactRootFamily.automatic?`,
  `RootPowers.ExactRootFamily.containsDisplayed`,
  `RootPowers.squareRootsOfFour_exact`,
  `RootPowers.selectedRoot_power_reconstructs`, and
  `RootPowers.selectedRoot_power_to_naturalRationalPower`;
* the three printed exact examples: the paired `*_blocks` and `*_raw`
  declarations in `Examples`.

`scripts/check-axioms.sh` generates the corresponding kernel-executed audit
from every active project module, so new declarations require no manifest
maintenance.

The facade deliberately exports only the finite constructive implementation;
superseded parallel implementations are not part of the public dependency
graph.
-/
