import mathlib.Tactic.QuotientFreeOmega
import RFAP.Paper
import RFAP.Approximation.HurwitzLakein
import RFAP.Approximation.LocalSuccessor
import RFAP.Approximation.RATBestApproximation
import RFAP.Approximation.SuccessorDynamics
import RFAP.Approximation.DirichletChain
import RFAP.Approximation.FiniteWindowSharpness
import RFAP.Approximation.CriticalTwoWindow
import RFAP.Approximation.CriticalTwoWindowTower
import RFAP.Approximation.ErrorComparisonStability
import RFAP.Approximation.RobustCriticalCylinder
import RFAP.Approximation.RobustCriticalExterior
import RFAP.Approximation.CriticalBadWindowRun
import RFAP.Approximation.CriticalRunBox
import RFAP.Approximation.RobustCriticalRun
import RFAP.Approximation.RobustDynamicalSharpness
import RFAP.Approximation.RobustSuccessorSharpness
import RFAP.Approximation.FiniteDirichletGlobal
import RFAP.Polynomial.BestResidual
import RFAP.Polynomial.GaussianDenominatorHeight
import RFAP.Polynomial.DenominatorHeightSharp
import RFAP.Rational.DenominatorHeight
import RFAP.Approximation.CalculationSize

/-!
# RFAP denominator-height companion API

This facade contains the denominator-height calibration, finite best-residual
search, finite Hurwitz--Lakein comparison, and explicit finite
Dirichlet-window sharpness witnesses developed in the second RFAP paper.  It
deliberately imports the first paper's finite box and residual interface, then
adds only explicitly bounded approximation constructions.
-/

namespace RFAP.ApproximationPaper

abbrev Coordinate := RFAP.Paper.Coordinate
abbrev Gaussian := RFAP.Paper.Gaussian
abbrev GaussianPolynomial := RFAP.Paper.GaussianPolynomial
abbrev GaussianFraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev SquarefreeCertificate := RFAP.Paper.SquarefreeCertificate
abbrev LocalQuotientContext := RFAP.Paper.LocalQuotientContext
abbrev HurwitzFraction := RFAP.HurwitzRational.Fraction
abbrev ReducedHurwitzFraction :=
  RFAP.ReducedGaussianFraction.CanonicalFraction
abbrev HurwitzStage := RFAP.HurwitzTrace.Stage
abbrev HurwitzGenerated := RFAP.HurwitzGeometry.Generated
abbrev HurwitzConvergentPair := RFAP.HurwitzRational.ConvergentPair
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev WorkingGaussian := RFAP.NormalizedGaussian.Gaussian
abbrev StageTwoInput := RFAP.CalculationSize.StageTwoInput

/-- The positive integer scale obtained by clearing the finitely many
Gaussian-rational coefficients of a displayed polynomial. -/
def denominatorCoefficientScale (p : GaussianPolynomial) : Nat :=
  RFAP.DenominatorHeight.coefficientScale p

/-- Necessary denominator-height inequality for every displayed sample with
nonzero residual. -/
theorem one_le_scaled_height_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (p.eval fraction.value) :=
  RFAP.DenominatorHeight.one_le_scaled_height_mul_residual
    p nonzero fraction residualNonzero

/-- Exact integral identity behind the common-denominator lower bound. -/
theorem scaledHeightResidual_eq_integralNorm
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) :
    (denominatorCoefficientScale p : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ p.natDegree *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval fraction.value) =
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (RFAP.DenominatorHeight.residualNumerator p fraction) : Coordinate) :=
  RFAP.DenominatorHeight.scaled_height_mul_residual_eq_normNat
    p nonzero fraction

/-- Necessary denominator-height inequality for a displayed
Gaussian-integer numerator/denominator sample. -/
theorem one_le_scaled_gaussianHeight_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (p.eval fraction.value) :=
  RFAP.GaussianDenominatorHeight.one_le_scaled_height_mul_residual
    p nonzero fraction residualNonzero

/-- Execute Gaussian Euclidean reduction and deterministic unit
canonicalisation on a displayed Gaussian fraction. -/
def canonicalReducedGaussianFraction (fraction : HurwitzFraction) :
    ReducedHurwitzFraction :=
  RFAP.GaussianDenominatorHeight.canonicalReduction fraction

theorem canonicalReducedGaussianFraction_value (fraction : HurwitzFraction) :
    (canonicalReducedGaussianFraction fraction).value = fraction.value :=
  RFAP.GaussianDenominatorHeight.canonicalReduction_value fraction

/-- Presentation-independent denominator quadrance obtained by canonical
Gaussian Euclidean reduction. -/
def intrinsicGaussianDenominatorHeight (fraction : HurwitzFraction) : Nat :=
  RFAP.GaussianDenominatorHeight.intrinsicHeight fraction

theorem intrinsicGaussianDenominatorHeight_pos (fraction : HurwitzFraction) :
    0 < intrinsicGaussianDenominatorHeight fraction :=
  RFAP.GaussianDenominatorHeight.intrinsicHeight_pos fraction

theorem intrinsicGaussianDenominatorHeight_le_displayed
    (fraction : HurwitzFraction) :
    intrinsicGaussianDenominatorHeight fraction ≤ fraction.height :=
  RFAP.GaussianDenominatorHeight.intrinsicHeight_le_height fraction

theorem intrinsicGaussianDenominatorHeight_eq_of_value_eq
    (left right : HurwitzFraction) (valueEqual : left.value = right.value) :
    intrinsicGaussianDenominatorHeight left =
      intrinsicGaussianDenominatorHeight right :=
  RFAP.GaussianDenominatorHeight.intrinsicHeight_eq_of_value_eq
    left right valueEqual

/-- Exact integral identity behind the intrinsic reduced Gaussian-height
obstruction. -/
theorem scaledIntrinsicGaussianHeightResidual_eq_integralNorm
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction) :
    (denominatorCoefficientScale p : Coordinate) ^ 2 *
          (intrinsicGaussianDenominatorHeight fraction : Coordinate) ^
            p.natDegree *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval fraction.value) =
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (RFAP.GaussianDenominatorHeight.intrinsicResidualNumerator p
          fraction) : Coordinate) :=
  RFAP.GaussianDenominatorHeight.scaled_intrinsicHeight_mul_residual_eq_normNat
    p nonzero fraction

/-- Necessary residual inequality using presentation-independent canonical
reduced Gaussian-denominator height. -/
theorem one_le_scaled_intrinsicGaussianHeight_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : HurwitzFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale p : Coordinate) ^ 2 *
        (intrinsicGaussianDenominatorHeight fraction : Coordinate) ^
            p.natDegree *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (p.eval fraction.value) :=
  RFAP.GaussianDenominatorHeight.one_le_scaled_intrinsicHeight_mul_residual
    p nonzero fraction residualNonzero

/-- Explicit equality family showing joint sharpness of the unit constant,
coefficient-scale square, and degree-th power of displayed height. -/
theorem denominatorHeightBound_isSharp
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (denominatorCoefficientScale
        (RFAP.DenominatorHeightSharp.sharpPolynomial degree scale
          scalePositive) : Coordinate) ^ 2 *
          ((RFAP.DenominatorHeightSharp.sharpFraction denominator
            denominatorPositive).height : Coordinate) ^
            (RFAP.DenominatorHeightSharp.sharpPolynomial degree scale
              scalePositive).natDegree *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((RFAP.DenominatorHeightSharp.sharpPolynomial degree scale
            scalePositive).eval
              (RFAP.DenominatorHeightSharp.sharpFraction denominator
                denominatorPositive).value) = 1 :=
  RFAP.DenominatorHeightSharp.scaled_height_mul_residual_eq_one
    degree scale denominator scalePositive denominatorPositive

/-- Execute Newton-band extraction and return an interior Gaussian-rational
sample with its exact common-denominator height and residual bound. -/
def approximateWithHeight
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RFAP.RawSubdivision.RawWindingState p ambient)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    RFAP.HeightApproximation.Output degreeAtLeastTwo squarefree elimination
      current epsilon :=
  RFAP.HeightApproximation.approximate degreeAtLeastTwo squarefree elimination
    current epsilonPositive

/-- Execute Newton-band extraction with the square-root-scaled request for a
displayed positive residual target. -/
def approximateWithTarget
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RFAP.RawSubdivision.RawWindingState p ambient)
    (target : Coordinate) :
    RFAP.HeightApproximation.Output degreeAtLeastTwo squarefree elimination
      current
        (RFAP.HeightApproximation.targetEpsilon
          (2 * RFAP.PolynomialBounds.denseLipschitzBound p ambient) target) :=
  RFAP.HeightApproximation.approximateTarget degreeAtLeastTwo squarefree
    elimination current target

theorem approximateWithTarget_residual_le
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : RFAP.RawSubdivision.RawWindingState p ambient)
    {target : Coordinate} (targetPositive : 0 < target) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (p.eval (approximateWithTarget degreeAtLeastTwo squarefree elimination
        current target).fraction.value) ≤ target :=
  RFAP.HeightApproximation.approximateTarget_residual_le degreeAtLeastTwo
    squarefree elimination current targetPositive

/-- Exact finite minimization of residual over all displayed
common-denominator Gaussian fractions in the supplied numerator and
denominator window. -/
def bestResidualSample (p : GaussianPolynomial)
    (numeratorBound denominatorBound : Nat) : Option GaussianFraction :=
  RFAP.BestResidual.best p numeratorBound denominatorBound

theorem bestResidualSample_exists (p : GaussianPolynomial)
    (numeratorBound : Nat) {denominatorBound : Nat}
    (positive : 0 < denominatorBound) :
    ∃ selected,
      bestResidualSample p numeratorBound denominatorBound = some selected :=
  RFAP.BestResidual.best_exists p numeratorBound positive

theorem bestResidualSample_is_optimal
    {p : GaussianPolynomial} {numeratorBound denominatorBound : Nat}
    {selected candidate : GaussianFraction}
    (selection : bestResidualSample p numeratorBound denominatorBound =
      some selected)
    (realBound : candidate.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : candidate.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : candidate.denominator ≤ denominatorBound) :
    RFAP.BestResidual.score p selected ≤ RFAP.BestResidual.score p candidate :=
  RFAP.BestResidual.best_is_optimal selection realBound imaginaryBound
    denominatorBounded

/-- Construct the denominator-controlled residual sample for a protected
rational-function site.  Swapping source and opposite gives the pole result
for the reciprocal residual. -/
def approximateQuotientWithHeight
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon) :
    RFAP.RationalDenominatorHeight.Output context degreeAtLeastTwo squarefree
      elimination epsilon :=
  RFAP.RationalDenominatorHeight.approximate context degreeAtLeastTwo
    squarefree elimination epsilonPositive

/-- Protected quotient approximation with the corresponding square-root
target request. -/
def approximateQuotientWithTarget
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    (target : Coordinate) :
    RFAP.RationalDenominatorHeight.Output context degreeAtLeastTwo squarefree
      elimination
        (RFAP.HeightApproximation.targetEpsilon
          (RFAP.RationalDenominatorHeight.targetCoefficient context) target) :=
  RFAP.RationalDenominatorHeight.approximateTarget context degreeAtLeastTwo
    squarefree elimination target

theorem approximateQuotientWithTarget_residual_le
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (context : LocalQuotientContext source opposite ambient)
    (degreeAtLeastTwo : 2 ≤ source.natDegree)
    (squarefree : SquarefreeCertificate source)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate source degreeBound)
    {target : Coordinate} (targetPositive : 0 < target) :
    RFAP.Paper.quotientResidualSq source opposite
        (approximateQuotientWithTarget context degreeAtLeastTwo squarefree
          elimination target).polynomial.fraction.value ≤ target :=
  RFAP.RationalDenominatorHeight.approximateTarget_quotientResidual_le
    context degreeAtLeastTwo squarefree elimination targetPositive

/-- Necessary height inequality for a protected nonzero quotient residual.
At a pole, source and opposite are exchanged, so this is the reciprocal
residual inequality. -/
theorem one_le_scaled_height_mul_quotientResidual
    {source opposite : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (context : LocalQuotientContext source opposite ambient)
    {state : RFAP.ShrinkingTrack.WindingOneState source ambient}
    (refinesProtected : state.box.Refines context.protectedState.box)
    (fraction : GaussianFraction) (inside : state.box.Contains fraction.value)
    (sourceNonzero : source.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (denominatorCoefficientScale source : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ source.natDegree *
          context.oppositeMajorant *
            RFAP.Paper.quotientResidualSq source opposite fraction.value :=
  RFAP.RationalDenominatorHeight.one_le_scaled_height_mul_quotientResidual
    context refinesProtected fraction inside sourceNonzero

/-- Finite Lakein comparison for every displayed stage of the executable
Hurwitz expansion.  Any Gaussian-rational competitor with nonzero and
strictly smaller denominator has at least the current convergent's
division-free residual quadrance. -/
theorem hurwitzConvergent_atLeastAsGoodAs
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage)
    (competitor : HurwitzConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          competitor.denominator <
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          stage.current.denominator) :
    RFAP.HurwitzApproximation.AtLeastAsGoodAs
      source.value stage.current competitor :=
  RFAP.HurwitzGeometry.Stage.atLeastAsGoodAs_of_generated stage generated
    competitor competitorDenominatorNonzero denominatorSmaller

/-- The stronger unconditional description of the existing Lakein result:
every generated continuant is weakly best against all strictly smaller
denominators. -/
theorem hurwitzConvergent_isWeakLowerBest
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage) :
    RFAP.BestApproximation.IsWeakLowerBest source.value stage.current :=
  RFAP.HurwitzGeometry.Stage.isWeakLowerBest_of_generated stage generated

/-- At the terminal stage the exact Hurwitz continuant satisfies the full
strict/equal-height best-approximation predicate. -/
theorem terminalHurwitzConvergent_isBest
    {source : HurwitzFraction} (stage : HurwitzStage source)
    (generated : HurwitzGenerated source stage)
    (terminal : RFAP.HurwitzRational.remainder stage.quotient = 0) :
    RFAP.BestApproximation.IsBest source.value stage.current :=
  RFAP.HurwitzGeometry.Stage.isBest_of_generated_of_terminal
    stage generated terminal

/-- Execute the proved finite search for all best Gaussian-rational
approximations to a displayed rational source. -/
def allBestGaussianApproximations (source : HurwitzFraction) :
    List HurwitzConvergentPair :=
  RFAP.BestApproximation.allBest source

/-- The finite selector is both sound and complete for the full two-tier
best-approximation predicate. -/
theorem mem_allBestGaussianApproximations_iff
    (source : HurwitzFraction) (pair : HurwitzConvergentPair) :
    pair ∈ allBestGaussianApproximations source ↔
      RFAP.BestApproximation.IsBest source.value pair :=
  RFAP.BestApproximation.mem_allBest_iff_isBest source pair

/-- The all-best calculation always returns at least one pair; the terminal
Hurwitz continuant is an explicit witness. -/
theorem allBestGaussianApproximations_nonempty (source : HurwitzFraction) :
    allBestGaussianApproximations source ≠ [] :=
  RFAP.HurwitzGeometry.allBest_nonempty source

/-- Execute the finite all-best calculation on the certified rational sample
returned by one RAT response. -/
def ratResponseBestApproximations (sample : GaussianFraction) :
    List HurwitzConvergentPair :=
  RFAP.RATBestApproximation.bestApproximations sample

/-- The RAT-response calculation emits all and only full best approximants
to its displayed finite response point. -/
theorem mem_ratResponseBestApproximations_iff
    (sample : GaussianFraction) (pair : HurwitzConvergentPair) :
    pair ∈ ratResponseBestApproximations sample ↔
      RFAP.BestApproximation.IsBest sample.value pair :=
  RFAP.RATBestApproximation.mem_bestApproximations_iff sample pair

/-- A finite RAT response always computes at least one full best
approximant. -/
theorem ratResponseBestApproximations_nonempty (sample : GaussianFraction) :
    ratResponseBestApproximations sample ≠ [] :=
  RFAP.RATBestApproximation.bestApproximations_nonempty sample

/-- Deterministically select one representative of the next occupied best
level above a certified best RAT-response approximant. -/
def nextRATResponseBestApproximation?
    (sample : GaussianFraction) (lower : HurwitzConvergentPair) :
    Option HurwitzConvergentPair :=
  RFAP.RATBestApproximation.nextBestApproximation? sample lower

/-- Every pair emitted by the RAT-response step is genuinely consecutive
best; the algorithm cannot emit a merely provisional approximant. -/
theorem nextRATResponseBestApproximation?_sound
    {sample : GaussianFraction} {lower next : HurwitzConvergentPair}
    (selected :
      nextRATResponseBestApproximation? sample lower = some next) :
    RFAP.BestApproximation.AreConsecutiveBest
      sample.value lower next :=
  RFAP.RATBestApproximation.nextBestApproximation?_sound selected

/-- Total finite RAT-response step: produce the next consecutive best pair,
or certify that the current pair represents the response exactly. -/
theorem nextRATResponseBestApproximation_or_exactTerminal
    {sample : GaussianFraction} {lower : HurwitzConvergentPair}
    (lowerBest : RFAP.BestApproximation.IsBest sample.value lower) :
    (∃ next : HurwitzConvergentPair,
      nextRATResponseBestApproximation? sample lower = some next ∧
        RFAP.BestApproximation.AreConsecutiveBest
          sample.value lower next) ∨
      RFAP.BestApproximation.errorQuadrance sample.value lower = 0 :=
  RFAP.RATBestApproximation.nextBestApproximation_or_exactTerminal lowerBest

/-- Complete RFAP-II arithmetic response attached directly to one finite call
of any RFAP-I root-approximation track.  It retains the refined box, canonical
rational anchor, residual bound, all-and-only-best table, and total
next-best-or-terminal step. -/
def respondToRAT
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon) :
    RFAP.RATBestApproximation.TrackBestResponse
      degreePositive track current epsilon epsilonPositive :=
  RFAP.RATBestApproximation.respondToTrack degreePositive track current epsilon
    epsilonPositive

/-- Every member emitted by the combined RFAP-I/RFAP-II response is a full
best approximant to that response's displayed rational anchor. -/
theorem mem_respondToRAT_approximants_iff
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (pair : HurwitzConvergentPair) :
    pair ∈ (respondToRAT degreePositive track current epsilon
        epsilonPositive).approximants ↔
      RFAP.BestApproximation.IsBest
        (respondToRAT degreePositive track current epsilon
          epsilonPositive).sample.value pair :=
  (respondToRAT degreePositive track current epsilon
    epsilonPositive).memApproximantsIff pair

/-- Every best member of a combined RFAP-I/RFAP-II response has a computed
consecutive successor or an exact zero-error terminal certificate. -/
theorem respondToRAT_next_or_exactTerminal
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (lower : HurwitzConvergentPair)
    (lowerBest : RFAP.BestApproximation.IsBest
      (respondToRAT degreePositive track current epsilon
        epsilonPositive).sample.value lower) :
    (∃ next : HurwitzConvergentPair,
      (respondToRAT degreePositive track current epsilon
        epsilonPositive).next? lower = some next ∧
        RFAP.BestApproximation.AreConsecutiveBest
          (respondToRAT degreePositive track current epsilon
            epsilonPositive).sample.value lower next) ∨
      RFAP.BestApproximation.errorQuadrance
        (respondToRAT degreePositive track current epsilon
          epsilonPositive).sample.value lower = 0 :=
  (respondToRAT degreePositive track current epsilon
    epsilonPositive).nextOrTerminal lowerBest

/-- RFAP-II arithmetic capability carried by every branch of the positive
degree RFAP-I finite FTA.  A linear result has an exact-point response;
a higher result supports a complete best response at every finite call of
each returned degree-indexed RAT. -/
def FTAApproximationCapability
    {p : GaussianPolynomial} : RFAP.BoxFTA.PositiveResult p → Type
  | .linear root _ => RFAP.RATBestApproximation.PointBestResponse root.point
  | .higher boxes degree =>
      ∀ (index : Fin p.natDegree)
        (current : WindingOneState p (RFAP.GlobalWinding.largeSquareBox p))
        (epsilon : Coordinate) (epsilonPositive : 0 < epsilon),
        RFAP.RATBestApproximation.TrackBestResponse
          (by omega : 0 < p.natDegree)
          (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Construct the RFAP-II best-approximation capability for an arbitrary
positive-degree RFAP-I FTA result, branch by branch and without changing the
Paper-I facade. -/
def strengthenFTAResult
    {p : GaussianPolynomial} (result : RFAP.BoxFTA.PositiveResult p) :
    FTAApproximationCapability result := by
  cases result with
  | linear root degree =>
      exact RFAP.RATBestApproximation.respondToPoint root.point
  | higher boxes degree =>
      intro index current epsilon epsilonPositive
      exact RFAP.RATBestApproximation.respondToTrack (by omega)
        (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- RFAP-II arithmetic capability carried by one signed polynomial-factor
observation in the RFAP-I rational-function action principle.  Exact linear
sites use their displayed point; every higher site supports a best response
at each finite call of each returned RAT. -/
def RationalSiteApproximationCapability
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.RationalSites.PositiveContext input.entries} :
    RFAP.RationalSites.PositiveSideInput.FactorObservation input context → Type
  | .exact root _ _ =>
      RFAP.RATBestApproximation.PointBestResponse root.point
  | .higher boxes degree =>
      ∀ (index : Fin context.focus.part.polynomial.natDegree)
        (current : WindingOneState context.focus.part.polynomial
          (RFAP.GlobalWinding.largeSquareBox context.focus.part.polynomial))
        (epsilon : Coordinate) (epsilonPositive : 0 < epsilon),
        RFAP.RATBestApproximation.TrackBestResponse
          (by omega : 0 < context.focus.part.polynomial.natDegree)
          (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Construct the RFAP-II best-approximation capability for every exact or
higher-degree signed site returned by RFAP-I. -/
def strengthenRationalSite
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.RationalSites.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context) :
    RationalSiteApproximationCapability observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      exact RFAP.RATBestApproximation.respondToPoint root.point
  | higher boxes degree =>
      intro index current epsilon epsilonPositive
      exact RFAP.RATBestApproximation.respondToTrack (by omega)
        (boxes.isolation.trackAt index) current epsilon epsilonPositive

/-- Execute the finite successor calculation returning every best pair at the
next occupied denominator level above `lower`. -/
def consecutiveBestSuccessors
    (source : HurwitzFraction) (lower : HurwitzConvergentPair) :
    List HurwitzConvergentPair :=
  RFAP.BestApproximation.consecutiveSuccessors source lower

/-- Exact specification of the finite consecutive-minimal-vector successor
calculation. -/
theorem mem_consecutiveBestSuccessors_iff
    (source : HurwitzFraction) (lower candidate : HurwitzConvergentPair) :
    candidate ∈ consecutiveBestSuccessors source lower ↔
      RFAP.BestApproximation.AreConsecutiveBest
        source.value lower candidate :=
  RFAP.BestApproximation.mem_consecutiveSuccessors_iff
    source lower candidate

/-- Source/state-computed trailing-coefficient bound used by the local
successor generator. -/
def localSuccessorCoefficientBound
    (source : HurwitzFraction) (previous : HurwitzConvergentPair) : Nat :=
  RFAP.LocalSuccessor.trailingCoefficientBound source previous

/-- Execute the proved coefficient-local successor search from one supplied
adjacent best pair. -/
def localConsecutiveBestSuccessors
    (source : HurwitzFraction)
    (previous current : HurwitzConvergentPair) :
    List HurwitzConvergentPair :=
  RFAP.LocalSuccessor.successors source previous current

/-- The exact coefficient-local validation predicate used by the successor
calculation. -/
def passesLocalSuccessorTest
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair) : Prop :=
  RFAP.LocalSuccessor.PassesLocalSuccessorTest
    source previous current candidate

/-- The coefficient-local validation predicate is equivalent to occupying
the next best level, provided the supplied state is adjacent. -/
theorem passesLocalSuccessorTest_iff
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current) :
    passesLocalSuccessorTest source previous current candidate ↔
      RFAP.BestApproximation.AreConsecutiveBest
        source.value current candidate :=
  RFAP.LocalSuccessor.passesLocalSuccessorTest_iff first

/-- The coefficient-local successor calculation returns exactly the next
occupied best level and skips none, provided its input state is adjacent. -/
theorem mem_localConsecutiveBestSuccessors_iff
    (source : HurwitzFraction)
    (previous current candidate : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value previous current) :
    candidate ∈ localConsecutiveBestSuccessors source previous current ↔
      RFAP.BestApproximation.AreConsecutiveBest
        source.value current candidate :=
  RFAP.LocalSuccessor.mem_successors_iff first candidate

/-- Explicit size bound for the coefficient-local candidate list underlying
the successor calculation. -/
theorem localSuccessorCandidates_length_le
    (source : HurwitzFraction)
    (previous current : HurwitzConvergentPair) :
    (RFAP.LocalSuccessor.candidates source previous current).length ≤
      64 * (localSuccessorCoefficientBound source previous + 1) ^ 2 :=
  RFAP.LocalSuccessor.candidates_length_le source previous current

/-- Constructive local characterization of consecutive best levels by the
absence of a nonzero pair in their mixed open cylinder. -/
theorem consecutiveBest_iff_mixedCylinderEmpty
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) :
    RFAP.BestApproximation.AreConsecutiveBest source.value lower upper ↔
      RFAP.BestApproximation.IsBest source.value lower ∧
        RFAP.BestApproximation.IsBest source.value upper ∧
        RFAP.BestApproximation.denominatorQuadrance lower <
          RFAP.BestApproximation.denominatorQuadrance upper ∧
        RFAP.BestApproximation.MixedCylinderEmpty
          source.value lower upper :=
  RFAP.BestApproximation.areConsecutiveBest_iff_mixedCylinderEmpty
    source lower upper

/-- A bounded small-error pair descends by an executable finite minimization
to a genuine best pair of no greater height or error. -/
theorem exists_bestBelow_of_small
    (source : HurwitzFraction) (candidate : HurwitzConvergentPair)
    (candidateNonzero : candidate.denominator ≠ 0)
    (denominatorBounded :
      RFAP.BestApproximation.denominatorQuadrance candidate ≤
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          source.denominator)
    (smallError :
      RFAP.BestApproximation.errorQuadrance source.value candidate ≤ 1 / 2) :
    ∃ selected : HurwitzConvergentPair,
      RFAP.BestApproximation.IsBest source.value selected ∧
        RFAP.BestApproximation.denominatorQuadrance selected ≤
          RFAP.BestApproximation.denominatorQuadrance candidate ∧
        RFAP.BestApproximation.errorQuadrance source.value selected ≤
          RFAP.BestApproximation.errorQuadrance source.value candidate :=
  RFAP.BestApproximation.exists_best_below_of_small candidateNonzero
    denominatorBounded smallError

/-- Determinant quadrance of the coefficient sublattice spanned by two
displayed approximation pairs. -/
def coefficientIndexQuadrance
    (left right : HurwitzConvergentPair) : Nat :=
  RFAP.BestApproximation.coefficientIndexQuadrance left right

/-- Consecutive best levels are represented by coefficientwise independent
pairs, so their displayed determinant quadrance is positive. -/
theorem consecutiveBest_coefficientIndexQuadrance_pos
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    0 < coefficientIndexQuadrance lower upper :=
  consecutive.coefficientIndexQuadrance_pos

/-- Sharp constructive determinant classification for consecutive best
pairs over a displayed rational source. -/
theorem consecutiveBest_coefficientIndexQuadrance_eq_one_or_two
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    coefficientIndexQuadrance lower upper = 1 ∨
      coefficientIndexQuadrance lower upper = 2 :=
  consecutive.coefficientIndexQuadrance_eq_one_or_two

/-- Complete finite coefficient-coset classification of every ambient pair
relative to two consecutive best levels. -/
theorem consecutiveBest_coefficientSpan_or_centeredCoset
    (source : HurwitzFraction) (lower upper candidate : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    RFAP.BestApproximation.InCoefficientSpan lower upper candidate ∨
      RFAP.BestApproximation.InCenteredCoefficientCoset
        lower upper candidate :=
  consecutive.coefficientSpan_or_centeredCoset candidate

/-- In the index-two case any two nondivisible cleared coefficients construct
an ambient pair in the centered coset. -/
theorem consecutiveBest_exists_centeredCoefficientPair
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (leftCoefficient rightCoefficient :
      RFAP.ConstructiveGaussianHeight.GaussianInt)
    (leftNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (RFAP.BestApproximation.coefficientDeterminant lower upper)
          leftCoefficient)
    (rightNotDivisible :
      ¬ RFAP.GaussianCoset.Divides
        (RFAP.BestApproximation.coefficientDeterminant lower upper)
          rightCoefficient) :
    ∃ candidate : HurwitzConvergentPair,
      RFAP.BestApproximation.scalePair
          (RFAP.BestApproximation.coefficientDeterminant lower upper)
          candidate =
        RFAP.BestApproximation.linearCombination lower upper
          leftCoefficient rightCoefficient :=
  consecutive.exists_centeredCoefficientPair indexTwo
    leftCoefficient rightCoefficient leftNotDivisible rightNotDivisible

/-- Coefficient normal form for two consecutive index-two transitions. -/
theorem consecutiveBest_indexTwoTransition
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient :
        RFAP.ConstructiveGaussianHeight.GaussianInt,
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          lowerCoefficient = 1 ∧
      RFAP.GaussianCoset.Divides
        (RFAP.BestApproximation.coefficientDeterminant lower middle)
          middleCoefficient ∧
      upper = RFAP.BestApproximation.linearCombination lower middle
        lowerCoefficient middleCoefficient :=
  first.integralTransition_with_divisible_middleCoefficient second
    leftIndexTwo rightIndexTwo

/-- Uniform square-root-free error-ratio bound for an index-two consecutive
best pair. -/
theorem consecutiveBest_indexTwoErrorRatio
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    RFAP.BestApproximation.errorQuadrance source.value lower <
      4 * RFAP.BestApproximation.errorQuadrance source.value upper :=
  consecutive.errorQuadrance_lower_lt_four_mul_upper_of_index_two indexTwo

/-- Fully finite repeated-index normal form.  The Gaussian step is one of the
twelve nonzero integral values having quadrance one, two, or four. -/
theorem consecutiveBest_indexTwoFiniteTransition
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : RFAP.ConstructiveGaussianHeight.GaussianInt,
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat lowerUnit = 1 ∧
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat step = 1 ∨
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat step = 2 ∨
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat step = 4) ∧
      upper = RFAP.BestApproximation.linearCombination lower middle lowerUnit
        (RFAP.BestApproximation.coefficientDeterminant lower middle * step) :=
  first.repeatedIndexTwo_finiteNormalForm second leftIndexTwo rightIndexTwo

/-- Two successive consecutive best transitions cannot both have
coefficient-index quadrance two. -/
theorem consecutiveBest_repeatedIndexTwo_impossible
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : coefficientIndexQuadrance middle upper = 2) : False :=
  RFAP.RepeatedIndex.repeatedIndexTwo_impossible first second leftIndexTwo
    rightIndexTwo

/-- An index-two consecutive best transition is necessarily followed by an
index-one transition. -/
theorem consecutiveBest_nextIndex_eq_one_of_indexTwo
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (leftIndexTwo : coefficientIndexQuadrance lower middle = 2) :
    coefficientIndexQuadrance middle upper = 1 :=
  RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two first
    second leftIndexTwo

/-- Source-computed finite bound for the determinant quadrance of consecutive
best pairs. -/
theorem consecutiveBest_coefficientIndexQuadrance_le_sourceBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    coefficientIndexQuadrance lower upper ≤
      4 * RFAP.BestApproximation.numeratorQuadranceBound source *
        RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          source.denominator :=
  consecutive.coefficientIndexQuadrance_le_sourceBound

/-- Squared denominator--error product governing the finite request window
between two consecutive best levels. -/
def consecutiveDirichletWindowQuadrance
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) : Coordinate :=
  RFAP.BestApproximation.dirichletWindowQuadrance
    source.value lower upper

/-- One displayed coefficient-index quadrance for every adjacent pair in a
finite list of approximation records. -/
def consecutiveCoefficientIndexQuadrances
    (pairs : List HurwitzConvergentPair) : List Nat :=
  RFAP.DirichletChain.coefficientIndexQuadrances pairs

/-- One exact squared Dirichlet-window product for every adjacent pair in a
finite list of approximation records. -/
def consecutiveDirichletWindowQuadrances
    (source : HurwitzFraction)
    (pairs : List HurwitzConvergentPair) : List Coordinate :=
  RFAP.DirichletChain.dirichletWindowQuadrances source.value pairs

theorem consecutiveDirichletWindowQuadrances_length_eq_indexQuadrances_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair) :
    (consecutiveDirichletWindowQuadrances source pairs).length =
      (consecutiveCoefficientIndexQuadrances pairs).length :=
  RFAP.DirichletChain.dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
    source.value pairs

/-- The determinant index is strictly below four times the exact consecutive
window product. -/
theorem consecutiveBest_index_lt_four_mul_dirichletWindow
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (coefficientIndexQuadrance lower upper : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  consecutive.coefficientIndexQuadrance_lt_four_mul_dirichletWindow

/-- Every consecutive window product is strictly greater than one quarter,
in a division-free statement. -/
theorem one_lt_four_mul_consecutiveDirichletWindow
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (1 : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  consecutive.one_lt_four_mul_dirichletWindow

/-- An index-two consecutive window product is strictly greater than one
half, again stated without division. -/
theorem two_lt_four_mul_consecutiveDirichletWindow_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (2 : Coordinate) <
      4 * consecutiveDirichletWindowQuadrance source lower upper :=
  consecutive.two_lt_four_mul_dirichletWindow_of_indexTwo indexTwo

/-- Normalized determinant gap associated to two consecutive best levels. -/
def consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq
    (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
      RFAP.DirichletWindow.errorRatio source.value lower upper)

/-- Displayed refined normalized-gap threshold, exactly `35/408`. -/
def refinedNormalizedDeterminantGapThreshold : Coordinate :=
  RFAP.DirichletWindow.refinedGapThreshold

theorem refinedNormalizedDeterminantGapThreshold_lt_half :
    refinedNormalizedDeterminantGapThreshold < (1 / 2 : Coordinate) :=
  RFAP.DirichletWindow.refinedGapThreshold_lt_half

theorem refinedNormalizedDeterminantGapThreshold_quadratic_nonnegative :
    0 ≤ refinedNormalizedDeterminantGapThreshold ^ 2 -
      3 * refinedNormalizedDeterminantGapThreshold + 1 / 4 :=
  RFAP.DirichletWindow.refinedGapThreshold_quadratic_nonnegative

theorem refinedNormalizedDeterminantGapThreshold_mul_denominator :
    refinedNormalizedDeterminantGapThreshold * 408 = 35 :=
  RFAP.DirichletWindow.refinedGapThreshold_mul_denominator

/-- Displayed refined universal squared-window bound, exactly `816/35`. -/
def refinedUniversalDirichletWindowBound : Coordinate :=
  RFAP.DirichletWindow.refinedUniversalWindowBound

/-- Displayed factor `408/35` multiplying one coefficient index in the
refined squared-window bound. -/
def refinedIndexDirichletWindowFactor : Coordinate :=
  RFAP.DirichletWindow.refinedIndexFactor

theorem refinedIndexDirichletWindowFactor_mul_denominator :
    refinedIndexDirichletWindowFactor * 35 = 408 :=
  RFAP.DirichletWindow.refinedIndexFactor_mul_denominator

theorem refinedUniversalDirichletWindowBound_mul_denominator :
    refinedUniversalDirichletWindowBound * 35 = 816 :=
  RFAP.DirichletWindow.refinedUniversalWindowBound_mul_denominator

/-- Displayed quadratic-boundary threshold, exactly `102/1189`. -/
def quadraticNormalizedDeterminantGapThreshold : Coordinate :=
  RFAP.DirichletWindow.quadraticGapThreshold

/-- Exact reciprocal factor `1189/102` for the quadratic-boundary threshold. -/
def quadraticIndexDirichletWindowFactor : Coordinate :=
  RFAP.DirichletWindow.quadraticIndexFactor

/-- Index-aware universal squared-window bound, exactly `1189/102`. -/
def indexAwareUniversalDirichletWindowBound : Coordinate :=
  RFAP.DirichletWindow.quadraticIndexFactor

/-- Centered index-two normalized determinant-gap bound, exactly `71/56`. -/
def centeredIndexTwoNormalizedDeterminantGap : Coordinate :=
  RFAP.IndexTwoWindow.centeredGapThreshold

theorem centeredIndexTwoNormalizedDeterminantGap_mul_denominator :
    centeredIndexTwoNormalizedDeterminantGap * 56 = 71 :=
  RFAP.IndexTwoWindow.centeredGapThreshold_mul_denominator

/-- Centered index-two squared-window bound, exactly `112/71`. -/
def centeredIndexTwoDirichletWindowBound : Coordinate :=
  RFAP.IndexTwoWindow.centeredWindowBound

theorem centeredIndexTwoDirichletWindowBound_mul_denominator :
    centeredIndexTwoDirichletWindowBound * 71 = 112 :=
  RFAP.IndexTwoWindow.centeredWindowBound_mul_denominator

/-- Finite-octant universal squared-window bound, exactly `112/71`. -/
def finiteOctantUniversalDirichletWindowBound : Coordinate :=
  RFAP.IndexOneWindow.normTwoIndexOneWindowBound

theorem finiteOctantUniversalDirichletWindowBound_mul_denominator :
    finiteOctantUniversalDirichletWindowBound * 71 = 112 :=
  RFAP.IndexOneWindow.normTwoIndexOneWindowBound_mul_denominator

/-- Improved finite-octant normalized-gap certificate, exactly `71/112`. -/
def finiteOctantNormalizedDeterminantGap : Coordinate :=
  RFAP.IndexOneWindow.normTwoIndexOneGapThreshold

theorem finiteOctantNormalizedDeterminantGap_mul_denominator :
    finiteOctantNormalizedDeterminantGap * 112 = 71 :=
  RFAP.IndexOneWindow.normTwoIndexOneGapThreshold_mul_denominator

/-- Improved determinant-index-one squared-window bound, exactly `112/71`. -/
def finiteOctantIndexOneDirichletWindowBound : Coordinate :=
  RFAP.IndexOneWindow.normTwoIndexOneWindowBound

theorem finiteOctantIndexOneDirichletWindowBound_mul_denominator :
    finiteOctantIndexOneDirichletWindowBound * 71 = 112 :=
  RFAP.IndexOneWindow.normTwoIndexOneWindowBound_mul_denominator

/-- Near-optimal dyadic base gap, exactly `205/256`. -/
def dyadicNormalizedDeterminantGap : Coordinate :=
  RFAP.IndexOneWindow.sharpIndexOneGapBound

theorem dyadicNormalizedDeterminantGap_mul_denominator :
    dyadicNormalizedDeterminantGap * (2 : Coordinate) ^ 8 =
      13 * 16 - 3 :=
  RFAP.IndexOneWindow.sharpIndexOneGapBound_mul_denominator

/-- Matching determinant-index-two gap, exactly `205/128`. -/
def dyadicCenteredIndexTwoNormalizedDeterminantGap : Coordinate :=
  RFAP.IndexTwoWindow.dyadicCenteredGapThreshold

/-- Near-optimal dyadic universal squared-window bound, exactly `256/205`. -/
def dyadicUniversalDirichletWindowBound : Coordinate :=
  RFAP.IndexOneWindow.sharpIndexOneWindowBound

theorem dyadicUniversalDirichletWindowBound_mul_denominator :
    dyadicUniversalDirichletWindowBound * (13 * 16 - 3 : Coordinate) =
      (2 : Coordinate) ^ 8 :=
  RFAP.IndexOneWindow.sharpIndexOneWindowBound_mul_denominator

/-- Universal squared-window bound obtained from the quadratic gap alone,
exactly `1189/51`. -/
def quadraticUniversalDirichletWindowBound : Coordinate :=
  RFAP.DirichletWindow.quadraticUniversalWindowBound

theorem quadraticNormalizedDeterminantGapThreshold_lt_half :
    quadraticNormalizedDeterminantGapThreshold < (1 / 2 : Coordinate) :=
  RFAP.DirichletWindow.quadraticGapThreshold_lt_half

theorem quadraticNormalizedDeterminantGapThreshold_quadratic_nonnegative :
    0 ≤ quadraticNormalizedDeterminantGapThreshold ^ 2 -
      3 * quadraticNormalizedDeterminantGapThreshold + 1 / 4 :=
  RFAP.DirichletWindow.quadraticGapThreshold_quadratic_nonnegative

theorem quadraticNormalizedDeterminantGapThreshold_integerCertificate :
    (4 * 102 ^ 2 - 12 * 102 * 1189 + 1189 ^ 2 : Int) = 1 :=
  RFAP.DirichletWindow.quadraticGapThreshold_integerCertificate

theorem quadraticUniversalDirichletWindowBound_mul_denominator :
    quadraticUniversalDirichletWindowBound * 51 = 1189 :=
  RFAP.DirichletWindow.quadraticUniversalWindowBound_mul_denominator

theorem indexAwareUniversalDirichletWindowBound_mul_denominator :
    indexAwareUniversalDirichletWindowBound * 102 = 1189 :=
  RFAP.IndexTwoWindow.quadraticIndexFactor_mul_denominator

theorem quadraticUniversalDirichletWindowBound_lt_refined :
    quadraticUniversalDirichletWindowBound <
      refinedUniversalDirichletWindowBound :=
  RFAP.DirichletWindow.quadraticUniversalWindowBound_lt_refinedUniversalWindowBound

/-- Displayed refined bound `1224/35` for the sum of two successive squared
Dirichlet-window products. -/
def refinedTwoWindowDirichletSumBound : Coordinate :=
  RFAP.DirichletBlock.refinedTwoWindowSumBound

theorem refinedTwoWindowDirichletSumBound_mul_denominator :
    refinedTwoWindowDirichletSumBound * 35 = 1224 :=
  RFAP.DirichletBlock.refinedTwoWindowSumBound_mul_denominator

/-- Sharper displayed bound `1189/34` for the sum of two successive squared
Dirichlet-window products. -/
def quadraticTwoWindowDirichletSumBound : Coordinate :=
  RFAP.DirichletBlock.quadraticTwoWindowSumBound

theorem quadraticTwoWindowDirichletSumBound_mul_denominator :
    quadraticTwoWindowDirichletSumBound * 34 = 1189 :=
  RFAP.DirichletBlock.quadraticTwoWindowSumBound_mul_denominator

/-- Improved finite-octant bound `224/71` for the sum of two successive
squared Dirichlet-window products. -/
def finiteOctantTwoWindowDirichletSumBound : Coordinate :=
  RFAP.DirichletBlock.finiteOctantTwoWindowSumBound

theorem finiteOctantTwoWindowDirichletSumBound_mul_denominator :
    finiteOctantTwoWindowDirichletSumBound * 71 = 224 :=
  RFAP.DirichletBlock.finiteOctantTwoWindowSumBound_mul_denominator

/-- Near-optimal dyadic bound `512/205` for the sum of two successive
squared Dirichlet-window products. -/
def dyadicTwoWindowDirichletSumBound : Coordinate :=
  RFAP.DirichletBlock.dyadicTwoWindowSumBound

theorem dyadicTwoWindowDirichletSumBound_mul_denominator :
    dyadicTwoWindowDirichletSumBound * 205 = 512 :=
  RFAP.DirichletBlock.dyadicTwoWindowSumBound_mul_denominator

/-- The normalized determinant gap of consecutive best levels is at least
`1/12`. -/
theorem one_twelfth_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (1 / 12 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.DirichletWindow.AreConsecutiveBest.one_twelfth_le_normalizedDeterminantGap
    consecutive

/-- The three neighbouring coefficients in the finite octant containing the
normalized error ratio force a determinant gap of at least one half. -/
theorem half_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexOneWindow.AreConsecutiveBest.half_le_normalizedDeterminantGap
    consecutive

/-- The exact finite chamber calculation with the norm-two leading
coefficient strengthens the normalized gap to the displayed rational
`71/112`. -/
theorem finiteOctantGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    finiteOctantNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexOneWindow.AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
    consecutive

/-- The five-obstruction chamber forces every consecutive normalized gap
above the near-optimal dyadic base value `205/256`. -/
theorem dyadicGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    dyadicNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexOneWindow.AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
    consecutive

/-- In determinant index two, the oriented centered chamber forces the
matching dyadic gap `205/128`. -/
theorem dyadicCenteredIndexTwoGap_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    dyadicCenteredIndexTwoNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexOneWindow.AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- Exact root-free index-two gap family.  Every displayed rational `gap`
between `3/4` and the smaller quadratic boundary gives the lower bound
`2 * gap`, without constructing the boundary as a completed value. -/
theorem twice_gapThreshold_le_consecutiveNormalizedDeterminantGap_of_indexTwo
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    2 * gap ≤ consecutiveNormalizedDeterminantGap source lower upper := by
  exact
    RFAP.IndexOneWindow.AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold RFAP.OptimalIndexOneWindow.gapPolynomial
        exact quadraticNonnegative⟩ consecutive indexTwo

/-- The explicit `12,5` weighted certificate sharpens the normalized gap to
the displayed rational `35/408`. -/
theorem refinedThreshold_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    refinedNormalizedDeterminantGapThreshold ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.DirichletWindow.AreConsecutiveBest.refinedGap_le_normalizedDeterminantGap
    consecutive

/-- The rational boundary certificate `102/1189` is a sharper lower bound
for the normalized determinant gap. -/
theorem quadraticThreshold_le_consecutiveNormalizedDeterminantGap
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    quadraticNormalizedDeterminantGapThreshold ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.DirichletWindow.AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    consecutive quadraticNormalizedDeterminantGapThreshold
      quadraticNormalizedDeterminantGapThreshold_lt_half
      quadraticNormalizedDeterminantGapThreshold_quadratic_nonnegative

/-- Root-free exact boundary for the normalized consecutive determinant gap:
it is at least one half, or it satisfies the displayed rational quadratic
inequality. -/
theorem consecutiveNormalizedDeterminantGap_boundary
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Coordinate) ≤
        consecutiveNormalizedDeterminantGap source lower upper ∨
      consecutiveNormalizedDeterminantGap source lower upper ^ 2 -
          3 * consecutiveNormalizedDeterminantGap source lower upper +
        1 / 4 < 0 :=
  RFAP.DirichletWindow.AreConsecutiveBest.normalizedDeterminantGap_boundary
    consecutive

/-- Certify any displayed rational normalized-gap threshold below one half by
checking that its boundary polynomial is nonnegative. -/
theorem threshold_le_consecutiveNormalizedDeterminantGap_of_quadratic
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold ≤ consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.DirichletWindow.AreConsecutiveBest.threshold_le_normalizedDeterminantGap_of_quadratic
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Direct division-free window bound furnished by any displayed rational
threshold passing the quadratic test. -/
theorem quadraticThreshold_mul_consecutiveDirichletWindow_le_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower upper ≤
      (coefficientIndexQuadrance lower upper : Coordinate) :=
  RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Universal division-free form of the quadratic-threshold window bound. -/
theorem quadraticThreshold_mul_consecutiveDirichletWindow_le_two
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_two
    consecutive threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- The exact window product times its normalized determinant gap equals the
coefficient-index quadrance. -/
theorem consecutiveDirichletWindow_mul_normalizedGap_eq_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper *
        consecutiveNormalizedDeterminantGap source lower upper =
      (coefficientIndexQuadrance lower upper : Coordinate) :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindow_mul_normalizedGap_eq_index
    consecutive

/-- A consecutive squared Dirichlet-window product is at most twelve times
its coefficient-index quadrance. -/
theorem consecutiveBest_dirichletWindow_le_twelve_mul_index
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      12 * (coefficientIndexQuadrance lower upper : Coordinate) :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_twelve_mul_index
    consecutive

/-- Every consecutive squared Dirichlet-window product is at most `24`,
independently of the displayed source. -/
theorem consecutiveBest_dirichletWindow_le_twentyFour
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 24 :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyFour
    consecutive

/-- Every consecutive squared Dirichlet-window product is at most the
displayed rational `816/35`, independently of the source. -/
theorem consecutiveBest_dirichletWindow_le_refinedUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      refinedUniversalDirichletWindowBound :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedUniversalBound
    consecutive

/-- The quadratic-boundary certificate bounds a consecutive squared window
by `1189/102` times its coefficient-index quadrance. -/
theorem consecutiveBest_dirichletWindow_le_quadraticIndexFactor
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticIndexDirichletWindowFactor *
        (coefficientIndexQuadrance lower upper : Coordinate) :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
    consecutive

/-- In determinant index two, the centered coefficient coset forces the
normalized determinant gap to be at least `71/56`. -/
theorem centeredIndexTwoNormalizedDeterminantGap_le_consecutive
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    centeredIndexTwoNormalizedDeterminantGap ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexTwoWindow.AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- Compatibility form of the strengthened centered index-two gap. -/
theorem one_le_consecutiveNormalizedDeterminantGap_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (1 : Coordinate) ≤
      consecutiveNormalizedDeterminantGap source lower upper :=
  RFAP.IndexTwoWindow.AreConsecutiveBest.one_le_normalizedDeterminantGap_of_indexTwo
    consecutive indexTwo

/-- A determinant-index-two consecutive squared window is at most
`112/71`. -/
theorem consecutiveBest_dirichletWindow_le_centeredIndexTwoBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      centeredIndexTwoDirichletWindowBound :=
  RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
    consecutive indexTwo

/-- Compatibility form of the strengthened index-two window bound. -/
theorem consecutiveBest_dirichletWindow_le_two_of_indexTwo
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexTwo
    consecutive indexTwo

/-- A determinant-index-one consecutive squared window is at most `2`. -/
theorem consecutiveBest_dirichletWindow_le_two_of_indexOne
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne : coefficientIndexQuadrance lower upper = 1) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 2 :=
  RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexOne
    consecutive indexOne

/-- A determinant-index-one consecutive squared window is at most the
displayed rational `112/71`. -/
theorem consecutiveBest_dirichletWindow_le_finiteOctantIndexOneBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne : coefficientIndexQuadrance lower upper = 1) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      finiteOctantIndexOneDirichletWindowBound :=
  RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
    consecutive indexOne

/-- Finite-octant source-independent squared-window bound `112/71`. -/
theorem consecutiveBest_dirichletWindow_le_finiteOctantUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      finiteOctantUniversalDirichletWindowBound :=
  RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
    consecutive

/-- Near-optimal dyadic source-independent squared-window bound `256/205`. -/
theorem consecutiveBest_dirichletWindow_le_dyadicUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      dyadicUniversalDirichletWindowBound :=
  RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
    consecutive

/-- Exact root-free universal Dirichlet-window family.  Every displayed
rational `gap` satisfying the three finite inequalities gives
`gap * window <= 1`; such cuts approach the optimal quadratic boundary from
inside the displayed rational arithmetic. -/
theorem gapThreshold_mul_consecutiveDirichletWindow_le_one
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    gap * consecutiveDirichletWindowQuadrance source lower upper ≤ 1 := by
  exact RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
    gap ⟨threeFourthsLe, gapLtOne, by
      unfold RFAP.OptimalIndexOneWindow.gapPolynomial
      exact quadraticNonnegative⟩ consecutive

/-! ## Finite sharpness beyond every requested scale -/

/-- Executable Pell stage selected for a proposed sharper rational threshold
and a requested finite scale. -/
def finiteSharpnessStage (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  RFAP.FiniteWindowSharpness.sharpnessStage threshold requestedScale

/-- Displayed rational source computed at the selected sharpness stage. -/
def finiteSharpnessSource (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzFraction :=
  RFAP.FiniteWindowSharpness.criticalSource
    (finiteSharpnessStage threshold requestedScale)

/-- Lower endpoint of the selected consecutive-best window. -/
def finiteSharpnessLowerPair (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzConvergentPair :=
  RFAP.FiniteWindowSharpness.criticalLowerPair
    (finiteSharpnessStage threshold requestedScale)

/-- Upper endpoint of the selected consecutive-best window. -/
def finiteSharpnessUpperPair (threshold : Coordinate) (requestedScale : Nat) :
    HurwitzConvergentPair :=
  RFAP.FiniteWindowSharpness.criticalUpperPair
    (finiteSharpnessStage threshold requestedScale)

/-- Actual upper-pair denominator quadrance of the explicit critical window. -/
def finiteSharpnessDenominatorScale
    (threshold : Coordinate) (requestedScale : Nat) : Nat :=
  RFAP.BestApproximation.denominatorQuadrance
    (finiteSharpnessUpperPair threshold requestedScale)

/-- Finite constructive sharpness of the rational-cut window theorem.  If a
displayed threshold is on the sharper side of the omitted quadratic boundary,
then beyond every requested finite scale the executable Pell construction
returns a displayed rational source and consecutive best pair for which that
threshold would make the universal window inequality false.  The source is
allowed to depend on the requested scale. -/
theorem sharperGapThreshold_has_finiteCounterexample
    (threshold : Coordinate)
    (threeFourthsLe : (3 / 4 : Coordinate) ≤ threshold)
    (thresholdLtOne : threshold < 1)
    (quadraticNegative : threshold ^ 2 - 12 * threshold + 9 < 0)
    (requestedScale : Nat) :
    requestedScale <
        finiteSharpnessDenominatorScale threshold requestedScale ∧
      RFAP.BestApproximation.AreConsecutiveBest
        (finiteSharpnessSource threshold requestedScale).value
        (finiteSharpnessLowerPair threshold requestedScale)
        (finiteSharpnessUpperPair threshold requestedScale) ∧
      1 < threshold *
        consecutiveDirichletWindowQuadrance
          (finiteSharpnessSource threshold requestedScale)
          (finiteSharpnessLowerPair threshold requestedScale)
          (finiteSharpnessUpperPair threshold requestedScale) := by
  have certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold := by
    exact ⟨threeFourthsLe, thresholdLtOne, by
      unfold RFAP.FiniteWindowSharpness.windowBoundaryPolynomial
      exact quadraticNegative⟩
  simpa only [finiteSharpnessStage, finiteSharpnessSource,
    finiteSharpnessLowerPair, finiteSharpnessUpperPair,
    finiteSharpnessDenominatorScale, consecutiveDirichletWindowQuadrance] using
      RFAP.FiniteWindowSharpness.finiteCriticalWindowSharpness
        certificate requestedScale

/-- Public result type for an arbitrary finite same-source sharpness run and
one rational box on which every selected window remains valid. -/
abbrev RobustFiniteSharpnessRun
    (threshold : Coordinate) (requestedScale count : Nat) :=
  RFAP.RobustCriticalRun.FullyRobustRun
    threshold requestedScale count

/-- Compute exactly the requested finite number of strictly scale-increasing
bad windows at one displayed source, together with one proper rational box
on which their consecutive-best and strict-violation certificates hold
uniformly. -/
def robustFiniteSharpnessRun
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    RobustFiniteSharpnessRun threshold requestedScale count :=
  RFAP.RobustCriticalRun.criticalFullyRobustRun
    certificate requestedScale count

/-- Index-aware source-independent squared-window bound `1189/102`. -/
theorem consecutiveBest_dirichletWindow_le_indexAwareUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      indexAwareUniversalDirichletWindowBound :=
  RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
    consecutive

/-- Quadratic-gap-only source-independent squared-window bound `1189/51`. -/
theorem consecutiveBest_dirichletWindow_le_quadraticUniversalBound
    (source : HurwitzFraction)
    (lower upper : HurwitzConvergentPair)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticUniversalDirichletWindowBound :=
  RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticUniversalBound
    consecutive

/-- The coefficient-index quadrances of two successive consecutive best
transitions have sum at most three. -/
theorem successiveBest_coefficientIndexQuadrance_add_le_three
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    coefficientIndexQuadrance lower middle +
        coefficientIndexQuadrance middle upper ≤ 3 :=
  RFAP.DirichletBlock.coefficientIndexQuadrance_add_le_three first second

/-- For every displayed rational threshold passing the quadratic test, one
of two successive windows satisfies the scaled index-one bound. -/
theorem quadraticThreshold_mul_one_successiveDirichletWindow_le_one
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * consecutiveDirichletWindowQuadrance source lower middle ≤ 1 ∨
      threshold * consecutiveDirichletWindowQuadrance source middle upper ≤ 1 :=
  RFAP.DirichletBlock.quadraticThreshold_mul_one_dirichletWindow_le_one
    first second threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Parameterized two-window certificate: every rational threshold passing
the quadratic test times the sum of two successive windows is at most three. -/
theorem quadraticThreshold_mul_successiveDirichletWindowSum_le_three
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold *
        (consecutiveDirichletWindowQuadrance source lower middle +
          consecutiveDirichletWindowQuadrance source middle upper) ≤ 3 :=
  RFAP.DirichletBlock.quadraticThreshold_mul_dirichletWindowSum_le_three
    first second threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Exact root-free two-window family: every displayed rational passing the
optimal quadratic test scales two successive windows by at most two. -/
theorem gapThreshold_mul_successiveDirichletWindowSum_le_two
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    gap * (consecutiveDirichletWindowQuadrance source lower middle +
      consecutiveDirichletWindowQuadrance source middle upper) ≤ 2 := by
  exact
    RFAP.DirichletBlock.gapThreshold_mul_dirichletWindowQuadrance_add_le_two
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold RFAP.OptimalIndexOneWindow.gapPolynomial
        exact quadraticNonnegative⟩ first second

/-- Among two successive consecutive best transitions, at least one squared
window satisfies the index-one bound `408/35`. -/
theorem successiveBest_one_dirichletWindow_le_refinedIndexFactor
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle ≤
        refinedIndexDirichletWindowFactor ∨
      consecutiveDirichletWindowQuadrance source middle upper ≤
        refinedIndexDirichletWindowFactor :=
  RFAP.DirichletBlock.one_dirichletWindowQuadrance_le_refinedIndexFactor
    first second

/-- Two successive squared Dirichlet-window products have sum at most the
displayed rational `1224/35`. -/
theorem successiveBest_dirichletWindow_add_le_refinedTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      refinedTwoWindowDirichletSumBound :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_refinedTwoWindowSumBound
    first second

/-- Among two successive transitions, one squared window satisfies the
sharper index-one bound `1189/102`. -/
theorem successiveBest_one_dirichletWindow_le_quadraticIndexFactor
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle ≤
        quadraticIndexDirichletWindowFactor ∨
      consecutiveDirichletWindowQuadrance source middle upper ≤
        quadraticIndexDirichletWindowFactor :=
  RFAP.DirichletBlock.one_dirichletWindowQuadrance_le_quadraticIndexFactor
    first second

/-- Sharper two-window sum bound `1189/34`. -/
theorem successiveBest_dirichletWindow_add_le_quadraticTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      quadraticTwoWindowDirichletSumBound :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_quadraticTwoWindowSumBound
    first second

/-- Index-aware two-window sum bound `1189/51`. -/
theorem successiveBest_dirichletWindow_add_le_indexAwareTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      quadraticUniversalDirichletWindowBound :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_quadraticUniversalWindowBound
    first second

/-- Improved finite-octant two-window sum bound `224/71`. -/
theorem successiveBest_dirichletWindow_add_le_finiteOctantTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      finiteOctantTwoWindowDirichletSumBound :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_finiteOctantTwoWindowSumBound
    first second

/-- Near-optimal dyadic two-window sum bound `512/205`. -/
theorem successiveBest_dirichletWindow_add_le_dyadicTwoWindowSumBound
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤
      dyadicTwoWindowDirichletSumBound :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_dyadicTwoWindowSumBound
    first second

/-- Finite-octant two-window sum bound `4`. -/
theorem successiveBest_dirichletWindow_add_le_four
    (source : HurwitzFraction)
    (lower middle upper : HurwitzConvergentPair)
    (first : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower middle)
    (second : RFAP.BestApproximation.AreConsecutiveBest
      source.value middle upper) :
    consecutiveDirichletWindowQuadrance source lower middle +
        consecutiveDirichletWindowQuadrance source middle upper ≤ 4 :=
  RFAP.DirichletBlock.dirichletWindowQuadrance_add_le_four first second

/-- Exact parity-sensitive form of the alternating index-two pattern along a
finite displayed chain. -/
theorem finiteBestChain_two_mul_coefficientIndexQuadrances_sum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    2 * (consecutiveCoefficientIndexQuadrances pairs).sum ≤
      3 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 :=
  RFAP.DirichletChain.two_mul_coefficientIndexQuadrances_sum_le_with_parity
    pairs chain

/-- Parity-free consequence of the finite-chain index bound. -/
theorem finiteBestChain_two_mul_coefficientIndexQuadrances_sum_le
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    2 * (consecutiveCoefficientIndexQuadrances pairs).sum ≤
      3 * (consecutiveCoefficientIndexQuadrances pairs).length + 1 :=
  RFAP.DirichletChain.two_mul_coefficientIndexQuadrances_sum_le pairs chain

/-- The quadratic threshold times the total exact window cost of a finite
displayed chain is at most its computed coefficient-index sum. -/
theorem finiteBestChain_quadraticThreshold_mul_windowSum_le_indexSum
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      ((consecutiveCoefficientIndexQuadrances pairs).sum : Coordinate) :=
  RFAP.DirichletChain.quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Uniform division-free finite-chain certificate obtained by combining the
quadratic threshold with exclusion of successive index two. -/
theorem finiteBestChain_two_mul_quadraticThreshold_mul_windowSum_le
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold *
        (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (3 * (consecutiveCoefficientIndexQuadrances pairs).length + 1 : Nat) :=
  RFAP.DirichletChain.two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Exact parity-sensitive finite-chain window certificate. -/
theorem finiteBestChain_two_mul_quadraticThreshold_mul_windowSum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold *
        (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  RFAP.DirichletChain.two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_with_parity
    pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative

/-- Concrete sharp finite-chain bound obtained from the certified threshold
`35/408` and its exact reciprocal factor `408/35`. -/
theorem finiteBestChain_two_mul_windowSum_le_refinedIndexFactor_mul_parityBound
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    2 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      refinedIndexDirichletWindowFactor *
        (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
          (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  RFAP.DirichletChain.two_mul_dirichletWindowQuadrances_sum_le_refinedIndexFactor_mul_parityBound
    pairs chain

/-- Sharper concrete finite-chain bound obtained from threshold `102/1189`
and reciprocal factor `1189/102`. -/
theorem finiteBestChain_two_mul_windowSum_le_quadraticIndexFactor_mul_parityBound
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    2 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      quadraticIndexDirichletWindowFactor *
        (3 * (consecutiveCoefficientIndexQuadrances pairs).length +
          (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  RFAP.DirichletChain.two_mul_dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_parityBound
    pairs chain

/-- Direct accumulated index-aware bound: each transition in the supplied
finite chain contributes at most `1189/102`. -/
theorem finiteBestChain_windowSum_le_indexAwareUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      indexAwareUniversalDirichletWindowBound *
        ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  RFAP.DirichletChain.dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
    pairs chain

/-- Direct accumulated finite-octant bound: each transition contributes at
most the universal rational `112/71`. -/
theorem finiteBestChain_windowSum_le_finiteOctantUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      finiteOctantUniversalDirichletWindowBound *
        ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  RFAP.DirichletChain.dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
    pairs chain

/-- The near-optimal dyadic bound accumulates along every supplied finite
chain of consecutive best pairs. -/
theorem finiteBestChain_windowSum_le_dyadicUniversalBound_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    (RFAP.DirichletChain.dirichletWindowQuadrances
        source.value pairs).sum ≤
      dyadicUniversalDirichletWindowBound *
        ((RFAP.DirichletChain.coefficientIndexQuadrances pairs).length :
          Coordinate) :=
  RFAP.DirichletChain.dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
    pairs chain

/-- Exact root-free finite-chain family: the displayed gap times the window
sum is at most the number of supplied transitions. -/
theorem gapThreshold_mul_finiteBestChain_windowSum_le_length
    (gap : Coordinate) (threeFourthsLe : (3 / 4 : Coordinate) ≤ gap)
    (gapLtOne : gap < 1)
    (quadraticNonnegative : 0 ≤ gap ^ 2 - 12 * gap + 9)
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    gap * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) := by
  exact
    RFAP.DirichletChain.gapThreshold_mul_dirichletWindowQuadrances_sum_le_length
      gap ⟨threeFourthsLe, gapLtOne, by
        unfold RFAP.OptimalIndexOneWindow.gapPolynomial
        exact quadraticNonnegative⟩ pairs chain

/-- Compatibility theorem for the earlier `28/15` finite-octant chain bound:
clearing its denominator gives `28n` for `n` transitions. -/
theorem finiteBestChain_fifteen_mul_windowSum_le_twentyEight_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    15 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (28 * (consecutiveCoefficientIndexQuadrances pairs).length : Nat) :=
  RFAP.DirichletChain.fifteen_mul_dirichletWindowQuadrances_sum_le_twentyEight_mul_length
    pairs chain

/-- Compatibility with the earlier parity-sensitive finite-octant bound. -/
theorem finiteBestChain_fifteen_mul_windowSum_le_with_parity
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    15 * (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      (29 * (consecutiveCoefficientIndexQuadrances pairs).length +
        (consecutiveCoefficientIndexQuadrances pairs).length % 2 : Nat) :=
  RFAP.DirichletChain.fifteen_mul_dirichletWindowQuadrances_sum_le_with_parity
    pairs chain

/-- Direct finite-octant chain bound: each transition contributes at most
two. -/
theorem finiteBestChain_windowSum_le_two_mul_length
    (source : HurwitzFraction) (pairs : List HurwitzConvergentPair)
    (chain : pairs.IsChain
      (RFAP.BestApproximation.AreConsecutiveBest source.value)) :
    (consecutiveDirichletWindowQuadrances source pairs).sum ≤
      2 * ((consecutiveCoefficientIndexQuadrances pairs).length : Coordinate) :=
  RFAP.DirichletChain.dirichletWindowQuadrances_sum_le_two_mul_length
    pairs chain

/-- A successor returned by the executable selector supplies the approximation
for every natural quadrance request between the two endpoint levels. -/
theorem mem_consecutiveBestSuccessors_witnesses_dirichletWindow
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower)
    (request : Nat)
    (aboveLower :
      RFAP.BestApproximation.denominatorQuadrance lower < request)
    (noHigherThanUpper :
      request ≤ RFAP.BestApproximation.denominatorQuadrance upper) :
    lower.denominator ≠ 0 ∧
      RFAP.BestApproximation.denominatorQuadrance lower < request ∧
      (request : Coordinate) *
          RFAP.BestApproximation.errorQuadrance source.value lower ≤
        consecutiveDirichletWindowQuadrance source lower upper := by
  have consecutive :=
    (mem_consecutiveBestSuccessors_iff source lower upper).mp member
  exact consecutive.lower_witnesses_dirichletWindow request aboveLower
    noHigherThanUpper

/-- The displayed source denominator bounds every consecutive Dirichlet
window product. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_sourceBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        source.denominator : Coordinate) / 2 :=
  ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)
    |>.dirichletWindowQuadrance_le_sourceBound

/-- Every successor returned by the executable selector has squared
Dirichlet-window product at most `24`, independently of the source. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_twentyFour
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤ 24 :=
  consecutiveBest_dirichletWindow_le_twentyFour source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
refined source-independent squared-window bound `816/35`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_refinedUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      refinedUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_refinedUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the sharper
source-independent squared-window bound `1189/51`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_quadraticUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      quadraticUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_quadraticUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
index-aware source-independent squared-window bound `1189/102`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_indexAwareUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      indexAwareUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_indexAwareUniversalBound source lower upper
    ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the exact
finite-octant source-independent squared-window bound `112/71`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_finiteOctantUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      finiteOctantUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_finiteOctantUniversalBound
    source lower upper
      ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-- Every successor returned by the executable selector satisfies the
near-optimal dyadic source-independent squared-window bound `256/205`. -/
theorem mem_consecutiveBestSuccessors_dirichletWindow_le_dyadicUniversalBound
    (source : HurwitzFraction) (lower upper : HurwitzConvergentPair)
    (member : upper ∈ consecutiveBestSuccessors source lower) :
    consecutiveDirichletWindowQuadrance source lower upper ≤
      dyadicUniversalDirichletWindowBound :=
  consecutiveBest_dirichletWindow_le_dyadicUniversalBound
    source lower upper
      ((mem_consecutiveBestSuccessors_iff source lower upper).mp member)

/-! ## Explicit RFAP-II calculation envelopes -/

/-- Execute addition through canonical gcd-reduced coordinate records. -/
def normalizedCoordinateAdd (left right : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedAdd left right

theorem normalizedCoordinateAdd_eq (left right : Coordinate) :
    normalizedCoordinateAdd left right = left + right :=
  RFAP.NormalizedFraction.normalizedAdd_eq left right

/-- Execute multiplication with cross-cancellation and a final canonical
gcd reduction. -/
def normalizedCoordinateMul (left right : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedMul left right

theorem normalizedCoordinateMul_eq (left right : Coordinate) :
    normalizedCoordinateMul left right = left * right :=
  RFAP.NormalizedFraction.normalizedMul_eq left right

def normalizedCoordinateNeg (source : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedNeg source

theorem normalizedCoordinateNeg_eq (source : Coordinate) :
    normalizedCoordinateNeg source = -source :=
  RFAP.NormalizedFraction.normalizedNeg_eq source

def normalizedCoordinateSub (left right : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedSub left right

theorem normalizedCoordinateSub_eq (left right : Coordinate) :
    normalizedCoordinateSub left right = left - right :=
  RFAP.NormalizedFraction.normalizedSub_eq left right

def normalizedCoordinateInv (source : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedInv source

theorem normalizedCoordinateInv_eq (source : Coordinate) :
    normalizedCoordinateInv source = source⁻¹ :=
  RFAP.NormalizedFraction.normalizedInv_eq source

def normalizedCoordinateDiv (left right : Coordinate) : Coordinate :=
  RFAP.NormalizedFraction.normalizedDiv left right

theorem normalizedCoordinateDiv_eq (left right : Coordinate) :
    normalizedCoordinateDiv left right = left / right :=
  RFAP.NormalizedFraction.normalizedDiv_eq left right

/-- Bit width of the canonical numerator/denominator record for a coordinate. -/
def rationalRecordWidth (value : Coordinate) : Nat :=
  RFAP.CalculationSize.rationalRecordWidth value

/-- Source-only bit budget for normalized coordinate addition. -/
def normalizedAddBitBudget (left right : Coordinate) : Nat :=
  RFAP.CalculationSize.normalizedAddBitBudget left right

theorem normalizedCoordinateAdd_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateAdd left right) ≤
      normalizedAddBitBudget left right :=
  RFAP.CalculationSize.normalizedAdd_width_le_budget left right

/-- Source-only bit budget for normalized coordinate multiplication. -/
def normalizedMulBitBudget (left right : Coordinate) : Nat :=
  RFAP.CalculationSize.normalizedMulBitBudget left right

theorem normalizedCoordinateMul_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateMul left right) ≤
      normalizedMulBitBudget left right :=
  RFAP.CalculationSize.normalizedMul_width_le_budget left right

def normalizedSubBitBudget (left right : Coordinate) : Nat :=
  RFAP.CalculationSize.normalizedSubBitBudget left right

theorem normalizedCoordinateSub_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateSub left right) ≤
      normalizedSubBitBudget left right :=
  RFAP.CalculationSize.normalizedSub_width_le_budget left right

def normalizedDivBitBudget (left right : Coordinate) : Nat :=
  RFAP.CalculationSize.normalizedDivBitBudget left right

theorem normalizedCoordinateDiv_width_le_budget (left right : Coordinate) :
    rationalRecordWidth (normalizedCoordinateDiv left right) ≤
      normalizedDivBitBudget left right :=
  RFAP.CalculationSize.normalizedDiv_width_le_budget left right

/-- Execute polynomial evaluation through normalized Gaussian working
records and erase the result. -/
def normalizedPolynomialEvaluation (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian :=
  RFAP.NormalizedGaussian.value
    (RFAP.NormalizedEvaluation.eval polynomial point)

theorem normalizedPolynomialEvaluation_eq (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    normalizedPolynomialEvaluation polynomial point = polynomial.eval point :=
  RFAP.NormalizedEvaluation.value_eval polynomial point

def normalizedEvaluationBitBudget (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) : Nat :=
  RFAP.CalculationSize.normalizedEvaluationBitBudget polynomial point

def normalizedEvaluationStepBudget (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) : Nat :=
  RFAP.CalculationSize.normalizedEvaluationStepBudget polynomial point

theorem normalizedEvaluation_steps_le_budget
    (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.NormalizedEvaluation.steps point polynomial.coeffs ≤
      normalizedEvaluationStepBudget polynomial point :=
  RFAP.CalculationSize.normalizedEvaluation_steps_le_budget polynomial point

/-- Normalized polynomial and derivative evaluation followed by the Newton
division and subtraction. -/
def normalizedNewtonCenter (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) : WorkingGaussian :=
  RFAP.NormalizedEvaluation.newtonCenter polynomial point

theorem normalizedNewtonCenter_eq (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.NormalizedGaussian.value (normalizedNewtonCenter polynomial point) =
      point - polynomial.eval point /
        (RFAP.ComputableDerivative.derivative polynomial).eval point :=
  RFAP.NormalizedEvaluation.value_newtonCenter polynomial point

def normalizedNewtonBitBudget (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) : Nat :=
  RFAP.CalculationSize.normalizedNewtonBitBudget polynomial point

def normalizedNewtonStepBudget (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) : Nat :=
  RFAP.CalculationSize.normalizedNewtonStepBudget polynomial point

theorem normalizedNewtonCenter_width_le_budget
    (polynomial : GaussianPolynomial)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.CalculationSize.workingGaussianWidth
        (normalizedNewtonCenter polynomial point) ≤
      normalizedNewtonBitBudget polynomial point :=
  RFAP.CalculationSize.normalizedNewtonCenter_width_le_budget polynomial point

/-- Component-bit budget for the numerator and denominator of the nearest
grid record returned from a displayed centre and radius. -/
def gridRecordBitBudget
    (center : RFAP.ConstructiveGaussian.Gaussian) (radius : Coordinate) : Nat :=
  RFAP.CalculationSize.gridRecordBitBudget center radius

theorem gridFraction_width_le_budget
    (center : RFAP.ConstructiveGaussian.Gaussian) (radius : Coordinate) :
    RFAP.CalculationSize.commonFractionWidth
        (RFAP.HeightApproximation.gridFraction center radius) ≤
      gridRecordBitBudget center radius :=
  RFAP.CalculationSize.gridFraction_width_le_budget center radius

/-- Natural quadrance recurrence bounding every intermediate suffix value of
homogeneous Gaussian-integer evaluation. -/
def homogeneousWorkingEnvelope (numerator denominator : GaussianInt)
    (coefficients : List GaussianInt) : Nat :=
  RFAP.CalculationSize.homogeneousWorkingEnvelope numerator denominator
    coefficients

theorem homogeneousEvaluation_norm_le_envelope
    (numerator denominator : GaussianInt) (coefficients : List GaussianInt) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (RFAP.GaussianDenominatorHeight.homogeneousEval numerator denominator
          coefficients) ≤
      homogeneousWorkingEnvelope numerator denominator coefficients :=
  (RFAP.CalculationSize.homogeneousEval_norm_le_envelope
    numerator denominator coefficients).trans (by
      cases coefficients with
      | nil => rfl
      | cons coefficient remaining => exact le_max_left _ _)

/-- Binary-width bound on the number of clauses in the terminating Hurwitz
encoder. -/
def hurwitzStepBudget (fraction : HurwitzFraction) : Nat :=
  RFAP.CalculationSize.hurwitzStepBudget fraction

theorem hurwitzEncoding_length_le_budget (fraction : HurwitzFraction) :
    (RFAP.HurwitzRational.encode fraction).length ≤
      hurwitzStepBudget fraction :=
  RFAP.CalculationSize.hurwitz_length_le_stepBudget fraction

/-- Source-only quadrance budget for both members of the encoded continuant. -/
def hurwitzContinuantNormBudget (fraction : HurwitzFraction) : Nat :=
  RFAP.CalculationSize.hurwitzContinuantNormBudget fraction

theorem hurwitzContinuant_norm_le_budget (fraction : HurwitzFraction) :
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          (RFAP.HurwitzRational.continuant
            (RFAP.HurwitzRational.encode fraction)).numerator ≤
        hurwitzContinuantNormBudget fraction ∧
      RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          (RFAP.HurwitzRational.continuant
            (RFAP.HurwitzRational.encode fraction)).denominator ≤
        hurwitzContinuantNormBudget fraction :=
  RFAP.CalculationSize.encodedContinuant_norm_le_budget fraction

/-- Aggregate accounted-operation budget for the normalized Newton and
RFAP-II post-processing calculations. -/
def stageTwoStepBudget (input : StageTwoInput) : Nat :=
  RFAP.CalculationSize.stageTwoStepBudget input

/-- Aggregate component-bit budget for the same calculation family. -/
def stageTwoBitBudget (input : StageTwoInput) : Nat :=
  RFAP.CalculationSize.stageTwoBitBudget input

/-- A single constructive certificate for all normalized-Horner, Newton,
grid, homogeneous-evaluation, Hurwitz, and target-scan bounds named by the
RFAP-II resource interface. -/
theorem stageTwoResourceCertificate (input : StageTwoInput) :
    RFAP.CalculationSize.StageTwoResourcesWithin input
      (stageTwoStepBudget input) (stageTwoBitBudget input) :=
  RFAP.CalculationSize.stageTwo_resource_certificate input

end RFAP.ApproximationPaper
