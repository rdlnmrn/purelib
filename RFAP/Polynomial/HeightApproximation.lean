import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.DenominatorHeight
import RFAP.Polynomial.CoprimeBounds
import RFAP.Approximation.HurwitzNearest
import mathlib.RFAP.NormalizedFraction

/-!
# Constructive small-residual samples with explicit denominator height

A selected Newton band contains a point on a computable square Gaussian grid.
Coordinatewise nearest-integer rounding halves the required mesh width: the
grid denominator is one more than the integer floor of `1 / (2r)`.  This gives
an exact finite denominator certificate for the box-to-residual estimate.
-/

namespace RFAP.HeightApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev Box := RFAP.Boxes.Box
abbrev RawWindingState := RFAP.RawSubdivision.RawWindingState
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev SquarefreeCertificate := RFAP.LocalExtraction.SquarefreeCertificate
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PolynomialBounds

/-- Every rational is strictly below one more than its computed floor. -/
theorem lt_intCast_floor_add_one (value : Coordinate) :
    value <
      ((RFAP.ConstructiveFraction.floor value + 1 : Int) : Coordinate) := by
  apply lt_of_not_ge
  intro reverse
  have impossible :=
    (RFAP.ConstructiveFraction.intCast_le_iff_floor
      (RFAP.ConstructiveFraction.floor value + 1) value).mp reverse
  exact (Int.not_le_of_gt
    (Int.lt_add_one_iff.mpr (Int.le_refl _)) impossible).elim

/-- Common grid denominator for a positive radius, using the half-mesh
guarantee supplied by nearest-integer rounding. -/
def gridDenominator (radius : Coordinate) : Nat :=
  (RFAP.ConstructiveFraction.floor
    (RFAP.NormalizedFraction.normalizedDiv (1 / 2 : Coordinate) radius)).toNat + 1

theorem gridDenominator_pos (radius : Coordinate) :
    0 < gridDenominator radius := by
  unfold gridDenominator
  simp only [RFAP.NormalizedFraction.normalizedDiv_eq]
  omega

/-- Half the grid mesh is strictly smaller than the requested positive
radius. -/
theorem half_reciprocal_gridDenominator_lt {radius : Coordinate}
    (positive : 0 < radius) :
    (1 / 2 : Coordinate) / (gridDenominator radius : Coordinate) < radius := by
  let reciprocal := (1 / 2 : Coordinate) / radius
  have reciprocalNonnegative : (0 : Coordinate) ≤ reciprocal :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) positive).le
  have floorNonnegative :
      0 ≤ RFAP.ConstructiveFraction.floor reciprocal := by
    exact (RFAP.ConstructiveFraction.intCast_le_iff_floor 0 reciprocal).mp
      reciprocalNonnegative
  have denominatorCast :
      (gridDenominator radius : Coordinate) =
        ((RFAP.ConstructiveFraction.floor reciprocal + 1 : Int) :
          Coordinate) := by
    unfold gridDenominator
    simp only [RFAP.NormalizedFraction.normalizedDiv_eq]
    dsimp only [reciprocal]
    rw [Nat.cast_add, Nat.cast_one, ← Int.cast_natCast,
      Int.toNat_of_nonneg floorNonnegative, Int.cast_add, Int.cast_one]
  have reciprocalStrict :
      reciprocal < (gridDenominator radius : Coordinate) := by
    rw [denominatorCast]
    exact lt_intCast_floor_add_one reciprocal
  have denominatorPositive :
      (0 : Coordinate) < (gridDenominator radius : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct (gridDenominator_pos radius)
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).mpr
  have scaled :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos positive).mp reciprocalStrict
  calc
    (1 / 2 : Coordinate) <
        (gridDenominator radius : Coordinate) * radius := scaled
    _ = radius * (gridDenominator radius : Coordinate) := by ring1

/-- The computed denominator is the least positive natural denominator whose
half-mesh is strictly smaller than the requested radius. -/
theorem gridDenominator_minimal {radius : Coordinate} (radiusPositive : 0 < radius)
    {candidate : Nat} (candidatePositive : 0 < candidate)
    (mesh : (1 / 2 : Coordinate) / (candidate : Coordinate) < radius) :
    gridDenominator radius ≤ candidate := by
  let reciprocal := (1 / 2 : Coordinate) / radius
  have candidateCastPositive : (0 : Coordinate) < (candidate : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct candidatePositive
  have halfLtScaled :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos candidateCastPositive).mp mesh
  have reciprocalLtCandidate : reciprocal < (candidate : Coordinate) := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos radiusPositive).mpr
    calc
      (1 / 2 : Coordinate) < radius * (candidate : Coordinate) := halfLtScaled
      _ = (candidate : Coordinate) * radius := by ring1
  have reciprocalNonnegative : (0 : Coordinate) ≤ reciprocal :=
    (RFAP.ConstructiveFraction.div_pos_direct (by decide) radiusPositive).le
  have floorNonnegative :
      0 ≤ RFAP.ConstructiveFraction.floor reciprocal :=
    (RFAP.ConstructiveFraction.intCast_le_iff_floor 0 reciprocal).mp
      reciprocalNonnegative
  have floorLtCandidateInt :
      RFAP.ConstructiveFraction.floor reciprocal < (candidate : Int) := by
    apply lt_of_not_ge
    intro candidateLeFloor
    have candidateLeReciprocal :=
      (RFAP.ConstructiveFraction.intCast_le_iff_floor
        (candidate : Int) reciprocal).mpr candidateLeFloor
    have castIdentity : ((candidate : Int) : Coordinate) =
        (candidate : Coordinate) := by rw [Int.cast_natCast]
    rw [castIdentity] at candidateLeReciprocal
    exact (not_lt_of_ge candidateLeReciprocal) reciprocalLtCandidate
  have floorLtCandidate :
      (RFAP.ConstructiveFraction.floor reciprocal).toNat < candidate := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg floorNonnegative]
    exact floorLtCandidateInt
  unfold gridDenominator
  simp only [RFAP.NormalizedFraction.normalizedDiv_eq]
  dsimp only [reciprocal] at floorLtCandidate
  omega

/-- The nearest grid coordinate to a displayed rational center, with
half-integer ties sent upward. -/
def gridCoordinate (center : Coordinate) (denominator : Nat) : Coordinate :=
  RFAP.NormalizedFraction.normalizedDiv
    (RFAP.HurwitzNearest.nearestCoordinate
      (RFAP.NormalizedFraction.normalizedMul
        (denominator : Coordinate) center) : Int)
    (denominator : Coordinate)

/-- Nearest rounding places the grid coordinate strictly above the lower
half-mesh endpoint and weakly below the upper endpoint. -/
theorem gridCoordinate_bounds (center : Coordinate) {denominator : Nat}
    (positive : 0 < denominator) :
    center - (1 / 2 : Coordinate) / denominator <
        gridCoordinate center denominator ∧
      gridCoordinate center denominator ≤
        center + (1 / 2 : Coordinate) / denominator := by
  simp only [gridCoordinate, RFAP.NormalizedFraction.normalizedDiv_eq,
    RFAP.NormalizedFraction.normalizedMul_eq]
  have denominatorPositive : (0 : Coordinate) < (denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct positive
  let scaledCenter := (denominator : Coordinate) * center
  let selected := RFAP.HurwitzNearest.nearestCoordinate scaledCenter
  have error := RFAP.HurwitzNearest.nearestCoordinate_error_bounds scaledCenter
  have halfCancel :
      ((1 / 2 : Coordinate) / (denominator : Coordinate)) *
          (denominator : Coordinate) = 1 / 2 :=
    RFAP.ExplicitField.div_mul_cancel _ (ne_of_gt denominatorPositive)
  constructor
  · apply (RFAP.ConstructiveFraction.lt_div_iff_pos
      denominatorPositive).mpr
    have translated := RFAP.ConstructiveFraction.add_lt_add_right_direct
      error.2 ((selected : Coordinate) - 1 / 2)
    calc
      (center - (1 / 2 : Coordinate) / denominator) * denominator =
          scaledCenter - 1 / 2 := by
        rw [sub_mul, halfCancel]
        dsimp only [scaledCenter]
        ring1
      _ = (scaledCenter - (selected : Coordinate)) +
          ((selected : Coordinate) - 1 / 2) := by ring1
      _ < (1 / 2 : Coordinate) +
          ((selected : Coordinate) - 1 / 2) := translated
      _ = (selected : Coordinate) := by ring1
  · apply (RFAP.ConstructiveFraction.div_le_iff_pos
      denominatorPositive).mpr
    have translated := RFAP.ConstructiveFraction.add_le_add_right_direct
      error.1 ((selected : Coordinate) + 1 / 2)
    calc
      (selected : Coordinate) =
          -(1 / 2 : Coordinate) +
            ((selected : Coordinate) + 1 / 2) := by ring1
      _ ≤ (scaledCenter - (selected : Coordinate)) +
          ((selected : Coordinate) + 1 / 2) := translated
      _ = (center + (1 / 2 : Coordinate) / denominator) * denominator := by
        rw [add_mul, halfCancel]
        dsimp only [scaledCenter]
        ring1

/-- The square-grid Gaussian fraction obtained by nearest rounding in both
coordinates. -/
def gridFraction (center : Gaussian) (radius : Coordinate) : Fraction :=
  let denominator := gridDenominator radius
  RFAP.ConstructiveGaussianHeight.Fraction.grid
    (RFAP.HurwitzNearest.nearestCoordinate
      (RFAP.NormalizedFraction.normalizedMul
        (denominator : Coordinate) center.re))
    (RFAP.HurwitzNearest.nearestCoordinate
      (RFAP.NormalizedFraction.normalizedMul
        (denominator : Coordinate) center.im))
    denominator (gridDenominator_pos radius)

@[simp] theorem gridFraction_height (center : Gaussian) (radius : Coordinate) :
    (gridFraction center radius).height = gridDenominator radius ^ 2 := rfl

@[simp] theorem gridFraction_value_re (center : Gaussian) (radius : Coordinate) :
    (gridFraction center radius).value.re =
      gridCoordinate center.re (gridDenominator radius) := by
  simp only [gridFraction, gridCoordinate,
    RFAP.NormalizedFraction.normalizedDiv_eq,
    RFAP.NormalizedFraction.normalizedMul_eq]
  rfl

@[simp] theorem gridFraction_value_im (center : Gaussian) (radius : Coordinate) :
    (gridFraction center radius).value.im =
      gridCoordinate center.im (gridDenominator radius) := by
  simp only [gridFraction, gridCoordinate,
    RFAP.NormalizedFraction.normalizedDiv_eq,
    RFAP.NormalizedFraction.normalizedMul_eq]
  rfl

/-- The constructed grid fraction lies strictly inside every selected Newton
band of the same center and radius. -/
theorem gridFraction_strictly_inside
    {center : Gaussian} {radius : Coordinate}
    (positive : 0 < radius)
    (band : RFAP.NewtonBand.NewtonBandBox center radius) :
    band.box.StrictContains (gridFraction center radius).value := by
  have denominatorPositive := gridDenominator_pos radius
  have mesh := half_reciprocal_gridDenominator_lt positive
  have realBounds := gridCoordinate_bounds center.re denominatorPositive
  have imaginaryBounds := gridCoordinate_bounds center.im denominatorPositive
  have negativeMesh := RFAP.ConstructiveFraction.neg_lt_neg_direct mesh
  have realLower : center.re - radius <
      gridCoordinate center.re (gridDenominator radius) :=
    (show center.re - radius <
        center.re - (1 / 2 : Coordinate) / gridDenominator radius by
      calc
        center.re - radius = -radius + center.re := by ring1
        _ < (-((1 / 2 : Coordinate) / gridDenominator radius)) + center.re :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct negativeMesh _
        _ = center.re - (1 / 2 : Coordinate) / gridDenominator radius := by
          ring1).trans realBounds.1
  have realUpper : gridCoordinate center.re (gridDenominator radius) <
      center.re + radius :=
    realBounds.2.trans_lt
      (RFAP.ConstructiveFraction.add_lt_add_left_direct mesh center.re)
  have imaginaryLower : center.im - radius <
      gridCoordinate center.im (gridDenominator radius) :=
    (show center.im - radius <
        center.im - (1 / 2 : Coordinate) / gridDenominator radius by
      calc
        center.im - radius = -radius + center.im := by ring1
        _ < (-((1 / 2 : Coordinate) / gridDenominator radius)) + center.im :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct negativeMesh _
        _ = center.im - (1 / 2 : Coordinate) / gridDenominator radius := by
          ring1).trans imaginaryBounds.1
  have imaginaryUpper : gridCoordinate center.im (gridDenominator radius) <
      center.im + radius :=
    imaginaryBounds.2.trans_lt
      (RFAP.ConstructiveFraction.add_lt_add_left_direct mesh center.im)
  exact
    ⟨by simpa only [gridFraction_value_re] using
        band.left_upper.trans_lt realLower,
      by simpa only [gridFraction_value_re] using
        realUpper.trans_le band.right_lower,
      by simpa only [gridFraction_value_im] using
        band.bottom_upper.trans_lt imaginaryLower,
      by simpa only [gridFraction_value_im] using
        imaginaryUpper.trans_le band.top_lower⟩

/-- Regard a Newton-band output as the winding-one state that it certifies. -/
def stateOfOutput
    {p : GaussianPolynomial} {ambient : Box}
    {squarefree : SquarefreeCertificate p}
    {current : RawWindingState p ambient} {epsilon : Coordinate}
    (output : RFAP.NewtonBand.Output squarefree current epsilon) :
    WindingOneState p ambient :=
  { box := output.box
    refinesAmbient := output.refinesAmbient
    proper := output.proper
    clearance := output.clearance
    rawWindingFour := output.rawWindingFour
    ambientLeftClearance := output.ambientLeftClearance
    ambientRightClearance := output.ambientRightClearance
    ambientBottomClearance := output.ambientBottomClearance
    ambientTopClearance := output.ambientTopClearance }

/-- Fully displayed output of the denominator-controlled approximation. -/
structure Output
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (epsilon : Coordinate) where
  extracted : RFAP.NewtonBand.Output squarefree current epsilon
  fraction : Fraction
  fraction_eq : fraction = gridFraction
    (RFAP.LocalExtraction.anchorNewtonCenter p extracted.source.box)
    extracted.radius
  strictlyInside : extracted.box.StrictContains fraction.value
  height_eq : fraction.height = gridDenominator extracted.radius ^ 2
  residual_le : normSq (p.eval fraction.value) ≤
    2 * denseLipschitzBound p ambient * epsilon ^ 2

/-- Execute Newton-band extraction and select its explicit grid fraction. -/
def approximate
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    Output degreeAtLeastTwo squarefree elimination current epsilon := by
  let extracted := RFAP.NewtonBand.extract degreeAtLeastTwo squarefree
    elimination current epsilonPositive
  let center := RFAP.LocalExtraction.anchorNewtonCenter p extracted.source.box
  let fraction := gridFraction center extracted.radius
  have strictlyInside : extracted.box.StrictContains fraction.value := by
    exact gridFraction_strictly_inside extracted.radiusPositive extracted.band
  let state := stateOfOutput extracted
  have residual :=
    RFAP.CoprimeBounds.normSq_eval_le_four_lipschitz_diagonal
      (show 0 < p.natDegree by omega) state strictlyInside.contains
  have residualBound : normSq (p.eval fraction.value) ≤
      2 * denseLipschitzBound p ambient * epsilon ^ 2 := by
    calc
      normSq (p.eval fraction.value) ≤
          4 * denseLipschitzBound p ambient * state.box.diagonalSq := residual
      _ ≤ 4 * denseLipschitzBound p ambient *
          ((1 / 2 : Coordinate) * epsilon ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          extracted.diagonalSq_le_half
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (denseLipschitzBound_pos p ambient).le)
      _ = 2 * denseLipschitzBound p ambient * epsilon ^ 2 := by
        have fourHalf : (4 : Coordinate) * (1 / 2) = 2 := by decide
        calc
          4 * denseLipschitzBound p ambient *
              ((1 / 2 : Coordinate) * epsilon ^ 2) =
              ((4 : Coordinate) * (1 / 2)) *
                denseLipschitzBound p ambient * epsilon ^ 2 := by ring1
          _ = 2 * denseLipschitzBound p ambient * epsilon ^ 2 := by
            rw [fourHalf]
  exact
    { extracted := extracted
      fraction := fraction
      fraction_eq := rfl
      strictlyInside := strictlyInside
      height_eq := gridFraction_height center extracted.radius
      residual_le := residualBound }

/-! ## Square-root-scaled residual requests -/

/-- Bounded scan for the first candidate whose square is strictly above the
input.  The fuel used by `squareThreshold` is sufficient to reach such a
candidate. -/
def squareThresholdAux (input candidate : Nat) : Nat → Nat
  | 0 => candidate
  | fuel + 1 =>
      if input < candidate * candidate then candidate
      else squareThresholdAux input (candidate + 1) fuel

theorem squareThresholdAux_le_add (input candidate fuel : Nat) :
    squareThresholdAux input candidate fuel ≤ candidate + fuel := by
  induction fuel generalizing candidate with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · exact Nat.le_add_right candidate (fuel + 1)
      · have recursive := inductionHypothesis (candidate + 1)
        calc
          squareThresholdAux input (candidate + 1) fuel ≤
              (candidate + 1) + fuel := recursive
          _ = candidate + (fuel + 1) := by ring1

theorem squareThresholdAux_spec {input candidate fuel : Nat}
    (eventual : input < (candidate + fuel) * (candidate + fuel)) :
    input < squareThresholdAux input candidate fuel *
      squareThresholdAux input candidate fuel := by
  induction fuel generalizing candidate with
  | zero =>
      simpa only [squareThresholdAux, Nat.add_zero] using eventual
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · assumption
      · apply inductionHypothesis
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          eventual

theorem squareThresholdAux_minimal {input candidate fuel comparison : Nat}
    (candidateLe : candidate ≤ comparison)
    (comparisonReachable : comparison ≤ candidate + fuel)
    (comparisonWorks : input < comparison * comparison) :
    squareThresholdAux input candidate fuel ≤ comparison := by
  induction fuel generalizing candidate with
  | zero =>
      unfold squareThresholdAux
      exact candidateLe
  | succ fuel inductionHypothesis =>
      unfold squareThresholdAux
      split
      · exact candidateLe
      · rename_i candidateFails
        have candidateNe : candidate ≠ comparison := by
          intro equal
          subst comparison
          exact candidateFails comparisonWorks
        have nextCandidateLe : candidate + 1 ≤ comparison :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne candidateLe candidateNe)
        have comparisonStillReachable : comparison ≤ candidate + 1 + fuel := by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_succ] using comparisonReachable
        exact inductionHypothesis (candidate := candidate + 1)
          nextCandidateLe comparisonStillReachable

/-- Least positive natural whose square is strictly above the input. -/
def squareThreshold (input : Nat) : Nat :=
  squareThresholdAux input 1 (input + 1)

theorem squareThreshold_spec (input : Nat) :
    input < squareThreshold input * squareThreshold input := by
  apply squareThresholdAux_spec
  rw [show 1 + (input + 1) = input + 2 by ring1]
  have oneLe : 1 ≤ input + 2 :=
    Nat.succ_le_succ (Nat.zero_le (input + 1))
  have productBound := Nat.mul_le_mul_left (input + 2) oneLe
  calc
    input < input + 2 := Nat.lt_add_of_pos_right (by decide)
    _ = (input + 2) * 1 := (Nat.mul_one _).symm
    _ ≤ (input + 2) * (input + 2) := productBound

theorem squareThreshold_pos (input : Nat) : 0 < squareThreshold input := by
  have strict := squareThreshold_spec input
  apply Nat.pos_of_ne_zero
  intro zero
  rw [zero] at strict
  simp only [Nat.zero_mul] at strict
  exact (Nat.not_lt_zero input) strict

theorem squareThreshold_minimal {input comparison : Nat}
    (comparisonPositive : 0 < comparison)
    (comparisonWorks : input < comparison * comparison) :
    squareThreshold input ≤ comparison := by
  by_cases reachable : comparison ≤ 1 + (input + 1)
  · exact squareThresholdAux_minimal comparisonPositive reachable
      comparisonWorks
  · have outputBound := squareThresholdAux_le_add input 1 (input + 1)
    unfold squareThreshold
    exact outputBound.trans
      (Nat.le_of_lt (Nat.lt_of_not_ge reachable))

/-- Natural denominator used for a quadratic residual request.  It is the
least positive natural whose square strictly exceeds the ceiling of
`coefficient / target`. -/
def targetDenominator (coefficient target : Coordinate) : Nat :=
  squareThreshold
    (RFAP.ConstructiveFraction.ceilNat (coefficient / target))

theorem targetDenominator_pos (coefficient target : Coordinate) :
    0 < targetDenominator coefficient target := by
  exact squareThreshold_pos _

/-- Rational request whose denominator grows at the square-root rate forced
by a quadratic residual estimate. -/
def targetEpsilon (coefficient target : Coordinate) : Coordinate :=
  1 / (targetDenominator coefficient target : Coordinate)

theorem targetEpsilon_pos (coefficient target : Coordinate) :
    0 < targetEpsilon coefficient target := by
  exact RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (targetDenominator_pos coefficient target))

/-- The displayed ratio is strictly below the square of its computed least
square threshold. -/
theorem ratio_lt_targetDenominator_sq
    {coefficient target : Coordinate} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient / target <
      (targetDenominator coefficient target : Coordinate) ^ 2 := by
  let ceiling := RFAP.ConstructiveFraction.ceilNat (coefficient / target)
  have ratioNonnegative : (0 : Coordinate) ≤ coefficient / target :=
    (RFAP.ConstructiveFraction.div_pos_direct coefficientPositive
      targetPositive).le
  have ratioLeCeiling : coefficient / target ≤ (ceiling : Coordinate) := by
    exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      ratioNonnegative
  have ceilingLtDenominatorSqNat :
      ceiling < squareThreshold ceiling * squareThreshold ceiling :=
    squareThreshold_spec ceiling
  have ceilingLtDenominatorSq :
      (ceiling : Coordinate) <
        (squareThreshold ceiling : Coordinate) ^ 2 := by
    have castStrict := RFAP.ConstructiveFraction.natCast_lt_direct
      ceilingLtDenominatorSqNat
    rw [Nat.cast_mul] at castStrict
    simpa only [pow_two] using castStrict
  change coefficient / target < (squareThreshold ceiling : Coordinate) ^ 2
  exact ratioLeCeiling.trans_lt ceilingLtDenominatorSq

/-- Clearing the positive target denominator converts the ratio estimate into
the multiplication estimate used below. -/
theorem coefficient_le_target_mul_targetDenominator_sq
    {coefficient target : Coordinate} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient ≤ target *
      (targetDenominator coefficient target : Coordinate) ^ 2 := by
  have ratioStrict := ratio_lt_targetDenominator_sq coefficientPositive
    targetPositive
  have scaledStrict : coefficient <
      (targetDenominator coefficient target : Coordinate) ^ 2 * target :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos targetPositive).mp ratioStrict
  calc
    coefficient ≤
        (targetDenominator coefficient target : Coordinate) ^ 2 * target :=
      scaledStrict.le
    _ = target *
        (targetDenominator coefficient target : Coordinate) ^ 2 := by ring1

/-- Exact algebraic form of the reciprocal-square request. -/
theorem coefficient_mul_targetEpsilon_sq_eq_div
    (coefficient target : Coordinate) :
    coefficient * targetEpsilon coefficient target ^ 2 =
      coefficient /
        (targetDenominator coefficient target : Coordinate) ^ 2 := by
  let denominator : Coordinate := targetDenominator coefficient target
  have oneDiv : (1 : Coordinate) / denominator = denominator⁻¹ := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.one_mul denominator⁻¹
  change coefficient * ((1 : Coordinate) / denominator) ^ 2 =
    coefficient / denominator ^ 2
  rw [oneDiv, RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.inv_pow_direct]

/-- The square-root-scaled request is sufficient for any positive quadratic
coefficient and positive residual target. -/
theorem coefficient_mul_targetEpsilon_sq_le
    {coefficient target : Coordinate} (coefficientPositive : 0 < coefficient)
    (targetPositive : 0 < target) :
    coefficient * targetEpsilon coefficient target ^ 2 ≤ target := by
  have denominatorPositive : (0 : Coordinate) <
      (targetDenominator coefficient target : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (targetDenominator_pos coefficient target)
  have squarePositive :
      0 < (targetDenominator coefficient target : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct denominatorPositive 2
  rw [coefficient_mul_targetEpsilon_sq_eq_div]
  exact (RFAP.ConstructiveFraction.div_le_iff_pos squarePositive).mpr
    (coefficient_le_target_mul_targetDenominator_sq coefficientPositive
      targetPositive)

/-- Execute the approximation with the square-root-scaled request belonging
to its checked residual coefficient. -/
def approximateTarget
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (target : Coordinate) :
    Output degreeAtLeastTwo squarefree elimination current
      (targetEpsilon (2 * denseLipschitzBound p ambient) target) :=
  approximate degreeAtLeastTwo squarefree elimination current
    (targetEpsilon_pos _ target)

theorem approximateTarget_residual_le
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) {target : Coordinate}
    (targetPositive : 0 < target) :
    normSq (p.eval
      (approximateTarget degreeAtLeastTwo squarefree elimination current
        target).fraction.value) ≤ target := by
  let coefficient := 2 * denseLipschitzBound p ambient
  have coefficientPositive : (0 : Coordinate) < coefficient :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (denseLipschitzBound_pos p ambient)
  exact
    (approximateTarget degreeAtLeastTwo squarefree elimination current
      target).residual_le.trans
      (coefficient_mul_targetEpsilon_sq_le coefficientPositive targetPositive)

end RFAP.HeightApproximation
