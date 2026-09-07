import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ShrinkingTrack

/-!
# Excluding a displayed clear point from a winding-one track

A fixed rational point at which the polynomial is nonzero cannot remain in
an arbitrarily small nonzero-winding box.  The proof uses the existing finite
constant-dominance homotopy: if the point were inside, its nonzero value and
the box's coefficient-computed variation bound would force winding zero.

This is the terminal-point part of the persistent CCL equality handler.  A
local CCL terminal is either an exact polynomial root, or one explicit track
refinement excludes that displayed rational point.
-/

namespace CCL.WindingPointExclusion

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.PolynomialBounds
open RFAP.Winding

/-- Four times the ambient polynomial Lipschitz coefficient. -/
def exclusionCoefficient (p : GaussianPolynomial) (ambient : Box) : Coordinate :=
  4 * denseLipschitzBound p ambient

theorem exclusionCoefficient_pos
    (p : GaussianPolynomial) (ambient : Box) :
    0 < exclusionCoefficient p ambient :=
  RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (denseLipschitzBound_pos p ambient)

/-- Positive rational radius computed from any uniform lower bound for the
polynomial residual.  The bound need not be attained by a displayed point. -/
def uniformExclusionRadius
    (p : GaussianPolynomial) (ambient : Box) (lower : Coordinate) :
    Coordinate :=
  min 1 (lower / (8 * denseLipschitzBound p ambient))

theorem uniformExclusionRadius_pos
    (p : GaussianPolynomial) (ambient : Box) {lower : Coordinate}
    (positive : 0 < lower) :
    0 < uniformExclusionRadius p ambient lower := by
  have denominatorPositive :
      0 < 8 * denseLipschitzBound p ambient :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (denseLipschitzBound_pos p ambient)
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct positive denominatorPositive)

private theorem uniform_exclusion_margin
    (p : GaussianPolynomial) (ambient : Box) {lower : Coordinate}
    (positive : 0 < lower) :
    exclusionCoefficient p ambient *
        uniformExclusionRadius p ambient lower ^ 2 < lower := by
  let lipschitz := denseLipschitzBound p ambient
  let radius := uniformExclusionRadius p ambient lower
  let quotient := lower / (8 * lipschitz)
  have lipschitzPositive : 0 < lipschitz :=
    denseLipschitzBound_pos p ambient
  have denominatorPositive : 0 < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have quotientPositive : 0 < quotient :=
    RFAP.ConstructiveFraction.div_pos_direct positive denominatorPositive
  have radiusPositive : 0 < radius :=
    uniformExclusionRadius_pos p ambient positive
  have radiusLeOne : radius ≤ 1 := min_le_left 1 quotient
  have radiusLeQuotient : radius ≤ quotient := min_le_right 1 quotient
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have coefficientPositive : 0 < 4 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have squareScaled :
      (4 * lipschitz) * radius ^ 2 ≤ (4 * lipschitz) * radius :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusSquareLe coefficientPositive.le
  have radiusScaled :
      (4 * lipschitz) * radius ≤ (4 * lipschitz) * quotient :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusLeQuotient coefficientPositive.le
  have fourLtEight : 4 * lipschitz < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (by decide) lipschitzPositive
  have quotientScaled :
      (4 * lipschitz) * quotient < (8 * lipschitz) * quotient :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      fourLtEight quotientPositive
  have cancellation : (8 * lipschitz) * quotient = lower := by
    calc
      (8 * lipschitz) * quotient = quotient * (8 * lipschitz) :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = lower :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne lower
          (8 * lipschitz) denominatorPositive.ne'
  change (4 * lipschitz) * radius ^ 2 < lower
  exact squareScaled.trans_lt
    (radiusScaled.trans_lt (quotientScaled.trans_eq cancellation))

/-- A displayed clear point whose value dominates the current box variation
cannot lie in a winding-one box. -/
theorem not_contains_of_margin
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (current : WindingOneState p ambient) (point : Gaussian)
    (margin : exclusionCoefficient p ambient * current.box.diagonalSq <
      normSq (p.eval point)) :
    ¬current.box.Contains point := by
  intro inside
  let certificate :
      RFAP.LocalExtraction.NearbyClearPointCertificate
        p ambient current.box :=
    { point := point
      point_mem := current.refinesAmbient.contains inside
      clearance := normSq (p.eval point)
      radiusSq := current.box.diagonalSq
      clearance_lower := le_rfl
      anchor_distance := current.box.normSq_sub_anchor_le inside
      dominates := by
        calc
          2 *
              (RFAP.LocalExtraction.anchorResidualBound
                  p ambient current.box +
                denseLipschitzBound p ambient * current.box.diagonalSq) =
              exclusionCoefficient p ambient * current.box.diagonalSq := by
            simp only [RFAP.LocalExtraction.anchorResidualBound,
              exclusionCoefficient]
            ring1
          _ < normSq (p.eval point) := margin }
  have windingZero :=
    RFAP.LocalExtraction.quadrupledBoxWinding_eq_zero_of_nearby_clear_point
      p degreePositive current.refinesAmbient current.proper certificate
  have fourZero : (4 : Int) = 0 := by
    calc
      4 = quadrupledBoxWinding p current.box := current.rawWindingFour.symm
      _ = 0 := windingZero
  exact (show (4 : Int) ≠ 0 by decide) fourZero

/-- One track refinement small enough to exclude every point whose displayed
polynomial residual is at least `lower`. -/
def refinePastUniformMargin
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (lower : Coordinate) (positive : 0 < lower) :
    WindingOneState p ambient :=
  track.refine current (uniformExclusionRadius p ambient lower)
    (uniformExclusionRadius_pos p ambient positive)

theorem refinePastUniformMargin_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (lower : Coordinate) (positive : 0 < lower) :
    (refinePastUniformMargin track current lower positive).box.Refines
      current.box :=
  track.nested current (uniformExclusionRadius p ambient lower)
    (uniformExclusionRadius_pos p ambient positive)

theorem refinePastUniformMargin_excludes
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (lower : Coordinate) (positive : 0 < lower) (point : Gaussian)
    (pointLower : lower ≤ normSq (p.eval point)) :
    ¬(refinePastUniformMargin track current lower positive).box.Contains
      point := by
  apply not_contains_of_margin degreePositive
  have accurate := track.accurate current
    (uniformExclusionRadius p ambient lower)
    (uniformExclusionRadius_pos p ambient positive)
  have coefficientNonnegative := (exclusionCoefficient_pos p ambient).le
  exact
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      ((uniform_exclusion_margin p ambient positive).trans_le pointLower)

/-- Positive rational radius small enough to exclude one displayed nonroot. -/
def exclusionRadius
    (p : GaussianPolynomial) (ambient : Box) (point : Gaussian) : Coordinate :=
  min 1
    (normSq (p.eval point) /
      (8 * denseLipschitzBound p ambient))

theorem exclusionRadius_pos
    (p : GaussianPolynomial) (ambient : Box) (point : Gaussian)
    (nonroot : p.eval point ≠ 0) :
    0 < exclusionRadius p ambient point := by
  have valuePositive : 0 < normSq (p.eval point) := normSq_pos nonroot
  have denominatorPositive :
      0 < 8 * denseLipschitzBound p ambient :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (denseLipschitzBound_pos p ambient)
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct valuePositive
      denominatorPositive)

private theorem exclusion_margin
    (p : GaussianPolynomial) (ambient : Box) (point : Gaussian)
    (nonroot : p.eval point ≠ 0) :
    exclusionCoefficient p ambient *
        exclusionRadius p ambient point ^ 2 <
      normSq (p.eval point) := by
  let value := normSq (p.eval point)
  let lipschitz := denseLipschitzBound p ambient
  let radius := exclusionRadius p ambient point
  let quotient := value / (8 * lipschitz)
  have valuePositive : 0 < value := normSq_pos nonroot
  have lipschitzPositive : 0 < lipschitz :=
    denseLipschitzBound_pos p ambient
  have denominatorPositive : 0 < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have quotientPositive : 0 < quotient :=
    RFAP.ConstructiveFraction.div_pos_direct valuePositive denominatorPositive
  have radiusPositive : 0 < radius :=
    exclusionRadius_pos p ambient point nonroot
  have radiusLeOne : radius ≤ 1 := by
    exact min_le_left 1 quotient
  have radiusLeQuotient : radius ≤ quotient := by
    exact min_le_right 1 quotient
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        radiusLeOne radiusPositive.le
    exact scaled.trans_eq (one_mul radius)
  have coefficientPositive : 0 < 4 * lipschitz :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide) lipschitzPositive
  have squareScaled :
      (4 * lipschitz) * radius ^ 2 ≤ (4 * lipschitz) * radius :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusSquareLe coefficientPositive.le
  have radiusScaled :
      (4 * lipschitz) * radius ≤ (4 * lipschitz) * quotient :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      radiusLeQuotient coefficientPositive.le
  have fourLtEight : 4 * lipschitz < 8 * lipschitz :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (by decide) lipschitzPositive
  have quotientScaled :
      (4 * lipschitz) * quotient < (8 * lipschitz) * quotient :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      fourLtEight quotientPositive
  have cancellation : (8 * lipschitz) * quotient = value := by
    calc
      (8 * lipschitz) * quotient = quotient * (8 * lipschitz) :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = value :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne value
          (8 * lipschitz) denominatorPositive.ne'
  change (4 * lipschitz) * radius ^ 2 < value
  exact squareScaled.trans_lt
    (radiusScaled.trans_lt (quotientScaled.trans_eq cancellation))

/-- One coefficient-computed track refinement that excludes a displayed
nonroot while retaining the same winding-one track. -/
def refinePastPoint
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Gaussian) (nonroot : p.eval point ≠ 0) :
    WindingOneState p ambient :=
  track.refine current (exclusionRadius p ambient point)
    (exclusionRadius_pos p ambient point nonroot)

theorem refinePastPoint_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Gaussian) (nonroot : p.eval point ≠ 0) :
    (refinePastPoint track current point nonroot).box.Refines current.box :=
  track.nested current (exclusionRadius p ambient point)
    (exclusionRadius_pos p ambient point nonroot)

theorem refinePastPoint_excludes
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (point : Gaussian) (nonroot : p.eval point ≠ 0) :
    ¬(refinePastPoint track current point nonroot).box.Contains point := by
  apply not_contains_of_margin degreePositive
  have accurate := track.accurate current
    (exclusionRadius p ambient point)
    (exclusionRadius_pos p ambient point nonroot)
  have coefficientNonnegative := (exclusionCoefficient_pos p ambient).le
  exact
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct accurate
      coefficientNonnegative).trans_lt
      (exclusion_margin p ambient point nonroot)

end CCL.WindingPointExclusion
