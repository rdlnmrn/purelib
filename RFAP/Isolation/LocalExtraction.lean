import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Global
import RFAP.Polynomial.DerivativeSeparation
import RFAP.Polynomial.NormalizedEvaluation

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace RFAP.LocalExtraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PolynomialBounds
open RFAP.Winding
open RFAP.WindingHomotopy
open RFAP.GlobalWinding

/-- Coefficient-computed upper bound for residual variation from the fixed
rational anchor of a subbox. -/
def anchorResidualBound (p : GaussianPolynomial)
    (ambient small : Box) : Coordinate :=
  denseLipschitzBound p ambient * small.diagonalSq

theorem anchorResidualBound_nonneg (p : GaussianPolynomial)
    (ambient small : Box) : 0 ≤ anchorResidualBound p ambient small :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (denseLipschitzBound_pos p ambient).le small.diagonalSq_nonneg

/-- Every point of the small box differs from its fixed rational anchor by at
most the displayed finite coefficient bound. -/
theorem normSq_eval_sub_anchor_le
    (p : GaussianPolynomial) {ambient small : Box}
    (refines : small.Refines ambient) {z : Gaussian}
    (inside : small.Contains z) :
    normSq (p.eval z - p.eval small.anchor) ≤
      anchorResidualBound p ambient small := by
  have zAmbient : ambient.Contains z := refines.contains inside
  have anchorAmbient : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variation := normSq_eval_sub_eval_le_denseLipschitzBound
    p zAmbient anchorAmbient
  have distance := small.normSq_sub_anchor_le inside
  exact variation.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct distance
      (denseLipschitzBound_pos p ambient).le)

/-- Positive rational gap available when the anchor residual strictly exceeds
the uniform box variation. -/
def anchorConstantDominanceMargin (p : GaussianPolynomial)
    (ambient small : Box) : Coordinate :=
  normSq (p.eval small.anchor) - anchorResidualBound p ambient small

theorem anchorConstantDominanceMargin_pos
    (p : GaussianPolynomial) (ambient small : Box)
    (large : anchorResidualBound p ambient small <
      normSq (p.eval small.anchor)) :
    0 < anchorConstantDominanceMargin p ambient small :=
  RFAP.ConstructiveFraction.sub_pos_direct large

/-- A too-large anchor residual gives one finite norm-dominance certificate
for the constant anchor value over the entire small-box boundary. -/
def anchorBoundaryNormDominance
    (p : GaussianPolynomial) {ambient small : Box}
    (refines : small.Refines ambient)
    (large : anchorResidualBound p ambient small <
      normSq (p.eval small.anchor)) :
    BoundaryNormDominance
      (gaussianConstant (p.eval small.anchor))
      (p.normalize - gaussianConstant (p.eval small.anchor)) small where
  margin := anchorConstantDominanceMargin p ambient small
  positive := anchorConstantDominanceMargin_pos p ambient small large
  lower := by
    intro z boundary
    have variation := normSq_eval_sub_anchor_le p refines boundary.1
    have dominance := RFAP.ConstructiveFraction.sub_le_sub_left_direct variation
      (normSq (p.eval small.anchor))
    simp only [anchorConstantDominanceMargin, gaussianConstant_eval,
      eval_sub, eval_normalize]
    exact dominance

/-- If the anchor value exceeded the uniform variation, constructive Rouché
would contract the normalized polynomial to a nonzero constant and force raw
winding zero. -/
theorem quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (large : anchorResidualBound p ambient small <
      normSq (p.eval small.anchor)) :
    quadrupledBoxWinding p small = 0 := by
  have polynomialNonzero := isZero_false_of_natDegree_pos degreePositive
  have anchorValueNonzero : p.eval small.anchor ≠ 0 := by
    intro zero
    have boundNonnegative := anchorResidualBound_nonneg p ambient small
    rw [zero, normSq_zero] at large
    exact (not_lt_of_ge boundNonnegative) large
  have sumIdentity :
      gaussianConstant (p.eval small.anchor) +
          (p.normalize - gaussianConstant (p.eval small.anchor)) =
        p.normalize :=
    constant_add_sub_constant_of_normalized
      (normalize_normalize p) (by simpa using polynomialNonzero)
      (by simpa using degreePositive) anchorValueNonzero
  have transfer := quadrupledBoxWinding_add_of_boundaryNormDominance
    (gaussianConstant (p.eval small.anchor))
    (p.normalize - gaussianConstant (p.eval small.anchor)) small proper
    (gaussianConstant_boundaryClearance anchorValueNonzero small)
    (anchorBoundaryNormDominance p refines large)
  rw [sumIdentity] at transfer
  calc
    quadrupledBoxWinding p small =
        quadrupledBoxWinding p.normalize small :=
      (quadrupledBoxWinding_normalize p small).symm
    _ = quadrupledBoxWinding
          (gaussianConstant (p.eval small.anchor)) small := transfer
    _ = 0 := quadrupledBoxWinding_gaussianConstant anchorValueNonzero small

/-- Nonzero raw winding forces an explicitly small rational anchor residual. -/
theorem anchor_residual_le_of_quadrupledBoxWinding_ne_zero
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : quadrupledBoxWinding p small ≠ 0) :
    normSq (p.eval small.anchor) ≤
      anchorResidualBound p ambient small := by
  by_cases residualSmall : normSq (p.eval small.anchor) ≤
      anchorResidualBound p ambient small
  · exact residualSmall
  · have large : anchorResidualBound p ambient small <
        normSq (p.eval small.anchor) := lt_of_not_ge residualSmall
    exact (windingNonzero
      (quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
        p degreePositive refines proper large)).elim

/-! ## Nearby clear points -/

/-- Finite quantitative data saying that a displayed clear point is close
enough to the fixed anchor of a nonzero-winding box to force constant
dominance. -/
structure NearbyClearPointCertificate
    (p : GaussianPolynomial) (ambient small : Box) where
  point : Gaussian
  point_mem : ambient.Contains point
  clearance : Coordinate
  radiusSq : Coordinate
  clearance_lower : clearance ≤ normSq (p.eval point)
  anchor_distance : normSq (point - small.anchor) ≤ radiusSq
  dominates :
    2 * (anchorResidualBound p ambient small +
      denseLipschitzBound p ambient * radiusSq) < clearance

/-- A sufficiently close clear point makes the anchor residual strictly
larger than its whole-box variation. -/
theorem anchorResidualBound_lt_of_nearby_clear_point
    (p : GaussianPolynomial) {ambient small : Box}
    (refines : small.Refines ambient)
    (certificate : NearbyClearPointCertificate p ambient small) :
    anchorResidualBound p ambient small < normSq (p.eval small.anchor) := by
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variationRaw := normSq_eval_sub_eval_le_denseLipschitzBound
    p certificate.point_mem anchorInside
  have variation : normSq (p.eval certificate.point - p.eval small.anchor) ≤
      denseLipschitzBound p ambient * certificate.radiusSq :=
    variationRaw.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        certificate.anchor_distance (denseLipschitzBound_pos p ambient).le)
  have valueIdentity : p.eval certificate.point = p.eval small.anchor +
      (p.eval certificate.point - p.eval small.anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im] <;>
      ring1
  have valueUpper := normSq_add_le_two (p.eval small.anchor)
    (p.eval certificate.point - p.eval small.anchor)
  rw [← valueIdentity] at valueUpper
  have chain :
      2 * (anchorResidualBound p ambient small +
          denseLipschitzBound p ambient * certificate.radiusSq) <
        2 * (normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient * certificate.radiusSq) := by
    calc
      2 * (anchorResidualBound p ambient small +
          denseLipschitzBound p ambient * certificate.radiusSq) <
          certificate.clearance := certificate.dominates
      _ ≤ normSq (p.eval certificate.point) := certificate.clearance_lower
      _ ≤ 2 * (normSq (p.eval small.anchor) +
          normSq (p.eval certificate.point - p.eval small.anchor)) :=
        valueUpper
      _ ≤ 2 * (normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient * certificate.radiusSq) := by
        have added : normSq (p.eval small.anchor) +
              normSq (p.eval certificate.point - p.eval small.anchor) ≤
            normSq (p.eval small.anchor) +
              denseLipschitzBound p ambient * certificate.radiusSq :=
          add_le_add (le_refl _) variation
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          added (by decide)
  have cancelledScale :
      anchorResidualBound p ambient small +
          denseLipschitzBound p ambient * certificate.radiusSq <
        normSq (p.eval small.anchor) +
          denseLipschitzBound p ambient * certificate.radiusSq := by
    apply RFAP.ConstructiveFraction.lt_of_mul_lt_mul_right_direct
      (c := 2) ?_ (by decide)
    simpa only [RFAP.ConstructiveFraction.mul_comm] using chain
  exact RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
    cancelledScale

/-- A nearby clear point contradicts nonzero raw winding by the finite
constant-dominance homotopy. -/
theorem quadrupledBoxWinding_eq_zero_of_nearby_clear_point
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (refines : small.Refines ambient) (proper : small.Proper)
    (certificate : NearbyClearPointCertificate p ambient small) :
    quadrupledBoxWinding p small = 0 :=
  quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt p degreePositive
    refines proper
      (anchorResidualBound_lt_of_nearby_clear_point p refines certificate)

/-! ## Finite Bézout derivative separation and the Newton point -/

abbrev SquarefreeCertificate (p : GaussianPolynomial) :=
  RFAP.Squarefree.SquarefreeCertificate p
abbrev DerivativeSeparation (p : GaussianPolynomial) (ambient : Box) :=
  RFAP.DerivativeSeparation.Certificate p ambient

/-- A fixed positive residual threshold computed from the left Bézout
coefficient on the ambient box. -/
def derivativeThreshold {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box) : Coordinate :=
  (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient).threshold

/-- A uniform positive derivative lower bound computed from the right
Bézout coefficient.  It is used only after the residual has crossed
`derivativeThreshold`. -/
def derivativeMargin {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box) : Coordinate :=
  (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient).margin

theorem derivativeThreshold_pos {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box) :
    0 < derivativeThreshold squarefree ambient :=
  (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient).threshold_pos

theorem derivativeMargin_pos {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box) :
    0 < derivativeMargin squarefree ambient :=
  (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient).margin_pos

/-- The finite Bézout identity supplies a uniform positive lower bound for
the derivative once the residual is below the left-coefficient threshold. -/
theorem derivativeMargin_le_of_small_residual
    {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box)
    {z : Gaussian} (inside : ambient.Contains z)
    (small : normSq (p.eval z) ≤ derivativeThreshold squarefree ambient) :
    derivativeMargin squarefree ambient ≤
      normSq ((RFAP.ConstructiveGCD.derivative p).eval z) :=
  (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient).lower inside small

/-- The finite Bézout identity forces the derivative to be nonzero whenever
the displayed residual is below the fixed threshold. -/
theorem derivative_ne_zero_of_small_residual
    {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box)
    {z : Gaussian} (inside : ambient.Contains z)
    (small : normSq (p.eval z) ≤ derivativeThreshold squarefree ambient) :
    (RFAP.ConstructiveGCD.derivative p).eval z ≠ 0 := by
  have margin := derivativeMargin_le_of_small_residual
    squarefree ambient inside small
  have marginPositive := derivativeMargin_pos squarefree ambient
  intro derivativeZero
  rw [derivativeZero, normSq_zero] at margin
  exact (not_lt_of_ge margin) marginPositive

/-- Executable Newton point based at the fixed rational anchor. -/
def anchorNewtonCenter (p : GaussianPolynomial) (small : Box) : Gaussian :=
  RFAP.NormalizedGaussian.value
    (RFAP.NormalizedEvaluation.newtonCenter p small.anchor)

@[simp] theorem anchorNewtonCenter_eq
    (p : GaussianPolynomial) (small : Box) :
    anchorNewtonCenter p small =
      small.anchor - p.eval small.anchor /
        (RFAP.ConstructiveGCD.derivative p).eval small.anchor := by
  simp only [anchorNewtonCenter, RFAP.NormalizedEvaluation.value_newtonCenter,
    RFAP.ConstructiveGCD.derivative]

theorem normSq_anchorNewtonCenter_sub_anchor
    {p : GaussianPolynomial} {small : Box}
    (derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval small.anchor ≠ 0) :
    normSq (anchorNewtonCenter p small - small.anchor) =
      normSq (p.eval small.anchor) *
        (normSq ((RFAP.ConstructiveGCD.derivative p).eval small.anchor))⁻¹ := by
  have displacement : anchorNewtonCenter p small - small.anchor =
      -(p.eval small.anchor /
        (RFAP.ConstructiveGCD.derivative p).eval small.anchor) := by
    rw [anchorNewtonCenter_eq]
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg,
      RFAP.ConstructiveGaussian.Gaussian.sub_eq_add_neg]
    ring1
  rw [displacement, normSq_neg,
    RFAP.ConstructiveGaussian.Gaussian.normSq_div _ _ derivativeNonzero]

/-- Proof-bearing finite output of the small raw-winding Newton step, using
only the displayed derivative-separation resource actually consumed by the
calculation. -/
structure SeparatedNewtonCenterCertificate
    (p : GaussianPolynomial) (ambient small : Box)
    (separation : DerivativeSeparation p ambient) where
  point : Gaussian
  point_eq : point = anchorNewtonCenter p small
  residual : normSq (p.eval small.anchor) ≤
    anchorResidualBound p ambient small
  derivativeNonzero :
    (RFAP.ConstructiveGCD.derivative p).eval small.anchor ≠ 0
  derivativeLower : separation.margin ≤
    normSq ((RFAP.ConstructiveGCD.derivative p).eval small.anchor)
  displacement : normSq (point - small.anchor) ≤
    anchorResidualBound p ambient small *
      (normSq ((RFAP.ConstructiveGCD.derivative p).eval small.anchor))⁻¹
  displacementMargin : normSq (point - small.anchor) ≤
    anchorResidualBound p ambient small / separation.margin

/-- Backward-compatible specialization to the exact squarefree Bézout
certificate. -/
abbrev NewtonCenterCertificate
    (p : GaussianPolynomial) (ambient small : Box)
    (squarefree : SquarefreeCertificate p) :=
  SeparatedNewtonCenterCertificate p ambient small
    (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)

/-- Construct the Newton certificate when the displayed point residual itself
meets the derivative threshold.  The enclosing-box residual majorant is still
retained for displacement accounting, but need not fit below the threshold. -/
def computeNewtonCenterOfPointResidualSeparated
    (p : GaussianPolynomial) {ambient small : Box}
    (separation : DerivativeSeparation p ambient)
    (refines : small.Refines ambient)
    (residual : normSq (p.eval small.anchor) ≤
      anchorResidualBound p ambient small)
    (pointThreshold : normSq (p.eval small.anchor) ≤ separation.threshold) :
    SeparatedNewtonCenterCertificate p ambient small separation := by
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have derivativeLower := separation.lower anchorInside pointThreshold
  have derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval small.anchor ≠ 0 := by
    intro derivativeZero
    rw [derivativeZero, normSq_zero] at derivativeLower
    exact (not_lt_of_ge derivativeLower) separation.margin_pos
  have derivativeNormPositive :
      0 < normSq ((RFAP.ConstructiveGCD.derivative p).eval small.anchor) :=
    normSq_pos derivativeNonzero
  have inverseBound :
      (normSq ((RFAP.ConstructiveGCD.derivative p).eval small.anchor))⁻¹ ≤
        separation.margin⁻¹ :=
    RFAP.ConstructiveFraction.inv_le_inv_of_pos_direct
      separation.margin_pos derivativeLower
  exact
    { point := anchorNewtonCenter p small
      point_eq := rfl
      residual := residual
      derivativeNonzero := derivativeNonzero
      derivativeLower := derivativeLower
      displacement := by
        rw [normSq_anchorNewtonCenter_sub_anchor derivativeNonzero]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          residual
          (RFAP.ConstructiveFraction.inv_pos_direct
            derivativeNormPositive).le
      displacementMargin := by
        rw [normSq_anchorNewtonCenter_sub_anchor derivativeNonzero]
        calc
          normSq (p.eval small.anchor) *
                (normSq
                  ((RFAP.ConstructiveGCD.derivative p).eval small.anchor))⁻¹ ≤
              anchorResidualBound p ambient small *
                (normSq
                  ((RFAP.ConstructiveGCD.derivative p).eval small.anchor))⁻¹ :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              residual
              (RFAP.ConstructiveFraction.inv_pos_direct
                derivativeNormPositive).le
          _ ≤ anchorResidualBound p ambient small * separation.margin⁻¹ :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              inverseBound (anchorResidualBound_nonneg p ambient small)
          _ = anchorResidualBound p ambient small / separation.margin := rfl }

/-- Construct the Newton certificate from an enclosing residual estimate and
an explicit derivative-separation resource. -/
def computeNewtonCenterOfResidualSeparated
    (p : GaussianPolynomial) {ambient small : Box}
    (separation : DerivativeSeparation p ambient)
    (refines : small.Refines ambient)
    (residual : normSq (p.eval small.anchor) ≤
      anchorResidualBound p ambient small)
    (threshold : anchorResidualBound p ambient small ≤
      separation.threshold) :
    SeparatedNewtonCenterCertificate p ambient small separation :=
  computeNewtonCenterOfPointResidualSeparated p separation refines residual
    (residual.trans threshold)

/-- Construct the Newton certificate directly from a residual estimate. -/
def computeNewtonCenterOfResidual
    (p : GaussianPolynomial) {ambient small : Box}
    (squarefree : SquarefreeCertificate p)
    (refines : small.Refines ambient)
    (residual : normSq (p.eval small.anchor) ≤
      anchorResidualBound p ambient small)
    (threshold : anchorResidualBound p ambient small ≤
      derivativeThreshold squarefree ambient) :
    NewtonCenterCertificate p ambient small squarefree :=
  computeNewtonCenterOfResidualSeparated p
    (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)
    refines residual threshold

/-- Raw-winding form using only explicit derivative separation. -/
def computeNewtonCenterOfRawWindingSeparated
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (separation : DerivativeSeparation p ambient)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : quadrupledBoxWinding p small ≠ 0)
    (threshold : anchorResidualBound p ambient small ≤
      separation.threshold) :
    SeparatedNewtonCenterCertificate p ambient small separation :=
  computeNewtonCenterOfResidualSeparated p separation refines
    (anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      p degreePositive refines proper windingNonzero)
    threshold

/-- Raw-winding form of the finite local Newton step. -/
def computeNewtonCenterOfRawWinding
    (p : GaussianPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : quadrupledBoxWinding p small ≠ 0)
    (threshold : anchorResidualBound p ambient small ≤
      derivativeThreshold squarefree ambient) :
    NewtonCenterCertificate p ambient small squarefree :=
  computeNewtonCenterOfRawWindingSeparated p degreePositive
    (RFAP.DerivativeSeparation.ofSquarefree squarefree ambient)
    refines proper windingNonzero threshold

end RFAP.LocalExtraction
