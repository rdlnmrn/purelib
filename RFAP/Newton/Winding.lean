import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.LocalExtraction
import RFAP.Winding.Affine

/-!
# Choice-free Newton winding transfer

The finite Bézout certificate supplies a positive derivative margin at a
small raw-winding source.  On a rational square centered at its exact Newton
point, the affine term has winding four and explicit radial clearance.  The
finite Horner Taylor scan bounds the remaining coefficient program, allowing
one constructive Rouché transfer.
-/

namespace RFAP.NewtonWinding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev NewtonCenterCertificate :=
  RFAP.LocalExtraction.NewtonCenterCertificate
abbrev DerivativeSeparation :=
  RFAP.LocalExtraction.DerivativeSeparation
abbrev SeparatedNewtonCenterCertificate :=
  RFAP.LocalExtraction.SeparatedNewtonCenterCertificate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PolynomialBounds
open RFAP.GlobalWinding
open RFAP.Winding
open RFAP.WindingHomotopy
open RFAP.LocalExtraction
open RFAP.AffineWinding

/-- The affine first-order term, centered at the exact rational Newton point
of the fixed source anchor. -/
def newtonLinearization (p : GaussianPolynomial) (source : Box) :
    GaussianPolynomial :=
  affineCoordinate ((RFAP.ConstructiveGCD.derivative p).eval source.anchor)
    (anchorNewtonCenter p source)

/-- The remaining finite coefficient program. -/
def newtonError (p : GaussianPolynomial) (source : Box) :
    GaussianPolynomial :=
  p.normalize - newtonLinearization p source

/-- The affine term and its coefficientwise Newton error restore the exact
normalized finite coefficient list in degree at least two. -/
theorem newtonLinearization_add_error_eq_normalize
    {p : GaussianPolynomial} (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (source : Box)
    (derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval source.anchor ≠ 0) :
    newtonLinearization p source + newtonError p source = p.normalize := by
  let slope := (RFAP.ConstructiveGCD.derivative p).eval source.anchor
  let center := anchorNewtonCenter p source
  have polynomialNonzero : p.isZero = false :=
    isZero_false_of_natDegree_pos
      ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)
  rw [newtonError, newtonLinearization,
    affineCoordinate_eq_linear derivativeNonzero center]
  exact linear_add_sub_linear_of_normalized
    (normalize_normalize p) (by simpa using polynomialNonzero)
    (by simpa using degreeAtLeastTwo) derivativeNonzero

/-- The Newton-centered affine program is exactly the ordinary first-order
Taylor expression at the source anchor. -/
theorem newtonLinearization_eval
    (p : GaussianPolynomial) (source : Box) (z : Gaussian)
    (derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval source.anchor ≠ 0) :
    (newtonLinearization p source).eval z =
      p.eval source.anchor +
        (RFAP.ConstructiveGCD.derivative p).eval source.anchor *
          (z - source.anchor) := by
  let slope := (RFAP.ConstructiveGCD.derivative p).eval source.anchor
  let value := p.eval source.anchor
  rw [newtonLinearization, affineCoordinate_eval]
  rw [anchorNewtonCenter_eq]
  change slope * (z - (source.anchor - value / slope)) =
    value + slope * (z - source.anchor)
  calc
    slope * (z - (source.anchor - value / slope)) =
        slope * (z - source.anchor) + slope * (value / slope) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;>
        ring1
    _ = slope * (z - source.anchor) + value := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_comm slope (value / slope),
        RFAP.ExplicitField.div_mul_cancel value derivativeNonzero]
    _ = value + slope * (z - source.anchor) :=
      RFAP.ConstructiveGaussian.Gaussian.add_comm _ _

/-- The executable Taylor scan bounds the finite Newton error program. -/
theorem normSq_newtonError_le
    (p : GaussianPolynomial) {ambient source : Box}
    (sourceRefines : source.Refines ambient) {z : Gaussian}
    (inside : ambient.Contains z)
    (derivativeNonzero :
      (RFAP.ConstructiveGCD.derivative p).eval source.anchor ≠ 0) :
    normSq ((newtonError p source).eval z) ≤
      denseTaylorRemainderBound p ambient *
        normSq (z - source.anchor) ^ 2 := by
  have anchorInside : ambient.Contains source.anchor :=
    sourceRefines.contains source.contains_anchor
  have taylor :=
    normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      p inside anchorInside
  have errorIdentity : (newtonError p source).eval z =
      p.eval z - p.eval source.anchor -
        (RFAP.ConstructiveGCD.derivative p).eval source.anchor *
          (z - source.anchor) := by
    rw [newtonError, eval_sub, eval_normalize,
      newtonLinearization_eval p source z derivativeNonzero]
    apply RFAP.ConstructiveGaussian.Gaussian.ext
    · change (p.eval z).re -
          ((p.eval source.anchor).re +
            ((RFAP.ConstructiveGCD.derivative p).eval source.anchor *
              (z - source.anchor)).re) =
        ((p.eval z).re - (p.eval source.anchor).re) -
          ((RFAP.ConstructiveGCD.derivative p).eval source.anchor *
            (z - source.anchor)).re
      ring1
    · change (p.eval z).im -
          ((p.eval source.anchor).im +
            ((RFAP.ConstructiveGCD.derivative p).eval source.anchor *
              (z - source.anchor)).im) =
        ((p.eval z).im - (p.eval source.anchor).im) -
          ((RFAP.ConstructiveGCD.derivative p).eval source.anchor *
            (z - source.anchor)).im
      ring1
  rw [errorIdentity]
  exact taylor

/-- If the Newton displacement is at most `r²`, every point of the
centered square is within `6r²` (in squared norm) of the source anchor. -/
theorem centeredSquare_normSq_sub_anchor_le
    {p : GaussianPolynomial} {source : Box} {r : Coordinate}
    (positive : 0 < r)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian}
    (inside : (centeredSquare (anchorNewtonCenter p source) r positive.le).Contains z) :
    normSq (z - source.anchor) ≤ 6 * r ^ 2 := by
  have radial := centeredSquare_normSq_sub_center_le
    (anchorNewtonCenter p source) positive.le inside
  have decomposition : z - source.anchor =
      (z - anchorNewtonCenter p source) +
        (anchorNewtonCenter p source - source.anchor) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring1
  rw [decomposition]
  have sumBound := normSq_add_le_two
    (z - anchorNewtonCenter p source)
    (anchorNewtonCenter p source - source.anchor)
  calc
    normSq ((z - anchorNewtonCenter p source) +
        (anchorNewtonCenter p source - source.anchor)) ≤
        2 * (normSq (z - anchorNewtonCenter p source) +
          normSq (anchorNewtonCenter p source - source.anchor)) := sumBound
    _ ≤ 2 * (2 * r ^ 2 + r ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add radial displacementSmall) (by decide)
    _ = 6 * r ^ 2 := by ring1

/-- Coarse Taylor-error budget on the Newton square. -/
def newtonErrorBudget (p : GaussianPolynomial) (ambient : Box)
    (r : Coordinate) : Coordinate :=
  36 * denseTaylorRemainderBound p ambient * (r ^ 2) ^ 2

/-- The positive norm gap left after paying the complete Taylor budget. -/
def newtonDominanceMargin {p : GaussianPolynomial}
    (squarefree : SquarefreeCertificate p) (ambient : Box)
    (r : Coordinate) : Coordinate :=
  derivativeMargin squarefree ambient * r ^ 2 -
    newtonErrorBudget p ambient r

theorem newtonError_le_budget
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    normSq ((newtonError p source).eval z) ≤
      newtonErrorBudget p ambient r := by
  have insideTarget := boundary.1
  have insideAmbient := targetRefines.contains insideTarget
  have distance := centeredSquare_normSq_sub_anchor_le
    positive displacementSmall insideTarget
  have distanceSquared : normSq (z - source.anchor) ^ 2 ≤
      (6 * r ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (normSq_nonneg (z - source.anchor)) distance 2
  have rawError := normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    normSq ((newtonError p source).eval z) ≤
        denseTaylorRemainderBound p ambient *
          normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ denseTaylorRemainderBound p ambient * (6 * r ^ 2) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        distanceSquared (denseTaylorRemainderBound_pos p ambient).le
    _ = newtonErrorBudget p ambient r := by
      dsimp only [newtonErrorBudget]
      ring1

theorem newtonDominanceMargin_pos
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    {r : Coordinate} (positive : 0 < r)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        derivativeMargin squarefree ambient) :
    0 < newtonDominanceMargin squarefree ambient r := by
  have radiusSquarePositive :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  let base := 36 * denseTaylorRemainderBound p ambient * r ^ 2
  have thirtySixPositive : (0 : Coordinate) < 36 :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 36) (by decide)
  have basePositive : 0 < base :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct thirtySixPositive
        (denseTaylorRemainderBound_pos p ambient)) radiusSquarePositive
  have halfStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have coefficientBound :
      36 * denseTaylorRemainderBound p ambient * r ^ 2 <
        derivativeMargin squarefree ambient := by
    change base < derivativeMargin squarefree ambient
    exact halfStrict.trans_le taylorSmall
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    coefficientBound radiusSquarePositive
  apply RFAP.ConstructiveFraction.sub_pos_direct
  change newtonErrorBudget p ambient r <
    derivativeMargin squarefree ambient * r ^ 2
  calc
    newtonErrorBudget p ambient r =
        (36 * denseTaylorRemainderBound p ambient * r ^ 2) * r ^ 2 := by
      dsimp only [newtonErrorBudget]
      ring1
    _ < derivativeMargin squarefree ambient * r ^ 2 := scaled

theorem newtonLinearization_boundary_lower
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    {r : Coordinate} (positive : 0 < r) {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    derivativeMargin squarefree ambient * r ^ 2 ≤
      normSq ((newtonLinearization p source).eval z) := by
  let affineClearance := affineCoordinate_boundaryClearance
    newton.derivativeNonzero (anchorNewtonCenter p source) positive
  have affineLower := affineClearance.lower z boundary
  have affineLowerExact :
      normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) *
          r ^ 2 ≤ normSq ((newtonLinearization p source).eval z) := by
    exact affineLower
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    newton.derivativeLower
    (RFAP.ConstructiveFraction.sq_nonneg_direct r)).trans affineLowerExact

private theorem gap_le_gap
    {eta budget error linear : Coordinate}
    (errorBound : error ≤ budget) (linearBound : eta ≤ linear) :
    eta - budget ≤ linear - error := by
  apply (le_sub_iff_add_le).mpr
  calc
    eta - budget + error ≤ eta - budget + budget :=
      add_le_add_right errorBound _
    _ = eta := by ring1
    _ ≤ linear := linearBound

theorem newtonDominanceMargin_le
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    newtonDominanceMargin squarefree ambient r ≤
      normSq ((newtonLinearization p source).eval z) -
        normSq ((newtonError p source).eval z) := by
  have errorUpper : normSq ((newtonError p source).eval z) ≤
      newtonErrorBudget p ambient r :=
    newtonError_le_budget (p := p) (ambient := ambient) (source := source)
      (squarefree := squarefree) newton sourceRefines positive targetRefines
      displacementSmall boundary
  have linearLower : derivativeMargin squarefree ambient * r ^ 2 ≤
      normSq ((newtonLinearization p source).eval z) :=
    newtonLinearization_boundary_lower (p := p) (ambient := ambient)
      (source := source) (squarefree := squarefree) newton positive boundary
  exact gap_le_gap errorUpper linearLower

/-- Taylor dominance on the complete Newton-centered square boundary. -/
def newtonBoundaryNormDominance
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        derivativeMargin squarefree ambient) :
    BoundaryNormDominance
      (newtonLinearization p source) (newtonError p source)
      (centeredSquare (anchorNewtonCenter p source) r positive.le) where
  margin := newtonDominanceMargin squarefree ambient r
  positive := newtonDominanceMargin_pos squarefree positive taylorSmall
  lower := fun _z boundary => newtonDominanceMargin_le newton sourceRefines
    positive targetRefines displacementSmall boundary

/-- The complete finite Rouché step, separated from the purely coefficient
identity that adds the Newton error back to the normalized polynomial. -/
theorem quadrupledBoxWinding_eq_four_of_newtonSquare_of_sumIdentity
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        derivativeMargin squarefree ambient)
    (sumIdentity : newtonLinearization p source + newtonError p source =
      p.normalize) :
    quadrupledBoxWinding p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) = 4 := by
  let target := centeredSquare (anchorNewtonCenter p source) r positive.le
  have transfer := quadrupledBoxWinding_add_of_boundaryNormDominance
    (newtonLinearization p source) (newtonError p source) target
    (centeredSquare_proper (anchorNewtonCenter p source) positive)
    (affineCoordinate_boundaryClearance newton.derivativeNonzero
      (anchorNewtonCenter p source) positive)
    (newtonBoundaryNormDominance newton sourceRefines positive targetRefines
      displacementSmall taylorSmall)
  rw [sumIdentity] at transfer
  calc
    quadrupledBoxWinding p target =
        quadrupledBoxWinding p.normalize target :=
      (quadrupledBoxWinding_normalize p target).symm
    _ = quadrupledBoxWinding (newtonLinearization p source) target := transfer
    _ = 4 := quadrupledBoxWinding_affineCoordinate_centeredSquare
      newton.derivativeNonzero (anchorNewtonCenter p source) positive

/-- Complete choice-free Newton-square winding theorem in degree at least
two. -/
theorem quadrupledBoxWinding_eq_four_of_newtonSquare
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        derivativeMargin squarefree ambient) :
    quadrupledBoxWinding p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) = 4 :=
  quadrupledBoxWinding_eq_four_of_newtonSquare_of_sumIdentity newton
    sourceRefines positive targetRefines displacementSmall taylorSmall
    (newtonLinearization_add_error_eq_normalize degreeAtLeastTwo source
      newton.derivativeNonzero)

/-- Coefficient-computed boundary clearance carried by the extracted Newton
square. -/
def newtonSquareBoundaryClearance
    {p : GaussianPolynomial} {ambient source : Box}
    {squarefree : SquarefreeCertificate p}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : NewtonCenterCertificate p ambient source squarefree)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        derivativeMargin squarefree ambient) :
    RFAP.BoxClearance.BoundaryClearance p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) := by
  let target := centeredSquare (anchorNewtonCenter p source) r positive.le
  let dominance := newtonBoundaryNormDominance newton sourceRefines positive
    targetRefines displacementSmall taylorSmall
  have sumClearance :=
    boundaryClearance_add_of_boundaryNormDominance
      (newtonLinearization p source) (newtonError p source) target
      (centeredSquare_proper (anchorNewtonCenter p source) positive) dominance
  have sumIdentity := newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at sumClearance
  exact RFAP.BoxClearance.BoundaryClearance.ofNormalize sumClearance

/-! ## Newton transfer from an explicit derivative separation -/

/-- The same Taylor gap, parameterized by the exact quantitative resource
rather than by the particular Bézout certificate from which it arose. -/
def separatedNewtonDominanceMargin
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    (r : Coordinate) : Coordinate :=
  separation.margin * r ^ 2 - newtonErrorBudget p ambient r

theorem separatedNewtonDominanceMargin_pos
    {p : GaussianPolynomial} {ambient : Box}
    (separation : DerivativeSeparation p ambient)
    {r : Coordinate} (positive : 0 < r)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    0 < separatedNewtonDominanceMargin separation r := by
  have radiusSquarePositive :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  let base := 36 * denseTaylorRemainderBound p ambient * r ^ 2
  have thirtySixPositive : (0 : Coordinate) < 36 :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 36) (by decide)
  have basePositive : 0 < base :=
    RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct thirtySixPositive
        (denseTaylorRemainderBound_pos p ambient)) radiusSquarePositive
  have halfStrict : base < 2 * base := by
    calc
      base = 0 + base := by ring1
      _ < base + base :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct basePositive base
      _ = 2 * base := by ring1
  have coefficientBound :
      36 * denseTaylorRemainderBound p ambient * r ^ 2 <
        separation.margin := by
    change base < separation.margin
    exact halfStrict.trans_le taylorSmall
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    coefficientBound radiusSquarePositive
  apply RFAP.ConstructiveFraction.sub_pos_direct
  change newtonErrorBudget p ambient r < separation.margin * r ^ 2
  calc
    newtonErrorBudget p ambient r =
        (36 * denseTaylorRemainderBound p ambient * r ^ 2) * r ^ 2 := by
      dsimp only [newtonErrorBudget]
      ring1
    _ < separation.margin * r ^ 2 := scaled

theorem separatedNewtonError_le_budget
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    normSq ((newtonError p source).eval z) ≤
      newtonErrorBudget p ambient r := by
  have insideTarget := boundary.1
  have insideAmbient := targetRefines.contains insideTarget
  have distance := centeredSquare_normSq_sub_anchor_le
    positive displacementSmall insideTarget
  have distanceSquared : normSq (z - source.anchor) ^ 2 ≤
      (6 * r ^ 2) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (normSq_nonneg (z - source.anchor)) distance 2
  have rawError := normSq_newtonError_le p sourceRefines insideAmbient
    newton.derivativeNonzero
  calc
    normSq ((newtonError p source).eval z) ≤
        denseTaylorRemainderBound p ambient *
          normSq (z - source.anchor) ^ 2 := rawError
    _ ≤ denseTaylorRemainderBound p ambient * (6 * r ^ 2) ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        distanceSquared (denseTaylorRemainderBound_pos p ambient).le
    _ = newtonErrorBudget p ambient r := by
      dsimp only [newtonErrorBudget]
      ring1

theorem separatedNewtonLinearization_boundary_lower
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    {r : Coordinate} (positive : 0 < r) {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    separation.margin * r ^ 2 ≤
      normSq ((newtonLinearization p source).eval z) := by
  let affineClearance := affineCoordinate_boundaryClearance
    newton.derivativeNonzero (anchorNewtonCenter p source) positive
  have affineLower := affineClearance.lower z boundary
  have affineLowerExact :
      normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) *
          r ^ 2 ≤ normSq ((newtonLinearization p source).eval z) :=
    affineLower
  exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    newton.derivativeLower
    (RFAP.ConstructiveFraction.sq_nonneg_direct r)).trans affineLowerExact

theorem separatedNewtonDominanceMargin_le
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    separatedNewtonDominanceMargin separation r ≤
      normSq ((newtonLinearization p source).eval z) -
        normSq ((newtonError p source).eval z) := by
  have errorUpper : normSq ((newtonError p source).eval z) ≤
      newtonErrorBudget p ambient r :=
    separatedNewtonError_le_budget newton sourceRefines positive targetRefines
      displacementSmall boundary
  have linearLower : separation.margin * r ^ 2 ≤
      normSq ((newtonLinearization p source).eval z) :=
    separatedNewtonLinearization_boundary_lower newton positive boundary
  exact gap_le_gap errorUpper linearLower

private theorem gaussian_dot_sq_le_product_normSq
    (left sum : Gaussian) :
    (left.re * sum.re + left.im * sum.im) ^ 2 ≤
      normSq left * normSq sum := by
  apply sub_nonneg.mp
  calc
    0 ≤ (left.re * sum.im - left.im * sum.re) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = normSq left * normSq sum -
        (left.re * sum.re + left.im * sum.im) ^ 2 := by
      simp only [normSq]
      ring1

/-- Turn norm dominance into a boundary clearance with a deliberately
displayed bound.  `majorant` is any positive upper bound for the dominant
summand on the boundary; retaining it in the result makes later coefficient
precision requests predictable before the next polynomial is read. -/
def boundaryClearance_add_of_dominance_with_majorant
    (base error : GaussianPolynomial) (box : Box)
    (dominance : BoundaryNormDominance base error box)
    (majorant : Coordinate) (majorantPositive : 0 < majorant)
    (baseUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary box z →
        normSq (base.eval z) ≤ majorant) :
    RFAP.BoxClearance.BoundaryClearance (base + error) box where
  bound := dominance.margin ^ 2 / (4 * majorant)
  positive := RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct dominance.positive 2)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide) majorantPositive)
  lower := by
    intro z boundary
    let left := base.eval z
    let right := error.eval z
    let sum := (base + error).eval z
    let dot := left.re * sum.re + left.im * sum.im
    have sumIdentity : sum = left + right := by
      dsimp only [sum, left, right]
      exact RFAP.ComputablePolynomial.DensePolynomial.eval_add _ _ _
    have sumNonnegative : 0 ≤ normSq sum := normSq_nonneg sum
    have doubledDot : 2 * dot =
        (normSq left - normSq right) + normSq sum := by
      dsimp only [dot]
      rw [sumIdentity]
      simp only [normSq, add_re, add_im]
      ring1
    have marginLeDoubledDot : dominance.margin ≤ 2 * dot := by
      rw [doubledDot]
      exact (dominance.lower z boundary).trans
        (le_add_of_nonneg_right sumNonnegative)
    have squaredMargin : dominance.margin ^ 2 ≤ (2 * dot) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct dominance.positive.le
        marginLeDoubledDot 2
    have dotCauchy : dot ^ 2 ≤ normSq left * normSq sum := by
      dsimp only [dot]
      exact gaussian_dot_sq_le_product_normSq left sum
    have scaledCauchy : (2 * dot) ^ 2 ≤
        (4 * majorant) * normSq sum := by
      calc
        (2 * dot) ^ 2 = 4 * dot ^ 2 := by ring1
        _ ≤ 4 * (normSq left * normSq sum) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            dotCauchy (by decide)
        _ ≤ 4 * (majorant * normSq sum) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (baseUpper z boundary) sumNonnegative) (by decide)
        _ = (4 * majorant) * normSq sum := by ring1
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct
        (by decide) majorantPositive)).2
    rw [RFAP.ConstructiveFraction.mul_comm (normSq sum)]
    exact squaredMargin.trans scaledCauchy

@[simp] theorem boundaryClearance_add_of_dominance_with_majorant_bound
    (base error : GaussianPolynomial) (box : Box)
    (dominance : BoundaryNormDominance base error box)
    (majorant : Coordinate) (majorantPositive : 0 < majorant)
    (baseUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary box z →
        normSq (base.eval z) ≤ majorant) :
    (boundaryClearance_add_of_dominance_with_majorant base error box
      dominance majorant majorantPositive baseUpper).bound =
        dominance.margin ^ 2 / (4 * majorant) := rfl

/-- Explicit upper bound for the Newton linearization on its centered-square
boundary. -/
def separatedNewtonLinearizationMajorant
    (p : GaussianPolynomial) (ambient : Box) (r : Coordinate) : Coordinate :=
  2 * denseEvalNormMajorant (RFAP.ConstructiveGCD.derivative p) ambient * r ^ 2

theorem separatedNewtonLinearizationMajorant_pos
    (p : GaussianPolynomial) (ambient : Box) {r : Coordinate}
    (positive : 0 < r) :
    0 < separatedNewtonLinearizationMajorant p ambient r :=
  RFAP.ConstructiveFraction.mul_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (denseEvalNormMajorant_pos
        (RFAP.ConstructiveGCD.derivative p) ambient))
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2)

theorem newtonLinearization_boundary_le_majorant
    {p : GaussianPolynomial} {ambient source : Box}
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r) {z : Gaussian}
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (centeredSquare (anchorNewtonCenter p source) r positive.le) z) :
    normSq ((newtonLinearization p source).eval z) ≤
      separatedNewtonLinearizationMajorant p ambient r := by
  have sourceAnchorInside : ambient.Contains source.anchor :=
    sourceRefines.contains source.contains_anchor
  have derivativeBound := normSq_eval_le_denseEvalNormMajorant
    (RFAP.ConstructiveGCD.derivative p) sourceAnchorInside
  have radial := centeredSquare_normSq_sub_center_le
    (anchorNewtonCenter p source) positive.le boundary.1
  rw [newtonLinearization, affineCoordinate_eval, normSq_mul]
  calc
    normSq ((RFAP.ConstructiveGCD.derivative p).eval source.anchor) *
        normSq (z - anchorNewtonCenter p source) ≤
      denseEvalNormMajorant (RFAP.ConstructiveGCD.derivative p) ambient *
        (2 * r ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct derivativeBound radial
        (normSq_nonneg (z - anchorNewtonCenter p source))
        (denseEvalNormMajorant_pos
          (RFAP.ConstructiveGCD.derivative p) ambient).le
    _ = separatedNewtonLinearizationMajorant p ambient r := by
      unfold separatedNewtonLinearizationMajorant
      ring1

/-- Taylor dominance on the Newton square from a generic separation
certificate. -/
def separatedNewtonBoundaryNormDominance
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    BoundaryNormDominance
      (newtonLinearization p source) (newtonError p source)
      (centeredSquare (anchorNewtonCenter p source) r positive.le) where
  margin := separatedNewtonDominanceMargin separation r
  positive := separatedNewtonDominanceMargin_pos separation positive taylorSmall
  lower := fun _z boundary => separatedNewtonDominanceMargin_le newton
    sourceRefines positive targetRefines displacementSmall boundary

/-- Complete Newton-square winding transfer from explicit derivative
separation. -/
theorem quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    quadrupledBoxWinding p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) = 4 := by
  let target := centeredSquare (anchorNewtonCenter p source) r positive.le
  have transfer := quadrupledBoxWinding_add_of_boundaryNormDominance
    (newtonLinearization p source) (newtonError p source) target
    (centeredSquare_proper (anchorNewtonCenter p source) positive)
    (affineCoordinate_boundaryClearance newton.derivativeNonzero
      (anchorNewtonCenter p source) positive)
    (separatedNewtonBoundaryNormDominance newton sourceRefines positive
      targetRefines displacementSmall taylorSmall)
  have sumIdentity := newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  rw [sumIdentity] at transfer
  calc
    quadrupledBoxWinding p target =
        quadrupledBoxWinding p.normalize target :=
      (quadrupledBoxWinding_normalize p target).symm
    _ = quadrupledBoxWinding (newtonLinearization p source) target := transfer
    _ = 4 := quadrupledBoxWinding_affineCoordinate_centeredSquare
      newton.derivativeNonzero (anchorNewtonCenter p source) positive

/-- Boundary clearance carried by a separated Newton square when the caller
supplies any positive upper bound for the Newton linearization on the square
boundary. -/
def separatedNewtonSquareBoundaryClearanceWithMajorant
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary
        (centeredSquare (anchorNewtonCenter p source) r positive.le) z →
      normSq ((newtonLinearization p source).eval z) ≤
        linearizationMajorant) :
    RFAP.BoxClearance.BoundaryClearance p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) := by
  let target := centeredSquare (anchorNewtonCenter p source) r positive.le
  let dominance := separatedNewtonBoundaryNormDominance newton sourceRefines
    positive targetRefines displacementSmall taylorSmall
  let sumClearance := boundaryClearance_add_of_dominance_with_majorant
    (newtonLinearization p source) (newtonError p source) target dominance
    linearizationMajorant linearizationMajorantPositive linearizationUpper
  have sumIdentity := newtonLinearization_add_error_eq_normalize
    degreeAtLeastTwo source newton.derivativeNonzero
  have sumBound : sumClearance.bound =
      separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * linearizationMajorant) := by
    change sumClearance.bound = dominance.margin ^ 2 /
      (4 * linearizationMajorant)
    exact boundaryClearance_add_of_dominance_with_majorant_bound
      (newtonLinearization p source) (newtonError p source) target dominance
      linearizationMajorant linearizationMajorantPositive linearizationUpper
  exact
    { bound := separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * linearizationMajorant)
      positive := by
        rw [← sumBound]
        exact sumClearance.positive
      lower := by
        intro z boundary
        rw [← sumBound]
        calc
          sumClearance.bound ≤
              normSq
                ((newtonLinearization p source +
                  newtonError p source).eval z) :=
            sumClearance.lower z boundary
          _ = normSq (p.eval z) := by
            rw [sumIdentity,
              RFAP.ComputablePolynomial.DensePolynomial.eval_normalize] }

theorem separatedNewtonSquareBoundaryClearanceWithMajorant_bound
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Coordinate)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian,
      RFAP.BoxClearance.OnBoxBoundary
        (centeredSquare (anchorNewtonCenter p source) r positive.le) z →
      normSq ((newtonLinearization p source).eval z) ≤
        linearizationMajorant) :
    (separatedNewtonSquareBoundaryClearanceWithMajorant degreeAtLeastTwo
      newton sourceRefines positive targetRefines displacementSmall
      taylorSmall linearizationMajorant linearizationMajorantPositive
      linearizationUpper).bound =
        separatedNewtonDominanceMargin separation r ^ 2 /
          (4 * linearizationMajorant) := by
  unfold separatedNewtonSquareBoundaryClearanceWithMajorant
  rfl

/-- Coefficient-computed specialization using the ordinary dense derivative
majorant. -/
def separatedNewtonSquareBoundaryClearance
    {p : GaussianPolynomial} {ambient source : Box}
    {separation : DerivativeSeparation p ambient}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (newton : SeparatedNewtonCenterCertificate
      p ambient source separation)
    (sourceRefines : source.Refines ambient)
    {r : Coordinate} (positive : 0 < r)
    (targetRefines :
      (centeredSquare (anchorNewtonCenter p source) r positive.le).Refines ambient)
    (displacementSmall :
      normSq (anchorNewtonCenter p source - source.anchor) ≤ r ^ 2)
    (taylorSmall :
      2 * (36 * denseTaylorRemainderBound p ambient * r ^ 2) ≤
        separation.margin) :
    RFAP.BoxClearance.BoundaryClearance p
      (centeredSquare (anchorNewtonCenter p source) r positive.le) :=
  separatedNewtonSquareBoundaryClearanceWithMajorant degreeAtLeastTwo newton
    sourceRefines positive targetRefines displacementSmall taylorSmall
    (separatedNewtonLinearizationMajorant p ambient r)
    (separatedNewtonLinearizationMajorant_pos p ambient positive)
    (fun _z boundary => newtonLinearization_boundary_le_majorant
      sourceRefines positive boundary)

end RFAP.NewtonWinding
