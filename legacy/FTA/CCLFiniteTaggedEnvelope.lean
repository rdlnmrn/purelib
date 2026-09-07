import FTA.CCLActiveCylinderProgress
import FTA.CCLObservedChordalEnvelope

/-!
# Common finite envelope interface for active CCL certificates

Phase-local canonical envelopes, initial-low raw-cylinder couplings, and
completed-history observation envelopes expose different numerical centers.
This file preserves those distinctions while giving all three one finite
word-tagged interface for region separation.
-/

namespace FTA
namespace CCLFiniteTaggedEnvelope

open CCL
open FTA.CCLActiveCylinderProgress
open FTA.CCLChordalEnvelope
open FTA.CCLObservedChordalEnvelope
open FTA.CCLRawCylinderEnvelope

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- A finite raw-word tag, a valid numerical projective center, and one
rational box reference certifying the displayed error.  The center need not
be the formal canonical truncation coordinate. -/
structure FiniteTaggedEnvelope where
  tag : TaggedTruncation
  box : RatBox
  center : Proj QI
  centerValid : center.HasNonzeroCoordinate
  reference : QI
  referenceInside : box.Contains reference
  errorSq : ℚ
  errorSqNonnegative : 0 ≤ errorSq
  certified : chordalSq (Proj.affine reference) center ≤ errorSq

namespace FiniteTaggedEnvelope

/-- A phase-local canonical coupled envelope already has the common finite
interface. -/
def ofCanonical (envelope : CCLChordalEnvelope.CoupledEnvelope) :
    FiniteTaggedEnvelope where
  tag := envelope.certificate.truncation
  box := envelope.box
  center := envelope.certificate.truncation.point
  centerValid := envelope.certificate.truncation.point_hasNonzeroCoordinate
  reference := envelope.certificate.reference
  referenceInside := envelope.referenceInside
  errorSq := envelope.radiusSq
  errorSqNonnegative := envelope.radiusSq_nonneg
  certified := envelope.contains_of_box_contains envelope.referenceInside

/-- Before the first completed block, use the honest represented box witness
as numerical center while retaining the raw prefix as its finite tag. -/
def ofInitialLow (coupling : BoxCylinderCoupling) : FiniteTaggedEnvelope where
  tag := coupling.cylinder.truncation
  box := coupling.box
  center := Proj.affine coupling.witness
  centerValid := Proj.affine_hasNonzeroCoordinate coupling.witness
  reference := coupling.witness
  referenceInside := coupling.witnessInside
  errorSq := coupling.errorSq
  errorSqNonnegative := coupling.errorSq_nonneg
  certified := by
    rw [chordalSq_eq_zero_of_equivalent
      (Proj.Equivalent.refl (Proj.affine coupling.witness))]
    exact coupling.errorSq_nonneg

/-- Completed-history observation coupling in the common finite interface. -/
def ofObserved (envelope : CoupledObservationEnvelope) :
    FiniteTaggedEnvelope where
  tag := envelope.tag
  box := envelope.box
  center := envelope.center
  centerValid := envelope.center_hasNonzeroCoordinate
  reference := envelope.reference
  referenceInside := envelope.referenceInside
  errorSq := envelope.radiusSq
  errorSqNonnegative := envelope.radiusSq_nonneg
  certified := envelope.contains_of_box_contains envelope.referenceInside

/-- Eliminate the two phase-local certificate variants without identifying
their distinct numerical meanings. -/
def ofPhaseCertificate
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : CCLActiveMetricTrack.State p ambient} {epsilon : ℚ}
    (certificate : ReachedMetricCertificate state epsilon) :
    FiniteTaggedEnvelope :=
  match certificate with
  | .tagged envelope _ _ _ => ofCanonical envelope
  | .initialLow coupling _ _ _ => ofInitialLow coupling

theorem ofPhaseCertificate_errorSq
    {p : GaussianPolynomial} {ambient : RatBox}
    {state : CCLActiveMetricTrack.State p ambient} {epsilon : ℚ}
    (certificate : ReachedMetricCertificate state epsilon) :
    (ofPhaseCertificate certificate).errorSq =
      match certificate with
      | .tagged envelope _ _ _ => envelope.radiusSq
      | .initialLow coupling _ _ _ => coupling.errorSq := by
  cases certificate <;> rfl

/-- Pairwise keep-apart for any mixture of the three finite certificate
forms.  Only their rational references and displayed errors are used. -/
theorem centers_not_equivalent_of_error_sum_lt_gap
    {B C : RatBox} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      B.xUpper + coordinateGap ≤ C.xLower ∨
      C.xUpper + coordinateGap ≤ B.xLower ∨
      B.yUpper + coordinateGap ≤ C.yLower ∨
      C.yUpper + coordinateGap ≤ B.yLower)
    {left right : FiniteTaggedEnvelope}
    (leftBox : left.box = B) (rightBox : right.box = C)
    (thin : 4 * (left.errorSq + right.errorSq) <
      chordalGapSq B C coordinateGap) :
    ¬left.center.Equivalent right.center := by
  intro equivalent
  have insideB : B.Contains left.reference := by
    simpa only [← leftBox] using left.referenceInside
  have insideC : C.Contains right.reference := by
    simpa only [← rightBox] using right.referenceInside
  have lower := chordalGapSq_le gapPositive coordinateSeparated insideB insideC
  have middleZero : chordalSq left.center right.center = 0 :=
    chordalSq_eq_zero_of_equivalent equivalent
  have rightTriangle := chordalSq_triangle_two left.centerValid
    right.centerValid (Proj.affine_hasNonzeroCoordinate right.reference)
  have rightBound :
      chordalSq right.center (Proj.affine right.reference) ≤ right.errorSq := by
    rw [chordalSq_comm]
    exact right.certified
  have leftToRightReference :
      chordalSq left.center (Proj.affine right.reference) ≤
        2 * right.errorSq := by
    linarith [rightTriangle, middleZero, rightBound]
  have leftTriangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate left.reference) left.centerValid
      (Proj.affine_hasNonzeroCoordinate right.reference)
  have upper :
      chordalSq (Proj.affine left.reference)
          (Proj.affine right.reference) ≤
        4 * (left.errorSq + right.errorSq) := by
    linarith [leftTriangle, left.certified, leftToRightReference,
      left.errorSqNonnegative, right.errorSqNonnegative]
  linarith

end FiniteTaggedEnvelope

end CCLFiniteTaggedEnvelope
end FTA
