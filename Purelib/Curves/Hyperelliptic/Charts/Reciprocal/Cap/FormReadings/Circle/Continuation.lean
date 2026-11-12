module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Transport
import Purelib.Tactic.Ring

/-! # Sheet persistence on the actual cap power-circle

The retained parameter circle uses the cap's original power coordinate.
Both degree parities retain their actual curved points. Original model-box
containment and the existing edge transition give one overlap sign; the
straight segment is only an erased proof inside those common boxes.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial (RootAligned)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial.Model (overlapRefine)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {base : Canonical}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    (actual : { value : RationalCurve // value = circle base })

include unitBound collarBound

/-- Two actual inverse models have one overlap flip along the supplied circle's genuine cap coordinate arc.

The original radius bounds place the cap model throughout that arc. The
other model supplies only its true box containment. The existing affine
edge theorem compares the actual endpoints inside their common boxes; it
does not replace the curved integration path or assume sheet agreement.
-/
theorem model_flip_eq {otherBox : Geometry.Rational.Box}
    (other : InverseRootPolynomial.Model cap.polynomial otherBox) (interval : Interval.Bounds)
    (otherInside : ∀ time, interval.Contains time →
      otherBox.Contains (Primitives.point curve (actual.val.point time)))
    {first last : Fraction.Rational} (firstInside : interval.Contains first) (lastInside : interval.Contains last) :
    (OverlapSample.build cap.model other (Primitives.point curve (actual.val.point first))).alignment.flip =
      (OverlapSample.build cap.model other (Primitives.point curve (actual.val.point last))).alignment.flip := by
  exact (InverseModelEdgeTransition.EdgeTransition.build cap.model other
    (Primitives.point curve (actual.val.point first)) (Primitives.point curve (actual.val.point last))
    (point_inside base unitBound collarBound actual first) (point_inside base unitBound collarBound actual last)
    (otherInside first firstInside) (otherInside last lastInside)).flip_eq_finish

/-- Sample an actual cap power-circle point with the same supplied initial overlap flip.

Both endpoint containments build the original edge transition with the
supplied whole start sample. Its original endpoint sampler reuses that
literal flip and both models. Equal-point transport retains its entire
result; no new sign comparison or root owner is selected.
-/
def sampleAt {otherBox : Geometry.Rational.Box}
    {other : InverseRootPolynomial.Model cap.polynomial otherBox} (interval : Interval.Bounds)
    (otherInside : ∀ time, interval.Contains time →
      otherBox.Contains (Primitives.point curve (actual.val.point time)))
    {first : Fraction.Rational} (firstInside : interval.Contains first)
    (sample : OverlapSample cap.model other (Primitives.point curve (actual.val.point first)))
    (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
    OverlapSample cap.model other (Primitives.point curve (actual.val.point parameter)) := by
  let firstPoint := Primitives.point curve (actual.val.point first)
  let point := Primitives.point curve (actual.val.point parameter)
  let edge : InverseModelEdgeTransition.EdgeTransition cap.model other firstPoint point :=
    ⟨point_inside base unitBound collarBound actual first, point_inside base unitBound collarBound actual parameter,
      otherInside first firstInside, otherInside parameter inside, sample⟩
  let moved := edge.sampleAt 1 ⟨by decide +kernel, le_rfl⟩
  exact Eq.mp (congrArg (fun value => OverlapSample cap.model other value)
    (InverseModelEdgeTransition.line_one firstPoint point)) moved

/-- The actual cap-circle sample reuses the original whole overlap's selected flip. -/
theorem sampleAt_flip {otherBox : Geometry.Rational.Box}
    {other : InverseRootPolynomial.Model cap.polynomial otherBox} (interval : Interval.Bounds)
    (otherInside : ∀ time, interval.Contains time →
      otherBox.Contains (Primitives.point curve (actual.val.point time)))
    {first : Fraction.Rational} (firstInside : interval.Contains first)
    (sample : OverlapSample cap.model other (Primitives.point curve (actual.val.point first)))
    (parameter : Fraction.Rational) (inside : interval.Contains parameter) :
    (sampleAt (unitBound := unitBound) (collarBound := collarBound) actual interval otherInside
      firstInside sample parameter inside).alignment.flip = sample.alignment.flip := by
  have castFlip {first last : Canonical} (equal : first = last)
      (retained : OverlapSample cap.model other first) :
      (Eq.mp (congrArg (fun value => OverlapSample cap.model other value) equal) retained).alignment.flip =
        retained.alignment.flip := by
    cases equal
    rfl
  unfold sampleAt
  exact (castFlip (InverseModelEdgeTransition.line_one
    (Primitives.point curve (actual.val.point first)) (Primitives.point curve (actual.val.point parameter))) _).trans
    (InverseModelEdgeTransition.EdgeTransition.sampleAt_flip _ _ _)

/-- Compare the actual terminal circle reading with its retained continued Point on the same original arc.

The supplied neighborhood contains the actual cap coordinate throughout
the interval. Its source query belongs to the original attached owner;
model alignment propagates between the two retained Points. The original
terminal sample bank then supplies an all-request comparison without
identifying the curved arc with an affine integration segment.
-/
def pointEquivalent (interval : Interval.Bounds)
    {first last : Fraction.Rational} (firstInside : interval.Contains first) (lastInside : interval.Contains last)
    {factor : Canonical}
    {prepared : Preparation cap (actual.val.point first)
      (point_inside base unitBound collarBound actual first) factor}
    (initial : Preparation.Attached prepared)
    (finish : Owners.Point cap (Primitives.point curve (actual.val.point last)))
    {count : Nat} (patch : ContinuedNeighborhood cap.polynomial count)
    (patchInside : ∀ time, interval.Contains time →
      patch.box.Contains (Primitives.point curve (actual.val.point time)))
    (firstSample : ContinuedNeighborhood.Point patch (Primitives.point curve (actual.val.point first)))
    (lastSample : ContinuedNeighborhood.Point patch (Primitives.point curve (actual.val.point last)))
    (source : NamedEquivalent
      (ownerRootName initial.1.val.channel.attachment.owner.parameterNonzero initial.1.val.channel.attachment.owner)
      firstSample.certificate.value.name) :
    NamedEquivalent finish.certificate.value.name lastSample.certificate.value.name := by
  have aligned (index : Nat) : RootAligned (overlapRefine cap.model index)
      (Primitives.point curve (actual.val.point last)) lastSample.certificate.value.name := by
    apply RootAligned.throughNeighborhood firstSample lastSample
      (point_inside base unitBound collarBound actual first)
      (point_inside base unitBound collarBound actual last)
      (patchInside first firstInside) (patchInside last lastInside)
    intro entries neighborhood localInside current roots refinement
    exact initial.aligned index neighborhood localInside current (source.trans roots) refinement
  let channel := finish.channel
  let compared := Riemann.Branches.PreparedPolynomialSheetReadings.rootEquivalent
    channel.samples channel.small channel.inside patch (patchInside last lastInside) lastSample
    lastSample.certificate (NamedEquivalent.refl _) aligned
  exact channel.samples_equivalent.symm.trans compared

/-- Adjacent actual retained quarter curves join their supplied original signed endpoint chart caches.

The original Entries.join is the only geometric input. Both preparations
use the same original factor function, including the canonical cap power
or the negative even sheet, so their actual retained coordinates agree.
-/
def adjacentJoin {nonzero : base ≠ 0} (entries : Integral.Entries base nonzero) (index : Fin 3)
    {factors : Canonical → Canonical}
    {firstInside : collar.box.Contains
      (Primitives.point curve ((entries.get index.castSucc).1.val.point 1))}
    {lastInside : collar.box.Contains (Primitives.point curve ((entries.get index.succ).1.val.point 0))}
    {firstPrepared : Preparation cap ((entries.get index.castSucc).1.val.point 1) firstInside
      (factors ((entries.get index.castSucc).1.val.point 1))}
    {lastPrepared : Preparation cap ((entries.get index.succ).1.val.point 0) lastInside
      (factors ((entries.get index.succ).1.val.point 0))}
    (first : Preparation.Attached firstPrepared) (last : Preparation.Attached lastPrepared) :
    RootCoordinates.Overlap.Join first.2.1.overlap last.2.1.overlap :=
  Preparation.Attached.join first last (entries.join index)

/-- The final and initial actual quarter occurrences close their supplied signed cap coordinates.

This consumes Entries.closed for the same retained four-quarter table and
both actual attached endpoint caches. It acquires no root, observation or
new preparation and makes no assertion about independent finite readings.
-/
def closingJoin {nonzero : base ≠ 0} (entries : Integral.Entries base nonzero)
    {factors : Canonical → Canonical}
    {firstInside : collar.box.Contains
      (Primitives.point curve ((entries.get ⟨3, by decide +kernel⟩).1.val.point 1))}
    {lastInside : collar.box.Contains
      (Primitives.point curve ((entries.get ⟨0, by decide +kernel⟩).1.val.point 0))}
    {firstPrepared : Preparation cap ((entries.get ⟨3, by decide +kernel⟩).1.val.point 1) firstInside
      (factors ((entries.get ⟨3, by decide +kernel⟩).1.val.point 1))}
    {lastPrepared : Preparation cap ((entries.get ⟨0, by decide +kernel⟩).1.val.point 0) lastInside
      (factors ((entries.get ⟨0, by decide +kernel⟩).1.val.point 0))}
    (first : Preparation.Attached firstPrepared) (last : Preparation.Attached lastPrepared) :
    RootCoordinates.Overlap.Join first.2.1.overlap last.2.1.overlap :=
  Preparation.Attached.join first last entries.closed

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle

end
