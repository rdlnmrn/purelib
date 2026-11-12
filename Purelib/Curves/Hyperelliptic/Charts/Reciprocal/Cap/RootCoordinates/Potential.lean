module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
public import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Normalization.InverseModelRootAgreement

/-! # The actual regular-root potential at one retained ramified coordinate

The original prepared coordinate supplies its own apart denominator. Its
ordinary quotient r/t retains that same preparation and original numerator.
A joined cap endpoint compares both actual roots and quotient presentations;
coordinate equality by itself is never used to identify the potential.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Difference
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The original cached ordinary quotient retains this exact cap coordinate preparation. -/
@[expose] def Potential {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) : Type _ :=
  { cached : Prepared.Quotient overlap.regularRoot.value overlap.coordinate.quotient //
    cached.prepared = overlap.coordinate.prepared }

/-- Construct r/t by ordinary division through the same original prepared coordinate, without new preparation. -/
def potential {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) : Potential overlap :=
  let cached := Prepared.Quotient.quotient overlap.regularRoot.value overlap.coordinate.prepared
  ⟨cached, rfl⟩

/-- The potential retains the complete original once-supplied quotient and denominator preparation. -/
private theorem packaged_potential_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) :
    overlap.potential =
      (let cached := Prepared.Quotient.quotient overlap.regularRoot.value overlap.coordinate.prepared
       ⟨cached, rfl⟩ : Potential overlap) := by rfl

/-- The potential retains the complete original once-supplied quotient and denominator preparation. -/
theorem potential_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) :
    overlap.potential =
      (let cached := Prepared.Quotient.quotient overlap.regularRoot.value overlap.coordinate.prepared
       ⟨cached, rfl⟩ : Potential overlap) := packaged_potential_factory overlap

/-- Multiplication by the same actual prepared t cancels the retained endpoint quotient. -/
def Potential.cancel {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : Overlap cap point owner} (retained : Potential overlap) :
    NamedEquivalent (mul retained.val.output overlap.coordinate.prepared.denominator).name
      overlap.regularRoot.value.name := by
  have output : retained.val.output =
      overlap.coordinate.prepared.quotient overlap.regularRoot.value :=
    retained.val.output_eq.trans
      (congrArg (fun prepared : Prepared overlap.coordinate.quotient =>
        prepared.quotient overlap.regularRoot.value) retained.property)
  exact NamedEquivalent.transport
    (congrArg (fun value : CoherentNamed => (mul value overlap.coordinate.prepared.denominator).name) output.symm)
    rfl (Cancellation.coherentDiv_mul_cancel overlap.regularRoot.value
      overlap.coordinate.prepared.denominator overlap.coordinate.prepared.apart)

/-- The actual potential r/t is the full regular polynomial divided by the same original reciprocal root.

The coefficient P(w) comes from the original regular-root square. The
original reconstruction t*r=v and the cached quotient cancellation derive
the comparison internally. No reciprocal owner or source point is replaced.
-/
def Potential.reciprocal {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : Overlap cap point owner} (retained : Potential overlap) :
    NamedEquivalent retained.val.output.name
      (div (Coherence.exact (cap.polynomial.eval point)) overlap.reciprocal.value overlap.reciprocal.apart).name := by
  let t := overlap.coordinate.prepared.denominator
  let r := overlap.regularRoot.value
  let v := overlap.reciprocal.value
  let candidate := div (Coherence.exact (cap.polynomial.eval point)) v overlap.reciprocal.apart
  have actual : NamedEquivalent (mul v retained.val.output).name
      (Coherence.exact (cap.polynomial.eval point)).name :=
    (Congruence.coherentMul_respects v (mul t r) retained.val.output retained.val.output
      overlap.coordinate.reconstruct.symm (NamedEquivalent.refl _)).trans
      ((Laws.coherentMul_assoc t r retained.val.output).trans
        ((Laws.coherentMul_left_comm t r retained.val.output).trans
          ((Congruence.coherentMul_respects r r (mul t retained.val.output) r
            (NamedEquivalent.refl _)
            ((Laws.coherentMul_comm t retained.val.output).trans retained.cancel)).trans
            overlap.regularRoot.square)))
  have divided : NamedEquivalent (mul v candidate).name (Coherence.exact (cap.polynomial.eval point)).name :=
    (Laws.coherentMul_comm v candidate).trans
      (Cancellation.coherentDiv_mul_cancel (Coherence.exact (cap.polynomial.eval point)) v
        overlap.reciprocal.apart)
  exact Cancellation.coherentMul_cancel_left v retained.val.output candidate overlap.reciprocal.apart
    (actual.trans divided.symm)

/-- A genuine cap-coordinate join compares both cached endpoint potentials at their original root owners. -/
def Join.potential {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {firstPoint lastPoint : ReciprocalRootNames.Gaussian}
    {firstOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : Overlap cap firstPoint firstOwner} {last : Overlap cap lastPoint lastOwner}
    (join : Join first last) (left : Potential first) (right : Potential last) :
    NamedEquivalent left.val.output.name right.val.output.name := by
  have regular : NamedEquivalent first.regularRoot.value.name last.regularRoot.value.name := by
    have points := join.point_eq
    cases points
    rewrite [first.regularRoot_eq, last.regularRoot_eq]
    exact InverseModelRootAgreement.equivalent_of_value first.regular.channel last.regular.channel rfl
  have coordinates : NamedEquivalent first.coordinate.quotient.name last.coordinate.quotient.name :=
    first.coordinate.prepared.equivalent.trans
      (join.equivalent.trans last.coordinate.prepared.equivalent.symm)
  exact left.val.respects right.val coordinates regular

/-- The oriented discrepancy of two actually joined cached potential endpoints is operationally zero. -/
def Join.potential_difference {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {firstPoint lastPoint : ReciprocalRootNames.Gaussian}
    {firstOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : Overlap cap firstPoint firstOwner} {last : Overlap cap lastPoint lastOwner}
    (join : Join first last) (left : Potential first) (right : Potential last) :
    NamedEquivalent (difference left.val.output right.val.output).name (Coherence.exact 0).name :=
  difference_zero_of_equivalent left.val.output right.val.output (join.potential left right).symm

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

end
