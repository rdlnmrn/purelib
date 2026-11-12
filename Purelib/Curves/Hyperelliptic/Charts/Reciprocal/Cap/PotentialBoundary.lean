module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Potential
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Differentials.Basic

/-! # Oriented potential endpoint cancellation on the actual closed cap bank

One original quotient potential is retained for each actual endpoint
occurrence. Adjacent coordinate joins and the original whole-bank root
return compare those same caches. Their oriented discrepancies are
operationally zero, not asserted equal at arbitrary finite reading stages.
No second bank, path preparation or root acquisition is executed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Difference (difference)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

namespace PathCover.Bank

/-- Retain both actual endpoint quotient caches for each parent occurrence, in the original bank order. -/
@[expose] def Potentials {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → Bank cap differential count parents → Type 3
  | [], .nil => PUnit
  | _ :: _, .cons data rest =>
      data.data.first.coordinates.Potential × data.data.last.coordinates.Potential × Potentials rest

/-- Build each endpoint potential once from its retained original coordinate preparation. -/
def potentials {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) → Potentials bank
  | [], .nil => ⟨⟩
  | _ :: _, .cons data rest =>
      ⟨data.data.first.coordinates.potential, data.data.last.coordinates.potential, potentials rest⟩

/-- Each actual retained adjacent endpoint connector has an operationally zero oriented potential discrepancy. -/
@[expose] def JunctionZeros {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      Potentials bank → Type 3
  | [], .nil, _ => PUnit
  | [_], .cons _ .nil, _ => PUnit
  | _ :: _ :: _, .cons _ (.cons next rest), values =>
      NamedEquivalent (difference values.2.1.val.output values.2.2.1.val.output).name (Coherence.exact 0).name ×
        JunctionZeros (.cons next rest) values.2.2

/-- Consume the original cached adjacent joins on the same endpoint potential caches. -/
def potentialJunctions {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → CoordinateLinks bank → JunctionZeros bank values
  | [], .nil, _, _ => ⟨⟩
  | [_], .cons _ .nil, _, _ => ⟨⟩
  | _ :: _ :: _, .cons _ (.cons next rest), values, links =>
      ⟨links.head.potential_difference values.2.1 values.2.2.1,
        potentialJunctions (.cons next rest) values.2.2 links.tail⟩

/-- The final actual quotient potential has zero oriented discrepancy from a retained target occurrence. -/
@[expose] def LastPotentialZero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point owner} (left : target.Potential) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      Potentials bank → Type
  | [], .nil, _ => PUnit
  | [_], .cons _ .nil, values =>
      NamedEquivalent (difference left.val.output values.2.1.val.output).name (Coherence.exact 0).name
  | _ :: _ :: _, .cons _ (.cons next rest), values =>
      LastPotentialZero left (.cons next rest) values.2.2

/-- Consume the actual final-coordinate join without reconstructing any endpoint or potential cache. -/
def lastPotentialZero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat}
    {point : ReciprocalRootNames.Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {target : Overlap cap point owner} (left : target.Potential) :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → LastJoin target bank → LastPotentialZero left bank values
  | [], .nil, _, _ => ⟨⟩
  | [_], .cons _ .nil, values, joined => joined.symm.potential_difference left values.2.1
  | _ :: _ :: _, .cons _ (.cons next rest), values, joined =>
      lastPotentialZero left (.cons next rest) values.2.2 joined

/-- Closing potential discrepancy uses the first and final caches of this exact original nonempty bank. -/
@[expose] def ClosingPotentialZero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      Potentials bank → Type
  | [], .nil, _ => PUnit
  | _ :: _, .cons data rest, values => LastPotentialZero values.1 (.cons data rest) values

/-- The original whole-bank closing coordinate join gives its actual oriented potential cancellation. -/
def closingPotentialZero {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : Differential genus} {count : Nat} :
    {parents : List (Parent curve differential)} → (bank : Bank cap differential count parents) →
      (values : Potentials bank) → ClosingJoin bank → ClosingPotentialZero bank values
  | [], .nil, _, _ => ⟨⟩
  | _ :: _, .cons data rest, values, joined => lastPotentialZero values.1 (.cons data rest) values joined

end PathCover.Bank

namespace Boundary

/-- Derive adjacent and closing potential cancellation from this same actual closed boundary and its cached joins. -/
def potentialCancellation {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}
    (data : Data cap owner differential) (values : PathCover.Bank.Potentials data.covered.bank) :
    PathCover.Bank.JunctionZeros data.covered.bank values ×
      PathCover.Bank.ClosingPotentialZero data.covered.bank values :=
  ⟨PathCover.Bank.potentialJunctions data.covered.bank values data.covered.coordinates,
    PathCover.Bank.closingPotentialZero data.covered.bank values (closingCoordinates data)⟩

/-- Retain one ordered endpoint potential bank and derive cancellation from its actual whole root return.

This consumes the already retained boundary and every original repeated
parent occurrence. The returned equivalences certify endpoint discrepancies;
they do not identify independent finite readings or supply a physical
primitive-integration estimate.
-/
def closedPotentials {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}
    (data : Data cap owner differential) :
    (values : PathCover.Bank.Potentials data.covered.bank) ×
    PathCover.Bank.JunctionZeros data.covered.bank values ×
      PathCover.Bank.ClosingPotentialZero data.covered.bank values :=
  let values := PathCover.Bank.potentials data.covered.bank
  let cancellation := potentialCancellation data values
  ⟨values, cancellation⟩

/-- The complete closed boundary factory builds one ordered potential bank and consumes those same caches. -/
private theorem packaged_closedPotentials_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}
    (data : Data cap owner differential) :
    closedPotentials data =
  (
    let values := PathCover.Bank.potentials data.covered.bank
      let cancellation := potentialCancellation data values
      ⟨values, cancellation⟩
    : (values : PathCover.Bank.Potentials data.covered.bank) ×
    PathCover.Bank.JunctionZeros data.covered.bank values ×
      PathCover.Bank.ClosingPotentialZero data.covered.bank values) := by rfl

/-- The complete closed boundary factory builds one ordered potential bank and consumes those same caches. -/
theorem closedPotentials_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
    {differential : Differential genus}
    (data : Data cap owner differential) :
    closedPotentials data =
  (
    let values := PathCover.Bank.potentials data.covered.bank
      let cancellation := potentialCancellation data values
      ⟨values, cancellation⟩
    : (values : PathCover.Bank.Potentials data.covered.bank) ×
    PathCover.Bank.JunctionZeros data.covered.bank values ×
      PathCover.Bank.ClosingPotentialZero data.covered.bank values) :=
  packaged_closedPotentials_factory data

end Boundary

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

end
