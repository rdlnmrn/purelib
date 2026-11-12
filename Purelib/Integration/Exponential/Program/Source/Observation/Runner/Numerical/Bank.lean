module

public import Purelib.Integration.Exponential.Program.Source.Observation.Runner.Model
public import Purelib.Integration.Exponential.Program.Source.Observation.Numerical.Points

/-! Retained mixed points with their exact original finite-source receipt. -/

public section

namespace Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Bank

open Purelib.Approximation
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Program.Source.Observation.Numerical

/-- A retained exact numerical point together with its original selected stage receipt. -/
abbrev ExactPoint {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    (retained : Program.Retained policy schedule extraDepth) :=
  Σ receipt : Model.Receipt retained, NumericalPoint (Points.finiteProcess receipt.selection.depth)

/-- Select cached exact points only from the same original receipt owner, preserving their order. -/
@[expose] def forReceipt {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} (receipt : Model.Receipt retained) :
    List (ExactPoint retained) → List (NumericalPoint (Points.finiteProcess receipt.selection.depth))
  | [] => []
  | ⟨owner, point⟩ :: rest =>
      if same : owner.index = receipt.index then
        let ownerEq := Model.Receipt.eq_of_index owner receipt same
        (ownerEq ▸ point) :: forReceipt receipt rest
      else forReceipt receipt rest

/-- Retain returned points only when the existing same-owner bank lacks a sufficient point at that tag.

The current request controls adequacy. Every accepted point is included in
the search bank for later candidates, and the returned additions preserve
their original occurrence order. -/
@[expose] def useful {source : Fraction.Rational → BoundProcess} (request : AccuracyRequest) :
    List (NumericalPoint source) → List (NumericalPoint source) → List (NumericalPoint source)
  | _, [] => []
  | bank, point :: rest =>
      match NumericalPoint.findSufficient bank point.point request with
      | some _ => useful request bank rest
      | none => point :: useful request (point :: bank) rest

/-- Extend a numerical owner's bank without replacing or reordering its original tail. -/
@[expose] def extend {source : Fraction.Rational → BoundProcess} (request : AccuracyRequest)
    (bank points : List (NumericalPoint source)) : List (NumericalPoint source) :=
  useful request bank points ++ bank

/-- Extend a receipt-indexed exact bank while retaining unmatched original stage owners. -/
@[expose] def extendExact {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} (receipt : Model.Receipt retained)
    (request : AccuracyRequest) (bank : List (ExactPoint retained))
    (points : List (NumericalPoint (Points.finiteProcess receipt.selection.depth))) : List (ExactPoint retained) :=
  (useful request (forReceipt receipt bank) points).map (fun point => ⟨receipt, point⟩) ++ bank

/-- Extension preserves the caller's complete original numerical bank as its exact tail. -/
theorem extend_retained {source : Fraction.Rational → BoundProcess} (request : AccuracyRequest)
    (bank points : List (NumericalPoint source)) : ∃ added, extend request bank points = added ++ bank :=
  ⟨useful request bank points, rfl⟩

/-- Exact-bank extension preserves every prior receipt owner in the original tail. -/
theorem extendExact_retained {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth : Nat}
    {retained : Program.Retained policy schedule extraDepth} (receipt : Model.Receipt retained)
    (request : AccuracyRequest) (bank : List (ExactPoint retained))
    (points : List (NumericalPoint (Points.finiteProcess receipt.selection.depth))) :
    ∃ added, extendExact receipt request bank points = added ++ bank :=
  ⟨(useful request (forReceipt receipt bank) points).map (fun point => ⟨receipt, point⟩), rfl⟩

end Purelib.Integration.Exponential.Program.Source.Observation.Runner.Numerical.Bank

end
