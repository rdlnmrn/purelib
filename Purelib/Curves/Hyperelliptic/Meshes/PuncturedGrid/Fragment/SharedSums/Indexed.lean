module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Data.List.OfFn.Basic

/-! # Original shared-sum spines from already cached indexed comparisons

Only original constructor data and exact at readbacks are used. The
supplied comparison at each literal index is consumed once. No source,
primitive, observation, endpoint or comparison producer is invoked.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings (BankReading)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target} {points : List Canonical}
variable {partition : AxisPartition 0 1 (axes.parameters parent)}
variable {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
variable {budgets : FaceMeshBudgets source points tolerance domains} {shared : FaceSharedMeshes budgets numerics}

namespace BankReadings

/-- Whole original fragment/Entry equality reindexes the same already completed comparison. -/
private def castPair {interval : Interval}
    {first last : Σ fragment : RegularPrimitiveFragment axes parent partition interval,
      SheetEntry fragment domains request}
    (equal : first = last) (reading : BankReading first.2 shared) : BankReading last.2 shared := by
  cases equal
  exact reading

/-- Whole pair transport changes no computed scalar comparison value. -/
private theorem castPair_value {interval : Interval}
    {first last : Σ fragment : RegularPrimitiveFragment axes parent partition interval,
      SheetEntry fragment domains request}
    (equal : first = last) (reading : BankReading first.2 shared) :
    (castPair equal reading).value = reading.value := by
  cases equal
  rfl

/-- Construct the original reading spine from the actual given comparisons at its original bounded positions. -/
def ofFn : ∀ {intervals : List Interval} {fragments : RegularPrimitiveFragments axes parent partition intervals}
    (entries : Fragment.FragmentSheets domains request fragments),
    ((position : Fin intervals.length) → BankReading (entries.at position).2 shared) → BankReadings shared entries
  | _, _, .nil, _read => .nil
  | _, _, .cons first remaining, read =>
      .cons (castPair (Fragment.FragmentSheets.at_zero first remaining) (read 0))
        (ofFn remaining fun position =>
          castPair (Fragment.FragmentSheets.at_succ first remaining position) (read position.succ))

/-- The supplied indexed comparisons retain their actual scalar list in the original order. -/
theorem values_ofFn : ∀ {intervals : List Interval}
    {fragments : RegularPrimitiveFragments axes parent partition intervals}
    (entries : Fragment.FragmentSheets domains request fragments)
    (read : (position : Fin intervals.length) → BankReading (entries.at position).2 shared),
    (ofFn entries read).values = List.ofFn (fun position => (read position).value)
  | _, _, .nil, _read => rfl
  | _, _, .cons first remaining, read => by
      let following := fun position =>
        castPair (Fragment.FragmentSheets.at_succ first remaining position) (read position.succ)
      have firstValue := castPair_value (Fragment.FragmentSheets.at_zero first remaining) (read 0)
      have tailValues := values_ofFn remaining following
      have tailEq : List.ofFn (fun position => (following position).value) =
          List.ofFn (fun position => (read position.succ).value) :=
        Data.List.OfFn.Basic.ofFn_congr fun position =>
          castPair_value (Fragment.FragmentSheets.at_succ first remaining position) (read position.succ)
      have whole : List.ofFn (fun position => (read position).value) =
          (read 0).value :: List.ofFn (fun position => (read position.succ).value) :=
        Data.List.OfFn.Basic.ofFn_succ
      exact (congrArg₂ List.cons firstValue (tailValues.trans tailEq)).trans whole.symm

end BankReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries
