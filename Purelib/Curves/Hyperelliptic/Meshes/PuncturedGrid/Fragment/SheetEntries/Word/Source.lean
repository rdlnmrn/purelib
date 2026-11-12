module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.Indexed
import Purelib.Data.List.OfFn.Basic

/-! # Source-fragment comparisons on the same retained original word

Every actual old endpoint cache is compared once. The existing shared-sum
spine is then constructed from those same comparison values, with whole
pair transports only. No Finish, view, source or numerical bank is built.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveFragments.SheetEntries
  renaming BankReadings -> SourceReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
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
variable {budgets : FaceMeshBudgets source points tolerance domains} (shared : FaceSharedMeshes budgets numerics)
variable {intervals : List Interval} {fragments : RegularPrimitiveFragments axes parent partition intervals}
variable (entries : FragmentSheets domains request fragments) (bank : Leaves shared entries)

/-- One completed source-model comparison at each actual retained endpoint cache. -/
abbrev SourceComparisons := DependentVector fun position : Fin intervals.length =>
  EndpointReadings.Compared (leafAt shared entries bank position).occurrence.view

/-- Compare each SAME retained endpoint view once, preserving its old source/model request and numerical cache. -/
def compareSources : SourceComparisons shared entries bank :=
  DependentVector.ofFn fun position =>
    EndpointReadings.compared (leafAt shared entries bank position).occurrence.view

/-- Complete original-pair equality transports one already completed source comparison without evaluating it again. -/
private def castSource {interval : Interval}
    {first last : OccurrencePair (axes := axes) (parent := parent) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (compared : BankReading first.2 shared) : BankReading last.2 shared := by
  cases equal
  exact compared

/-- Whole pair transport preserves the computed source-fragment comparison scalar. -/
private theorem castSource_value {interval : Interval}
    {first last : OccurrencePair (axes := axes) (parent := parent) (partition := partition)
      (domains := domains) (request := request) interval}
    (equal : first = last) (compared : BankReading first.2 shared) :
    (castSource shared equal compared).value = compared.value := by
  cases equal
  rfl

/-- Read one same completed comparison in the original indexed source-reading family. -/
def sourceReading (compared : SourceComparisons shared entries bank) (position : Fin intervals.length) :
    BankReading (entries.at position).2 shared :=
  castSource shared (Leaf.pair_eq (leafAt shared entries bank position)) (compared.get position).comparison

/-- The same completed comparison is the actual old finish-minus-incoming value of that literal retained leaf. -/
theorem sourceReading_value (compared : SourceComparisons shared entries bank) (position : Fin intervals.length) :
    (sourceReading shared entries bank compared position).value =
      (leafAt shared entries bank position).occurrence.terminal -
        (leafAt shared entries bank position).occurrence.initial :=
  (castSource_value shared (Leaf.pair_eq (leafAt shared entries bank position))
    (compared.get position).comparison).trans
    (EndpointReadings.Compared.value_eq (compared.get position))

/-- Actual positive comparisons and the existing reading spine assembled only from those same given values. -/
abbrev SourceCache :=
  Σ compared : {value : SourceComparisons shared entries bank // value = compareSources shared entries bank},
  {value : SourceReadings shared entries //
    value = SourceReadings.ofFn entries (sourceReading shared entries bank compared.val)}

/-- Materialize all actual comparisons once, then index those retained results into the existing source container. -/
def sourceCache : SourceCache shared entries bank :=
  let compared : {value : SourceComparisons shared entries bank // value = compareSources shared entries bank} :=
    ⟨compareSources shared entries bank, rfl⟩
  let readings : {value : SourceReadings shared entries //
      value = SourceReadings.ofFn entries (sourceReading shared entries bank compared.val)} :=
    ⟨SourceReadings.ofFn entries (sourceReading shared entries bank compared.val), rfl⟩
  ⟨compared, readings⟩

namespace SourceCache

variable {shared entries bank} (kept : SourceCache shared entries bank)

/-- Read the same completed comparison bank; its actual per-leaf requests/old caches remain retained. -/
@[expose] def comparisons : SourceComparisons shared entries bank := kept.1.val

/-- Read the existing original source-reading spine containing those same actual comparison values. -/
@[expose] def readings : SourceReadings shared entries := kept.2.val

/-- The complete comparison bank is its one original materialization on the given endpoint caches. -/
theorem comparisons_eq : kept.comparisons = compareSources shared entries bank := kept.1.property

/-- The source-reading spine is its exact given-comparison constructor, not another comparison build. -/
theorem readings_eq : kept.readings = SourceReadings.ofFn entries
    (sourceReading shared entries bank kept.comparisons) := kept.2.property

/-- The original source-reading scalar list is the SAME retained leaf increment list, with exact occurrence order. -/
theorem values_eq : kept.readings.values = List.ofFn (fun position : Fin intervals.length =>
    (leafAt shared entries bank position).occurrence.terminal -
      (leafAt shared entries bank position).occurrence.initial) :=
  (congrArg (fun value : SourceReadings shared entries => value.values) kept.readings_eq).trans
    ((SourceReadings.values_ofFn entries (sourceReading shared entries bank kept.comparisons)).trans
      (Data.List.OfFn.Basic.ofFn_congr fun position =>
        sourceReading_value shared entries bank kept.comparisons position))

end SourceCache

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.FragmentSheets
