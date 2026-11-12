module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

/-! # Original source-fragment comparisons on retained endpoint caches

The comparison consumes the SAME old numerical slice, budget, shared values
and source request. Whole equality transport happens after its actual
result exists; it changes no primitive, observation, stage or scalar.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.EndpointReadings

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
  (DomainMeshBudget DomainMeshReadings FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Polynomial.Rectangle.Accuracy
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational}
variable {request : Riemann.Readings.UniformPreparedRequests.LocalRequest parent count target}
variable {points : List Canonical} {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable (assigned : SheetEntry fragment domains request)
variable {numerics : FacePrimitiveBank source index domains} {budgets : FaceMeshBudgets source points tolerance domains}
variable (shared : FaceSharedMeshes budgets numerics)

/-- The exact existing comparison family on the supplied old data, budget and actual shared-value cache. -/
@[expose] def ComparisonOn (data : DomainPrimitives assigned.domain source index)
    (budget : DomainMeshBudget assigned.domain source points tolerance) (values : DomainMeshReadings budget data) :=
  SharedComparison (assigned := assigned) (bounds := budget.bounds)
    (accuracy := FragmentIndex.GridPrimitiveAccuracy.atIndex budget.accuracy index values.later)
    (primitives := data.primitives) (anchors := data.anchors) (offsets := data.offsets) (mesh := budget.mesh)
    values.readings

/-- Cast the already completed comparison through whole cached owner equalities, never before its construction. -/
private def originalOn {data : DomainPrimitives assigned.domain source index}
    {budget : DomainMeshBudget assigned.domain source points tolerance} {values : DomainMeshReadings budget data}
    (dataEq : data = SharedComparison.sharedPrimitives assigned numerics)
    (budgetEq : budget = BankReadings.meshBudget assigned budgets)
    (valuesEq : HEq values (BankReadings.meshReadings assigned shared))
    (compared : ComparisonOn assigned data budget values) : BankReadings.BankReading assigned shared := by
  cases dataEq
  cases budgetEq
  have same : values = BankReadings.meshReadings assigned shared := eq_of_heq valuesEq
  cases same
  exact compared

/-- The complete existing comparison value survives whole owner-index transport. -/
private theorem originalOn_heq {data : DomainPrimitives assigned.domain source index}
    {budget : DomainMeshBudget assigned.domain source points tolerance} {values : DomainMeshReadings budget data}
    (dataEq : data = SharedComparison.sharedPrimitives assigned numerics)
    (budgetEq : budget = BankReadings.meshBudget assigned budgets)
    (valuesEq : HEq values (BankReadings.meshReadings assigned shared))
    (compared : ComparisonOn assigned data budget values) :
    HEq (originalOn assigned shared dataEq budgetEq valuesEq compared) compared := by
  cases dataEq
  cases budgetEq
  have same : values = BankReadings.meshReadings assigned shared := eq_of_heq valuesEq
  cases same
  rfl

/-- Whole owner-index transport preserves the actual cached scalar of the original comparison. -/
private theorem originalOn_value {data : DomainPrimitives assigned.domain source index}
    {budget : DomainMeshBudget assigned.domain source points tolerance} {values : DomainMeshReadings budget data}
    (dataEq : data = SharedComparison.sharedPrimitives assigned numerics)
    (budgetEq : budget = BankReadings.meshBudget assigned budgets)
    (valuesEq : HEq values (BankReadings.meshReadings assigned shared))
    (compared : ComparisonOn assigned data budget values) :
    (originalOn assigned shared dataEq budgetEq valuesEq compared).value = compared.value := by
  cases dataEq
  cases budgetEq
  have same : values = BankReadings.meshReadings assigned shared := eq_of_heq valuesEq
  cases same
  rfl

variable {assigned shared} {included : ∀ value ∈ assigned.split.points, value ∈ points}
variable (cached : Cache assigned shared included)

/-- The original source-fragment comparison at the SAME retained endpoint-cache inputs. -/
@[expose] def Comparison := ComparisonOn assigned (data cached) (budget cached) (meshValues cached)

/-- Compute one original source comparison and its analytic/count charge from the same old cached inputs. -/
def compare : Comparison cached :=
  SharedComparison.build (assigned := assigned) (bounds := (budget cached).bounds)
    (accuracy := FragmentIndex.GridPrimitiveAccuracy.atIndex (budget cached).accuracy index (meshValues cached).later)
    (primitives := (data cached).primitives) (anchors := (data cached).anchors) (offsets := (data cached).offsets)
    (mesh := (budget cached).mesh) (meshValues cached).readings included

/-- Spell an already completed comparison in the original shared-sum container's exact owner family. -/
def toOriginal (compared : Comparison cached) : BankReadings.BankReading assigned shared :=
  originalOn assigned shared (data_eq cached) (budget_eq cached) (meshValues_heq cached) compared

/-- The complete actual comparison, including its old source model and charge, is unchanged by the spelling. -/
theorem toOriginal_heq (compared : Comparison cached) : HEq (toOriginal cached compared) compared :=
  originalOn_heq assigned shared (data_eq cached) (budget_eq cached) (meshValues_heq cached) compared

/-- The actual original source request and endpoint cache accompany one comparison and its whole transport. -/
abbrev Compared :=
  {value : Riemann.Readings.UniformPreparedRequests.LocalRequest parent count target ×
      SheetEntry fragment domains request × Cache assigned shared included // value = (request, assigned, cached)} ×
  (Σ actual : {value : Comparison cached // value = compare cached},
    {value : BankReadings.BankReading assigned shared // value = toOriginal cached actual.val})

/-- Compare once before transporting the complete actual result; no old bank, Finish or view is prepared again. -/
def compared : Compared cached :=
  let actual : {value : Comparison cached // value = compare cached} := ⟨compare cached, rfl⟩
  let original : {value : BankReadings.BankReading assigned shared // value = toOriginal cached actual.val} :=
    ⟨toOriginal cached actual.val, rfl⟩
  ⟨⟨(request, assigned, cached), rfl⟩, actual, original⟩

namespace Compared

variable {cached} (kept : Compared cached)

/-- Read the same actual comparison built on the stored data/budget/shared values. -/
@[expose] def actual : Comparison cached := kept.2.1.val

/-- Read the same completed object in the original container's exact family. -/
@[expose] def comparison : BankReadings.BankReading assigned shared := kept.2.2.val

/-- The original source/model request and complete endpoint cache remain their actual input values. -/
theorem originals_eq : kept.1.val = (request, assigned, cached) := kept.1.property

/-- The actual comparison is its one original shared-comparison operation on these cached inputs. -/
theorem actual_eq : kept.actual = compare cached := kept.2.1.property

/-- The original-family result is the whole transport of the same already built actual comparison. -/
theorem comparison_eq : kept.comparison = toOriginal cached kept.actual := kept.2.2.property

/-- The entire old comparison survives, including both source/target owner indices and its computed bound. -/
theorem comparison_heq : HEq kept.comparison kept.actual :=
  (heq_of_eq kept.comparison_eq).trans (toOriginal_heq cached kept.actual)

/-- The comparison value is exactly the two literal endpoint-cache readings, with their same old constants. -/
theorem value_eq : kept.comparison.value = (reading cached).values 1 - (reading cached).values 0 :=
  (congrArg (fun value : BankReadings.BankReading assigned shared => value.value) kept.comparison_eq).trans
    ((originalOn_value assigned shared (data_eq cached) (budget_eq cached) (meshValues_heq cached) kept.actual).trans
      (kept.actual.value_eq.trans
        (congrArg₂ (fun last first : Canonical => last - first)
          (value_eq_atPoint cached 1).symm (value_eq_atPoint cached 0).symm)))

end Compared

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.EndpointReadings
