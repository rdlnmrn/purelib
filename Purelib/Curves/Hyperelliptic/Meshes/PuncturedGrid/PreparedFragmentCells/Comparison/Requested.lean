module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Norm.Sum.Basic

/-! # Cached finite primitive payments for the same regular/hole leaf spine

One shared face budget and numerical cache are read at each retained regular
location and actual sheet. Their actual increment list, old request
increment, charge list and computed bound are materialized once. Hole
outcomes keep their same unresolved original payload; no zero is substituted.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation HoleLocation)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {parent : CenteredEdge curve differential}
variable {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
variable {interval : PreparedAxisPartitions.Interval} {target : Rational}
variable {domains : FaceDomainBank frames faces.regulars}
variable {points : List Canonical} {tolerance : Rational}

namespace PrimitiveFragmentCell.RegularComparison

variable {request : LocalRequest parent count target} {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}
variable {sample : ContinuedNeighborhood.Point request.neighborhood fragment.first}

/-- Retain the original shared budget/data and exact finite numerical payment on this same regular leaf.

The old scalar is the existing request polynomial's oriented endpoint
increment. The left values remain an ordered list of cellwise primitive
increments; this cache does not claim their canonical or global attachment.
-/
@[expose] def Requested (compared : RegularComparison domains request fragment location sample)
    (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :=
  Σ budget : {value : CommonMeshes.DomainMeshBudget compared.domain differential points tolerance //
    value = compared.budget budgets},
  Σ data : {value : PrimitiveData.DomainPrimitives compared.domain differential index //
    value = compared.data numerics},
  Σ values : {value : List Canonical // value = compared.split.pieces.map fun piece =>
    data.val.primitives.value piece.column piece.row piece.lastPoint -
      data.val.primitives.value piece.column piece.row piece.firstPoint},
  Σ source : {value : Canonical // value = request.request.model.primitive.value.eval fragment.last -
    request.request.model.primitive.value.eval fragment.first},
  Σ charges : {value : List Rational // value = compared.split.pieces.map fun piece =>
    request.facePieceCharge compared.domain budget.val.bounds piece index},
  {bound : Rational // bound = (compared.split.pieces.length : Rational) * coordinateSum charges.val ∧
    normSq (gaussianSum values.val - source.val) ≤ bound}

namespace Requested

variable {compared : RegularComparison domains request fragment location sample}
variable {budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains}
variable {numerics : PrimitiveData.FacePrimitiveBank differential index domains}

/-- Read the shared original caches once and compute the exact finite lists and certified scalar bound once. -/
def build (compared : RegularComparison domains request fragment location sample)
    (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) : Requested compared budgets numerics := by
  let budget := compared.budget budgets
  let data := compared.data numerics
  let values := compared.split.pieces.map fun piece =>
    data.primitives.value piece.column piece.row piece.lastPoint -
      data.primitives.value piece.column piece.row piece.firstPoint
  let source := request.request.model.primitive.value.eval fragment.last -
    request.request.model.primitive.value.eval fragment.first
  let charges := compared.split.pieces.map fun piece =>
    request.facePieceCharge compared.domain budget.bounds piece index
  let bound := (compared.split.pieces.length : Rational) * coordinateSum charges
  have paid := compared.split_le budgets numerics
  change normSq (gaussianSum values - source) ≤ bound at paid
  exact ⟨⟨budget, rfl⟩, ⟨data, rfl⟩, ⟨values, rfl⟩, ⟨source, rfl⟩, ⟨charges, rfl⟩, ⟨bound, rfl, paid⟩⟩

variable (retained : Requested compared budgets numerics)

/-- Read the complete original shared budget retained on this actual leaf. -/
@[expose] def budget : CommonMeshes.DomainMeshBudget compared.domain differential points tolerance := retained.1.val

/-- Read the complete original numerical cache, including its unchanged primitive constants, anchors and offsets. -/
@[expose] def data : PrimitiveData.DomainPrimitives compared.domain differential index := retained.2.1.val

/-- Read the same ordered list of actual local-cell primitive increments. -/
@[expose] def values : List Canonical := retained.2.2.1.val

/-- Read the same old original-request primitive endpoint increment. -/
@[expose] def source : Canonical := retained.2.2.2.1.val

/-- Read the complete ordered actual analytic-charge list. -/
@[expose] def charges : List Rational := retained.2.2.2.2.1.val

/-- Read the exact retained count-times-charge-sum payment. -/
@[expose] def bound : Rational := retained.2.2.2.2.2.val

/-- The stored budget is the whole original shared cache lookup. -/
theorem budget_eq : retained.budget = compared.budget budgets := retained.1.property

/-- The stored numerical data are the whole original shared cache lookup. -/
theorem data_eq : retained.data = compared.data numerics := retained.2.1.property

/-- The stored values use the same complete retained primitive data and exact ordered analytic pieces. -/
theorem values_eq : retained.values = compared.split.pieces.map fun piece =>
    retained.data.primitives.value piece.column piece.row piece.lastPoint -
      retained.data.primitives.value piece.column piece.row piece.firstPoint := retained.2.2.1.property

/-- The stored old increment uses the original request polynomial and original oriented leaf endpoints. -/
theorem source_eq : retained.source = request.request.model.primitive.value.eval fragment.last -
    request.request.model.primitive.value.eval fragment.first := retained.2.2.2.1.property

/-- The stored charges use the same retained original budget and piece order. -/
theorem charges_eq : retained.charges = compared.split.pieces.map fun piece =>
    request.facePieceCharge compared.domain retained.budget.bounds piece index := retained.2.2.2.2.1.property

/-- The exact retained count and actual charge sum define the stored bound. -/
theorem bound_eq : retained.bound = (compared.split.pieces.length : Rational) * coordinateSum retained.charges :=
  retained.2.2.2.2.2.property.1

/-- The same actual cellwise increment list differs from the same old scalar by the computed finite payment. -/
theorem accurate : normSq (gaussianSum retained.values - retained.source) ≤ retained.bound :=
  retained.2.2.2.2.2.property.2

end Requested

end PrimitiveFragmentCell.RegularComparison

namespace PrimitiveFragmentCells

/-- Every regular leaf retains a complete actual numerical payment; each hole keeps its literal unresolved payload. -/
@[expose] def Evaluation (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains)
    (request : LocalRequest parent count target) :
    {intervals : List PreparedAxisPartitions.Interval} → (located : PrimitiveFragmentCells axes parent partition
      intervals) → (classified : Classifications faces located) → Comparisons domains request located classified → Type
  | _, .nil => fun _ _ => PUnit
  | _, .cons fragment remaining => fun classified =>
      match classified with
      | (.regular _location, tail) => fun compared =>
          PrimitiveFragmentCell.RegularComparison.Requested compared.1.compared budgets numerics ×
            Evaluation budgets numerics request remaining tail compared.2
      | (.hole location, tail) => fun compared =>
          {value : HoleLocation faces.holes fragment.cell // value = location} ×
            Evaluation budgets numerics request remaining tail compared.2
termination_by structural _ located => located

/-- Read each regular comparison once in order, retaining every original hole outcome without a zero payment. -/
def evaluate (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains)
    (request : LocalRequest parent count target) :
    {intervals : List PreparedAxisPartitions.Interval} → (located : PrimitiveFragmentCells axes parent partition
      intervals) → (classified : Classifications faces located) → (compared : Comparisons domains request located
        classified) → Evaluation budgets numerics request located classified compared
  | _, .nil => fun _ _ => PUnit.unit
  | _, .cons _fragment remaining => fun classified =>
      match classified with
      | (.regular _location, tail) => fun compared =>
          let head := PrimitiveFragmentCell.RegularComparison.Requested.build compared.1.compared budgets numerics
          let rest := evaluate budgets numerics request remaining tail compared.2
          ⟨head, rest⟩
      | (.hole _location, tail) => fun compared =>
          let rest := evaluate budgets numerics request remaining tail compared.2
          ⟨compared.1, rest⟩
termination_by structural _ located => located

end PrimitiveFragmentCells

namespace LocatedPrimitiveSplits

/-- The same ordered original parent requests and comparison spine index the full mixed regular/hole payment bank. -/
@[expose] def Evaluation (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → (requests : RequestedParents count target parents) →
    (classified : Classifications faces located) → Comparisons domains located requests classified → Type 2
  | _, _, .nil => fun _ _ _ => PUnit
  | _, _, .cons first remaining => fun requests =>
      match requests with
      | .cons request rest => fun classified compared =>
          PrimitiveFragmentCells.Evaluation budgets numerics request first classified.1 compared.1 ×
            Evaluation budgets numerics remaining rest classified.2 compared.2
termination_by structural _ _ located => located

/-- Materialize finite original-cache payments in the same parent/interval order, retaining unresolved hole cases. -/
def evaluate (budgets : CommonMeshes.FaceMeshBudgets differential points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank differential index domains) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → (requests : RequestedParents count target parents) →
    (classified : Classifications faces located) → (compared : Comparisons domains located requests classified) →
      Evaluation budgets numerics located requests classified compared
  | _, _, .nil => fun _ _ _ => PUnit.unit
  | _, _, .cons first remaining => fun requests =>
      match requests with
      | .cons request rest => fun classified compared =>
          let head := PrimitiveFragmentCells.evaluate budgets numerics request first classified.1 compared.1
          let tail := evaluate budgets numerics remaining rest classified.2 compared.2
          ⟨head, tail⟩
termination_by structural _ _ located => located

end LocatedPrimitiveSplits

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
