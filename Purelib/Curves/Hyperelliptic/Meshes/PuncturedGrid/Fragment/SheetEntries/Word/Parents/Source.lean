module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Source
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

/-! # Actual source-model attachment to the retained closed gap word

The old request models and endpoint banks remain the originals. One
source-fragment comparison per stored leaf feeds the existing shared-sum
container. Its actual allowance bounds the original request increments
against the SAME ordered rooted gap sum, without normalizing any gap.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  renaming BankReadings -> ParentReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {target tolerance : Rational} {points : List Canonical}
variable {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
variable {budgets : FaceMeshBudgets source points tolerance domains} (shared : FaceSharedMeshes budgets numerics)

/-- The actual source comparisons on the SAME stored endpoint products of every original parent. -/
@[expose] def SourceBlocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests), Blocks shared entries → Type 3
  | _, _, _, _, .nil, _bank => PUnit.{4}
  | _, _, _, _, .cons first remaining, bank =>
      FragmentSheets.SourceCache shared first bank.1.word.leaves × SourceBlocks remaining bank.2

/-- Compare each given endpoint cache once, with no Finish, endpoint-view or source/numerical preparation replay. -/
def buildSourceBlocks : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries), SourceBlocks shared entries bank
  | _, _, _, _, .nil, _bank => PUnit.unit
  | _, _, _, _, .cons first remaining, bank =>
      let compared := FragmentSheets.sourceCache shared first bank.1.word.leaves
      let following := buildSourceBlocks remaining bank.2
      (compared, following)

/-- Assemble the existing whole source-reading spine from those same already completed comparisons. -/
def sourceReadings : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries),
    SourceBlocks shared entries bank → ParentReadings shared entries
  | _, _, _, _, .nil, _bank, _compared => .nil
  | _, _, _, _, .cons _first remaining, bank, compared =>
      .cons compared.1.readings (sourceReadings remaining bank.2 compared.2)

/-- The existing whole reading spine retains the SAME ordered old endpoint increments from the given block bank. -/
theorem sourceReadings_values : ∀ {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits} {requests : RequestedParents count target parents}
    (entries : SplitSheets domains fragments requests) (bank : Blocks shared entries)
    (compared : SourceBlocks shared entries bank),
    (sourceReadings shared entries bank compared).values = SplitSheets.increments shared entries bank
  | _, _, _, _, .nil, _bank, _compared => rfl
  | _, _, _, _, .cons _first remaining, bank, compared =>
      congrArg₂ List.append compared.1.values_eq (sourceReadings_values remaining bank.2 compared.2)

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (requests : RequestedParents count target parents)
variable (entries : SplitSheets domains fragments requests) {point : LiftedPoint 2} {root : Named}
variable (geometry : CenteredPathChain parents (start := point) (finish := point)) (roots : RootChain parents root root)
variable {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
variable (closed : Closed shared entries geometry roots included)

/-- Actual old request/model data, given rooted word, per-leaf comparisons and original shared-sum result.

The source request spine is retained as DATA with the given closed word.
Both old model indices and the old endpoint caches remain unchanged. The
shared sum is packaged from the completed comparisons, never rebuilt.
-/
abbrev SourceAttachment :=
  {value : RequestedParents count target parents × Closed shared entries geometry roots included //
    value = (requests, closed)} ×
  (Σ compared : {value : SourceBlocks shared entries (Closed.blocks shared entries geometry roots closed) //
      value = buildSourceBlocks shared entries (Closed.blocks shared entries geometry roots closed)},
  Σ readings : {value : ParentReadings shared entries //
      value = sourceReadings shared entries (Closed.blocks shared entries geometry roots closed) compared.val},
  {value : SharedSum shared entries // value = SharedSum.ofReadings readings.val})

/-- Compare once on the given rooted caches, then compose only those SAME results through the old scalar folds. -/
def attachSource : SourceAttachment shared requests entries geometry roots closed :=
  let bank := Closed.blocks shared entries geometry roots closed
  let compared : {value : SourceBlocks shared entries bank // value = buildSourceBlocks shared entries bank} :=
    ⟨buildSourceBlocks shared entries bank, rfl⟩
  let readings : {value : ParentReadings shared entries //
      value = sourceReadings shared entries bank compared.val} :=
    ⟨sourceReadings shared entries bank compared.val, rfl⟩
  let sum : {value : SharedSum shared entries // value = SharedSum.ofReadings readings.val} :=
    ⟨SharedSum.ofReadings readings.val, rfl⟩
  ⟨⟨(requests, closed), rfl⟩, compared, readings, sum⟩

namespace SourceAttachment

variable {shared requests entries geometry roots closed}
variable (kept : SourceAttachment shared requests entries geometry roots closed)

/-- Read the original complete request/model spine as retained data, rather than recovering it from a type index. -/
@[expose] def sourceRequests : RequestedParents count target parents := kept.1.val.1

/-- Read the SAME given complete rooted word with all original endpoint and closing caches. -/
@[expose] def closedWord : Closed shared entries geometry roots included := kept.1.val.2

/-- The stored model/request spine is exactly the supplied original input. -/
theorem sourceRequests_eq : kept.sourceRequests = requests := congrArg Prod.fst kept.1.property

/-- The stored rooted word is exactly the given value, never another word construction. -/
theorem closedWord_eq : kept.closedWord = closed := congrArg Prod.snd kept.1.property

/-- Read the completed per-leaf original source comparison bank. -/
@[expose] def comparisons : SourceBlocks shared entries (Closed.blocks shared entries geometry roots closed) :=
  kept.2.1.val

/-- Read the old source-reading container built from those same actual cached comparison values. -/
@[expose] def readings : ParentReadings shared entries := kept.2.2.1.val

/-- Read the same completed original shared sum and its full original computed allowance. -/
@[expose] def sum : SharedSum shared entries := kept.2.2.2.val

/-- The original complete request/model spine and given rooted word remain their actual input values. -/
theorem originals_eq : kept.1.val = (requests, closed) := kept.1.property

/-- The entire comparison bank is its single original constructor on those same endpoint caches. -/
theorem comparisons_eq : kept.comparisons =
    buildSourceBlocks shared entries (Closed.blocks shared entries geometry roots closed) := kept.2.1.property

/-- The old reading container is assembled from the SAME retained comparisons. -/
theorem readings_eq : kept.readings =
    sourceReadings shared entries (Closed.blocks shared entries geometry roots closed) kept.comparisons :=
  kept.2.2.1.property

/-- The complete original shared sum is its given-reading constructor, with no comparison evaluation. -/
theorem sum_eq : kept.sum = SharedSum.ofReadings kept.readings := kept.2.2.2.property

/-- The original shared sum retains the SAME literal increment list as the given rooted word. -/
theorem values_eq : kept.sum.values = Closed.increments shared entries geometry roots closed := by
  have sameReadings : kept.sum.readings = kept.readings :=
    (congrArg (fun value : SharedSum shared entries => value.readings) kept.sum_eq).trans
      (SharedSum.ofReadings_readings kept.readings)
  exact kept.sum.values_eq.trans
    ((congrArg (fun value : ParentReadings shared entries => value.values) sameReadings).trans
      ((congrArg (fun value : ParentReadings shared entries => value.values) kept.readings_eq).trans
        ((sourceReadings_values shared entries (Closed.blocks shared entries geometry roots closed)
          kept.comparisons).trans (Closed.increments_blocks shared entries geometry roots closed))))

/-- The actual original shared sum is exactly the ordered actual outgoing-gap sum, retaining its literal return. -/
theorem value_eq_gaps : kept.sum.value = gaussianSum (Closed.gaps shared entries geometry roots closed) :=
  kept.sum.value_eq.trans ((congrArg gaussianSum kept.values_eq).trans
    (Closed.telescope shared entries geometry roots closed))

/-- The original count constant equals the literal same retained fragment occurrence count. -/
theorem count_eq : kept.sum.fragmentCount = fragmentCount entries := by
  have actual : kept.sum.values.length = fragmentCount entries :=
    (congrArg List.length kept.values_eq).trans (Closed.increments_length shared entries geometry roots closed)
  have original : kept.sum.values.length = kept.sum.fragmentCount :=
    (congrArg List.length kept.sum.values_eq).trans
      ((ParentReadings.values_length kept.sum.readings).trans kept.sum.fragmentCount_eq.symm)
  exact original.symm.trans actual

/-- The allowance retains the exact original local analytic/count charges and actual outer occurrence constant. -/
theorem bound_eq : kept.sum.bound =
    Approximation.Rational.Budget.Aggregate.countCoordinate (fragmentCount entries) * kept.sum.chargeSum :=
  kept.sum.bound_eq.trans (congrArg (fun value : Nat =>
    Approximation.Rational.Budget.Aggregate.countCoordinate value * kept.sum.chargeSum) kept.count_eq)

/-- Original source-fragment comparisons bound the actual outgoing gaps against the SAME old request increments.

The old allowances and indices remain explicit. This is a finite source
model increment comparison, not an absolute primitive normalization or
a claimed physical/canonical integral equality.
-/
theorem accurate : Data.Gaussian.Norm.Basic.normSq
    (gaussianSum (Closed.gaps shared entries geometry roots closed) - gaussianSum requests.increments) ≤
      kept.sum.bound :=
  Eq.mp (congrArg (fun value : Canonical => Data.Gaussian.Norm.Basic.normSq
    (value - gaussianSum requests.increments) ≤ kept.sum.bound) kept.value_eq_gaps) kept.sum.accurate

/-- A retained actual comparison and target, with either a derived strict payment or honest old-bound insufficiency. -/
abbrev Payment (requested : Rational) :=
  {value : SourceAttachment shared requests entries geometry roots closed × Rational // value = (kept, requested)} ×
  ({_value : Unit // kept.sum.bound < requested ∧ Data.Gaussian.Norm.Basic.normSq
      (gaussianSum (Closed.gaps shared entries geometry roots closed) - gaussianSum requests.increments) < requested} ⊕
   {_value : Unit // ¬kept.sum.bound < requested})

/-- Check the actual retained old-stage allowance without changing any old request, stage, source or observation.

The unpaid branch certifies only that this computed bound is insufficient
for the strict target check. It gives no lower bound on the actual error.
-/
def pay (requested : Rational) : kept.Payment requested :=
  if paid : kept.sum.bound < requested then
    ⟨⟨(kept, requested), rfl⟩, Sum.inl ⟨(), paid, kept.accurate.trans_lt paid⟩⟩
  else ⟨⟨(kept, requested), rfl⟩, Sum.inr ⟨(), paid⟩⟩

end SourceAttachment

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets
