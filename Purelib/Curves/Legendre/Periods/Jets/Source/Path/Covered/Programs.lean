module
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Integration.CertifiedProgram.Arithmetic

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Certificates
public import Purelib.Riemann.Paths.PreparedPathParentCaches
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Comparison
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
public import Purelib.Data.Nat.List.Maximum
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Progressive source integrals on an unchanged finite covered path

Only the original source-model and observation accuracies change with stage.
The original centered parents, physical endpoints, covering neighborhoods and
lifted sheets remain literal owners of all six programme lists. Actual source
preparation caches are supplied once per finite request and consumed directly;
no source or endpoint request is repeated by a row-selection operation.

The numerical programme applies to open or closed centered paths. Closed
cycle certification retains its original literal return endpoint. The
construction certifies fixed-parameter integrands and their progressive
finite integral samples. Root-chain admissions for primitive relations and
parameter differentiation are separate certificates.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}

/-- Every selected physical source cell retains the original parent's exact displacement cost. -/
theorem cell_cost (prepared : PreparedParent patch count floor covered targets) (channel : Fin 6) :
    Norm.Basic.normSq (prepared.preparation.cell.models.cell channel).displacement = cost parent := by
  rewrite [prepared.preparation.cell_eq]
  change Norm.Basic.normSq ((prepared.preparation.models.cell channel).finish -
    (prepared.preparation.models.cell channel).start) = _
  rewrite [prepared.preparation.models.cell_start, prepared.preparation.models.cell_finish]
  rfl

/-- Every selected physical source cell retains the original count-paid local allowance. -/
theorem cell_allowance (prepared : PreparedParent patch count floor covered targets) (channel : Fin 6) :
    (prepared.preparation.cell.models.cell channel).localAllowance = targets.localBound := by
  rewrite [prepared.preparation.cell_eq]
  exact prepared.preparation.models.cell_allowance channel

/-- The weighted allowance uses that same original displacement cost and count-paid allocation. -/
theorem cell_weightedAllowance (prepared : PreparedParent patch count floor covered targets) (channel : Fin 6) :
    (prepared.preparation.cell.models.cell channel).weightedAllowance =
      cost parent * targets.localBound := by
  change Basic.Canonical.normSq (prepared.preparation.cell.models.cell channel).displacement *
    (prepared.preparation.cell.models.cell channel).localAllowance = _
  rewrite [← Norm.Basic.normSq_eq_canonical, prepared.cell_cost, prepared.cell_allowance]
  rfl

/-- Actual independent same-patch preparations have close selected original integral samples at both paid accuracies.

The two original target paths may differ; their allocations retain both
local bounds. The same physical parent fixes both oriented sample endpoints
and displacement cost. Complete requests, independent floors, models,
point-query factories and reading states are retained. The comparison is
derived from those caches without a supplied root or final bound.
-/
theorem integral_difference_le {lastBaseStart lastBaseFinish : LiftedPoint 2}
    {lastOriginal : LiftedPath 2 lastBaseStart lastBaseFinish} {lastFloor firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets original firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParent patch count floor covered firstTargets)
    (last : PreparedParent patch count lastFloor covered lastTargets) (channel : Fin 6) :
    Norm.Basic.normSq ((first.preparation.cell.models.cell channel).integralSample -
      (last.preparation.cell.models.cell channel).integralSample) ≤
        16 * (firstTargets.localBound + lastTargets.localBound) * cost parent := by
  let firstQuery := first.preparation.query.castCell first.preparation.cell_eq
  let lastQuery := last.preparation.query.castCell last.preparation.cell_eq
  rewrite [first.preparation.cell_eq, last.preparation.cell_eq]
  change Norm.Basic.normSq ((first.preparation.models.cell channel).integralSample -
      (last.preparation.models.cell channel).integralSample) ≤
    16 * (firstTargets.localBound + lastTargets.localBound) *
      Norm.Basic.normSq ((finishPoint parent).coordinate - (startPoint parent).coordinate)
  refine Fin.cases ?_ ?_ channel
  · exact Query.valueZero_integral_difference_le first.preparation.models last.preparation.models
      (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
      firstTargets.localBound_positive lastTargets.localBound_positive
  · intro channel
    refine Fin.cases ?_ ?_ channel
    · exact Query.valueOne_integral_difference_le first.preparation.models last.preparation.models
        (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
        firstTargets.localBound_positive lastTargets.localBound_positive
    · intro channel
      refine Fin.cases ?_ ?_ channel
      · exact Query.firstZero_integral_difference_le first.preparation.models last.preparation.models
          (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
          firstTargets.localBound_positive lastTargets.localBound_positive
      · intro channel
        refine Fin.cases ?_ ?_ channel
        · exact Query.firstOne_integral_difference_le first.preparation.models last.preparation.models
            (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
            firstTargets.localBound_positive lastTargets.localBound_positive
        · intro channel
          refine Fin.cases ?_ ?_ channel
          · exact Query.secondZero_integral_difference_le first.preparation.models last.preparation.models
              (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
              firstTargets.localBound_positive lastTargets.localBound_positive
          · intro channel
            refine Fin.cases ?_ (fun index => Fin.elim0 index) channel
            · exact Query.secondOne_integral_difference_le first.preparation.models last.preparation.models
                (start_inside patch count) (finish_inside patch count covered) firstQuery lastQuery frame
                firstTargets.localBound_positive lastTargets.localBound_positive

section CommonPrimitive

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Geometric
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget)
open Purelib.Riemann.Normalization
open ContinuedInverseRoot (ContinuedNeighborhood)
open InverseModelEdgeTransition (EdgeTransition)

/-- The actual stored common source model is selected above this same original preparation floor.

The first retained integrand Selection, its place in the original six-way
maximum and the same attached source payment supply the three bounds.
No request, model or endpoint observation is constructed by this readback.
-/
theorem floor_le_model_stage (prepared : PreparedParent patch count floor covered targets) :
    floor ≤ prepared.preparation.attached.source.selection.stage :=
  (prepared.requests.valueZero.selection.lower.trans prepared.requests.valueZero_stage_le).trans
    prepared.preparation.attached.integrands_paid

/-- Construct the actual common model edge from the same retained parent source sample and original source-owner link.

The patch's original base-query bridge identifies the stored firstSample;
the supplied common Point retains the original parent's signed name link.
Only the two cached selected model values are evaluated. Whole signed-edge
transport consumes their stored model equalities without another Point,
model refinement, source preparation or sign search.
-/
def commonEdge (prepared : PreparedParent patch count floor covered targets)
    {commonCount commonFloor : Nat} {commonTarget : Rational}
    {common : ContinuedNeighborhood (Paths.polynomial parameter) commonCount} {commonCache : Cache common}
    (requested : Request commonCache commonFloor commonTarget)
    (sample : ContinuedNeighborhood.Point common (startPoint parent).coordinate)
    (related : NamedEquivalent (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      sample.certificate.value.name)
    (commonStart : common.box.Contains (startPoint parent).coordinate)
    (commonFinish : common.box.Contains (finishPoint parent).coordinate) :
    {edge : EdgeTransition ((patch.neighborhood count).base.refine
        prepared.preparation.attached.source.selection.stage)
      (common.base.refine requested.selection.stage) (startPoint parent).coordinate (finishPoint parent).coordinate //
      edge.sample.alignment.flip = false} :=
  let original := prepared.preparation.attached.source
  let queryToLocal := patch.point_equivalent_at count 0 parent.edge.baseInside parent.edge.point_zero
    (start_inside patch count) prepared.firstSample
  let sourceToQuery := PreparedConstantModels.PreparedEdge.ownerRootEquivalent_baseQuery parent.edge
  let roots := (sourceToQuery.trans queryToLocal).symm.trans related
  let retained := ContinuedInverseRootOverlap.EdgeTransition.ofEquivalentPoints prepared.firstSample sample
    (start_inside patch count) (finish_inside patch count covered) commonStart commonFinish roots
    original.selection.stage requested.selection.stage original.model requested.model
    (congrArg (fun model => model.value.eval (startPoint parent).coordinate) original.model_eq)
    (congrArg (fun model => model.value.eval (startPoint parent).coordinate) requested.model_eq)
  let signed : {edge : EdgeTransition original.model requested.model
      (startPoint parent).coordinate (finishPoint parent).coordinate // edge.sample.alignment.flip = false} :=
    ⟨retained, rfl⟩
  let first := Eq.mp (congrArg (fun model =>
    {edge : EdgeTransition model requested.model (startPoint parent).coordinate (finishPoint parent).coordinate //
      edge.sample.alignment.flip = false}) original.model_eq) signed
  Eq.mp (congrArg (fun model =>
    {edge : EdgeTransition ((patch.neighborhood count).base.refine original.selection.stage) model
      (startPoint parent).coordinate (finishPoint parent).coordinate // edge.sample.alignment.flip = false})
    requested.model_eq) first

/-- The retained original parent and common source cells satisfy their actual selected six-form primitive payment.

The complete original source preparation and original common model bank
remain inputs. The signed transition is derived here from the stored first
sample and parent's root bridge, rather than supplied as a successful
comparison. Stage inequalities concern the actual retained pair Selection.
-/
theorem common_integral_difference_lt (prepared : PreparedParent patch count floor covered targets)
    {commonCount commonFloor : Nat} {commonTarget commonAllowance : Rational}
    {common : ContinuedNeighborhood (Paths.polynomial parameter) commonCount} {commonCache : Cache common}
    {requested : Request commonCache commonFloor commonTarget}
    (models : CellModels requested (startPoint parent).coordinate (finishPoint parent).coordinate commonAllowance)
    (sample : ContinuedNeighborhood.Point common (startPoint parent).coordinate)
    (related : NamedEquivalent (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      sample.certificate.value.name)
    (commonStart : common.box.Contains (startPoint parent).coordinate)
    (commonFinish : common.box.Contains (finishPoint parent).coordinate) (channel : Fin 6)
    (budget : PrimitivePairBudget (patch.neighborhood count) common
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (startPoint parent).coordinate (finishPoint parent).coordinate
      (Specification.Table.forms parameter channel).denominatorPairs)
    {current : Nat} {tolerance : Rational} (selection : Search.Selection budget.scale current tolerance)
    (localFloorPaid : selection.stage ≤ floor)
    (commonFloorPaid : selection.stage ≤ commonFloor) :
    Norm.Basic.normSq ((prepared.preparation.models.cell channel).integralSample -
      (models.cell channel).integralSample) < tolerance := by
  let edge := prepared.commonEdge requested sample related commonStart commonFinish
  exact prepared.preparation.models.pair_integral_difference_lt models channel budget selection edge.val
    edge.property (localFloorPaid.trans prepared.floor_le_model_stage)
    (commonFloorPaid.trans requested.selection.lower)

end CommonPrimitive

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- A scalar head and bounded scalar tail retain their exact finite summation order. -/
private theorem sumFin_cases {size : Nat} (head : Canonical) (tail : Fin size → Canonical) :
    sumFin (Fin.cases head tail) = head + sumFin tail := Algebra.FiniteSum.Fin.sumFin_succ _

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- The actual fixed parent spine's finite sum of original squared displacements. -/
@[expose] def displacementCost (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : Rational :=
  sumFin (fun index : Fin parents.length => PreparedParent.cost (parents[index.val]'index.isLt))

/-- Adding one original parent adds exactly its retained displacement cost to the finite total. -/
theorem displacementCost_cons (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    displacementCost (parent :: parents) = PreparedParent.cost parent + displacementCost parents := by
  have split := Algebra.FiniteSum.Fin.sumFin_succ
    (fun index : Fin (parent :: parents).length => PreparedParent.cost ((parent :: parents)[index.val]'index.isLt))
  have tail : sumFin (fun index : Fin parents.length =>
        PreparedParent.cost ((parent :: parents)[index.succ.val]'index.succ.isLt)) = displacementCost parents :=
    Algebra.FiniteSum.Fin.sumFin_congr (fun _ => rfl)
  exact split.trans (congrArg (PreparedParent.cost parent + ·) tail)

/-- The original finite displacement-cost sum is nonnegative, including the empty spine. -/
theorem displacementCost_nonnegative (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    0 ≤ displacementCost parents :=
  Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _
    (fun index => PreparedParent.cost_nonnegative (parents[index.val]'index.isLt))

/-- Each selected source list contains exactly one original cell per original centered parent. -/
theorem cells_length : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (channel : Fin 6) → ((sources covered prepared chain).cells channel).length = parents.length
  | [], .nil, .unit, _, _, .nil point, channel =>
      congrArg List.length (Path.cells_nil (parameter := parameter) point channel)
  | _ :: _, .cons _ _ covered, ⟨head, remaining⟩, _, _, .cons _ chain, channel =>
      (congrArg List.length (Path.cells_cons head.preparation.cell (sources covered remaining chain) channel)).trans
        (congrArg Nat.succ (cells_length covered remaining chain channel))

/-- The actual source-list integral is the finite sum of its identical retained bounded-occurrence cell samples. -/
theorem integralSample_eq_sumFin : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (channel : Fin 6) → (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample =
      sumFin (fun index : Fin parents.length =>
        ((prepared.entry index).preparation.cell.models.cell channel).integralSample)
  | [], .nil, .unit, _, _, .nil point, channel =>
      congrArg (fun cells => (PathModel.mk cells).integralSample)
        (Path.cells_nil (parameter := parameter) point channel)
  | parent :: parents, .cons patch inside covered, ⟨head, remaining⟩, _, _, .cons _ chain, channel => by
      have lists := Path.cells_cons head.preparation.cell (sources covered remaining chain) channel
      let samples := fun index : Fin (parent :: parents).length =>
        ((entry (covered := CoveredParents.cons patch inside covered)
          (targets := targets) ⟨head, remaining⟩ index).preparation.cell.models.cell channel).integralSample
      let tail := fun index : Fin parents.length =>
        ((entry (covered := covered) (targets := targets) remaining index).preparation.cell.models.cell
          channel).integralSample
      have pointwise : ∀ index, samples index =
          Fin.cases (head.preparation.cell.models.cell channel).integralSample tail index := by
        intro index
        refine Fin.cases (Eq.refl _) ?_ index
        intro index
        rfl
      have finite := Algebra.FiniteSum.Fin.sumFin_congr pointwise
      calc
        _ = (PathModel.mk (head.preparation.cell.models.cell channel ::
              (sources covered remaining chain).cells channel)).integralSample :=
          congrArg (fun cells => (PathModel.mk cells).integralSample) lists
        _ = (head.preparation.cell.models.cell channel).integralSample +
            (PathModel.mk ((sources covered remaining chain).cells channel)).integralSample := rfl
        _ = (head.preparation.cell.models.cell channel).integralSample +
            sumFin (fun index =>
              ((entry (covered := covered) (targets := targets) remaining index).preparation.cell.models.cell
                channel).integralSample) :=
          congrArg ((head.preparation.cell.models.cell channel).integralSample + ·)
            (integralSample_eq_sumFin covered remaining chain channel)
        _ = sumFin (Fin.cases (head.preparation.cell.models.cell channel).integralSample tail) :=
          (sumFin_cases _ tail).symm
        _ = _ := finite.symm

section BlockRows

open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents (append)

/-- The original source path reads precisely the ordered cells from its retained prepared-parent product.

The centered chain supplies only incidence and endpoint indices. This
whole-list identity reads the same complete cell at every original parent;
no source, point, observation or model is produced by the readback.
-/
theorem sources_cells : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (channel : Fin 6) →
    (sources covered prepared chain).cells channel =
      cells prepared channel
  | [], .nil, .unit, _, _, .nil point, channel => (Path.cells_nil point channel).trans (cells_nil channel).symm
  | _ :: _, .cons patch inside covered, ⟨head, remaining⟩, _, _, .cons _ chain, channel =>
      (Path.cells_cons head.preparation.cell (sources covered remaining chain) channel).trans
        ((congrArg (List.cons (head.preparation.cell.models.cell channel))
          (sources_cells covered remaining chain channel)).trans
            (cells_cons patch inside covered head remaining channel).symm)

/-- Splitting a retained source product adds the samples of its exact original prefix and suffix.

The three centered chains supply only their original incidence indices.
The split consumes the actual saved product; both resulting cell lists
retain the same source preparations, allocation and floor.
-/
theorem split_integralSample
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    {wholeStart wholeFinish firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (wholeChain : CenteredPathChain (first ++ last) (start := wholeStart) (finish := wholeFinish))
    (firstChain : CenteredPathChain first (start := firstStart) (finish := firstFinish))
    (lastChain : CenteredPathChain last (start := lastStart) (finish := lastFinish))
    (prepared : PreparedParents (firstCover.append lastCover) floor targets) (channel : Fin 6) :
    let divided := split firstCover lastCover prepared
    (PathModel.mk ((sources (firstCover.append lastCover) prepared wholeChain).cells channel)).integralSample =
      (PathModel.mk ((sources firstCover divided.1 firstChain).cells channel)).integralSample +
        (PathModel.mk ((sources lastCover divided.2 lastChain).cells channel)).integralSample := by
  intro divided
  have wholeCells := (sources_cells (firstCover.append lastCover) prepared wholeChain channel).trans
    (split_cells firstCover lastCover prepared channel)
  have firstCells := sources_cells firstCover divided.1 firstChain channel
  have lastCells := sources_cells lastCover divided.2 lastChain channel
  calc
    _ = (PathModel.mk (cells divided.1 channel ++ cells divided.2 channel)).integralSample :=
      congrArg (fun list => (PathModel.mk list).integralSample) wholeCells
    _ = (PathModel.mk (cells divided.1 channel)).integralSample +
        (PathModel.mk (cells divided.2 channel)).integralSample := PathModel.integralSample_concat _ _
    _ = _ := congrArg₂ (fun left right : Canonical => left + right)
      (congrArg (fun list => (PathModel.mk list).integralSample) firstCells).symm
      (congrArg (fun list => (PathModel.mk list).integralSample) lastCells).symm

/-- The original global source product at one retained covered-block parent cache.

This ordinary exact type view retains the supplied complete cache, its
literal original parent list, global Targets and unchanged floor. It
constructs no preparation or alternative source family.
-/
@[expose] def OnBlocks {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks) :=
  PreparedParents (frame := frame) (basis := basis) (count := 1)
    (parents := caches.parents) caches.covered floor targets

/-- Materialize the six actual physical cell lists at each original covered-block boundary.

The original global product is split once per moving block. Its same
suffix is passed to the tail, including stationary handoffs, and the six
lists are cached before any channel lookup. No local chain, target,
source request, point, model or observation is reconstructed.
-/
def blockRows {sheet : Fin 2} :
    ∀ {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
      {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
      {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
      (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks),
      OnBlocks (floor := floor) (targets := targets) caches →
        List (DependentVector (fun _ : Fin 6 => List CellModel)) :=
  Blocks.ParentCaches.mapBanks
    (fun parents cover => PreparedParents (frame := frame) (basis := basis) (count := 1)
      (parents := parents) cover floor targets)
    (fun {first last} firstCover lastCover bank =>
      split (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (first := first) (last := last) firstCover lastCover bank)
    (fun _ cache bank => DependentVector.ofFn (fun channel : Fin 6 =>
      cells (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (parents := cache.parents) (covered := cache.covered) bank channel))

/-- Read the original block-row operation as its unchanged retained-bank interpreter.

The opaque equality exposes only the whole operation's defining equation.
The executable body stays hidden; all callbacks consume the same actual
split prefix and literal suffix with unchanged source floor and Targets.
-/
theorem blockRows_eq_mapBanks {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks)
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) :
    blockRows caches prepared = Blocks.ParentCaches.mapBanks
      (fun parents cover => PreparedParents (frame := frame) (basis := basis) (count := 1)
        (parents := parents) cover floor targets)
      (fun {first last} firstCover lastCover bank =>
        split (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
          (first := first) (last := last) firstCover lastCover bank)
      (fun _ cache bank => DependentVector.ofFn (fun channel : Fin 6 =>
        cells (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
          (parents := cache.parents) (covered := cache.covered) bank channel))
      caches prepared := (rfl)

/-- A complete six-cell vector is read from one original prepared product on its unchanged cover.

The same global Targets and source floor index the witness. This exact
proposition does not prepare a source or introduce another numerical bank.
-/
@[expose] def CellRow {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (floor : Nat) (targets : CellEndpoints.Targets original stage)
    (row : DependentVector (fun _ : Fin 6 => List CellModel)) : Prop :=
  ∃ prepared : PreparedParents (frame := frame) covered floor targets,
    row = DependentVector.ofFn (fun channel : Fin 6 => cells prepared channel)

/-- An empty original block spine has no stored physical source row. -/
theorem blockRows_nil {sheet : Fin 2} (point : Canonical)
    (source : Owner ((Fibre.frameCurve frame).polynomial.eval point))
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.nil point source))
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) :
    blockRows caches prepared = [] := by
  unfold blockRows
  apply Blocks.ParentCaches.mapBanks_nil

/-- A moving block retains its exact prepared prefix and passes the same split suffix to the remaining blocks.

The six complete cell lists come from the original head parent cache.
The original global floor and Targets remain unchanged in both products.
-/
theorem blockRows_cons {sheet : Fin 2}
    {start middle finish : Canonical} {ambient : Purelib.Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial ambient start middle}
    {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    (covered : CoveredTracedPath path source)
    (tail : Blocks (Fibre.frameCurve frame).polynomial middle covered.traced.finishOwner finish target)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.cons covered tail))
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) :
    blockRows caches prepared =
      let divided := split (frame := frame) (basis := basis) (count := 1)
        (floor := floor) (targets := targets) caches.1.covered (Blocks.ParentCaches.covered caches.2) prepared
      DependentVector.ofFn (fun channel : Fin 6 => cells divided.1 channel) ::
        blockRows caches.2 divided.2 := by
  unfold blockRows
  apply Blocks.ParentCaches.mapBanks_cons

/-- A stationary owner handoff preserves the complete source bank and contributes no physical cell row. -/
theorem blockRows_handoff {sheet : Fin 2} {point finish : Canonical}
    {source : Owner ((Fibre.frameCurve frame).polynomial.eval point)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    (join : Blocks.Join source)
    (tail : Blocks (Fibre.frameCurve frame).polynomial point join.1 finish target)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.handoff join tail))
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) :
    blockRows caches prepared = blockRows (blocks := tail) caches prepared := by
  unfold blockRows
  apply Blocks.ParentCaches.mapBanks_handoff

/-- Each channel of the stored block rows flattens to the identical original global physical cells.

The split law preserves every complete cell in its original order. The
channel vector is an eager cache, so its getter reuses the same values
without splitting or preparing the original source product again.
-/
@[expose] def BlockRowReadback {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks)
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) (channel : Fin 6) : Prop :=
  ((blockRows (frame := frame) (basis := basis) (floor := floor) (targets := targets)
    caches prepared).map (fun row => row.get channel)).flatten =
      cells (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (parents := caches.parents) (covered := caches.covered) prepared channel

/-- The complete original owner-indexed six-channel cell-list readback telescope. -/
@[expose] def BlockRowsReadback {sheet : Fin 2} : Prop :=
  ∀ {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks)
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) (channel : Fin 6),
    BlockRowReadback (frame := frame) (basis := basis) (floor := floor) (targets := targets)
      caches prepared channel

/-- The actual retained block rows preserve each complete original global physical cell list. -/
theorem blockRows_flatten {sheet : Fin 2} :
    BlockRowsReadback (frame := frame) (basis := basis) (floor := floor) (targets := targets) (sheet := sheet) := by
  intro start finish source target blocks caches prepared channel
  exact Blocks.ParentCaches.mapBanks_flatten
    (fun parents cover => PreparedParents (frame := frame) (basis := basis) (count := 1)
      (parents := parents) cover floor targets)
    (fun {first last} firstCover lastCover bank =>
      split (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (first := first) (last := last) firstCover lastCover bank)
    (fun _ cache bank => DependentVector.ofFn (fun channel : Fin 6 =>
      cells (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (parents := cache.parents) (covered := cache.covered) bank channel))
    (fun row => row.get channel)
    (fun _ bank => cells (frame := frame) (basis := basis) (count := 1)
      (floor := floor) (targets := targets) bank channel)
    (fun bank => by
      cases bank
      exact cells_nil (frame := frame) (basis := basis) (count := 1)
        (floor := floor) (targets := targets) channel)
    (fun firstCover lastCover bank => split_cells (frame := frame) (basis := basis) (count := 1)
      (floor := floor) (targets := targets) firstCover lastCover bank channel)
    (fun _ cache bank => DependentVector.ofFn_get (fun channel : Fin 6 =>
      cells (frame := frame) (basis := basis) (count := 1) (floor := floor) (targets := targets)
        (parents := cache.parents) (covered := cache.covered) bank channel) channel)
    caches prepared

/-- The single global source path has exactly the flattened stored cells at its original block occurrences. -/
theorem sources_cells_blockRows {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks)
    (prepared : OnBlocks (floor := floor) (targets := targets) caches) (channel : Fin 6) :
    (sources caches.covered prepared caches.centeredChain).cells channel =
      ((blockRows (frame := frame) (basis := basis) (floor := floor) (targets := targets)
        caches prepared).map (fun row => row.get channel)).flatten :=
  (sources_cells (frame := frame) (basis := basis) (count := 1) (floor := floor)
    (targets := targets) caches.covered prepared caches.centeredChain channel).trans
    (blockRows_flatten (frame := frame) (basis := basis) (floor := floor) (targets := targets)
      caches prepared channel).symm

/-- The complete same-owner global source acquisition with its retained factory equations and six row lists.

This exact Sigma names the existing centered chain, global Targets,
original prepared product, whole Source.Path and actual cached row lists.
It introduces no alternative geometric or numerical owner.
-/
@[expose] def BlockSources {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      basis sheet blocks) (floor stage : Nat) :=
    Σ chain : {actual : CenteredPathChain caches.parents
        (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) // actual = caches.centeredChain},
    Σ targets : {actual : CellEndpoints.Targets chain.val.path stage //
      actual = CellEndpoints.Targets.build chain.val.path stage},
    Σ prepared : {actual : PreparedParents (frame := frame) (basis := basis) (count := 1)
        (parents := caches.parents) caches.covered floor targets.val //
      actual = prepareCovered caches.covered floor targets.val},
    Σ whole : {actual : Path parameter chain.val.path //
      actual = sources caches.covered prepared.val chain.val},
    {rows : List (DependentVector (fun _ : Fin 6 => List CellModel)) //
      rows = blockRows caches prepared.val ∧
        ∀ channel : Fin 6, whole.val.cells channel = (rows.map (fun row => row.get channel)).flatten}

/-- Construct the retained global source acquisition once on the supplied original parent caches. -/
def blockSources {sheet : Fin 2}
    {start finish : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval finish)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial start source finish target}
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      basis sheet blocks) (floor stage : Nat) :
    BlockSources caches floor stage := by
  let chain := caches.centeredChain
  let targets := CellEndpoints.Targets.build chain.path stage
  let prepared := prepareCovered caches.covered floor targets
  let whole := sources caches.covered prepared chain
  let rows := blockRows caches prepared
  refine ⟨⟨chain, rfl⟩, ⟨targets, rfl⟩, ⟨prepared, rfl⟩, ⟨whole, rfl⟩, ⟨rows, rfl, ?_⟩⟩
  intro channel
  exact sources_cells_blockRows caches prepared channel

end BlockRows

section SegmentRows

open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments (ParentCaches)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments (parents)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {ambient : Box}

/-- Original source products on the same ordered covered-segment parent caches.

This reducible product view keeps each segment's exact original parent list
and cover. Every entry retains the same global endpoint targets and source
floor; the empty segment family contains no source data.
-/
@[expose] def OnSegments (floor : Nat) (targets : CellEndpoints.Targets original stage) {sheet : Fin 2} :
    ∀ {start finish : Canonical}
      {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      (pieces : CoveredSegments prepared), ParentCaches basis sheet pieces → Type 1
  | _, _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, _, .cons _ tail, caches =>
      PreparedParents caches.1.covered floor targets ×
        OnSegments floor targets tail caches.2
termination_by structural _ _ _ _ _ pieces _ => pieces

/-- Cut one saved global source bank along its retained segment counts, without preparing a new source.

The existing parent-cache constructor determines the exact segment owners.
Each cut retains whole original prepared parents and passes the same saved
suffix into the next segment. Parent and cover selectors run only on the
stored spines; no traced preparation or numerical source is acquired.
-/
def segmentSources {sheet : Fin 2} :
    ∀ {start finish : Canonical}
      {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      (pieces : CoveredSegments prepared) (cached : List (CenteredEdge (Fibre.frameCurve frame) basis))
      (same : cached = parents basis sheet pieces)
      (covered : CoveredParents 1 cached), PreparedParents covered floor targets →
      OnSegments (floor := floor) (targets := targets)
        pieces (ParentCaches.build basis sheet pieces cached same covered)
  | _, _, _, _, _, .nil _ _, _, _, _, _ => PUnit.unit
  | _, _, _, _, _, .cons first tail, cached, same, covered, saved => by
      have split : cached = (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet
          first.path.traced.prepared).parents ++
            parents basis sheet tail := same
      have tailEq : cached.drop first.mesh.edgeCount =
          parents basis sheet tail := by
        rewrite [split, ← PreparedSegmentParentBanks.CoveredSegment.path_parentCount first basis sheet,
          List.drop_left]
        rfl
      let divided := splitAt first.mesh.edgeCount covered saved
      let remainingParents := cached.drop first.mesh.edgeCount
      let remainingCover := PreparedPathParentCaches.CoveredParents.drop first.mesh.edgeCount covered
      exact ⟨divided.1, segmentSources tail remainingParents tailEq remainingCover divided.2⟩
termination_by structural _ _ _ _ _ pieces _ _ _ _ => pieces

/-- Read complete cached physical cells from the original segment source products in occurrence order. -/
@[expose] def segmentCells {sheet : Fin 2} :
    ∀ {start finish : Canonical}
      {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      (pieces : CoveredSegments prepared) (caches : ParentCaches basis sheet pieces),
      OnSegments (floor := floor) (targets := targets) pieces caches → Fin 6 → List (List CellModel)
  | _, _, _, _, _, .nil _ _, _, _, _ => []
  | _, _, _, _, _, .cons _ tail, caches, saved, channel =>
      cells saved.1 channel :: segmentCells tail caches.2 saved.2 channel
termination_by structural _ _ _ _ _ pieces _ _ _ => pieces

namespace OnSegments

/-- Prepare one six-channel source product per original cached segment at the common floor.

Each entry consumes its existing parent list and covering spine. The tail
is passed directly to the next structural step; source observations are
materialized once and subsequently shared by all six channel selectors.
-/
def prepare (floor : Nat) (targets : CellEndpoints.Targets original stage) {sheet : Fin 2} :
    ∀ {start finish : Canonical}
      {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      (pieces : CoveredSegments prepared) (caches : ParentCaches basis sheet pieces),
      OnSegments floor targets pieces caches
  | _, _, _, _, _, .nil _ _, _ => PUnit.unit
  | _, _, _, _, _, .cons _ tail, caches =>
      ⟨prepareCovered caches.1.covered floor targets, prepare floor targets tail caches.2⟩
termination_by structural _ _ _ _ _ pieces _ => pieces

variable {sheet : Fin 2} {start finish : Canonical}
variable {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
variable {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
variable {pieces : CoveredSegments prepared} {caches replacement : ParentCaches basis sheet pieces}

/-- Transport the saved source product through equality of its complete original segment parent caches.

The equality retains every parent, cover and prepared-path provenance.
Only the cache index changes; all original source preparations, targets,
selected stages and observations remain the supplied data.
-/
@[expose] def castCaches (saved : OnSegments floor targets pieces caches) (same : caches = replacement) :
    OnSegments floor targets pieces replacement := by
  cases same
  exact saved

/-- Cache-index transport preserves the complete original source product. -/
theorem castCaches_heq (saved : OnSegments floor targets pieces caches) (same : caches = replacement) :
    HEq (saved.castCaches same) saved := by
  cases same
  rfl

/-- Reading a transported segment source preserves its complete ordered cell lists in every channel. -/
theorem castCaches_cells (saved : OnSegments floor targets pieces caches) (same : caches = replacement)
    (channel : Fin 6) :
    segmentCells pieces replacement (saved.castCaches same) channel = segmentCells pieces caches saved channel := by
  cases same
  rfl

end OnSegments

/-- The segment source views retain the whole original physical cell list for every channel.

Each finite cut reads the original cached cells on its two retained sides.
Flattening the segment lists preserves all repeated parent occurrences,
zero displacements, signed cells and original selected source stages.
-/
theorem segmentSources_cells {sheet : Fin 2} :
    ∀ {start finish : Canonical}
      {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      (pieces : CoveredSegments prepared) (cached : List (CenteredEdge (Fibre.frameCurve frame) basis))
      (same : cached = parents basis sheet pieces)
      (covered : CoveredParents 1 cached) (saved : PreparedParents covered floor targets) (channel : Fin 6),
      (segmentCells pieces (ParentCaches.build basis sheet pieces cached same covered)
        (segmentSources pieces cached same covered saved) channel).flatten = cells saved channel
  | _, _, _, _, _, .nil _ _, cached, same, covered, saved, channel => by
      change cached = [] at same
      subst cached
      cases covered
      cases saved
      exact (cells_nil (frame := frame) (basis := basis) (count := 1)
        (floor := floor) (targets := targets) channel).symm
  | _, _, _, _, _, .cons first tail, cached, same, covered, saved, channel => by
      have split : cached = (CenteredPathChain.ofPreparedPath (Fibre.frameCurve frame) basis sheet
          first.path.traced.prepared).parents ++
            parents basis sheet tail := same
      have tailEq : cached.drop first.mesh.edgeCount =
          parents basis sheet tail := by
        rewrite [split, ← PreparedSegmentParentBanks.CoveredSegment.path_parentCount first basis sheet,
          List.drop_left]
        rfl
      let divided := splitAt first.mesh.edgeCount covered saved
      let remainingParents := cached.drop first.mesh.edgeCount
      let remainingCover := PreparedPathParentCaches.CoveredParents.drop first.mesh.edgeCount covered
      change cells divided.1 channel ++
        (segmentCells tail (ParentCaches.build basis sheet tail remainingParents tailEq remainingCover)
          (segmentSources tail remainingParents tailEq remainingCover divided.2) channel).flatten = cells saved channel
      rewrite [segmentSources_cells tail remainingParents tailEq remainingCover divided.2 channel]
      exact (cells_splitAt first.mesh.edgeCount covered saved channel).symm
termination_by structural _ _ _ _ _ pieces _ _ _ _ _ => pieces

end SegmentRows

/-- The weighted allowance is the same count-paid allocation times the original finite displacement-cost sum. -/
theorem totalWeightedAllowance_eq : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    (channel : Fin 6) → (PathModel.mk ((sources covered prepared chain).cells channel)).totalWeightedAllowance =
      targets.localBound * displacementCost parents
  | [], .nil, .unit, _, _, .nil point, channel => by
      have lists := Path.cells_nil (parameter := parameter) point channel
      calc
        _ = (PathModel.mk []).totalWeightedAllowance :=
          congrArg (fun cells => (PathModel.mk cells).totalWeightedAllowance) lists
        _ = _ := (Field.mul_zero_direct _).symm
  | parent :: _, .cons _ _ covered, ⟨head, remaining⟩, _, _, .cons _ chain, channel => by
      have lists := Path.cells_cons head.preparation.cell (sources covered remaining chain) channel
      calc
        _ = (PathModel.mk (head.preparation.cell.models.cell channel ::
              (sources covered remaining chain).cells channel)).totalWeightedAllowance :=
          congrArg (fun cells => (PathModel.mk cells).totalWeightedAllowance) lists
        _ = (head.preparation.cell.models.cell channel).weightedAllowance +
            (PathModel.mk ((sources covered remaining chain).cells channel)).totalWeightedAllowance := rfl
        _ = PreparedParent.cost parent * targets.localBound + targets.localBound * displacementCost _ :=
          (congrArg (fun value => value +
            (PathModel.mk ((sources covered remaining chain).cells channel)).totalWeightedAllowance)
              (head.cell_weightedAllowance channel)).trans
            (congrArg (PreparedParent.cost parent * targets.localBound + ·)
              (totalWeightedAllowance_eq covered remaining chain channel))
        _ = _ := by
          rewrite [displacementCost_cons]
          ring1

/-- The aggregate allowance retains the original parent count and the identical finite displacement costs. -/
theorem aggregateAllowance_eq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (channel : Fin 6) : (PathModel.mk ((sources covered prepared chain).cells channel)).aggregateAllowance =
      (parents.length : Rational) * targets.localBound * displacementCost parents := by
  change (((sources covered prepared chain).cells channel).length : Rational) *
      (PathModel.mk ((sources covered prepared chain).cells channel)).totalWeightedAllowance = _
  rewrite [cells_length covered prepared chain channel, totalWeightedAllowance_eq covered prepared chain channel]
  ring1

/-- Source-list samples at independent floors and target paths obey their actual count and displacement-cost sum.

The same covered ordered physical parents and centered chain fix every
oriented sample endpoint. Each original target path retains its own local
allocation, and both complete source products remain supplied unchanged.
-/
theorem integral_difference_le {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents)
    {lastBaseStart lastBaseFinish : LiftedPoint 2} {lastOriginal : LiftedPath 2 lastBaseStart lastBaseFinish}
    {lastFloor firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets original firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParents covered floor firstTargets) (last : PreparedParents covered lastFloor lastTargets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (channel : Fin 6) :
    Norm.Basic.normSq ((PathModel.mk ((sources covered first chain).cells channel)).integralSample -
      (PathModel.mk ((sources covered last chain).cells channel)).integralSample) ≤
        16 * (firstTargets.localBound + lastTargets.localBound) *
          (parents.length : Rational) * displacementCost parents := by
  have bound := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    (fun index : Fin parents.length => ((first.entry index).preparation.cell.models.cell channel).integralSample)
    (fun index : Fin parents.length => ((last.entry index).preparation.cell.models.cell channel).integralSample)
    (fun index : Fin parents.length =>
      16 * (firstTargets.localBound + lastTargets.localBound) * PreparedParent.cost (parents[index.val]'index.isLt))
    (fun index => (first.entry index).integral_difference_le (last.entry index) channel)
  rewrite [← integralSample_eq_sumFin covered first chain channel,
    ← integralSample_eq_sumFin covered last chain channel, Algebra.FiniteSum.Fin.sumFin_mul_left] at bound
  exact bound.trans_eq (by unfold displacementCost; ring1)

open Purelib.Approximation.Rational
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)

variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}

/-- The literal original closed centered path, retained unchanged at every finite programme request. -/
@[expose] def constantCycle {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point)) : LiftedCycleRefinement 2 :=
  ⟨fun _ => ⟨point, chain.path⟩⟩

section Numerical

variable {start finish : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish))
    {targetStart targetFinish : LiftedPoint 2} {targetPath : LiftedPath 2 targetStart targetFinish}
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build targetPath index))

/-- Read the actual selected source list from the original preparation cache at the requested stage. -/
@[expose] def model (channel : Fin 6) (index : Nat) : PathModel :=
  ⟨(sources covered (prepared index) chain).cells channel⟩

/-- The original finite path count and displacement-cost sum determine the common progressive error scale. -/
@[expose] def errorScale (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : Rational :=
  32 * (parents.length : Rational) * displacementCost parents

/-- The common scale computed from the original finite geometry is nonnegative. -/
theorem errorScale_nonnegative (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    0 ≤ errorScale parents :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length)))
    (displacementCost_nonnegative parents)

/-- The actual count times displacement cost lies below the retained progressive error scale. -/
private theorem cost_le_errorScale (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    (parents.length : Rational) * displacementCost parents ≤ errorScale parents := by
  have productNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
    (displacementCost_nonnegative parents)
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel : (1 : Rational) ≤ 32) productNonnegative
  calc
    _ = 1 * ((parents.length : Rational) * displacementCost parents) := by ring1
    _ ≤ 32 * ((parents.length : Rational) * displacementCost parents) := scaled
    _ = errorScale parents := by unfold errorScale; ring1

section Precision

variable (precision : Nat → Nat)
    (requested : (index : Nat) → { value : CellEndpoints.Targets chain.path (precision index) //
      value = CellEndpoints.Targets.build chain.path (precision index) })
    (preparedAt : (index : Nat) → PreparedParents covered floor (requested index).val)

/-- Read the literal supplied source list at its actual independently selected precision. -/
@[expose] def modelAtPrecision (channel : Fin 6) (index : Nat) : PathModel :=
  ⟨(sources covered (preparedAt index) chain).cells channel⟩

/-- The actual source allowance follows the programme index through its retained precision floor. -/
theorem modelAllowanceAtPrecision_le (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    (modelAtPrecision covered chain precision requested preparedAt channel index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius (errorScale parents) index := by
  have exactAllowance := aggregateAllowance_eq covered (preparedAt index) chain channel
  have scaleBound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (cost_le_errorScale parents) (requested index).val.localBound_positive.le
  calc
    _ = (parents.length : Rational) * (requested index).val.localBound * displacementCost parents := exactAllowance
    _ = ((parents.length : Rational) * displacementCost parents) * (requested index).val.localBound := by ring1
    _ ≤ errorScale parents * (requested index).val.localBound := scaleBound
    _ ≤ Geometric.Basic.quarterRadius (errorScale parents) (precision index) :=
      (requested index).val.mul_localBound_le_quarterRadius (errorScale parents) (errorScale_nonnegative parents)
    _ ≤ _ := Geometric.Basic.quarterRadius_antitone (errorScale_nonnegative parents) (precisionFloor index)

/-- Two independent actual precisions pay the earlier programme index without a monotone precision selector.

Both whole preparations and their original request caches remain distinct.
The two programme-floor witnesses bound the actual local allocations on
this SAME covered chain before the original two-cache integral estimate.
-/
theorem later_closeAtPrecision (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq
      ((modelAtPrecision covered chain precision requested preparedAt channel later).integralSample -
        (modelAtPrecision covered chain precision requested preparedAt channel earlier).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale parents) earlier := by
  let originalTargets := CellEndpoints.Targets.build chain.path earlier
  let firstTargets := (requested earlier).val
  let lastTargets := (requested later).val
  have firstOrder : firstTargets.localBound ≤ originalTargets.localBound :=
    originalTargets.localBound_antitone firstTargets (precisionFloor earlier)
  have lastOrder : lastTargets.localBound ≤ originalTargets.localBound :=
    originalTargets.localBound_antitone lastTargets (order.trans (precisionFloor later))
  have localSum : lastTargets.localBound + firstTargets.localBound ≤ 2 * originalTargets.localBound :=
    (Order.Arithmetic.add_le_add_direct lastOrder firstOrder).trans_eq (by ring1)
  have geometryNonnegative : 0 ≤ (parents.length : Rational) * displacementCost parents :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
      (displacementCost_nonnegative parents)
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localSum (by decide +kernel : (0 : Rational) ≤ 16))
    geometryNonnegative
  have originalBound := integral_difference_le covered
    (preparedAt later) (preparedAt earlier) chain channel
  calc
    _ ≤ 16 * (lastTargets.localBound + firstTargets.localBound) *
        (parents.length : Rational) * displacementCost parents := originalBound
    _ = (16 * (lastTargets.localBound + firstTargets.localBound)) *
        ((parents.length : Rational) * displacementCost parents) := by ring1
    _ ≤ (16 * (2 * originalTargets.localBound)) *
        ((parents.length : Rational) * displacementCost parents) := scaled
    _ = errorScale parents * originalTargets.localBound := by unfold errorScale; ring1
    _ ≤ _ := originalTargets.mul_localBound_le_quarterRadius
      (errorScale parents) (errorScale_nonnegative parents)

/-- The actual model at programme index zero and original finite geometry determine the common sample-center bound. -/
@[expose] def centerBoundAtPrecision (channel : Fin 6) : Rational :=
  2 * (Norm.Basic.normSq
    (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample + errorScale parents)

/-- The actual sample at programme index zero and geometric scale are both nonnegative. -/
theorem centerBoundAtPrecision_nonnegative (channel : Fin 6) :
    0 ≤ centerBoundAtPrecision covered chain precision requested preparedAt channel := by
  have terms := Order.Arithmetic.add_le_add_direct
    (Norm.Basic.normSq_nonneg
      (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample)
    (errorScale_nonnegative parents)
  rewrite [Field.zero_add] at terms
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2) terms

/-- Every actual selected-precision sample lies in the bound computed from that same family's zero model. -/
theorem sample_boundedAtPrecision (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    Norm.Basic.normSq
      (modelAtPrecision covered chain precision requested preparedAt channel index).integralSample ≤
        centerBoundAtPrecision covered chain precision requested preparedAt channel := by
  have movement := (later_closeAtPrecision covered chain precision requested preparedAt precisionFloor channel
    (Nat.zero_le index)).trans
      (Geometric.Basic.quarterRadius_le_scale (errorScale_nonnegative parents) 0)
  have decomposition : (modelAtPrecision covered chain precision requested preparedAt channel index).integralSample =
      ((modelAtPrecision covered chain precision requested preparedAt channel index).integralSample -
        (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample) +
          (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample := by ring1
  have triangle := Norm.Bounds.normSq_add_le_two
    ((modelAtPrecision covered chain precision requested preparedAt channel index).integralSample -
      (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample)
    (modelAtPrecision covered chain precision requested preparedAt channel 0).integralSample
  rewrite [← decomposition] at triangle
  exact (triangle.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct movement (Order.Basic.le_refl _))
    (by decide +kernel : (0 : Rational) ≤ 2))).trans_eq (by unfold centerBoundAtPrecision; ring1)

/-- Construct one progressive programme from the actual request and preparation families at their paid precisions.

The original geometry, request factories, source caches, and model lists are
retained. Each numerical sample invokes its supplied preparation rule at
that programme index. Independent calls are not asserted to be memoized.
-/
def programAtPrecision (precisionFloor : ∀ index, index ≤ precision index) (channel : Fin 6) :
    RefinementProgram where
  model := modelAtPrecision covered chain precision requested preparedAt channel
  errorScale := errorScale parents
  errorScale_nonneg := errorScale_nonnegative parents
  modelAllowance_le :=
    modelAllowanceAtPrecision_le covered chain precision requested preparedAt precisionFloor channel
  later_close := by
    intro earlier later order
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact later_closeAtPrecision covered chain precision requested preparedAt precisionFloor channel order
  centerBound := centerBoundAtPrecision covered chain precision requested preparedAt channel
  centerBound_nonneg := centerBoundAtPrecision_nonnegative covered chain precision requested preparedAt channel
  sample_bounded := by
    intro index
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact sample_boundedAtPrecision covered chain precision requested preparedAt precisionFloor channel index

/-- The selected-precision programme retains the literal supplied original source model. -/
theorem programAtPrecision_model (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    (programAtPrecision covered chain precision requested preparedAt precisionFloor channel).model index =
      modelAtPrecision covered chain precision requested preparedAt channel index := by
  unfold programAtPrecision
  rfl

end Precision

/-- The actual retained source model's aggregate allowance obeys the original finite geometric schedule. -/
theorem modelAllowance_le (channel : Fin 6) (index : Nat) :
    (model covered chain prepared channel index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius (errorScale parents) index := by
  have exactAllowance := aggregateAllowance_eq covered (prepared index) chain channel
  change (model covered chain prepared channel index).aggregateAllowance = _ at exactAllowance
  have scaleBound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (cost_le_errorScale parents) (CellEndpoints.Targets.build targetPath index).localBound_positive.le
  calc
    _ = (parents.length : Rational) * (CellEndpoints.Targets.build targetPath index).localBound *
        displacementCost parents := exactAllowance
    _ = ((parents.length : Rational) * displacementCost parents) *
        (CellEndpoints.Targets.build targetPath index).localBound := by ring1
    _ ≤ errorScale parents * (CellEndpoints.Targets.build targetPath index).localBound := scaleBound
    _ ≤ _ := (CellEndpoints.Targets.build targetPath index).mul_localBound_le_quarterRadius
      (errorScale parents) (errorScale_nonnegative parents)

/-- Actual later source samples on the identical finite geometry obey the earlier request's geometric bound.

Both supplied banks retain their own original model floors, target paths
and actual queries at the same physical affine points. Each target path
pays its own local allocation. The original count and separate displacement
costs give the same geometric bound; no target-path identity is required.
The original numerical programme specializes this law to its own family.
-/
theorem later_close {earlierFloor laterFloor earlier later : Nat}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    (first : PreparedParents covered earlierFloor (CellEndpoints.Targets.build firstPath earlier))
    (last : PreparedParents covered laterFloor (CellEndpoints.Targets.build lastPath later))
    (channel : Fin 6) (order : earlier ≤ later) :
    Norm.Basic.normSq ((PathModel.mk ((sources covered last chain).cells channel)).integralSample -
      (PathModel.mk ((sources covered first chain).cells channel)).integralSample) ≤
        Geometric.Basic.quarterRadius (errorScale parents) earlier := by
  let firstTargets := CellEndpoints.Targets.build firstPath earlier
  let lastTargets := CellEndpoints.Targets.build lastPath later
  have localOrder := lastTargets.localBound_le_quarterRadius.trans
    (Geometric.Basic.quarterRadius_antitone (by decide +kernel : (0 : Rational) ≤ 1) order)
  have localSum : lastTargets.localBound + firstTargets.localBound ≤
      2 * Geometric.Basic.quarterRadius 1 earlier :=
    (Order.Arithmetic.add_le_add_direct localOrder firstTargets.localBound_le_quarterRadius).trans_eq
      (by ring1)
  have geometryNonnegative : 0 ≤ (parents.length : Rational) * displacementCost parents :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
      (displacementCost_nonnegative parents)
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localSum (by decide +kernel : (0 : Rational) ≤ 16))
    geometryNonnegative
  have originalBound := integral_difference_le covered last first chain channel
  change Norm.Basic.normSq ((PathModel.mk ((sources covered last chain).cells channel)).integralSample -
    (PathModel.mk ((sources covered first chain).cells channel)).integralSample) ≤
    16 * (lastTargets.localBound + firstTargets.localBound) *
      (parents.length : Rational) * displacementCost parents at originalBound
  calc
    _ ≤ 16 * (lastTargets.localBound + firstTargets.localBound) *
        (parents.length : Rational) * displacementCost parents := originalBound
    _ = (16 * (lastTargets.localBound + firstTargets.localBound)) *
        ((parents.length : Rational) * displacementCost parents) := by ring1
    _ ≤ (16 * (2 * Geometric.Basic.quarterRadius 1 earlier)) *
        ((parents.length : Rational) * displacementCost parents) := scaled
    _ = Geometric.Basic.quarterRadius (errorScale parents) earlier := by
      unfold errorScale
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- The original stage-zero sample and computed progressive scale determine a common sample-center bound. -/
@[expose] def centerBound (channel : Fin 6) : Rational :=
  2 * (Norm.Basic.normSq (model covered chain prepared channel 0).integralSample + errorScale parents)

/-- The sample-center bound retains two nonnegative original terms. -/
theorem centerBound_nonnegative (channel : Fin 6) : 0 ≤ centerBound covered chain prepared channel := by
  have terms := Order.Arithmetic.add_le_add_direct
    (Norm.Basic.normSq_nonneg (model covered chain prepared channel 0).integralSample)
    (errorScale_nonnegative parents)
  rewrite [Field.zero_add] at terms
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2) terms

/-- Every original source-programme sample lies in the common ball determined by its actual stage-zero sample. -/
theorem sample_bounded (channel : Fin 6) (index : Nat) :
    Norm.Basic.normSq (model covered chain prepared channel index).integralSample ≤
      centerBound covered chain prepared channel := by
  have movement := (later_close covered chain (prepared 0) (prepared index) channel (Nat.zero_le index)).trans
    (Geometric.Basic.quarterRadius_le_scale (errorScale_nonnegative parents) 0)
  have decomposition : (model covered chain prepared channel index).integralSample =
      ((model covered chain prepared channel index).integralSample -
        (model covered chain prepared channel 0).integralSample) +
          (model covered chain prepared channel 0).integralSample := by ring1
  have triangle := Norm.Bounds.normSq_add_le_two
    ((model covered chain prepared channel index).integralSample -
      (model covered chain prepared channel 0).integralSample)
    (model covered chain prepared channel 0).integralSample
  rewrite [← decomposition] at triangle
  exact (triangle.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct movement (Order.Basic.le_refl _))
    (by decide +kernel : (0 : Rational) ≤ 2))).trans_eq (by unfold centerBound; ring1)

/-- Construct the original progressive integration programme from the actual fixed-spine source preparations.

The model at each request is its literal original selected source-cell list.
Its supplied target path may allocate one larger retained global source
family; the physical centered chain and its endpoints remain unchanged.
All schedule, comparison and sample-center bounds are derived internally from
the original finite geometry, count-paid allocations and original queries.
No desired period inequality or synthetic integral sample is an input.
-/
def program (channel : Fin 6) : RefinementProgram where
  model := model covered chain prepared channel
  errorScale := errorScale parents
  errorScale_nonneg := errorScale_nonnegative parents
  modelAllowance_le := modelAllowance_le covered chain prepared channel
  later_close := by
    intro earlier later order
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact later_close covered chain (prepared earlier) (prepared later) channel order
  centerBound := centerBound covered chain prepared channel
  centerBound_nonneg := centerBound_nonnegative covered chain prepared channel
  sample_bounded := by
    intro index
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact sample_bounded covered chain prepared channel index

/-- The progressive programme retains the exact original requested source model. -/
theorem program_model (channel : Fin 6) (index : Nat) :
    (program covered chain prepared channel).model index = model covered chain prepared channel index := by rfl

/-- The original programme retains the scale computed from these same actual parent displacements. -/
theorem program_errorScale (channel : Fin 6) :
    (program covered chain prepared channel).errorScale = errorScale parents := by rfl

end Numerical

variable {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))

section PrecisionCertificates

variable (precision : Nat → Nat)
    (requested : (index : Nat) → { value : CellEndpoints.Targets chain.path (precision index) //
      value = CellEndpoints.Targets.build chain.path (precision index) })
    (preparedAt : (index : Nat) → PreparedParents covered floor (requested index).val)

/-- Certify the six actual fixed-parameter integrands on the SAME original cycle at their selected precisions.

The existing certify traversal consumes each supplied preparation's stored
queries. No source preparation, model or endpoint observation is produced
by this wrapper, and no derivative or primitive admission is inferred.
-/
def certifiedAtPrecision (precisionFloor : ∀ index, index ≤ precision index) (channel : Fin 6) :
    CertifiedPeriodProgram (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (constantCycle chain) where
  integral := programAtPrecision covered chain precision requested preparedAt precisionFloor channel
  certificates := by
    intro index
    rewrite [programAtPrecision_model]
    exact (certify frame covered (preparedAt index) chain).channel channel

/-- The selected-precision certificate retains its identical whole progressive programme. -/
theorem certifiedAtPrecision_integral (precisionFloor : ∀ index, index ≤ precision index) (channel : Fin 6) :
    (certifiedAtPrecision covered chain precision requested preparedAt precisionFloor channel).integral =
      programAtPrecision covered chain precision requested preparedAt precisionFloor channel := by
  unfold certifiedAtPrecision
  rfl

/-- The selected-precision certificate uses the original supplied source model at this actual programme index. -/
theorem certifiedAtPrecision_model (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    ((certifiedAtPrecision covered chain precision requested preparedAt precisionFloor channel).integral.model index) =
      PathModel.mk ((sources covered (preparedAt index) chain).cells channel) := by
  unfold certifiedAtPrecision programAtPrecision modelAtPrecision
  rfl

/-- Each selected-precision cell list is read from the SAME original supplied preparation. -/
theorem certifiedAtPrecision_cells (precisionFloor : ∀ index, index ≤ precision index)
    (channel : Fin 6) (index : Nat) :
    ((certifiedAtPrecision covered chain precision requested preparedAt precisionFloor channel).integral.model
      index).cells =
      (sources covered (preparedAt index) chain).cells channel := by
  unfold certifiedAtPrecision programAtPrecision modelAtPrecision
  rfl

end PrecisionCertificates

/-- Certify the actual fixed-parameter differential on the original unchanged lifted cycle at every request.

The programme and all uniform certificates consume the same retained source
preparation family. Each observation callback retains its own original query;
there is no execution-sharing assertion across independent programme calls.
-/
def certified (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (constantCycle chain) where
  integral := program covered chain prepared channel
  certificates := by
    intro index
    rewrite [program_model]
    exact (certify frame covered (prepared index) chain).channel channel

/-- The certified owner retains the identical whole progressive programme and its original preparation callback. -/
theorem certified_integral
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    (prepared : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      covered floor (CellEndpoints.Targets.build chain.path index)) (channel : Fin 6) :
    (certified covered chain prepared channel).integral = program covered chain prepared channel := (rfl)

/-- The certified programme uses the literal selected source list at the original request. -/
theorem certified_cells (channel : Fin 6) (index : Nat) :
    ((certified covered chain prepared channel).integral.model index).cells =
      (sources covered (prepared index) chain).cells channel := by rfl

/-- Construct a genuine differential programme by executing the original count-paid source preparation at each request.

The geometric parent list and original covered patches remain constant.
Every requested source model comes from prepareCovered on that same path;
all six bounds and the stage-zero sample bound are derived by certified.
Independent programme callbacks are independent executions, without a
cross-callback or cross-channel memoization claim.
-/
def fromCovered (requestFloor : Nat) (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (constantCycle chain) :=
  certified covered chain
    (fun index => prepareCovered covered requestFloor (CellEndpoints.Targets.build chain.path index)) channel

/-- The programme constructed from the original cover retains each original count-paid source-cell list literally. -/
theorem fromCovered_cells (requestFloor : Nat) (channel : Fin 6) (index : Nat) :
    ((fromCovered covered chain requestFloor channel).integral.model index).cells =
      (sources covered (prepareCovered covered requestFloor (CellEndpoints.Targets.build chain.path index)) chain).cells
        channel := by rfl

section CommonPayments

open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Nat.List

variable {commonCount : Nat}
    (common : ContinuedNeighborhood (Paths.polynomial parameter) commonCount)
    (pairCover : CoveredParents count parents) (current : Nat) (target : Rational)

/-- Six original finite parent products retain each actual primitive-pair budget and its selected payment.

Each channel retains the same ordered parent occurrences and original cover.
The scaled numerator is fixed by its actual original form. This exact view
uses only the original dependent vector, dependent product, budget and
Selection owners; it adds no alternate primitive or request certificate.
-/
@[expose] def PairEntries : Type 1 :=
  DependentVector (fun channel : Fin 6 => DependentProduct parents (fun index =>
    Σ budget : PrimitivePairBudget ((pairCover.entry index).1.neighborhood count) common
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (PreparedParent.startPoint (parents[index.val]'index.isLt)).coordinate
      (PreparedParent.finishPoint (parents[index.val]'index.isLt)).coordinate
      (Specification.Table.forms parameter channel).denominatorPairs,
    Search.Selection budget.scale current target))

/-- Retain all actual pair entries, their six computed stage maxima and the one global model floor.

The maxima are calculated from the stored budget selections, never from
new selections or source requests. The existing finite list maximum and
dependent-vector maximum retain the exact computed floor, including an
empty parent list. Source/model acquisition is a later operation.
-/
@[expose] def PairSelections : Type 1 :=
  Σ entries : PairEntries common pairCover current target,
  Σ maxima : {actual : DependentVector (fun _ : Fin 6 => Nat) //
    actual = DependentVector.ofFn (fun channel => Maximum.listMaximum
      (DependentProduct.mapToList parents (entries.get channel) (fun _ selected => selected.2.stage)))},
  {actual : Nat // actual = maxima.val.maximum (fun _ stage => stage)}

/-- Build each original pair budget and selection once, then compute one retained global floor.

Each scaled numerator is computed outside its actual parent-entry callback.
The six parent products and six scalar maxima are eager stored banks. No
Point, root, inverse model, source Request or programme is acquired here.
-/
def pairSelections (positive : 0 < target) : PairSelections common pairCover current target :=
  let entries : PairEntries common pairCover current target := DependentVector.ofFn (fun channel =>
    let form := Specification.Table.forms parameter channel
    let numerator := form.numerator.scale form.scale
    DependentProduct.ofFn parents (fun index =>
      let parent := parents[index.val]'index.isLt
      let patch := (pairCover.entry index).1.neighborhood count
      let budget := PrimitivePairBudget.build patch common numerator
        (PreparedParent.startPoint parent).coordinate (PreparedParent.finishPoint parent).coordinate
        form.denominatorPairs
      ⟨budget, budget.choose current target positive⟩))
  let maxima := DependentVector.ofFn (fun channel => Maximum.listMaximum
    (DependentProduct.mapToList parents (entries.get channel) (fun _ selected => selected.2.stage)))
  let floor := maxima.maximum (fun _ stage => stage)
  ⟨entries, ⟨maxima, rfl⟩, ⟨floor, rfl⟩⟩

namespace PairSelections

variable {common pairCover current target}

/-- Read the identical stored channel/parent pair and its original finite payment. -/
@[expose] def entry (selected : PairSelections common pairCover current target)
    (channel : Fin 6) (index : Fin parents.length) :=
  DependentProduct.get parents (selected.1.get channel) index

/-- Read the one computed floor retained with these exact original pair selections. -/
@[expose] def modelFloor (selected : PairSelections common pairCover current target) : Nat := selected.2.2.val

/-- Every actual retained channel/parent payment is covered by the same computed global floor.

The proof reads the same bounded parent occurrence and original stored
Selection. It uses the original finite-list and vector maximum laws;
no source/model selection or cached pair is reconstructed.
-/
theorem stage_le (selected : PairSelections common pairCover current target)
    (channel : Fin 6) (index : Fin parents.length) :
    (selected.entry channel index).2.stage ≤ selected.modelFloor := by
  let row := selected.1.get channel
  let weights := DependentProduct.mapToList parents row (fun _ paid => paid.2.stage)
  have readback := DependentProduct.get_mapToList parents row (fun _ paid => paid.2.stage) index
  have member : (selected.entry channel index).2.stage ∈ weights := by
    have sameLength : weights.length = parents.length :=
      DependentProduct.length_mapToList parents row (fun _ paid => paid.2.stage)
    have bounded : index.val < weights.length :=
      Eq.mpr (congrArg (fun size => index.val < size) sameLength) index.isLt
    have actual : weights[index.val]'bounded ∈ weights := _root_.List.getElem_mem bounded
    exact readback ▸ actual
  have below := Maximum.member_le_listMaximum weights _ member
  have maximum_eq : (selected.2.1.val.get channel) = Maximum.listMaximum weights := by
    have same := congrArg (fun values => values.get channel) selected.2.1.property
    exact same.trans (DependentVector.ofFn_get _ channel)
  have global := selected.2.1.val.get_le_maximum (fun _ stage => stage) channel
  have floor_eq : selected.modelFloor = selected.2.1.val.maximum (fun _ stage => stage) := selected.2.2.property
  exact (below.trans_eq maximum_eq.symm).trans (global.trans_eq floor_eq.symm)

end PairSelections

end CommonPayments

section AppendProgrammes

open Purelib.Integration.CertifiedProgram
open Purelib.Riemann.Integration.PreparedCoveredParentLists.CoveredParents (append)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The original global source sample is close to the same two retained local source samples.

The global product is split at its original cover boundary. Both slices
retain its complete original entries, source floor and global allocation.
The two supplied local banks keep their own paths, floors and allocations;
the same physical parents determine all three oriented samples.
-/
private theorem append_model_difference_le
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    {wholeStart wholeFinish firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (wholeChain : CenteredPathChain (first ++ last) (start := wholeStart) (finish := wholeFinish))
    (firstChain : CenteredPathChain first (start := firstStart) (finish := firstFinish))
    (lastChain : CenteredPathChain last (start := lastStart) (finish := lastFinish))
    {wholeAllocationStart wholeAllocationFinish firstAllocationStart firstAllocationFinish
      lastAllocationStart lastAllocationFinish : LiftedPoint 2}
    {wholeAllocation : LiftedPath 2 wholeAllocationStart wholeAllocationFinish}
    {firstAllocation : LiftedPath 2 firstAllocationStart firstAllocationFinish}
    {lastAllocation : LiftedPath 2 lastAllocationStart lastAllocationFinish}
    {wholeFloor firstFloor lastFloor stage : Nat}
    (whole : PreparedParents (firstCover.append lastCover)
      wholeFloor (CellEndpoints.Targets.build wholeAllocation stage))
    (earlier : PreparedParents firstCover firstFloor (CellEndpoints.Targets.build firstAllocation stage))
    (later : PreparedParents lastCover lastFloor (CellEndpoints.Targets.build lastAllocation stage))
    (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources (firstCover.append lastCover)
          whole wholeChain).cells channel)).integralSample -
        ((PathModel.mk ((sources firstCover earlier firstChain).cells channel)).integralSample +
          (PathModel.mk ((sources lastCover later lastChain).cells channel)).integralSample)) ≤
      Geometric.Basic.quarterRadius (2 * (errorScale first + errorScale last)) stage := by
  let divided := split firstCover lastCover whole
  have firstBound := later_close firstCover firstChain earlier divided.1 channel (Nat.le_refl stage)
  have lastBound := later_close lastCover lastChain later divided.2 channel (Nat.le_refl stage)
  have sampled := split_integralSample firstCover lastCover wholeChain firstChain lastChain whole channel
  rewrite [sampled]
  have difference :
      ((PathModel.mk ((sources firstCover divided.1 firstChain).cells channel)).integralSample +
        (PathModel.mk ((sources lastCover divided.2 lastChain).cells channel)).integralSample) -
      ((PathModel.mk ((sources firstCover earlier firstChain).cells channel)).integralSample +
        (PathModel.mk ((sources lastCover later lastChain).cells channel)).integralSample) =
      ((PathModel.mk ((sources firstCover divided.1 firstChain).cells channel)).integralSample -
        (PathModel.mk ((sources firstCover earlier firstChain).cells channel)).integralSample) +
      ((PathModel.mk ((sources lastCover divided.2 lastChain).cells channel)).integralSample -
        (PathModel.mk ((sources lastCover later lastChain).cells channel)).integralSample) := by ring1
  rewrite [difference]
  exact ((Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct firstBound lastBound) (by decide +kernel))).trans_eq (by
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1)

/-- The original globally allocated source programme realizes the sum of its two original physical parent programmes.

The three complete original programmes and their supplied preparation
families remain retained inputs, with exact whole factory equations.
Covering patches, centered chains, source/model floors and count allocations
remain distinct. No programme, source family or stage-zero model is rebuilt.
The original global product split
and source comparison prove the numerical bridge internally. This asserts
operational addition of oriented samples, not equality of the three paths,
their endpoint owners, executions or cycle certificates.
-/
def append_outputEquivalent
    {first last : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (firstCover : CoveredParents count first) (lastCover : CoveredParents count last)
    {wholeStart wholeFinish firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    (wholeChain : CenteredPathChain (first ++ last) (start := wholeStart) (finish := wholeFinish))
    (firstChain : CenteredPathChain first (start := firstStart) (finish := firstFinish))
    (lastChain : CenteredPathChain last (start := lastStart) (finish := lastFinish))
    {wholeAllocationStart wholeAllocationFinish firstAllocationStart firstAllocationFinish
      lastAllocationStart lastAllocationFinish : LiftedPoint 2}
    {wholeAllocation : LiftedPath 2 wholeAllocationStart wholeAllocationFinish}
    {firstAllocation : LiftedPath 2 firstAllocationStart firstAllocationFinish}
    {lastAllocation : LiftedPath 2 lastAllocationStart lastAllocationFinish}
    {wholeFloor firstFloor lastFloor : Nat}
    (wholePrepared : (index : Nat) → PreparedParents (firstCover.append lastCover)
      wholeFloor (CellEndpoints.Targets.build wholeAllocation index))
    (firstPrepared : (index : Nat) → PreparedParents firstCover firstFloor
      (CellEndpoints.Targets.build firstAllocation index))
    (lastPrepared : (index : Nat) → PreparedParents lastCover lastFloor
      (CellEndpoints.Targets.build lastAllocation index))
    (channel : Fin 6)
    (wholeProgramme : RefinementProgram)
    (wholeFactory : wholeProgramme = program (firstCover.append lastCover) wholeChain wholePrepared channel)
    (firstProgramme : RefinementProgram)
    (firstFactory : firstProgramme = program firstCover firstChain firstPrepared channel)
    (lastProgramme : RefinementProgram)
    (lastFactory : lastProgramme = program lastCover lastChain lastPrepared channel) :
    NamedEquivalent wholeProgramme.output.name (firstProgramme.output.add lastProgramme.output).name := by
  let combined := firstProgramme.certifiedView.program.add lastProgramme.certifiedView.program
  let scale : Rational := 2 * (errorScale first + errorScale last)
  have sumNonnegative : 0 ≤ errorScale first + errorScale last := by
    have actual := Order.Arithmetic.add_le_add_direct (errorScale_nonnegative first) (errorScale_nonnegative last)
    rewrite [Field.zero_add] at actual
    exact actual
  have nonnegative : 0 ≤ scale := Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Rational) ≤ 2) sumNonnegative
  have samples (index : Nat) :
      Norm.Basic.normSq ((wholeProgramme.certifiedView.program.stage index).sample -
        (combined.stage index).sample) ≤ Geometric.Basic.quarterRadius scale index := by
    rewrite [Program.add_sample]
    have wholeSample := congrArg (fun actual : RefinementProgram => (actual.model index).integralSample) wholeFactory
    have firstSample := congrArg (fun actual : RefinementProgram => (actual.model index).integralSample) firstFactory
    have lastSample := congrArg (fun actual : RefinementProgram => (actual.model index).integralSample) lastFactory
    have same := congrArg₂ (fun whole pieceSum : Canonical => Norm.Basic.normSq (whole - pieceSum)) wholeSample
      (congrArg₂ (fun earlier later : Canonical => earlier + later) firstSample lastSample)
    exact same.trans_le (append_model_difference_le firstCover lastCover wholeChain firstChain lastChain
      (wholePrepared index) (firstPrepared index) (lastPrepared index) channel)
  let compared := wholeProgramme.certifiedView.program.output_equivalent_of_samples_close combined scale
    nonnegative samples
  let summed := firstProgramme.certifiedView.program.add_output_equivalent lastProgramme.certifiedView.program
    ⟨combined, rfl⟩
  exact compared.trans summed.symm

end AppendProgrammes

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
