module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Source
import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring

/-! # Actual original request primitives on the retained six-channel source bank

Whole original cover factories transport the given preparation product.
Each retained primitive is compared once with its actual value-zero model;
independent source and request stages keep their exact computed charges.
The given closed fragment word supplies its original signed gap bound.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone quarterRadius_eq_mul_pow)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets (Closed SourceAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
variable {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {point : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient point point}
variable {owner : Owner ((Paths.polynomial parameter).eval point)} {prepared : PreparedPath clearPath owner}
variable {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) point owner point
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)

namespace Geometry.Sources

variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets sourcePath stage}
variable (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
variable {target : Rational} (requests : RequestedParents count target retained.parents)
variable (sameCovered : requests.covered = retained.covered)

/-- Original request data and source bank, their whole preparation view and actual per-parent comparison factories.

The cover equality concerns the entire original patch spine, not a path,
coordinate or root identity. Both dependent preparation views remain data
with their complete original factories. No source or request is acquired.
-/
abbrev RequestComparison :=
  {value : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory ×
      Sources (count := count) (floor := floor) (targets := targets) retained ×
      RequestedParents count target retained.parents // value = (retained, sourceBank, requests)} ×
  (Σ original : {value : PreparedParents retained.covered floor targets //
      value = preparations (count := count) (floor := floor) (targets := targets) retained sourceBank},
  Σ viewed : {value : PreparedParents requests.covered floor targets //
      value = original.val.castCovered sameCovered.symm},
  {value : PreparedParents.RequestComparisons requests viewed.val //
    value = PreparedParents.compareRequests requests viewed.val})

/-- Retain the given whole source preparation, transport that same cache and compile each old primitive once. -/
def compareRequests : RequestComparison (count := count) (floor := floor) (targets := targets)
    retained sourceBank requests sameCovered :=
  let original : {value : PreparedParents retained.covered floor targets //
      value = preparations (count := count) (floor := floor) (targets := targets) retained sourceBank} :=
    ⟨preparations (count := count) (floor := floor) (targets := targets) retained sourceBank, rfl⟩
  let viewed : {value : PreparedParents requests.covered floor targets //
      value = original.val.castCovered sameCovered.symm} :=
    ⟨original.val.castCovered sameCovered.symm, rfl⟩
  let compared : {value : PreparedParents.RequestComparisons requests viewed.val //
      value = PreparedParents.compareRequests requests viewed.val} :=
    ⟨PreparedParents.compareRequests requests viewed.val, rfl⟩
  ⟨⟨(retained, sourceBank, requests), rfl⟩, original, viewed, compared⟩

namespace RequestComparison

variable {retained sourceBank requests sameCovered}
variable (kept : RequestComparison (count := count) (floor := floor) (targets := targets)
    retained sourceBank requests sameCovered)

/-- Read the complete given geometry with every original Head, owner transport and stationary outer role. -/
@[expose] def geometry : Materialized.Geometry (count := count)
    diameter positive lineage inputCenters materialized factory := kept.1.val.1

/-- Read the SAME actual six-channel numerical bank without preparing any channel again. -/
@[expose] def bank : Sources (count := count) (floor := floor) (targets := targets) retained := kept.1.val.2.1

/-- Read every original request/model cache, retaining its actual local index and target. -/
@[expose] def oldRequests : RequestedParents count target retained.parents := kept.1.val.2.2

/-- Read the SAME complete actual source preparation product before its original cover-index transport. -/
@[expose] def original : PreparedParents retained.covered floor targets := kept.2.1.val

/-- Read the SAME product under the requests' whole original patch spine. -/
@[expose] def viewed : PreparedParents requests.covered floor targets := kept.2.2.1.val

/-- Read every actual finite primitive comparison cache in original parent order. -/
@[expose] def comparisons : PreparedParents.RequestComparisons requests kept.viewed := kept.2.2.2.val

/-- The complete original geometry and both numerical inputs remain actual retained data. -/
theorem originals_eq : kept.1.val = (retained, sourceBank, requests) := kept.1.property

/-- The complete stored geometric owner remains the original input value. -/
theorem geometry_eq : kept.geometry = retained := congrArg Prod.fst kept.originals_eq

/-- The stored numerical bank remains the same complete original six-channel input. -/
theorem bank_eq : kept.bank = sourceBank := congrArg Prod.fst (congrArg Prod.snd kept.originals_eq)

/-- Every stored old request/model remains the original supplied input. -/
theorem oldRequests_eq : kept.oldRequests = requests :=
  congrArg Prod.snd (congrArg Prod.snd kept.originals_eq)

/-- The complete source product is exactly the given whole bank's original preparation projection. -/
theorem original_eq : kept.original =
    preparations (count := count) (floor := floor) (targets := targets) retained sourceBank := kept.2.1.property

/-- The request-index view is the whole original cache transport, with no preparation replay. -/
theorem viewed_eq : kept.viewed = kept.original.castCovered sameCovered.symm := kept.2.2.1.property

/-- Both dependent views retain the entire same original prepared cache heterogeneously. -/
theorem viewed_heq : HEq kept.viewed kept.original :=
  (heq_of_eq kept.viewed_eq).trans (PreparedParents.castCovered_heq kept.original sameCovered.symm)

/-- The complete comparison product is its one original compilation on these actual retained caches. -/
theorem comparisons_eq : kept.comparisons = PreparedParents.compareRequests requests kept.viewed :=
  kept.2.2.2.property

variable (childChain : CenteredPathChain retained.parents
  (start := (⟨point, sheet⟩ : LiftedPoint 2)) (finish := (⟨point, sheet⟩ : LiftedPoint 2)))

/-- The request-index source path reads exactly the SAME retained whole-bank value-zero model. -/
theorem model_eq :
    PathModel.mk ((PreparedParents.sources requests.covered kept.viewed childChain).cells 0) =
      model (count := count) (floor := floor) (targets := targets) retained sourceBank 0 := by
  have viewedSources := congrArg (fun value : PreparedParents requests.covered floor targets =>
    PreparedParents.sources requests.covered value childChain) kept.viewed_eq
  have originalSources := PreparedParents.sources_castCovered kept.original sameCovered.symm childChain
  have givenSources := congrArg (fun value : PreparedParents retained.covered floor targets =>
    PreparedParents.sources retained.covered value childChain) kept.original_eq
  exact (congrArg (fun value : Path parameter childChain.path => PathModel.mk (value.cells 0))
    (viewedSources.trans (originalSources.trans givenSources))).trans
      (model_eq_sources (count := count) (floor := floor) (targets := targets)
        retained sourceBank childChain 0).symm

/-- The exact count-weighted charge reads old inverse indices separately from the actual new source target. -/
@[expose] def bound : Rational :=
  (retained.parents.length : Rational) * PreparedParents.requestChargeSum targets.localBound kept.oldRequests

/-- The count-weighted charge reads precisely the original given request/model spine. -/
theorem bound_eq : kept.bound =
    (retained.parents.length : Rational) * PreparedParents.requestChargeSum targets.localBound requests :=
  congrArg (fun value : RequestedParents count target retained.parents =>
    (retained.parents.length : Rational) * PreparedParents.requestChargeSum targets.localBound value)
    kept.oldRequests_eq

include childChain in
/-- The original request increments and SAME actual value-zero source model obey their internally derived charge. -/
theorem accurate : Norm.Basic.normSq (gaussianSum requests.increments -
    (model (count := count) (floor := floor) (targets := targets) retained sourceBank 0).integralSample) ≤ kept.bound :=
  (Eq.mp (congrArg (fun value : PathModel => Norm.Basic.normSq
    (gaussianSum requests.increments - value.integralSample) ≤
      (retained.parents.length : Rational) * PreparedParents.requestChargeSum targets.localBound requests)
      (kept.model_eq childChain))
    (PreparedParents.request_error_le requests kept.viewed childChain)).trans_eq kept.bound_eq.symm

/-- The original certified programme reads this SAME value-zero model at its own independently selected precision.

The original old request indices stay fixed. The programme index and its
actual precision are read through the existing whole-model factory; neither
is substituted for a primitive model index or geometric subdivision depth.
-/
theorem programme_error_le
    (precision : Nat → Nat)
    (requested : (index : Nat) → {value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    (precisionFloor : ∀ index, index ≤ precision index) (index : Nat)
    (current : RequestComparison (count := count) (floor := floor) (targets := (requested index).val)
      retained (sourceBanks index) requests sameCovered) :
    Norm.Basic.normSq (gaussianSum requests.increments -
      ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor 0).integral.model
        index).integralSample) ≤ current.bound :=
  Eq.mpr (congrArg (fun value : PathModel =>
    Norm.Basic.normSq (gaussianSum requests.increments - value.integralSample) ≤ current.bound)
      (certifiedAtPrecision_model retained childChain precision requested sourceBanks precisionFloor 0 index))
    (current.accurate childChain)

include childChain in
/-- The actual controlled primitive sum and source model obey their independent source and request schedules.

The original coefficient target pays its own retained movement mass.
The source Targets pay the actual source stage separately. This grants
no smaller charge to an unchanged old request.
-/
theorem controlled_error_le {requestTarget : Rational}
    (controlled : ControlledSumRequest retained.parents count requestTarget)
    {cover : controlled.requests.covered = retained.covered}
    (compared : RequestComparison (count := count) (floor := floor) (targets := targets)
      retained sourceBank controlled.requests cover) :
    Norm.Basic.normSq (gaussianSum controlled.requests.increments -
      (model (count := count) (floor := floor) (targets := targets) retained sourceBank 0).integralSample) ≤
        quarterRadius (16 * controlled.mass) stage + 8 * requestTarget := by
  have zero : basis.exponent = 0 := by
    change basis.index.val = 0
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ basis.index.isLt)
  have original := PreparedParents.primitive_error_le
    (parameter := parameter) (frame := frame) (basis := basis) (targets := targets)
    (coefficientTarget := controlled.coefficientTarget)
    controlled.requests compared.viewed zero controlled.coefficient_accurate childChain
  have transported := Eq.mp (congrArg (fun value : PathModel => Norm.Basic.normSq
    (gaussianSum controlled.requests.increments - value.integralSample) ≤
      16 * (targets.localBound + controlled.coefficientTarget) * (retained.parents.length : Rational) *
        PreparedParents.displacementCost retained.parents) (compared.model_eq childChain)) original
  have massEq := (PreparedParents.countCost_eq_movementMass retained.parents).trans controlled.mass_eq.symm
  have scalar :
      16 * (targets.localBound + controlled.coefficientTarget) * (retained.parents.length : Rational) *
          PreparedParents.displacementCost retained.parents =
        (16 * controlled.mass) * targets.localBound + 16 * (controlled.mass * controlled.coefficientTarget) := by
    rewrite [← massEq]
    ring1
  have sourcePaid := targets.mul_localBound_le_quarterRadius (16 * controlled.mass)
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Eq.mpr (congrArg (fun mass : Rational => 0 ≤ mass) controlled.mass_eq)
        (movementMass_nonnegative retained.parents)))
  have coefficientBound : controlled.mass * controlled.coefficientTarget ≤ requestTarget / 2 :=
    Eq.mpr (congrArg (fun mass : Rational => mass * controlled.coefficientTarget ≤ requestTarget / 2)
      controlled.mass_eq) controlled.mass_mul_coefficientTarget_le
  have coefficientPaid := Arithmetic.mul_le_mul_of_nonneg_left_direct
    coefficientBound (by decide +kernel : (0 : Rational) ≤ 16)
  have coefficientScale : 16 * (requestTarget / 2) = 8 * requestTarget :=
    (show 16 * (requestTarget / 2) = 8 * ((requestTarget / 2) * 2) by ring1).trans
      (congrArg (fun value : Rational => 8 * value)
        (Data.Rat.Fraction.Field.div_mul_cancel_of_ne requestTarget (2 : Rational) (by decide +kernel)))
  exact (transported.trans_eq scalar).trans
    (Arithmetic.add_le_add_direct sourcePaid (coefficientPaid.trans_eq coefficientScale))

/-- Independent programme precision preserves the controlled request's original shrinking comparison.

Only the given precision floor is used. The old primitive indices and
target remain those of the same supplied controlled request.
-/
theorem programme_controlled_error_le
    (precision : Nat → Nat)
    (requested : (index : Nat) → {value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    (precisionFloor : ∀ index, index ≤ precision index) (index : Nat) {requestTarget : Rational}
    (controlled : ControlledSumRequest retained.parents count requestTarget)
    {cover : controlled.requests.covered = retained.covered}
    (current : RequestComparison (count := count) (floor := floor) (targets := (requested index).val)
      retained (sourceBanks index) controlled.requests cover) :
    Norm.Basic.normSq (gaussianSum controlled.requests.increments -
      ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor 0).integral.model
        index).integralSample) ≤ quarterRadius (16 * controlled.mass) index + 8 * requestTarget := by
  have raw := controlled_error_le (childChain := childChain) controlled current
  have later : quarterRadius (16 * controlled.mass) (precision index) ≤
      quarterRadius (16 * controlled.mass) index := quarterRadius_antitone
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 16)
      (Eq.mpr (congrArg (fun mass : Rational => 0 ≤ mass) controlled.mass_eq)
        (movementMass_nonnegative retained.parents))) (precisionFloor index)
  have bounded := raw.trans
    (Arithmetic.add_le_add_direct later (Data.Rat.Fraction.Order.Basic.le_refl (8 * requestTarget)))
  exact Eq.mpr (congrArg (fun value : PathModel => Norm.Basic.normSq
    (gaussianSum controlled.requests.increments - value.integralSample) ≤
      quarterRadius (16 * controlled.mass) index + 8 * requestTarget)
      (certifiedAtPrecision_model retained childChain precision requested sourceBanks precisionFloor 0 index)) bounded

/-- Geometrically requested actual primitive sums have an internally derived common-stage programme bound.

Each controlled request keeps its actual target and model indices. Its
retained mass readback and the independent source precision floor produce
the stated common scale; no sample-closeness certificate is an input.
-/
theorem scheduled_controlled_error_le
    (precision : Nat → Nat)
    (requested : (index : Nat) → {value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    (precisionFloor : ∀ index, index ≤ precision index) (requestScale : Rational) (index : Nat)
    (controlled : ControlledSumRequest retained.parents count (quarterRadius requestScale index))
    {cover : controlled.requests.covered = retained.covered}
    (current : RequestComparison (count := count) (floor := floor) (targets := (requested index).val)
      retained (sourceBanks index) controlled.requests cover) :
    Norm.Basic.normSq (gaussianSum controlled.requests.increments -
      ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor 0).integral.model
        index).integralSample) ≤ quarterRadius (16 * movementMass retained.parents + 8 * requestScale) index :=
  (programme_controlled_error_le childChain precision requested sourceBanks precisionFloor index
    controlled current).trans_eq
    (by
      rewrite [controlled.mass_eq, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
      ring1)

end RequestComparison

variable {sameCovered}

/-- The ordinary acquisition factory derives the entire same original cover and all patch admissions. -/
theorem acquiredRequests_covered (oldPositive : 0 < target)
    (requestFactory : requests = RequestedParents.acquire retained.covered target oldPositive retained.parents_proper) :
    requests.covered = retained.covered :=
  (congrArg (fun value : RequestedParents count target retained.parents => value.covered) requestFactory).trans
    (RequestedParents.acquire_covered retained.covered target oldPositive retained.parents_proper)

/-- Compare GIVEN ordinary acquired requests on the actual bank, deriving their whole cover identity internally. -/
def compareAcquiredRequests (oldPositive : 0 < target)
    (requestFactory : requests = RequestedParents.acquire retained.covered target oldPositive retained.parents_proper) :
    {value : RequestedParents count target retained.parents //
      value = RequestedParents.acquire retained.covered target oldPositive retained.parents_proper} ×
      RequestComparison (count := count) (floor := floor) (targets := targets) retained sourceBank requests
        (acquiredRequests_covered retained requests oldPositive requestFactory) :=
  let original : {value : RequestedParents count target retained.parents //
      value = RequestedParents.acquire retained.covered target oldPositive retained.parents_proper} :=
    ⟨requests, requestFactory⟩
  let compared := compareRequests retained sourceBank requests
    (acquiredRequests_covered retained requests oldPositive requestFactory)
  (original, compared)

/-- The actual controlled-sum factory derives the same cover while preserving every original request and stage. -/
theorem controlledRequests_covered {oldTarget : Rational}
    (supplied : ControlledSumRequest retained.parents count oldTarget)
    (oldPositive : 0 < oldTarget) (minimum : Nat)
    (requestFactory : supplied = ControlledSumRequest.acquire
      retained.covered retained.parents_proper oldTarget oldPositive minimum) :
    supplied.requests.covered = retained.covered :=
  (congrArg (fun value : ControlledSumRequest retained.parents count oldTarget => value.requests.covered)
    requestFactory).trans
      (ControlledSumRequest.acquire_covered retained.covered retained.parents_proper oldTarget oldPositive minimum)

/-- Consume the GIVEN controlled request used by the actual fragment constructor through the SAME comparison worker. -/
def compareControlledRequests {oldTarget : Rational} (supplied : ControlledSumRequest retained.parents count oldTarget)
    (oldPositive : 0 < oldTarget) (minimum : Nat)
    (requestFactory : supplied = ControlledSumRequest.acquire
      retained.covered retained.parents_proper oldTarget oldPositive minimum) :
    {value : ControlledSumRequest retained.parents count oldTarget //
      value = ControlledSumRequest.acquire retained.covered retained.parents_proper oldTarget oldPositive minimum} ×
      RequestComparison (count := count) (floor := floor) (targets := targets) retained sourceBank supplied.requests
        (controlledRequests_covered retained supplied oldPositive minimum requestFactory) :=
  let original : {value : ControlledSumRequest retained.parents count oldTarget //
      value = ControlledSumRequest.acquire retained.covered retained.parents_proper oldTarget oldPositive minimum} :=
    ⟨supplied, requestFactory⟩
  let compared := compareRequests retained sourceBank supplied.requests
    (controlledRequests_covered retained supplied oldPositive minimum requestFactory)
  (original, compared)

namespace RequestComparison

variable {retained sourceBank requests}

variable (childChain : CenteredPathChain retained.parents
  (start := (⟨point, sheet⟩ : LiftedPoint 2)) (finish := (⟨point, sheet⟩ : LiftedPoint 2)))
variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {base : FramedPuncturedGrid (Fibre.frameCurve frame) branches higher}
variable {rootFrames : RootFrames base.bank.grid} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank rootFrames base.faces.regulars} {numericIndex : Nat}
variable {meshPoints : List Canonical} {meshTolerance : Rational}
variable {numerics : FacePrimitiveBank basis numericIndex domains}
variable {budgets : FaceMeshBudgets basis meshPoints meshTolerance domains}
variable (shared : FaceSharedMeshes budgets numerics)
variable {splits : PrimitiveSplits axes retained.parents}
variable {fragments : RegularPrimitiveSplits (base := base) axes splits}
variable (entries : SplitSheets domains fragments requests) {root : Named}
variable (roots : RootChain retained.parents root root)
variable {included : ∀ value ∈
  PointBanks.RegularPrimitiveSplits.SheetEntries.points entries,
  value ∈ meshPoints}
variable (closed : Closed shared entries childChain roots included)
variable (attachment : SourceAttachment shared requests entries childChain roots closed)
variable (kept : RequestComparison (count := count) (floor := floor) (targets := targets)
    retained sourceBank requests sameCovered)

/-- The actual retained closed-gap sum is compared with the actual retained source model, with both errors retained.

The first error is the original own-face fragment comparison; the second
is the exact old-request/source-model charge. Both independent banks,
stages, offsets and all ordered gaps remain unchanged.
-/
theorem gaps_error_le : Norm.Basic.normSq
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) -
      (model (count := count) (floor := floor) (targets := targets) retained sourceBank 0).integralSample) ≤
    2 * (attachment.sum.bound + kept.bound) :=
  (Norm.Bounds.normSq_sub_le_via
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed))
    (gaussianSum requests.increments)
    ((model (count := count) (floor := floor) (targets := targets) retained sourceBank 0).integralSample)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct attachment.accurate (kept.accurate childChain)) (by decide +kernel))

/-- The same actual gap sum is compared with the original certified programme through its owned model readback. -/
theorem programme_gaps_error_le
    (precision : Nat → Nat)
    (requested : (index : Nat) → {value : CellEndpoints.Targets childChain.path (precision index) //
      value = CellEndpoints.Targets.build childChain.path (precision index)})
    (sourceBanks : (index : Nat) → Sources (count := count) (floor := floor)
      (original := childChain.path) (stage := precision index) (targets := (requested index).val) retained)
    (precisionFloor : ∀ index, index ≤ precision index) (index : Nat)
    (current : RequestComparison (count := count) (floor := floor) (targets := (requested index).val)
      retained (sourceBanks index) requests sameCovered) :
    Norm.Basic.normSq
      (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) -
        ((certifiedAtPrecision retained childChain precision requested sourceBanks precisionFloor 0).integral.model
          index).integralSample) ≤ 2 * (attachment.sum.bound + current.bound) :=
  Eq.mpr (congrArg (fun value : PathModel => Norm.Basic.normSq
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) - value.integralSample) ≤
      2 * (attachment.sum.bound + current.bound))
      (certifiedAtPrecision_model retained childChain precision requested sourceBanks precisionFloor 0 index))
    (gaps_error_le childChain shared entries roots closed attachment current)

/-- Both actual given comparison products and their single computed source/gap allowance.

The bound is derived internally. This cache neither evaluates the source
polynomial integral at runtime nor executes any source, word or comparison
producer a second time.
-/
abbrev GapComparison :=
  {value : SourceAttachment shared requests entries childChain roots closed ×
      RequestComparison (count := count) (floor := floor) (targets := targets)
        retained sourceBank requests sameCovered // value = (attachment, kept)} ×
  (Σ bound : {value : Rational // value = 2 * (attachment.sum.bound + kept.bound)},
  {_value : Unit // Norm.Basic.normSq
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) -
      (model (count := count) (floor := floor) (targets := targets) retained sourceBank 0).integralSample) ≤ bound.val})

/-- Bind the actual scalar allowance once, retaining both whole inputs and the derived finite integral-sample bound. -/
def compareGaps : GapComparison childChain shared entries roots closed attachment kept :=
  let bound : {value : Rational // value = 2 * (attachment.sum.bound + kept.bound)} :=
    ⟨2 * (attachment.sum.bound + kept.bound), rfl⟩
  ⟨⟨(attachment, kept), rfl⟩, bound,
    ⟨(), gaps_error_le childChain shared entries roots closed attachment kept⟩⟩

namespace GapComparison

variable {childChain shared entries roots closed attachment kept}
variable (paid : GapComparison childChain shared entries roots closed attachment kept)

/-- Read the actual once computed allowance on the two original retained comparison products. -/
@[expose] def bound : Rational := paid.2.1.val

/-- Both entire original comparison products are retained, including the same numerical and rooted word caches. -/
theorem originals_eq : paid.1.val = (attachment, kept) := paid.1.property

/-- The stored allowance is exactly the squared-norm two-error sum on the original actual charges. -/
theorem bound_eq : paid.bound = 2 * (attachment.sum.bound + kept.bound) := paid.2.1.property

/-- The stored allowance bounds the actual retained gap sum against the actual retained value-zero model. -/
theorem accurate : Norm.Basic.normSq
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) -
      (model (count := count) (floor := floor) (targets := targets)
        retained sourceBank 0).integralSample) ≤ paid.bound :=
  paid.2.2.property

/-- A target check retains the actual cache and either its derived strict payment or computed-bound insufficiency. -/
abbrev Payment (requested : Rational) :=
  {value : GapComparison childChain shared entries roots closed attachment kept × Rational //
      value = (paid, requested)} ×
  ({_value : Unit // paid.bound < requested ∧ Norm.Basic.normSq
    (gaussianSum (SplitSheets.Closed.gaps shared entries childChain roots closed) -
      (model (count := count) (floor := floor) (targets := targets)
        retained sourceBank 0).integralSample) < requested} ⊕
    {_value : Unit // ¬paid.bound < requested})

/-- Check the actual bound without upgrading any old request, mesh stage or source allocation.

An unpaid result certifies only failure of this strict bound test. It
proves neither a lower bound on the actual error nor impossibility.
-/
def pay (requested : Rational) : paid.Payment requested :=
  if admitted : paid.bound < requested then
    ⟨⟨(paid, requested), rfl⟩, Sum.inl ⟨(), admitted, paid.accurate.trans_lt admitted⟩⟩
  else ⟨⟨(paid, requested), rfl⟩, Sum.inr ⟨(), admitted⟩⟩

end GapComparison
end RequestComparison
end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized
