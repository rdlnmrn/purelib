module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Inspection
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Certificates
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Integrals
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Fin.Two
import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # Three primitive rows on one retained physical six-channel source bank

One certified source product precedes all row observations and comparisons.
The actual DirectPathChain orders its same physical cells; six uniform
certificates and literal model lists consume those unchanged caches.
The three selected primitive-row sums are their exact six-cell algebraic
combinations, rather than an asserted identity to an independent jet.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.Cache

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- The selected relation on an abstract supplied source path has its original six-channel combination. -/
private theorem source_integral_combine {parameter : Canonical} {start finish : LiftedPoint 2}
    {original : LiftedPath 2 start finish} (row : Row) (path : Path parameter original) :
    (match row with
      | .inl coordinate => Fin.cases (PathModel.mk path.zero).integralSample
          (fun _ => (PathModel.mk path.one).integralSample) coordinate
      | .inr _ => (PathModel.mk path.scalar).integralSample) =
      Row.combine parameter row (fun channel => (PathModel.mk (path.cells channel)).integralSample) := by
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
      · cases zero
        exact path.zero_integralSample
      · cases one
        exact path.one_integralSample
  | inr _ => exact path.scalar_integralSample

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- The actual zero row samples sum to the same retained ordered physical source relation. -/
theorem sum_sourceIntegrals_zero : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    gaussianSum (sourceIntegrals (Row.connection 0) covered prepared) =
      (PathModel.mk (sources covered prepared chain).zero).integralSample
  | [], .nil, _, _, _, .nil _ => rfl
  | parent :: _, .cons _ _ covered, prepared, _, _, .cons _ chain => by
      have head := congrArg (fun cell : Cell (parameter := parameter) (PreparedParent.liftedCell parent) =>
        ((Row.connection 0).cell cell.models).integralSample) prepared.1.preparation.cell_eq
      change (prepared.1.preparation.cell.models.zero).integralSample =
        ((Row.connection 0).cell prepared.1.preparation.models).integralSample at head
      change ((Row.connection 0).cell prepared.1.preparation.models).integralSample +
          gaussianSum (sourceIntegrals (Row.connection 0) covered prepared.2) =
        (prepared.1.preparation.cell.models.zero).integralSample +
          (PathModel.mk (sources covered prepared.2 chain).zero).integralSample
      exact congrArg₂ (fun first last : Canonical => first + last) head.symm
        (sum_sourceIntegrals_zero covered prepared.2 chain)
termination_by structural _ covered _ _ _ _ => covered

/-- The actual one row samples sum to the same retained ordered physical source relation. -/
theorem sum_sourceIntegrals_one : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    gaussianSum (sourceIntegrals (Row.connection 1) covered prepared) =
      (PathModel.mk (sources covered prepared chain).one).integralSample
  | [], .nil, _, _, _, .nil _ => rfl
  | parent :: _, .cons _ _ covered, prepared, _, _, .cons _ chain => by
      have head := congrArg (fun cell : Cell (parameter := parameter) (PreparedParent.liftedCell parent) =>
        ((Row.connection 1).cell cell.models).integralSample) prepared.1.preparation.cell_eq
      change (prepared.1.preparation.cell.models.one).integralSample =
        ((Row.connection 1).cell prepared.1.preparation.models).integralSample at head
      change ((Row.connection 1).cell prepared.1.preparation.models).integralSample +
          gaussianSum (sourceIntegrals (Row.connection 1) covered prepared.2) =
        (prepared.1.preparation.cell.models.one).integralSample +
          (PathModel.mk (sources covered prepared.2 chain).one).integralSample
      exact congrArg₂ (fun first last : Canonical => first + last) head.symm
        (sum_sourceIntegrals_one covered prepared.2 chain)
termination_by structural _ covered _ _ _ _ => covered

/-- The actual scalar row samples sum to the same retained ordered physical source relation. -/
theorem sum_sourceIntegrals_scalar : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    gaussianSum (sourceIntegrals (Row.scalar) covered prepared) =
      (PathModel.mk (sources covered prepared chain).scalar).integralSample
  | [], .nil, _, _, _, .nil _ => rfl
  | parent :: _, .cons _ _ covered, prepared, _, _, .cons _ chain => by
      have head := congrArg (fun cell : Cell (parameter := parameter) (PreparedParent.liftedCell parent) =>
        ((Row.scalar).cell cell.models).integralSample) prepared.1.preparation.cell_eq
      change (prepared.1.preparation.cell.models.scalar).integralSample =
        ((Row.scalar).cell prepared.1.preparation.models).integralSample at head
      change ((Row.scalar).cell prepared.1.preparation.models).integralSample +
          gaussianSum (sourceIntegrals (Row.scalar) covered prepared.2) =
        (prepared.1.preparation.cell.models.scalar).integralSample +
          (PathModel.mk (sources covered prepared.2 chain).scalar).integralSample
      exact congrArg₂ (fun first last : Canonical => first + last) head.symm
        (sum_sourceIntegrals_scalar covered prepared.2 chain)
termination_by structural _ covered _ _ _ _ => covered

/-- The actual model-row sample list is the exact original combination of its SAME six literal source-cell lists.

The supplied centered chain proves physical ordering only. Existing local
row telescopes and source Path algebra derive the equality; all source
models and queries remain the supplied actual cache values.
-/
theorem sum_sourceIntegrals_combine (row : Row)
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    gaussianSum (sourceIntegrals row covered prepared) =
      Row.combine parameter row (fun channel =>
        (PathModel.mk (PreparedParents.cells (covered := covered) prepared channel)).integralSample) := by
  have each : ∀ channel,
      (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample =
        (PathModel.mk (PreparedParents.cells (covered := covered) prepared channel)).integralSample := fun channel =>
    congrArg (fun cells => (PathModel.mk cells).integralSample)
      (PreparedParents.cells_eq_sources channel covered prepared chain).symm
  have originalCombination := source_integral_combine row (sources covered prepared chain)
  have comparedCombination := Row.combine_congr parameter row
    (fun channel => (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample)
    (fun channel => (PathModel.mk (PreparedParents.cells (covered := covered) prepared channel)).integralSample) each
  have combination := originalCombination.trans comparedCombination
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
      · cases zero
        exact (sum_sourceIntegrals_zero covered prepared chain).trans combination
      · cases one
        exact (sum_sourceIntegrals_one covered prepared chain).trans combination
  | inr _ =>
      exact (sum_sourceIntegrals_scalar covered prepared chain).trans combination

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.Cache

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.OnInspection

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}
variable (parent : CenteredEdge (Fibre.frameCurve frame) basis) (safe : EndpointSafeBlock parent)
variable (inspected : CoveredParents.Inspection (count := count) safe.block.children)
variable (covered : CoveredParents.Inspection.Success inspected)
variable (firstOwner : Owner ((Paths.polynomial parameter).eval (PreparedParent.startPoint parent).coordinate))
variable (lastOwner : Owner ((Paths.polynomial parameter).eval (PreparedParent.finishPoint parent).coordinate))
variable {oldAccuracy : AccuracyRequest}
variable (first : (row : Row) →
  Primitive.Vertex (row.expression parameter) (PreparedParent.startPoint parent).coordinate firstOwner oldAccuracy)
variable (last : (row : Row) →
  Primitive.Vertex (row.expression parameter) (PreparedParent.finishPoint parent).coordinate lastOwner oldAccuracy)
variable (request : AccuracyRequest)
variable (roots : RootChain safe.block.children (ownerName firstOwner) (ownerName lastOwner))

/-- Three actual row comparisons retain one complete original six-channel preparation product.

The original source factory is retained before any row cache. Each row's
whole factory consumes that SAME certified value; the independent old
Vertices and all actual Point readings, endpoint joins and residuals keep
their original expression, requests and owners.
-/
@[expose] def Rows :=
  Σ _chain : {value : CenteredPathChain safe.block.children
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.finishPoint parent) //
    value = CenteredPathChain.ofDirect safe.block.chain},
  Σ prepared : {value : PreparedParents covered.val floor targets //
    value = PreparedParents.fromInspection inspected covered floor targets},
  {value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.connection 0) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 0)) (last (Row.connection 0))
      request roots //
    value = fromPrepared (count := count) (floor := floor) (targets := targets)
      (Row.connection 0) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 0)) (last (Row.connection 0))
      request roots prepared} ×
  {value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.connection 1) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 1)) (last (Row.connection 1))
      request roots //
    value = fromPrepared (count := count) (floor := floor) (targets := targets)
      (Row.connection 1) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 1)) (last (Row.connection 1))
      request roots prepared} ×
  {value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.scalar) parent safe inspected covered firstOwner lastOwner (first (Row.scalar)) (last (Row.scalar))
      request roots //
    value = fromPrepared (count := count) (floor := floor) (targets := targets)
      (Row.scalar) parent safe inspected covered firstOwner lastOwner (first (Row.scalar)) (last (Row.scalar))
      request roots prepared}

namespace Rows

/-- Construct all three row-specific observations and comparisons on the SAME supplied certified source bank. -/
def ofPrepared
    (prepared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    Rows (count := count) (floor := floor) (targets := targets)
      parent safe inspected covered firstOwner lastOwner first last request roots :=
  let chain : {value : CenteredPathChain safe.block.children
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.finishPoint parent) //
      value = CenteredPathChain.ofDirect safe.block.chain} := ⟨CenteredPathChain.ofDirect safe.block.chain, rfl⟩
  let zero := fromPrepared (count := count) (floor := floor) (targets := targets)
    (Row.connection 0) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 0)) (last (Row.connection 0))
    request roots prepared
  let one := fromPrepared (count := count) (floor := floor) (targets := targets)
    (Row.connection 1) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 1)) (last (Row.connection 1))
    request roots prepared
  let scalar := fromPrepared (count := count) (floor := floor) (targets := targets)
    (Row.scalar) parent safe inspected covered firstOwner lastOwner (first (Row.scalar)) (last (Row.scalar))
    request roots prepared
  ⟨chain, prepared, ⟨zero, rfl⟩, ⟨one, rfl⟩, ⟨scalar, rfl⟩⟩

/-- Prepare one six-channel source bank and consume it unchanged for both connection rows and the scalar row. -/
def build : Rows (count := count) (floor := floor) (targets := targets)
    parent safe inspected covered firstOwner lastOwner first last request roots :=
  let prepared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets} :=
    ⟨PreparedParents.fromInspection inspected covered floor targets, rfl⟩
  ofPrepared (count := count) (floor := floor) (targets := targets)
    parent safe inspected covered firstOwner lastOwner first last request roots prepared

variable {parent safe inspected covered firstOwner lastOwner first last request roots}
variable (retained : Rows (count := count) (floor := floor) (targets := targets)
  parent safe inspected covered firstOwner lastOwner first last request roots)

/-- Read the single retained centered representation of the SAME actual direct child block. -/
@[expose] def chain : CenteredPathChain safe.block.children
    (start := PreparedParent.startPoint parent) (finish := PreparedParent.finishPoint parent) := retained.1.val

/-- The whole retained geometric view is the original direct-to-centered conversion on that SAME actual block. -/
theorem chain_eq : retained.chain = CenteredPathChain.ofDirect safe.block.chain := retained.1.property

/-- Read the same actual full source preparation shared by all three row executions. -/
@[expose] def prepared : PreparedParents covered.val floor targets := retained.2.1.val

/-- The given-source producer forwards the SAME complete supplied preparation without source or query execution. -/
theorem ofPrepared_prepared
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    (ofPrepared (count := count) (floor := floor) (targets := targets)
      parent safe inspected covered firstOwner lastOwner first last request roots shared).prepared = shared.val := by
  unfold ofPrepared prepared
  rfl

/-- The shared source retains its original complete inspected-neighborhood preparation factory. -/
theorem prepared_eq : retained.prepared = PreparedParents.fromInspection inspected covered floor targets :=
  retained.2.1.property

/-- Read the actual zero row's Point observations and signed endpoint/source comparison caches. -/
@[expose] def zero : OnInspection (count := count) (floor := floor) (targets := targets)
    (Row.connection 0) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 0)) (last (Row.connection 0))
    request roots := retained.2.2.1.val

/-- The actual zero row consumes the SAME complete shared six-channel source product. -/
theorem zero_prepared : retained.zero.prepared = retained.prepared :=
  (congrArg (fun value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.connection 0) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 0)) (last (Row.connection 0))
      request roots => value.prepared) retained.2.2.1.property).trans
    (fromPrepared_prepared (count := count) (floor := floor) (targets := targets) retained.2.1)

/-- The actual zero row's ordered cached samples read the SAME shared source-model integrals. -/
theorem zero_integrals_eq :
    Cache.integrals (Row.connection 0) covered.val retained.zero.prepared retained.zero.readings =
      Cache.sourceIntegrals (Row.connection 0) covered.val retained.prepared :=
  (Cache.integrals_eq (Row.connection 0) covered.val retained.zero.prepared retained.zero.readings).trans
    (congrArg (Cache.sourceIntegrals (Row.connection 0) covered.val) retained.zero_prepared)

/-- Read the actual one row's Point observations and signed endpoint/source comparison caches. -/
@[expose] def one : OnInspection (count := count) (floor := floor) (targets := targets)
    (Row.connection 1) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 1)) (last (Row.connection 1))
    request roots := retained.2.2.2.1.val

/-- The actual one row consumes the SAME complete shared six-channel source product. -/
theorem one_prepared : retained.one.prepared = retained.prepared :=
  (congrArg (fun value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.connection 1) parent safe inspected covered firstOwner lastOwner
      (first (Row.connection 1)) (last (Row.connection 1))
      request roots => value.prepared) retained.2.2.2.1.property).trans
    (fromPrepared_prepared (count := count) (floor := floor) (targets := targets) retained.2.1)

/-- The actual one row's ordered cached samples read the SAME shared source-model integrals. -/
theorem one_integrals_eq :
    Cache.integrals (Row.connection 1) covered.val retained.one.prepared retained.one.readings =
      Cache.sourceIntegrals (Row.connection 1) covered.val retained.prepared :=
  (Cache.integrals_eq (Row.connection 1) covered.val retained.one.prepared retained.one.readings).trans
    (congrArg (Cache.sourceIntegrals (Row.connection 1) covered.val) retained.one_prepared)

/-- Read the actual scalar row's Point observations and signed endpoint/source comparison caches. -/
@[expose] def scalar : OnInspection (count := count) (floor := floor) (targets := targets)
    (Row.scalar) parent safe inspected covered firstOwner lastOwner (first (Row.scalar)) (last (Row.scalar))
    request roots := retained.2.2.2.2.val

/-- The actual scalar row consumes the SAME complete shared six-channel source product. -/
theorem scalar_prepared : retained.scalar.prepared = retained.prepared :=
  (congrArg (fun value : OnInspection (count := count) (floor := floor) (targets := targets)
      (Row.scalar) parent safe inspected covered firstOwner lastOwner (first (Row.scalar)) (last (Row.scalar))
      request roots => value.prepared) retained.2.2.2.2.property).trans
    (fromPrepared_prepared (count := count) (floor := floor) (targets := targets) retained.2.1)

/-- The actual scalar row's ordered cached samples read the SAME shared source-model integrals. -/
theorem scalar_integrals_eq :
    Cache.integrals (Row.scalar) covered.val retained.scalar.prepared retained.scalar.readings =
      Cache.sourceIntegrals (Row.scalar) covered.val retained.prepared :=
  (Cache.integrals_eq (Row.scalar) covered.val retained.scalar.prepared retained.scalar.readings).trans
    (congrArg (Cache.sourceIntegrals (Row.scalar) covered.val) retained.scalar_prepared)

/-- Join the unchanged actual source cells along the SAME retained child block's lifted geometry. -/
@[expose] def sources : Path parameter retained.chain.path :=
  PreparedParents.sources covered.val retained.prepared retained.chain

/-- Read one of the six literal original differential-cell lists as a polynomial integration model. -/
@[expose] def model (channel : Fin 6) : PathModel := PathModel.mk (retained.sources.cells channel)

/-- Every shared numerical model contains exactly its literal ordered retained source-cell list. -/
theorem model_cells (channel : Fin 6) : (retained.model channel).cells = retained.sources.cells channel := rfl

/-- Each actual shared model sample is the exact finite sum of its same per-occurrence original source cells. -/
theorem model_integralSample (channel : Fin 6) :
    (retained.model channel).integralSample =
      Algebra.FiniteSum.Fin.sumFin (fun index : Fin safe.block.children.length =>
        ((retained.prepared.entry index).preparation.cell.models.cell channel).integralSample) :=
  PreparedParents.integralSample_eq_sumFin covered.val retained.prepared
    retained.chain channel

/-- Certify all six actual same-cell differential models using their retained source queries and exact child chain. -/
def certificates : Certificates frame covered.val retained.prepared retained.chain :=
  PreparedParents.certify frame covered.val retained.prepared retained.chain

/-- The actual first connection-row sum is the exact combination of the SAME six-channel numerical bank. -/
theorem zero_integralSample :
    gaussianSum (Cache.integrals (Row.connection 0) covered.val retained.zero.prepared retained.zero.readings) =
      Clearance.connectionDenominator parameter * (retained.model 2).integralSample -
        (parameter * (retained.model 0).integralSample - (retained.model 1).integralSample) :=
  ((congrArg gaussianSum retained.zero_integrals_eq).trans
    (Cache.sum_sourceIntegrals_zero covered.val retained.prepared retained.chain)).trans
      retained.sources.zero_integralSample

/-- The actual second connection-row sum uses the weighted first channel of that SAME unchanged numerical bank. -/
theorem one_integralSample :
    gaussianSum (Cache.integrals (Row.connection 1) covered.val retained.one.prepared retained.one.readings) =
      Clearance.connectionDenominator parameter * (retained.model 3).integralSample -
        (parameter * (retained.model 0).integralSample - parameter * (retained.model 1).integralSample) :=
  ((congrArg gaussianSum retained.one_integrals_eq).trans
    (Cache.sum_sourceIntegrals_one covered.val retained.prepared retained.chain)).trans
      retained.sources.one_integralSample

/-- The actual scalar-row sum uses the original value, first and second channels of the SAME shared source product. -/
theorem scalar_integralSample :
    gaussianSum (Cache.integrals Row.scalar covered.val retained.scalar.prepared retained.scalar.readings) =
      4 * parameter * (1 - parameter) * (retained.model 4).integralSample +
        4 * (1 - 2 * parameter) * (retained.model 2).integralSample - (retained.model 0).integralSample :=
  ((congrArg gaussianSum retained.scalar_integrals_eq).trans
    (Cache.sum_sourceIntegrals_scalar covered.val retained.prepared
      retained.chain)).trans
      retained.sources.scalar_integralSample

end Rows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.OnInspection

end
