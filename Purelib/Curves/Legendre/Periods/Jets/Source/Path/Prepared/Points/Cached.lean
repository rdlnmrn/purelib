module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Inspection
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Refinement
public import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints.Queries
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Tactic.Ring

/-! # Actual cached endpoint Owners in a GIVEN-cover source comparison

Both QueryAt values are retained data on the exact original endpoint
roles. Their name certificates reindex the GIVEN genuine child root
chain, while their actual Owner fields explicitly feed the shared source
constructor. No coarse endpoint Owner is synthesized from a Vertex type.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.Cached

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (QueryAt)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}
variable (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
variable (sourceQuery : QueryAt parent.edge 0 parent.edge.baseInside (PreparedParent.startPoint parent).coordinate)
variable (movingQuery : QueryAt parent.edge 1 (of_decide_eq_true rfl) (PreparedParent.finishPoint parent).coordinate)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The actual query record supplies its original endpoint name equation without evaluating that endpoint again. -/
private theorem query_name {fraction : Data.Rat.Fraction.Rational} {inside : 0 ≤ fraction ∧ fraction ≤ 1}
    {point : Canonical} (query : QueryAt parent.edge fraction inside point) :
    parent.edge.rootName fraction inside = ownerName query.owner :=
  query.name_eq.symm.trans (by
    unfold ownerName Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
    rfl)

/-- Transport the SAME given original child root chain to BOTH actual cached endpoint Owner names.

Both equalities come from genuine original QueryAt certificates. Only
chain indices change; every actual signed comparison and child remains
unchanged. No canonical transported Owner is a data argument.
-/
def rootsAt {children : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (roots : RootChain children (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (of_decide_eq_true rfl))) :
    RootChain children (ownerName sourceQuery.owner) (ownerName movingQuery.owner) :=
  Riemann.Topology.PreparedBankRootChains.RootChain.castNames
    (query_name parent sourceQuery) (query_name parent movingQuery) roots

variable (safe : EndpointSafeBlock parent)
variable (inspected : CoveredParents.Inspection (count := count) safe.block.children)
variable (covered : CoveredParents.Inspection.Success inspected)
variable {oldAccuracy : AccuracyRequest}
variable (first : Primitive.Vertex (row.expression parameter) (PreparedParent.startPoint parent).coordinate
  sourceQuery.owner oldAccuracy)
variable (last : Primitive.Vertex (row.expression parameter) (PreparedParent.finishPoint parent).coordinate
  movingQuery.owner oldAccuracy)
variable (request : AccuracyRequest)
variable (queryRoots : RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
  (parent.edge.rootName 1 (of_decide_eq_true rfl)))

/-- The actual reindexed roots and SAME-source construction on GIVEN cover data and both actual endpoint Owners. -/
@[expose] def Compared :=
  Σ roots : {value : RootChain safe.block.children (ownerName sourceQuery.owner) (ownerName movingQuery.owner) //
    value = rootsAt parent sourceQuery movingQuery queryRoots},
  {value : OnInspection (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered sourceQuery.owner movingQuery.owner first last request roots.val //
    value = OnInspection.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered sourceQuery.owner movingQuery.owner first last request roots.val}

/-- Build sources/Point readings/joins once on the GIVEN cover, explicitly using both actual cached Owner values.

The caller may have selected Targets after acquiring this SAME geometry.
The old Vertices retain their actual preselected requests. No geometry,
inspection, root-query, old observation or coarse transport is executed.
-/
def compare : Compared (count := count) (floor := floor) (targets := targets)
    row parent sourceQuery movingQuery safe inspected covered first last request queryRoots :=
  let roots : { value : RootChain safe.block.children (ownerName sourceQuery.owner)
      (ownerName movingQuery.owner) // value = rootsAt parent sourceQuery movingQuery queryRoots } :=
    ⟨rootsAt parent sourceQuery movingQuery queryRoots, rfl⟩
  let completed := OnInspection.build (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row parent safe inspected covered
    sourceQuery.owner movingQuery.owner first last request roots.val
  ⟨roots, ⟨completed, rfl⟩⟩

/-- Compare the same cached endpoint Owners on the GIVEN certified six-channel preparation.

The original query-name transport, Point-reading worker and signed source
comparison remain unchanged. Only the already retained source product
replaces the original source preparation execution.
-/
def comparePrepared
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    Compared (count := count) (floor := floor) (targets := targets)
      row parent sourceQuery movingQuery safe inspected covered first last request queryRoots :=
  let roots : {value : RootChain safe.block.children (ownerName sourceQuery.owner)
      (ownerName movingQuery.owner) // value = rootsAt parent sourceQuery movingQuery queryRoots} :=
    ⟨rootsAt parent sourceQuery movingQuery queryRoots, rfl⟩
  let completed := OnInspection.fromPrepared (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row parent safe inspected covered sourceQuery.owner movingQuery.owner
    first last request roots.val shared
  have factory := OnInspection.fromPrepared_eq_build (frame := frame) (basis := basis) (count := count)
    (floor := floor) (targets := targets) (row := row) (parent := parent) (safe := safe)
    (inspected := inspected) (covered := covered) (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner)
    (first := first) (last := last) (request := request) (roots := roots.val) shared
  ⟨roots, ⟨completed, factory⟩⟩

/-- The actual supplied-source route retains the original complete cached-Owner comparison factory. -/
theorem comparePrepared_eq_compare
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    comparePrepared (count := count) (floor := floor) (targets := targets)
      row parent sourceQuery movingQuery safe inspected covered first last request queryRoots shared =
    compare (count := count) (floor := floor) (targets := targets)
      row parent sourceQuery movingQuery safe inspected covered first last request queryRoots := by
  let roots : {value : RootChain safe.block.children (ownerName sourceQuery.owner)
      (ownerName movingQuery.owner) // value = rootsAt parent sourceQuery movingQuery queryRoots} :=
    ⟨rootsAt parent sourceQuery movingQuery queryRoots, rfl⟩
  let expected := OnInspection.build (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row parent safe inspected covered sourceQuery.owner movingQuery.owner
    first last request roots.val
  let completed := OnInspection.fromPrepared (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row parent safe inspected covered sourceQuery.owner movingQuery.owner
    first last request roots.val shared
  have completedEq : completed = expected :=
    OnInspection.fromPrepared_eq_build (frame := frame) (basis := basis) (count := count)
      (floor := floor) (targets := targets) (row := row) (parent := parent) (safe := safe)
      (inspected := inspected) (covered := covered) (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner)
      (first := first) (last := last) (request := request) (roots := roots.val) shared
  have same : (⟨completed, completedEq⟩ : {value : OnInspection (count := count) (floor := floor)
      (targets := targets) row parent safe inspected covered sourceQuery.owner movingQuery.owner
      first last request roots.val // value = expected}) = ⟨expected, rfl⟩ := by
    apply Subtype.ext
    exact completedEq
  exact congrArg (fun result => (⟨roots, result⟩ : Compared (count := count) (floor := floor) (targets := targets)
    row parent sourceQuery movingQuery safe inspected covered first last request queryRoots)) same

namespace Compared

variable {row parent sourceQuery movingQuery safe inspected covered first last request queryRoots}
variable (retained : Compared (count := count) (floor := floor) (targets := targets)
  row parent sourceQuery movingQuery safe inspected covered first last request queryRoots)

/-- Read the SAME given child root chain at both actual cached endpoint Owner names. -/
@[expose] def roots : RootChain safe.block.children (ownerName sourceQuery.owner) (ownerName movingQuery.owner) :=
  retained.1.val

/-- Read all actual source, Point and join caches built on the same GIVEN geometry and endpoint Owners. -/
@[expose] def completed : OnInspection (count := count) (floor := floor) (targets := targets)
    row parent safe inspected covered sourceQuery.owner movingQuery.owner
    first last request retained.roots := retained.2.val

/-- The root transport consumes the SAME actual QueryAt name readbacks and original supplied chain. -/
theorem roots_eq : retained.roots = rootsAt parent sourceQuery movingQuery queryRoots := retained.1.property

/-- The complete source execution has its exact whole factory with BOTH actual cached Owners as explicit arguments. -/
theorem completed_eq : retained.completed = OnInspection.build
    (count := count) (floor := floor) (targets := targets) row parent safe inspected covered
    sourceQuery.owner movingQuery.owner first last request retained.roots := retained.2.property

/-- Read the SAME ordered actual child source integrals. -/
@[expose] def integrals : List Canonical := Cache.integrals row covered.val
  retained.completed.prepared retained.completed.readings

/-- Read actual signed source/join residuals, preserving all child and stationary occurrences. -/
@[expose] def errors : List Canonical := Cache.errors (frame := frame) (basis := basis) (count := count)
  (floor := floor) (targets := targets) row request covered.val retained.completed.prepared retained.completed.readings
  ⟨safe.block.chain⟩ (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner)
  first last retained.roots retained.completed.compared

/-- The actual cached endpoints and SAME child sources retain their exact oriented increment telescope. -/
theorem sum_errors : Norm.Sum.Basic.gaussianSum retained.errors = last.value - first.value -
    Norm.Sum.Basic.gaussianSum retained.integrals :=
  Cache.sum_errors (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request covered.val retained.completed.prepared retained.completed.readings ⟨safe.block.chain⟩
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots
      retained.completed.compared

/-- Read the exact actual refined child count supplied by this SAME stored block. -/
@[expose] def childCount (_retained : Compared (count := count) (floor := floor) (targets := targets)
    row parent sourceQuery movingQuery safe inspected covered first last request queryRoots) : Nat :=
  safe.block.children.length

/-- Read the internally derived local charge, keeping BOTH unchanged old request tolerances. -/
@[expose] def charge (_retained : Compared (count := count) (floor := floor) (targets := targets)
    row parent sourceQuery movingQuery safe inspected covered first last request queryRoots) :
    Data.Rat.Fraction.Rational :=
  PreparedParents.Points.charge targets request safe.block.children.length oldAccuracy oldAccuracy

/-- The SAME actual source comparison contains precisely two residuals per child and one endpoint comparison. -/
theorem errors_length : retained.errors.length = 2 * retained.childCount + 1 :=
  Cache.errors_length (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request covered.val retained.completed.prepared retained.completed.readings ⟨safe.block.chain⟩
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots
      retained.completed.compared

/-- The original old requests and actual new source/join caches pay their full finite norm sum. -/
theorem normSum_le : Norm.Sum.Basic.gaussianNormSqSum retained.errors ≤ retained.charge :=
  Cache.normSum_le (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request covered.val retained.completed.prepared retained.completed.readings ⟨safe.block.chain⟩
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots
      retained.completed.compared

/-- Both actual old request floors remain explicit in the finite derived source-integral payment. -/
theorem integral_error_le : Norm.Basic.normSq (last.value - first.value -
    Norm.Sum.Basic.gaussianSum retained.integrals) ≤
      ((2 * safe.block.children.length + 1 : Nat) : Data.Rat.Fraction.Rational) *
        PreparedParents.Points.charge targets request safe.block.children.length oldAccuracy oldAccuracy :=
  Cache.integral_error_le retained.completed.compared

end Compared

/-- The cached-Owner given-source comparison reads the SAME ordered source-model integral list. -/
theorem comparePrepared_integrals
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    (comparePrepared (count := count) (floor := floor) (targets := targets)
      row parent sourceQuery movingQuery safe inspected covered first last request queryRoots shared).integrals =
      Cache.sourceIntegrals row covered.val shared.val := by
  unfold comparePrepared Compared.integrals Compared.completed
  exact OnInspection.fromPrepared_integrals (frame := frame) (basis := basis)
    (count := count) (floor := floor) (targets := targets) shared

/-- One actual stationary comparison on GIVEN original endpoint queries and the actual zero-width root chain.

The empty inner word retains both old endpoint roles and real requested
comparison. No source cell, checked block, mesh, query, Owner or old
observation is fabricated for this branch.
-/
@[expose] def EmptyCompared (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter)
    (givenRoots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl))) :=
  Σ roots : {value : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (ownerName sourceQuery.owner) (ownerName movingQuery.owner) //
    value = rootsAt parent sourceQuery movingQuery givenRoots},
  {value : Cache (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
      (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last roots.val //
    value = Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
      (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last roots.val}

/-- Compare both actual cached old endpoint Owners once on the GIVEN empty rooted occurrence. -/
def compareEmpty (same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter)
    (givenRoots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl))) :
    EmptyCompared (count := count) (floor := floor) (targets := targets)
      row parent sourceQuery movingQuery first last request same givenRoots :=
  let roots : { value : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (ownerName sourceQuery.owner) (ownerName movingQuery.owner) //
      value = rootsAt parent sourceQuery movingQuery givenRoots } :=
    ⟨rootsAt parent sourceQuery movingQuery givenRoots, rfl⟩
  let compared := Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last roots.val
  ⟨roots, ⟨compared, rfl⟩⟩

namespace EmptyCompared

variable {row parent sourceQuery movingQuery first last request}
variable {same : parent.edge.left.parameter = parent.edge.request.endpoint.parameter}
variable {givenRoots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
  (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl))}
variable (retained : EmptyCompared (count := count) (floor := floor) (targets := targets)
  row parent sourceQuery movingQuery first last request same givenRoots)

/-- Read the SAME actual signed empty root comparison at both original cached endpoint Owners. -/
@[expose] def roots : RootChain (curve := Fibre.frameCurve frame) (differential := basis) []
    (ownerName sourceQuery.owner) (ownerName movingQuery.owner) := retained.1.val

/-- Read the real old-to-old requested comparison on the empty inner word. -/
@[expose] def compared : Cache (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots := retained.2.val

/-- The empty word retains its one actual signed stationary residual. -/
@[expose] def errors : List Canonical := Cache.errors (frame := frame) (basis := basis) (count := count)
  (floor := floor) (targets := targets) row request CoveredParents.nil PUnit.unit PUnit.unit
  (stationary_geometry parent same) (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner)
  first last retained.roots retained.compared

/-- Both actual old endpoint request targets remain in the empty-word comparison charge. -/
@[expose] def charge (_retained : EmptyCompared (count := count) (floor := floor) (targets := targets)
    row parent sourceQuery movingQuery first last request same givenRoots) : Data.Rat.Fraction.Rational :=
  junctionCharge oldAccuracy oldAccuracy request

/-- A zero-width outer role retains exactly one real endpoint comparison. -/
theorem errors_length : retained.errors.length = 1 :=
  Cache.errors_length (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots retained.compared

/-- The actual retained residual is the unchanged old endpoint increment, with no presumed reading equality. -/
theorem sum_errors : Norm.Sum.Basic.gaussianSum retained.errors = last.value - first.value := by
  have original := Cache.sum_errors (frame := frame) (basis := basis) (count := count) (floor := floor)
    (targets := targets) row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots retained.compared
  exact original.trans (by change _ - 0 = _; ring1)

/-- The SAME cached requests pay the actual stationary residual without new source or Owner acquisition. -/
theorem normSum_le : Norm.Sum.Basic.gaussianNormSqSum retained.errors ≤ retained.charge :=
  Cache.normSum_le (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request CoveredParents.nil PUnit.unit PUnit.unit (stationary_geometry parent same)
    (firstOwner := sourceQuery.owner) (lastOwner := movingQuery.owner) first last retained.roots retained.compared

end EmptyCompared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points.Cached

end
