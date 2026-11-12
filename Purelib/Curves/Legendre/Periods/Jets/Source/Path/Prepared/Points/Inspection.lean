module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Inspection
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover

/-! # Source construction on GIVEN inspected children and actual endpoint Owners

The original safe block, successful inspection and signed root chain
are already retained inputs. Source targets may therefore be selected
after the actual geometry/count is available. The two actual old Owner
values are explicit data; every source, Point request and join consumes
those same inputs, without a computed transported-owner type as its data source.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {count floor : Nat} {targets : CellEndpoints.Targets original stage}
variable (row : Row) (parent : CenteredEdge (Fibre.frameCurve frame) basis)
variable (safe : EndpointSafeBlock parent)
variable (inspected : CoveredParents.Inspection (count := count) safe.block.children)
variable (covered : CoveredParents.Inspection.Success inspected)
variable (firstOwner : Owner ((Paths.polynomial parameter).eval (PreparedParent.startPoint parent).coordinate))
variable (lastOwner : Owner ((Paths.polynomial parameter).eval (PreparedParent.finishPoint parent).coordinate))
variable {oldAccuracy : AccuracyRequest}
variable (first : Primitive.Vertex (row.expression parameter) (PreparedParent.startPoint parent).coordinate
  firstOwner oldAccuracy)
variable (last : Primitive.Vertex (row.expression parameter) (PreparedParent.finishPoint parent).coordinate
  lastOwner oldAccuracy)
variable (request : AccuracyRequest)
variable (roots : RootChain safe.block.children (ownerName firstOwner) (ownerName lastOwner))

/-- One actual source product, Point-reading product and join cache built on the SAME inspected children and Owners.

Both endpoint Owner records and old Vertex requests remain GIVEN data.
Every new completed object retains its whole factory. Root and geometry
certificates are consumed unchanged; neither a cover, mesh, block, query,
Owner nor old observation is acquired by this source construction.
-/
@[expose] def OnInspection :=
  Σ prepared : {value : PreparedParents covered.val floor targets //
    value = PreparedParents.fromInspection inspected covered floor targets},
  Σ readings : {value : Readings row covered.val prepared.val //
    value = Readings.build row covered.val prepared.val},
  {compared : Cache (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row request covered.val prepared.val readings.val ⟨safe.block.chain⟩
      (firstOwner := firstOwner) (lastOwner := lastOwner) first last roots //
    compared = Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row request covered.val prepared.val readings.val ⟨safe.block.chain⟩
      (firstOwner := firstOwner) (lastOwner := lastOwner) first last roots}

namespace OnInspection

/-- Observe and compare one row on the SAME given certified six-channel source product.

Only the row-specific Point readings and signed comparisons are new work.
The complete original preparation and its actual factory are retained;
no source, neighborhood, endpoint Point or six-channel model is rebuilt.
-/
def fromPrepared
    (prepared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    OnInspection (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered firstOwner lastOwner first last request roots :=
  let readings := Readings.build row covered.val prepared.val
  let compared := Cache.build (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request covered.val prepared.val readings ⟨safe.block.chain⟩
    (firstOwner := firstOwner) (lastOwner := lastOwner) first last roots
  ⟨prepared, ⟨readings, rfl⟩, ⟨compared, rfl⟩⟩

/-- Prepare SAME inspected source caches once, observe their Point denotations once, and compare actual given Owners. -/
def build : OnInspection (count := count) (floor := floor) (targets := targets)
    row parent safe inspected covered firstOwner lastOwner first last request roots :=
  let prepared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets} :=
    ⟨PreparedParents.fromInspection inspected covered floor targets, rfl⟩
  fromPrepared (count := count) (floor := floor) (targets := targets)
    row parent safe inspected covered firstOwner lastOwner first last request roots prepared

variable {row parent safe inspected covered firstOwner lastOwner first last request roots}
variable (retained : OnInspection (count := count) (floor := floor) (targets := targets)
  row parent safe inspected covered firstOwner lastOwner first last request roots)

/-- Read the SAME completed six-channel source product on the actual supplied successful inspection. -/
@[expose] def prepared : PreparedParents covered.val floor targets := retained.1.val

/-- Read the actual independent Point-owned primitive requests constructed on that SAME retained source product. -/
@[expose] def readings : Readings row covered.val retained.prepared := retained.2.1.val

/-- Read the actual requested joins and child moving residuals with BOTH supplied endpoint Owners unchanged. -/
@[expose] def compared : Cache (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
    row request covered.val retained.prepared retained.readings ⟨safe.block.chain⟩
    (firstOwner := firstOwner) (lastOwner := lastOwner) first last roots := retained.2.2.val

/-- The complete source product uses the SAME inspected neighborhoods through the original given-cache constructor. -/
theorem prepared_eq : retained.prepared = PreparedParents.fromInspection inspected covered floor targets :=
  retained.1.property

/-- The shared row operation forwards the SAME complete supplied six-channel source preparation.

The original factory remains in its certified input. This projection law
requires no source execution or equality between independent requests.
-/
theorem fromPrepared_prepared
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    (fromPrepared (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered firstOwner lastOwner first last request roots shared).prepared =
        shared.val := by
  unfold fromPrepared prepared
  rfl

/-- The given-source worker has the complete original row factory from its retained whole source certificate.

Only exact source-product equality is eliminated. The given-source
operation executes neither the source factory nor the old convenience
producer to recover data; this law is an erased whole-result readback.
-/
theorem fromPrepared_eq_build
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    fromPrepared (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered firstOwner lastOwner first last request roots shared =
    build (count := count) (floor := floor) (targets := targets)
      row parent safe inspected covered firstOwner lastOwner first last request roots := by
  rcases shared with ⟨shared, factory⟩
  cases factory
  rfl

/-- The retained Point-reading product has the exact factory on that SAME actual source product. -/
theorem readings_eq : retained.readings = Readings.build row covered.val retained.prepared := retained.2.1.property

/-- The actual comparison cache consumes SAME explicit Owners, old Vertices, roots and literal source/Point products. -/
theorem compared_eq : retained.compared = Cache.build (frame := frame) (basis := basis) (count := count)
    (floor := floor) (targets := targets) row request covered.val retained.prepared retained.readings ⟨safe.block.chain⟩
    (firstOwner := firstOwner) (lastOwner := lastOwner) first last roots := retained.2.2.property

/-- The actual given-source row samples read exactly the SAME supplied source-model integrals.

Original Point-reading readbacks and the whole prepared-product identity
are composed. No Point/source factory is rerun to prove this list equality.
-/
theorem fromPrepared_integrals
    (shared : {value : PreparedParents covered.val floor targets //
      value = PreparedParents.fromInspection inspected covered floor targets}) :
    Cache.integrals row covered.val
      (fromPrepared (count := count) (floor := floor) (targets := targets)
        row parent safe inspected covered firstOwner lastOwner first last request roots shared).prepared
      (fromPrepared (count := count) (floor := floor) (targets := targets)
        row parent safe inspected covered firstOwner lastOwner first last request roots shared).readings =
      Cache.sourceIntegrals row covered.val shared.val :=
  (Cache.integrals_eq row covered.val _ _).trans
    (congrArg (Cache.sourceIntegrals row covered.val)
      (fromPrepared_prepared (count := count) (floor := floor) (targets := targets) shared))

end OnInspection

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

end
