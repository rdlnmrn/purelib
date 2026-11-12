module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Samples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Data.Nat.Order

/-! # Fresh numerical crops on the same retained geometric Point owners

An original preparation and actual Point cache remain inputs. New Targets
execute one new original preparation and strict-crop acquisition. Both
whole preparation factories and actual sample factories derive the whole
endpoint Point identities. Only those genuine identities reindex the
old Entry acquisition and its exact domain, split and rectangular cache.
The new numerical observations and stationary payment remain distinct.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.InverseModels.BranchCellBank (FaceModels)
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

universe u

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    (points : observed.Points requested)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels rootFrames face}
    (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition models firstInside points.samples.1.val.owner)
    (domain : PeriodDomain models acquired.entry.sheet)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    {numerator : Polynomial}
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})

/-- Reindex the SAME complete domain, split and certified rectangular cache by an actual sheet identity.

Equality elimination returns the original values. The named castSheet
factory law records the intended original transport; no geometry, split,
model or numerator-bound factory executes during this operation.
-/
private def reuseDomain
    {firstSheet lastSheet : Fin 2} (equal : firstSheet = lastSheet)
    (originalDomain : PeriodDomain models firstSheet)
    (originalSplit : SegmentSplit originalDomain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (originalBounds : {value : Rectangular face.clearance originalDomain.geometry
        originalDomain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance originalDomain.geometry originalDomain.patch.cell_refines numerator})
    {Result : Type u}
    (consume :
      (view : PeriodDomain models lastSheet) → view = PeriodDomain.castSheet equal originalDomain →
      HEq view originalDomain → view.steps = originalDomain.steps →
      (viewSplit : SegmentSplit view.cuts (parent.edge.point lower) (parent.edge.point upper)) →
      HEq viewSplit originalSplit → viewSplit.count = originalSplit.count →
      (viewBounds : {value : Rectangular face.clearance view.geometry view.patch.cell_refines numerator //
        value = Rectangular.build face.clearance view.geometry view.patch.cell_refines numerator}) →
      HEq viewBounds originalBounds → Result) : Result := by
  cases equal
  exact consume originalDomain (PeriodDomain.castSheet_refl originalDomain).symm
    (HEq.refl originalDomain) rfl originalSplit (HEq.refl originalSplit) rfl originalBounds (HEq.refl originalBounds)

/-- Exact new source/crop caches together with views of the SAME original Entry, domain, split and bound cache.

The whole endpoint Point identities and separate Owner identities precede
Entry reindexing. The original-domain transport retains every cache and
factory, while the newly executed Point joins and typed payment outcome
remain in the actual fresh acquisition.
-/
abbrev PreparedConsumer (sourceFloor : Nat) {newStage : Nat}
    (newTargets : CellEndpoints.Targets original newStage)
    (newComparisonRequest newRequested : AccuracyRequest) (Result : Type u) : Type _ :=
  (next : PreparedParent patch count (Nat.max 2 sourceFloor) covered newTargets) →
  (_prepared_factory : next = prepareParent (frame := frame) patch count
    (Nat.max 2 sourceFloor) covered newTargets) →
  (_floor_two : 2 ≤ Nat.max 2 sourceFloor) →
  (_requested_floor : sourceFloor ≤ Nat.max 2 sourceFloor) →
  (vertices : ∀ first last, (operation.2 first last).vertices = [parent.edge.point upper]) →
  (actual : Crop.Acquisition (frame := frame) (basis := basis) (row := row)
    (accuracy := Primitive.localRequest newRequested 3)
    next lower upper lowerInside upperInside operation newComparisonRequest newRequested) →
  (_acquisition_factory : actual = Crop.Acquisition.build (frame := frame) (basis := basis) (row := row)
    (accuracy := Primitive.localRequest newRequested 3) next lower upper lowerInside upperInside operation
    vertices newComparisonRequest newRequested) →
  (_first_point : points.samples.1.val = actual.2.2.samples.1.val) →
  (_last_point : points.samples.2.val = actual.2.2.samples.2.val) →
  (firstOwner : points.samples.1.val.owner = actual.2.2.samples.1.val.owner) →
  (_last_owner : points.samples.2.val.owner = actual.2.2.samples.2.val.owner) →
  (viewAcquired : Entry.Acquisition models firstInside actual.2.2.samples.1.val.owner) →
  (_acquired_factory : viewAcquired = Entry.Acquisition.castPoint
    (models := models) (lastInside := firstInside) rfl (heq_of_eq firstOwner) acquired) →
  HEq viewAcquired acquired →
  (sameSheet : viewAcquired.entry.sheet = acquired.entry.sheet) →
  (view : PeriodDomain models viewAcquired.entry.sheet) →
  (_domain_factory : view = PeriodDomain.castSheet sameSheet.symm domain) →
  HEq view domain → view.steps = domain.steps →
  (viewSplit : SegmentSplit view.cuts (parent.edge.point lower) (parent.edge.point upper)) →
  HEq viewSplit split → viewSplit.count = split.count →
  (viewBounds : {value : Rectangular face.clearance view.geometry view.patch.cell_refines numerator //
    value = Rectangular.build face.clearance view.geometry view.patch.cell_refines numerator}) →
  HEq viewBounds cachedBounds → Result

/-- Execute one fresh numerical source/crop, then reuse the original geometric acquisition and full domain caches.

The old preparation factory and both actual sample factories derive each
whole Point identity through the original same-patch law. Owner equality
is a projection of that whole identity. The actual castPoint operation
consumes this evidence; only its selected sheet identity reindexes the
old domain, split and rectangular bounds. All new queries, observations,
endpoint joins and successful/unpaid payment data remain retained in actual.
No final model error, sheet choice or Owner equivalence is supplied.
-/
def withPreparation
    (preparedFactory : prepared = prepareParent (frame := frame) patch count floor covered targets)
    (sourceFloor : Nat) {newStage : Nat} (newTargets : CellEndpoints.Targets original newStage)
    (newComparisonRequest newRequested : AccuracyRequest) {Result : Type u}
    (consume : PreparedConsumer (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (cachedBounds := cachedBounds)
      sourceFloor newTargets newComparisonRequest newRequested Result) : Result :=
  let next := prepareParent (frame := frame) patch count (Nat.max 2 sourceFloor) covered newTargets
  have vertices : ∀ first last, (operation.2 first last).vertices = [parent.edge.point upper] :=
    fun first last =>
      (congrArg (fun physical : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside =>
        (physical.2 first last).vertices) cropped.physical_eq).symm.trans
          (cropped.physical_vertices first last)
  let actual := Crop.Acquisition.build (frame := frame) (basis := basis) (row := row)
    (accuracy := Primitive.localRequest newRequested 3) next lower upper lowerInside upperInside operation
    vertices newComparisonRequest newRequested
  have firstPoint : points.samples.1.val = actual.2.2.samples.1.val :=
    points.samples.1.property.trans
      ((PreparedParent.sampleAt_eq_of_factories (parameter := parameter) (frame := frame) (basis := basis)
        (parent := parent) (patch := patch) (count := count) (covered := covered)
        (firstFloor := floor) (lastFloor := Nat.max 2 sourceFloor)
        (firstPath := original) (lastPath := original) (firstStage := stage) (lastStage := newStage)
        (firstTargets := targets) (lastTargets := newTargets)
        prepared next preparedFactory rfl lower lowerInside).trans actual.2.2.samples.1.property.symm)
  have lastPoint : points.samples.2.val = actual.2.2.samples.2.val :=
    points.samples.2.property.trans
      ((PreparedParent.sampleAt_eq_of_factories (parameter := parameter) (frame := frame) (basis := basis)
        (parent := parent) (patch := patch) (count := count) (covered := covered)
        (firstFloor := floor) (lastFloor := Nat.max 2 sourceFloor)
        (firstPath := original) (lastPath := original) (firstStage := stage) (lastStage := newStage)
        (firstTargets := targets) (lastTargets := newTargets)
        prepared next preparedFactory rfl upper upperInside).trans actual.2.2.samples.2.property.symm)
  have firstOwner := congrArg
    (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count) (parent.edge.point lower) => sample.owner)
    firstPoint
  have lastOwner := congrArg
    (fun sample : ContinuedNeighborhood.Point (patch.neighborhood count) (parent.edge.point upper) => sample.owner)
    lastPoint
  let viewAcquired := Entry.Acquisition.castPoint (models := models) (lastInside := firstInside)
    rfl (heq_of_eq firstOwner) acquired
  have acquiredSame := Entry.Acquisition.castPoint_heq (models := models) (lastInside := firstInside)
    rfl (heq_of_eq firstOwner) acquired
  have sameSheet := Entry.Acquisition.castPoint_sheet (models := models) (lastInside := firstInside)
    rfl (heq_of_eq firstOwner) acquired
  reuseDomain (parameter := parameter) (frame := frame) (basis := basis) (parent := parent)
    (branches := branches) (higher := higher) (bank := bank) (rootFrames := rootFrames) (face := face)
    (models := models) (lower := lower) (upper := upper) (numerator := numerator)
    sameSheet.symm domain split cachedBounds
    (fun view domainFactory domainSame stepsSame viewSplit splitSame countSame viewBounds boundsSame =>
      consume next rfl (Data.Nat.Order.le_max_left 2 sourceFloor) (Data.Nat.Order.le_max_right 2 sourceFloor)
        vertices actual rfl firstPoint lastPoint firstOwner lastOwner viewAcquired rfl acquiredSame sameSheet
        view domainFactory domainSame stepsSame viewSplit splitSame countSame viewBounds boundsSame)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
