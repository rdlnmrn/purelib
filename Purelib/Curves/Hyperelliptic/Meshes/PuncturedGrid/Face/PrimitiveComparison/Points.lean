module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RootComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.ModelComparison
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathParentContainment
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Tactic.QuotientFreeOmega

/-! # Whole-cell signed comparison on the actual retained physical Point

A new finite covered route stays in the old model cell. Its actual ordered
patches propagate the old model's aligned sign. The retained source Point
acquisition supplies the target frame, selected forward row and exact
operational comparisons; no executable witness is extracted from Reached.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (Acquisition)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation.ClearBoxRootTransport
open Purelib.Riemann.RootContinuation.RootPathTransport
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)

universe u

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
  {models : FaceModels frames face} {point : Canonical} {patch : ContinuedNeighborhood curve.polynomial count}
  (actual : ContinuedNeighborhood.Point patch point) (insideFace : face.cell.box.Contains point)
  (acquired : Acquisition models insideFace actual.owner) {inner : Box}
  (cell : TransportedCell models.bounds (models.frame.owners acquired.entry.sheet) inner)

/-- Compare the new contained cell-route finish to the SAME supplied Point through actual retained frame selections.

The old cell route and aligned seed are retained. Their stationary seed
handoff is used only in the erased winding proof. The only new target-frame
selection classifies the already retained new covered-route finish Owner.
-/
def finishEquivalent
    (route : Route curve.polynomial inner inner.anchor point)
    (covered : CoveredTracedPath route.path cell.aligned.seed.owner) :
    NamedEquivalent (ownerName covered.traced.finishOwner) actual.certificate.value.name := by
  let row := acquired.forward.row acquired.entry.sheet
  let seedJoin := OwnerPath.join curve.polynomial inner.anchor cell.traced.finishOwner cell.aligned.seed.owner
    (RootComparison.seedEquivalent cell).symm
  let reached := cell.traced.trace.get.append (seedJoin.append covered.traced.trace.get)
  let selected := acquired.pointFrame.select covered.traced.finishOwner
  have innerInside : InBox inner route.path :=
    InBox.ofWithin route.path route.within inner.contains_anchor
  have faceInside : InBox face.cell.box route.path := InBox.mono cell.geometry.refines innerInside
  have oldWinding := ClearBoxPathWinding.Route.winding face.clearance
    (BranchIsolation.degreePositive curve) cell.route face.cell.box.contains_anchor
  have newWinding := ClearBoxPathWinding.ClearPath.rawWinding_eq_potential face.clearance
    (BranchIsolation.degreePositive curve) route.path faceInside
  have outwardWinding := ClearBoxPathWinding.Route.winding face.clearance
    (BranchIsolation.degreePositive curve) acquired.outward face.cell.box.contains_anchor
  have winding : PreparedPathWinding.ClearPath.rawWinding acquired.outward.path =
      Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial face.cell.box.anchor reached.vertices := by
    change _ = Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial face.cell.box.anchor
      (cell.traced.trace.get.append (seedJoin.append covered.traced.trace.get)).vertices
    rewrite [OwnerPath.append_winding, OwnerPath.append_winding,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original cell.traced,
      OwnerPath.join_winding,
      PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original covered.traced,
      oldWinding, newWinding, outwardWinding]
    omega0
  let reference := (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
    (face.cell.anchor_mem face.member)).toLoop
  have equivalent := TracedPath.equivalentOfOwnerPathSelections reference acquired.outward.within row.traced reached
    acquired.pointFrame row.selected selected winding
  exact equivalent.symm.trans acquired.equivalent

/-- Propagate the SAME supplied old model through the retained total cover to the actual original Point.

The initial model readback is the bank's exact pointwise cache law, not an
accuracy premise. The finite cover and actual root comparisons are given
retained results; neither route nor preparation is executed by this proof.
-/
theorem nearest_of_owned_cover
    (reference : OverlapReady curve.polynomial inner) (referenceIndex : Nat)
    (readback : ∀ value, reference.model.value.eval value = (cell.model.refine referenceIndex).value.eval value)
    (route : Route curve.polynomial inner inner.anchor point)
    (covered : CoveredTracedPath route.path cell.aligned.seed.owner)
    (basis : Differential genus) (parents : ParentCache covered basis acquired.entry.sheet)
    (insideActual : patch.box.Contains point)
    (equivalent : NamedEquivalent (ownerName covered.traced.finishOwner) actual.certificate.value.name) :
    normSq (reference.model.value.eval point - (patch.base.refine 2).value.eval point) ≤
      normSq (reference.model.value.eval point + (patch.base.refine 2).value.eval point) := by
  let site := ObservationNeighborhood.ofPoint curve.polynomial 0 inner.anchor cell.traced.finishOwner.parameterNonzero
  let initialPatch := ContinuedNeighborhood.ofAligned site cell.aligned
  let initial : ContinuedNeighborhood.Point initialPatch inner.anchor :=
    ContinuedNeighborhood.Point.ofOwner cell.aligned.seed.owner (Box.refines_refl _)
  have oldNear := cell.anchor_nearest initial initialPatch.center_inside
    (NamedEquivalent.refl (ownerName cell.aligned.seed.owner)) referenceIndex 2
  have initialNear : normSq (reference.model.value.eval inner.anchor -
      (initialPatch.base.refine 2).value.eval inner.anchor) ≤
      normSq (reference.model.value.eval inner.anchor + (initialPatch.base.refine 2).value.eval inner.anchor) := by
    have scalar : normSq ((cell.model.refine referenceIndex).value.eval inner.anchor -
        (initialPatch.base.refine 2).value.eval inner.anchor) ≤
        normSq ((cell.model.refine referenceIndex).value.eval inner.anchor +
          (initialPatch.base.refine 2).value.eval inner.anchor) := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using oldNear
    exact Eq.mpr (congrArg (fun value : Canonical =>
      normSq (value - (initialPatch.base.refine 2).value.eval inner.anchor) ≤
        normSq (value + (initialPatch.base.refine 2).value.eval inner.anchor)) (readback inner.anchor)) scalar
  let originalRoots := PreparedBankRootChains.preparedPathRootChain curve basis acquired.entry.sheet
    covered.traced.prepared
  let roots := PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm originalRoots
  have outgoing := NamedEquivalent.transport
    (congrArg (fun owner => ownerName owner) covered.traced.finishOwner_eq) rfl equivalent
  obtain ⟨chain⟩ := parents.chain
  exact UniformPreparedMesh.CoveredParents.nearest_of_cover reference parents.covered chain roots
    (fun parent member => PreparedPathParentContainment.ParentCache.endpoints_within parents parent member)
    initial initialPatch.center_inside inner.contains_anchor initialNear
    (NamedEquivalent.refl (ownerName cell.aligned.seed.owner)) actual insideActual outgoing

/-- Construct a finite owner-preserving comparison on one old cell and immediately consume its actual caches.

The old reference model and original Point remain supplied values. The
restricted whole-box clearance creates a genuine two-axis route, and the
original covered-path builder computes sufficient finite primitive/root
floors internally before constructing the same parent cache and comparison.
-/
def withCellPointComparison
    (reference : OverlapReady curve.polynomial inner) (referenceIndex : Nat)
    (readback : ∀ value, reference.model.value.eval value = (cell.model.refine referenceIndex).value.eval value)
    (basis : Differential genus) (insideCell : inner.Contains point) (insideActual : patch.box.Contains point)
    {Result : Type u}
    (consume : (route : Route curve.polynomial inner inner.anchor point) →
      (covered : CoveredTracedPath route.path cell.aligned.seed.owner) →
      (parents : ParentCache covered basis acquired.entry.sheet) →
      NamedEquivalent (ownerName covered.traced.finishOwner) actual.certificate.value.name →
      (normSq (reference.model.value.eval point - (patch.base.refine 2).value.eval point) ≤
        normSq (reference.model.value.eval point + (patch.base.refine 2).value.eval point)) → Result) : Result :=
  let clearance := face.clearance.restrict cell.geometry.refines
  let route := Route.build clearance inner.anchor point inner.contains_anchor insideCell
  let covered := CoveredTracedPath.build route.path route.within cell.aligned.seed.owner
  let parents := ParentCache.build covered basis acquired.entry.sheet
  let equivalent := finishEquivalent actual insideFace acquired cell route covered
  consume route covered parents equivalent
    (nearest_of_owned_cover actual insideFace acquired cell reference referenceIndex readback route covered basis
      parents
      insideActual equivalent)

/-- Compare the actual rectangular bank cache at its literal column and row without rebuilding either original model.

The bank's own value_eq field supplies the synchronized old-model readback.
No sign bit of its independent SheetCache is erased by this operation: the
comparison concerns the exact retained unflipped transported model cache.
-/
def withRectangularPointComparison
    {columns rows : Nat} {geometry : Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
    (rectangles : Riemann.Meshes.RectangularFaceModels.RectangularPatch models.bounds
      (models.frame.owners acquired.entry.sheet) geometry)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (basis : Differential genus)
    (insideCell : (geometry.box column row).Contains point) (insideActual : patch.box.Contains point)
    {Result : Type u}
    (consume : (route : Route curve.polynomial (geometry.box column row) (geometry.box column row).anchor point) →
      (covered : CoveredTracedPath route.path (rectangles.transported.cell column row).aligned.seed.owner) →
      (parents : ParentCache covered basis acquired.entry.sheet) →
      NamedEquivalent (ownerName covered.traced.finishOwner) actual.certificate.value.name →
      (normSq ((rectangles.models.ready column row).model.value.eval point -
          (patch.base.refine 2).value.eval point) ≤
        normSq ((rectangles.models.ready column row).model.value.eval point +
          (patch.base.refine 2).value.eval point)) → Result) : Result :=
  withCellPointComparison actual insideFace acquired (rectangles.transported.cell column row)
    (rectangles.models.ready column row) 2 (rectangles.value_eq column row) basis insideCell insideActual consume

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
