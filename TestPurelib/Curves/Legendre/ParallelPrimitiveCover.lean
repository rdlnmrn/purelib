module
import Purelib.Data.Nat.Order
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Data.List.Membership
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Box.Intersection
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

/-! # Exact retained factories of the actual source-anchored primitive cover

The public result retains the real source-to-anchor route and terminal
owner before acquiring its finite rectangular model bank. Its six whole
factory equations remain accessible without exposing the producer body.
-/

namespace TestPurelib.Curves.Legendre.ParallelPrimitiveCover

open Purelib.Data
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box Gaussian Coordinate)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Readings
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds Mesh)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch RectangularLayout)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry (uniform dyadicSteps)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- All original cached factories remain public readbacks of one acquired cover and its actual ending Owner. -/
example {polynomial : Polynomial} {box : Box} (clearance : Clearance polynomial box)
    (proper : box.Proper) (point : Gaussian) (inside : box.Contains point)
    (source : Owner (polynomial.eval point)) :
    let acquired := RectangularPatch.acquireAt clearance proper point inside source
    acquired.1.val = ClearBoxPaths.Route.build clearance point box.anchor inside box.contains_anchor ∧
      acquired.2.1.val = TracedPath.build acquired.1.val.path acquired.1.val.within source ∧
        acquired.2.2.1.val = Bounds.build clearance ∧
          acquired.2.2.2.1.val = Mesh.build acquired.2.2.1.val ∧
            acquired.2.2.2.2.1.val = uniform box proper (dyadicSteps acquired.2.2.2.1.val.depth) ∧
              acquired.2.2.2.2.2.val = RectangularPatch.acquire
                (Eq.mp (congrArg (RectangularLayout acquired.2.2.1.val) acquired.2.2.2.2.1.property.symm)
                  (RectangularLayout.ofMesh acquired.2.2.2.1.val proper)) acquired.2.1.val.finishOwner := by
  let acquired := RectangularPatch.acquireAt clearance proper point inside source
  exact ⟨acquired.1.property, acquired.2.1.property, acquired.2.2.1.property,
    acquired.2.2.2.1.property, acquired.2.2.2.2.1.property, acquired.2.2.2.2.2.property⟩

/-- Delegating uniform location retains the complete former result at every point and grid depth. -/
example (box : Box) (proper : box.Proper) (steps : Nat) (point : Gaussian) (inside : box.Contains point) :
    RectangularUniformGeometry.locateUniform box proper steps point inside =
      (let horizontal := RectangularUniformGeometry.Axis.locate
          (RectangularUniformGeometry.Axis.uniform steps box.xLower box.xUpper proper.1) point.re
          ((RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.1).trans_le inside.1)
          (inside.2.1.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.1).symm)
       let vertical := RectangularUniformGeometry.Axis.locate
          (RectangularUniformGeometry.Axis.uniform steps box.yLower box.yUpper proper.2) point.im
          ((RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.2).trans_le inside.2.2.1)
          (inside.2.2.2.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.2).symm)
       (⟨horizontal.index, vertical.index, horizontal.inside.1, horizontal.inside.2,
          vertical.inside.1, vertical.inside.2⟩ :
          RectangularUniformGeometry.Located (uniform box proper steps) point)) :=
  rfl

/-- The original point-bank estimate compares two actual meshes without evaluating a new reading. -/
example {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} {bounds : PrimitiveOverlapBounds clearance numerator}
    {columns rows : Nat} {target : Coordinate} {geometry : RectangularInverseModels.Geometry columns rows}
    {bank : RectangularInverseModels.Bank polynomial geometry}
    (request : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy bounds columns target)
    {transitions : RectangularInverseModels.Transitions (bank.refine request.index)}
    {gauge : Purelib.Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : Purelib.LinearAlgebra.Grid.Offsets anchors.edges}
    {firstTriangles lastTriangles : List (ModelTriangle geometry)}
    {firstSurface : OwnedTriangulation firstTriangles} {lastSurface : OwnedTriangulation lastTriangles}
    (first : SharedPrimitiveValues anchors offsets firstSurface)
    (last : SharedPrimitiveValues anchors offsets lastSurface)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (firstStart firstFinish : Fin firstSurface.mesh.vertices.length)
    (lastStart lastFinish : Fin lastSurface.mesh.vertices.length)
    (startEqual : firstSurface.mesh.coordinate firstStart = lastSurface.mesh.coordinate lastStart)
    (finishEqual : firstSurface.mesh.coordinate firstFinish = lastSurface.mesh.coordinate lastFinish) :
    normSq ((first.values firstFinish - first.values firstStart) -
      (last.values lastFinish - last.values lastStart)) ≤ 16 * request.globalBound := by
  have paid := RectangularPointReadings.GridPrimitiveAccuracy.point_increment_bound request
    (RectangularPointReadings.PointReadings.ofMesh first) last refines
    firstStart firstFinish lastStart lastFinish startEqual.symm finishEqual.symm
  rewrite [RectangularPointReadings.PointReadings.values_ofMesh] at paid
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact paid

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial

/-- The actual source-to-anchor acquisition calibrates a computed containing cell to the actual retained path root.

The retained route and its true finish Owner supply the prefix. The
coordinate search uses the cached geometry, deriving its four endpoint
bounds from the saved whole geometry equation. The actual path supplies
its original final Owner. No cell lookup, root-sign
agreement or final numerical estimate is supplied by the caller.
-/
example {genus : Nat} (curve : HyperellipticCurve genus) (differential : Differential genus)
    {box : Box} (clearance : Clearance curve.polynomial box) (proper : box.Proper)
    (point : Gaussian) (inside : box.Contains point) (source : Owner (curve.polynomial.eval point))
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial point)
    {finish : Gaussian} (path : ClearPath curve.polynomial box point finish) (traced : TracedPath path source)
    (index : Nat) :
    let acquired := RectangularPatch.acquireAt clearance proper point inside source
    let geometry := acquired.2.2.2.2.1.val
    let patch := acquired.2.2.2.2.2.val
    ∃ column row, (geometry.box column row).Contains finish ∧
      RootAligned ((Model.overlapRefine (patch.transported.cell column row).model) index) finish
        (ownerName traced.finishOwner) := by
  let acquired := RectangularPatch.acquireAt clearance proper point inside source
  let geometry := acquired.2.2.2.2.1.val
  let patch := acquired.2.2.2.2.2.val
  have finishInside : box.Contains finish :=
    ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_finish_inside traced.prepared inside
  let steps := dyadicSteps acquired.2.2.2.1.val.depth
  have geometryEq : geometry = uniform box proper steps := acquired.2.2.2.2.1.property
  have xLower : geometry.x.coordinates 0 ≤ finish.re := by
    rewrite [geometryEq]
    exact (RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.1).trans_le finishInside.1
  have xUpper : finish.re ≤ geometry.x.coordinates (Fin.last (steps + 1)) := by
    rewrite [geometryEq]
    exact finishInside.2.1.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.1).symm
  have yLower : geometry.y.coordinates 0 ≤ finish.im := by
    rewrite [geometryEq]
    exact (RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.2).trans_le finishInside.2.2.1
  have yUpper : finish.im ≤ geometry.y.coordinates (Fin.last (steps + 1)) := by
    rewrite [geometryEq]
    exact finishInside.2.2.2.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.2).symm
  let located := RectangularUniformGeometry.locate geometry finish xLower xUpper yLower yUpper
  have enteredInside := InBox.ofWithin acquired.1.val.path acquired.1.val.within inside
  have tracedInside := InBox.ofWithin path
    (ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_within traced.prepared) inside
  have aligned : RootAligned ((Model.overlapRefine
      (patch.transported.cell located.column located.row).model) index) finish (ownerName traced.finishOwner) :=
    (patch.transported.cell located.column located.row).trace_aligned
    (entered := acquired.2.1.val) enteredInside differential degreePositive reference traced tracedInside
    (OwnerFrame.build traced.finishOwner.parameterNonzero) located.inside index
  exact ⟨located.column, located.row, located.inside, aligned⟩

/-- The same actual acquisition keeps the original unflipped gauge and transported readings throughout its grid.

The stored prefix supplies the source-to-anchor ownership. Both conclusions
consume that same patch and its actual geometry at arbitrary later indices.
-/
example {genus : Nat} (curve : HyperellipticCurve genus) (differential : Differential genus)
    {box : Box} (clearance : Clearance curve.polynomial box) (proper : box.Proper)
    (point : Gaussian) (inside : box.Contains point) (source : Owner (curve.polynomial.eval point))
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial point) :
    let acquired := RectangularPatch.acquireAt clearance proper point inside source
    let patch := acquired.2.2.2.2.2.val
    ∀ column row index query,
      patch.sheets.gauge.values column row = false ∧
      ((RectangularSheetGauge.Transitions.oriented
        (patch.sheets.refine index).transitions (patch.sheets.refine index).gauge).ready column row).model.value.eval
          query = ((patch.transported.cell column row).model.refine (index + 2)).value.eval query := by
  let acquired := RectangularPatch.acquireAt clearance proper point inside source
  let patch := acquired.2.2.2.2.2.val
  have enteredInside := InBox.ofWithin acquired.1.val.path acquired.1.val.within inside
  exact fun column row index query =>
    ⟨patch.gauge_false (entered := acquired.2.1.val) enteredInside differential degreePositive reference column row,
    patch.oriented_value (entered := acquired.2.1.val) enteredInside differential degreePositive reference
      index column row query⟩

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveEdgeAccuracy)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Geometry.Rational.Box
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
open Purelib.Polynomial.Dense.Gaussian.Bounds.Box
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- The existing box operation preserves the complete former zero-pair primitive-on-base construction. -/
example {polynomial numerator : Polynomial} {count index : Nat}
    {patch : ContinuedInverseRoot.ContinuedNeighborhood polynomial count}
    (model : PrimitiveModel patch index numerator) :
    model.primitive.onBox patch.base.box =
      (show DensePrimitive model.coefficient patch.base.box from
        { value := model.primitive.value
          derivative_eq := model.primitive.derivative_eq
          remainderBound := Taylor.denseTaylorRemainderBound model.primitive.value patch.base.box
          remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
          increment_bound := fun firstInside lastInside => by
            have estimate := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
              model.primitive.value lastInside firstInside
            rewrite [model.primitive.derivative_eq] at estimate
            exact estimate }) := rfl

open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)

section

attribute [local irreducible] PrimitiveModel.ofPowers

/-- Construct the cubic comparison on the same retained simple source, cell and endpoint neighborhood owners. -/
private theorem cubicEdge {genus : Nat} {curve : HyperellipticCurve genus}
    {box inner prefixAmbient ambient : Box} {clearance : Clearance curve.polynomial box}
    {bounds : Bounds clearance} {point query : Gaussian} {source : Owner (curve.polynomial.eval point)}
    {prefixPath : ClearPath curve.polynomial prefixAmbient point box.anchor}
    {entered : TracedPath prefixPath source} {path : ClearPath curve.polynomial ambient point query}
    (cell : TransportedCell bounds entered.finishOwner inner) (prefixInside : InBox box prefixPath)
    (differential : Differential genus) (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial point) (traced : TracedPath path source)
    (tracedInside : InBox box path) (pointInside : inner.Contains query) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count)
    (numerator : Polynomial) (floor : Nat) (target : Coordinate) (positive : 0 < target) :
    ∃ finish leftIndex rightIndex,
      floor ≤ leftIndex ∧ leftIndex < rightIndex ∧
      ∃ coefficient : Polynomial,
        (∀ argument, coefficient.eval argument =
          numerator.eval argument * (cell.model.refine (leftIndex + 2)).value.eval argument ^ 3) ∧
        ∃ first : DensePrimitive coefficient inner,
          ∃ second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator 1,
            normSq ((first.value.eval finish - first.value.eval query) -
            (second.primitive.value.eval finish - second.primitive.value.eval query)) < target := by
  have commonLeft : (Point.pointBox query).Refines inner := pointInside
  have commonRight : (Point.pointBox query).Refines neighborhood.patch.box := neighborhood.center_inside
  let common := Intersection.intersection inner neighborhood.patch.box (Point.pointBox query) commonLeft commonRight
  let finish := common.anchor
  have leftFinish : inner.Contains finish := Intersection.intersection_refines_first.contains common.contains_anchor
  have rightFinish : neighborhood.patch.box.Contains finish :=
    Intersection.intersection_refines_second.contains common.contains_anchor
  let overlap := PrimitiveOverlapBounds.build (clearance.restrict cell.geometry.refines) numerator
  let request := PrimitiveEdgeAccuracy.build overlap cell.model neighborhood.patch.base.model query finish target
    positive 1
  let leftIndex := max request.index floor
  let rightIndex := leftIndex + 1
  let leftModel := cell.model.refine (leftIndex + 2)
  let rightModel : InverseRootPolynomial.Model curve.polynomial neighborhood.patch.base.box :=
    neighborhood.patch.base.refine (rightIndex + 2)
  let leftPowers := OddPowers.build leftModel.value
  let rightPowers : OddPowers rightModel.value := OddPowers.build rightModel.value
  let first := DensePrimitive.ofPolynomial (numerator * leftPowers.cube) inner
  let second : PrimitiveModel (polynomial := curve.polynomial) (count := count)
      neighborhood.patch (rightIndex + 2) numerator 1 :=
    PrimitiveModel.ofPowers (polynomial := curve.polynomial) (count := count)
      neighborhood.patch (rightIndex + 2) numerator rightModel
      (show rightModel.value = (neighborhood.patch.base.refine (rightIndex + 2)).value from Eq.refl rightModel.value)
      rightPowers 1
  have coefficientEq : ∀ argument, (numerator * leftPowers.cube).eval argument =
      numerator.eval argument * leftModel.value.eval argument ^ 3 := fun argument => by
    rewrite [DensePolynomial.eval_mul, leftPowers.cube_eval]
    rfl
  have paid := cell.trace_primitive_increment_lt (entered := entered) (pairs := 1) (numerator := numerator)
    prefixInside differential degreePositive reference traced tracedInside
    (OwnerFrame.build traced.finishOwner.parameterNonzero) pointInside neighborhood request leftIndex rightIndex
    (Nat.Order.le_max_left _ _) (by exact (Nat.Order.le_max_left _ _).trans (Nat.le_add_right _ _))
    first coefficientEq second leftFinish rightFinish
  exact ⟨finish, leftIndex, rightIndex, Nat.Order.le_max_right _ _, Nat.lt_succ_self _,
    numerator * leftPowers.cube, coefficientEq, first, second,
    by simpa only [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical] using paid⟩

end

/-- A computed common subbox and actual retained source acquisition pay a cubic primitive edge at independent floors.

The original cached geometry locates the actual path endpoint. The finite
coordinate intersection supplies a second endpoint in both original
primitive domains. One retained accuracy request chooses both later
indices before the model powers and two primitives are built. No endpoint
domain, root-sign comparison or final error inequality is assumed.
-/
example {genus : Nat} (curve : HyperellipticCurve genus) (differential : Differential genus)
    {box : Box} (clearance : Clearance curve.polynomial box) (proper : box.Proper)
    (point : Gaussian) (inside : box.Contains point) (source : Owner (curve.polynomial.eval point))
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial point)
    {query : Gaussian} (path : ClearPath curve.polynomial box point query) (traced : TracedPath path source)
    (numerator : Polynomial) (floor : Nat) (target : Coordinate) (positive : 0 < target) :
    let acquired := RectangularPatch.acquireAt clearance proper point inside source
    let geometry := acquired.2.2.2.2.1.val
    let patch := acquired.2.2.2.2.2.val
    ∃ column row : Fin (dyadicSteps acquired.2.2.2.1.val.depth + 1),
      ∃ finish leftIndex rightIndex,
        floor ≤ leftIndex ∧ leftIndex < rightIndex ∧
        ∃ coefficient : Polynomial,
          (∀ argument, coefficient.eval argument = numerator.eval argument *
            ((patch.transported.cell column row).model.refine (leftIndex + 2)).value.eval argument ^ 3) ∧
          ∃ first : DensePrimitive coefficient (geometry.box column row),
            ∃ second : PrimitiveModel (TracedPrimitiveNeighborhood.Neighborhood.build traced 0).patch
            (rightIndex + 2) numerator 1,
            normSq ((first.value.eval finish - first.value.eval query) -
              (second.primitive.value.eval finish - second.primitive.value.eval query)) < target := by
  let acquired := RectangularPatch.acquireAt clearance proper point inside source
  let geometry := acquired.2.2.2.2.1.val
  let patch := acquired.2.2.2.2.2.val
  have queryInside : box.Contains query :=
    ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_finish_inside traced.prepared inside
  let steps := dyadicSteps acquired.2.2.2.1.val.depth
  have geometryEq : geometry = uniform box proper steps := acquired.2.2.2.2.1.property
  have xLower : geometry.x.coordinates 0 ≤ query.re := by
    rewrite [geometryEq]
    exact (RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.1).trans_le queryInside.1
  have xUpper : query.re ≤ geometry.x.coordinates (Fin.last (steps + 1)) := by
    rewrite [geometryEq]
    exact queryInside.2.1.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.1).symm
  have yLower : geometry.y.coordinates 0 ≤ query.im := by
    rewrite [geometryEq]
    exact (RectangularUniformGeometry.Axis.uniform_first steps _ _ proper.2).trans_le queryInside.2.2.1
  have yUpper : query.im ≤ geometry.y.coordinates (Fin.last (steps + 1)) := by
    rewrite [geometryEq]
    exact queryInside.2.2.2.trans_eq (RectangularUniformGeometry.Axis.uniform_last steps _ _ proper.2).symm
  let located := RectangularUniformGeometry.locate geometry query xLower xUpper yLower yUpper
  let cell := patch.transported.cell located.column located.row
  let neighborhood := TracedPrimitiveNeighborhood.Neighborhood.build traced 0
  have enteredInside := InBox.ofWithin acquired.1.val.path acquired.1.val.within inside
  have tracedInside := InBox.ofWithin path
    (ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation.prepared_within traced.prepared) inside
  exact ⟨located.column, located.row,
    cubicEdge cell enteredInside differential degreePositive reference traced tracedInside located.inside
      neighborhood numerator floor target positive⟩

section

attribute [local irreducible] PrimitiveModel.ofPowers Primitives.build

/-- A cached cubic grid primitive bank and original source neighborhood are constructed once at their paid indices.

The common endpoint is computed in the two actual domains. The same saved
accuracy request chooses both later indices before the bank and source
primitive are built. The complete original caches remain in the result.
-/
example {genus : Nat} {curve : HyperellipticCurve genus}
    {box prefixAmbient ambient : Box} {clearance : Clearance curve.polynomial box} {bounds : Bounds clearance}
    {start point : Gaussian} {source : Owner (curve.polynomial.eval start)}
    {prefixPath : ClearPath curve.polynomial prefixAmbient start box.anchor} {entered : TracedPath prefixPath source}
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    (patch : RectangularPatch bounds entered.finishOwner geometry)
    (prefixInside : InBox box prefixPath) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial start)
    {path : ClearPath curve.polynomial ambient start point} (traced : TracedPath path source)
    (inside : InBox box path) (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (pointInside : (geometry.box column row).Contains point) {count : Nat}
    (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count)
    (numerator : Polynomial) (floor : Nat) (target : Coordinate) (positive : 0 < target) :
    ∃ finish leftIndex rightIndex, floor ≤ leftIndex ∧ leftIndex < rightIndex ∧
      ∃ primitives : Primitives
        (RectangularSheetGauge.Transitions.oriented (patch.sheets.refine leftIndex).transitions
          (patch.sheets.refine leftIndex).gauge) numerator 1,
        ∃ second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator 1,
          normSq ((primitives.value column row finish - primitives.value column row point) -
            (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  let cell := patch.transported.cell column row
  let common := Intersection.intersection (geometry.box column row) neighborhood.patch.box (Point.pointBox point)
    (show (Point.pointBox point).Refines (geometry.box column row) from pointInside)
    (show (Point.pointBox point).Refines neighborhood.patch.box from neighborhood.center_inside)
  let finish := common.anchor
  have leftFinish : (geometry.box column row).Contains finish :=
    Intersection.intersection_refines_first.contains common.contains_anchor
  have rightFinish : neighborhood.patch.box.Contains finish :=
    Intersection.intersection_refines_second.contains common.contains_anchor
  let overlap := PrimitiveOverlapBounds.build (clearance.restrict cell.geometry.refines) numerator
  let request := PrimitiveEdgeAccuracy.build overlap cell.model neighborhood.patch.base.model point finish target
    positive 1
  let leftIndex := max request.index floor
  let rightIndex := leftIndex + 1
  let primitives : Primitives
      (RectangularSheetGauge.Transitions.oriented (patch.sheets.refine leftIndex).transitions
        (patch.sheets.refine leftIndex).gauge) numerator 1 :=
    Primitives.build (RectangularSheetGauge.Transitions.oriented (patch.sheets.refine leftIndex).transitions
      (patch.sheets.refine leftIndex).gauge) numerator 1
  let rightModel : InverseRootPolynomial.Model curve.polynomial neighborhood.patch.base.box :=
    neighborhood.patch.base.refine (rightIndex + 2)
  let powers := OddPowers.build rightModel.value
  let second : PrimitiveModel neighborhood.patch (rightIndex + 2) numerator 1 :=
    PrimitiveModel.ofPowers neighborhood.patch (rightIndex + 2) numerator rightModel
      (show rightModel.value = (neighborhood.patch.base.refine (rightIndex + 2)).value from Eq.refl rightModel.value)
      powers 1
  have paid := patch.primitive_trace_increment_lt prefixInside differential degreePositive reference
    primitives column row traced inside (OwnerFrame.build traced.finishOwner.parameterNonzero)
    pointInside neighborhood second request (Nat.Order.le_max_left _ _)
    (by exact (Nat.Order.le_max_left _ _).trans (Nat.le_add_right _ _)) leftFinish rightFinish
  exact ⟨finish, leftIndex, rightIndex, Nat.Order.le_max_right _ _, Nat.lt_succ_self _, primitives, second, paid⟩

end

section RetainedPathSplits

open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits PreparedSplitMesh)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (traced_parent_reached)

/-- Actual retained path-parent lineage gives the original uniform-grid endpoint coverage. -/
private theorem traceCoverage {genus : Nat} {curve : HyperellipticCurve genus}
    (differential : Differential genus) {box : Box} (proper : box.Proper) (steps : Nat)
    (clearance : Clearance curve.polynomial box) {ambient : Box} {start finish : Gaussian}
    {source : Owner (curve.polynomial.eval start)} {path : ClearPath curve.polynomial ambient start finish}
    {prepared : CoveredTracedPath path source} (inside : InBox box path) (sheet : Fin 2)
    (cache : ParentCache prepared differential sheet) :
    ∀ parent ∈ cache.parents,
      RectangularSegmentSplitting.Geometry.Covers (uniform box proper steps) (parent.edge.point 0) ∧
        RectangularSegmentSplitting.Geometry.Covers (uniform box proper steps) (parent.edge.point 1) := by
  intro parent member
  have original := Eq.mp (congrArg (fun parents => parent ∈ parents) cache.parents_eq) member
  have reached := traced_parent_reached clearance differential sheet prepared.traced inside parent original
  exact ⟨RectangularSegmentSplitting.Geometry.uniform_covers box proper steps reached.first_inside,
    RectangularSegmentSplitting.Geometry.uniform_covers box proper steps reached.last_inside⟩

/-- Split two actual retained covered parent caches once, then build one common endpoint mesh.

The two ordered splitting banks are stored beside the common mesh. Its
split bank is their original structural append, retaining both complete
parent orders and every repeated endpoint occurrence.
-/
private def retainedPairMesh {genus : Nat} {curve : HyperellipticCurve genus}
    (differential : Differential genus) {box : Box} (proper : box.Proper) (steps : Nat)
    (cuts : GridCuts (uniform box proper steps)) (clearance : Clearance curve.polynomial box)
    {firstAmbient secondAmbient : Box} {firstStart firstFinish secondStart secondFinish : Gaussian}
    {firstSource : Owner (curve.polynomial.eval firstStart)}
    {secondSource : Owner (curve.polynomial.eval secondStart)}
    {firstPath : ClearPath curve.polynomial firstAmbient firstStart firstFinish}
    {secondPath : ClearPath curve.polynomial secondAmbient secondStart secondFinish}
    {first : CoveredTracedPath firstPath firstSource} {second : CoveredTracedPath secondPath secondSource}
    (firstInside : InBox box firstPath) (secondInside : InBox box secondPath) (sheet : Fin 2)
    (firstCache : ParentCache first differential sheet) (secondCache : ParentCache second differential sheet) :
    Σ left : ParentSplits cuts firstCache.parents, Σ right : ParentSplits cuts secondCache.parents,
      {mesh : PreparedSplitMesh cuts (firstCache.parents ++ secondCache.parents) //
        mesh.splits = left.append right} :=
  let firstCovered := traceCoverage differential proper steps clearance firstInside sheet firstCache
  let secondCovered := traceCoverage differential proper steps clearance secondInside sheet secondCache
  let left := ParentSplits.build cuts firstCache.parents firstCovered
  let right := ParentSplits.build cuts secondCache.parents secondCovered
  have joined : ∀ parent ∈ firstCache.parents ++ secondCache.parents,
      RectangularSegmentSplitting.Geometry.Covers (uniform box proper steps) (parent.edge.point 0) ∧
        RectangularSegmentSplitting.Geometry.Covers (uniform box proper steps) (parent.edge.point 1) := by
    intro parent member
    cases (Data.List.Membership.mem_append.mp member) with
    | inl member => exact firstCovered parent member
    | inr member => exact secondCovered parent member
  let mesh := PreparedSplitMesh.build cuts (firstCache.parents ++ secondCache.parents) joined [] (left.append right)
  ⟨left, right, mesh, rfl⟩

/-- Omitting a retained splitting bank preserves the complete former mesh result at every input. -/
example {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows} (cuts : GridCuts geometry)
    (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential))
    (covered : ∀ parent ∈ parents,
      RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 0) ∧
        RectangularSegmentSplitting.Geometry.Covers geometry (parent.edge.point 1)) (extra : List Gaussian) :
    PreparedSplitMesh.build cuts parents covered extra =
      (let splits := ParentSplits.build cuts parents covered
       let points := splits.points ++ extra
       (⟨splits, points, rfl, RectangularCommonMesh.RectangularInverseModels.CommonMesh.build geometry
         (RectangularExteriorBoundary.Geometry.allCells geometry) points⟩ : PreparedSplitMesh cuts parents extra)) :=
  rfl

end RetainedPathSplits

end TestPurelib.Curves.Legendre.ParallelPrimitiveCover
