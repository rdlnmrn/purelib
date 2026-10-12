module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Grid

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularPrimitiveGluing

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Actual face-trace comparison for glued rectangular primitives

The rectangular gauge has already been identified with the transported
face owner. Thus cached primitives and their translated values compare
with an actual contained path occurrence anywhere in a cell. Independent
later indices permit one common finite accuracy across a whole bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (SeededNeighborhood)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison (trace_primitive_increment_le
  trace_primitive_increment_lt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge (oriented_value)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face} {sheet :
    Fin 2}
  {columns rows : Nat} {geometry : Geometry columns rows}
  {patch : RectangularPatch models.bounds (models.frame.owners sheet)
    geometry}
  {numerator : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial} {index : Nat}
  {primitives : Primitives
    (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented (patch.sheets.refine index).transitions
    (patch.sheets.refine index).gauge) numerator}

/-- Identify the derivative of the actual retained primitive cache with the transported cell model. No canonical
primitive or coefficient-list equality is needed, and additive primitive constants remain unrestricted. -/
theorem primitive_coefficient_eq (differential : Differentials.Basic.Differential genus)
    (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : InverseRootPolynomial.Gaussian) :
    (primitives.cells column row).coefficient.eval point =
      numerator.eval point * ((patch.transported.cell column row).model.refine (index + 2)).value.eval point := by
  rw [primitives.coefficient_eq, SheetGauge.oriented_value patch differential]

/-- Full-edge comparison of retained rectangular primitives with the actual trace endpoint's neighborhood, at
independent polynomial indices. -/
theorem primitive_trace_increment_le (differential : Differentials.Basic.Differential genus)
    (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : InverseRootPolynomial.Box} {point : InverseRootPolynomial.Gaussian} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient face.cell.box.anchor point}
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains
      point)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (rightIndex : Nat)
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (rightIndex + 2) numerator)
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict (patch.cell_refines column row))
      numerator)
    (finish : InverseRootPolynomial.Gaussian) (leftFinish : (geometry.box column row).Contains finish)
    (rightFinish : neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((primitives.value column row finish - primitives.value column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) ≤
      12 * (((patch.transported.cell column row).model.refine (index + 2)).bound +
        (neighborhood.patch.base.refine (rightIndex + 2)).bound) *
          (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - point) :=
  ContinuedComparison.trace_primitive_increment_le (patch.transported.cell column row) differential traced inside frame
    pointInside
    neighborhood index rightIndex (primitives.dense column row)
      (primitive_coefficient_eq differential primitives
      column row)
    second bounds finish leftFinish rightFinish

/-- A single retained request remains valid at independently selected later indices. This allows a finite bank-wide
maximum without rebuilding the request's bounds or introducing another successful-check premise. -/
theorem primitive_trace_increment_lt (differential : Differentials.Basic.Differential genus)
    (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine index).transitions
      (patch.sheets.refine index).gauge) numerator)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : InverseRootPolynomial.Box} {point : InverseRootPolynomial.Gaussian} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient face.cell.box.anchor point}
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains
      point)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) {rightIndex : Nat}
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (rightIndex + 2) numerator)
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict (patch.cell_refines column row))
      numerator}
    {finish : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model
      neighborhood.patch.base.model point finish target)
    (leftLater : request.index ≤ index) (rightLater : request.index ≤ rightIndex)
    (leftFinish : (geometry.box column row).Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((primitives.value column row finish - primitives.value column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  have leftDecrease : ((patch.transported.cell column row).model.refine (index + 2)).bound ≤
      ((patch.transported.cell column row).model.refine request.index).bound := by
    rw [Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone (patch.transported.cell column row).model.bound_nonnegative
      (leftLater.trans (Nat.le_add_right _ _))
  have rightDecrease : (neighborhood.patch.base.refine (rightIndex + 2)).bound ≤
      (neighborhood.patch.base.refine request.index).bound := by
    rw [SeededNeighborhood.refine, SeededNeighborhood.refine, Model.refine_bound, Model.refine_bound]
    exact quarterRadius_antitone neighborhood.patch.base.model.bound_nonnegative
      (rightLater.trans (Nat.le_add_right _ _))
  have bound := primitive_trace_increment_le differential
    primitives column row traced inside frame pointInside neighborhood
    rightIndex second bounds finish leftFinish rightFinish
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, SeededNeighborhood.refine] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply bound.trans_lt
  apply lt_of_le_of_lt _ request.refined_scale_lt
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftDecrease rightDecrease) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - point))

/-- The spanning-tree translation cancels on each genuine local edge. This compares the values actually used by the
glued surface, without assuming that adjacent primitive polynomials agree exactly. -/
theorem aligned_trace_increment_lt (differential : Differentials.Basic.Differential genus)
    (anchors : RectangularPrimitiveGluing.PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
      anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {ambient : InverseRootPolynomial.Box} {point : InverseRootPolynomial.Gaussian} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient face.cell.box.anchor point}
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval point)) (pointInside : (geometry.box column row).Contains
      point)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) {rightIndex : Nat}
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (rightIndex + 2) numerator)
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict (patch.cell_refines column row))
      numerator}
    {finish : InverseRootPolynomial.Gaussian} {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model
      neighborhood.patch.base.model point finish target)
    (leftLater : request.index ≤ index) (rightLater : request.index ≤ rightIndex)
    (leftFinish : (geometry.box column row).Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((anchors.alignedValue offsets column row finish - anchors.alignedValue
      offsets column row point) -
      (second.primitive.value.eval finish - second.primitive.value.eval point)) < target := by
  have increments : anchors.alignedValue offsets column row finish - anchors.alignedValue offsets column row point =
      primitives.value column row finish - primitives.value column row point := by
    simp only [PrimitiveAnchors.alignedValue]
    ring1
  rw [increments]
  exact primitive_trace_increment_lt differential
    primitives column row traced inside frame pointInside neighborhood
    second request leftLater rightLater leftFinish rightFinish

/-- Shared mesh readings now compare with the actual face-trace primitive. Both vertex-owner changes are charged before
the local analytic error. The displayed global term must still be paid when summing over a surface; this theorem does
not silently treat it as a spatially decaying error. -/
theorem shared_trace_increment_lt (differential : Differentials.Basic.Differential genus)
    {globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance numerator} {tolerance :
      InverseRootPolynomial.Coordinate}
    (gridRequest : RectangularPrimitiveAccuracy.GridPrimitiveAccuracy globalBounds columns tolerance)
    {primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented
      (patch.sheets.refine gridRequest.index).transitions (patch.sheets.refine gridRequest.index).gauge) numerator}
    {anchors : RectangularPrimitiveGluing.PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets
      anchors.edges}
    {triangles : List (RectangularOwnedTriangulation.ModelTriangle geometry)} {surface :
      RectangularOwnedTriangulation.OwnedTriangulation triangles}
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets surface)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (first last : Fin surface.mesh.vertices.length)
    (firstInside : (geometry.box column row).Contains (surface.mesh.coordinate first))
    (lastInside : (geometry.box column row).Contains (surface.mesh.coordinate last))
    {ambient : InverseRootPolynomial.Box} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      face.cell.box.anchor
      (surface.mesh.coordinate first)}
    (traced : PreparedPathTrace.TracedPath path (models.frame.owners sheet)) (inside : ClearPath.InBox face.cell.box
      path)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval (surface.mesh.coordinate first)))
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) {rightIndex : Nat}
    (second : InverseRootPrimitive.PrimitiveModel neighborhood.patch (rightIndex + 2) numerator)
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds (face.clearance.restrict (patch.cell_refines column row))
      numerator}
    {target : InverseRootPolynomial.Coordinate}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds (patch.transported.cell column row).model
      neighborhood.patch.base.model
      (surface.mesh.coordinate first) (surface.mesh.coordinate last) target)
    (leftLater : request.index ≤ gridRequest.index) (rightLater : request.index ≤ rightIndex)
    (rightFinish : neighborhood.patch.box.Contains (surface.mesh.coordinate last)) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      (second.primitive.value.eval (surface.mesh.coordinate last) - second.primitive.value.eval (surface.mesh.coordinate
        first))) <
      32 * gridRequest.globalBound + 2 * target := by
  let localIncrement := primitives.value column row (surface.mesh.coordinate last) -
    primitives.value column row (surface.mesh.coordinate first)
  let actualIncrement := second.primitive.value.eval (surface.mesh.coordinate last) -
    second.primitive.value.eval (surface.mesh.coordinate first)
  have ownership := GridPrimitiveAccuracy.shared_local_increment_bound
    gridRequest readings patch.cell_refines column row first last firstInside lastInside
  have analytic := primitive_trace_increment_lt
    differential primitives column row traced inside frame firstInside
    neighborhood second request leftLater rightLater lastInside rightFinish
  have identity : (readings.values last - readings.values first) - actualIncrement =
      ((readings.values last - readings.values first) - localIncrement) + (localIncrement - actualIncrement) := by ring1
  change Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) - actualIncrement) < _
  rw [identity]
  have triangle := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((readings.values last - readings.values first) - localIncrement) (localIncrement - actualIncrement)
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at triangle ownership analytic
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact triangle.trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((add_le_add ownership le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct analytic (16 * gridRequest.globalBound)))).trans_eq (by
          ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives
