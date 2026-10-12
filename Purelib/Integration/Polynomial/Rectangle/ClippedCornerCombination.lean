module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic

import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Polynomial.Geometry.Grid.ClearGrid

public section

/-! Coefficient expansion of the actual clipped corner polygons, retaining
every owner and every junction introduced by the common cut bank. -/
section

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {columns rows leftCount rightCount : Nat} {geometry :
  Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry} {box :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Retain the observation mesh's exact corner grid as nested fixed-length vectors.

The two vector dimensions are the exact retained boundary dimensions. Each entry caches the existing owner-indexed
corner grid at its original finite position. -/
@[expose] def cornerValues (mesh :
  RectangularObservationMesh.ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Stokes.PrimitivePoint) :
    BilinearGridBoundary.Values mesh.boundaryColumns mesh.boundaryRows :=
  Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => mesh.cornerGrid values column row

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- The retained assembly's corner total equals the interior corner sum of its exact mesh values.

Pointwise cache readback identifies each retained interior corner. The two finite sums then combine those same ordered
corner occurrences. -/
theorem
  cornerTotal_eq_values
  {mesh : RectangularObservationMesh.ObservationMesh cuts box}
    {values : Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Stokes.PrimitivePoint}
    (assembly : RectangularObservationAssembly.ObservationMesh.ClippedAssembly mesh values) :
    assembly.cornerTotal = BilinearGridBoundary.cornerSum (mesh.cornerValues values) := by
  rw [assembly.cornerTotal_eq]
  unfold BilinearGridBoundary.cornerSum
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  conv_lhs => simp only [BilinearGridBoundary.interiorCorner,
    assembly.corners_eq, RectangularObservationMesh.ObservationMesh.cornerValues, Vector.Basic.vectorOfFn_apply]
  conv_rhs => simp only [BilinearGridBoundary.interiorCorner,
    assembly.corners_eq, RectangularObservationMesh.ObservationMesh.cornerValues, Vector.Basic.vectorOfFn_apply]

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

namespace Purelib.Integration.Polynomial.Rectangle.ClippedCornerCombination

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Periods in
/-- The interior corner sum distributes into the double weighted sum of the original paired coefficient families.

Bilinearity expands each retained grid corner into every ordered coefficient pair. The finite sum interchange keeps the
original mesh indices and corner orientation. -/
theorem cornerSum_combination (mesh : RectangularObservationMesh.ObservationMesh cuts box)
    (left : Fin leftCount → Basic.Canonical) (right : Fin rightCount → Basic.Canonical)
    (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Basic.Canonical)
    (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Basic.Canonical) :
    BilinearGridBoundary.cornerSum (mesh.cornerValues (fun column row point =>
      ⟨sumFin (fun i => left i * first i column row point),
        FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩)) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        BilinearGridBoundary.cornerSum (mesh.cornerValues
          (fun column row point => ⟨first i column row point, second j column row point⟩)))) := by
  have pointwise (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows) :
      BilinearGridBoundary.interiorCorner (mesh.cornerValues (fun column row point =>
        ⟨sumFin (fun i => left i * first i column row point),
          FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩)) column row =
        FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
          BilinearGridBoundary.interiorCorner (mesh.cornerValues
            (fun column row point => ⟨first i column row point, second j column row point⟩)) column row)) := by
    conv_lhs => simp only [BilinearGridBoundary.interiorCorner, BilinearGridBoundary.cornerArea,
      RectangularObservationMesh.ObservationMesh.cornerValues, Vector.Basic.vectorOfFn_apply,
        RectangularObservationMesh.ObservationMesh.cornerGrid, BilinearCombination.edgeArea_combination, mul_add,
        FiniteSum.Fin.sumFin_add]
    conv_rhs => simp only [BilinearGridBoundary.interiorCorner, BilinearGridBoundary.cornerArea,
      RectangularObservationMesh.ObservationMesh.cornerValues, Vector.Basic.vectorOfFn_apply,
        RectangularObservationMesh.ObservationMesh.cornerGrid, BilinearCombination.edgeArea_combination, mul_add,
        FiniteSum.Fin.sumFin_add]
  unfold BilinearGridBoundary.cornerSum
  rw [FiniteSum.Fin.sumFin_congr (fun column => FiniteSum.Fin.sumFin_congr (pointwise column))]
  simp only [BilinearCombination.sumFin_combination, -eq_self, -iff_self]
  rfl

end Purelib.Integration.Polynomial.Rectangle.ClippedCornerCombination

end

end
