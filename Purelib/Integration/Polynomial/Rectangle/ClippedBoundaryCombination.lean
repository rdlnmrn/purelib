module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Algebra.FiniteSum.Fin

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic

public section

/-! Coefficient expansion preserves every subdivided clipped side. -/
namespace Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
open Purelib.Riemann.Periods.BilinearCombination (edgeArea_combination)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Box)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_add sumFin_sub)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {leftCount rightCount : Nat}
  (left : Fin leftCount → Gaussian) (right : Fin rightCount → Gaussian)
  (first : Fin leftCount → Gaussian → Gaussian) (second : Fin rightCount → Gaussian → Gaussian)

open Purelib.Algebra
open Purelib.Geometry.Rectangle.Partition
/-- The dyadic horizontal boundary of paired finite linear combinations is the double weighted sum of original pair
boundaries.

Both finite coefficient families retain every ordered index pair. Dyadic recursion visits the same half intervals, with
the fixed vertical coordinate and subdivision depth unchanged. -/
theorem horizontalBoundary_combination (depth : Nat)
  (lower upper fixed : Coordinate) :
    PreparedBoxBoundary.horizontalBoundary (fun point => ⟨sumFin (fun row => left row * first row point),
      FiniteSum.Fin.sumFin (fun row => right row * second row point)⟩) depth lower upper fixed =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        PreparedBoxBoundary.horizontalBoundary (fun point => ⟨first i point, second j point⟩) depth lower upper fixed))
          := by
  induction depth generalizing lower upper with
  | zero => exact edgeArea_combination left right _ _ _ _
  | succ depth ih =>
      simp only [PreparedBoxBoundary.horizontalBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [ih, ih]

/-- The dyadic vertical boundary of paired finite linear combinations is the double weighted sum of original pair
boundaries.

Both finite coefficient families retain every ordered index pair. Dyadic recursion visits the same half intervals, with
the fixed horizontal coordinate and subdivision depth unchanged. -/
theorem verticalBoundary_combination (depth : Nat)
  (lower upper fixed : Coordinate) :
    PreparedBoxBoundary.verticalBoundary (fun point => ⟨sumFin (fun row => left row * first row point),
      FiniteSum.Fin.sumFin (fun row => right row * second row point)⟩) depth lower upper fixed =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        PreparedBoxBoundary.verticalBoundary (fun point => ⟨first i point, second j point⟩) depth lower upper fixed)) :=
          by
  induction depth generalizing lower upper with
  | zero => exact edgeArea_combination left right _ _ _ _
  | succ depth ih =>
      simp only [PreparedBoxBoundary.verticalBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [ih, ih]

/-- The rectangular boundary of paired finite linear combinations is the double weighted sum of pair boundaries.

All four sides use the same retained box endpoints and subdivision depth. Their oriented contributions are expanded
without identifying or reordering coefficient pairs. -/
theorem rectangleBoundary_combination (depth : Nat) (box
  : Box) :
    PreparedBoxBoundary.rectangleBoundary (fun point => ⟨sumFin (fun row => left row * first row point),
      FiniteSum.Fin.sumFin (fun row => right row * second row point)⟩) depth box =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        PreparedBoxBoundary.rectangleBoundary (fun point => ⟨first i point, second j point⟩) depth box)) := by
  simp only [PreparedBoxBoundary.rectangleBoundary, mul_add, mul_sub, FiniteSum.Fin.sumFin_add,
    FiniteSum.Fin.sumFin_sub]
  rw [horizontalBoundary_combination, verticalBoundary_combination,
    horizontalBoundary_combination, verticalBoundary_combination]

end Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_add)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
variable {columns rows leftCount rightCount : Nat} {geometry : Geometry columns rows}

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Meshes in
/-- The retained observation pieces' local boundary distributes over the two original coefficient families.

The exact box occurrences, cell owners and subdivision depth remain fixed in every paired boundary term. -/
theorem localBoundary_combination {boxes :
  List Box} (pieces : ObservationPieces geometry boxes)
    (left : Fin leftCount → Gaussian) (right : Fin rightCount → Gaussian)
    (first : Fin leftCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian)
    (second : Fin rightCount → Fin (columns + 1) → Fin (rows + 1) → Gaussian → Gaussian) (depth : Nat) :
    pieces.localBoundary (fun column row point => ⟨sumFin (fun i => left i * first i column row point),
      FiniteSum.Fin.sumFin (fun j => right j * second j column row point)⟩) depth =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        pieces.localBoundary (fun column row point => ⟨first i column row point, second j column row point⟩) depth)) :=
          by
  induction pieces with
  | nil =>
      conv_lhs => simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_zero,
        FiniteSum.Fin.sumFin_zero]
      conv_rhs => simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_zero,
        FiniteSum.Fin.sumFin_zero]
  | cons column row refines tail ih =>
      simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [PreparedBoxBoundary.rectangleBoundary_combination, ih]

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

end
