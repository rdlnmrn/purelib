module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Polynomial.Rectangle.ClippedBoundaryCombination

open Purelib.Data.Gaussian.Basic (conj)

open Purelib.Data.Gaussian.Basic (Canonical)

public section

/-!
# Coefficient expansion of conjugate/value boundaries

Energy pairs are sesquilinear: the first coefficient is conjugated. These
finite expansions retain every subdivided side and model owner, including
all cross terms between different standard differentials.
-/

namespace Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- Conjugation distributes over the retained finite Gaussian sum.

Each bounded summand is conjugated once. First-position sum recursion applies the additive law to the unchanged
successor tail. -/
private theorem conjugate_sum {count : Nat} (values : Fin count → Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun index =>
      Data.Gaussian.Basic.conj (values
      index)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, Basic.conj_add, ih,
      FiniteSum.Fin.sumFin_succ]

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Polynomial in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The energy area of a finite linear combination expands into conjugate-left times right coefficient pair areas.

Only the left coefficient and value are conjugated. Both endpoint sums use the same retained finite coefficient family.
-/
theorem edgeArea_energy_combination {count : Nat} (coefficients : Fin count → Basic.Canonical)
    (first last : Fin count → Basic.Canonical) :
    Stokes.edgeArea (Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun row => coefficients row * first
      row)))
      (Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun row => coefficients row * last row))) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        Stokes.edgeArea ⟨conj (first i), first j⟩ ⟨conj (last i), last j⟩)) := by
  have firstConjugate : Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun row => coefficients row * first row)) =
      FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Basic.conj (coefficients row) * Data.Gaussian.Basic.conj (first
        row)) :=
    (conjugate_sum _).trans (FiniteSum.Fin.sumFin_congr (fun row =>
      Basic.conj_mul _ _))
  have lastConjugate : Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun row => coefficients row * last row)) =
      FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Basic.conj (coefficients row) * Data.Gaussian.Basic.conj (last
        row)) :=
    (conjugate_sum _).trans (FiniteSum.Fin.sumFin_congr (fun row =>
      Basic.conj_mul _ _))
  unfold Energy.Polygon.energyPrimitivePoint
  rw [firstConjugate, lastConjugate]
  exact BilinearCombination.edgeArea_combination (fun row => Data.Gaussian.Basic.conj (coefficients row)) coefficients
    _ _ _
    _

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Polynomial in
open Purelib.Topology.Polygon in
/-- The original oriented edge word's energy area expands into the double coefficient-weighted pair areas.

Every successive endpoint pair remains in the original edge word. Its energy contribution retains the left conjugation
and the ordered coefficient pair. -/
theorem edgeListArea_energy_combination {count vertices : Nat} (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Fin vertices → Basic.Canonical) (word : List (Stokes.OrientedEdge vertices)) :
    Stokes.edgeListArea (fun vertex => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun row =>
      coefficients row * values row vertex))) word =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        Stokes.edgeListArea (fun vertex => ⟨conj (values i vertex), values j vertex⟩) word)) := by
  induction word with
  | nil =>
      conv_lhs => simp only [Stokes.edgeListArea, mul_zero, FiniteSum.Fin.sumFin_zero]
      conv_rhs => simp only [Stokes.edgeListArea, mul_zero, FiniteSum.Fin.sumFin_zero]
  | cons edge word ih =>
      simp only [Stokes.edgeListArea, mul_add, FiniteSum.Fin.sumFin_add]
      rw [edgeArea_energy_combination, ih]

end Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes

namespace Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PreparedBoxPartitions

open Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PolygonStokes (edgeArea_energy_combination)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {count : Nat} (coefficients : Fin count → Canonical) (values : Fin count →
  Canonical → Canonical)

section
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration
open Purelib.Integration.Polynomial
open Purelib.Riemann.Normalization
/-- The dyadic horizontal energy boundary distributes over the original coefficient family and its conjugate.

The dyadic split keeps the original endpoints and fixed vertical coordinate. Every ordered coefficient pair contributes
at the same subdivision depth. -/
theorem horizontalBoundary_energy_combination (depth : Nat) (lower upper fixed : InverseRootPolynomial.Coordinate) :
    PreparedBoxBoundary.horizontalBoundary (fun point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun
      row => coefficients row * values row point)))
      depth lower upper fixed =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        PreparedBoxBoundary.horizontalBoundary (fun point => ⟨conj (values i point), values j point⟩) depth lower upper
          fixed)) := by
  induction depth generalizing lower upper with
  | zero => exact Rectangle.ClippedEnergyCombination.PolygonStokes.edgeArea_energy_combination coefficients _ _
  | succ depth ih =>
      simp only [PreparedBoxBoundary.horizontalBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [ih, ih]

/-- The dyadic vertical energy boundary distributes over the original coefficient family and its conjugate.

The dyadic split keeps the original endpoints and fixed horizontal coordinate. Every ordered coefficient pair
contributes at the same subdivision depth. -/
theorem verticalBoundary_energy_combination (depth : Nat) (lower upper fixed : InverseRootPolynomial.Coordinate) :
    PreparedBoxBoundary.verticalBoundary (fun point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun
      row => coefficients row * values row point)))
      depth lower upper fixed =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        PreparedBoxBoundary.verticalBoundary (fun point => ⟨conj (values i point), values j point⟩) depth lower upper
          fixed)) := by
  induction depth generalizing lower upper with
  | zero => exact Rectangle.ClippedEnergyCombination.PolygonStokes.edgeArea_energy_combination coefficients _ _
  | succ depth ih =>
      simp only [PreparedBoxBoundary.verticalBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [ih, ih]

/-- The rectangular energy boundary distributes into conjugate-left times right coefficient pair boundaries.

All four box sides keep their original orientation and subdivision depth. Conjugation applies solely to the left factors
in the coefficient expansion. -/
theorem rectangleBoundary_energy_combination (depth : Nat) (box : InverseRootPolynomial.Box) :
    PreparedBoxBoundary.rectangleBoundary (fun point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun
      row => coefficients row * values row point))) depth box =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        PreparedBoxBoundary.rectangleBoundary (fun point => ⟨conj (values i point), values j point⟩) depth box)) := by
  simp only [PreparedBoxBoundary.rectangleBoundary, mul_add, mul_sub, FiniteSum.Fin.sumFin_add,
    FiniteSum.Fin.sumFin_sub]
  rw [horizontalBoundary_energy_combination,
    verticalBoundary_energy_combination,
    horizontalBoundary_energy_combination,
      verticalBoundary_energy_combination]

end

end Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.PreparedBoxPartitions

namespace Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.ObservationPieces

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr
variable {columns rows count : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns
  rows}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Polynomial in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Normalization in
/-- The retained observation pieces' local energy boundary is the double weighted sum of pair boundaries.

The original pieces, polynomial values and subdivision depth are shared by every term, with conjugation applied only to
the left coefficient and left value. -/
theorem localBoundary_energy_combination {boxes : List InverseRootPolynomial.Box} (pieces :
  RectangularObservationMesh.ObservationPieces geometry boxes)
    (coefficients : Fin count → Basic.Canonical)
    (values : Fin count → Fin (columns + 1) → Fin (rows + 1) → Basic.Canonical → Basic.Canonical) (depth : Nat) :
    pieces.localBoundary (fun column row point => Energy.Polygon.energyPrimitivePoint
      (FiniteSum.Fin.sumFin (fun i => coefficients i * values i column row point))) depth =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => Data.Gaussian.Basic.conj (coefficients i) *
        coefficients
        j *
        pieces.localBoundary (fun column row point => ⟨conj (values i column row point), values j column row point⟩)
          depth)) := by
  induction pieces with
  | nil =>
      conv_lhs => simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_zero,
        FiniteSum.Fin.sumFin_zero]
      conv_rhs => simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_zero,
        FiniteSum.Fin.sumFin_zero]
  | cons column row refines tail ih =>
      simp only [RectangularObservationMesh.ObservationPieces.localBoundary, mul_add, FiniteSum.Fin.sumFin_add]
      rw [Rectangle.ClippedEnergyCombination.PreparedBoxPartitions.rectangleBoundary_energy_combination, ih]

end Purelib.Integration.Polynomial.Rectangle.ClippedEnergyCombination.ObservationPieces

end
