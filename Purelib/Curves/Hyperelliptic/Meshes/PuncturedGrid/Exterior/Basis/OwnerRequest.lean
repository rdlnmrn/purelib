module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Riemann.Readings.RectangularPointOwnerBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

/-! A shared finite owner-error request for all basis rows, selected before
reading any coefficient vector or fine boundary path. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
public section
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin.Rational (sum_constant)
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Data.Rat.Fraction.Compatibility

namespace OwnerRequest

/-- The retained grid-owner accuracy budget for one original basis row at its count-allocated tolerance.

The tolerance is divided across the exact number of basis rows and the retained grid-owner request; the occurrence
supplies the unchanged geometry and stage floor. -/
@[expose]
def RowOwnerBudget (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (tolerance : Normalization.InverseRootPolynomial.Coordinate) (row : Fin genus) :=
  Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy (occurrence.recastComparison
    (Periods.PeriodMatrix.standardDifferential row)).entered.globalBounds
    (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.domain.steps
    (Rational.Budget.Aggregate.perTerm (tolerance / 4) genus / 4)

end OwnerRequest

/-- The dependent vector of original grid-owner budgets for every basis row on one occurrence.

Each component retains its own basis-row budget and the original occurrence; the dependent vector keeps the row indices
attached to those requests. -/
@[expose]
def OwnerRequest (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (tolerance : Normalization.InverseRootPolynomial.Coordinate) :=
  Data.Vector.DependentVector (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.RowOwnerBudget occurrence
    tolerance)

namespace OwnerRequest
variable {tolerance : Normalization.InverseRootPolynomial.Coordinate}

/-- Allocate every original basis-row owner budget before reading a coefficient vector or fine boundary path.

Positive tolerance gives a positive allocated row budget at every retained index. The resulting requests keep the
occurrence's original grid and basis-row order. -/
@[expose]
def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    (tolerance : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < tolerance) :
      OwnerRequest occurrence tolerance :=
  Data.Vector.DependentVector.ofFn fun _ => Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.build _ _ _
    (Fraction.Order.Field.div_pos_direct (Rational.Budget.Aggregate.perTerm_positive
      (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) <
        4)) genus) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4))

/-- The cached maximum stage of all original basis-row owner requests. -/
@[expose]
def index (owners : OwnerRequest occurrence tolerance) :
  Nat := owners.maximum (fun _ request => request.index)

/-- A retained point reading is close to the same row's aligned cell value at the allocated owner accuracy.

The original point owner, containing cell and common late row budget supply the comparison. -/
theorem row_bound (owners : OwnerRequest occurrence
  tolerance) {faceIndex vertices : Nat}
    (later : owners.index ≤ faceIndex) (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
      occurrence faceIndex) {points : Fin vertices → Normalization.InverseRootPolynomial.Gaussian}
    (row : Fin genus) (readings : Readings.RectangularPointReadings.PointReadings (data row).anchors (data row).offsets
      points)
    (vertex : Fin vertices) (column height : Fin (occurrence.compared.entered.domain.steps + 1))
    (inside : (occurrence.compared.entered.domain.geometry.box column height).Contains (points vertex)) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex - (data row).anchors.alignedValue (data row).offsets
      column height (points vertex)) ≤
      Rational.Budget.Aggregate.perTerm (tolerance / 4) genus := open Purelib.Integration in by
  let selected := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex
    (owners.get row) faceIndex ((owners.get_le_maximum (fun _ request => request.index) row).trans later)
  have bounded := Readings.RectangularPointOwnerBounds.point_cell_bound selected readings
    (occurrence.recastComparison (Periods.PeriodMatrix.standardDifferential row)).entered.domain.patch.cell_refines
    vertex column height inside
  exact bounded.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct selected.accurate.le (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq
    ((show 4 * (Rational.Budget.Aggregate.perTerm (tolerance / 4) genus / 4) =
      (Rational.Budget.Aggregate.perTerm (tolerance / 4) genus / 4) * 4 by ring1).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end OwnerRequest

namespace OwnerRequest

/-- The actual retained point readings for every original basis row on the same finite point vector.

Each row retains its original anchors and offsets on the same finite point vector; no point owner is replaced by another
row's realization. -/
@[expose]
def OwnedReadings {faceIndex vertices : Nat} (data :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex) (points : Fin vertices
  → Normalization.InverseRootPolynomial.Gaussian) :=
  (row : Fin genus) → Readings.RectangularPointReadings.PointReadings (data row).anchors (data row).offsets points

/-- Read the coefficient-weighted sum of the retained basis-row values at one original vertex.

The finite sum uses the retained row readings and the supplied coefficient at each original row index, preserving their
pairing at the selected vertex. -/
@[expose]
def ownedValue {faceIndex vertices : Nat} {data :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex} {points : Fin vertices
  → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data points) (coefficients
      : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (vertex : Fin vertices) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (readings row).values vertex

/-- Every row keeps its actual point owner. The uniform owner request pays
the weighted discrepancy even when adjacent vertices share a coordinate. -/
theorem owned_value_bound {tolerance : Normalization.InverseRootPolynomial.Coordinate} (owners :
  OwnerRequest occurrence tolerance)
    (positive : 0 < tolerance) {faceIndex vertices : Nat} (later : owners.index ≤ faceIndex)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence faceIndex) {points :
      Fin vertices → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data points) (coefficients
      : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (vertex : Fin vertices) (column height : Fin (occurrence.compared.entered.domain.steps + 1))
    (inside : (occurrence.compared.entered.domain.geometry.box column height).Contains (points vertex)) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue
      readings coefficients vertex - FiniteSum.Fin.sumFin (fun row => coefficients row *
      (data row).anchors.alignedValue (data row).offsets column height (points vertex))) ≤
      (tolerance / 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let errors := fun row => (readings row).values vertex -
    (data row).anchors.alignedValue (data row).offsets column height (points vertex)
  let budget := Readings.AffineBasisEnergy.WeightedNormBudget.build errors
  have paid : budget.scale ≤ tolerance / 4 := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row => owners.row_bound later data row (readings row)
        vertex column height inside))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [sum_constant] at bound
    exact bound.trans (Rational.Budget.Aggregate.count_mul_perTerm_lt
      (Fraction.Order.Field.div_pos_direct positive (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)) genus).le
  have equal : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue readings coefficients vertex -
    FiniteSum.Fin.sumFin (fun row => coefficients row *
      (data row).anchors.alignedValue (data row).offsets column height (points vertex)) =
      FiniteSum.Fin.sumFin (fun row => coefficients row * errors row) := by
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.ownedValue
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by dsimp only [errors]; ring1)
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  rw [equal]
  exact (budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid nonnegative).trans_eq (by ring1))

end OwnerRequest

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
