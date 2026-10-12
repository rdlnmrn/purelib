module
import Purelib.Algebra.Group.Negation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SheetGauge
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CellNegation
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison

section

open Purelib

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Data.Rat

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration.RectangularPrimitiveModels

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-!
# Opposite-sheet increments in the existing shared face domains

The two domains may retain different axes, cells and polynomial indices.
On any edge contained in a cell from each sheet, their actual primitive
increments sum to a requested error. The existing gauge and root transport
proofs supply the sign throughout both domains, including non-origin cells.
-/

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank}

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition line_one line_zero)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAccuracy)
open Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain

/-- Read the retained oriented inverse-root model at the supplied domain cell and polynomial stage. -/
@[expose] def cellModel
    {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (index : Nat) (column row : Fin (domain.steps + 1)) :
    InverseRootPolynomial.Model curve.polynomial (domain.geometry.box column row) :=
  ((Transitions.oriented
    (domain.patch.sheets.refine index).transitions (domain.patch.sheets.refine index).gauge).ready column row).model

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

/-- The oriented cell polynomial has the same value as the exact transported model refined two stages further. -/
private theorem cell_value {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (differential : Differentials.Basic.Differential genus)
    (index : Nat) (column row : Fin (domain.steps + 1)) (point : Data.Gaussian.Basic.Canonical) :
    (domain.cellModel index column row).value.eval point =
      ((domain.patch.transported.cell column row).model.refine (index + 2)).value.eval point :=
  SheetGauge.oriented_value domain.patch differential index column row point

/-- The oriented cell model keeps exactly the bound of the retained coarse model refined to this stage. -/
private theorem cell_bound {models : BranchCellBank.FaceModels frames face} {sheet : Fin 2}
    (domain : Periods.PeriodDomain models sheet) (index : Nat) (column row : Fin (domain.steps + 1)) :
    (domain.cellModel index column row).bound =
      ((domain.patch.models.ready column row).model.refine index).bound := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain.cellModel,
    Transitions.oriented,
    Bank.orient_bound]
  exact (domain.patch.models.refine_bound index column row).trans
    ((domain.patch.models.ready column row).model.refine_bound index).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains

/-- The actual cached models have a negative transition on any common edge. No source-sign, winding, or canonical-gauge
premise is supplied. -/
@[expose] def cellTransition
    (domains : DomainBanks.FaceDomains frames face) (differential : Differentials.Basic.Differential genus)
    (leftColumn leftRow : Fin ((domains.domain 0).steps + 1))
    (rightColumn rightRow : Fin ((domains.domain 1).steps + 1)) (leftIndex rightIndex : Nat)
    (start finish : Data.Gaussian.Basic.Canonical)
    (leftStart : ((domains.domain 0).geometry.box leftColumn leftRow).Contains start)
    (leftFinish : ((domains.domain 0).geometry.box leftColumn leftRow).Contains finish)
    (rightStart : ((domains.domain 1).geometry.box rightColumn rightRow).Contains start)
    (rightFinish : ((domains.domain 1).geometry.box rightColumn rightRow).Contains finish) :
    InverseModelEdgeTransition.EdgeTransition
      ((domains.domain 0).cellModel leftIndex leftColumn leftRow)
      ((domains.domain 1).cellModel rightIndex rightColumn rightRow) start finish where
  leftStart := leftStart
  leftFinish := leftFinish
  rightStart := rightStart
  rightFinish := rightFinish
  sample :=
    let first := ((domains.domain 0).cellModel leftIndex leftColumn leftRow).value.eval start
    let second := ((domains.domain 1).cellModel rightIndex rightColumn rightRow).value.eval start
    ⟨first, rfl, second, rfl, ⟨true, -second, rfl, by
      dsimp only [first, second]
      rw [Data.Gaussian.Basic.Canonical.sub_eq_add_neg, neg_neg,
        ← Data.Gaussian.Basic.sub_eq_add_neg,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation.cell_value (domains.domain 0) differential,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation.cell_value (domains.domain 1) differential]
      have scalar := CellNegation.opposite_cells_nearest
        ((domains.domain 0).patch.transported.cell leftColumn leftRow)
        ((domains.domain 1).patch.transported.cell rightColumn rightRow)
        differential leftStart rightStart leftIndex rightIndex
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar⟩⟩

/-- The values are the retained primitives used by face sewing and period comparison. Their same-oriented increment sum
pays both residual budgets. -/
theorem cell_primitive_sum_le
    (domains : DomainBanks.FaceDomains frames face)
    {differential : Differentials.Basic.Differential genus} {leftIndex rightIndex : Nat}
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftColumn leftRow : Fin ((domains.domain 0).steps + 1))
    (rightColumn rightRow : Fin ((domains.domain 1).steps + 1))
    (bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds
      (face.clearance.restrict ((domains.domain 0).patch.transported.cell leftColumn leftRow).geometry.refines)
      (PreparedPrimitiveSamples.differentialNumerator differential))
    (start finish : Data.Gaussian.Basic.Canonical)
    (leftStart : ((domains.domain 0).geometry.box leftColumn leftRow).Contains start)
    (leftFinish : ((domains.domain 0).geometry.box leftColumn leftRow).Contains finish)
    (rightStart : ((domains.domain 1).geometry.box rightColumn rightRow).Contains start)
    (rightFinish : ((domains.domain 1).geometry.box rightColumn rightRow).Contains finish) :
    Data.Gaussian.Norm.Basic.normSq ((first.primitives.value leftColumn leftRow finish - first.primitives.value
      leftColumn leftRow start) +
      (second.primitives.value rightColumn rightRow finish - second.primitives.value rightColumn rightRow start)) ≤
      12 * (((domains.domain 0).cellModel leftIndex leftColumn leftRow).bound +
        ((domains.domain 1).cellModel rightIndex rightColumn rightRow).bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * Data.Gaussian.Norm.Basic.normSq (finish - start) := by
  let edge := domains.cellTransition differential
    leftColumn leftRow rightColumn rightRow leftIndex rightIndex
    start finish leftStart leftFinish rightStart rightFinish
  have estimate := EdgeTransition.primitive_increment_le
    edge bounds (first.primitives.dense leftColumn leftRow)
    (second.primitives.dense rightColumn rightRow)
    (first.primitives.coefficient_eq leftColumn leftRow) (second.primitives.coefficient_eq rightColumn rightRow)
    (first := 1) (last := 0) ⟨by decide, le_rfl⟩ ⟨le_rfl, by decide⟩
  have sign : edge.sign = -1 := rfl
  rw [sign, InverseModelEdgeTransition.line_one, InverseModelEdgeTransition.line_zero] at estimate
  have same (a b : Data.Gaussian.Basic.Canonical) : a - (-1) * b = a + b := by ring1
  rw [same] at estimate
  have scalar := estimate.trans_eq (by rw [show (1 : Fraction.Rational) - 0 = 1 by ring1, one_pow,
    Fraction.Field.mul_one_direct])
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, Primitives.dense, Primitives.value] using scalar

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomains

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

/-- One existing executable edge request pays the actual two-domain sum at every pair of later polynomial indices. It
reuses the cached coarse bounds. -/
theorem FaceDomains.cell_primitive_sum_accurate (domains : DomainBanks.FaceDomains frames face)
    {differential : Differentials.Basic.Differential genus} {leftIndex rightIndex : Nat}
    (leftColumn leftRow : Fin ((domains.domain 0).steps + 1))
    (rightColumn rightRow : Fin ((domains.domain 1).steps + 1))
    {start finish : Data.Gaussian.Basic.Canonical} {target : InverseRootPolynomial.Coordinate}
    {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds
      (face.clearance.restrict ((domains.domain 0).patch.transported.cell leftColumn leftRow).geometry.refines)
      (PreparedPrimitiveSamples.differentialNumerator differential)}
    (request : PrimitiveEdgeComparison.PrimitiveEdgeAccuracy bounds ((domains.domain 0).patch.models.ready leftColumn
      leftRow).model
      ((domains.domain 1).patch.models.ready rightColumn rightRow).model start finish target)
    (first : PrimitiveData.DomainPrimitives (domains.domain 0) differential leftIndex)
    (second : PrimitiveData.DomainPrimitives (domains.domain 1) differential rightIndex)
    (leftStart : ((domains.domain 0).geometry.box leftColumn leftRow).Contains start)
    (leftFinish : ((domains.domain 0).geometry.box leftColumn leftRow).Contains finish)
    (rightStart : ((domains.domain 1).geometry.box rightColumn rightRow).Contains start)
    (rightFinish : ((domains.domain 1).geometry.box rightColumn rightRow).Contains finish)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq ((first.primitives.value leftColumn leftRow finish - first.primitives.value
      leftColumn leftRow start) +
      (second.primitives.value rightColumn rightRow finish - second.primitives.value rightColumn rightRow start)) <
        target := by
  have bound := domains.cell_primitive_sum_le first second leftColumn leftRow rightColumn rightRow
    bounds start finish leftStart leftFinish rightStart rightFinish
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation.cell_bound,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation.cell_bound] at bound
  have leftBound := (((domains.domain 0).patch.models.ready leftColumn leftRow).model.refine_bound leftIndex).trans_le
    ((quarterRadius_antitone
      ((domains.domain 0).patch.models.ready leftColumn leftRow).model.bound_nonnegative leftLater).trans_eq
      (((domains.domain 0).patch.models.ready leftColumn leftRow).model.refine_bound request.index).symm)
  have rightBound := (((domains.domain 1).patch.models.ready rightColumn rightRow).model.refine_bound
    rightIndex).trans_le
    ((quarterRadius_antitone
      ((domains.domain 1).patch.models.ready rightColumn rightRow).model.bound_nonnegative rightLater).trans_eq
      (((domains.domain 1).patch.models.ready rightColumn rightRow).model.refine_bound request.index).symm)
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply bound.trans_lt
  apply lt_of_le_of_lt _ request.refined_scale_lt
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
    (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - start))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveNegation

end
