module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Sampling
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Quadrature
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Paid finite bank boundary differences against unchanged original chart samples

Each actual cell certificate uses the original shared endpoint bank and its
independent spatial derivative observation. Its arithmetic Taylor payment
and the original same-source refined-versus-old cell payment derive a fixed
fourth-power spatial ceiling. Original finite quadrance summation and dyadic
count cancellation then contract that bound.

The exact telescope keeps both independently selected boundary witnesses.
The integral sample is the original cached Layer model's literal finite sum.
There is no returning-sheet, FTC, geometric integral, canonical integral or
parameter-derivative conclusion.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Layer Piece)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Integration

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}
variable {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
variable {samples : Differential.Refinement.Layer.RefinedSamples layer initialPositive}
variable {upper : Transport.Reading actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)}
variable {bank : Bank primitive samples upper}
variable {chain : Partition.Interval.Chain initial.span.lower initial.span.upper
  (Differential.Refinement.Piece.chartIntervals layer.pieces)}

section Uniform

variable (specification)

/-- Original observed Taylor, derivative arithmetic and cell-refinement budgets compute one fixed spatial ceiling. -/
def cellCeiling {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) : Fraction.Rational :=
  4 * (Taylor.Observation.ceiling site parameter primitive specification initial.cell.regular +
    Taylor.Observation.derivativeCeiling site parameter specification) +
    2 * Differential.Refinement.Layer.refinementCeiling initial

/-- The same original regularity and coefficient budgets make the computed spatial cell ceiling nonnegative. -/
theorem cellCeiling_nonnegative {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) :
    0 ≤ cellCeiling specification initial :=
  Arithmetic.add_le_add_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Taylor.Observation.ceiling_nonnegative site parameter primitive specification initial.cell.regular)
        (Taylor.Observation.derivativeCeiling_nonnegative site parameter specification initial.cell.regular)))
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Differential.Refinement.Layer.refinementCeiling_nonnegative initial))

end Uniform

namespace Cell

/-- The actual selected bank increment pays its finite error against the literal unchanged original cell sample.

The original observed certificate first pays the identical later scalar
cell. The existing Layer comparison then pays that actual refined sample's
difference from the retained old sample; neither is replaced or redefined.
-/
theorem integral_error_le {index : Fin layer.pieces.length} (cache : Cell specification bank chain index) :
    Norm.Basic.normSq (bank.increment index - (layer.node index).cell.cell.integralSample) ≤
      cellCeiling specification initial * (layer.node index).span.width ^ 4 := by
  have arithmetic := cache.refined_integral_error_le
  have original := layer.refined_integral_error_le initialPositive (layer.node index)
    (List.getElem_mem index.isLt) (samples.get index)
  have decomposition : bank.increment index - (layer.node index).cell.cell.integralSample =
      (bank.increment index - (samples.get index).val.cell.integralSample) +
        ((samples.get index).val.cell.integralSample - (layer.node index).cell.cell.integralSample) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct arithmetic original)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq (by unfold cellCeiling; ring1))

end Cell

namespace Cells

/-- Each actual finite error uses the shared bank increment and the unchanged original cell integral sample. -/
def integralError (_cells : Cells specification bank chain) (index : Fin layer.pieces.length) : Canonical :=
  bank.increment index - (layer.node index).cell.cell.integralSample

/-- Sum those actual finite errors in the same original retained parent-index order. -/
def integralErrorSum (cells : Cells specification bank chain) : Canonical :=
  FiniteSum.Fin.sumFin (fun index => cells.integralError index)

/-- Shared endpoint observations telescope exactly while retaining the original cached path's literal integral sum. -/
theorem integralErrorSum_eq (cells : Cells specification bank chain) :
    cells.integralErrorSum =
      bank.terminal.entry.value - (bank.nodes.get ⟨0, layer.nonempty⟩).value - layer.model.integralSample := by
  unfold integralErrorSum integralError
  rewrite [FiniteSum.Fin.sumFin_sub]
  change bank.incrementSum -
    FiniteSum.Fin.sumFin (fun index : Fin layer.pieces.length =>
      (layer.node index).cell.cell.integralSample) = _
  rewrite [bank.incrementSum_eq, ← layer.integralSample_eq_sumFin]
  rfl

/-- All stored actual cell errors pay the original dyadic count twice and a uniformly contracting spatial allowance. -/
theorem integralErrorSum_le (cells : Cells specification bank chain) :
    Norm.Basic.normSq cells.integralErrorSum ≤
      cellCeiling specification initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
  have bounded (index : Fin layer.pieces.length) :
      Norm.Basic.normSq (cells.integralError index) ≤
        cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
    have paid := (cells.get index).integral_error_le
    have member : layer.node index ∈ layer.pieces := List.getElem_mem index.isLt
    have fourth : (layer.node index).span.width ^ 4 =
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2 := by
      calc
        _ = ((layer.node index).span.width ^ 2) ^ 2 := by ring1
        _ = _ := congrArg (fun value : Fraction.Rational => value ^ 2) (layer.widths (layer.node index) member)
    exact paid.trans_eq (congrArg (fun value : Fraction.Rational => cellCeiling specification initial * value) fourth)
  have sumBound := Norm.Sum.Indexed.normSq_sumFin_le (fun index => cells.integralError index)
    (cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) bounded
  have countCast : (layer.pieces.length : Fraction.Rational) = ((2 ^ depth : Nat) : Fraction.Rational) :=
    congrArg (fun count : Nat => (count : Fraction.Rational)) layer.count
  have cancellation : (layer.pieces.length : Fraction.Rational) ^ 2 *
      (cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth ^ 2) =
      cellCeiling specification initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
    rewrite [countCast]
    calc
      _ = (cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          (((2 ^ depth : Nat) : Fraction.Rational) *
            (((2 ^ depth : Nat) : Fraction.Rational) *
              Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)) := by ring1
      _ = (cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) *
          initial.span.width ^ 2 := congrArg
        (fun value : Fraction.Rational =>
          (cellCeiling specification initial * Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth) * value)
        (Geometric.DyadicCount.dyadic_count_cancel (initial.span.width ^ 2) depth)
      _ = _ := by ring1
  exact sumBound.trans_eq cancellation

/-- Both original selected boundary witnesses approximate the unchanged finite path sample at the paid allowance. -/
theorem boundary_error_le (cells : Cells specification bank chain) :
    Norm.Basic.normSq
      (bank.terminal.entry.value - (bank.nodes.get ⟨0, layer.nonempty⟩).value - layer.model.integralSample) ≤
      cellCeiling specification initial * initial.span.width ^ 2 *
        Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth := by
  rewrite [← cells.integralErrorSum_eq]
  exact cells.integralErrorSum_le

end Cells

section Uniform

variable (specification)

/-- The original initial span and actual cell ceiling compute the scale of the finite spatial contraction. -/
def errorScale {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) : Fraction.Rational :=
  cellCeiling specification initial * initial.span.width ^ 4

/-- The retained finite contraction scale is nonnegative under the same original regularity and request. -/
theorem errorScale_nonnegative {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy) :
    0 ≤ errorScale specification initial :=
  Arithmetic.mul_nonneg_direct (cellCeiling_nonnegative specification initial)
    ((Arithmetic.sq_nonneg_direct (initial.span.width * initial.span.width)).trans_eq (by ring1))

/-- Retain the original finite depth search and its actual stopping/payment certificate for the computed cell scale. -/
def errorSelection {initialAccuracy : AccuracyRequest} (initial : Piece data actual initialAccuracy)
    (current : Nat) (request : AccuracyRequest) :
    Geometric.Search.Selection (errorScale specification initial) current request.tolerance :=
  Geometric.Search.Selection.build (errorScale specification initial) (errorScale_nonnegative specification initial)
    current request.tolerance request.positive

end Uniform

/-- This actual retained bank and cell-cache family meet the finite request at or after the original selected depth. -/
theorem Cells.requested_error_lt (cells : Cells specification bank chain)
    {current : Nat} (request : AccuracyRequest)
    (selection : Geometric.Search.Selection (errorScale specification initial) current request.tolerance)
    (after : selection.stage ≤ depth) :
    Norm.Basic.normSq
      (bank.terminal.entry.value - (bank.nodes.get ⟨0, layer.nonempty⟩).value - layer.model.integralSample) <
      request.tolerance := by
  have allowance := selection.later_accurate after
  have equal : cellCeiling specification initial * initial.span.width ^ 2 *
      Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth =
      Geometric.Basic.quarterRadius (errorScale specification initial) depth := by
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold errorScale
    ring1
  exact cells.boundary_error_le.trans_lt (equal.trans_lt allowance)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank

end
