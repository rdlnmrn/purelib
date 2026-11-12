module

public import Purelib.Polynomial.Dense.Division.Synthetic
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-!
# Quantitative interpolation at separated Gaussian rational nodes

The original synthetic division removes one coefficient slot at each actual
node. Its retained remainder is the original polynomial value at that node.
Uniform sample and node-separation bounds therefore control evaluation on the
whole rational unit disk by an explicit finite recurrence.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Interpolation

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The finite amplification of sample quadrances on separated interpolation nodes.

The radius bounds every original node quadrance and the positive separation
bounds every distinct node-pair quadrance. One original synthetic division
contributes the next displayed affine amplification.
-/
@[expose] public def amplification (radius separation : Rational) : Nat → Rational
  | 0 => 0
  | count + 1 => 2 + (16 * (1 + radius) / separation) * amplification radius separation count

/-- Nonnegative node radius and positive separation give nonnegative amplification. -/
public theorem amplification_nonnegative {radius separation : Rational}
    (radiusNonnegative : 0 ≤ radius) (separationPositive : 0 < separation) (count : Nat) :
    0 ≤ amplification radius separation count := by
  induction count with
  | zero => exact le_refl _
  | succ count inductionHypothesis =>
      exact (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
        (Arithmetic.mul_nonneg_direct
          (Field.div_nonneg_direct
            (Arithmetic.mul_nonneg_direct (by decide)
              (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) radiusNonnegative).le)
            separationPositive.le)
          inductionHypothesis)).le

set_option genInjectivity false in
/-- The actual original synthetic divisions at one ordered finite node list.

Each step retains its complete original result and its defining equation.
The next step consumes that same retained quotient, so no later bound or
readback performs a replacement division.
-/
public inductive Expansion : CoefficientPolynomial → List Canonical → Type
  /-- No interpolation node requires no division. -/
  | nil {polynomial : CoefficientPolynomial} : Expansion polynomial []
  /-- Retain one original division and continue with its actual quotient. -/
  | cons {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
      (division : Division.Synthetic.Result polynomial node)
      (division_eq : division = Division.Synthetic.divide polynomial node)
      (tail : Expansion division.quotient remaining) : Expansion polynomial (node :: remaining)

namespace Expansion

/-- Materialize the original synthetic division chain at the given ordered nodes. -/
@[expose] public def prepare (polynomial : CoefficientPolynomial) :
    (nodes : List Canonical) → Expansion polynomial nodes
  | [] => .nil
  | node :: remaining =>
      let division := Division.Synthetic.divide polynomial node
      .cons division rfl (prepare division.quotient remaining)

/-- Read the complete first retained original division at a nonempty node list. -/
@[expose] public def first {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical} :
    Expansion polynomial (node :: remaining) → Division.Synthetic.Result polynomial node
  | .cons division _ _ => division

/-- The first retained division is the complete original constructor result. -/
public theorem first_eq {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    (expansion : Expansion polynomial (node :: remaining)) :
    expansion.first = Division.Synthetic.divide polynomial node := by
  cases expansion with
  | cons _ equation _ => exact equation

/-- Read the retained tail whose source is the same stored first quotient. -/
@[expose] public def next {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    (expansion : Expansion polynomial (node :: remaining)) : Expansion expansion.first.quotient remaining :=
  match expansion with
  | .cons _ _ tail => tail

/-- The same first retained quotient inherits the finite residual payment on every remaining original node.

A positive squared-distance floor separates the first actual node from every
actual tail node. The retained original synthetic evaluation and remainder
identities therefore bound each tail residual by four times the input sample
budget divided by that same floor. No division or sample is recomputed.
-/
public theorem next_samples_le {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    (expansion : Expansion polynomial (node :: remaining)) {separation residual : Rational}
    (separationPositive : 0 < separation)
    (separated : (node :: remaining).Pairwise (fun left right =>
      separation ≤ Norm.Basic.normSq (left - right)))
    (samples : ∀ point ∈ node :: remaining, Norm.Basic.normSq (polynomial.eval point) ≤ residual) :
    ∀ point ∈ remaining, Norm.Basic.normSq (expansion.first.quotient.eval point) ≤ 4 * residual / separation := by
  let division := expansion.first
  have pairwise := List.pairwise_cons.mp separated
  have rootSample := samples node List.mem_cons_self
  intro other member
  have distance := pairwise.1 other member
  rw [Norm.Bounds.normSq_sub_symm node other] at distance
  have reconstruction : (other - node) * division.quotient.eval other =
      polynomial.eval other - polynomial.eval node := by
    rw [division.eval_eq other, division.remainder_eval]
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im] <;> ring1
  have productBound : Norm.Basic.normSq (other - node) *
      Norm.Basic.normSq (division.quotient.eval other) ≤ 4 * residual := by
    rw [← Norm.Basic.normSq_mul, reconstruction]
    calc
      _ ≤ 2 * (Norm.Basic.normSq (polynomial.eval other) +
          Norm.Basic.normSq (polynomial.eval node)) :=
        Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (residual + residual) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct
            (samples other (List.mem_cons_of_mem node member)) rootSample)
          (by decide)
      _ = 4 * residual := by ring1
  apply (Field.le_div_iff_pos separationPositive).mpr
  calc
    Norm.Basic.normSq (division.quotient.eval other) * separation =
        separation * Norm.Basic.normSq (division.quotient.eval other) := by ring1
    _ ≤ Norm.Basic.normSq (other - node) *
        Norm.Basic.normSq (division.quotient.eval other) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct distance (Norm.Basic.normSq_nonneg _)
    _ ≤ 4 * residual := productBound

/-- Separated sample residuals control evaluation on the complete rational unit disk.

The source has at most as many retained coefficient slots as interpolation
nodes. Every node stays in the same quadrance bound; every ordered distinct
node pair has the same positive squared-distance floor. The estimate uses
only the actual divisions retained by this expansion.
-/
public theorem normSq_eval_le {polynomial : CoefficientPolynomial}
    {nodes : List Canonical} (expansion : Expansion polynomial nodes)
    {radius separation residual : Rational}
    (radiusNonnegative : 0 ≤ radius) (separationPositive : 0 < separation)
    (residualNonnegative : 0 ≤ residual)
    (lengthBound : polynomial.coeffs.length ≤ nodes.length)
    (nodeBounds : ∀ node ∈ nodes, Norm.Basic.normSq node ≤ radius)
    (separated : nodes.Pairwise (fun left right =>
      separation ≤ Norm.Basic.normSq (left - right)))
    (samples : ∀ node ∈ nodes, Norm.Basic.normSq (polynomial.eval node) ≤ residual)
    {point : Canonical} (unitDisk : Norm.Basic.normSq point ≤ 1) :
    Norm.Basic.normSq (polynomial.eval point) ≤
      residual * amplification radius separation nodes.length := by
  induction expansion generalizing radius separation residual with
  | @nil polynomial =>
      have empty : polynomial.coeffs = [] := by
        cases source : polynomial.coeffs with
        | nil => rfl
        | cons leading remaining =>
            rw [source] at lengthBound
            exact False.elim (Nat.not_succ_le_zero _ lengthBound)
      change Norm.Basic.normSq
        (Dense.Basic.DensePolynomial.evalCoeffs point polynomial.coeffs) ≤ residual * 0
      rewrite [empty, Dense.Basic.DensePolynomial.evalCoeffs_nil, Norm.Basic.normSq_zero,
        Rat.Fraction.Field.mul_zero_direct]
      exact le_refl _
  | @cons polynomial node remaining division divisionEq tail inductionHypothesis =>
      have pairwise := List.pairwise_cons.mp separated
      have rootSample := samples node List.mem_cons_self
      have rootBound := nodeBounds node List.mem_cons_self
      let nextResidual := 4 * residual / separation
      have nextNonnegative : 0 ≤ nextResidual := Field.div_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide) residualNonnegative) separationPositive.le
      have quotientLength : division.quotient.coeffs.length ≤ remaining.length := by
        rw [division.quotient_length]
        change polynomial.coeffs.length ≤ remaining.length + 1 at lengthBound
        omega0
      have quotientSamples : ∀ other ∈ remaining,
          Norm.Basic.normSq (division.quotient.eval other) ≤ nextResidual :=
        (Expansion.cons division divisionEq tail).next_samples_le separationPositive separated samples
      have quotientBound := inductionHypothesis radiusNonnegative separationPositive nextNonnegative
        quotientLength (fun other member => nodeBounds other (List.mem_cons_of_mem node member))
        pairwise.2 quotientSamples
      have differenceBound : Norm.Basic.normSq (point - node) ≤ 2 * (1 + radius) :=
        (Norm.Bounds.normSq_sub_le_two point node).trans
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.add_le_add_direct unitDisk rootBound) (by decide))
      rw [division.eval_eq point, division.remainder_eval]
      calc
        _ ≤ 2 * (Norm.Basic.normSq ((point - node) * division.quotient.eval point) +
            Norm.Basic.normSq (polynomial.eval node)) :=
          Norm.Bounds.normSq_add_le_two _ _
        _ = 2 * (Norm.Basic.normSq (point - node) *
            Norm.Basic.normSq (division.quotient.eval point) +
            Norm.Basic.normSq (polynomial.eval node)) := by
          rw [Norm.Basic.normSq_mul]
        _ ≤ 2 * ((2 * (1 + radius)) *
            (nextResidual * amplification radius separation remaining.length) + residual) := by
          apply Arithmetic.mul_le_mul_of_nonneg_left_direct
          · apply Arithmetic.add_le_add_direct _ rootSample
            exact Arithmetic.mul_le_mul_direct differenceBound quotientBound
              (Norm.Basic.normSq_nonneg _)
              (Arithmetic.mul_nonneg_direct (by decide)
                (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) radiusNonnegative).le)
          · decide
        _ = residual * amplification radius separation (node :: remaining).length := by
          simp only [List.length_cons, amplification]
          dsimp only [nextResidual]
          rw [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.div_eq_mul_inv_direct]
          ring1

end Expansion
end Purelib.Polynomial.Dense.Gaussian.Interpolation
