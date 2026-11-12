module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Finite coefficient expansion with the complete basis-pair count paid. -/
namespace Purelib.Riemann.Periods.BilinearCombination

open Purelib.Topology.Polygon.Stokes (OrientedEdge edgeArea edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub sumFin_mul_left sumFin_mul_right)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul normSq_nonneg)

attribute [local congr] sumFin_congr

section
open Purelib.Algebra
open Purelib.Topology
open Purelib.Data
/-- Expand an edge's bilinear area under two independent finite coefficient vectors.

The exact double sum retains every ordered pair of left and right basis values at both endpoints. -/
theorem edgeArea_combination {leftCount rightCount : Nat}
    (left : Fin leftCount → Canonical) (right : Fin rightCount → Canonical)
    (firstLeft lastLeft : Fin leftCount → Canonical) (firstRight lastRight : Fin rightCount →
      Canonical) :
    edgeArea ⟨sumFin (fun row => left row * firstLeft row), sumFin (fun row => right row *
      firstRight row)⟩
      ⟨sumFin (fun row => left row * lastLeft row), sumFin (fun row => right row * lastRight row)⟩ =
      sumFin (fun first => sumFin (fun second => left first * right second *
        edgeArea ⟨firstLeft first, firstRight second⟩ ⟨lastLeft first, lastRight second⟩)) := by
  have expanded := sumFin_congr (fun first : Fin leftCount => sumFin_congr
    (fun second : Fin rightCount => show left first * right second *
      edgeArea ⟨firstLeft first, firstRight second⟩ ⟨lastLeft first, lastRight second⟩ =
        (left first * firstLeft first) * (right second * lastRight second) -
        (left first * lastLeft first) * (right second * firstRight second) by
      simp only [edgeArea]
      ring1))
  rw [expanded]
  conv_lhs => simp only [sumFin_sub, sumFin_mul_left, sumFin_mul_right,
    edgeArea]
  conv_rhs => simp only [sumFin_sub, sumFin_mul_left, sumFin_mul_right,
    edgeArea]

/-- Expand a finite edge-word area into all coefficient-weighted basis-pair areas.

The same ordered word is used for every pair, preserving all endpoint contributions. -/
theorem edgeListArea_combination {leftCount rightCount vertices : Nat}
    (left : Fin leftCount → Canonical) (right : Fin rightCount → Canonical)
    (first : Fin leftCount → Fin vertices → Canonical) (second : Fin rightCount → Fin vertices →
      Canonical)
    (word : List (OrientedEdge vertices)) :
    edgeListArea (fun vertex => ⟨sumFin (fun row => left row * first row vertex),
      sumFin (fun row => right row * second row vertex)⟩) word =
      sumFin (fun i => sumFin (fun j => left i * right j * edgeListArea (fun
        vertex => ⟨first i vertex, second j vertex⟩) word)) := by
  induction word with
  | nil =>
      conv_lhs => simp only [edgeListArea, mul_zero, FiniteSum.Fin.sumFin_zero]
      conv_rhs => simp only [edgeListArea, mul_zero, FiniteSum.Fin.sumFin_zero]
  | cons edge word ih =>
      simp only [edgeListArea, mul_add, sumFin_add]
      rw [edgeArea_combination, ih]

end

open Purelib.Algebra
open Purelib.Data
/-- Bound a coefficient-weighted bilinear error by both coefficient quadrance sums and the complete pair count.

Every displayed basis-pair error has quadrance at most the same target. The bound pays leftCount times rightCount before
multiplying the two coefficient sums and target. -/
theorem combination_bound {leftCount rightCount : Nat}
    (left : Fin leftCount → Canonical) (right : Fin rightCount → Canonical)
    (errors : Fin leftCount → Fin rightCount → Canonical) {target : Rat.Fraction.Rational}
    (bounded : ∀ first second, normSq (errors first second) ≤ target) :
    normSq (sumFin (fun first => sumFin (fun second => left
      first * right second * errors first second))) ≤
      ((leftCount : Rat.Fraction.Rational) * (rightCount : Rat.Fraction.Rational)) *
        sumFin (fun first => normSq (left first)) * sumFin (fun
          second => normSq (right second)) * target := by
  have pointwise (first : Fin leftCount) (second : Fin rightCount) :
      normSq (left first * right second * errors first second) ≤
        normSq (left first) * normSq (right second) * target
        := by
    rw [normSq_mul, normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded first second)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (normSq_nonneg _)
        (normSq_nonneg _))
  have inner (first : Fin leftCount) := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun second => left first * right second * errors first second)
    (fun second => normSq (left first) * normSq (right second)
      * target) (pointwise first)
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun first => sumFin (fun second => left first * right second * errors first second))
    (fun first => (rightCount : Rat.Fraction.Rational) *
      sumFin (fun second => normSq (left first) *
        normSq (right second) * target)) inner
  apply estimate.trans_eq
  simp only [sumFin_mul_right, sumFin_mul_left]
  ring1

/-- Interchange finite entry summation with bilinear coefficient combination.

The two coefficient vectors are independent of the entry index, and all three finite index sets are retained. -/
theorem sumFin_combination {count leftCount rightCount : Nat}
    (left : Fin leftCount → Canonical) (right : Fin rightCount → Canonical)
    (errors : Fin count → Fin leftCount → Fin rightCount → Canonical) :
    sumFin (fun entry => sumFin (fun first => sumFin (fun second => left first
      * right second * errors entry first second))) =
      sumFin (fun first => sumFin (fun second => left first * right second *
        sumFin (fun entry => errors entry first second))) := by
  rw [FiniteSum.Fin.sumFin_swap]
  apply sumFin_congr
  intro first
  rw [FiniteSum.Fin.sumFin_swap]
  apply sumFin_congr
  intro second
  exact sumFin_mul_left _ _

end Purelib.Riemann.Periods.BilinearCombination

end
