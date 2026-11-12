module

public import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Polynomial.Dense.Reflection

/-!
# Coefficient identities for dense multiplication

The original Horner product satisfies the ring multiplication identities over
any commutative coefficient ring, including rings with zero divisors. One
finite shift algebra reflects the scalar identities back to the actual
normalized coefficient tables.
-/

public section

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Polynomial.Dense
open Purelib.Algebra.Monogenic

variable {K : Type*} [CommRing K] [DecidableEq K]

/-- The original normalized Horner multiplication is associative. -/
theorem mul_assoc (first second third : DensePolynomial K) :
    (first * second) * third = first * (second * third) := by
  have same : ((first * second) * third).normalize = (first * (second * third)).normalize := by
    apply Reflection.normalize_eq
    let left := (first * second) * third
    let right := first * (second * third)
    let dimension := Nat.max left.coeffs.length right.coeffs.length + 1
    let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
    let function := Cyclic.Element.scalar cyclic
    let point := Cyclic.Element.root cyclic
    change (Map.map function left).eval point = (Map.map function right).eval point
    dsimp only [left, right]
    repeat rewrite [Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic)]
    repeat rewrite [eval_mul]
    exact _root_.mul_assoc _ _ _
  exact (normalize_mul _ _).symm.trans (same.trans (normalize_mul _ _))

/-- A scalar factor in the right polynomial scales the same original product. -/
theorem mul_scale (first second : DensePolynomial K) (scalar : K) :
    first * scale scalar second = scale scalar (first * second) := by
  have same : (first * scale scalar second).normalize = (scale scalar (first * second)).normalize := by
    apply Reflection.normalize_eq
    let left := first * scale scalar second
    let right := scale scalar (first * second)
    let dimension := Nat.max left.coeffs.length right.coeffs.length + 1
    let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
    let function := Cyclic.Element.scalar cyclic
    let point := Cyclic.Element.root cyclic
    change (Map.map function left).eval point = (Map.map function right).eval point
    dsimp only [left, right]
    repeat rewrite [Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic)]
    repeat rewrite [Map.map_scale function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal) (Cyclic.Element.scalar_mul cyclic)]
    rewrite [Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic)]
    repeat first | rewrite [eval_mul] | rewrite [eval_scale]
    exact _root_.mul_left_comm ((Map.map function first).eval point) (function scalar)
      ((Map.map function second).eval point)
  exact (normalize_mul _ _).symm.trans (same.trans (normalize_scale _ _))

/-- Multiplication by the displayed constant one returns the normalized original polynomial. -/
theorem mul_constant_one (polynomial : DensePolynomial K) :
    polynomial * constant 1 = polynomial.normalize := by
  have same : (polynomial * constant 1).normalize = polynomial.normalize := by
    apply Reflection.normalize_eq
    let left := polynomial * constant 1
    let dimension := Nat.max left.coeffs.length polynomial.coeffs.length + 1
    let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
    let function := Cyclic.Element.scalar cyclic
    let point := Cyclic.Element.root cyclic
    change (Map.map function left).eval point = (Map.map function polynomial).eval point
    dsimp only [left]
    rewrite [Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic), Map.map_constant,
      eval_mul, eval_constant]
    have one : function 1 = 1 := Cyclic.Element.scalar_one cyclic
    exact (congrArg ((Map.map function polynomial).eval point * ·) one).trans (mul_one _)
  exact (normalize_mul _ _).symm.trans same

/-- Removing the left input's leading zero coefficients preserves the original product. -/
theorem normalize_mul_left (first second : DensePolynomial K) :
    first.normalize * second = first * second := by
  have same : (first.normalize * second).normalize = (first * second).normalize := by
    apply Reflection.normalize_eq
    let left := first.normalize * second
    let right := first * second
    let dimension := Nat.max left.coeffs.length right.coeffs.length + 1
    let cyclic := Cyclic.shift K dimension (Nat.zero_lt_succ _)
    let function := Cyclic.Element.scalar cyclic
    let point := Cyclic.Element.root cyclic
    change (Map.map function left).eval point = (Map.map function right).eval point
    dsimp only [left, right]
    repeat rewrite [Map.map_mul function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)
      (Cyclic.Element.scalar_add cyclic) (Cyclic.Element.scalar_mul cyclic)]
    rewrite [Map.map_normalize function (Cyclic.Element.scalar_zero cyclic)
      (fun _ _ equal => Cyclic.Element.scalar_injective cyclic equal)]
    repeat rewrite [eval_mul]
    rewrite [eval_normalize]
    rfl
  exact (normalize_mul _ _).symm.trans (same.trans (normalize_mul _ _))

/-- Scaling the displayed constant one gives the normalized displayed scalar constant. -/
theorem scale_constant_one (scalar : K) : scale scalar (constant 1) = (constant scalar).normalize := by
  change (⟨[scalar * 1]⟩ : DensePolynomial K).normalize = (⟨[scalar]⟩ : DensePolynomial K).normalize
  rewrite [mul_one]
  rfl

end Purelib.Polynomial.Dense.Basic.DensePolynomial

end
