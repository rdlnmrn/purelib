module

public import Mathlib.Tactic.NormNum.Result
public import Purelib.Algebra.Semiring.Nat

namespace Purelib.Algebra.Semiring.Normalization

open Mathlib.Meta

public section

variable {R : Type*} [CommSemiring R] {a a' a₁ a₂ b b₁ b₂ c c₁ c₂ : R}

/-- A zero semiring element raised to a positive natural exponent remains zero.

The retained exponent is nonzero. Its successor power contains the original
zero as a right factor, so multiplication by zero certifies the result. -/
theorem zero_pow {exponent : Nat} (positive : 0 < exponent) : (0 : R) ^ exponent = 0 := by
  cases exponent with
  | zero => exact False.elim (Nat.not_lt_zero 0 positive)
  | succ exponent =>
      rw [_root_.pow_succ]
      exact MulZeroClass.mul_zero _

/-- An additive zero on the left does not change a normalized value. -/
theorem add_pf_zero_add (b : R) : 0 + b = b := zero_add b

/-- An additive zero on the right does not change a normalized value. -/
theorem add_pf_add_zero (a : R) : a + 0 = a := add_zero a

/-- A computed sum can be transported past a retained leading summand. -/
theorem add_pf_add_lt (a₁ : R) (computed : a₂ + b = c) :
    (a₁ + a₂) + b = a₁ + c := by
  rw [add_assoc, computed]

/-- A computed sum can be transported past a leading summand on the right. -/
theorem add_pf_add_gt (b₁ : R) (computed : a + b₂ = c) :
    a + (b₁ + b₂) = b₁ + c := by
  rw [← add_assoc, add_comm a b₁, add_assoc, computed]

/-- Two computed sums give the sum of their corresponding paired terms. -/
theorem add_pf_add_overlap (first : a₁ + b₁ = c₁) (second : a₂ + b₂ = c₂) :
    (a₁ + a₂) + (b₁ + b₂) = c₁ + c₂ := by
  rw [add_assoc, ← add_assoc a₂ b₁ b₂, add_comm a₂ b₁,
    add_assoc b₁ a₂ b₂, ← add_assoc, first, second]

/-- A zero certificate for one pair leaves the computed sum of the other pair. -/
theorem add_pf_add_overlap_zero (first : NormNum.IsNat (a₁ + b₁) 0)
    (second : a₂ + b₂ = c) : (a₁ + a₂) + (b₁ + b₂) = c := by
  have firstZero : a₁ + b₁ = 0 := first.out.trans Nat.cast_zero
  rw [add_pf_add_overlap firstZero second, zero_add]

/-- Multiplication by zero on the right annihilates a normalized value. -/
theorem mul_zero (a : R) : a * 0 = 0 := MulZeroClass.mul_zero a

/-- Multiplication by zero on the left annihilates a normalized value. -/
theorem zero_mul (b : R) : 0 * b = 0 := MulZeroClass.zero_mul b

/-- Computed products and their computed sum evaluate a right sum factor. -/
theorem mul_add {d : R} (first : a * b₁ = c₁) (second : a * b₂ = c₂)
    (combined : c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d := by
  rw [add_zero] at combined
  rw [_root_.mul_add, first, second]
  exact combined

/-- Computed products and their computed sum evaluate a left sum factor. -/
theorem add_mul {d : R} (first : a₁ * b = c₁) (second : a₂ * b = c₂)
    (combined : c₁ + c₂ = d) : (a₁ + a₂) * b = d := by
  rw [_root_.add_mul, first, second]
  exact combined

/-- A computed coefficient sum transports through a retained monomial factor. -/
theorem add_overlap_pf (x : R) (e : Nat) (computed : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by
  rw [← _root_.mul_add, computed]

/-- A zero coefficient sum certifies that its retained monomial sum is zero. -/
theorem add_overlap_pf_zero (x : R) (e : Nat)
    (computed : NormNum.IsNat (a + b) 0) :
    NormNum.IsNat (x ^ e * a + x ^ e * b) 0 := by
  have coefficientZero : a + b = 0 := computed.out.trans Nat.cast_zero
  refine ⟨?_⟩
  rw [← _root_.mul_add, coefficientZero, mul_zero, Nat.cast_zero]

/-- Two monomials with the same base combine their exponents and coefficients. -/
theorem mul_pp_pf_overlap {ea eb e : Nat} (x : R) (exponents : ea + eb = e)
    (coefficients : a₂ * b₂ = c) :
    (x ^ ea * a₂) * (x ^ eb * b₂) = x ^ e * c := by
  rw [mul_assoc, ← mul_assoc a₂, mul_comm a₂ (x ^ eb), mul_assoc (x ^ eb),
    ← mul_assoc, ← pow_add, exponents, coefficients]

/-- A computed power is preserved when its source and target have additive zero. -/
theorem single_pow {b : Nat} (computed : a ^ b = c) : (a + 0) ^ b = c + 0 := by
  rw [add_zero, add_zero]
  exact computed

/-- A computed power with additive zero and a unit coefficient identifies the base power.

The retained equality has the semiring's additive zero on the base and the
natural cast of one as its coefficient. Removing those two neutral elements
preserves the original exponent and the computed value. -/
theorem pow_prod_atom (a : R) (b : Nat) {e : R}
    (computed : (a + 0) ^ b * (1 : Nat).rawCast = e) : a ^ b = e := by
  rewrite [add_zero, show (1 : Nat).rawCast = (1 : R) from Nat.cast_one,
    _root_.mul_one] at computed
  exact computed

/-- A retained unit exponent and coefficient identify a normalized atom.

The displayed exponent is one and the monomial's unit coefficient is the
ordinary natural cast of one into the semiring. -/
theorem atom_pf (a : R) {e : Nat} (hone : 1 = e)
    (computed : a ^ e * (1 : Nat).rawCast = b) : a = b + 0 := by
  rw [← hone, show (1 : Nat).rawCast = (1 : R) from Nat.cast_one,
    pow_one, mul_one] at computed
  rw [add_zero]
  exact computed

/-- A natural-value certificate supplies the normalized value with additive zero. -/
theorem cast_pos {n : Nat} (computed : NormNum.IsNat a n) :
    a = n.rawCast + 0 := by
  rw [add_zero]
  exact computed.out

/-- A natural zero certificate identifies the semiring zero. -/
theorem cast_zero (computed : NormNum.IsNat a 0) : a = 0 := by
  exact computed.out.trans Nat.cast_zero

/-- A normalized unit exponent preserves its base. -/
theorem pow_one (a : R) : a ^ 1 = a := _root_.pow_one a

/-- A computed power and its square certify a doubled natural exponent.

The retained exponent doubles by natural addition, so its power is the
product of the two retained equal powers. -/
theorem pow_bit0 {k : Nat} (power : a ^ k = b) (product : b * b = c) :
    a ^ (Nat.mul 2 k) = c := by
  change a ^ (Nat.succ 1 * k) = c
  rw [Nat.succ_mul, Nat.one_mul, _root_.pow_add, power, product]

/-- A retained power, its square and one final factor certify a doubled successor exponent.

The supplied power equality and product equalities keep the original base and
intermediate values. The successor power law appends that same base to the
certified doubled power. -/
theorem pow_bit1 {k : Nat} {d : R} (power : a ^ k = b)
    (square : b * b = c) (product : c * a = d) :
    a ^ (Nat.add (Nat.mul 2 k) 1) = d := by
  rewrite [_root_.pow_succ]
  exact (congrArg (fun retained : R => retained * a)
    (pow_bit0 power square)).trans product

/-- A retained unit value stays fixed under any natural exponent.

The source's natural-value certificate identifies it with one. The monoid's
recursive power laws preserve that unit through the supplied finite exponent. -/
theorem one_pow {a : R} (exponent : Nat) (unit : NormNum.IsNat a 1) :
    a ^ exponent = a := by
  have sourceOne : a = 1 := unit.out.trans Nat.cast_one
  rw [sourceOne]
  exact _root_.one_pow exponent

/-- A natural coefficient has a normalized retained unit factor. -/
theorem coeff_one (coefficient : Nat) {unit : Nat}
    (unitEquation : @Nat.rawCast Nat
      Nat.commSemiring.toSemiring.toAddMonoidWithOne 1 = unit) :
    @Nat.rawCast Nat Nat.commSemiring.toSemiring.toAddMonoidWithOne coefficient =
      unit * coefficient := by
  change 1 = unit at unitEquation
  rw [← unitEquation]
  exact (Nat.one_mul coefficient).symm

/-- A natural-value certificate for one gives a normalized unit exponent. -/
theorem pow_one_cast_of_isNat (a : R) (exponent : Nat)
    (unit : @NormNum.IsNat Nat
      Nat.commSemiring.toSemiring.toAddMonoidWithOne exponent 1) :
    a ^ exponent = a := by
  have exponentOne : exponent = 1 := unit.out
  rw [exponentOne]
  exact _root_.pow_one a

/-- Computed powers compose through a retained product of natural exponents.

The supplied exponent equation determines the same nested finite power. Each
retained computed equality transports its value without changing the operation. -/
theorem pow_nat {exponent firstExponent secondExponent : Nat} {firstValue value : R}
    (exponents : exponent = firstExponent * secondExponent)
    (first : a ^ firstExponent = firstValue)
    (second : firstValue ^ secondExponent = value) : a ^ exponent = value := by
  rw [exponents, _root_.pow_mul, first, second]

/-- A retained normalized unit coefficient gives the zeroth power's value. -/
theorem pow_zero (a : R) {unit : R} (unitEquation : (1 : Nat).rawCast = unit) :
    a ^ 0 = unit + 0 := by
  rw [_root_.pow_zero, add_zero]
  exact Nat.cast_one.symm.trans unitEquation

/-- Two retained computed powers and their product certify a summed exponent.

The original monoid power law factors the sum into the supplied powers, and
their retained product equation supplies the normalized value. -/
theorem pow_add {firstExponent secondExponent : Nat} {value : R}
    (first : a ^ firstExponent = c₁) (second : a ^ secondExponent = c₂)
    (product : c₁ * c₂ = value) : a ^ (firstExponent + secondExponent) = value := by
  rw [_root_.pow_add, first, second, product]

/-- A displayed product's natural power factors into the powers of its factors.

Scalar reassociation and commutation align each successor product with the
original recursive monoid power operations. -/
theorem product_pow (left right : R) (exponent : Nat) :
    (left * right) ^ exponent = left ^ exponent * right ^ exponent := by
  induction exponent with
  | zero => rw [_root_.pow_zero, _root_.pow_zero, _root_.pow_zero, one_mul]
  | succ exponent induction =>
      rw [_root_.pow_succ, _root_.pow_succ, _root_.pow_succ, induction,
        mul_assoc, ← mul_assoc (right ^ exponent) left right,
        mul_comm (right ^ exponent) left, mul_assoc left (right ^ exponent) right,
        ← mul_assoc]

/-- Retained exponent, coefficient and product equations certify a monomial power.

Powering the monomial retains its original base and coefficient. The supplied
exponent product and computed scalar powers identify the resulting monomial
and its final normalized product. -/
theorem mul_pow_mul {baseExponent exponent resultExponent : Nat} {base monomial value : R}
    (exponents : baseExponent * exponent = resultExponent)
    (coefficientPower : a₂ ^ exponent = c₂)
    (monomialEquation : base ^ resultExponent * (1 : Nat).rawCast = monomial)
    (product : monomial * c₂ = value) : (base ^ baseExponent * a₂) ^ exponent = value := by
  have monomialValue : base ^ resultExponent = monomial := by
    rw [show (1 : Nat).rawCast = (1 : R) from Nat.cast_one, mul_one]
      at monomialEquation
    exact monomialEquation
  rw [product_pow, ← _root_.pow_mul, exponents, coefficientPower, monomialValue, product]

end

end Purelib.Algebra.Semiring.Normalization
