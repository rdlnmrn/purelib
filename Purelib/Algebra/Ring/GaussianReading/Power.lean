module

public import Purelib.Algebra.Ring.GaussianReading
public import Purelib.Data.Vector.Scan
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.NatCast
import Purelib.Data.Fin
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-fixed finite power errors for original Gaussian readings

A single original structural scan retains rational weight and discrepancy
coefficients before any reading is observed. The same original product-error
law then controls actual finite powers without asserting multiplicativity.
-/

public section

namespace Purelib.Algebra.Ring.GaussianReading

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector.Scan
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Algebra

variable {K : Type*} [CommRing K] {weight : Weight K} {scalar : Canonical → K}

/-- The original additive reading preserves multiplication by every natural scalar exactly. -/
theorem read_natMul (reading : GaussianReading weight scalar) (count : Nat) (value : K) :
    reading.read ((count : K) * value) = (count : Canonical) * reading.read value := by
  induction count with
  | zero =>
      rewrite [Nat.cast_zero, Nat.cast_zero, zero_mul, zero_mul]
      exact reading.mapZero
  | succ count previous =>
      rewrite [NatCast.add, Nat.cast_one, add_mul, one_mul, reading.mapAdd, previous,
        NatCast.add, Nat.cast_one, add_mul, one_mul]
      rfl

namespace Power

/-- Advance one retained rational weight bound and original power-error coefficient. -/
@[expose] def step (rootWeight multiplier radius : Rational) (state : Rational × Rational) (_edge : Unit) :
    Rational × Rational :=
  (multiplier * state.1 * rootWeight, 2 * (state.1 * rootWeight + radius * state.2))

set_option genInjectivity false in
/-- Source-fixed rational coefficients for all original powers through one finite horizon.

The original scalar weight, root, gain and horizon remain indices. A single
retained original scan starts at the original unit weight and zero error;
every state stores its weight bound and linear multiplication-error factor.
-/
structure Parameters (weight : Weight K) (root : K) (gain : Rational) (count : Nat) where
  /-- The fixed original gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The once-computed original source-root weight. -/
  rootWeight : Rational
  /-- The retained root weight belongs to the same original scalar. -/
  rootWeight_eq : rootWeight = weight.value root
  /-- The once-computed original unit weight. -/
  unitWeight : Rational
  /-- The retained unit weight belongs to the original coefficient ring. -/
  unitWeight_eq : unitWeight = weight.value 1
  /-- The fixed squared radius for every future root reading. -/
  radius : Rational
  /-- The radius consumes the same source-fixed gain and retained root weight. -/
  radius_eq : radius = gain * rootWeight
  /-- The one materialized rational bound/error table, including the original initial state. -/
  table : Vec (Rational × Rational) (count + 1)
  /-- The table is the original structural scan of the same source-fixed rational step. -/
  table_eq : table = scan (step rootWeight weight.multiplier radius) (unitWeight, 0)
    (vectorOfFn (fun _ : Fin count => Unit.unit))

constructive_injectivity Parameters

namespace Parameters

/-- Prepare all original finite power coefficients before a Gaussian reading is observed. -/
@[expose] def prepare (weight : Weight K) (root : K) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (count : Nat) : Parameters weight root gain count :=
  let rootWeight := weight.value root
  let unitWeight := weight.value 1
  let radius := gain * rootWeight
  let edges := vectorOfFn (fun _ : Fin count => Unit.unit)
  let table := scan (step rootWeight weight.multiplier radius) (unitWeight, 0) edges
  { gainNonnegative, rootWeight, rootWeight_eq := rfl, unitWeight, unitWeight_eq := rfl
    radius, radius_eq := rfl, table, table_eq := rfl }

variable {root : K} {gain : Rational} {count : Nat} (parameters : Parameters weight root gain count)

/-- The retained original source-root weight is nonnegative. -/
theorem rootWeight_nonnegative : 0 ≤ parameters.rootWeight :=
  parameters.rootWeight_eq ▸ weight.nonnegative root

/-- The retained original unit weight is nonnegative. -/
theorem unitWeight_nonnegative : 0 ≤ parameters.unitWeight :=
  parameters.unitWeight_eq ▸ weight.nonnegative 1

/-- The retained pre-observation root radius is nonnegative. -/
theorem radius_nonnegative : 0 ≤ parameters.radius := by
  rewrite [parameters.radius_eq]
  exact Arithmetic.mul_nonneg_direct parameters.gainNonnegative parameters.rootWeight_nonnegative

/-- The initial retained scan state is the same original unit weight and zero discrepancy. -/
theorem table_zero : parameters.table ⟨0, Nat.zero_lt_succ count⟩ = (parameters.unitWeight, 0) := by
  rewrite [parameters.table_eq]
  cases count <;> rfl

/-- Each retained successor consumes the same preceding rational state. -/
theorem table_step (index : Fin count) :
    parameters.table index.succ = step parameters.rootWeight weight.multiplier parameters.radius
      (parameters.table index.castSucc) Unit.unit := by
  rewrite [parameters.table_eq, scan_step, vectorOfFn_apply]
  rfl

/-- Both rational coefficients at every retained power index are nonnegative. -/
theorem table_nonnegative (index : Fin (count + 1)) :
    0 ≤ (parameters.table index).1 ∧ 0 ≤ (parameters.table index).2 := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    0 ≤ (parameters.table index).1 ∧ 0 ≤ (parameters.table index).2) ?_ ?_ index
  · rewrite [parameters.table_zero]
    exact ⟨parameters.unitWeight_nonnegative, le_refl 0⟩
  · intro previous bounded
    rewrite [parameters.table_step]
    constructor
    · exact Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct weight.multiplier_nonnegative bounded.1)
        parameters.rootWeight_nonnegative
    · exact Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct bounded.1 parameters.rootWeight_nonnegative)
          (Arithmetic.mul_nonneg_direct parameters.radius_nonnegative bounded.2))

/-- Every original root power has its weight bounded by the same retained scan state. -/
theorem weight_bound (index : Fin (count + 1)) : weight.value (root ^ index.val) ≤ (parameters.table index).1 := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    weight.value (root ^ index.val) ≤ (parameters.table index).1) ?_ ?_ index
  · rewrite [parameters.table_zero, pow_zero, parameters.unitWeight_eq]
    exact le_refl _
  · intro previous bounded
    rewrite [parameters.table_step]
    change weight.value (root ^ (previous.val + 1)) ≤
      weight.multiplier * (parameters.table previous.castSucc).1 * parameters.rootWeight
    rewrite [pow_succ]
    exact (weight.mul_le _ _).trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded weight.multiplier_nonnegative)
      (weight.nonnegative root)).trans_eq (by rewrite [parameters.rootWeight_eq]; rfl))

/-- Every future root reading has the same source-fixed radius bound. -/
theorem root_bound (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain) :
    Norm.Basic.normSq (reading.read root) ≤ parameters.radius := by
  exact (reading.gainBound root).trans_eq (by rewrite [gain_eq, parameters.radius_eq, parameters.rootWeight_eq]; rfl)

/-- The actual original power discrepancy is at most the reading's error times its retained source-fixed coefficient.

The proof uses the original product-error law once at each finite successor.
The retained gain bounds the same original root reading; no exact product
homomorphism, inverse, or candidate-dependent coefficient is assumed.
-/
theorem bound (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (index : Fin (count + 1)) :
    Norm.Basic.normSq (reading.read (root ^ index.val) - reading.read root ^ index.val) ≤
      reading.error * (parameters.table index).2 := by
  refine Purelib.Data.Fin.induction (motive := fun index =>
    Norm.Basic.normSq (reading.read (root ^ index.val) - reading.read root ^ index.val) ≤
      reading.error * (parameters.table index).2) ?_ ?_ index
  · rewrite [parameters.table_zero, pow_zero, pow_zero, reading.mapOne, sub_self,
      Norm.Basic.normSq_zero, mul_zero]
    exact le_refl _
  · intro previous bounded
    have product := reading.productBound (root ^ previous.val) root
    have paidProduct : Norm.Basic.normSq (reading.read (root ^ previous.val * root) -
        reading.read (root ^ previous.val) * reading.read root) ≤
        reading.error * (parameters.table previous.castSucc).1 * parameters.rootWeight :=
      product.trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (parameters.weight_bound previous.castSucc)
          reading.errorNonnegative) (weight.nonnegative root)).trans_eq
            (by rewrite [parameters.rootWeight_eq]; rfl))
    have paidPrevious : Norm.Basic.normSq
        ((reading.read (root ^ previous.val) - reading.read root ^ previous.val) * reading.read root) ≤
        (reading.error * (parameters.table previous.castSucc).2) * parameters.radius := by
      rewrite [Norm.Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct bounded (parameters.root_bound reading gain_eq)
        (Norm.Basic.normSq_nonneg _) (Arithmetic.mul_nonneg_direct reading.errorNonnegative
          (parameters.table_nonnegative previous.castSucc).2)
    have identity : reading.read (root ^ (previous.val + 1)) - reading.read root ^ (previous.val + 1) =
        (reading.read (root ^ previous.val * root) - reading.read (root ^ previous.val) * reading.read root) +
          (reading.read (root ^ previous.val) - reading.read root ^ previous.val) * reading.read root := by
      rewrite [pow_succ, pow_succ]
      ring1
    change Norm.Basic.normSq (reading.read (root ^ (previous.val + 1)) -
      reading.read root ^ (previous.val + 1)) ≤ _
    rewrite [identity, parameters.table_step]
    calc
      _ ≤ 2 * (Norm.Basic.normSq (reading.read (root ^ previous.val * root) -
            reading.read (root ^ previous.val) * reading.read root) +
          Norm.Basic.normSq ((reading.read (root ^ previous.val) - reading.read root ^ previous.val) *
            reading.read root)) := Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (reading.error * (parameters.table previous.castSucc).1 * parameters.rootWeight +
          (reading.error * (parameters.table previous.castSucc).2) * parameters.radius) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct paidProduct paidPrevious) (by decide)
      _ = _ := by dsimp only [step]; ring1

end Parameters
end Power
end Purelib.Algebra.Ring.GaussianReading

end
