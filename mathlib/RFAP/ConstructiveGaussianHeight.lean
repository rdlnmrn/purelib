import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian

/-!
# Finite Gaussian-integer fractions and common denominator height

This module supplies the paper-facing denominator data for constructive
Gaussian rationals.  It is deliberately independent of the CCL encoders: a
Gaussian integer is two displayed integers, and a common-denominator fraction
is finite numerator data together with one positive natural denominator.
-/

namespace RFAP.ConstructiveGaussianHeight

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

/-- A Gaussian integer is exactly a pair of displayed integers. -/
@[ext]
structure GaussianInt where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace GaussianInt

instance : Zero GaussianInt := ⟨⟨0, 0⟩⟩
instance : One GaussianInt := ⟨⟨1, 0⟩⟩
instance : Add GaussianInt :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg GaussianInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub GaussianInt :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : Mul GaussianInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im,
    z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem zero_re : (0 : GaussianInt).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussianInt).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussianInt).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussianInt).im = 0 := rfl
@[simp] theorem add_re (z w : GaussianInt) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : GaussianInt) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : GaussianInt) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : GaussianInt) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : GaussianInt) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : GaussianInt) : (z - w).im = z.im - w.im := rfl
@[simp] theorem mul_re (z w : GaussianInt) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : GaussianInt) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

@[simp] theorem zero_add (z : GaussianInt) : 0 + z = z := by
  ext <;> simp only [add_re, add_im, zero_re, zero_im, Int.zero_add]

@[simp] theorem add_zero (z : GaussianInt) : z + 0 = z := by
  ext <;> simp only [add_re, add_im, zero_re, zero_im, Int.add_zero]

theorem add_assoc (x y z : GaussianInt) : x + y + z = x + (y + z) := by
  ext <;> simp only [add_re, add_im] <;> ring1

theorem neg_add_cancel (z : GaussianInt) : -z + z = 0 := by
  ext <;> simp only [neg_re, neg_im, add_re, add_im, zero_re, zero_im] <;>
    ring1

@[simp] theorem zero_mul (z : GaussianInt) : 0 * z = 0 := by
  ext <;> simp only [mul_re, mul_im, zero_re, zero_im] <;> ring1

@[simp] theorem mul_zero (z : GaussianInt) : z * 0 = 0 := by
  ext <;> simp only [mul_re, mul_im, zero_re, zero_im] <;> ring1

@[simp] theorem one_mul (z : GaussianInt) : 1 * z = z := by
  ext <;> simp only [mul_re, mul_im, one_re, one_im] <;> ring1

@[simp] theorem mul_one (z : GaussianInt) : z * 1 = z := by
  ext <;> simp only [mul_re, mul_im, one_re, one_im] <;> ring1

theorem mul_assoc (x y z : GaussianInt) : x * y * z = x * (y * z) := by
  ext <;> simp only [mul_re, mul_im] <;> ring1

theorem mul_comm (z w : GaussianInt) : z * w = w * z := by
  ext <;> simp only [mul_re, mul_im] <;> ring1

theorem left_distrib (x y z : GaussianInt) : x * (y + z) = x * y + x * z := by
  ext <;> simp only [mul_re, mul_im, add_re, add_im] <;> ring1

instance instCommRing : CommRing GaussianInt :=
  CommRing.ofMinimalAxioms add_assoc zero_add neg_add_cancel mul_assoc mul_comm
    one_mul left_distrib

/-- Integer-valued squared norm. -/
def normInt (z : GaussianInt) : Int := z.re * z.re + z.im * z.im

private theorem int_mul_self_nonneg (value : Int) : 0 ≤ value * value := by
  by_cases nonnegative : 0 ≤ value
  · exact Int.mul_nonneg nonnegative nonnegative
  · have nonpositive : value ≤ 0 := Int.le_of_lt (Int.lt_of_not_ge nonnegative)
    exact Int.mul_nonneg_of_nonpos_of_nonpos nonpositive nonpositive

theorem normInt_nonneg (z : GaussianInt) : 0 ≤ normInt z :=
  Int.add_nonneg (int_mul_self_nonneg z.re) (int_mul_self_nonneg z.im)

theorem normInt_eq_zero {z : GaussianInt} : normInt z = 0 ↔ z = 0 := by
  constructor
  · intro zero
    have realNonnegative := int_mul_self_nonneg z.re
    have imagNonnegative := int_mul_self_nonneg z.im
    have realProduct : z.re * z.re = 0 := by
      apply le_antisymm
      · calc
          z.re * z.re ≤ z.re * z.re + z.im * z.im :=
            Int.le_add_of_nonneg_right imagNonnegative
          _ = 0 := zero
      · exact realNonnegative
    have imagProduct : z.im * z.im = 0 := by
      apply le_antisymm
      · calc
          z.im * z.im ≤ z.re * z.re + z.im * z.im :=
            Int.le_add_of_nonneg_left realNonnegative
          _ = 0 := zero
      · exact imagNonnegative
    apply GaussianInt.ext
    · exact (Int.mul_eq_zero.mp realProduct).elim id id
    · exact (Int.mul_eq_zero.mp imagProduct).elim id id
  · intro zero
    rw [zero]
    rfl

/-- Natural squared norm used as a finite height. -/
def normNat (z : GaussianInt) : Nat := (normInt z).natAbs

@[simp] theorem normNat_neg (z : GaussianInt) : normNat (-z) = normNat z := by
  apply congrArg Int.natAbs
  simp only [normInt, neg_re, neg_im]
  ring1

theorem normNat_pos {z : GaussianInt} (nonzero : z ≠ 0) : 0 < normNat z :=
  Int.natAbs_pos.mpr (fun zero => nonzero (normInt_eq_zero.mp zero))

/-- The natural quadrance is the sum of the squares of the two displayed
component magnitudes. -/
theorem normNat_eq_component_squares (z : GaussianInt) :
    normNat z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  unfold normNat normInt
  rw [Int.natAbs_add_of_nonneg (int_mul_self_nonneg z.re)
    (int_mul_self_nonneg z.im), Int.natAbs_mul, Int.natAbs_mul]
  simp only [pow_two]

/-- Each displayed real component is bounded by the natural quadrance. -/
theorem realComponent_natAbs_le_normNat (z : GaussianInt) :
    z.re.natAbs ≤ normNat z := by
  rw [normNat_eq_component_squares]
  by_cases zero : z.re.natAbs = 0
  · omega
  · have selfLe : z.re.natAbs ≤ z.re.natAbs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_right z.re.natAbs (Nat.pos_of_ne_zero zero)
    exact selfLe.trans (Nat.le_add_right _ _)

/-- Each displayed imaginary component is bounded by the natural quadrance. -/
theorem imaginaryComponent_natAbs_le_normNat (z : GaussianInt) :
    z.im.natAbs ≤ normNat z := by
  rw [normNat_eq_component_squares]
  by_cases zero : z.im.natAbs = 0
  · omega
  · have selfLe : z.im.natAbs ≤ z.im.natAbs ^ 2 := by
      simpa only [pow_two] using
        Nat.le_mul_of_pos_right z.im.natAbs (Nat.pos_of_ne_zero zero)
    exact selfLe.trans (Nat.le_add_left _ _)

/-- Both signs of every displayed integer magnitude through `bound`.  Zero
is duplicated harmlessly; consumers may deduplicate a final record list. -/
def signedComponents (bound : Nat) : List Int :=
  (List.range (bound + 1)).map (fun (magnitude : Nat) => (magnitude : Int)) ++
    (List.range (bound + 1)).map
      (fun (magnitude : Nat) => -(magnitude : Int))

theorem mem_signedComponents {component : Int} {bound : Nat}
    (bounded : component.natAbs ≤ bound) :
    component ∈ signedComponents bound := by
  cases component with
  | ofNat magnitude =>
      change magnitude ≤ bound at bounded
      rw [signedComponents, List.mem_append]
      left
      exact QuotientFreeList.mem_map_of_mem
        (QuotientFreeList.mem_range.mpr (Nat.lt_succ_of_le bounded))
  | negSucc predecessor =>
      let magnitude := predecessor + 1
      have magnitudeBound : magnitude ≤ bound := by
        change predecessor + 1 ≤ bound at bounded
        exact bounded
      rw [signedComponents, List.mem_append]
      right
      have member := QuotientFreeList.mem_map_of_mem
        (f := fun magnitude : Nat => -(magnitude : Int))
        (QuotientFreeList.mem_range.mpr (Nat.lt_succ_of_le magnitudeBound))
      change Int.negSucc predecessor ∈
        (List.range (bound + 1)).map
          (fun (value : Nat) => -(value : Int))
      simpa only [magnitude, Int.negSucc_eq, Nat.cast_add, Nat.cast_one,
        Nat.succ_eq_add_one] using member

/-- The finite square of Gaussian integers whose component magnitudes are at
most `bound`.  It is a convenient over-enumeration for any quadrance-bounded
search. -/
def componentSquare (bound : Nat) : List GaussianInt :=
  (signedComponents bound).flatMap fun real =>
    (signedComponents bound).map fun imaginary => ⟨real, imaginary⟩

@[simp] theorem signedComponents_length (bound : Nat) :
    (signedComponents bound).length = 2 * (bound + 1) := by
  simp only [signedComponents, List.length_append, List.length_map,
    List.length_range]
  ring1

private theorem length_flatMap_constant
    {Outer Inner Result : Type} (outer : List Outer) (inner : List Inner)
    (combine : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (combine left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

@[simp] theorem componentSquare_length (bound : Nat) :
    (componentSquare bound).length = 4 * (bound + 1) ^ 2 := by
  rw [componentSquare, length_flatMap_constant]
  simp only [signedComponents_length, pow_two]
  ring1

theorem mem_componentSquare_of_normNat_le {z : GaussianInt} {bound : Nat}
    (bounded : normNat z ≤ bound) : z ∈ componentSquare bound := by
  rw [componentSquare]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨z.re, mem_signedComponents
    ((realComponent_natAbs_le_normNat z).trans bounded), ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨z.im, mem_signedComponents
    ((imaginaryComponent_natAbs_le_normNat z).trans bounded), ?_⟩
  rfl

/-- Embed a Gaussian integer into the constructive Gaussian rationals. -/
def toGaussian (z : GaussianInt) : Gaussian := ⟨z.re, z.im⟩

@[simp] theorem toGaussian_zero : toGaussian 0 = 0 := rfl
@[simp] theorem toGaussian_one : toGaussian 1 = 1 := rfl

@[simp] theorem toGaussian_add (z w : GaussianInt) :
    toGaussian (z + w) = toGaussian z + toGaussian w := by
  ext <;> simp only [toGaussian, add_re, add_im,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.add_im, Int.cast_add]

@[simp] theorem toGaussian_mul (z w : GaussianInt) :
    toGaussian (z * w) = toGaussian z * toGaussian w := by
  ext <;> simp only [toGaussian, mul_re, mul_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_sub, Int.cast_add,
    QuotientFreeRing.intCast_mul]

@[simp] theorem toGaussian_eq_zero {z : GaussianInt} :
    toGaussian z = 0 ↔ z = 0 := by
  constructor
  · intro zero
    apply GaussianInt.ext
    · exact RFAP.ConstructiveFraction.intCast_injective_direct
        (congrArg RFAP.ConstructiveGaussian.Gaussian.re zero)
    · exact RFAP.ConstructiveFraction.intCast_injective_direct
        (congrArg RFAP.ConstructiveGaussian.Gaussian.im zero)
  · intro zero
    rw [zero, toGaussian_zero]

theorem normSq_toGaussian (z : GaussianInt) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (toGaussian z) =
      (normNat z : Coordinate) := by
  rw [← Int.cast_natCast]
  rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg z)]
  change (z.re : Coordinate) ^ 2 + (z.im : Coordinate) ^ 2 =
    ((normInt z : Int) : Coordinate)
  simp only [normInt, pow_two, Int.cast_add, QuotientFreeRing.intCast_mul]

/-- Gaussian-integer conjugation. -/
def conj (z : GaussianInt) : GaussianInt := ⟨z.re, -z.im⟩

@[simp] theorem toGaussian_conj (z : GaussianInt) :
    toGaussian (conj z) = RFAP.ConstructiveGaussian.Gaussian.conj
      (toGaussian z) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · change ((-z.im : Int) : Coordinate) = -(z.im : Coordinate)
    exact Int.cast_neg z.im

@[simp] theorem normNat_conj (z : GaussianInt) :
    normNat (conj z) = normNat z := by
  apply RFAP.ConstructiveFraction.natCast_injective_direct
  rw [← normSq_toGaussian, ← normSq_toGaussian, toGaussian_conj]
  change (z.re : Coordinate) ^ 2 + (-(z.im : Coordinate)) ^ 2 =
    (z.re : Coordinate) ^ 2 + (z.im : Coordinate) ^ 2
  ring1

@[simp] theorem normNat_mul (z w : GaussianInt) :
    normNat (z * w) = normNat z * normNat w := by
  apply RFAP.ConstructiveFraction.natCast_injective_direct
  rw [Nat.cast_mul, ← normSq_toGaussian, toGaussian_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_mul, normSq_toGaussian,
    normSq_toGaussian]

/-- The real Gaussian integer associated with a natural number. -/
def ofNat (value : Nat) : GaussianInt := ⟨(value : Int), 0⟩

@[simp] theorem toGaussian_ofNat (value : Nat) :
    toGaussian (ofNat value) = ⟨(value : Coordinate), 0⟩ := by
  rfl

@[simp] theorem normNat_ofNat (value : Nat) : normNat (ofNat value) = value ^ 2 := by
  simp only [normNat, normInt, ofNat, pow_two]
  rw [Int.mul_zero, Int.add_zero, ← Int.natCast_mul, Int.natAbs_natCast]

/-- Multiplication by the conjugate produces the real Gaussian integer whose
natural coordinate is the squared norm. -/
theorem mul_conj (z : GaussianInt) : z * conj z = ofNat (normNat z) := by
  apply GaussianInt.ext
  · change z.re * z.re - z.im * -z.im = (normNat z : Nat)
    rw [normNat, Int.ofNat_natAbs_of_nonneg (normInt_nonneg z)]
    dsimp only [normInt]
    ring1
  · change z.re * -z.im + z.im * z.re = 0
    ring1

end GaussianInt

/-- A Gaussian rational displayed with a common positive natural denominator. -/
@[ext]
structure Fraction where
  numerator : GaussianInt
  denominator : Nat
  denominatorPositive : 0 < denominator
deriving Repr

namespace Fraction

/-- Exact Gaussian value of the displayed common-denominator fraction. -/
def value (fraction : Fraction) : Gaussian :=
  ⟨(fraction.numerator.re : Coordinate) / (fraction.denominator : Coordinate),
    (fraction.numerator.im : Coordinate) / (fraction.denominator : Coordinate)⟩

/-- Squared norm of the real Gaussian denominator. -/
def height (fraction : Fraction) : Nat := fraction.denominator ^ 2

theorem denominatorCast_ne (fraction : Fraction) :
    (fraction.denominator : Coordinate) ≠ 0 := by
  intro zero
  have := RFAP.ConstructiveFraction.natCast_injective_direct
    (zero.trans (Nat.cast_zero).symm)
  exact (Nat.ne_of_gt fraction.denominatorPositive) this

/-- Clearing the common denominator recovers the Gaussian-integer numerator. -/
theorem value_mul_denominator (fraction : Fraction) :
    fraction.value * GaussianInt.toGaussian
        (GaussianInt.ofNat fraction.denominator) =
      GaussianInt.toGaussian fraction.numerator := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change
      ((fraction.numerator.re : Coordinate) /
          (fraction.denominator : Coordinate)) *
            (fraction.denominator : Coordinate) - _ * 0 =
        (fraction.numerator.re : Coordinate)
    rw [RFAP.ExplicitField.div_mul_cancel _ fraction.denominatorCast_ne]
    ring1
  · change
      ((fraction.numerator.re : Coordinate) / _ : Coordinate) * 0 +
          ((fraction.numerator.im : Coordinate) /
            (fraction.denominator : Coordinate)) *
              (fraction.denominator : Coordinate) =
        (fraction.numerator.im : Coordinate)
    rw [RFAP.ExplicitField.div_mul_cancel _ fraction.denominatorCast_ne]
    ring1

/-- Exact norm quotient for a common-denominator Gaussian fraction. -/
theorem normSq_value (fraction : Fraction) :
    RFAP.ConstructiveGaussian.Gaussian.normSq fraction.value =
      (GaussianInt.normNat fraction.numerator : Coordinate) /
        fraction.height := by
  simp only [value, height, RFAP.ConstructiveGaussian.Gaussian.normSq]
  rw [Nat.cast_pow]
  change
    ((fraction.numerator.re : Coordinate) /
          (fraction.denominator : Coordinate)) ^ 2 +
        ((fraction.numerator.im : Coordinate) /
          (fraction.denominator : Coordinate)) ^ 2 =
      (GaussianInt.normNat fraction.numerator : Coordinate) /
        (fraction.denominator : Coordinate) ^ 2
  have numeratorNorm := GaussianInt.normSq_toGaussian fraction.numerator
  change
    (fraction.numerator.re : Coordinate) ^ 2 +
        (fraction.numerator.im : Coordinate) ^ 2 =
      (GaussianInt.normNat fraction.numerator : Coordinate) at numeratorNorm
  rw [RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv, ← numeratorNorm]
  simp only [pow_two]
  rw [RFAP.ConstructiveFraction.inv_mul_direct]
  generalize ((fraction.denominator : Coordinate)⁻¹) = denominatorInverse
  ring1

/-- Canonical finite common-denominator presentation obtained from the two
gcd-reduced constructive rational coordinates. -/
def ofGaussian (source : Gaussian) : Fraction := by
  let real := RFAP.ConstructiveFraction.representative source.re
  let imaginary := RFAP.ConstructiveFraction.representative source.im
  let denominator := real.den * imaginary.den
  exact
    { numerator :=
        ⟨real.num * (imaginary.den : Int),
          imaginary.num * (real.den : Int)⟩
      denominator := denominator
      denominatorPositive := Nat.mul_pos real.den_pos imaginary.den_pos }

/-- The computed common-denominator presentation denotes its source exactly. -/
theorem ofGaussian_value (source : Gaussian) :
    (ofGaussian source).value = source := by
  let real := RFAP.ConstructiveFraction.representative source.re
  let imaginary := RFAP.ConstructiveFraction.representative source.im
  have realClear := RFAP.ConstructiveFraction.representative_mul_den source.re
  have imaginaryClear :=
    RFAP.ConstructiveFraction.representative_mul_den source.im
  change source.re * (real.den : Coordinate) = (real.num : Coordinate) at realClear
  change source.im * (imaginary.den : Coordinate) =
    (imaginary.num : Coordinate) at imaginaryClear
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change
      ((real.num * (imaginary.den : Int) : Int) : Coordinate) /
          ((real.den * imaginary.den : Nat) : Coordinate) = source.re
    rw [QuotientFreeRing.intCast_mul, Int.cast_natCast, Nat.cast_mul]
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show ((real.den : Coordinate) * (imaginary.den : Coordinate)) ≠ 0 by
        exact RFAP.ConstructiveFraction.mul_ne_zero_direct
          (fun zero => (Nat.ne_of_gt real.den_pos)
            (RFAP.ConstructiveFraction.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm)))
          (fun zero => (Nat.ne_of_gt imaginary.den_pos)
            (RFAP.ConstructiveFraction.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm))))
    rw [RFAP.ExplicitField.div_mul_cancel _
      (RFAP.ConstructiveFraction.mul_ne_zero_direct
        (fun zero => (Nat.ne_of_gt real.den_pos)
          (RFAP.ConstructiveFraction.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm)))
        (fun zero => (Nat.ne_of_gt imaginary.den_pos)
          (RFAP.ConstructiveFraction.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm))))]
    rw [← realClear]
    ring1
  · change
      ((imaginary.num * (real.den : Int) : Int) : Coordinate) /
          ((real.den * imaginary.den : Nat) : Coordinate) = source.im
    rw [QuotientFreeRing.intCast_mul, Int.cast_natCast, Nat.cast_mul]
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show ((real.den : Coordinate) * (imaginary.den : Coordinate)) ≠ 0 by
        exact RFAP.ConstructiveFraction.mul_ne_zero_direct
          (fun zero => (Nat.ne_of_gt real.den_pos)
            (RFAP.ConstructiveFraction.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm)))
          (fun zero => (Nat.ne_of_gt imaginary.den_pos)
            (RFAP.ConstructiveFraction.natCast_injective_direct
              (zero.trans (Nat.cast_zero).symm))))
    rw [RFAP.ExplicitField.div_mul_cancel _
      (RFAP.ConstructiveFraction.mul_ne_zero_direct
        (fun zero => (Nat.ne_of_gt real.den_pos)
          (RFAP.ConstructiveFraction.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm)))
        (fun zero => (Nat.ne_of_gt imaginary.den_pos)
          (RFAP.ConstructiveFraction.natCast_injective_direct
            (zero.trans (Nat.cast_zero).symm))))]
    rw [← imaginaryClear]
    ring1

/-- A grid fraction with prescribed real and imaginary numerators. -/
def grid (real imaginary : Int) (denominator : Nat)
    (positive : 0 < denominator) : Fraction :=
  ⟨⟨real, imaginary⟩, denominator, positive⟩

@[simp] theorem grid_height (real imaginary : Int) (denominator : Nat)
    (positive : 0 < denominator) :
    (grid real imaginary denominator positive).height = denominator ^ 2 := rfl

end Fraction

end RFAP.ConstructiveGaussianHeight
