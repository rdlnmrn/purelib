import mathlib.RFAP.FiniteCyclotomic
import mathlib.Tactic.QuotientFreeOmega

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

namespace RFAP.FiniteIntegerPolynomial

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Polynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Rational

open RFAP.ComputablePolynomial.DensePolynomial

namespace IntegerPolynomial

open RFAP.IntegerPolynomialCertificate

/-- Convert an ascending integer coefficient list into the finite descending
dense rational representation. -/
def castCoefficients (coefficients : List Int) : List Rational :=
  List.map (fun coefficient : Int => (coefficient : Rational)) coefficients

def ofAscending (coefficients : List Int) : Polynomial :=
  normalize ⟨castCoefficients coefficients.reverse⟩

@[simp] theorem ofAscending_normalized (coefficients : List Int) :
    (ofAscending coefficients).normalize = ofAscending coefficients :=
  normalize_normalize _

private theorem evalCoeffs_append_singleton
    (coefficients : List Rational) (coefficient point : Rational) :
    evalCoeffs point (coefficients ++ [coefficient]) =
      evalCoeffs point coefficients * point + coefficient := by
  unfold evalCoeffs
  rw [QuotientFreeList.foldl_append]
  rfl

private theorem evalCoeffs_reverse_cast : ∀ coefficients : List Int,
    ∀ point : Rational,
    evalCoeffs point
        (castCoefficients coefficients.reverse) =
      eval coefficients point
  | [], point => rfl
  | coefficient :: remaining, point => by
      rw [List.reverse_cons]
      unfold castCoefficients
      rw [List.map_append, List.map_singleton,
        evalCoeffs_append_singleton]
      change evalCoeffs point (castCoefficients remaining.reverse) * point +
        (coefficient : Rational) = eval (coefficient :: remaining) point
      rw [evalCoeffs_reverse_cast remaining point, eval_cons]
      ring0

@[simp] theorem eval_ofAscending (coefficients : List Int)
    (point : Rational) :
    (ofAscending coefficients).eval point = eval coefficients point := by
  rw [ofAscending, eval_normalize]
  exact evalCoeffs_reverse_cast coefficients point

theorem ofAscending_zero : ofAscending [] = 0 := rfl

theorem ofAscending_one : ofAscending [1] = constant (1 : Rational) := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _)
    (normalize_constant_of_ne RFAP.ConstructiveFraction.zero_ne_one.symm)
  intro point
  rw [eval_ofAscending, eval_cons, eval_nil, Int.cast_one, mul_zero,
    add_zero, eval_constant]

theorem ofAscending_add (left right : List Int) :
    ofAscending (add left right) =
      ofAscending left + ofAscending right := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_add _ _)
  intro point
  rw [eval_ofAscending, RFAP.IntegerPolynomialCertificate.eval_add,
    RFAP.ComputablePolynomial.DensePolynomial.eval_add,
    eval_ofAscending, eval_ofAscending]

theorem ofAscending_neg (coefficients : List Int) :
    ofAscending (neg coefficients) = -ofAscending coefficients := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_neg _)
  intro point
  rw [eval_ofAscending, RFAP.IntegerPolynomialCertificate.eval_neg,
    RFAP.ComputablePolynomial.DensePolynomial.eval_neg, eval_ofAscending]

theorem ofAscending_sub (left right : List Int) :
    ofAscending (sub left right) =
      ofAscending left - ofAscending right := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_sub _ _)
  intro point
  rw [eval_ofAscending, RFAP.IntegerPolynomialCertificate.eval_sub,
    RFAP.ComputablePolynomial.DensePolynomial.eval_sub,
    eval_ofAscending, eval_ofAscending]

theorem ofAscending_mul (left right : List Int) :
    ofAscending (mul left right) =
      ofAscending left * ofAscending right := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_mul _ _)
  intro point
  rw [eval_ofAscending, RFAP.IntegerPolynomialCertificate.eval_mul,
    RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
    eval_ofAscending, eval_ofAscending]

theorem ofAscending_scale (factor : Int) (coefficients : List Int) :
    ofAscending (scale factor coefficients) =
      RFAP.ComputablePolynomial.DensePolynomial.scale
        (factor : Rational) (ofAscending coefficients) := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_scale _ _)
  intro point
  rw [eval_ofAscending, RFAP.IntegerPolynomialCertificate.eval_scale,
    RFAP.ComputablePolynomial.DensePolynomial.eval_scale,
    eval_ofAscending]

/-- Repeat the ascending-list multiplication-by-`X` operation. -/
def shiftN : Nat → List Int → List Int
  | 0, coefficients => coefficients
  | exponent + 1, coefficients => shift (shiftN exponent coefficients)

@[simp] theorem eval_shiftN : ∀ exponent : Nat,
    ∀ coefficients : List Int, ∀ point : Rational,
    eval (shiftN exponent coefficients) point =
      eval coefficients point * point ^ exponent
  | 0, coefficients, point => by rw [shiftN, pow_zero, mul_one]
  | exponent + 1, coefficients, point => by
      rw [shiftN, RFAP.IntegerPolynomialCertificate.eval_shift,
        eval_shiftN exponent coefficients point,
        pow_succ]
      ring0

theorem ofAscending_shiftN (exponent : Nat) (coefficients : List Int) :
    ofAscending (shiftN exponent coefficients) =
      RFAP.ComputablePolynomial.DensePolynomial.shift exponent
        (ofAscending coefficients) := by
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (ofAscending_normalized _) (normalize_shift _ _)
  intro point
  rw [eval_ofAscending, eval_shiftN,
    RFAP.ComputablePolynomial.DensePolynomial.eval_shift,
    eval_ofAscending]

end IntegerPolynomial

/-- A rational value has a displayed integer witness. -/
def IsIntegralRational (value : Rational) : Prop :=
  ∃ integer : Int, value = (integer : Rational)

/-- A dense polynomial has an executable ascending integer certificate. -/
def IsIntegralPolynomial (polynomial : Polynomial) : Prop :=
  ∃ coefficients : List Int,
    polynomial.normalize = IntegerPolynomial.ofAscending coefficients

theorem integral_zero : IsIntegralPolynomial (0 : Polynomial) :=
  ⟨[], rfl⟩

theorem integral_of_integer (integer : Int) :
    IsIntegralRational (integer : Rational) := ⟨integer, rfl⟩

theorem integral_constant {value : Rational}
    (integral : IsIntegralRational value) :
    IsIntegralPolynomial (constant value) := by
  rcases integral with ⟨integer, rfl⟩
  refine ⟨[integer], ?_⟩
  unfold IntegerPolynomial.ofAscending
  rfl

theorem eval_eq_integerCertificate {polynomial : Polynomial}
    {coefficients : List Int}
    (certificate : polynomial.normalize =
      IntegerPolynomial.ofAscending coefficients)
    (point : Rational) :
    polynomial.eval point =
      RFAP.IntegerPolynomialCertificate.eval coefficients point := by
  calc
    polynomial.eval point = polynomial.normalize.eval point :=
      (eval_normalize polynomial point).symm
    _ = (IntegerPolynomial.ofAscending coefficients).eval point := by
      rw [certificate]
    _ = RFAP.IntegerPolynomialCertificate.eval coefficients point :=
      IntegerPolynomial.eval_ofAscending coefficients point

theorem integral_normalize {polynomial : Polynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial polynomial.normalize := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨coefficients, ?_⟩
  rw [normalize_normalize, certificate]

theorem integral_add {left right : Polynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left + right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨RFAP.IntegerPolynomialCertificate.add
    leftCoefficients rightCoefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize, eval_add,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← RFAP.IntegerPolynomialCertificate.eval_add,
    IntegerPolynomial.eval_ofAscending]

theorem integral_neg {polynomial : Polynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial (-polynomial) := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨RFAP.IntegerPolynomialCertificate.neg coefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize, eval_neg, eval_eq_integerCertificate certificate,
    ← RFAP.IntegerPolynomialCertificate.eval_neg,
    IntegerPolynomial.eval_ofAscending]

theorem integral_sub {left right : Polynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left - right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨RFAP.IntegerPolynomialCertificate.sub
    leftCoefficients rightCoefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize, eval_sub,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← RFAP.IntegerPolynomialCertificate.eval_sub,
    IntegerPolynomial.eval_ofAscending]

theorem integral_mul {left right : Polynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left * right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨RFAP.IntegerPolynomialCertificate.mul
    leftCoefficients rightCoefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize, eval_mul,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← RFAP.IntegerPolynomialCertificate.eval_mul,
    IntegerPolynomial.eval_ofAscending]

theorem integral_scale {factor : Rational} {polynomial : Polynomial}
    (factorIntegral : IsIntegralRational factor)
    (polynomialIntegral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial
      (RFAP.ComputablePolynomial.DensePolynomial.scale factor polynomial) := by
  rcases factorIntegral with ⟨integer, rfl⟩
  rcases polynomialIntegral with ⟨coefficients, certificate⟩
  refine ⟨RFAP.IntegerPolynomialCertificate.scale integer coefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize,
    RFAP.ComputablePolynomial.DensePolynomial.eval_scale,
    eval_eq_integerCertificate certificate,
    ← RFAP.IntegerPolynomialCertificate.eval_scale,
    IntegerPolynomial.eval_ofAscending]

theorem integral_shift (exponent : Nat) {polynomial : Polynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial
      (RFAP.ComputablePolynomial.DensePolynomial.shift exponent polynomial) := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨IntegerPolynomial.shiftN exponent coefficients, ?_⟩
  apply RFAP.FinitePolynomialExtensionality.rational_normalized_eq_of_eval_eq
    (normalize_normalize _) (IntegerPolynomial.ofAscending_normalized _)
  intro point
  rw [eval_normalize,
    RFAP.ComputablePolynomial.DensePolynomial.eval_shift,
    eval_eq_integerCertificate certificate,
    ← IntegerPolynomial.eval_shiftN,
    IntegerPolynomial.eval_ofAscending]

private theorem mem_of_mem_dropWhile {A : Type*}
    (predicate : A → Bool) (value : A) : ∀ values : List A,
    value ∈ values.dropWhile predicate → value ∈ values
  | [], member => member
  | head :: remaining, member => by
      cases equation : predicate head with
      | false =>
          simpa only [List.dropWhile, equation, Bool.false_eq_true,
            ↓reduceIte] using member
      | true =>
          apply List.mem_cons_of_mem head
          apply mem_of_mem_dropWhile predicate value remaining
          simpa only [List.dropWhile, equation, ↓reduceIte] using member

private theorem integral_of_mem_castCoefficients
    (value : Rational) : ∀ coefficients : List Int,
    value ∈ IntegerPolynomial.castCoefficients coefficients →
      IsIntegralRational value
  | [], member => by
      unfold IntegerPolynomial.castCoefficients at member
      exact (List.not_mem_nil member).elim
  | coefficient :: remaining, member => by
      unfold IntegerPolynomial.castCoefficients at member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with equal | remainingMember
      · exact ⟨coefficient, equal⟩
      · exact integral_of_mem_castCoefficients value remaining
          (by
            unfold IntegerPolynomial.castCoefficients
            exact remainingMember)

theorem ofAscending_coefficient_integral (coefficients : List Int)
    {value : Rational}
    (member : value ∈ (IntegerPolynomial.ofAscending coefficients).coeffs) :
    IsIntegralRational value := by
  unfold IntegerPolynomial.ofAscending at member
  rw [normalize_coeffs] at member
  have rawMember : value ∈
      IntegerPolynomial.castCoefficients coefficients.reverse :=
    mem_of_mem_dropWhile _ _ _ member
  exact integral_of_mem_castCoefficients value coefficients.reverse rawMember

theorem integral_coefficient {polynomial : Polynomial}
    (integral : IsIntegralPolynomial polynomial) {value : Rational}
    (member : value ∈ polynomial.normalize.coeffs) :
    IsIntegralRational value := by
  rcases integral with ⟨coefficients, certificate⟩
  rw [certificate] at member
  exact ofAscending_coefficient_integral coefficients member

theorem representative_intCast (integer : Int) :
    RFAP.ConstructiveFraction.representative (integer : Rational) =
      RFAP.CanonicalFraction.fromInt integer := by
  change (integer : Rational) = RFAP.CanonicalFraction.fromInt integer
  exact RFAP.CanonicalFraction.intCast_eq_fromInt integer

theorem integral_eq_cast_representative_num {value : Rational}
    (integral : IsIntegralRational value) :
    value = (RFAP.ConstructiveFraction.representative value).num := by
  rcases integral with ⟨integer, equality⟩
  rw [equality, representative_intCast]
  rfl

theorem integral_representative_den_eq_one {value : Rational}
    (integral : IsIntegralRational value) :
    (RFAP.ConstructiveFraction.representative value).den = 1 := by
  rcases integral with ⟨integer, equality⟩
  rw [equality, representative_intCast]
  rfl

/-- Canonical executable integer coefficients extracted from a normalized
finite dense rational polynomial. -/
def integerCoefficients (polynomial : Polynomial) : List Int :=
  polynomial.normalize.coeffs.reverse.map fun coefficient =>
    (RFAP.ConstructiveFraction.representative coefficient).num

private theorem cast_representative_coefficients : ∀ values : List Rational,
    (∀ value ∈ values, IsIntegralRational value) →
    IntegerPolynomial.castCoefficients
        (values.map fun value =>
          (RFAP.ConstructiveFraction.representative value).num) = values
  | [], allIntegral => rfl
  | value :: remaining, allIntegral => by
      unfold IntegerPolynomial.castCoefficients
      simp only [List.map_cons]
      apply congrArg₂ List.cons
      · exact (integral_eq_cast_representative_num
          (allIntegral value List.mem_cons_self)).symm
      · change IntegerPolynomial.castCoefficients
            (remaining.map fun entry =>
              (RFAP.ConstructiveFraction.representative entry).num) = remaining
        exact cast_representative_coefficients remaining
          (fun entry member => allIntegral entry
            (List.mem_cons_of_mem value member))

theorem ofAscending_integerCoefficients_eq_normalize
    (polynomial : Polynomial) (integral : IsIntegralPolynomial polynomial) :
    IntegerPolynomial.ofAscending (integerCoefficients polynomial) =
      polynomial.normalize := by
  have reversed : (integerCoefficients polynomial).reverse =
      polynomial.normalize.coeffs.map fun coefficient =>
        (RFAP.ConstructiveFraction.representative coefficient).num := by
    unfold integerCoefficients
    rw [← List.map_reverse, List.reverse_reverse]
  unfold IntegerPolynomial.ofAscending
  rw [reversed]
  rw [cast_representative_coefficients polynomial.normalize.coeffs
    (fun value member => integral_coefficient integral member)]
  exact normalize_normalize polynomial

theorem castCoefficients_dropWhile_zero : ∀ values : List Int,
    IntegerPolynomial.castCoefficients (values.dropWhile (fun value => value = 0)) =
      (IntegerPolynomial.castCoefficients values).dropWhile
        (fun value => value = 0)
  | [] => rfl
  | value :: remaining => by
      by_cases valueZero : value = 0
      · subst value
        rw [List.dropWhile_cons_of_pos (by decide)]
        unfold IntegerPolynomial.castCoefficients
        rw [List.map_cons, List.dropWhile_cons_of_pos (by decide)]
        exact castCoefficients_dropWhile_zero remaining
      · have castNonzero : (value : Rational) ≠ 0 := by
          intro castZero
          apply valueZero
          exact RFAP.ConstructiveFraction.intCast_injective_direct
            castZero
        have integerTest :
            decide (value = (0 : Int)) ≠ true := by
          intro truth
          exact valueZero (of_decide_eq_true truth)
        have integerFalse : decide (value = (0 : Int)) = false :=
          Bool.eq_false_of_not_eq_true integerTest
        rw [List.dropWhile]
        rw [integerFalse]
        unfold IntegerPolynomial.castCoefficients
        have rationalTest :
            decide ((value : Rational) = 0) ≠ true := by
          intro truth
          exact castNonzero (of_decide_eq_true truth)
        have rationalFalse : decide ((value : Rational) = 0) = false :=
          Bool.eq_false_of_not_eq_true rationalTest
        rw [List.map_cons, List.dropWhile]
        rw [rationalFalse]

private theorem castCoefficients_injective : ∀ {left right : List Int},
    IntegerPolynomial.castCoefficients left =
      IntegerPolynomial.castCoefficients right → left = right
  | [], [], equal => rfl
  | [], _ :: _, equal => by
      unfold IntegerPolynomial.castCoefficients at equal
      simp only [List.map_nil, List.map_cons] at equal
      exact (List.cons_ne_nil _ _ equal.symm).elim
  | _ :: _, [], equal => by
      unfold IntegerPolynomial.castCoefficients at equal
      simp only [List.map_nil, List.map_cons] at equal
      exact (List.cons_ne_nil _ _ equal).elim
  | left :: lefts, right :: rights, equal => by
      unfold IntegerPolynomial.castCoefficients at equal
      simp only [List.map_cons] at equal
      have heads : left = right :=
        RFAP.ConstructiveFraction.intCast_injective_direct
          (List.cons.inj equal).1
      have tails : lefts = rights := castCoefficients_injective
        (List.cons.inj equal).2
      rw [heads, tails]

private theorem evalCoeffs_reverse_intCast
    {K : Type*} [RFAP.ExplicitField K] : ∀ coefficients : List Int,
    ∀ point : K,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        (coefficients.reverse.map fun coefficient : Int =>
          (coefficient : K)) =
      RFAP.IntegerPolynomialCertificate.eval coefficients point
  | [], point => rfl
  | coefficient :: remaining, point => by
      rw [List.reverse_cons, List.map_append, List.map_singleton]
      unfold RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
      rw [QuotientFreeList.foldl_append]
      change
        RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
            (remaining.reverse.map fun value : Int => (value : K)) * point +
          (coefficient : K) =
        RFAP.IntegerPolynomialCertificate.eval
          (coefficient :: remaining) point
      rw [evalCoeffs_reverse_intCast remaining point,
        RFAP.IntegerPolynomialCertificate.eval_cons]
      ring0

private theorem evalCoeffs_map_dropWhile_int_zero
    {K : Type*} [RFAP.ExplicitField K] (point : K) : ∀ values : List Int,
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        ((values.dropWhile fun value => value = 0).map
          fun value : Int => (value : K)) =
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
        (values.map fun value : Int => (value : K))
  | [] => rfl
  | value :: remaining => by
      by_cases valueZero : value = 0
      · subst value
        rw [List.dropWhile_cons_of_pos (by decide), List.map_cons,
          Int.cast_zero]
        rw [RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_cons_zero]
        exact evalCoeffs_map_dropWhile_int_zero point remaining
      · rw [List.dropWhile_cons_of_neg (by simpa using valueZero)]

/-- Equality of canonical rational embeddings of two integer polynomials is
a coefficient identity, hence their evaluations agree in every explicitly
supplied field, including finite characteristic. -/
theorem normalized_reverse_eq_of_ofAscending_eq
    {left right : List Int}
    (equal : IntegerPolynomial.ofAscending left =
      IntegerPolynomial.ofAscending right) :
    left.reverse.dropWhile (fun value => value = 0) =
      right.reverse.dropWhile (fun value => value = 0) := by
  have coefficientEquality := congrArg
    RFAP.ComputablePolynomial.DensePolynomial.coeffs equal
  unfold IntegerPolynomial.ofAscending at coefficientEquality
  simp only [normalize_coeffs] at coefficientEquality
  rw [← castCoefficients_dropWhile_zero,
    ← castCoefficients_dropWhile_zero] at coefficientEquality
  exact castCoefficients_injective coefficientEquality

theorem eval_eq_of_ofAscending_eq
    {left right : List Int}
    (equal : IntegerPolynomial.ofAscending left =
      IntegerPolynomial.ofAscending right)
    {K : Type*} [RFAP.ExplicitField K] (point : K) :
    RFAP.IntegerPolynomialCertificate.eval left point =
      RFAP.IntegerPolynomialCertificate.eval right point := by
  have integerEquality :
      left.reverse.dropWhile (fun value => value = 0) =
        right.reverse.dropWhile (fun value => value = 0) :=
    normalized_reverse_eq_of_ofAscending_eq equal
  calc
    RFAP.IntegerPolynomialCertificate.eval left point =
        RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
          (left.reverse.map fun value : Int => (value : K)) :=
      (evalCoeffs_reverse_intCast left point).symm
    _ = RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
          ((left.reverse.dropWhile fun value => value = 0).map
            fun value : Int => (value : K)) :=
      (evalCoeffs_map_dropWhile_int_zero point left.reverse).symm
    _ = RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
          ((right.reverse.dropWhile fun value => value = 0).map
            fun value : Int => (value : K)) := by rw [integerEquality]
    _ = RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs point
          (right.reverse.map fun value : Int => (value : K)) :=
      evalCoeffs_map_dropWhile_int_zero point right.reverse
    _ = RFAP.IntegerPolynomialCertificate.eval right point :=
      evalCoeffs_reverse_intCast right point

/-- A displayed nonzero final ascending coefficient prevents normalization
from removing any slot. -/
theorem ofAscending_degreeCount_of_getLast
    {coefficients : List Int} {leading : Int}
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (IntegerPolynomial.ofAscending coefficients).degreeCount =
      coefficients.length := by
  have lastMember : leading ∈ coefficients.getLast? := by
    simp [last]
  have decomposition : coefficients.dropLast ++ [leading] = coefficients :=
    List.dropLast_append_getLast? leading lastMember
  have castNonzero : (leading : Rational) ≠ 0 := by
    intro castZero
    exact leadingNonzero
      (RFAP.ConstructiveFraction.intCast_injective_direct castZero)
  unfold IntegerPolynomial.ofAscending degreeCount
  rw [normalize_normalize]
  change
    ((IntegerPolynomial.castCoefficients coefficients.reverse).dropWhile
        (fun value => value = 0)).length = coefficients.length
  rw [← decomposition]
  simp only [List.reverse_append, List.reverse_singleton,
    List.singleton_append, IntegerPolynomial.castCoefficients, List.map_cons]
  have rationalTest :
      decide ((leading : Rational) = 0) ≠ true := by
    intro truth
    exact castNonzero (of_decide_eq_true truth)
  have rationalFalse : decide ((leading : Rational) = 0) = false :=
    Bool.eq_false_of_not_eq_true rationalTest
  rw [List.dropWhile, rationalFalse]
  simp only [List.length_cons, List.length_map, List.length_append,
    List.length_reverse, List.length_nil, Nat.zero_add]

/-- Exact natural degree from an ascending slot count and a nonzero final
coefficient. -/
theorem ofAscending_natDegree_of_getLast
    {coefficients : List Int} {degree : Nat} {leading : Int}
    (length : coefficients.length = degree + 1)
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (IntegerPolynomial.ofAscending coefficients).natDegree = degree := by
  unfold natDegree
  rw [ofAscending_degreeCount_of_getLast last leadingNonzero, length]
  omega0

/-- The same finite shape certificate proves that the represented polynomial
is nonzero. -/
theorem ofAscending_isZero_false_of_getLast
    {coefficients : List Int} {leading : Int}
    (last : coefficients.getLast? = some leading)
    (leadingNonzero : leading ≠ 0) :
    (IntegerPolynomial.ofAscending coefficients).isZero = false := by
  cases zeroTest : (IntegerPolynomial.ofAscending coefficients).isZero with
  | false => rfl
  | true =>
      have countZero := degreeCount_eq_zero_of_isZero zeroTest
      rw [ofAscending_degreeCount_of_getLast last leadingNonzero] at countZero
      have nonempty : coefficients ≠ [] := by
        intro empty
        rw [empty] at last
        simp only [List.getLast?_nil, reduceCtorEq] at last
      have countPositive : 0 < coefficients.length :=
        List.length_pos_of_ne_nil nonempty
      exact False.elim (by omega0)

theorem ofAscending_leadingCoeff_integral (coefficients : List Int) :
    IsIntegralRational
      (IntegerPolynomial.ofAscending coefficients).leadingCoeff := by
  unfold leadingCoeff IntegerPolynomial.ofAscending
  rw [normalize_normalize]
  change IsIntegralRational
    (((IntegerPolynomial.castCoefficients coefficients.reverse).dropWhile
      (fun value => value = 0)).headD 0)
  cases trimmedEquation :
      (IntegerPolynomial.castCoefficients coefficients.reverse).dropWhile
        (fun value => value = 0) with
  | nil => exact ⟨0, rfl⟩
  | cons leading remaining =>
      have leadingMember : leading ∈
          (IntegerPolynomial.castCoefficients coefficients.reverse).dropWhile
            (fun value => value = 0) := by
        rw [trimmedEquation]
        exact List.mem_cons_self
      have rawMember : leading ∈
          IntegerPolynomial.castCoefficients coefficients.reverse :=
        mem_of_mem_dropWhile _ _ _ leadingMember
      simpa only [trimmedEquation, List.headD_cons] using
        integral_of_mem_castCoefficients leading coefficients.reverse rawMember

theorem integral_leadingCoeff {polynomial : Polynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralRational polynomial.leadingCoeff := by
  rcases integral with ⟨coefficients, certificate⟩
  unfold leadingCoeff
  rw [certificate]
  have result := ofAscending_leadingCoeff_integral coefficients
  unfold leadingCoeff at result
  rw [IntegerPolynomial.ofAscending_normalized] at result
  exact result

theorem integral_leadingQuotientCoefficient
    {dividend divisor : Polynomial}
    (dividendIntegral : IsIntegralPolynomial dividend)
    (divisorMonic : divisor.leadingCoeff = 1) :
    IsIntegralRational (dividend.leadingCoeff / divisor.leadingCoeff) := by
  rcases integral_leadingCoeff dividendIntegral with ⟨integer, equality⟩
  refine ⟨integer, ?_⟩
  have inverseOne : ((1 : Rational)⁻¹) = 1 := by
    simpa only [one_mul] using
      (RFAP.ExplicitField.mul_inv_cancel (1 : Rational)
        RFAP.ConstructiveFraction.zero_ne_one.symm)
  rw [divisorMonic, RFAP.ExplicitField.div_eq_mul_inv, inverseOne, mul_one,
    equality]

theorem integral_leadQuotient {dividend divisor : Polynomial}
    (dividendIntegral : IsIntegralPolynomial dividend)
    (divisorMonic : divisor.leadingCoeff = 1) :
    IsIntegralPolynomial (leadQuotient dividend divisor) := by
  unfold leadQuotient
  exact integral_shift _
    (integral_constant
      (integral_leadingQuotientCoefficient dividendIntegral divisorMonic))

theorem integral_cancelLead {dividend divisor : Polynomial}
    (dividendIntegral : IsIntegralPolynomial dividend)
    (divisorIntegral : IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1) :
    IsIntegralPolynomial (cancelLead dividend divisor) := by
  unfold cancelLead
  apply integral_sub dividendIntegral
  apply integral_shift
  exact integral_scale
    (integral_leadingQuotientCoefficient dividendIntegral divisorMonic)
    divisorIntegral

private theorem divLoop_quotient_integral (fuel : Nat)
    (dividend divisor quotient : Polynomial)
    (dividendIntegral : IsIntegralPolynomial dividend)
    (divisorIntegral : IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1)
    (quotientIntegral : IsIntegralPolynomial quotient) :
    IsIntegralPolynomial
      (divLoop fuel dividend divisor quotient).quotient := by
  induction fuel generalizing dividend quotient with
  | zero => exact quotientIntegral
  | succ fuel inductionHypothesis =>
      rw [divLoop_succ]
      split
      · exact quotientIntegral
      · dsimp only
        exact inductionHypothesis (cancelLead dividend divisor)
          (quotient + leadQuotient dividend divisor)
          (integral_cancelLead dividendIntegral divisorIntegral divisorMonic)
          (integral_add quotientIntegral
            (integral_leadQuotient dividendIntegral divisorMonic))

/-- Finite dense long division by a monic integer polynomial produces an
executable integer-coefficient quotient. -/
theorem divMod_quotient_integral (dividend divisor : Polynomial)
    (dividendIntegral : IsIntegralPolynomial dividend)
    (divisorIntegral : IsIntegralPolynomial divisor)
    (divisorMonic : divisor.leadingCoeff = 1) :
    IsIntegralPolynomial (divMod dividend divisor).quotient := by
  have normalizedMonic : divisor.normalize.leadingCoeff = 1 := by
    unfold leadingCoeff
    rw [normalize_normalize]
    exact divisorMonic
  exact divLoop_quotient_integral (dividend.degreeCount + 1)
    dividend.normalize divisor.normalize 0
    (integral_normalize dividendIntegral)
    (integral_normalize divisorIntegral) normalizedMonic integral_zero

end RFAP.FiniteIntegerPolynomial
