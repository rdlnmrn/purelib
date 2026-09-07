import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructivePolynomial

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

namespace RFAP.ConstructiveRationalRootCandidates

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Rational

open RFAP.ConstructiveFraction
open RFAP.ComputablePolynomial.DensePolynomial

/-! ## Finite denominator clearance -/

/-- Integer coefficients together with their common positive denominator. -/
structure ClearedCoefficients where
  denominator : Nat
  denominatorPositive : 0 < denominator
  coefficients : List Int

/-- Clear a finite high-to-low coefficient list by a structural product of
its canonical positive denominators. -/
def clear : List Rational → ClearedCoefficients
  | [] => ⟨1, by decide, []⟩
  | coefficient :: remaining =>
      let head := representative coefficient
      let tail := clear remaining
      { denominator := head.den * tail.denominator
        denominatorPositive := Nat.mul_pos head.den_pos tail.denominatorPositive
        coefficients :=
          head.num * (tail.denominator : Int) ::
            tail.coefficients.map (fun value => (head.den : Int) * value) }

@[simp] theorem clear_length (coefficients : List Rational) :
    (clear coefficients).coefficients.length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient remaining inductionHypothesis =>
      simp only [clear, List.length_cons, List.length_map,
        inductionHypothesis]

/-- Horner evaluation of an integer coefficient list after embedding it in
the constructive rationals. -/
def evalIntegers (point : Rational) (coefficients : List Int) : Rational :=
  evalCoeffs point (coefficients.map fun (coefficient : Int) =>
    (coefficient : Rational))

@[simp] theorem evalIntegers_nil (point : Rational) :
    evalIntegers point [] = 0 := rfl

theorem evalIntegers_cons (point : Rational) (coefficient : Int)
    (remaining : List Int) :
    evalIntegers point (coefficient :: remaining) =
      (coefficient : Rational) * point ^ remaining.length +
        evalIntegers point remaining := by
  simp only [evalIntegers, List.map_cons, evalCoeffs_cons_expansion,
    List.length_map]

theorem evalIntegers_map_mul (point : Rational) (initial : Int)
    (coefficients : List Int) :
    evalIntegers point (coefficients.map fun value => initial * value) =
      (initial : Rational) * evalIntegers point coefficients := by
  induction coefficients with
  | nil => simp only [List.map_nil, evalIntegers_nil, mul_zero]
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.map_cons, evalIntegers_cons, List.length_map,
        QuotientFreeRing.intCast_mul, inductionHypothesis]
      ring1

/-- Clearing multiplies evaluation by exactly the displayed common
denominator. -/
theorem eval_clear (point : Rational) (coefficients : List Rational) :
    evalIntegers point (clear coefficients).coefficients =
      ((clear coefficients).denominator : Rational) *
        evalCoeffs point coefficients := by
  induction coefficients with
  | nil => simp [clear, evalIntegers, evalCoeffs]
  | cons coefficient remaining inductionHypothesis =>
      let head := representative coefficient
      let tail := clear remaining
      rw [show (clear (coefficient :: remaining)).coefficients =
          head.num * (tail.denominator : Int) ::
            tail.coefficients.map (fun value => (head.den : Int) * value)
        from rfl]
      rw [evalIntegers_cons, List.length_map, clear_length,
        evalIntegers_map_mul, QuotientFreeRing.intCast_mul, Int.cast_natCast,
        inductionHypothesis]
      change
        (head.num : Rational) * (tail.denominator : Rational) *
              point ^ remaining.length +
            (head.den : Rational) *
              ((tail.denominator : Rational) * evalCoeffs point remaining) =
          ((head.den * tail.denominator : Nat) : Rational) *
            evalCoeffs point (coefficient :: remaining)
      have clearance := representative_mul_den coefficient
      change coefficient * (head.den : Rational) =
        (head.num : Rational) at clearance
      rw [evalCoeffs_cons_expansion, ← clearance, Nat.cast_mul]
      ring1

/-! ## Homogeneous integer evaluation -/

/-- High-to-low homogeneous evaluation.  For `m+1` coefficients it is the
ordinary rational evaluation at `num/den`, multiplied by `den^m`. -/
def homogeneousEval (num : Int) (den : Nat) : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      coefficient * num ^ remaining.length +
        (den : Int) * homogeneousEval num den remaining

/-- Last high-to-low coefficient, with zero only for the empty list. -/
def constantCoefficient : List Int → Int
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

@[simp] theorem constantCoefficient_singleton (coefficient : Int) :
    constantCoefficient [coefficient] = coefficient := rfl

@[simp] theorem constantCoefficient_cons_cons
    (leading next : Int) (remaining : List Int) :
    constantCoefficient (leading :: next :: remaining) =
      constantCoefficient (next :: remaining) := by
  simp only [constantCoefficient, List.foldl_cons]

/-- Every term below the leading term contains the displayed denominator. -/
theorem denominator_dvd_homogeneousEval_sub_leading
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    (den : Int) ∣
      homogeneousEval num den (leading :: remaining) -
        leading * num ^ remaining.length := by
  refine ⟨homogeneousEval num den remaining, ?_⟩
  simp only [homogeneousEval]
  ring1

/-- Every term above the constant term contains the displayed numerator. -/
theorem numerator_dvd_homogeneousEval_sub_constant
    (num : Int) (den : Nat) (leading : Int) (remaining : List Int) :
    num ∣
      homogeneousEval num den (leading :: remaining) -
        constantCoefficient (leading :: remaining) *
          (den : Int) ^ remaining.length := by
  induction remaining generalizing leading with
  | nil =>
      refine ⟨0, ?_⟩
      simp [homogeneousEval, constantCoefficient]
  | cons next remaining inductionHypothesis =>
      rcases inductionHypothesis next with ⟨factor, factorization⟩
      refine ⟨leading * num ^ remaining.length + (den : Int) * factor, ?_⟩
      simp only [homogeneousEval, constantCoefficient_cons_cons,
        List.length_cons, pow_succ]
      calc
        leading * (num ^ remaining.length * num) +
              (den : Int) * homogeneousEval num den (next :: remaining) -
            constantCoefficient (next :: remaining) *
              ((den : Int) ^ remaining.length * den) =
            num * (leading * num ^ remaining.length) +
              (den : Int) *
                (homogeneousEval num den (next :: remaining) -
                  constantCoefficient (next :: remaining) *
                    (den : Int) ^ remaining.length) := by
          ring1
        _ = num *
            (leading * num ^ remaining.length + (den : Int) * factor) := by
          rw [factorization]
          ring1

theorem homogeneousEval_cons_eq_scaled
    (num : Int) {den : Nat} (denPositive : 0 < den)
    (coefficient : Int) (remaining : List Int) :
    ((homogeneousEval num den (coefficient :: remaining) : Int) : Rational) =
      (den : Rational) ^ remaining.length *
        evalIntegers ((num : Rational) / (den : Rational))
          (coefficient :: remaining) := by
  induction remaining generalizing coefficient with
  | nil =>
      simp [homogeneousEval, evalIntegers, evalCoeffs]
  | cons next remaining inductionHypothesis =>
      let denominator : Rational := den
      let numerator : Rational := num
      let point : Rational := numerator / denominator
      have denominatorNonzero : denominator ≠ 0 := by
        change (den : Rational) ≠ 0
        intro equal
        have denZero : den = 0 :=
          RFAP.ConstructiveFraction.natCast_injective_direct
            (equal.trans (Nat.cast_zero).symm)
        exact (Nat.ne_of_gt denPositive) denZero
      have pointClear : denominator * point = numerator := by
        change (den : Rational) * ((num : Rational) / (den : Rational)) =
          (num : Rational)
        rw [RFAP.ConstructiveFraction.mul_comm]
        exact RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero
      have powerClear :
          denominator ^ (List.length (next :: remaining)) *
              point ^ (List.length (next :: remaining)) =
            numerator ^ (List.length (next :: remaining)) := by
        rw [← mul_pow, pointClear]
      change
        ((coefficient * num ^ (next :: remaining).length +
            (den : Int) * homogeneousEval num den (next :: remaining) : Int) :
            Rational) =
          denominator ^ (List.length (next :: remaining)) *
            evalIntegers point (coefficient :: next :: remaining)
      rw [Int.cast_add, QuotientFreeRing.intCast_mul, QuotientFreeRing.intCast_mul, QuotientFreeRing.intCast_pow,
        Int.cast_natCast, inductionHypothesis]
      conv_rhs =>
        rw [evalIntegers_cons point coefficient (next :: remaining)]
      change
        (coefficient : Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
          denominator ^ (List.length (next :: remaining)) *
            ((coefficient : Rational) *
                point ^ (List.length (next :: remaining)) +
              evalIntegers point (next :: remaining))
      calc
        (coefficient : Rational) *
              numerator ^ (List.length (next :: remaining)) +
            denominator *
              (denominator ^ remaining.length *
                evalIntegers point (next :: remaining)) =
            (coefficient : Rational) *
                (denominator ^ (List.length (next :: remaining)) *
                  point ^ (List.length (next :: remaining))) +
              (denominator * denominator ^ remaining.length) *
                evalIntegers point (next :: remaining) := by
          rw [powerClear]
          ring1
        _ = _ := by
          rw [List.length_cons, pow_succ]
          ring1

/-! ## The finite rational-root bounds -/

private theorem natCast_ne_zero_of_pos {value : Nat} (positive : 0 < value) :
    (value : Rational) ≠ 0 := by
  intro equal
  have valueZero : value = 0 :=
    RFAP.ConstructiveFraction.natCast_injective_direct
      (equal.trans (Nat.cast_zero).symm)
  exact (Nat.ne_of_gt positive) valueZero

/-- The canonical finite representative is its displayed numerator divided
by its displayed positive denominator. -/
theorem representative_eq_num_div_den (value : Rational) :
    value = ((representative value).num : Rational) /
      ((representative value).den : Rational) := by
  let reduced := representative value
  have denominatorNonzero : (reduced.den : Rational) ≠ 0 :=
    natCast_ne_zero_of_pos reduced.den_pos
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne denominatorNonzero
  rw [representative_mul_den]
  exact (RFAP.ExplicitField.div_mul_cancel
    (reduced.num : Rational) denominatorNonzero).symm

private theorem natAbs_dvd_natAbs_of_dvd {left right : Int}
    (dvd : left ∣ right) : left.natAbs ∣ right.natAbs := by
  rcases dvd with ⟨factor, rfl⟩
  refine ⟨factor.natAbs, ?_⟩
  exact Int.natAbs_mul left factor

/-- Sum of absolute values, used as a deliberately coarse common bound for
the finitely many cleared coefficients. -/
def coefficientBound : List Int → Nat
  | [] => 0
  | coefficient :: remaining =>
      coefficient.natAbs + coefficientBound remaining

theorem coefficient_natAbs_le_bound
    {coefficient : Int} {coefficients : List Int}
    (member : coefficient ∈ coefficients) :
    coefficient.natAbs ≤ coefficientBound coefficients := by
  induction coefficients with
  | nil => contradiction
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact Nat.le_add_right _ _
      · exact le_trans (inductionHypothesis tailMember)
          (Nat.le_add_left _ _)

theorem constantCoefficient_mem
    (leading : Int) (remaining : List Int) :
    constantCoefficient (leading :: remaining) ∈ leading :: remaining := by
  induction remaining generalizing leading with
  | nil => exact List.mem_cons_self
  | cons next remaining inductionHypothesis =>
      rw [constantCoefficient_cons_cons]
      exact List.mem_cons_of_mem leading (inductionHypothesis next)

/-- A homogeneous zero with coprime numerator and denominator has numerator
dividing the displayed constant coefficient and denominator dividing the
displayed leading coefficient.  These are the sharp finite facts consumed by
the divisor candidate enumerator below. -/
theorem reduced_divisors_of_homogeneous_zero
    (reduced : ReducedFraction) (leading : Int) (remaining : List Int)
    (_leadingNonzero : leading ≠ 0)
    (_constantNonzero :
      constantCoefficient (leading :: remaining) ≠ 0)
    (zero : homogeneousEval reduced.num reduced.den
      (leading :: remaining) = 0) :
    reduced.num.natAbs ∣
        (constantCoefficient (leading :: remaining)).natAbs ∧
      reduced.den ∣ leading.natAbs := by
  have denominatorDvdInteger :=
    denominator_dvd_homogeneousEval_sub_leading reduced.num reduced.den
      leading remaining
  rw [zero, zero_sub] at denominatorDvdInteger
  have denominatorDvdNat :=
    natAbs_dvd_natAbs_of_dvd denominatorDvdInteger
  simp only [Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_mul,
    Int.natAbs_pow] at denominatorDvdNat
  have denominatorDvdLeading : reduced.den ∣ leading.natAbs :=
    by
      rcases reduced.reduced with ⟨certificate⟩
      exact certificate.symm.dvd_of_dvd_mul_right_pow
        remaining.length denominatorDvdNat

  have numeratorDvdInteger :=
    numerator_dvd_homogeneousEval_sub_constant reduced.num reduced.den
      leading remaining
  rw [zero, zero_sub] at numeratorDvdInteger
  have numeratorDvdNat := natAbs_dvd_natAbs_of_dvd numeratorDvdInteger
  simp only [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_natCast] at numeratorDvdNat
  have numeratorDvdConstant :
      reduced.num.natAbs ∣
        (constantCoefficient (leading :: remaining)).natAbs :=
    by
      rcases reduced.reduced with ⟨certificate⟩
      exact certificate.dvd_of_dvd_mul_right_pow
        remaining.length numeratorDvdNat

  exact ⟨numeratorDvdConstant, denominatorDvdLeading⟩

/-- The former common-bound corollary remains useful for coarse coefficient
accounts, but candidate generation no longer scans its full rectangle. -/
theorem reduced_bounds_of_homogeneous_zero
    (reduced : ReducedFraction) (leading : Int) (remaining : List Int)
    (leadingNonzero : leading ≠ 0)
    (constantNonzero :
      constantCoefficient (leading :: remaining) ≠ 0)
    (zero : homogeneousEval reduced.num reduced.den
      (leading :: remaining) = 0) :
    reduced.num.natAbs ≤ coefficientBound (leading :: remaining) ∧
      reduced.den ≤ coefficientBound (leading :: remaining) := by
  have divisors := reduced_divisors_of_homogeneous_zero reduced leading
    remaining leadingNonzero constantNonzero zero
  constructor
  · exact le_trans
      (Nat.le_of_dvd (Int.natAbs_pos.mpr constantNonzero) divisors.1)
      (coefficient_natAbs_le_bound
        (constantCoefficient_mem leading remaining))
  · exact le_trans
      (Nat.le_of_dvd (Int.natAbs_pos.mpr leadingNonzero) divisors.2)
      (coefficient_natAbs_le_bound List.mem_cons_self)

/-- An exact rational zero of a nonempty displayed coefficient list gives a
zero of its finitely cleared homogeneous integer list. -/
theorem homogeneous_zero_of_eval_zero
    (point : Rational) (coefficient : Rational) (remaining : List Rational)
    (zero : evalCoeffs point (coefficient :: remaining) = 0) :
    homogeneousEval (representative point).num (representative point).den
      (clear (coefficient :: remaining)).coefficients = 0 := by
  have clearedZero :
      evalIntegers point (clear (coefficient :: remaining)).coefficients = 0 := by
    rw [eval_clear, zero, mul_zero]
  let leading :=
    (representative coefficient).num *
      ((clear remaining).denominator : Int)
  let integerRemaining :=
    (clear remaining).coefficients.map
      (fun value => ((representative coefficient).den : Int) * value)
  have clearedShape :
      (clear (coefficient :: remaining)).coefficients =
        leading :: integerRemaining := rfl
  rw [clearedShape] at clearedZero ⊢
  rw [representative_eq_num_div_den point] at clearedZero
  have scaled := homogeneousEval_cons_eq_scaled
    (representative point).num (representative point).den_pos
    leading integerRemaining
  rw [clearedZero, mul_zero] at scaled
  exact RFAP.ConstructiveFraction.intCast_injective_direct scaled

/-! ## Removing only finitely displayed trailing zeros -/

/-- A finite high-to-low coefficient list with all of its displayed trailing
zeros removed. -/
def trimTrailing (coefficients : List Rational) : List Rational :=
  (coefficients.reverse.dropWhile (· = 0)).reverse

/-- The finite suffix removed by `trimTrailing`, retained explicitly for the
evaluation proof. -/
def trailingPart (coefficients : List Rational) : List Rational :=
  (coefficients.reverse.takeWhile (· = 0)).reverse

theorem trimTrailing_append_trailingPart (coefficients : List Rational) :
    trimTrailing coefficients ++ trailingPart coefficients = coefficients := by
  unfold trimTrailing trailingPart
  rw [← List.reverse_append, List.takeWhile_append_dropWhile,
    List.reverse_reverse]

private theorem mem_takeWhile_zero
    {value : Rational} {coefficients : List Rational}
    (member : value ∈ coefficients.takeWhile (· = 0)) : value = 0 := by
  induction coefficients with
  | nil => contradiction
  | cons coefficient remaining inductionHypothesis =>
      by_cases coefficientZero : coefficient = 0
      · simp only [List.takeWhile, coefficientZero, decide_true,
          List.mem_cons] at member
        rcases member with equal | tailMember
        · exact equal
        · exact inductionHypothesis tailMember
      · simp only [List.takeWhile, coefficientZero, decide_false,
          List.not_mem_nil] at member

private theorem eq_replicate_zero_of_all
    (coefficients : List Rational)
    (allZero : ∀ value ∈ coefficients, value = 0) :
    coefficients = List.replicate coefficients.length 0 := by
  induction coefficients with
  | nil => rfl
  | cons value remaining inductionHypothesis =>
      have valueZero := allZero value List.mem_cons_self
      have remainingZero : ∀ member ∈ remaining, member = 0 := by
        intro member memberIn
        exact allZero member (List.mem_cons_of_mem value memberIn)
      rw [valueZero]
      change 0 :: remaining = 0 :: List.replicate remaining.length 0
      exact congrArg (List.cons (0 : Rational))
        (inductionHypothesis remainingZero)

private theorem trailingPart_eq_replicate (coefficients : List Rational) :
    trailingPart coefficients =
      List.replicate (trailingPart coefficients).length 0 := by
  have allZero : ∀ value ∈ trailingPart coefficients, value = 0 := by
    intro value member
    unfold trailingPart at member
    rw [List.mem_reverse] at member
    exact mem_takeWhile_zero member
  exact eq_replicate_zero_of_all (trailingPart coefficients) allZero

theorem eval_trimTrailing_mul_power
    (point : Rational) (coefficients : List Rational) :
    evalCoeffs point coefficients =
      evalCoeffs point (trimTrailing coefficients) *
        point ^ (trailingPart coefficients).length := by
  let kept := trimTrailing coefficients
  let removed := trailingPart coefficients
  have decomposition : kept ++ removed = coefficients :=
    trimTrailing_append_trailingPart coefficients
  have removedZeros : removed = List.replicate removed.length 0 :=
    trailingPart_eq_replicate coefficients
  calc
    evalCoeffs point coefficients = evalCoeffs point (kept ++ removed) := by
      rw [decomposition]
    _ = evalCoeffs point (kept ++ List.replicate removed.length 0) := by
      exact congrArg (evalCoeffs point)
        (congrArg (fun suffix => kept ++ suffix) removedZeros)
    _ = evalCoeffs point kept * point ^ removed.length :=
      evalCoeffs_append_replicate_zero point kept removed.length
    _ = _ := rfl

/-- A nonzero root survives removal of finitely many trailing zero
coefficients. -/
private theorem pow_ne_zero_direct (point : Rational) (pointNonzero : point ≠ 0) :
    (exponent : Nat) → point ^ exponent ≠ 0
  | 0 => by
      change (1 : Rational) ≠ 0
      decide
  | exponent + 1 => by
      rw [pow_succ]
      exact RFAP.ExplicitField.mul_ne_zero
        (pow_ne_zero_direct point pointNonzero exponent) pointNonzero

theorem eval_trimTrailing_eq_zero_of_nonzero_root
    (point : Rational) (coefficients : List Rational)
    (pointNonzero : point ≠ 0) (root : evalCoeffs point coefficients = 0) :
    evalCoeffs point (trimTrailing coefficients) = 0 := by
  rw [eval_trimTrailing_mul_power] at root
  by_contra trimmedNonzero
  have powerNonzero :
      point ^ (trailingPart coefficients).length ≠ 0 :=
    pow_ne_zero_direct point pointNonzero _
  exact (RFAP.ExplicitField.mul_ne_zero trimmedNonzero powerNonzero) root

/-- A nonzero displayed leading coefficient is retained by trailing
trimming. -/
theorem trimTrailing_cons_of_leading_nonzero
    (leading : Rational) (remaining : List Rational)
    (leadingNonzero : leading ≠ 0) :
    ∃ trimmedRemaining,
      trimTrailing (leading :: remaining) = leading :: trimmedRemaining := by
  have decomposition :=
    trimTrailing_append_trailingPart (leading :: remaining)
  have nonempty : trimTrailing (leading :: remaining) ≠ [] := by
    intro empty
    rw [empty, List.nil_append] at decomposition
    have leadingMember : leading ∈ trailingPart (leading :: remaining) := by
      rw [decomposition]
      exact List.mem_cons_self
    have trailingZeros := trailingPart_eq_replicate (leading :: remaining)
    rw [trailingZeros, List.mem_replicate] at leadingMember
    exact leadingNonzero leadingMember.2
  cases shape : trimTrailing (leading :: remaining) with
  | nil => exact (nonempty shape).elim
  | cons trimmedLeading trimmedRemaining =>
      rw [shape] at decomposition
      have leadingEqual : trimmedLeading = leading := by
        injection decomposition
      exact ⟨trimmedRemaining,
        congrArg (fun value => value :: trimmedRemaining) leadingEqual⟩

/-- Last rational coefficient, with zero only for the empty list. -/
def rationalConstantCoefficient : List Rational → Rational
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

@[simp] theorem rationalConstantCoefficient_singleton (coefficient : Rational) :
    rationalConstantCoefficient [coefficient] = coefficient := rfl

@[simp] theorem rationalConstantCoefficient_cons_cons
    (leading next : Rational) (remaining : List Rational) :
    rationalConstantCoefficient (leading :: next :: remaining) =
      rationalConstantCoefficient (next :: remaining) := by
  simp only [rationalConstantCoefficient, List.foldl_cons]

theorem rationalConstantCoefficient_append_singleton
    (coefficients : List Rational) (coefficient : Rational) :
    rationalConstantCoefficient (coefficients ++ [coefficient]) =
      coefficient := by
  induction coefficients with
  | nil => rfl
  | cons leading remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next remaining =>
          rw [List.cons_append, List.cons_append,
            rationalConstantCoefficient_cons_cons]
          exact inductionHypothesis

/-- Reverse induction derived directly from ordinary finite-list induction. -/
private theorem finiteReverseRec {α : Type*} {motive : List α → Prop}
    (nilCase : motive [])
    (snocCase : ∀ list value, motive list → motive (list ++ [value]))
    (list : List α) : motive list := by
  have reversed : ∀ source : List α, motive source.reverse := by
    intro source
    induction source with
    | nil => simpa using nilCase
    | cons value remaining inductionHypothesis =>
        rw [List.reverse_cons]
        exact snocCase remaining.reverse value inductionHypothesis
  simpa using reversed list.reverse

/-- Every nonempty trailing-trim result ends in a nonzero coefficient.  The
proof is a direct reverse induction on the finite source list, avoiding the
choice-bearing generic `getLast` convenience route. -/
theorem trimTrailing_constant_nonzero
    (coefficients : List Rational) (leading : Rational)
    (remaining : List Rational)
    (shape : trimTrailing coefficients = leading :: remaining) :
    rationalConstantCoefficient (leading :: remaining) ≠ 0 := by
  apply finiteReverseRec
    (motive := fun source => ∀ leading remaining,
      trimTrailing source = leading :: remaining →
        rationalConstantCoefficient (leading :: remaining) ≠ 0)
    (by intro leading remaining impossible; simp [trimTrailing] at impossible)
    (by
      intro coefficients coefficient inductionHypothesis leading remaining shape
      simp only [trimTrailing, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.dropWhile] at shape
      split at shape
      · exact inductionHypothesis leading remaining (by
          simpa only [trimTrailing] using shape)
      · rename_i coefficientNonzero
        have constantIdentity := congrArg rationalConstantCoefficient shape
        simp only [List.reverse_cons, List.reverse_reverse,
          rationalConstantCoefficient_append_singleton] at constantIdentity
        intro constantZero
        have coefficientZero : coefficient = 0 :=
          constantIdentity.trans constantZero
        rw [coefficientZero] at coefficientNonzero
        contradiction)
    coefficients leading remaining shape

private theorem representative_num_ne_zero {value : Rational}
    (nonzero : value ≠ 0) : (representative value).num ≠ 0 := by
  intro numeratorZero
  apply nonzero
  rw [representative_eq_num_div_den value, numeratorZero]
  exact RFAP.ExplicitField.zero_div _

private theorem constantCoefficient_map_mul (factor : Int)
    (leading : Int) (remaining : List Int) :
    constantCoefficient
        ((leading :: remaining).map fun value => factor * value) =
      factor * constantCoefficient (leading :: remaining) := by
  induction remaining generalizing leading with
  | nil => rfl
  | cons next remaining inductionHypothesis =>
      rw [List.map_cons, List.map_cons, constantCoefficient_cons_cons,
        constantCoefficient_cons_cons]
      exact inductionHypothesis next

/-- A nonzero first rational coefficient clears to a nonzero first integer
coefficient. -/
theorem clear_leading_nonzero
    (leading : Rational) (remaining : List Rational)
    (nonzero : leading ≠ 0) :
    ∃ integerLeading integerRemaining,
      (clear (leading :: remaining)).coefficients =
          integerLeading :: integerRemaining ∧
        integerLeading ≠ 0 := by
  let numerator := (representative leading).num
  let multiplier : Int := clear remaining |>.denominator
  refine ⟨numerator * multiplier,
    (clear remaining).coefficients.map
      (fun value => ((representative leading).den : Int) * value), rfl, ?_⟩
  exact Int.mul_ne_zero (representative_num_ne_zero nonzero)
    (Int.ofNat_ne_zero.mpr
      (Nat.ne_of_gt (clear remaining).denominatorPositive))

/-- A nonzero last rational coefficient clears to a nonzero last integer
coefficient. -/
theorem clear_constant_nonzero
    (leading : Rational) (remaining : List Rational)
    (nonzero : rationalConstantCoefficient (leading :: remaining) ≠ 0) :
    constantCoefficient (clear (leading :: remaining)).coefficients ≠ 0 := by
  induction remaining generalizing leading with
  | nil =>
      have leadingNonzero : leading ≠ 0 := by
        simpa only [rationalConstantCoefficient_singleton] using nonzero
      change (representative leading).num * (1 : Int) ≠ 0
      rw [Int.mul_one]
      exact representative_num_ne_zero leadingNonzero
  | cons next remaining inductionHypothesis =>
      let integerLeading :=
        (representative next).num * ((clear remaining).denominator : Int)
      let integerRemaining :=
        (clear remaining).coefficients.map
          (fun value => ((representative next).den : Int) * value)
      have tailShape :
          (clear (next :: remaining)).coefficients =
            integerLeading :: integerRemaining := rfl
      rw [show (clear (leading :: next :: remaining)).coefficients =
          (representative leading).num *
              ((clear (next :: remaining)).denominator : Int) ::
            (clear (next :: remaining)).coefficients.map
              (fun value => ((representative leading).den : Int) * value)
        from rfl]
      rw [tailShape, List.map_cons, constantCoefficient_cons_cons]
      rw [← List.map_cons, constantCoefficient_map_mul]
      exact Int.mul_ne_zero
        (Int.ofNat_ne_zero.mpr
          (Nat.ne_of_gt (representative leading).den_pos))
        (by
          rw [← tailShape]
          exact inductionHypothesis next (by
            simpa only [rationalConstantCoefficient_cons_cons] using nonzero))

/-! ## Executable bounded enumeration -/

/-- Indices `d-1` of the positive divisors `d` of one displayed natural.
The source is a finite range, so this is executable without a global divisor
set. -/
def positiveDivisorIndices (value : Nat) : List Nat :=
  (List.range value).filter (fun index => index + 1 ∣ value)

theorem mem_positiveDivisorIndices {index value : Nat}
    (bounded : index < value) (divides : index + 1 ∣ value) :
    index ∈ positiveDivisorIndices value := by
  simp only [positiveDivisorIndices, List.mem_filter, QuotientFreeList.mem_range,
    bounded, divides, decide_true, and_self]

theorem positiveDivisorIndices_length_le (value : Nat) :
    (positiveDivisorIndices value).length ≤ value := by
  calc
    (positiveDivisorIndices value).length ≤ (List.range value).length :=
      List.length_filter_le _ _
    _ = value := List.length_range

/-- Both signs of every positive divisor of one displayed natural. -/
def signedDivisors (value : Nat) : List Int :=
  (positiveDivisorIndices value).map
      (fun index => ((index + 1 : Nat) : Int)) ++
    (positiveDivisorIndices value).map
      (fun index => -((index + 1 : Nat) : Int))

theorem mem_signedDivisors {numerator : Int} {value : Nat}
    (valuePositive : 0 < value) (numeratorNonzero : numerator ≠ 0)
    (divides : numerator.natAbs ∣ value) :
    numerator ∈ signedDivisors value := by
  cases numerator with
  | ofNat magnitude =>
      have magnitudeDivides : magnitude ∣ value := by
        change magnitude ∣ value at divides
        exact divides
      have magnitudePositive : 0 < magnitude := by
        cases magnitude with
        | zero => exact (numeratorNonzero rfl).elim
        | succ predecessor => exact Nat.zero_lt_succ predecessor
      have magnitudeBound : magnitude ≤ value :=
        Nat.le_of_dvd valuePositive divides
      let index := magnitude - 1
      have indexBound : index < value := by
        dsimp only [index]
        exact (Nat.sub_lt_of_pos_le (by decide) magnitudePositive).trans_le
          magnitudeBound
      have indexIdentity : index + 1 = magnitude := by
        dsimp only [index]
        exact Nat.sub_add_cancel magnitudePositive
      rw [signedDivisors, List.mem_append]
      left
      apply QuotientFreeList.mem_map.mpr
      refine ⟨index,
        mem_positiveDivisorIndices indexBound ?_, ?_⟩
      · simpa only [indexIdentity] using magnitudeDivides
      · rw [indexIdentity]
        rfl
  | negSucc predecessor =>
      have magnitudeBound : predecessor + 1 ≤ value :=
        Nat.le_of_dvd valuePositive divides
      have indexBound : predecessor < value :=
        Nat.lt_of_succ_le magnitudeBound
      rw [signedDivisors, List.mem_append]
      right
      apply QuotientFreeList.mem_map.mpr
      refine ⟨predecessor,
        mem_positiveDivisorIndices indexBound ?_, ?_⟩
      · exact divides
      · simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]

/-- The fraction with numerator `num` and positive denominator `index+1`. -/
def displayedFraction (num : Int) (denominatorIndex : Nat) : Rational :=
  ofFraction
    ⟨num, (denominatorIndex + 1 : Nat), by
      exact Int.natCast_pos.mpr (Nat.zero_lt_succ denominatorIndex)⟩

/-- Fractions whose nonzero signed numerator divides `numeratorMagnitude` and
whose positive denominator divides `denominatorMagnitude`.  Denominators are
stored as `index+1`, so no positivity proof is recovered from list
membership. -/
def divisorFractions (numeratorMagnitude denominatorMagnitude : Nat) :
    List Rational :=
  (positiveDivisorIndices denominatorMagnitude).flatMap
    (fun denominatorIndex =>
      (signedDivisors numeratorMagnitude).map
        (fun numerator => displayedFraction numerator denominatorIndex))

/-- Both signs of every magnitude at most the finite bound.  Zero is
duplicated harmlessly; callers may deduplicate their final exact list. -/
def signedNumerators (bound : Nat) : List Int :=
  (List.range (bound + 1)).map (fun (magnitude : Nat) => (magnitude : Int)) ++
    (List.range (bound + 1)).map
      (fun (magnitude : Nat) => -(magnitude : Int))

theorem mem_signedNumerators {numerator : Int} {bound : Nat}
    (bounded : numerator.natAbs ≤ bound) :
    numerator ∈ signedNumerators bound := by
  cases numerator with
  | ofNat magnitude =>
      change magnitude ≤ bound at bounded
      rw [signedNumerators, List.mem_append]
      left
      exact QuotientFreeList.mem_map_of_mem
        (f := fun value : Nat => (value : Int))
        (QuotientFreeList.mem_range.mpr (Nat.lt_succ_of_le bounded))
  | negSucc predecessor =>
      let magnitude := predecessor + 1
      have magnitudeBound : magnitude ≤ bound := by
        change predecessor + 1 ≤ bound at bounded
        exact bounded
      rw [signedNumerators, List.mem_append]
      right
      have member := QuotientFreeList.mem_map_of_mem
        (f := fun value : Nat => -(value : Int))
        (QuotientFreeList.mem_range.mpr (Nat.lt_succ_of_le magnitudeBound))
      change Int.negSucc predecessor ∈
        (List.range (bound + 1)).map
          (fun (value : Nat) => -(value : Int))
      simpa only [magnitude, Int.negSucc_eq, Nat.cast_add, Nat.cast_one,
        Nat.succ_eq_add_one] using member

/-- All displayed fractions whose numerator magnitude and positive
denominator are at most `bound`.  This is a finite rectangular over-search,
not a list of all rationals. -/
def boundedFractions (bound : Nat) : List Rational :=
  (List.range bound).flatMap fun denominatorIndex =>
    (signedNumerators bound).map fun numerator =>
      displayedFraction numerator denominatorIndex

@[simp] theorem signedNumerators_length (bound : Nat) :
    (signedNumerators bound).length = 2 * (bound + 1) := by
  simp only [signedNumerators, List.length_append, List.length_map,
    List.length_range]
  rw [two_mul]

private theorem length_flatMap_map
    {Outer Inner Result : Type}
    (outer : List Outer) (inner : List Inner) (f : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (f left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons left remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

@[simp] theorem signedDivisors_length (value : Nat) :
    (signedDivisors value).length =
      2 * (positiveDivisorIndices value).length := by
  simp only [signedDivisors, List.length_append, List.length_map]
  rw [two_mul]

theorem divisorFractions_length_le
    (numeratorMagnitude denominatorMagnitude : Nat) :
    (divisorFractions numeratorMagnitude denominatorMagnitude).length ≤
      2 * numeratorMagnitude * denominatorMagnitude := by
  rw [divisorFractions, length_flatMap_map, signedDivisors_length]
  have numeratorBound :=
    positiveDivisorIndices_length_le numeratorMagnitude
  have denominatorBound :=
    positiveDivisorIndices_length_le denominatorMagnitude
  calc
    (positiveDivisorIndices denominatorMagnitude).length *
          (2 * (positiveDivisorIndices numeratorMagnitude).length) ≤
        denominatorMagnitude * (2 * numeratorMagnitude) :=
      Nat.mul_le_mul denominatorBound (Nat.mul_le_mul_left 2 numeratorBound)
    _ = 2 * numeratorMagnitude * denominatorMagnitude := by ring1

@[simp] theorem boundedFractions_length (bound : Nat) :
    (boundedFractions bound).length = 2 * bound * (bound + 1) := by
  rw [boundedFractions, length_flatMap_map]
  simp only [List.length_range, signedNumerators_length]
  ring1

theorem mem_boundedFractions_of_representative_bounds
    (point : Rational) (bound : Nat)
    (numeratorBound : (representative point).num.natAbs ≤ bound)
    (denominatorBound : (representative point).den ≤ bound) :
    point ∈ boundedFractions bound := by
  let reduced := representative point
  let denominatorIndex := reduced.den - 1
  have denominatorIndexMem : denominatorIndex ∈ List.range bound := by
    apply QuotientFreeList.mem_range.mpr
    change reduced.den ≤ bound at denominatorBound
    exact (Nat.sub_lt_of_pos_le (by decide) reduced.den_pos).trans_le
      denominatorBound
  have denominatorIdentity : denominatorIndex + 1 = reduced.den := by
    exact Nat.sub_add_cancel reduced.den_pos
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨denominatorIndex, denominatorIndexMem, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨reduced.num, mem_signedNumerators numeratorBound, ?_⟩
  rw [displayedFraction]
  calc
    ofFraction ⟨reduced.num, (denominatorIndex + 1 : Nat), by
        exact Int.natCast_pos.mpr (Nat.zero_lt_succ denominatorIndex)⟩ =
        ofFraction reduced.toFraction := by
      apply ofFraction_eq_of_equivalent
      change reduced.num * (reduced.den : Int) =
        reduced.num * (denominatorIndex + 1 : Nat)
      rw [denominatorIdentity]
    _ = point := representative_spec point

/-- Endpoint divisibility places one nonzero reduced rational directly in the
finite divisor product; no magnitude rectangle is inspected. -/
theorem mem_divisorFractions_of_representative_divisors
    (point : Rational) (numeratorMagnitude denominatorMagnitude : Nat)
    (pointNonzero : point ≠ 0)
    (numeratorMagnitudePositive : 0 < numeratorMagnitude)
    (denominatorMagnitudePositive : 0 < denominatorMagnitude)
    (numeratorDivides :
      (representative point).num.natAbs ∣ numeratorMagnitude)
    (denominatorDivides :
      (representative point).den ∣ denominatorMagnitude) :
    point ∈ divisorFractions numeratorMagnitude denominatorMagnitude := by
  let reduced := representative point
  let denominatorIndex := reduced.den - 1
  have denominatorBound : reduced.den ≤ denominatorMagnitude :=
    Nat.le_of_dvd denominatorMagnitudePositive denominatorDivides
  have denominatorIndexBound : denominatorIndex < denominatorMagnitude := by
    dsimp only [denominatorIndex]
    exact (Nat.sub_lt_of_pos_le (by decide) reduced.den_pos).trans_le
      denominatorBound
  have denominatorIdentity : denominatorIndex + 1 = reduced.den := by
    exact Nat.sub_add_cancel reduced.den_pos
  have denominatorIndexMember :
      denominatorIndex ∈ positiveDivisorIndices denominatorMagnitude := by
    apply mem_positiveDivisorIndices denominatorIndexBound
    simpa only [denominatorIdentity] using denominatorDivides
  have numeratorMember : reduced.num ∈ signedDivisors numeratorMagnitude :=
    mem_signedDivisors numeratorMagnitudePositive
      (representative_num_ne_zero pointNonzero) numeratorDivides
  rw [divisorFractions]
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨denominatorIndex, denominatorIndexMember, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨reduced.num, numeratorMember, ?_⟩
  rw [displayedFraction]
  calc
    ofFraction ⟨reduced.num, (denominatorIndex + 1 : Nat), by
        exact Int.natCast_pos.mpr (Nat.zero_lt_succ denominatorIndex)⟩ =
        ofFraction reduced.toFraction := by
      apply ofFraction_eq_of_equivalent
      change reduced.num * (reduced.den : Int) =
        reduced.num * (denominatorIndex + 1 : Nat)
      rw [denominatorIdentity]
    _ = point := representative_spec point

/-- Coarse finite search bound obtained from the actually displayed,
normalized, trailing-trimmed, denominator-cleared coefficients. -/
def candidateBound (p : Polynomial) : Nat :=
  coefficientBound
    (clear (trimTrailing p.normalize.coeffs)).coefficients

/-- A defensive upper bound on the number of displayed fractions inspected
by `candidates` for one polynomial.  It deliberately charges for both copies
of zero in `signedNumerators` as well as the separately tested zero. -/
def candidateSearchSize (bound : Nat) : Nat :=
  1 + 2 * bound * (bound + 1)

/-- First coefficient of a finite high-to-low integer list, or zero for the
empty defensive branch. -/
def leadingCoefficient : List Int → Int
  | [] => 0
  | coefficient :: _ => coefficient

/-- The actual finite integer polynomial on which endpoint divisibility is
applied. -/
def preparedCoefficients (p : Polynomial) : List Int :=
  (clear (trimTrailing p.normalize.coeffs)).coefficients

def numeratorEndpointMagnitude (p : Polynomial) : Nat :=
  (constantCoefficient (preparedCoefficients p)).natAbs

def denominatorEndpointMagnitude (p : Polynomial) : Nat :=
  (leadingCoefficient (preparedCoefficients p)).natAbs

/-- Work charged to the separately tested zero and the finite product of
signed constant-term divisors with positive leading-term divisors. -/
def divisorCandidateSearchSize (p : Polynomial) : Nat :=
  1 + 2 * numeratorEndpointMagnitude p * denominatorEndpointMagnitude p

/-- Derive and exactly filter the finite rational-root candidate list using
only divisors of the two nonzero endpoint coefficients.  Zero is tested
separately because it is the one root removed by trailing-zero trimming. -/
def candidates (p : Polynomial) : List Rational :=
  (0 :: divisorFractions (numeratorEndpointMagnitude p)
      (denominatorEndpointMagnitude p)).filter
    (fun candidate => p.eval candidate = 0)

/-- Exact filtering cannot make the finite endpoint-divisor product larger. -/
theorem candidates_length_le (p : Polynomial) :
    (candidates p).length ≤ divisorCandidateSearchSize p := by
  calc
    (candidates p).length ≤
        (0 :: divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)).length := by
      exact List.length_filter_le _ _
    _ = 1 + (divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)).length := by
      simp only [List.length_cons]
      exact Nat.add_comm _ _
    _ ≤ 1 + 2 * numeratorEndpointMagnitude p *
          denominatorEndpointMagnitude p :=
      Nat.add_le_add_left
        (divisorFractions_length_le (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p)) 1
    _ = divisorCandidateSearchSize p := rfl

/-- Every displayed rational root of a nonzero dense polynomial occurs in
the automatically derived finite candidate list.  The quantifier is over one
supplied value only; the construction itself is the finite list `candidates
p`. -/
theorem root_mem_candidates (p : Polynomial) (nonzero : p.isZero = false)
    (point : Rational) (root : p.eval point = 0) :
    point ∈ candidates p := by
  by_cases pointZero : point = 0
  · subst point
    simp only [candidates, List.mem_filter, List.mem_cons, true_or,
      root, decide_true, and_self]
  · rcases normalized_coeffs_shape nonzero with
      ⟨remaining, normalizedShape, _degreeShape⟩
    have leadingNonzero := leadingCoeff_ne_zero nonzero
    rcases trimTrailing_cons_of_leading_nonzero p.leadingCoeff remaining
        leadingNonzero with ⟨trimmedRemaining, trimmedShape⟩
    have normalizedRoot :
        evalCoeffs point p.normalize.coeffs = 0 := by
      change p.normalize.eval point = 0
      rw [eval_normalize, root]
    have trimmedRoot := eval_trimTrailing_eq_zero_of_nonzero_root point
      p.normalize.coeffs pointZero normalizedRoot
    rw [normalizedShape, trimmedShape] at trimmedRoot
    have homogeneousZero := homogeneous_zero_of_eval_zero point
      p.leadingCoeff trimmedRemaining trimmedRoot
    rcases clear_leading_nonzero p.leadingCoeff trimmedRemaining
        leadingNonzero with
      ⟨integerLeading, integerRemaining, clearedShape,
        integerLeadingNonzero⟩
    rw [clearedShape] at homogeneousZero
    have rationalConstantNonzero := trimTrailing_constant_nonzero
      (p.leadingCoeff :: remaining) p.leadingCoeff trimmedRemaining
      trimmedShape
    have integerConstantNonzero := clear_constant_nonzero
      p.leadingCoeff trimmedRemaining rationalConstantNonzero
    rw [clearedShape] at integerConstantNonzero
    have divisors := reduced_divisors_of_homogeneous_zero
      (representative point) integerLeading integerRemaining
      integerLeadingNonzero integerConstantNonzero homogeneousZero
    have divisorMember : point ∈
        divisorFractions (numeratorEndpointMagnitude p)
          (denominatorEndpointMagnitude p) := by
      apply mem_divisorFractions_of_representative_divisors point
      · exact pointZero
      · simpa only [numeratorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using Int.natAbs_pos.mpr integerConstantNonzero
      · simpa only [denominatorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using Int.natAbs_pos.mpr integerLeadingNonzero
      · simpa only [numeratorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using divisors.1
      · simpa only [denominatorEndpointMagnitude, preparedCoefficients,
          normalizedShape, trimmedShape, clearedShape, leadingCoefficient]
          using divisors.2
    simp only [candidates, List.mem_filter, List.mem_cons, divisorMember,
      or_true, root, decide_true, and_self]

end RFAP.ConstructiveRationalRootCandidates
