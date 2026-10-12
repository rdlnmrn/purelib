module

import Purelib.Data.Bool.Decide
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.CancelLead
import Purelib.Polynomial.Dense.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained fuel-bounded dense division

Each continuing step retains the original leading quotient and cancelled
polynomial, then consumes one unit of natural fuel. The result stores the same
quotient accumulator, normalized remainder and performed cancellation count.
Evaluation and degree certificates describe those exact retained outputs.
-/

namespace Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Algebra.Field
open Purelib.Data.Bool

variable {K : Type*} [ExplicitField K] [DecidableEq K]

set_option genInjectivity false in
/-- Finite output of dense long division.

The original dividend and divisor index the completed run. Its quotient,
remainder and performed step count are the exact outputs of that same run. -/
public structure DivResult (p q : DensePolynomial K) where
  /-- The polynomial quotient accumulated by this finite division run. -/ quotient : DensePolynomial K
  /-- The polynomial left after the performed cancellation steps. -/ remainder : DensePolynomial K
  /-- The number of leading-coefficient cancellation steps actually performed. -/ steps : ℕ

constructive_injectivity DivResult

/-- Fuel-bounded long division.  The initial fuel is coefficient-computable;
each call consumes one natural number regardless of coefficient values.

The original zero-test and degree guard decide whether to return the retained accumulator unchanged. Otherwise the
original leading quotient and cancelled dividend feed the next run, whose completed outputs are reused once. -/
@[expose] public def divLoop : ℕ → (p q quotient : DensePolynomial K) → DivResult p q
  := Nat.rec
    (fun p _q quotient => ⟨quotient, p, 0⟩)
    (fun _ recursive p q quotient =>
      if q.isZero || p.isZero || p.natDegree < q.natDegree then
        ⟨quotient, p, 0⟩
      else
        let term := leadQuotient p q
        let next := cancelLead p q
        let result := recursive next q (quotient + term)
        ⟨result.quotient, result.remainder, result.steps + 1⟩)

/-- Zero fuel returns the supplied quotient accumulator and unchanged dividend, with no steps. -/
@[simp] public theorem divLoop_zero (p q quotient : DensePolynomial K) :
    divLoop 0 p q quotient = ⟨quotient, p, 0⟩ := rfl

/-- Unfold one unit of division fuel into a stopping branch or one exact cancellation and recursive run.

The original stopping test either returns the current dividend and quotient or supplies the exact cancelled dividend and
updated quotient to the predecessor-fuel run. -/
public theorem divLoop_succ (fuel : Nat) (p q quotient : DensePolynomial K) :
    divLoop (fuel + 1) p q quotient =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then
        ⟨quotient, p, 0⟩
      else
        let term := leadQuotient p q
        let next := cancelLead p q
        let result := divLoop fuel next q (quotient + term)
        ⟨result.quotient, result.remainder, result.steps + 1⟩ := rfl

/-- The remainder after one fuel step is the dividend on stopping, otherwise the recursive cancellation remainder.

The quotient accumulator and step counter are left in the original result; this equality reads only its retained
remainder through the same stopping test. -/
public theorem divLoop_succ_remainder
    (fuel : Nat) (p q quotient : DensePolynomial K) :
    (divLoop (fuel + 1) p q quotient).remainder =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then p
      else (divLoop fuel (cancelLead p q) q
        (quotient + leadQuotient p q)).remainder := by
  rw [divLoop_succ]
  split <;> rfl

/-- Read the remainder coefficient count through the division stopping test and recursive branch.

The equality projects the original normalized coefficient count from the retained remainder without rebuilding either
branch output. -/
public theorem divLoop_succ_remainder_degreeCount
    (fuel : Nat) (p q quotient : DensePolynomial K) :
    (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
      if q.isZero || p.isZero || p.natDegree < q.natDegree then p.degreeCount
      else (divLoop fuel (cancelLead p q) q
        (quotient + leadQuotient p q)).remainder.degreeCount := by
  by_cases stopping :
      (q.isZero || p.isZero || p.natDegree < q.natDegree) = true
  · rw [if_pos stopping]
    apply congrArg degreeCount
    have remainder := divLoop_succ_remainder fuel p q quotient
    rw [if_pos stopping] at remainder
    exact remainder
  · rw [if_neg stopping]
    apply congrArg degreeCount
    have remainder := divLoop_succ_remainder fuel p q quotient
    rw [if_neg stopping] at remainder
    exact remainder

/-- Executable Euclidean division with a displayed finite fuel bound.

The normalized original inputs are passed to the same division loop with the displayed dividend count plus one. The
completed quotient, remainder and step count are retained under the original input indices. -/
@[expose] public def divMod (p q : DensePolynomial K) : DivResult p q :=
  let result := divLoop (p.degreeCount + 1) p.normalize q.normalize 0
  ⟨result.quotient, result.remainder, result.steps⟩

/-- Long division stops immediately when the dividend has smaller degree than
the divisor.  In particular, its quotient is zero and its remainder is the
normalized dividend.

Normalization retains both original degrees. The strict inequality makes the same first stopping guard true, so the
original zero quotient and normalized dividend are returned. -/
public theorem divMod_of_natDegree_lt {p q : DensePolynomial K}
    (hdegree : p.natDegree < q.natDegree) :
    (divMod p q).quotient = 0 ∧
      (divMod p q).remainder = p.normalize := by
  have smaller : p.normalize.natDegree < q.normalize.natDegree := by
    rewrite [natDegree_normalize, natDegree_normalize]
    exact hdegree
  have stopping : (q.normalize.isZero || p.normalize.isZero ||
      decide (p.normalize.natDegree < q.normalize.natDegree)) = true := by
    rewrite [decide_eq_true smaller]
    cases q.normalize.isZero || p.normalize.isZero <;> rfl
  unfold divMod
  rewrite [divLoop_succ, if_pos stopping]
  exact ⟨Eq.refl _, Eq.refl _⟩

/-- At every fuel depth, negating a nonzero divisor leaves the long-division
remainder unchanged.  Quotients are deliberately generalized away because
the remainder recursion does not inspect them.

The original nonzero divisor certificate makes negating its coefficients preserve every retained cancellation remainder.
Both original quotient accumulators and the same fuel are retained. -/
public theorem divLoop_remainder_neg_right (fuel : ℕ) (p q quotientNeg quotient : DensePolynomial K)
    (hq : q.isZero = false) :
    (divLoop fuel p (-q) quotientNeg).remainder =
      (divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotientNeg quotient with
  | zero => rfl
  | succ fuel ih =>
      rw [divLoop_succ, divLoop_succ]
      simp only [isZero_neg, natDegree_neg]
      split
      · rfl
      · dsimp only
        rw [cancelLead_neg_right p q hq]
        exact ih (cancelLead p q)
          (quotientNeg + leadQuotient p (-q))
          (quotient + leadQuotient p q)

/-- Negating both inputs negates the finite long-division remainder at every
fuel depth.

The original normalization certificate ensures each simultaneous leading cancellation negates the same remainder.
Induction retains the original fuel and both quotient accumulators. -/
public theorem divLoop_remainder_neg_both
    (fuel : ℕ) (p q quotientNeg quotient : DensePolynomial K)
    (pNormalized : p.normalize = p) :
    (divLoop fuel (-p) (-q) quotientNeg).remainder =
      -(divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotientNeg quotient with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [divLoop_succ, divLoop_succ]
      simp only [isZero_neg, natDegree_neg]
      split
      · rfl
      · dsimp only
        rw [cancelLead_neg_both p q pNormalized]
        exact inductionHypothesis (cancelLead p q)
          (quotientNeg + leadQuotient (-p) (-q))
          (quotient + leadQuotient p q)
          (normalize_cancelLead p q)

/-- Executable division has the same remainder after negating a nonzero
divisor.

The same original finite fuel and normalized dividend run against the negated divisor. Its original nonzero test makes
each retained cancellation remainder unchanged. -/
public theorem divMod_remainder_neg_right (p q : DensePolynomial K)
    (hq : q.isZero = false) :
    (divMod p (-q)).remainder = (divMod p q).remainder := by
  have h := divLoop_remainder_neg_right (p.degreeCount + 1) p.normalize q.normalize 0 0
    (by rewrite [isZero_normalize]; exact hq)
  rw [divMod, divMod, normalize_neg]
  rw [neg_normalize q] at h
  exact h

/-- Simultaneously negating both inputs negates the executable division
remainder.

Both normalized original inputs and the same original fuel are retained. The resulting cancellation chain therefore
reverses every remainder coefficient sign. -/
public theorem divMod_remainder_neg_both_direct (p q : DensePolynomial K) :
    (divMod (-p) (-q)).remainder = -(divMod p q).remainder := by
  have result := divLoop_remainder_neg_both
    (p.degreeCount + 1) p.normalize q.normalize 0 0
      (normalize_normalize p)
  rw [divMod, divMod, degreeCount_neg, normalize_neg, normalize_neg,
    ← neg_normalize p, ← neg_normalize q]
  exact result

/-- Division preserves normalization of the remainder when its starting dividend is normalized.

A stopped run retains its normalized dividend. A continuing run reuses the original cancellation normalization
certificate for the next finite recursive state. -/
public theorem divLoop_remainder_normalized (fuel : ℕ)
    (p q quotient : DensePolynomial K) (hp : p.normalize = p) :
    (divLoop fuel p q quotient).remainder.normalize =
      (divLoop fuel p q quotient).remainder := by
  induction fuel generalizing p quotient with
  | zero => exact hp
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · exact hp
      · dsimp only
        exact ih (cancelLead p q) (quotient + leadQuotient p q)
          (normalize_cancelLead p q)

/-- A continuing division guard certifies nonzero inputs and an admissible degree difference.

Excluding the true branch of the original Boolean guard identifies both retained
zero tests with false and excludes a strictly smaller dividend degree. -/
private theorem continuing_conditions (p q : DensePolynomial K)
    (continuing : (q.isZero || p.isZero || decide (p.natDegree < q.natDegree)) ≠ true) :
    p.isZero = false ∧ q.isZero = false ∧ q.natDegree ≤ p.natDegree := by
  have qNonzero : q.isZero = false := by
    cases qZero : q.isZero with
    | false => rfl
    | true =>
        apply False.elim
        apply continuing
        rewrite [qZero]
        exact Eq.refl _
  have pNonzero : p.isZero = false := by
    cases pZero : p.isZero with
    | false => rfl
    | true =>
        apply False.elim
        apply continuing
        rewrite [qNonzero, pZero]
        exact Eq.refl _
  have degree : q.natDegree ≤ p.natDegree := by
    by_cases smaller : p.natDegree < q.natDegree
    · apply False.elim
      apply continuing
      rewrite [qNonzero, pNonzero, decide_eq_true smaller]
      exact Eq.refl _
    · exact Nat.le_of_not_gt smaller
  exact ⟨pNonzero, qNonzero, degree⟩

/-- A fuel-bounded division run cannot increase the normalized dividend coefficient count.

The normalized inputs ensure each continuing cancellation decreases the count; a stopped branch returns the current
dividend. -/
private theorem divLoop_remainder_degreeCount_le
    (fuel : ℕ) (p q quotient : DensePolynomial K)
    (pNormalized : p.normalize = p) (qNormalized : q.normalize = q) :
    (divLoop fuel p q quotient).remainder.degreeCount ≤ p.degreeCount := by
  induction fuel generalizing p quotient with
  | zero => exact Nat.le_refl _
  | succ fuel inductionHypothesis =>
      calc
        (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
            (if q.isZero || p.isZero || p.natDegree < q.natDegree then
              p.degreeCount
            else (divLoop fuel (cancelLead p q) q
              (quotient + leadQuotient p q)).remainder.degreeCount) :=
          divLoop_succ_remainder_degreeCount fuel p q quotient
        _ ≤ p.degreeCount := by
          split
          · exact Nat.le_refl _
          · rename_i continuing
            obtain ⟨pNonzero, qNonzero, degree⟩ := continuing_conditions p q continuing
            exact (inductionHypothesis (cancelLead p q)
              (quotient + leadQuotient p q)
              (normalize_cancelLead p q)).trans
                (Nat.le_of_lt (cancelLead_degreeCount_lt pNonzero
                  qNonzero pNormalized qNormalized degree))

/-- Executable division never returns a remainder with more normalized
coefficient slots than its dividend.

The loop begins with the original normalized inputs. Each continuing cancellation strictly reduces the same coefficient
count, while a stopped run retains it. -/
public theorem divMod_remainder_degreeCount_le (p q : DensePolynomial K) :
    (divMod p q).remainder.degreeCount ≤ p.degreeCount := by
  have bound := divLoop_remainder_degreeCount_le (p.degreeCount + 1)
    p.normalize q.normalize 0 (normalize_normalize p) (normalize_normalize q)
  change (divLoop (p.degreeCount + 1) p.normalize q.normalize 0).remainder.degreeCount ≤ _
  rewrite [degreeCount_normalize] at bound
  exact bound

/-- The executable division remainder is already normalized. -/
@[simp] public theorem divMod_remainder_normalize (p q : DensePolynomial K) :
    (divMod p q).remainder.normalize = (divMod p q).remainder := by
  exact divLoop_remainder_normalized (p.degreeCount + 1) p.normalize q.normalize 0
    (normalize_normalize p)

/-- The number of cancellations in a division loop is at most its supplied fuel.

Each continuing branch adds one to the completed predecessor-fuel run. Stopping branches perform zero cancellations and
retain their original polynomial state. -/
public theorem divLoop_steps_le (fuel : ℕ) (p q quotient : DensePolynomial K) :
    (divLoop fuel p q quotient).steps ≤ fuel := by
  induction fuel generalizing p quotient with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · exact Nat.zero_le _
      · dsimp only
        exact Nat.add_le_add_right
          (ih (p := cancelLead p q) (quotient := quotient + leadQuotient p q)) 1

/-- Exact evaluation invariant for every finite long-division run.

The retained quotient accumulator accounts for every original cancelled divisor contribution. Each continuing step
preserves that scalar equality at the same supplied field element. -/
public theorem divLoop_eval_equation (fuel : ℕ) (p q quotient : DensePolynomial K) (x : K) :
    let result := divLoop fuel p q quotient
    result.remainder.eval x + q.eval x * result.quotient.eval x =
      p.eval x + q.eval x * quotient.eval x := by
  induction fuel generalizing p quotient with
  | zero => rfl
  | succ fuel ih =>
      rw [divLoop_succ]
      split
      · rfl
      · dsimp only
        rw [ih, eval_cancelLead, eval_add]
        ring1

/-- Executable division performs at most the dividend coefficient count plus one cancellations.

The displayed natural fuel is the original dividend coefficient count plus one. Every performed cancellation consumes
exactly one unit of that bound. -/
public theorem divMod_steps_le (p q : DensePolynomial K) :
    (divMod p q).steps ≤ p.degreeCount + 1 :=
  divLoop_steps_le (p.degreeCount + 1) p.normalize q.normalize 0

/-- The executable quotient and remainder satisfy the exact evaluation
identity at every field element.

The original normalized inputs are evaluated at the same supplied field element. The completed quotient and remainder
retain the loop invariant with its original zero accumulator. -/
public theorem divMod_eval_equation (p q : DensePolynomial K) (x : K) :
    (divMod p q).remainder.eval x + q.eval x * (divMod p q).quotient.eval x =
      p.eval x := by
  have h := divLoop_eval_equation (p.degreeCount + 1) p.normalize q.normalize 0 x
  simpa only [divMod, eval_normalize, eval_zero, mul_zero, add_zero] using h

/-- Sufficient division fuel makes the remainder coefficient count smaller than the nonzero divisor count.

The normalized dividend count is strictly below the supplied fuel, so every continuing cancellation preserves enough
fuel for the next step. -/
private theorem divLoop_remainder_degreeCount_lt
    (fuel : ℕ) (p q quotient : DensePolynomial K)
    (hq : q.isZero = false) (hpNormalized : p.normalize = p)
    (hqNormalized : q.normalize = q) (hfuel : p.degreeCount < fuel) :
    (divLoop fuel p q quotient).remainder.degreeCount < q.degreeCount := by
  induction fuel generalizing p quotient with
  | zero => exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      calc
        (divLoop (fuel + 1) p q quotient).remainder.degreeCount =
            (if q.isZero || p.isZero || p.natDegree < q.natDegree then
              p.degreeCount
            else (divLoop fuel (cancelLead p q) q
              (quotient + leadQuotient p q)).remainder.degreeCount) :=
          divLoop_succ_remainder_degreeCount fuel p q quotient
        _ < q.degreeCount := by
          by_cases hp : p.isZero = true
          · have stopping : (q.isZero || p.isZero ||
                decide (p.natDegree < q.natDegree)) = true := by
              rewrite [hq, hp]
              exact Eq.refl _
            rewrite [if_pos stopping, degreeCount_eq_zero_of_isZero hp]
            exact degreeCount_pos_of_isZero_false hq
          · have hpFalse := Decide.bool_eq_false_of_not_eq_true p.isZero hp
            by_cases hdegree : p.natDegree < q.natDegree
            · have stopping : (q.isZero || p.isZero ||
                  decide (p.natDegree < q.natDegree)) = true := by
                rewrite [hq, hpFalse, decide_eq_true hdegree]
                exact Eq.refl _
              rewrite [if_pos stopping,
                ← natDegree_add_one_eq_degreeCount hpFalse,
                ← natDegree_add_one_eq_degreeCount hq]
              exact Nat.succ_lt_succ hdegree
            · have notStopping : (q.isZero || p.isZero ||
                  decide (p.natDegree < q.natDegree)) ≠ true := by
                rewrite [hq, hpFalse, decide_eq_false hdegree]
                exact fun impossible => Bool.noConfusion impossible
              rewrite [if_neg notStopping]
              apply ih (p := cancelLead p q)
              · exact normalize_cancelLead p q
              · have hcancel := cancelLead_degreeCount_lt hpFalse hq
                  hpNormalized hqNormalized (Nat.le_of_not_gt hdegree)
                exact Nat.lt_of_lt_of_le hcancel (Nat.le_of_lt_succ hfuel)

/-- Division by a represented nonzero polynomial returns a remainder with smaller coefficient count.

The original nonzero divisor supplies a positive coefficient count. The retained normalization and strict fuel bound
ensure a continuing cancellation cannot exhaust fuel before its remainder becomes smaller. -/
public theorem divMod_remainder_degreeCount_lt (p q : DensePolynomial K)
    (hq : q.isZero = false) :
    (divMod p q).remainder.degreeCount < q.degreeCount := by
  have h := divLoop_remainder_degreeCount_lt (p.degreeCount + 1)
      p.normalize q.normalize 0 (by rewrite [isZero_normalize]; exact hq)
      (normalize_normalize p) (normalize_normalize q) (by
        rw [degreeCount_normalize]
        exact Nat.lt_succ_self p.degreeCount)
  change (divLoop (p.degreeCount + 1) p.normalize q.normalize 0).remainder.degreeCount < _
  rewrite [degreeCount_normalize] at h
  exact h

end Purelib.Polynomial.Dense.Basic.DensePolynomial
