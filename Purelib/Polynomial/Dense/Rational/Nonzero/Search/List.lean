module
import Purelib.Data.Rat.Fraction
import Init.Core
import Init.Data.Fin.Lemmas
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Evaluation
-- The exposed indexed scan retains the original finite-table decomposition proof.
public import Purelib.Data.List.OfFn.Basic
import Purelib.Polynomial.Dense.Rational.Roots.FiniteBound

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

/-!
# First nonzero evaluation in a retained rational candidate list

The original finite scan returns its first candidate with nonzero polynomial
evaluation. Its certificates retain membership and the exact failed-scan
condition; enough distinct original candidates force a successful result.
-/

open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Search.List

set_option genInjectivity false in
/-- A finite scan certifies its exact ordered evaluations and first nonzero result or finite-list exhaustion.

A found head retains its exact nonzero polynomial value. A missed head
retains its exact zero value and the unchanged tail receipt. Exhaustion is
only the empty original remainder, not a claim about any other candidate.
-/
public inductive Receipt (p : Basic.CoordinatePolynomial) : List Fraction.Rational →
    List (Fraction.Rational × Fraction.Rational) → Option Fraction.Rational → Prop where
  /-- The original empty remainder performs no evaluations and is exhausted. -/ | exhausted : Receipt p [] [] none
  /-- The first nonzero head ends this same finite scan. -/ | found
      (point value : Fraction.Rational) (remaining : List Fraction.Rational)
      (valueEq : value = p.eval point) (nonzero : value ≠ 0) :
      Receipt p (point :: remaining) [(point, value)] (some point)
  /-- A zero head retains its exact evaluation and the original tail's complete receipt. -/ | missed
      (point value : Fraction.Rational) (remaining : List Fraction.Rational)
      (valueEq : value = p.eval point) (zero : value = 0)
      {evaluations : List (Fraction.Rational × Fraction.Rational)} {result : Option Fraction.Rational}
      (tail : Receipt p remaining evaluations result) :
      Receipt p (point :: remaining) ((point, value) :: evaluations) result

set_option genInjectivity false in
/-- One certified finite scan retains its result and every actual evaluation at its original polynomial and list. -/
public structure Scan (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) where
  /-- The first original candidate with a nonzero value, or exhaustion of the finite list. -/ result :
    Option Fraction.Rational
  /-- The exact tested candidates and their already computed polynomial values. -/ evaluations :
    List (Fraction.Rational × Fraction.Rational)
  /-- The actual result and every cached evaluation follow the original ordered finite procedure. -/ receipt :
    Receipt p points evaluations result

/-- Scan the original candidate list once, retaining each computed value before testing it for zero. -/
@[expose] public def scan (p : Basic.CoordinatePolynomial) : (points : List Fraction.Rational) → Scan p points
  | [] => ⟨none, [], .exhausted⟩
  | x :: remaining =>
      let value := p.eval x
      if zero : value = 0 then
        let tail := scan p remaining
        ⟨tail.result, (x, value) :: tail.evaluations, .missed x value remaining rfl zero tail.receipt⟩
      else ⟨some x, [(x, value)], .found x value remaining rfl zero⟩

namespace Receipt

/-- A successful certified scan supplies its original member and exact nonzero value. -/
public theorem found_spec {p : Basic.CoordinatePolynomial} {points : List Fraction.Rational}
    {evaluations : List (Fraction.Rational × Fraction.Rational)} {result : Option Fraction.Rational}
    (receipt : Receipt p points evaluations result) {point : Fraction.Rational} (found : result = some point) :
    point ∈ points ∧ p.eval point ≠ 0 := by
  induction receipt with
  | exhausted => nomatch found
  | found candidate value remaining valueEq nonzero =>
      have same := Option.some.inj found
      cases same
      exact ⟨List.Mem.head remaining, fun zero => nonzero (valueEq.trans zero)⟩
  | missed candidate _ _ _ _ _ induction =>
      have prior := induction found
      exact ⟨List.Mem.tail candidate prior.1, prior.2⟩

/-- Exhausting a certified finite list proves exactly that every original displayed candidate has zero value. -/
public theorem exhausted_spec {p : Basic.CoordinatePolynomial} {points : List Fraction.Rational}
    {evaluations : List (Fraction.Rational × Fraction.Rational)} {result : Option Fraction.Rational}
    (receipt : Receipt p points evaluations result) (exhausted : result = none) :
    ∀ point ∈ points, p.eval point = 0 := by
  induction receipt with
  | exhausted => intro _ impossible; nomatch impossible
  | found _ _ _ _ _ => nomatch exhausted
  | missed candidate _ _ valueEq zero _ induction =>
      intro point member
      cases member with
      | head => exact valueEq.symm.trans zero
      | tail _ retained => exact induction exhausted point retained

end Receipt

/-- Return the first displayed point where `p` is nonzero.

The original head is tested before its unchanged tail. A nonzero
evaluation returns that same rational candidate; zero evaluation
continues the original recursive scan and an empty list returns none.
This mathematical result projection states the original search laws;
executable checking clients consume the certified scan and its cache.
-/
@[expose] public def firstNonzero (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) : Option
    Fraction.Rational := (scan p points).result

/-- The retained scan preserves the original first-nonzero branch equation. -/
public theorem firstNonzero_cons (p : Basic.CoordinatePolynomial) (x : Fraction.Rational)
    (remaining : List Fraction.Rational) :
    firstNonzero p (x :: remaining) = if p.eval x = 0 then firstNonzero p remaining else some x := by
  by_cases zero : p.eval x = 0
  · rewrite [firstNonzero, scan, dif_pos zero, if_pos zero]
    rfl
  · rewrite [firstNonzero, scan, dif_neg zero, if_neg zero]
    rfl

/-- The exact retained evaluation count never exceeds the original finite candidate count. -/
public theorem scan_length_le (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) :
    (scan p points).evaluations.length ≤ points.length := by
  induction points with
  | nil => exact Nat.le_refl _
  | cons x remaining induction =>
      rewrite [scan]
      split
      · exact Nat.succ_le_succ induction
      · exact Nat.succ_le_succ (Nat.zero_le _)

/-- The tested candidates retain exactly an initial segment of the original ordered list. -/
public theorem scan_prefix (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) :
    ((scan p points).evaluations.map Prod.fst).IsPrefix points := by
  induction points with
  | nil => exact ⟨[], rfl⟩
  | cons x remaining induction =>
      rewrite [scan]
      split
      · rcases induction with ⟨suffix, same⟩
        exact ⟨suffix, congrArg (List.cons x) same⟩
      · exact ⟨remaining, rfl⟩

/-- Every retained pair is an original candidate and its exact value under this same polynomial. -/
public theorem scan_evaluation (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational)
    (entry : Fraction.Rational × Fraction.Rational) (member : entry ∈ (scan p points).evaluations) :
    entry.1 ∈ points ∧ entry.2 = p.eval entry.1 := by
  induction points with
  | nil => nomatch member
  | cons x remaining induction =>
      rewrite [scan] at member
      split at member
      · cases member with
        | head => exact ⟨List.Mem.head _, rfl⟩
        | tail _ retained =>
            have prior := induction retained
            exact ⟨List.Mem.tail _ prior.1, prior.2⟩
      · cases member with
        | head => exact ⟨List.Mem.head _, rfl⟩
        | tail _ impossible => nomatch impossible

/-- Scan the original candidates with one retained exact integer coefficient clearance and every original value.

Each point's homogeneous integer numerator supplies its exact rational value
once. The same value is retained and tested before the unchanged tail. Zero
heads need no rational Horner evaluation or denominator normalization.
-/
@[expose] public def scanWithPrepared {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) : (points : List Fraction.Rational) → Scan p points
  | [] => ⟨none, [], .exhausted⟩
  | point :: remaining =>
      let value := prepared.evaluate point
      if zero : value = 0 then
        let tail := scanWithPrepared prepared remaining
        ⟨tail.result, (point, value) :: tail.evaluations,
          .missed point value remaining (prepared.evaluate_eq point) zero tail.receipt⟩
      else ⟨some point, [(point, value)],
        .found point value remaining (prepared.evaluate_eq point) zero⟩

/-- Equal result and evaluation data identify the complete scan, whose receipt is proposition-valued. -/
private theorem Scan.eq_of_data {p : Basic.CoordinatePolynomial} {points : List Fraction.Rational}
    (first second : Scan p points) (result : first.result = second.result)
    (evaluations : first.evaluations = second.evaluations) : first = second := by
  cases first
  cases second
  cases result
  cases evaluations
  rfl

/-- The prepared producer returns the complete original scan, including every exact value and stopping condition. -/
public theorem scanWithPrepared_eq {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) (points : List Fraction.Rational) :
    scanWithPrepared prepared points = scan p points := by
  induction points with
  | nil => rfl
  | cons point remaining inductionHypothesis =>
      rw [scanWithPrepared, scan]
      have valueEq : prepared.evaluate point = p.eval point := prepared.evaluate_eq point
      by_cases zero : p.eval point = 0
      · have preparedZero := valueEq.trans zero
        rw [dif_pos preparedZero, dif_pos zero]
        apply Scan.eq_of_data
        · exact congrArg (fun tail : Scan p remaining => tail.result) inductionHypothesis
        · exact congrArg₂ List.cons (congrArg (Prod.mk point) valueEq)
            (congrArg (fun tail : Scan p remaining => tail.evaluations) inductionHypothesis)
      · have preparedNonzero : prepared.evaluate point ≠ 0 := fun vanished => zero (valueEq.symm.trans vanished)
        rw [dif_neg preparedNonzero, dif_neg zero]
        apply Scan.eq_of_data
        · rfl
        · exact congrArg (fun value => [(point, value)]) valueEq

attribute [local irreducible] Evaluation.Prepared.ReducesTo in
/-- Consume a finite indexed scan through its final retained record.

One retained residue table supplies the same exact ordered zero decisions,
with integer fallback. A final consumer receives the complete original result
and evaluation cache; specialization can discard unused numerator thunks.
Full-record consumers force each original numerator once, reusing any fallback.
-/
-- The final consumer changes during recursion, so specialize it explicitly.
@[expose, specialize 10] public def scanOfFnUsing {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) (modulus : Nat) [NeZero modulus]
    (residues : List (Fin modulus))
    (correct : prepared.ReducesTo modulus residues) {Result : Type} :
    {size : Nat} → (points : Fin size → Fraction.Rational) →
      (Scan p (List.ofFn points) → Result) → Result
  | 0, _, finish => finish ⟨none, [], .exhausted⟩
  | size + 1, points, finish =>
      let point := points ⟨0, Nat.zero_lt_succ size⟩
      let tested := prepared.zeroTestUsing modulus residues correct point
      match tested.2 with
      | .isTrue zero =>
          scanOfFnUsing prepared modulus residues correct
            (fun index : Fin size => points index.succ) (fun tail =>
              finish ⟨tail.result, (point, 0) :: tail.evaluations, by
                rewrite [OfFn.Basic.ofFn_succ]
                exact .missed point 0 _ ((prepared.numerator_zero_iff point).mp zero).symm
                  rfl tail.receipt⟩)
      | .isFalse nonzero =>
          let value := prepared.evaluateNumerator point tested.1.val.get tested.1.property
          finish ⟨some point, [(point, value)], by
            rewrite [OfFn.Basic.ofFn_succ]
            have valueEq := prepared.evaluateNumerator_eq point tested.1.val.get tested.1.property
            exact .found point value _ valueEq (fun vanished =>
              nonzero ((prepared.numerator_zero_iff point).mpr (valueEq.symm.trans vanished)))⟩

/-- Every consumer of the indexed scan receives the complete original ordered scan. -/
public theorem scanOfFnUsing_eq {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) (modulus : Nat) [NeZero modulus]
    (residues : List (Fin modulus))
    (correct : prepared.ReducesTo modulus residues) {Result : Type} {size : Nat}
    (points : Fin size → Fraction.Rational) (finish : Scan p (List.ofFn points) → Result) :
    scanOfFnUsing prepared modulus residues correct points finish =
      finish (scanWithPrepared prepared (List.ofFn points)) := by
  induction size with
  | zero => rfl
  | succ size inductionHypothesis =>
      have table : List.ofFn points = points ⟨0, Nat.zero_lt_succ size⟩ ::
          List.ofFn (fun index : Fin size => points index.succ) :=
        OfFn.Basic.ofFn_succ (function := points)
      rewrite [scanOfFnUsing]
      cases decision : (prepared.zeroTestUsing modulus residues correct
          (points ⟨0, Nat.zero_lt_succ size⟩)).2 with
      | isTrue zero =>
          dsimp only
          rewrite [inductionHypothesis]
          have valueZero := (prepared.evaluate_eq (points ⟨0, Nat.zero_lt_succ size⟩)).trans
            ((prepared.numerator_zero_iff (points ⟨0, Nat.zero_lt_succ size⟩)).mp zero)
          apply congrArg finish
          apply Scan.eq_of_data
          · dsimp only
            rewrite [table, scanWithPrepared, dif_pos valueZero]
            rfl
          · dsimp only
            rewrite [table, scanWithPrepared, dif_pos valueZero]
            exact congrArg (fun value => (points ⟨0, Nat.zero_lt_succ size⟩, value) ::
              (scanWithPrepared prepared
                (List.ofFn (fun index : Fin size => points index.succ))).evaluations) valueZero.symm
      | isFalse nonzero =>
          have valueNonzero : prepared.evaluate (points ⟨0, Nat.zero_lt_succ size⟩) ≠ 0 := by
            intro vanished
            exact nonzero ((prepared.numerator_zero_iff _).mpr
              ((prepared.evaluate_eq _).symm.trans vanished))
          apply congrArg finish
          apply Scan.eq_of_data
          · dsimp only
            rewrite [table, scanWithPrepared, dif_neg valueNonzero]
            rfl
          · dsimp only
            rewrite [table, scanWithPrepared, dif_neg valueNonzero]
            exact congrArg (fun value => [(points ⟨0, Nat.zero_lt_succ size⟩, value)])
              ((prepared.evaluateNumerator_eq _ _ _).trans (prepared.evaluate_eq _).symm)

/-- Retain the complete indexed scan, including each exact tested rational value.

The indexed producer shares its exact zero decisions with projected consumers.
One residue table serves the whole scan. The complete record forces each
original numerator once, without visiting an untested tail.
-/
@[expose] public def scanOfFn {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) : {size : Nat} →
    (points : Fin size → Fraction.Rational) → Scan p (List.ofFn points)
  | 0, _ => ⟨none, [], .exhausted⟩
  | _ + 1, points =>
      prepared.withResidues fun modulus [_modulusInstance : NeZero modulus] residues correct =>
        scanOfFnUsing prepared modulus residues correct points (fun scan => scan)

/-- Indexed scanning preserves the complete original prepared scan at every finite size. -/
public theorem scanOfFn_eq {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) {size : Nat}
    (points : Fin size → Fraction.Rational) :
    scanOfFn prepared points = scanWithPrepared prepared (List.ofFn points) := by
  cases size with
  | zero => rfl
  | succ size =>
      unfold scanOfFn
      apply prepared.withResidues_result
      intro modulus modulusInstance residues correct
      exact scanOfFnUsing_eq prepared modulus residues correct points (fun scan => scan)

/-- Select the first indexed nonroot with the shared modular tests and exact integer fallback. -/
@[expose] public def firstNonzeroOfFn {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) : {size : Nat} →
    (Fin size → Fraction.Rational) → Option Fraction.Rational
  | 0, _ => none
  | _ + 1, points =>
      prepared.withResidues fun modulus [_modulusInstance : NeZero modulus] residues correct =>
        scanOfFnUsing prepared modulus residues correct points Scan.result

/-- The projected indexed search retains exactly the complete scan's first result or exhaustion. -/
public theorem firstNonzeroOfFn_eq {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) {size : Nat}
    (points : Fin size → Fraction.Rational) :
    firstNonzeroOfFn prepared points = (scanOfFn prepared points).result := by
  cases size with
  | zero => rfl
  | succ size =>
      have projected : firstNonzeroOfFn prepared points =
          (scanWithPrepared prepared (List.ofFn points)).result := by
        unfold firstNonzeroOfFn
        apply prepared.withResidues_result
        intro modulus modulusInstance residues correct
        exact scanOfFnUsing_eq prepared modulus residues correct points Scan.result
      exact projected.trans (congrArg Scan.result (scanOfFn_eq prepared points)).symm

/-- Clear the original coefficients once and retain every original evaluation in the same finite scan. -/
@[expose] public def scanPrepared (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) : Scan p points :=
  scanWithPrepared (Evaluation.prepare p.coeffs) points

/-- The once-prepared finite producer preserves the complete original scan record. -/
public theorem scanPrepared_eq (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) :
    scanPrepared p points = scan p points := scanWithPrepared_eq (Evaluation.prepare p.coeffs) points

/-- Project the first nonzero result from the same prepared scan and its retained original evaluations. -/
@[expose] public def firstNonzeroWithPrepared {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) (points : List Fraction.Rational) : Option Fraction.Rational :=
  (scanWithPrepared prepared points).result

/-- The integer-discriminated scan returns the complete original Option result for every ordered candidate list. -/
public theorem firstNonzeroWithPrepared_eq {p : Basic.CoordinatePolynomial}
    (prepared : Evaluation.Prepared p.coeffs) (points : List Fraction.Rational) :
    firstNonzeroWithPrepared prepared points = firstNonzero p points :=
  congrArg Scan.result (scanWithPrepared_eq prepared points)

/-- Clear the original polynomial coefficients once before scanning the original ordered points. -/
@[expose] public def firstNonzeroPrepared (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) :
    Option Fraction.Rational :=
  firstNonzeroWithPrepared (Evaluation.prepare p.coeffs) points

/-- The prepared scan preserves every original failure and first-success result. -/
public theorem firstNonzeroPrepared_eq (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational) :
    firstNonzeroPrepared p points = firstNonzero p points :=
  firstNonzeroWithPrepared_eq (Evaluation.prepare p.coeffs) points

/-- A returned candidate belongs to the input list and has nonzero polynomial value.

The original Option result retains either the current nonzero head
or the result of the unchanged tail scan. Those same constructor
branches supply the displayed membership and nonzero evaluation. -/
public theorem firstNonzero_some_spec {p : Basic.CoordinatePolynomial} {points : List Fraction.Rational}
    {x : Fraction.Rational} (found : firstNonzero p points = some x) :
    x ∈ points ∧ p.eval x ≠ 0 := by
  induction points with
  | nil =>
      change none = some x at found
      nomatch found
  | cons candidate remaining inductionHypothesis =>
      by_cases candidateZero : p.eval candidate = 0
      · rw [firstNonzero_cons, if_pos candidateZero] at found
        rcases inductionHypothesis found with ⟨member, nonzero⟩
        exact ⟨List.mem_cons_of_mem candidate member, nonzero⟩
      · rw [firstNonzero_cons, if_neg candidateZero] at found
        have equal : candidate = x := Option.some.inj found
        cases equal
        exact ⟨List.Mem.head remaining, candidateZero⟩

/-- The finite nonzero search fails exactly when every displayed candidate is a root.

Every original candidate is tested in list order. Failure of that
same scan supplies a zero evaluation at each actual occurrence,
and those retained zero evaluations force the original none result. -/
public theorem firstNonzero_eq_none_iff (p : Basic.CoordinatePolynomial)
    (points : List Fraction.Rational) :
    firstNonzero p points = none ↔
      ∀ x ∈ points, p.eval x = 0 := by
  induction points with
  | nil =>
      constructor
      · intro _ x impossible
        nomatch impossible
      · intro _
        rfl
  | cons candidate remaining inductionHypothesis =>
      constructor
      · intro search x member
        by_cases candidateZero : p.eval candidate = 0
        · rw [firstNonzero_cons, if_pos candidateZero] at search
          cases member with
          | head => exact candidateZero
          | tail _ tailMember => exact inductionHypothesis.mp search x tailMember
        · rw [firstNonzero_cons, if_neg candidateZero] at search
          nomatch search
      · intro allZero
        have candidateZero : p.eval candidate = 0 :=
          allZero candidate List.mem_cons_self
        rw [firstNonzero_cons, if_pos candidateZero]
        apply inductionHypothesis.mpr
        intro x member
        exact allZero x (List.mem_cons_of_mem candidate member)

/-- Enough distinct displayed candidates guarantee a successful nonzero search.

The polynomial must be nonzero, the candidate list must have no duplicates, and its length must reach the polynomial
coefficient count. -/
public theorem firstNonzero_exists (p : Basic.CoordinatePolynomial) (points : List Fraction.Rational)
    (nonzero : p.isZero = false) (nodup : points.Nodup)
    (degreeBound : p.degreeCount ≤ points.length) :
    ∃ x, firstNonzero p points = some x := by
  cases search : firstNonzero p points with
  | none =>
      have allZero := (firstNonzero_eq_none_iff p points).mp search
      have impossible := Roots.FiniteBound.nodup_zeros_length_lt_degreeCount p nonzero points
        nodup allZero
      exact (Nat.not_lt_of_ge degreeBound impossible).elim
  | some x => exact ⟨x, rfl⟩

end Purelib.Polynomial.Dense.Rational.Nonzero.Search.List
