module
-- The exposed scalar negation body retains this direct field parent.
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Append
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.DropWhile.Bounds
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.List.Zip
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

open Purelib.Data.List

open Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Executable dense polynomials and finite Euclidean division

Mathlib's sparse `Polynomial` arithmetic is intended for specifications at the
representation level.  The FTA algorithms therefore use this separate dense
coefficient program.  Coefficients are stored highest-degree first; leading
zeros are removed by a finite `dropWhile` pass.
-/

namespace Purelib.Polynomial.Dense.Basic
namespace DensePolynomial

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Left zero padding aligns two high-to-low coefficient lists. -/
def padLeft (n : ℕ) (cs : List K) : List K := List.replicate n 0
  ++ cs

omit [DecidableEq K] in
/-- Prepending any finite block of zeros preserves the descending Horner value. -/
theorem evalCoeffs_replicate_zero_append (x : K) (n : ℕ) (cs :
  List K) :
    Dense.Basic.DensePolynomial.evalCoeffs x (List.replicate n 0 ++ cs) = Dense.Basic.DensePolynomial.evalCoeffs x cs :=
      by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, Dense.Basic.DensePolynomial.evalCoeffs_cons_zero, ih]

omit [DecidableEq K] in
/-- For equal-length coefficient lists, their paired sum preserves addition of Horner accumulators.

The final fold is the sum of the two individual folds with their respective initial accumulators. -/
private theorem foldl_zipWith_add (x : K) :
    ∀ (as bs : List K) (accA accB : K), as.length = bs.length →
      (List.zipWith (· + ·) as bs).foldl (fun acc a => acc * x + a) (accA + accB) =
        as.foldl (fun acc a => acc * x + a) accA +
          bs.foldl (fun acc b => acc * x + b) accB
  | [], [], accA, accB, _ => rfl
  | [], _ :: _, _, _, h => by exact Nat.noConfusion h
  | _ :: _, [], _, _, h => by exact Nat.noConfusion h
  | a :: as, b :: bs, accA, accB, h => by
      have tailLengths : as.length = bs.length := Nat.succ.inj h
      simp only [List.zipWith_cons_cons, List.foldl_cons]
      have hacc : (accA + accB) * x + (a + b) =
          (accA * x + a) + (accB * x + b) := by ring1
      rw [hacc]
      exact foldl_zipWith_add x as bs (accA * x + a) (accB * x + b)
        tailLengths

omit [DecidableEq K] in
/-- For equal-length coefficient lists, Horner evaluation of their paired sum is the sum of their values. -/
theorem evalCoeffs_zipWith_add (x : K) (as bs : List K) (h :
  as.length = bs.length) :
    Dense.Basic.DensePolynomial.evalCoeffs x (List.zipWith (· + ·) as bs) =
      Dense.Basic.DensePolynomial.evalCoeffs x as + Dense.Basic.DensePolynomial.evalCoeffs x bs := by
  simpa only [Dense.Basic.DensePolynomial.evalCoeffs, zero_add] using foldl_zipWith_add x as
    bs 0 0 h

/-- Coefficientwise addition after finite left-padding. -/
def add (p q : Dense.Basic.DensePolynomial K) :
  Dense.Basic.DensePolynomial K :=
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  Dense.Basic.DensePolynomial.normalize ⟨List.zipWith (· + ·) ps qs⟩

/-- The addition instance uses aligned coefficient addition followed by normalization. -/
instance instAddDensePolynomial : Add (Dense.Basic.DensePolynomial K) := ⟨add⟩

/-- Dense addition already returns a normalized representation. -/
@[simp] theorem normalize_add (p q : Dense.Basic.DensePolynomial
  K) :
    (p + q).normalize = p + q := by
  exact Dense.Basic.DensePolynomial.normalize_normalize _

omit [DecidableEq K] in
/-- Paired coefficient-list addition is unchanged when the two input lists are exchanged. -/
private theorem zipWith_add_comm : ∀ first second : List K,
    List.zipWith (· + ·) first second =
      List.zipWith (· + ·) second first
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | left :: leftTail, right :: rightTail => by
      simp only [List.zipWith_cons_cons]
      rw [_root_.add_comm left right,
        zipWith_add_comm leftTail rightTail]

/-- Coefficientwise addition is commutative by a direct finite-list proof.

Swapping the inputs preserves their actual maximum coefficient length and
therefore their retained left padding. The paired scalar sums commute at
each entry, and normalization consumes the same resulting coefficient list. -/
theorem add_comm_direct (p q : Dense.Basic.DensePolynomial K) : p
  + q = q + p := by
  apply Dense.Basic.DensePolynomial.ext
  change (add p q).coeffs = (add q p).coeffs
  simp only [add]
  have retainedMaximum (left right : Nat) : max left right = Nat.max left right := by
    by_cases ordered : left ≤ right
    · have actualChoice : max left right = right :=
        (_root_.max_def left right).trans (if_pos ordered)
      have naturalChoice : Nat.max left right = right :=
        Nat.max_def.trans (if_pos ordered)
      exact actualChoice.trans naturalChoice.symm
    · have actualChoice : max left right = left :=
        (_root_.max_def left right).trans (if_neg ordered)
      have naturalChoice : Nat.max left right = left :=
        Nat.max_def.trans (if_neg ordered)
      exact actualChoice.trans naturalChoice.symm
  have maximum : max p.coeffs.length q.coeffs.length = max q.coeffs.length p.coeffs.length :=
    (retainedMaximum _ _).trans ((Order.max_comm _ _).trans (retainedMaximum _ _).symm)
  rw [maximum]
  change (List.zipWith (· + ·)
      (padLeft (max q.coeffs.length p.coeffs.length - p.coeffs.length) p.coeffs)
      (padLeft (max q.coeffs.length p.coeffs.length - q.coeffs.length) q.coeffs)).dropWhile
        (· = 0) =
    (List.zipWith (· + ·)
      (padLeft (max q.coeffs.length p.coeffs.length - q.coeffs.length) q.coeffs)
      (padLeft (max q.coeffs.length p.coeffs.length - p.coeffs.length) p.coeffs)).dropWhile
        (· = 0)
  exact congrArg
    (fun coefficients : List K =>
      coefficients.dropWhile (fun coefficient => decide (coefficient = 0)))
    (zipWith_add_comm _ _)

/-- Adding the represented zero constant changes only normalization.

The original padding aligns each displayed coefficient with scalar zero.
Paired addition retains those same coefficients, and normalization therefore
returns the original normalized display. -/
@[simp] theorem add_constant_zero (p : Dense.Basic.DensePolynomial
  K) :
    p + Dense.Basic.DensePolynomial.constant 0 = p.normalize := by
  cases p with
  | mk coefficients =>
      apply Dense.Basic.DensePolynomial.ext
      cases coefficients with
      | nil =>
          have maximum : max (0 : Nat) 1 = 1 :=
            (max_def 0 1).trans (if_pos (Nat.zero_le 1))
          change (List.zipWith (fun left right : K => left + right)
            (padLeft (max 0 1 - 0) [])
            (padLeft (max 0 1 - 1) [0])).dropWhile (· = 0) = []
          rw [maximum]
          change [(0 : K) + 0].dropWhile (· = 0) = []
          rw [add_zero]
          exact DropWhile.cons_of_true (fun value : K => decide (value = 0))
            0 [] (decide_eq_true rfl)
      | cons a as =>
          have oneBound : 1 ≤ as.length + 1 := Nat.succ_le_succ (Nat.zero_le as.length)
          have maximum : max (as.length + 1) 1 = as.length + 1 := by
            by_cases ordered : as.length + 1 ≤ 1
            · exact (max_def _ _).trans
                ((if_pos ordered).trans (Nat.le_antisymm oneBound ordered))
            · exact (max_def _ _).trans (if_neg ordered)
          change (List.zipWith (· + ·)
            (padLeft
              (max (as.length + 1) 1 - (as.length + 1)) (a :: as))
            (padLeft
              (max (as.length + 1) 1 - 1) [0])).dropWhile (· = 0) =
            (a :: as).dropWhile (· = 0)
          rw [maximum, Nat.sub_self, Subtraction.add_sub_cancel_right]
          change (List.zipWith (· + ·) (a :: as)
            (List.replicate as.length 0 ++ [0])).dropWhile (· = 0) =
            (a :: as).dropWhile (· = 0)
          have zipZeros : ∀ (head : K) (tail : List K),
              List.zipWith (· + ·) (head :: tail)
                (List.replicate tail.length 0 ++ [0]) = head :: tail := by
            intro head tail
            induction tail generalizing head with
            | nil =>
                change [head + 0] = [head]
                exact congrArg (fun value : K => [value]) (add_zero head)
            | cons value values ih =>
                rw [List.length_cons, List.replicate_succ, List.cons_append,
                  List.zipWith_cons_cons, add_zero, ih]
          rw [zipZeros a as]

/-- Adding a constant to a linear table with zero constant term fills that term.

The retained nonzero leading coefficient keeps both output entries after
normalization. Original left zero padding aligns the supplied constant with
the linear table's trailing zero. -/
theorem constant_add_linear {leading : K} (trailing : K)
    (leadingNonzero : leading ≠ 0) :
    Dense.Basic.DensePolynomial.constant trailing + ⟨[leading, 0]⟩ = ⟨[leading, trailing]⟩ := by
  apply Dense.Basic.DensePolynomial.ext
  have maximum : max (1 : Nat) 2 = 2 := (max_def 1 2).trans (if_pos (by decide))
  change (List.zipWith (· + ·)
    (padLeft (max 1 2 - 1) [trailing])
    (padLeft (max 1 2 - 2) [leading, 0])).dropWhile (· = 0) =
      [leading, trailing]
  rw [maximum]
  change [(0 : K) + leading, trailing + 0].dropWhile (· = 0) = [leading, trailing]
  rw [zero_add, add_zero]
  exact DropWhile.cons_of_false (fun value : K => decide (value = 0))
    leading [trailing] (decide_eq_false leadingNonzero)

/-- Adding a constant to an exact nonconstant linear list changes only its trailing coefficient.

The retained nonzero leading coefficient survives normalization unchanged.
The original right zero padding aligns the constant with the trailing entry,
whose scalar sum gives the displayed new constant coefficient. -/
theorem linear_add_constant {leading : K} (trailing constantTerm :
  K)
    (leadingNonzero : leading ≠ 0) :
    ⟨[leading, trailing]⟩ + Dense.Basic.DensePolynomial.constant constantTerm =
      ⟨[leading, trailing + constantTerm]⟩ := by
  apply Dense.Basic.DensePolynomial.ext
  have maximum : max (2 : Nat) 1 = 2 := (max_def 2 1).trans (if_neg (by decide))
  change (List.zipWith (· + ·)
    (padLeft (max 2 1 - 2) [leading, trailing])
    (padLeft (max 2 1 - 1) [constantTerm])).dropWhile (· = 0) =
      [leading, trailing + constantTerm]
  rw [maximum]
  change [leading + (0 : K), trailing + constantTerm].dropWhile (· = 0) =
    [leading, trailing + constantTerm]
  rw [add_zero]
  exact DropWhile.cons_of_false (fun value : K => decide (value = 0))
    leading [trailing + constantTerm] (decide_eq_false leadingNonzero)

/-- Evaluation preserves normalized dense polynomial addition.

Both original coefficient lists are padded to their actual maximum length.
The retained equal-length certificate permits paired Horner addition, while
the original zero-padding and normalization preserve each evaluation. -/
@[simp] theorem eval_add (p q : Dense.Basic.DensePolynomial K) (x
  : K) :
    (p + q).eval x = p.eval x + q.eval x := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := by
    change p.coeffs.length ≤ max p.coeffs.length q.coeffs.length
    by_cases ordered : p.coeffs.length ≤ q.coeffs.length
    · rw [max_def, if_pos ordered]
      exact ordered
    · rw [max_def, if_neg ordered]
  have hq : q.coeffs.length ≤ n := by
    change q.coeffs.length ≤ max p.coeffs.length q.coeffs.length
    by_cases ordered : p.coeffs.length ≤ q.coeffs.length
    · rw [max_def, if_pos ordered]
    · rw [max_def, if_neg ordered]
      exact Nat.le_of_not_ge ordered
  have hps : ps.length = n := by
    dsimp only [ps, padLeft]
    rw [Append.length_append, Replicate.length_replicate]
    exact (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le hp)
  have hqs : qs.length = n := by
    dsimp only [qs, padLeft]
    rw [Append.length_append, Replicate.length_replicate]
    exact (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le hq)
  change (Dense.Basic.DensePolynomial.normalize ⟨List.zipWith (· + ·) ps qs⟩).eval x = _
  rw [Dense.Basic.DensePolynomial.eval_normalize]
  change Dense.Basic.DensePolynomial.evalCoeffs x (List.zipWith (· + ·) ps qs) = _
  rw [evalCoeffs_zipWith_add x ps qs (hps.trans hqs.symm)]
  dsimp only [Dense.Basic.DensePolynomial.eval, ps, qs, padLeft]
  rw [evalCoeffs_replicate_zero_append,
    evalCoeffs_replicate_zero_append]

/-- Negate each retained coefficient and normalize the resulting dense display.

The finite coefficient map uses the original scalar negation operation.
Normalization removes only the leading zero coefficients of that mapped list. -/
def neg (p : Dense.Basic.DensePolynomial K) :
  Dense.Basic.DensePolynomial K :=
  Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (-·)⟩

/-- The negation instance negates coefficients and normalizes their list. -/
instance instNegDensePolynomial : Neg (Dense.Basic.DensePolynomial K) := ⟨neg⟩

/-- Negation commutes with dropping leading zero coefficients.

A zero head and its negation select the same recursive scan branch. A
nonzero head remains nonzero under the retained involutive negation, so
both scans retain the same original tail and coefficient map. -/
private theorem dropWhile_map_neg (cs : List K) :
    (cs.map (-·)).dropWhile (· = 0) =
      (cs.dropWhile (· = 0)).map (-·) := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons]
      by_cases ha : a = 0
      · have mappedZero : -a = 0 := by
          calc
            -a = -(0 : K) := congrArg (fun value : K => -value) ha
            _ = 0 := neg_zero
        rw [DropWhile.cons_of_true (fun value : K => decide (value = 0))
            (-a) (as.map (-·)) (decide_eq_true mappedZero),
          DropWhile.cons_of_true (fun value : K => decide (value = 0))
            a as (decide_eq_true ha)]
        exact ih
      · have mappedNonzero : -a ≠ 0 := by
          intro mappedZero
          apply ha
          calc
            a = - -a := (InvolutiveNeg.neg_neg a).symm
            _ = -(0 : K) := congrArg (fun value : K => -value) mappedZero
            _ = 0 := neg_zero
        rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
            (-a) (as.map (-·)) (decide_eq_false mappedNonzero),
          DropWhile.cons_of_false (fun value : K => decide (value = 0))
            a as (decide_eq_false ha)]; rfl

/-- The negated polynomial retains the negations of the normalized original coefficients. -/
@[simp] theorem neg_coeffs (p : Dense.Basic.DensePolynomial K) :
    (-p).coeffs = p.normalize.coeffs.map (-·) := by
  exact dropWhile_map_neg p.coeffs

/-- Dense negation already returns a normalized representation. -/
@[simp] theorem normalize_neg (p : Dense.Basic.DensePolynomial K)
  :
    (-p).normalize = -p := by
  exact Dense.Basic.DensePolynomial.normalize_normalize ⟨p.coeffs.map (-·)⟩

/-- Normalizing before negation does not change the result.

Both negations retain the scalar negatives of the same normalized coefficient
list. Idempotence of the original normalization identifies those exact lists. -/
@[simp] theorem neg_normalize (p : Dense.Basic.DensePolynomial K)
  :
    -p.normalize = -p := by
  apply Dense.Basic.DensePolynomial.ext
  rw [neg_coeffs p.normalize,
    neg_coeffs p,
    Dense.Basic.DensePolynomial.normalize_normalize]

omit [DecidableEq K] in
/-- Negating an entire coefficient list twice recovers that exact list. -/
private theorem map_neg_neg : ∀ coefficients : List K,
    (coefficients.map (-·)).map (-·) = coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      rw [List.map_cons, List.map_cons, _root_.neg_neg,
        map_neg_neg coefficients]

/-- Negating a dense polynomial twice recovers its normalized representation. -/
@[simp] theorem neg_neg (p : Dense.Basic.DensePolynomial K) : - -p
  = p.normalize := by
  apply Dense.Basic.DensePolynomial.ext
  rw [neg_coeffs, normalize_neg,
    neg_coeffs]
  exact map_neg_neg p.normalize.coeffs

/-- Negation preserves the dense zero test.

The negated normalized display maps one scalar negative to each retained
coefficient. Its list is empty exactly when the original normalized list is
empty, as witnessed directly by the two list constructors. -/
@[simp] theorem isZero_neg (p : Dense.Basic.DensePolynomial K) :
  (-p).isZero = p.isZero := by
  change (-p).normalize.coeffs.isEmpty = p.normalize.coeffs.isEmpty
  rw [normalize_neg, neg_coeffs]
  cases p.normalize.coeffs with
  | nil => rfl
  | cons head tail => rfl

/-- Negation preserves the normalized degree count.

The negated polynomial retains exactly one scalar negative for each normalized
input coefficient. Mapping that retained finite list preserves its length. -/
@[simp] theorem degreeCount_neg (p : Dense.Basic.DensePolynomial
  K) :
    (-p).degreeCount = p.degreeCount := by
  change (-p).normalize.coeffs.length = p.normalize.coeffs.length
  rw [normalize_neg, neg_coeffs]
  exact Map.length_map (fun value : K => -value) p.normalize.coeffs

/-- Negation preserves the natural degree.

The normalized coefficient count is unchanged by scalar negation. Applying
the original truncated subtraction of one preserves its natural degree,
including the zero-polynomial value. -/
@[simp] theorem natDegree_neg (p : Dense.Basic.DensePolynomial K)
  :
    (-p).natDegree = p.natDegree := by
  exact congrArg (fun count : Nat => count - 1) (degreeCount_neg p)

/-- The leading coefficient of the negated polynomial is the negative original leading coefficient.

A nonempty normalized list retains the negated original head. The empty list
uses scalar zero as its head default, and negation fixes that same zero. -/
@[simp] theorem leadingCoeff_neg (p : Dense.Basic.DensePolynomial
  K) :
    (-p).leadingCoeff = -p.leadingCoeff := by
  rw [Dense.Basic.DensePolynomial.leadingCoeff, normalize_neg,
    neg_coeffs]
  change (p.normalize.coeffs.map (-·)).headD 0 = -p.normalize.coeffs.headD 0
  cases p.normalize.coeffs with
  | nil => exact (neg_zero : -(0 : K) = 0).symm
  | cons head tail => rfl

omit [DecidableEq K] in
/-- Negating both coefficients and initial accumulator negates the final Horner state. -/
private theorem foldl_map_neg (x : K) : ∀ (cs : List K) (acc : K),
    (cs.map (-·)).foldl (fun value a => value * x + a) (-acc) =
      -cs.foldl (fun value a => value * x + a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      have hacc : -acc * x + -a = -(acc * x + a) := by ring1
      rw [hacc]
      exact foldl_map_neg x as (acc * x + a)

/-- Evaluation of dense negation is the negative original value. -/
@[simp] theorem eval_neg (p : Dense.Basic.DensePolynomial K) (x :
  K) :
    (-p).eval x = -p.eval x := by
  rw [show -p = Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (-·)⟩ from rfl,
    Dense.Basic.DensePolynomial.eval_normalize]
  dsimp only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs]
  simpa only [neg_zero] using foldl_map_neg x p.coeffs 0

/-- Subtract dense polynomials by adding the normalized negative of the right polynomial. -/
def sub (p q : Dense.Basic.DensePolynomial K) :
  Dense.Basic.DensePolynomial K := p + -q

/-- The subtraction instance adds the negated right polynomial. -/
instance instSubDensePolynomial : Sub (Dense.Basic.DensePolynomial K) := ⟨sub⟩

omit [DecidableEq K] in
/-- Negation commutes with left zero padding of a coefficient list.

Each retained padding entry is zero and remains zero under scalar negation.
Structural recursion preserves the exact padded tail and the original map
on the supplied coefficients. -/
private theorem padLeft_map_neg (n : Nat) (coefficients : List K)
  :
    padLeft n (coefficients.map (-·)) =
      (padLeft n coefficients).map (-·) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 : K) :: padLeft n (coefficients.map (-·)) =
        ((0 : K) :: padLeft n coefficients).map (-·)
      rw [List.map_cons]
      exact congrArg₂ List.cons (neg_zero : -(0 : K) = 0).symm ih

omit [DecidableEq K] in
/-- Negating the left input of paired addition is the negative of adding the left input to the negative right input. -/
private theorem zipWith_neg_add : ∀ first second : List K,
    List.zipWith (· + ·) (first.map (-·)) second =
      (List.zipWith (· + ·) first (second.map (-·))).map (-·)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | first :: restFirst, second :: restSecond => by
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [zipWith_neg_add restFirst restSecond]
      exact congrArg₂ List.cons (by ring1) rfl

/-- Dropping an initial zero coefficient block twice has the same result as dropping it once. -/
private theorem dropWhile_zero_idempotent (coefficients : List K)
  :
    (coefficients.dropWhile (· = 0)).dropWhile (· = 0) =
      coefficients.dropWhile (· = 0) := by
  have normalized := congrArg Dense.Basic.DensePolynomial.coeffs
    (Dense.Basic.DensePolynomial.normalize_normalize (K := K) ⟨coefficients⟩)
  exact normalized

/-- Dense subtraction already returns a normalized representation. -/
@[simp] theorem normalize_sub (p q : Dense.Basic.DensePolynomial
  K) :
    (p - q).normalize = p - q := by
  exact normalize_add p (-q)

/-- Evaluation preserves dense polynomial subtraction. -/
@[simp] theorem eval_sub (p q : Dense.Basic.DensePolynomial K) (x
  : K) :
    (p - q).eval x = p.eval x - q.eval x := by
  change (p + -q).eval x = _
  rw [eval_add, eval_neg, sub_eq_add_neg]

omit [DecidableEq K] in
/-- Adding a constant back to the final slot cancels its prior subtraction in the same aligned list.

Both updates use a zero prefix of the retained tail length, preserving every earlier coefficient. -/
private theorem zipWith_trailing_cancel (second c : K) :
    ∀ rest : List K,
      List.zipWith (· + ·) (List.replicate rest.length 0 ++ [c])
          (List.zipWith (· + ·) (second :: rest)
            (List.replicate rest.length 0 ++ [-c])) =
        second :: rest := by
  intro rest
  induction rest generalizing second with
  | nil =>
      simp only [List.length_nil, List.replicate_zero, List.nil_append,
        List.zipWith]
      apply congrArg (fun value : K => [value])
      ring1
  | cons next rest inductionHypothesis =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, zero_add]
      rw [inductionHypothesis next, add_zero]

/-- Adding back a nonzero constant after subtracting it restores the exact normalized coefficient list.

The retained positive degree supplies a nonempty trailing list, and the
original nonzero leading coefficient survives both normalizations. The two
aligned updates cancel in the final slot while preserving every earlier entry. -/
theorem constant_add_sub_constant_of_normalized
    {p : Dense.Basic.DensePolynomial K} {c : K}
    (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false)
    (degreePositive : 0 < p.natDegree)
    (cNonzero : c ≠ 0) :
    Dense.Basic.DensePolynomial.constant c + (p - Dense.Basic.DensePolynomial.constant c) = p := by
  obtain ⟨tail, coefficients, tailLength⟩ := Dense.Basic.DensePolynomial.normalized_coeffs_shape pNonzero
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero pNonzero
  rw [pNormalized] at coefficients
  cases tail with
  | nil =>
      simp only [List.length_nil] at tailLength
      rw [← tailLength] at degreePositive
      exact (Nat.not_lt_zero 0 degreePositive).elim
  | cons trailing rest =>
      have pShape : p = ⟨p.leadingCoeff :: trailing :: rest⟩ :=
        Dense.Basic.DensePolynomial.ext coefficients
      rw [pShape] at ⊢
      have negativeNonzero : -c ≠ 0 := by
        intro vanished
        apply cNonzero
        calc
          c = - -c := (InvolutiveNeg.neg_neg c).symm
          _ = -(0 : K) := congrArg (fun value : K => -value) vanished
          _ = 0 := neg_zero
      have negConstantCoeffs : (neg (Dense.Basic.DensePolynomial.constant c)).coeffs = [-c]
        := by
        change (Dense.Basic.DensePolynomial.normalize (Dense.Basic.DensePolynomial.constant (-c))).coeffs = [-c]
        rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne negativeNonzero]; rfl
      have negConstant : neg (Dense.Basic.DensePolynomial.constant c) = ⟨[-c]⟩ :=
        Dense.Basic.DensePolynomial.ext negConstantCoeffs
      let tailDifference := List.zipWith (· + ·) (trailing :: rest)
        (List.replicate rest.length 0 ++ [-c])
      have tailDifferenceLength : tailDifference.length = rest.length + 1 := by
        have alignedLength : (trailing :: rest).length =
            (List.replicate rest.length (0 : K) ++ [-c]).length := by
          rw [Append.length_append, Replicate.length_replicate]; rfl
        exact Zip.length_zipWith_of_length_eq (· + ·) (trailing :: rest)
          (List.replicate rest.length 0 ++ [-c]) alignedLength
      let difference := add ⟨p.leadingCoeff :: trailing :: rest⟩
        (neg (Dense.Basic.DensePolynomial.constant c))
      have differenceCoeffs : difference.coeffs =
          p.leadingCoeff :: tailDifference := by
        dsimp only [difference]
        rw [negConstant]
        simp only [add, List.length_cons, List.length_nil]
        have oneBound : 1 ≤ rest.length + 1 + 1 :=
          Nat.succ_le_succ (Nat.zero_le (rest.length + 1))
        have maximum : max (rest.length + 1 + 1) 1 = rest.length + 1 + 1 := by
          by_cases ordered : rest.length + 1 + 1 ≤ 1
          · exact (max_def _ _).trans
              ((if_pos ordered).trans (Nat.le_antisymm oneBound ordered))
          · exact (max_def _ _).trans (if_neg ordered)
        have padding : rest.length + 1 + 1 - 1 = rest.length + 1 := by
          exact Subtraction.add_sub_cancel_right (rest.length + 1) 1
        simp only [maximum, Nat.sub_self, padding, padLeft,
          List.replicate_zero, List.nil_append]
        rw [List.replicate_succ, List.cons_append,
          List.zipWith_cons_cons, add_zero]
        change (p.leadingCoeff ::
          List.zipWith (· + ·) (trailing :: rest)
            (List.replicate rest.length 0 ++ [-c])).dropWhile (· = 0) = _
        rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
          p.leadingCoeff _ (decide_eq_false leadingNonzero)]
      have differenceShape : difference =
          ⟨p.leadingCoeff :: tailDifference⟩ := Dense.Basic.DensePolynomial.ext differenceCoeffs
      apply Dense.Basic.DensePolynomial.ext
      change (add (Dense.Basic.DensePolynomial.constant c) difference).coeffs = _
      rw [differenceShape]
      simp only [add, Dense.Basic.DensePolynomial.constant, List.length_cons,
        List.length_nil,
        tailDifferenceLength]
      have maximum : max 1 (rest.length + 1 + 1) = rest.length + 1 + 1 :=
        (max_def _ _).trans (if_pos (Nat.succ_le_succ (Nat.zero_le (rest.length + 1))))
      have padding : rest.length + 1 + 1 - 1 = rest.length + 1 := by
        exact Subtraction.add_sub_cancel_right (rest.length + 1) 1
      simp only [maximum, Nat.sub_self, padding, padLeft,
        List.replicate_zero, List.nil_append]
      rw [List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, zero_add]
      change (p.leadingCoeff ::
        List.zipWith (· + ·) (List.replicate rest.length 0 ++ [c])
          tailDifference).dropWhile (· = 0) = _
      rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
        p.leadingCoeff _ (decide_eq_false leadingNonzero)]
      apply congrArg (List.cons p.leadingCoeff)
      dsimp only [tailDifference]
      exact zipWith_trailing_cancel trailing c rest

omit [DecidableEq K] in
/-- Aligned additions cancel opposite updates in the final two coefficient slots.

The retained list has length at least two, and its zero prefix preserves all
earlier entries. Structural recursion reaches the two final scalar additions,
where each original update cancels its opposite. -/
private theorem zipWith_two_trailing_cancel (s t : K) :
  ∀ coefficients : List K, 2 ≤ coefficients.length →
      List.zipWith (· + ·)
          (List.replicate (coefficients.length - 2) 0 ++ [s, t])
          (List.zipWith (· + ·) coefficients
            (List.replicate (coefficients.length - 2) 0 ++ [-s, -t])) =
        coefficients
  | [], length => False.elim (Nat.not_succ_le_zero 1 length)
  | _ :: [], length =>
      False.elim (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ length))
  | first :: second :: rest, _ => by
      cases rest with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.replicate_zero, List.nil_append,
            List.zipWith_cons_cons, List.zipWith]
          apply congrArg₂ List.cons (by ring1)
          apply congrArg₂ List.cons (by ring1) rfl
      | cons third remaining =>
          have inductionHypothesis := zipWith_two_trailing_cancel s t
            (second :: third :: remaining)
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le remaining.length)))
          have exponent :
              (first :: second :: third :: remaining).length - 2 =
                ((second :: third :: remaining).length - 2) + 1 := by
            calc
              (first :: second :: third :: remaining).length - 2 = remaining.length + 1 :=
                Subtraction.add_sub_cancel_right (remaining.length + 1) 2
              _ = ((second :: third :: remaining).length - 2) + 1 :=
                congrArg (fun value : Nat => value + 1)
                  (Subtraction.add_sub_cancel_right remaining.length 2).symm
          rw [exponent, List.replicate_succ]
          change List.zipWith (· + ·)
              (0 :: (List.replicate
                ((second :: third :: remaining).length - 2) 0 ++ [s, t]))
              (List.zipWith (· + ·) (first :: second :: third :: remaining)
                (0 :: (List.replicate
                  ((second :: third :: remaining).length - 2) 0 ++
                    [-s, -t]))) =
            first :: second :: third :: remaining
          rw [List.zipWith_cons_cons, List.zipWith_cons_cons,
            add_zero, zero_add, inductionHypothesis]

/-- Adding back an exact nonzero linear list after subtracting it restores a normalized polynomial of degree at least
two.

The retained degree bound supplies at least two trailing slots. Both aligned
updates preserve the original nonzero leading coefficient, and the final two
scalar updates cancel while retaining the same preceding coefficient list. -/
theorem linear_add_sub_linear_of_normalized
    {p : Dense.Basic.DensePolynomial K} {s t : K}
    (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (sNonzero : s ≠ 0) :
    ⟨[s, t]⟩ + (p - ⟨[s, t]⟩) = p := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    Dense.Basic.DensePolynomial.normalized_coeffs_shape pNonzero
  have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero pNonzero
  rw [pNormalized] at coefficients
  have tailLong : 2 ≤ tail.length := by
    rw [tailLength]
    exact degreeAtLeastTwo
  have pShape : p = ⟨p.leadingCoeff :: tail⟩ := Dense.Basic.DensePolynomial.ext coefficients
  rw [pShape] at ⊢
  have negLinear : neg ⟨[s, t]⟩ = ⟨[-s, -t]⟩ := by
    apply Dense.Basic.DensePolynomial.ext
    change (Dense.Basic.DensePolynomial.normalize ⟨[-s, -t]⟩).coeffs = [-s, -t]
    have negativeNonzero : -s ≠ 0 := by
      intro vanished
      apply sNonzero
      calc
        s = - -s := (InvolutiveNeg.neg_neg s).symm
        _ = -(0 : K) := congrArg (fun value : K => -value) vanished
        _ = 0 := neg_zero
    rw [Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero negativeNonzero]
  have tailReconstructed : (tail.length - 2) + 2 = tail.length :=
    (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le tailLong)
  have leadingLengthBound : 2 ≤ tail.length + 1 := Nat.le_trans tailLong (Nat.le_succ _)
  have firstPadding : tail.length + 1 - 2 = (tail.length - 2) + 1 := by
    calc
      tail.length + 1 - 2 = ((tail.length - 2) + 2) + 1 - 2 :=
        congrArg (fun value : Nat => value + 1 - 2) tailReconstructed.symm
      _ = (tail.length - 2) + 1 :=
        Subtraction.add_sub_cancel_right ((tail.length - 2) + 1) 2
  let tailDifference := List.zipWith (· + ·) tail
    (List.replicate (tail.length - 2) 0 ++ [-s, -t])
  have tailDifferenceLength : tailDifference.length = tail.length := by
    have paddingLength : (List.replicate (tail.length - 2) (0 : K) ++ [-s, -t]).length =
        tail.length := by
      rw [Append.length_append, Replicate.length_replicate]
      exact tailReconstructed
    exact Zip.length_zipWith_of_length_eq (· + ·) tail
      (List.replicate (tail.length - 2) 0 ++ [-s, -t]) paddingLength.symm
  let difference := add ⟨p.leadingCoeff :: tail⟩ (neg ⟨[s, t]⟩)
  have differenceCoeffs : difference.coeffs =
      p.leadingCoeff :: tailDifference := by
    dsimp only [difference]
    rw [negLinear]
    simp only [add, List.length_cons]
    simp only [List.length_nil, Nat.zero_add, Nat.reduceAdd]
    have maximum : max (tail.length + 1) 2 = tail.length + 1 := by
      by_cases ordered : tail.length + 1 ≤ 2
      · exact (max_def _ _).trans
          ((if_pos ordered).trans (Nat.le_antisymm leadingLengthBound ordered))
      · exact (max_def _ _).trans (if_neg ordered)
    rw [maximum, Nat.sub_self, firstPadding]
    simp only [padLeft, List.replicate_zero, List.nil_append]
    rw [List.replicate_succ, List.cons_append,
      List.zipWith_cons_cons, add_zero]
    change (p.leadingCoeff ::
      List.zipWith (· + ·) tail
        (List.replicate (tail.length - 2) 0 ++ [-s, -t])).dropWhile
          (· = 0) = _
    rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
        p.leadingCoeff _ (decide_eq_false leadingNonzero)]
  have differenceShape : difference =
      ⟨p.leadingCoeff :: tailDifference⟩ := Dense.Basic.DensePolynomial.ext differenceCoeffs
  apply Dense.Basic.DensePolynomial.ext
  change (add ⟨[s, t]⟩ difference).coeffs = _
  rw [differenceShape]
  simp only [add, List.length_cons, tailDifferenceLength]
  simp only [List.length_nil, Nat.zero_add, Nat.reduceAdd]
  have maximum : max 2 (tail.length + 1) = tail.length + 1 :=
    (max_def _ _).trans (if_pos leadingLengthBound)
  rw [maximum, Nat.sub_self, firstPadding]
  simp only [padLeft, List.replicate_zero, List.nil_append]
  rw [List.replicate_succ, List.cons_append,
    List.zipWith_cons_cons, zero_add]
  change (p.leadingCoeff ::
    List.zipWith (· + ·)
      (List.replicate (tail.length - 2) 0 ++ [s, t])
      tailDifference).dropWhile (· = 0) = _
  rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
        p.leadingCoeff _ (decide_eq_false leadingNonzero)]
  apply congrArg (List.cons p.leadingCoeff)
  dsimp only [tailDifference]
  exact zipWith_two_trailing_cancel s t tail tailLong

/-- Simultaneous negation distributes through subtraction once both displayed representatives are normalized.

The retained normalization equalities identify the original input coefficient
lists. Negation preserves their lengths and aligned zero padding, while each
paired scalar sum commutes with the original coefficient negation. -/
theorem neg_sub_neg_of_normalized (p q :
  Dense.Basic.DensePolynomial K)
    (pNormalized : p.normalize = p) (qNormalized : q.normalize = q) :
    (-p) - (-q) = -(p - q) := by
  change add (-p) (-(-q)) = neg (add
    p (-q))
  rw [neg_neg, qNormalized]
  have pCoefficients : p.normalize.coeffs = p.coeffs := by
    exact congrArg Dense.Basic.DensePolynomial.coeffs pNormalized
  have qCoefficients : q.normalize.coeffs = q.coeffs := by
    exact congrArg Dense.Basic.DensePolynomial.coeffs qNormalized
  change p.coeffs.dropWhile (· = 0) = p.coeffs at pCoefficients
  change q.coeffs.dropWhile (· = 0) = q.coeffs at qCoefficients
  apply Dense.Basic.DensePolynomial.ext
  simp only [add, neg,
    Dense.Basic.DensePolynomial.normalize_coeffs, neg_coeffs,
    pCoefficients, qCoefficients, Map.length_map]
  rw [padLeft_map_neg, padLeft_map_neg,
    zipWith_neg_add]
  rw [dropWhile_map_neg, dropWhile_map_neg,
    dropWhile_zero_idempotent]

/-- Scalar multiplication of every coefficient. -/
def scale (c : K) (p : Dense.Basic.DensePolynomial K) :
  Dense.Basic.DensePolynomial K :=
  Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (c * ·)⟩

/-- Dense scalar multiplication already returns a normalized representation. -/
@[simp] theorem normalize_scale (c : K) (p :
  Dense.Basic.DensePolynomial K) :
    (scale c p).normalize = scale c p := by
  exact Dense.Basic.DensePolynomial.normalize_normalize _

/-- Scaling by a nonzero field element commutes with removing leading zeros.

The supplied nonzero scalar preserves nonzeroness of each retained nonzero
coefficient. A zero coefficient remains zero, so the original and mapped
lists discard exactly the same leading block. -/
private theorem dropWhile_map_mul_left {c : K} (hc : c ≠ 0) (cs :
  List K) :
    (cs.map (c * ·)).dropWhile (· = 0) =
      (cs.dropWhile (· = 0)).map (c * ·) := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons]
      by_cases ha : a = 0
      · have mappedZero : c * a = 0 := by
          calc
            c * a = c * 0 := congrArg (fun value : K => c * value) ha
            _ = 0 := mul_zero c
        rw [DropWhile.cons_of_true (fun value : K => decide (value = 0))
            (c * a) (as.map (c * ·)) (decide_eq_true mappedZero),
          DropWhile.cons_of_true (fun value : K => decide (value = 0))
            a as (decide_eq_true ha)]
        exact ih
      · have mappedNonzero : c * a ≠ 0 :=
          Dense.Basic.DensePolynomial.mul_ne_zero_direct hc ha
        rw [DropWhile.cons_of_false (fun value : K => decide (value = 0))
            (c * a) (as.map (c * ·)) (decide_eq_false mappedNonzero),
          DropWhile.cons_of_false (fun value : K => decide (value = 0))
            a as (decide_eq_false ha)]; rfl

/-- Nonzero scaling retains exactly the scaled normalized input coefficients. -/
theorem scale_coeffs_of_ne_zero {c : K} (hc : c ≠ 0) (p :
  Dense.Basic.DensePolynomial K) :
    (scale c p).coeffs = p.normalize.coeffs.map (c * ·) := by
  exact dropWhile_map_mul_left hc p.coeffs

/-- Scaling any dense polynomial by zero returns the empty zero polynomial.

Every mapped coefficient is the original scalar zero. The finite leading-zero
scan therefore discards each mapped entry and returns the empty coefficient
list, which is the retained dense zero representation. -/
@[simp] theorem scale_zero_left (p : Dense.Basic.DensePolynomial
  K) : scale 0 p = 0 := by
  apply Dense.Basic.DensePolynomial.ext
  change (p.coeffs.map (0 * ·)).dropWhile (· = 0) = []
  induction p.coeffs with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons]
      change (0 * a :: as.map (0 * ·)).dropWhile (· = 0) = []
      rw [zero_mul, DropWhile.cons_of_true
        (fun value : K => decide (value = 0)) 0 (as.map (0 * ·)) (decide_eq_true rfl)]
      exact ih

omit [DecidableEq K] in
/-- Multiplying every coefficient by one preserves the exact list. -/
private theorem map_one_mul : ∀ coefficients : List K,
    coefficients.map (1 * ·) = coefficients
  | [] => rfl
  | coefficient :: coefficients => by
      rw [List.map_cons, one_mul, map_one_mul coefficients]

/-- Scaling by one returns the normalized input representation. -/
@[simp] theorem scale_one_left (p : Dense.Basic.DensePolynomial K)
  :
    scale 1 p = p.normalize := by
  apply Dense.Basic.DensePolynomial.ext
  change (p.coeffs.map (1 * ·)).dropWhile (· = 0) =
    p.coeffs.dropWhile (· = 0)
  rw [map_one_mul]

/-- Scaling a constant gives the normalized singleton product coefficient. -/
theorem scale_constant (c a : K) :
    scale c (Dense.Basic.DensePolynomial.constant a) = Dense.Basic.DensePolynomial.normalize
      (Dense.Basic.DensePolynomial.constant (c * a)) := rfl

/-- Scaling a negated polynomial by the oppositely signed quotient leaves the normalized representation unchanged.

The supplied nonzero denominator retains both quotient nonzeroness certificates
when the numerator is nonzero. Each original mapped coefficient then agrees
by the explicit inverse-negation law and scalar involution; zero numerators
select the original empty scaled display. -/
theorem scale_div_neg_neg {a b : K} (hb : b ≠ 0) (p :
  Dense.Basic.DensePolynomial K) :
    scale (a / -b) (-p) = scale (a / b) p := by
  by_cases ha : a = 0
  · subst a
    rw [ExplicitField.zero_div, ExplicitField.zero_div,
      scale_zero_left, scale_zero_left]
  · have negativeNonzero : -b ≠ 0 := by
      intro vanished
      apply hb
      calc
        b = - -b := (InvolutiveNeg.neg_neg b).symm
        _ = -(0 : K) := congrArg (fun value : K => -value) vanished
        _ = 0 := neg_zero
    have hab : a / b ≠ 0 := Dense.Basic.DensePolynomial.div_ne_zero_direct ha hb
    have hanegb : a / -b ≠ 0 := Dense.Basic.DensePolynomial.div_ne_zero_direct ha negativeNonzero
    have scalarQuotient (value : K) : (a / -b) * (-value) = (a / b) * value := by
      rw [ExplicitField.div_neg, neg_mul, mul_neg]
      exact InvolutiveNeg.neg_neg (a / b * value)
    have mappedQuotient : ∀ coefficients : List K,
        (coefficients.map (-·)).map ((a / -b) * ·) = coefficients.map ((a / b) * ·) := by
      intro coefficients
      induction coefficients with
      | nil => rfl
      | cons head tail ih =>
          rw [List.map_cons, List.map_cons, List.map_cons]
          exact congrArg₂ List.cons (scalarQuotient head) ih
    apply Dense.Basic.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero hanegb,
      scale_coeffs_of_ne_zero hab]
    rw [normalize_neg, neg_coeffs]
    exact mappedQuotient p.normalize.coeffs

omit [DecidableEq K] in
/-- Scaling both a coefficient list and its accumulator scales the final Horner state. -/
private theorem foldl_map_scale (c x : K) : ∀ (cs : List K) (acc :
  K),
    (cs.map (c * ·)).foldl (fun value a => value * x + a) (c * acc) =
      c * cs.foldl (fun value a => value * x + a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      have hacc : c * acc * x + c * a = c * (acc * x + a) := by ring1
      rw [hacc]
      exact foldl_map_scale c x as (acc * x + a)

/-- Evaluation commutes with dense scalar multiplication. -/
@[simp] theorem eval_scale (c : K) (p :
  Dense.Basic.DensePolynomial K) (x : K) :
    (scale c p).eval x = c * p.eval x := by
  rw [scale, Dense.Basic.DensePolynomial.eval_normalize]
  dsimp only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs]
  simpa only [mul_zero] using foldl_map_scale c x p.coeffs 0

/-- Normalizing before scalar multiplication does not change its result. -/
theorem scale_normalize (c : K) (p : Dense.Basic.DensePolynomial
  K) :
    scale c p.normalize = scale c p := by
  by_cases hc : c = 0
  · subst c
    rw [scale_zero_left, scale_zero_left]
  · apply Dense.Basic.DensePolynomial.ext
    rw [scale_coeffs_of_ne_zero hc, scale_coeffs_of_ne_zero hc,
      Dense.Basic.DensePolynomial.normalize_normalize]

/-- Scaling a polynomial passing the zero test returns the empty zero representation. -/
theorem scale_eq_zero_of_isZero (c : K) {p :
  Dense.Basic.DensePolynomial K}
    (hp : p.isZero = true) : scale c p = 0 := by
  rw [← scale_normalize c p, Dense.Basic.DensePolynomial.normalize_eq_zero_of_isZero hp]
  rfl

/-- Scaling the empty zero polynomial returns zero. -/
@[simp] theorem scale_zero_right (c : K) :
    scale c (0 : Dense.Basic.DensePolynomial K) = 0 :=
  scale_eq_zero_of_isZero c Dense.Basic.DensePolynomial.isZero_zero

/-- Negating the scalar negates the scaled dense polynomial.

The original coefficient maps agree entry by entry by scalar multiplication
with a negated factor. Negation commutes with normalization, so both operations
normalize those exact same mapped entries, including a zero scalar. -/
@[simp] theorem scale_neg_left (c : K) (p :
  Dense.Basic.DensePolynomial K) :
    scale (-c) p = -scale c p := by
  have mappedNegation : ∀ coefficients : List K,
      coefficients.map ((-c) * ·) = (coefficients.map (c * ·)).map (-·) := by
    intro coefficients
    induction coefficients with
    | nil => rfl
    | cons head tail ih =>
        rw [List.map_cons, List.map_cons, List.map_cons]
        exact congrArg₂ List.cons (neg_mul c head) ih
  change Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map ((-c) * ·)⟩ =
    -(Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (c * ·)⟩)
  rw [neg_normalize]
  change Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map ((-c) * ·)⟩ =
    Dense.Basic.DensePolynomial.normalize ⟨(p.coeffs.map (c * ·)).map (-·)⟩
  exact congrArg (fun coefficients : List K =>
    Dense.Basic.DensePolynomial.normalize ⟨coefficients⟩) (mappedNegation p.coeffs)

/-- Scaling a negated polynomial negates the scaled result.

Scaling and negation each commute with the original normalization. On the
retained coefficient list, scaling scalar negatives agrees entry by entry
with negating the original scaled coefficients. -/
@[simp] theorem scale_neg_right (c : K) (p :
  Dense.Basic.DensePolynomial K) :
    scale c (-p) = -scale c p := by
  have mappedNegation : ∀ coefficients : List K,
      (coefficients.map (-·)).map (c * ·) = (coefficients.map (c * ·)).map (-·) := by
    intro coefficients
    induction coefficients with
    | nil => rfl
    | cons head tail ih =>
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons]
        exact congrArg₂ List.cons (mul_neg c head) ih
  change scale c
      (Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (-·)⟩) =
    -(Dense.Basic.DensePolynomial.normalize ⟨p.coeffs.map (c * ·)⟩)
  rw [scale_normalize, neg_normalize]
  change Dense.Basic.DensePolynomial.normalize ⟨(p.coeffs.map (-·)).map (c * ·)⟩ =
    Dense.Basic.DensePolynomial.normalize ⟨(p.coeffs.map (c * ·)).map (-·)⟩
  exact congrArg (fun coefficients : List K =>
    Dense.Basic.DensePolynomial.normalize ⟨coefficients⟩) (mappedNegation p.coeffs)

/-- Multiplication by `X^n`, implemented by appending `n` zero coefficients. -/
def shift (n : ℕ) (p : Dense.Basic.DensePolynomial K) :
  Dense.Basic.DensePolynomial K :=
  if p.isZero then 0 else ⟨p.normalize.coeffs ++ List.replicate n 0⟩

/-- Every degree shift of the empty zero polynomial is zero. -/
@[simp] theorem shift_zero (n : ℕ) :
  shift n (0 : Dense.Basic.DensePolynomial K) = 0 := rfl

/-- Dense shifting returns an already normalized representation.

The retained Boolean zero test either selects the empty zero display or
preserves the normalized nonzero leading coefficient. Appending the finite
zero block leaves that head nonzero, so normalization retains the full list. -/
@[simp] theorem normalize_shift (n : ℕ) (p :
  Dense.Basic.DensePolynomial K) :
    (shift n p).normalize = shift n p := by
  cases pZero : p.isZero with
  | true =>
      rw [shift, if_pos pZero]; rfl
  | false =>
      have notZero : ¬p.isZero = true := fun zero => Bool.noConfusion (pZero.symm.trans zero)
      obtain ⟨tail, coefficients, _⟩ := Dense.Basic.DensePolynomial.normalized_coeffs_shape pZero
      have leadingNonzero := Dense.Basic.DensePolynomial.leadingCoeff_ne_zero pZero
      apply Dense.Basic.DensePolynomial.ext
      rw [shift, if_neg notZero]
      change
        ((p.normalize.coeffs ++ List.replicate n 0).dropWhile (· = 0)) =
          p.normalize.coeffs ++ List.replicate n 0
      rw [coefficients]
      change (p.leadingCoeff :: (tail ++ List.replicate n 0)).dropWhile (· = 0) =
        p.leadingCoeff :: (tail ++ List.replicate n 0)
      exact DropWhile.cons_of_false (fun value : K => decide (value = 0))
        p.leadingCoeff (tail ++ List.replicate n 0) (decide_eq_false leadingNonzero)

/-- Shifting by `n` adds at most `n` finite coefficient slots.

The original zero test selects the empty display or appends the retained
block of `n` zeroes to the normalized coefficients. The latter display is
already normalized and its exact finite list length adds that block size. -/
theorem degreeCount_shift_le (n : ℕ) (p :
  Dense.Basic.DensePolynomial K) :
    (shift n p).degreeCount ≤ p.degreeCount + n := by
  cases zero : p.isZero with
  | true =>
      rw [shift, if_pos zero, Dense.Basic.DensePolynomial.degreeCount]
      exact Nat.zero_le _
  | false =>
      have notZero : ¬p.isZero = true := fun accepted => Bool.noConfusion (zero.symm.trans accepted)
      rw [Dense.Basic.DensePolynomial.degreeCount, normalize_shift,
        shift, if_neg notZero,
        Append.length_append, Replicate.length_replicate]
      exact Nat.le_refl _

/-- A displayed constant occupies at most one normalized coefficient slot. -/
theorem degreeCount_constant_le_one (a : K) :
    (Dense.Basic.DensePolynomial.constant a).degreeCount ≤ 1 := by
  by_cases zero : a = 0
  · subst a
    change (Dense.Basic.DensePolynomial.normalize (Dense.Basic.DensePolynomial.constant (0 : K))).coeffs.length ≤ 1
    rw [Dense.Basic.DensePolynomial.normalize_constant_zero]
    exact Nat.zero_le _
  · rw [Dense.Basic.DensePolynomial.degreeCount, Dense.Basic.DensePolynomial.normalize_constant_of_ne zero]
    rfl

/-- Degree shifting commutes with dense negation.

Negation preserves the original Boolean zero test and normalized coefficient
list. The appended zero block is fixed by scalar negation, and structural
mapping preserves the exact original coefficient prefix. -/
@[simp] theorem shift_neg (n : ℕ) (p : Dense.Basic.DensePolynomial
  K) :
    shift n (-p) = -shift n p := by
  have mappedBlock : ∀ coefficients : List K,
      (coefficients ++ List.replicate n 0).map (-·) =
        coefficients.map (-·) ++ List.replicate n 0 := by
    intro coefficients
    induction coefficients with
    | nil =>
        change (List.replicate n (0 : K)).map (-·) = List.replicate n 0
        calc
          (List.replicate n (0 : K)).map (-·) = List.replicate n (-(0 : K)) :=
            Replicate.map_replicate (fun value : K => -value) n 0
          _ = List.replicate n 0 := congrArg (List.replicate n) (neg_zero : -(0 : K) = 0)
    | cons head tail ih =>
        change -head :: (tail ++ List.replicate n 0).map (-·) =
          -head :: (tail.map (-·) ++ List.replicate n 0)
        exact congrArg (List.cons (-head)) ih
  cases pZero : p.isZero with
  | true =>
      have negZero : (-p).isZero = true := (isZero_neg p).trans pZero
      rw [shift, if_pos negZero,
        shift, if_pos pZero]; rfl
  | false =>
      have notZero : ¬p.isZero = true := fun zero => Bool.noConfusion (pZero.symm.trans zero)
      have negNonzero : (-p).isZero = false := (isZero_neg p).trans pZero
      have negNotZero : ¬(-p).isZero = true := fun zero => Bool.noConfusion (negNonzero.symm.trans zero)
      apply Dense.Basic.DensePolynomial.ext
      rw [shift, if_neg negNotZero,
        normalize_neg, neg_coeffs]
      rw [neg_coeffs, normalize_shift,
        shift, if_neg notZero]
      exact (mappedBlock p.normalize.coeffs).symm

/-- Shifting a nonzero constant once gives the exact descending table `[a, 0]`.

The supplied nonzero coefficient keeps the original singleton constant
normalized and excludes the zero-test branch. The retained shift then appends
its single zero coefficient to that singleton. -/
theorem shift_one_constant_of_ne {a : K} (ha : a ≠ 0) :
    shift 1 (Dense.Basic.DensePolynomial.constant a) = ⟨[a, 0]⟩ := by
  have normalized := Dense.Basic.DensePolynomial.normalize_constant_of_ne ha
  have notZero : ¬(Dense.Basic.DensePolynomial.constant a).isZero = true := by
    change ¬(Dense.Basic.DensePolynomial.constant a).normalize.coeffs.isEmpty = true
    rw [normalized]
    intro impossible
    exact Bool.noConfusion impossible
  rw [shift, if_neg notZero, normalized]; rfl

omit [DecidableEq K] in
/-- Folding a zero block multiplies the initial accumulator by the corresponding input power.

Each retained zero coefficient advances the accumulator by multiplication
with the displayed input. The zero-length block retains the accumulator,
and a successor block contributes the next input-power factor. -/
private theorem foldl_replicate_zero (x : K) (n : ℕ) (acc : K) :
    (List.replicate n 0).foldl (fun value a => value * x + a) acc = acc * x ^ n := by
  induction n generalizing acc with
  | zero =>
      calc
        acc = acc * 1 := (mul_one acc).symm
        _ = acc * x ^ 0 := congrArg (fun factor : K => acc * factor) (pow_zero x).symm
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, add_zero, ih, pow_succ]
      ring1

omit [DecidableEq K] in
/-- Appending a zero block multiplies a descending Horner value by the corresponding input power. -/
theorem evalCoeffs_append_replicate_zero (x : K) (cs : List K) (n
  : ℕ) :
    Dense.Basic.DensePolynomial.evalCoeffs x (cs ++ List.replicate n 0) = Dense.Basic.DensePolynomial.evalCoeffs x cs *
      x ^ n := open Purelib in by
  simp only [Dense.Basic.DensePolynomial.evalCoeffs, Data.List.Fold.foldl_append]
  exact foldl_replicate_zero x n _

/-- A polynomial passing the dense zero test evaluates to zero at every supplied point.

The retained zero-test certificate identifies its normalized display with
the original empty polynomial. Normalization preserves evaluation, and the
empty coefficient fold has the supplied scalar zero as its value. -/
theorem eval_eq_zero_of_isZero {p : Dense.Basic.DensePolynomial K}
  (hp : p.isZero = true) (x : K) :
    p.eval x = 0 := by
  calc
    p.eval x = p.normalize.eval x := (Dense.Basic.DensePolynomial.eval_normalize p x).symm
    _ = (0 : Dense.Basic.DensePolynomial K).eval x :=
      congrArg (fun polynomial : Dense.Basic.DensePolynomial K => polynomial.eval x)
        (Dense.Basic.DensePolynomial.normalize_eq_zero_of_isZero hp)
    _ = 0 := Dense.Basic.DensePolynomial.eval_zero x

/-- A displayed nonzero evaluation makes the polynomial fail the zero test. -/
theorem isZero_false_of_eval_ne {p : Dense.Basic.DensePolynomial
  K} {x : K}
    (hp : p.eval x ≠ 0) : p.isZero = false := by
  cases zero : p.isZero with
  | false => rfl
  | true => exact (hp (eval_eq_zero_of_isZero zero x)).elim

/-- A degree shift multiplies the polynomial value by the matching input power. -/
@[simp] theorem eval_shift (n : ℕ) (p :
  Dense.Basic.DensePolynomial K) (x : K) :
    (shift n p).eval x = p.eval x * x ^ n := by
  rw [shift]
  split
  · rename_i hp
    rw [Dense.Basic.DensePolynomial.eval_zero, eval_eq_zero_of_isZero hp, zero_mul]
  · change Dense.Basic.DensePolynomial.evalCoeffs x (p.normalize.coeffs ++ List.replicate n 0) =
        Dense.Basic.DensePolynomial.evalCoeffs x p.coeffs * x ^ n
    rw [evalCoeffs_append_replicate_zero]
    change Dense.Basic.DensePolynomial.evalCoeffs x (p.coeffs.dropWhile (· = 0)) * x ^ n =
      Dense.Basic.DensePolynomial.evalCoeffs x p.coeffs * x ^ n
    rw [Dense.Basic.DensePolynomial.evalCoeffs_dropWhile_zero]

/-- Normalization can only shorten a finite coefficient list. -/
public theorem degreeCount_le_coeffs_length (p :
  Dense.Basic.DensePolynomial K) :
    p.degreeCount ≤ p.coeffs.length :=
  Purelib.Data.List.DropWhile.Bounds.length_dropWhile_zero_le p.coeffs

/-- The normalized sum has at most the maximum of its input coefficient-list lengths.

The retained left-padding length bounds the paired coefficient traversal.
Removing leading zeroes cannot increase that original finite output length. -/
public theorem coeffs_length_add_le (p q :
  Dense.Basic.DensePolynomial K) :
    (p + q).coeffs.length ≤ max p.coeffs.length q.coeffs.length := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := by
    change p.coeffs.length ≤ max p.coeffs.length q.coeffs.length
    by_cases ordered : p.coeffs.length ≤ q.coeffs.length
    · rw [max_def, if_pos ordered]
      exact ordered
    · rw [max_def, if_neg ordered]
  have hps : ps.length = n := by
    dsimp only [ps, padLeft]
    rw [Append.length_append, Replicate.length_replicate]
    exact (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le hp)
  change ((List.zipWith (· + ·) ps qs).dropWhile (· = 0)).length ≤ n
  have paddedBound : ps.length ≤ n := by
    rw [hps]
  exact Nat.le_trans (Purelib.Data.List.DropWhile.Bounds.length_dropWhile_zero_le _)
    (Nat.le_trans (Zip.length_zipWith_le_left (· + ·) ps qs) paddedBound)

/-- Adding normalized polynomials has degree count at most the maximum input degree count. -/
theorem degreeCount_add_le_of_normalized {p q :
  Dense.Basic.DensePolynomial K}
    (hp : p.normalize = p) (hq : q.normalize = q) :
    (p + q).degreeCount ≤ max p.degreeCount q.degreeCount := by
  change (p + q).normalize.coeffs.length ≤ _
  rw [normalize_add]
  apply (coeffs_length_add_le p q).trans
  change max p.coeffs.length q.coeffs.length ≤
    max p.normalize.coeffs.length q.normalize.coeffs.length
  rw [hp, hq]

/-- Subtracting from a normalized left polynomial has degree count at most the maximum input degree count. -/
theorem degreeCount_sub_le_of_normalized {p q :
  Dense.Basic.DensePolynomial K}
    (hp : p.normalize = p) :
    (p - q).degreeCount ≤ max p.degreeCount q.degreeCount := by
  change (p + -q).degreeCount ≤ _
  have hneg : (-q).normalize = -q := normalize_neg q
  have hbound := degreeCount_add_le_of_normalized hp hneg
  rw [degreeCount_neg] at hbound
  exact hbound

/-- The scaled output list has length at most the original normalized degree count.

A zero scalar gives the empty output. A nonzero scalar retains one mapped
coefficient for each normalized input entry, preserving that exact list length. -/
public theorem coeffs_length_scale_le (c : K) (p :
  Dense.Basic.DensePolynomial K) :
    (scale c p).coeffs.length ≤ p.degreeCount := by
  by_cases hc : c = 0
  · subst c
    rw [scale_zero_left]
    exact Nat.zero_le _
  · rw [scale_coeffs_of_ne_zero hc, Map.length_map]
    exact Nat.le_refl _

/-- A one-degree shift adds at most one coefficient to the normalized input count.

The zero-test branch keeps the empty display. The nonzero branch appends the
retained singleton zero to the normalized coefficient list, adding one entry. -/
public theorem coeffs_length_shift_le (p :
  Dense.Basic.DensePolynomial K) :
    (shift 1 p).coeffs.length ≤ p.degreeCount + 1 := by
  rw [shift]
  split
  · exact Nat.zero_le _
  · change (p.normalize.coeffs ++ [0]).length ≤ p.normalize.coeffs.length + 1
    rw [Append.length_append]
    exact Nat.le_refl _

end DensePolynomial

end Purelib.Polynomial.Dense.Basic

end
