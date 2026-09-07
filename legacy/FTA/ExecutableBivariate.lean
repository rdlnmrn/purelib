import FTA.DensePolynomialBridge
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Executable bivariate polynomials and Sylvester determinants

Mathlib's sparse polynomial ring is an excellent specification type, but its
generic arithmetic instances are intentionally not executable.  This module
stores both variables as finite high-to-low coefficient lists and implements
the operations needed by the resultant specifications by structural
recursion.  Conversion back to `Polynomial (Polynomial K)` constructs both
finite supports directly.
-/

namespace FTA.ExecutableBivariate

open FTA.ComputablePolynomial

/-- Construct a sparse specification polynomial directly from a finite
high-to-low coefficient list. -/
def polynomialOfHighCoeffs {R : Type*} [Semiring R] [DecidableEq R]
    (coeffs : List R) : Polynomial R :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff coeffs.reverse.toFinsupp)

@[simp] theorem coeff_polynomialOfHighCoeffs
    {R : Type*} [Semiring R] [DecidableEq R]
    (coeffs : List R) (n : ℕ) :
    (polynomialOfHighCoeffs coeffs).coeff n = coeffs.reverse.getD n 0 := by
  rfl

/-- Reading the complete high-to-low coefficient list and rebuilding its
finite support is an exact round trip. -/
theorem polynomialOfHighCoeffs_coeffList
    {R : Type*} [Semiring R] [DecidableEq R] (p : Polynomial R) :
    polynomialOfHighCoeffs p.coeffList = p := by
  apply Polynomial.ext
  intro n
  rw [coeff_polynomialOfHighCoeffs]
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Polynomial.coeffList,
      Polynomial.withBotSucc_degree_eq_natDegree_add_one hp]
    simp only [List.map_reverse, List.reverse_reverse]
    by_cases hn : n < p.natDegree + 1
    · rw [List.getD_eq_getElem _ 0 (by simpa using hn)]
      simp
    · have hdegree : p.natDegree < n := by omega
      rw [List.getD_eq_default _ 0 (by simpa using hn)]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt hdegree).symm

/-- A bivariate polynomial whose outer coefficients are executable dense
polynomials in the inner variable.  Both lists are high-to-low. -/
structure DenseBivariate (K : Type*) where
  coeffs : List (DensePolynomial K)
deriving DecidableEq, Repr

namespace DenseBivariate

variable {K : Type*} [Field K] [DecidableEq K]

def zero : DenseBivariate K := ⟨[]⟩

def constant (a : K) : DenseBivariate K :=
  ⟨[DensePolynomial.constant a]⟩

def outerX : DenseBivariate K :=
  ⟨[DensePolynomial.constant 1, (0 : DensePolynomial K)]⟩

def innerX : DenseBivariate K :=
  ⟨[⟨[1, 0]⟩]⟩

def padLeft (n : ℕ) (coeffs : List (DensePolynomial K)) :
    List (DensePolynomial K) :=
  List.replicate n 0 ++ coeffs

def add (p q : DenseBivariate K) : DenseBivariate K :=
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  ⟨List.zipWith (· + ·) ps qs⟩

def neg (p : DenseBivariate K) : DenseBivariate K :=
  ⟨p.coeffs.map (-·)⟩

def sub (p q : DenseBivariate K) : DenseBivariate K :=
  add p (neg q)

/-- Multiplication by the outer variable. -/
def shiftOuter (p : DenseBivariate K) : DenseBivariate K :=
  if p.coeffs.isEmpty then zero else ⟨p.coeffs ++ [0]⟩

/-- Multiply every outer coefficient by an inner dense polynomial. -/
def scaleInner (c : DensePolynomial K) (p : DenseBivariate K) :
    DenseBivariate K :=
  ⟨p.coeffs.map (c * ·)⟩

/-- Outer Horner multiplication, using executable dense multiplication for
the inner coefficients. -/
def mul (p q : DenseBivariate K) : DenseBivariate K :=
  p.coeffs.foldl
    (fun acc a ↦ add (shiftOuter acc) (scaleInner a q)) zero

def pow (p : DenseBivariate K) : ℕ → DenseBivariate K
  | 0 => constant 1
  | n + 1 => mul (pow p n) p

def scale (a : K) (p : DenseBivariate K) : DenseBivariate K :=
  ⟨p.coeffs.map (DensePolynomial.scale a)⟩

/-- Horner embedding of an ordinary sparse polynomial as an outer
polynomial with constant inner coefficients. -/
def lift (p : Polynomial K) : DenseBivariate K :=
  ⟨p.coeffList.map DensePolynomial.constant⟩

/-- Horner substitution into a bivariate polynomial. -/
def composeOuter (p : Polynomial K) (q : DenseBivariate K) :
    DenseBivariate K :=
  p.coeffList.foldl
    (fun acc a ↦ add (mul acc q) (constant a)) zero

/-- Finite geometric divided difference for a power. -/
def powerDifferenceQuotient (n : ℕ) : DenseBivariate K :=
  (List.range n).foldl
    (fun acc i ↦
      add acc (mul (pow (add outerX innerX) i)
        (pow outerX (n - 1 - i)))) zero

/-- One simultaneous Horner step for the original polynomial and its divided
difference.  If the accumulated polynomial is `q`, the divided difference of
`qX+a` is `Δq·(X+T)+q`. -/
def dividedDifferenceStep
    (state : DenseBivariate K × DenseBivariate K) (a : K) :
    DenseBivariate K × DenseBivariate K :=
  (add (mul state.1 outerX) (constant a),
    add (mul state.2 (add outerX innerX)) state.1)

/-- Explicit divided difference computed simultaneously with a Horner pass
over the finite coefficient list. -/
def dividedDifference (p : Polynomial K) : DenseBivariate K :=
  (p.coeffList.foldl dividedDifferenceStep (zero, zero)).2

theorem coeffs_length_add (p q : DenseBivariate K) :
    (add p q).coeffs.length = max p.coeffs.length q.coeffs.length := by
  simp [add, padLeft, Nat.sub_add_cancel (le_max_left _ _),
    Nat.sub_add_cancel (le_max_right _ _)]

omit [Field K] [DecidableEq K] in
theorem coeffs_length_shiftOuter_le (p : DenseBivariate K) :
    (shiftOuter p).coeffs.length ≤ p.coeffs.length + 1 := by
  rw [shiftOuter]
  split
  · simp [zero]
  · simp

@[simp] theorem coeffs_length_scaleInner
    (c : DensePolynomial K) (p : DenseBivariate K) :
    (scaleInner c p).coeffs.length = p.coeffs.length := by
  simp [scaleInner]

private theorem coeffs_length_mulFold_le (q : DenseBivariate K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : DenseBivariate K) (bound : ℕ),
      q.coeffs.length ≤ bound + 1 →
      acc.coeffs.length ≤ bound →
      (coeffs.foldl
          (fun value a => add (shiftOuter value) (scaleInner a q)) acc).coeffs.length ≤
        bound + coeffs.length
  | [], _, _, _, hacc => by simpa using hacc
  | a :: as, acc, bound, hq, hacc => by
      simp only [List.foldl_cons, List.length_cons]
      have hnext :
          (add (shiftOuter acc) (scaleInner a q)).coeffs.length ≤ bound + 1 := by
        rw [coeffs_length_add, coeffs_length_scaleInner]
        apply max_le
        · exact (coeffs_length_shiftOuter_le acc).trans (by omega)
        · exact hq.trans (by omega)
      have hrecursive := coeffs_length_mulFold_le q as
        (add (shiftOuter acc) (scaleInner a q)) (bound + 1)
        (by omega) hnext
      omega

theorem coeffs_length_mul_le (p q : DenseBivariate K)
    (hq : q.coeffs ≠ []) :
    (mul p q).coeffs.length ≤ p.coeffs.length + q.coeffs.length - 1 := by
  have hqPositive : 0 < q.coeffs.length := List.length_pos_iff.mpr hq
  rw [mul]
  have h := coeffs_length_mulFold_le q p.coeffs zero (q.coeffs.length - 1)
    (by omega) (by simp [zero])
  omega

private theorem dividedDifferenceFold_coeffs_length_le :
    ∀ (coeffs : List K) (state : DenseBivariate K × DenseBivariate K) (bound : ℕ),
      state.1.coeffs.length ≤ bound →
      state.2.coeffs.length ≤ bound →
      let finalState := coeffs.foldl dividedDifferenceStep state
      finalState.1.coeffs.length ≤ bound + coeffs.length ∧
        finalState.2.coeffs.length ≤ bound + coeffs.length
  | [], _, _, hfirst, hsecond => ⟨hfirst, hsecond⟩
  | a :: as, state, bound, hfirst, hsecond => by
      simp only [List.foldl_cons, List.length_cons]
      have hnextFirst :
          (dividedDifferenceStep state a).1.coeffs.length ≤ bound + 1 := by
        dsimp only [dividedDifferenceStep]
        rw [coeffs_length_add]
        apply max_le
        · have hmul := coeffs_length_mul_le state.1 outerX (by simp [outerX])
          simp only [outerX, List.length_cons, List.length_nil,
            Nat.reduceAdd] at hmul
          apply hmul.trans
          omega
        · simp [constant]
      have hnextSecond :
          (dividedDifferenceStep state a).2.coeffs.length ≤ bound + 1 := by
        dsimp only [dividedDifferenceStep]
        rw [coeffs_length_add]
        apply max_le
        · have htranslatedLength :
              (add outerX innerX : DenseBivariate K).coeffs.length = 2 := by
            rw [coeffs_length_add]
            simp [outerX, innerX]
          have htranslatedNonempty :
              (add outerX innerX : DenseBivariate K).coeffs ≠ [] := by
            intro hempty
            have := congrArg List.length hempty
            rw [htranslatedLength] at this
            simp at this
          have hmul := coeffs_length_mul_le state.2
            (add outerX innerX) htranslatedNonempty
          rw [htranslatedLength] at hmul
          apply hmul.trans
          omega
        · exact hfirst.trans (by omega)
      have hrecursive := dividedDifferenceFold_coeffs_length_le as
        (dividedDifferenceStep state a) (bound + 1) hnextFirst hnextSecond
      constructor <;> omega

/-- The divided-difference program displays no more outer coefficient slots
than the finite coefficient list it scans. -/
theorem dividedDifference_coeffs_length_le_coeffList (p : Polynomial K) :
    (dividedDifference p).coeffs.length ≤ p.coeffList.length := by
  have h := dividedDifferenceFold_coeffs_length_le p.coeffList
    (zero, zero) 0 (by simp [zero]) (by simp [zero])
  simpa [dividedDifference] using h.2

/-- Evaluate first in the inner variable and then by outer Horner recursion. -/
def eval (p : DenseBivariate K) (x t : K) : K :=
  p.coeffs.foldl (fun acc a ↦ acc * x + a.eval t) 0

omit [DecidableEq K] in
@[simp] theorem eval_zero (x t : K) : eval zero x t = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem eval_constant (a x t : K) : eval (constant a) x t = a := by
  simp [eval, constant]

omit [DecidableEq K] in
@[simp] theorem eval_outerX (x t : K) : eval (outerX : DenseBivariate K) x t = x := by
  rw [eval]
  change [DensePolynomial.constant (1 : K), (0 : DensePolynomial K)].foldl
      (fun acc a ↦ acc * x + a.eval t) 0 = x
  simp

omit [DecidableEq K] in
@[simp] theorem eval_innerX (x t : K) : eval (innerX : DenseBivariate K) x t = t := by
  rw [eval]
  change [(⟨[1, 0]⟩ : DensePolynomial K)].foldl
      (fun acc a ↦ acc * x + a.eval t) 0 = t
  simp [DensePolynomial.eval, DensePolynomial.evalCoeffs]

omit [DecidableEq K] in
private theorem eval_foldl_append_zero (x t : K)
    (coeffs : List (DensePolynomial K)) (acc : K) :
    (coeffs ++ [0]).foldl
        (fun value (a : DensePolynomial K) ↦ value * x + a.eval t) acc =
      coeffs.foldl
        (fun value (a : DensePolynomial K) ↦ value * x + a.eval t) acc * x := by
  simp [List.foldl_append]

omit [DecidableEq K] in
@[simp] theorem eval_shiftOuter (p : DenseBivariate K) (x t : K) :
    eval (shiftOuter p) x t = eval p x t * x := by
  rw [shiftOuter]
  split
  · rename_i hp
    have hempty : p.coeffs = [] := List.isEmpty_iff.mp hp
    simp [eval, zero, hempty]
  · exact eval_foldl_append_zero x t p.coeffs 0

private theorem eval_foldl_map_scaleInner
    (c : DensePolynomial K) (x t : K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : K),
      (coeffs.map (c * ·)).foldl
          (fun value a ↦ value * x + a.eval t) (c.eval t * acc) =
        c.eval t * coeffs.foldl
          (fun value a ↦ value * x + a.eval t) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons, DensePolynomial.eval_mul]
      rw [show c.eval t * acc * x + c.eval t * a.eval t =
          c.eval t * (acc * x + a.eval t) by ring]
      exact eval_foldl_map_scaleInner c x t as (acc * x + a.eval t)

@[simp] theorem eval_scaleInner (c : DensePolynomial K)
    (p : DenseBivariate K) (x t : K) :
    eval (scaleInner c p) x t = c.eval t * eval p x t := by
  change (p.coeffs.map (c * ·)).foldl
      (fun value a ↦ value * x + a.eval t) 0 = _
  change (p.coeffs.map (c * ·)).foldl
      (fun value a ↦ value * x + a.eval t) 0 =
    c.eval t * p.coeffs.foldl
      (fun value a ↦ value * x + a.eval t) 0
  simpa using eval_foldl_map_scaleInner c x t p.coeffs 0

omit [DecidableEq K] in
private theorem eval_foldl_replicate_zero (x t : K) (n : ℕ)
    (coeffs : List (DensePolynomial K)) :
    (List.replicate n 0 ++ coeffs).foldl
        (fun value (a : DensePolynomial K) ↦ value * x + a.eval t) 0 =
      coeffs.foldl
        (fun value (a : DensePolynomial K) ↦ value * x + a.eval t) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

private theorem eval_foldl_zipWith_add (x t : K) :
    ∀ (as bs : List (DensePolynomial K)) (accA accB : K),
      as.length = bs.length →
      (List.zipWith (· + ·) as bs).foldl
          (fun value a ↦ value * x + a.eval t) (accA + accB) =
        as.foldl (fun value a ↦ value * x + a.eval t) accA +
          bs.foldl (fun value a ↦ value * x + a.eval t) accB
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, accA, accB, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.zipWith_cons_cons, List.foldl_cons,
        DensePolynomial.eval_add]
      rw [show (accA + accB) * x + (a.eval t + b.eval t) =
          (accA * x + a.eval t) + (accB * x + b.eval t) by ring]
      exact eval_foldl_zipWith_add x t as bs
        (accA * x + a.eval t) (accB * x + b.eval t) h

@[simp] theorem eval_add (p q : DenseBivariate K) (x t : K) :
    eval (add p q) x t = eval p x t + eval q x t := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := le_max_left _ _
  have hq : q.coeffs.length ≤ n := le_max_right _ _
  have hps : ps.length = n := by
    simp [ps, padLeft, Nat.sub_add_cancel hp]
  have hqs : qs.length = n := by
    simp [qs, padLeft, Nat.sub_add_cancel hq]
  change (List.zipWith (· + ·) ps qs).foldl
      (fun value a ↦ value * x + a.eval t) 0 = _
  rw [show (0 : K) = 0 + 0 by ring,
    eval_foldl_zipWith_add x t ps qs 0 0 (hps.trans hqs.symm)]
  simp only [ps, qs, padLeft, eval_foldl_replicate_zero]
  rfl

private theorem eval_foldl_mul (q : DenseBivariate K) (x t : K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : DenseBivariate K),
      eval (coeffs.foldl
          (fun value a ↦ add (shiftOuter value) (scaleInner a q)) acc) x t =
        coeffs.foldl
          (fun value a ↦ value * x + a.eval t * eval q x t)
          (eval acc x t)
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.foldl_cons]
      rw [eval_foldl_mul q x t as,
        eval_add, eval_shiftOuter, eval_scaleInner]

@[simp] theorem eval_mul (p q : DenseBivariate K) (x t : K) :
    eval (mul p q) x t = eval p x t * eval q x t := by
  rw [mul, eval_foldl_mul]
  change p.coeffs.foldl
      (fun value a ↦ value * x + a.eval t * eval q x t) 0 = _
  have hscaled : ∀ (coeffs : List (DensePolynomial K)) (acc : K),
      coeffs.foldl
          (fun value a ↦ value * x + a.eval t * eval q x t)
          (acc * eval q x t) =
        coeffs.foldl (fun value a ↦ value * x + a.eval t) acc *
          eval q x t := by
    intro coeffs acc
    induction coeffs generalizing acc with
    | nil => rfl
    | cons a as ih =>
        simp only [List.foldl_cons]
        rw [show acc * eval q x t * x + a.eval t * eval q x t =
            (acc * x + a.eval t) * eval q x t by ring, ih]
  change p.coeffs.foldl
      (fun value a ↦ value * x + a.eval t * eval q x t) 0 =
    p.coeffs.foldl (fun value a ↦ value * x + a.eval t) 0 * eval q x t
  simpa using hscaled p.coeffs 0

@[simp] theorem eval_pow (p : DenseBivariate K) (n : ℕ) (x t : K) :
    eval (pow p n) x t = eval p x t ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

/-- Specialize the inner parameter and retain the outer polynomial. -/
def atParameter (t : K) (p : DenseBivariate K) : Polynomial K :=
  polynomialOfHighCoeffs (p.coeffs.map (·.eval t))

/-- Read an outer coefficient, with zero outside the displayed finite list. -/
def coeff (p : DenseBivariate K) (n : ℕ) : DensePolynomial K :=
  p.coeffs.reverse.getD n 0

@[simp] theorem coeff_atParameter (t : K) (p : DenseBivariate K) (n : ℕ) :
    (atParameter t p).coeff n = (p.coeff n).eval t := by
  rw [atParameter, coeff_polynomialOfHighCoeffs, coeff]
  rw [← List.map_reverse]
  simpa only [DensePolynomial.eval_zero] using
    (List.getD_map p.coeffs.reverse (0 : DensePolynomial K)
      (fun q ↦ q.eval t))

/-- Specialization followed by ordinary polynomial evaluation agrees with
the two-level executable Horner evaluator. -/
theorem eval_atParameter (p : DenseBivariate K) (x t : K) :
    Polynomial.eval x (atParameter t p) = eval p x t := by
  change Polynomial.eval x
      ((⟨p.coeffs.map (·.eval t)⟩ : DensePolynomial K).toPolynomial) = _
  rw [DensePolynomial.eval_toPolynomial]
  rw [eval]
  simp only [DensePolynomial.eval, DensePolynomial.evalCoeffs]
  rw [List.foldl_map]

theorem natDegree_atParameter_lt_length_of_coeffs_ne_nil
    (p : DenseBivariate K) (t : K) (hp : p.coeffs ≠ []) :
    (atParameter t p).natDegree < p.coeffs.length := by
  have hlen : 0 < p.coeffs.length := List.length_pos_iff.mpr hp
  have hdegree : (atParameter t p).natDegree ≤ p.coeffs.length - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_atParameter]
    have hnLength : p.coeffs.length ≤ n := by omega
    rw [coeff, List.getD_eq_default p.coeffs.reverse 0]
    · exact DensePolynomial.eval_zero t
    · simpa using hnLength
  omega

/-- Expansion over every displayed outer coefficient slot, including
representation-only leading zeros. -/
theorem eval_eq_sum_range (p : DenseBivariate K) (x t : K) :
    eval p x t =
      ∑ j ∈ Finset.range p.coeffs.length, (p.coeff j).eval t * x ^ j := by
  by_cases hp : p.coeffs = []
  · rcases p with ⟨coeffs⟩
    simp only at hp
    subst coeffs
    simp [eval, coeff]
  · rw [← eval_atParameter]
    rw [Polynomial.eval_eq_sum_range'
      (natDegree_atParameter_lt_length_of_coeffs_ne_nil p t hp)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_atParameter]

private theorem eval_dividedDifferenceFold_first
    (x t : K) (coeffs : List K) (state : DenseBivariate K × DenseBivariate K) :
    eval (coeffs.foldl dividedDifferenceStep state).1 x t =
      coeffs.foldl (fun value a ↦ value * x + a) (eval state.1 x t) := by
  induction coeffs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [dividedDifferenceStep]

private theorem dividedDifferenceFold_invariant (x t : K) :
    ∀ (coeffs : List K) (state : DenseBivariate K × DenseBivariate K),
      t * eval state.2 x t = eval state.1 (x + t) t - eval state.1 x t →
      t * eval (coeffs.foldl dividedDifferenceStep state).2 x t =
        eval (coeffs.foldl dividedDifferenceStep state).1 (x + t) t -
          eval (coeffs.foldl dividedDifferenceStep state).1 x t
  | [], _, h => h
  | a :: as, state, h => by
      simp only [List.foldl_cons]
      apply dividedDifferenceFold_invariant x t as (dividedDifferenceStep state a)
      simp only [dividedDifferenceStep, eval_add, eval_mul, eval_outerX,
        eval_innerX, eval_constant]
      calc
        t * (eval state.2 x t * (x + t) + eval state.1 x t) =
            (t * eval state.2 x t) * (x + t) +
              t * eval state.1 x t := by ring
        _ = (eval state.1 (x + t) t - eval state.1 x t) * (x + t) +
              t * eval state.1 x t := by rw [h]
        _ = eval state.1 (x + t) t * (x + t) + a -
              (eval state.1 x t * x + a) := by ring

private theorem eval_coeffList_horner (p : Polynomial K) (x : K) :
    p.coeffList.foldl (fun value a ↦ value * x + a) 0 = p.eval x := by
  have h := DensePolynomial.eval_toPolynomial
    (⟨p.coeffList⟩ : DensePolynomial K) x
  rw [show (⟨p.coeffList⟩ : DensePolynomial K).toPolynomial = p from
    polynomialOfHighCoeffs_coeffList p] at h
  exact h.symm

@[simp] theorem eval_lift (p : Polynomial K) (x t : K) :
    eval (lift p) x t = p.eval x := by
  rw [eval, lift, List.foldl_map]
  simp only [DensePolynomial.eval_constant]
  exact eval_coeffList_horner p x

theorem atParameter_lift (p : Polynomial K) (t : K) :
    atParameter t (lift p) = p := by
  rw [atParameter, lift, List.map_map]
  simpa [Function.comp_def] using polynomialOfHighCoeffs_coeffList p

/-- Exact finite divided-difference identity for the executable Horner
program. -/
theorem eval_dividedDifference_identity (p : Polynomial K) (x t : K) :
    t * eval (dividedDifference p) x t = p.eval (x + t) - p.eval x := by
  let state := p.coeffList.foldl dividedDifferenceStep (zero, zero)
  have hinvariant := dividedDifferenceFold_invariant x t p.coeffList (zero, zero)
    (by simp)
  have hfirstShift := eval_dividedDifferenceFold_first
    (x + t) t p.coeffList (zero, zero)
  have hfirst := eval_dividedDifferenceFold_first x t p.coeffList (zero, zero)
  rw [eval_zero] at hfirstShift hfirst
  simpa only [dividedDifference, state, hfirstShift, hfirst,
    eval_coeffList_horner] using hinvariant

private theorem atParameter_eq_foldl_horner (t : K) (p : DenseBivariate K) :
    atParameter t p = p.coeffs.foldl
      (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) 0 := by
  change (⟨p.coeffs.map (·.eval t)⟩ : DensePolynomial K).toPolynomial = _
  rw [DensePolynomial.toPolynomial_eq_foldl_horner, List.foldl_map]

omit [DecidableEq K] in
private theorem foldl_replicate_zero_outer (t : K) (n : ℕ)
    (acc : Polynomial K) :
    (List.replicate n (0 : DensePolynomial K)).foldl
        (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) acc =
      acc * Polynomial.X ^ n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, DensePolynomial.eval_zero,
        map_zero, add_zero, ih, pow_succ]
      ring

private theorem atParameter_shiftOuter (t : K) (p : DenseBivariate K) :
    atParameter t (shiftOuter p) = atParameter t p * Polynomial.X := by
  rw [shiftOuter]
  split
  · rename_i hp
    have hempty : p.coeffs = [] := List.isEmpty_iff.mp hp
    simp [atParameter_eq_foldl_horner, zero, hempty]
  · rw [atParameter_eq_foldl_horner, atParameter_eq_foldl_horner,
      List.foldl_append]
    simp

private theorem foldl_zipWith_add_outer (t : K) :
    ∀ (as bs : List (DensePolynomial K)) (accA accB : Polynomial K),
      as.length = bs.length →
      (List.zipWith (· + ·) as bs).foldl
          (fun value a => value * Polynomial.X + Polynomial.C (a.eval t))
          (accA + accB) =
        as.foldl
            (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) accA +
          bs.foldl
            (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) accB
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, accA, accB, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.zipWith_cons_cons, List.foldl_cons,
        DensePolynomial.eval_add]
      rw [show (accA + accB) * Polynomial.X +
          Polynomial.C (a.eval t + b.eval t) =
          (accA * Polynomial.X + Polynomial.C (a.eval t)) +
            (accB * Polynomial.X + Polynomial.C (b.eval t)) by
        simp [map_add]; ring]
      exact foldl_zipWith_add_outer t as bs
        (accA * Polynomial.X + Polynomial.C (a.eval t))
        (accB * Polynomial.X + Polynomial.C (b.eval t)) h

private theorem atParameter_add (t : K) (p q : DenseBivariate K) :
    atParameter t (add p q) = atParameter t p + atParameter t q := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := le_max_left _ _
  have hq : q.coeffs.length ≤ n := le_max_right _ _
  have hps : ps.length = n := by
    simp [ps, padLeft, Nat.sub_add_cancel hp]
  have hqs : qs.length = n := by
    simp [qs, padLeft, Nat.sub_add_cancel hq]
  rw [atParameter_eq_foldl_horner, atParameter_eq_foldl_horner,
    atParameter_eq_foldl_horner]
  change (List.zipWith (· + ·) ps qs).foldl
      (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) 0 = _
  have hadd := foldl_zipWith_add_outer t ps qs 0 0 (hps.trans hqs.symm)
  simp only [zero_add] at hadd
  rw [hadd]
  dsimp only [ps, qs, padLeft]
  rw [List.foldl_append, List.foldl_append,
    foldl_replicate_zero_outer, foldl_replicate_zero_outer]
  simp

private theorem foldl_map_scaleInner_outer (t : K) (c : DensePolynomial K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : Polynomial K),
      (coeffs.map (c * ·)).foldl
          (fun value a => value * Polynomial.X + Polynomial.C (a.eval t))
          (Polynomial.C (c.eval t) * acc) =
        Polynomial.C (c.eval t) * coeffs.foldl
          (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons, DensePolynomial.eval_mul]
      rw [show Polynomial.C (c.eval t) * acc * Polynomial.X +
          Polynomial.C (c.eval t * a.eval t) =
          Polynomial.C (c.eval t) *
            (acc * Polynomial.X + Polynomial.C (a.eval t)) by
        simp [map_mul]; ring]
      exact foldl_map_scaleInner_outer t c as
        (acc * Polynomial.X + Polynomial.C (a.eval t))

private theorem atParameter_scaleInner
    (t : K) (c : DensePolynomial K) (p : DenseBivariate K) :
    atParameter t (scaleInner c p) =
      Polynomial.C (c.eval t) * atParameter t p := by
  rw [atParameter_eq_foldl_horner, atParameter_eq_foldl_horner]
  change (p.coeffs.map (c * ·)).foldl
      (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) 0 = _
  simpa only [mul_zero] using foldl_map_scaleInner_outer t c p.coeffs 0

private theorem atParameter_mulFold (t : K) (q : DenseBivariate K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : DenseBivariate K),
      atParameter t (coeffs.foldl
          (fun value a => add (shiftOuter value) (scaleInner a q)) acc) =
        coeffs.foldl
          (fun value a => value * Polynomial.X +
            Polynomial.C (a.eval t) * atParameter t q)
          (atParameter t acc)
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.foldl_cons]
      rw [atParameter_mulFold t q as, atParameter_add,
        atParameter_shiftOuter, atParameter_scaleInner]

omit [DecidableEq K] in
private theorem foldl_scaled_horner_outer (t : K) (q : Polynomial K) :
    ∀ (coeffs : List (DensePolynomial K)) (acc : Polynomial K),
      coeffs.foldl
          (fun value a => value * Polynomial.X + Polynomial.C (a.eval t) * q)
          (acc * q) =
        coeffs.foldl
          (fun value a => value * Polynomial.X + Polynomial.C (a.eval t)) acc * q
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.foldl_cons]
      rw [show acc * q * Polynomial.X + Polynomial.C (a.eval t) * q =
          (acc * Polynomial.X + Polynomial.C (a.eval t)) * q by ring]
      exact foldl_scaled_horner_outer t q as
        (acc * Polynomial.X + Polynomial.C (a.eval t))

private theorem atParameter_mul (t : K) (p q : DenseBivariate K) :
    atParameter t (mul p q) = atParameter t p * atParameter t q := by
  rw [mul, atParameter_mulFold]
  change p.coeffs.foldl
      (fun value a => value * Polynomial.X +
        Polynomial.C (a.eval t) * atParameter t q) 0 = _
  have hp := atParameter_eq_foldl_horner t p
  rw [hp]
  simpa only [zero_mul] using
    foldl_scaled_horner_outer t (atParameter t q) p.coeffs 0

private theorem atParameter_zero (t : K) :
    atParameter t (zero : DenseBivariate K) = 0 := by
  rfl

private theorem atParameter_constant (t a : K) :
    atParameter t (constant a) = Polynomial.C a := by
  simp [atParameter_eq_foldl_horner, constant]

private theorem atParameter_outerX (t : K) :
    atParameter t (outerX : DenseBivariate K) = Polynomial.X := by
  simp [atParameter_eq_foldl_horner, outerX]

private theorem atParameter_innerX (t : K) :
    atParameter t (innerX : DenseBivariate K) = Polynomial.C t := by
  simp [atParameter_eq_foldl_horner, innerX, DensePolynomial.eval,
    DensePolynomial.evalCoeffs]

private theorem dividedDifferenceFold_derivativeInvariant :
    ∀ (coeffs : List K) (state : DenseBivariate K × DenseBivariate K)
      (q : Polynomial K),
      atParameter 0 state.1 = q →
      atParameter 0 state.2 = q.derivative →
      let finalState := coeffs.foldl dividedDifferenceStep state
      let finalPolynomial := coeffs.foldl
        (fun acc a ↦ acc * Polynomial.X + Polynomial.C a) q
      atParameter 0 finalState.2 = finalPolynomial.derivative
  | [], _, _, _, hderivative => hderivative
  | a :: as, state, q, hvalue, hderivative => by
      simp only [List.foldl_cons]
      apply dividedDifferenceFold_derivativeInvariant as
        (dividedDifferenceStep state a) (q * Polynomial.X + Polynomial.C a)
      · simp only [dividedDifferenceStep, atParameter_add,
          atParameter_mul, atParameter_outerX,
          atParameter_constant]
        rw [hvalue]
      · simp only [dividedDifferenceStep, atParameter_add,
          atParameter_mul, atParameter_outerX,
          atParameter_innerX, hvalue, hderivative,
          Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_X, Polynomial.derivative_C,
          map_zero, add_zero]
        ring

/-- At parameter zero, the executable divided difference specializes exactly
to the formal derivative. -/
theorem atParameter_zero_dividedDifference (p : Polynomial K) :
    atParameter 0 (dividedDifference p) = p.derivative := by
  have h := dividedDifferenceFold_derivativeInvariant p.coeffList
    (zero, zero) 0 (atParameter_zero 0)
      (by rw [atParameter_zero, Polynomial.derivative_zero])
  rw [show p.coeffList.foldl
      (fun acc a ↦ acc * Polynomial.X + Polynomial.C a) 0 = p from by
        have hround := polynomialOfHighCoeffs_coeffList p
        change (⟨p.coeffList⟩ : DensePolynomial K).toPolynomial = p at hround
        exact (DensePolynomial.toPolynomial_eq_foldl_horner
          (⟨p.coeffList⟩ : DensePolynomial K)).symm.trans hround] at h
  exact h

private theorem dividedDifferenceFold_polynomialInvariant (t : K) :
    ∀ (coeffs : List K) (state : DenseBivariate K × DenseBivariate K)
      (q : Polynomial K),
      atParameter t state.1 = q →
      Polynomial.C t * atParameter t state.2 =
        q.comp (Polynomial.X + Polynomial.C t) - q →
      let finalState := coeffs.foldl dividedDifferenceStep state
      let finalPolynomial := coeffs.foldl
        (fun acc a ↦ acc * Polynomial.X + Polynomial.C a) q
      Polynomial.C t * atParameter t finalState.2 =
        finalPolynomial.comp (Polynomial.X + Polynomial.C t) - finalPolynomial
  | [], _, _, _, hdifference => hdifference
  | a :: as, state, q, hvalue, hdifference => by
      simp only [List.foldl_cons]
      apply dividedDifferenceFold_polynomialInvariant t as
        (dividedDifferenceStep state a) (q * Polynomial.X + Polynomial.C a)
      · simp only [dividedDifferenceStep, atParameter_add,
          atParameter_mul, atParameter_outerX, atParameter_constant]
        rw [hvalue]
      · simp only [dividedDifferenceStep, atParameter_add,
          atParameter_mul, atParameter_outerX, atParameter_innerX,
          hvalue, Polynomial.add_comp, Polynomial.mul_comp,
          Polynomial.X_comp, Polynomial.C_comp]
        calc
          Polynomial.C t *
              (atParameter t state.2 * (Polynomial.X + Polynomial.C t) + q) =
              (Polynomial.C t * atParameter t state.2) *
                  (Polynomial.X + Polynomial.C t) + Polynomial.C t * q := by ring
          _ = (q.comp (Polynomial.X + Polynomial.C t) - q) *
                  (Polynomial.X + Polynomial.C t) + Polynomial.C t * q := by
            rw [hdifference]
          _ = q.comp (Polynomial.X + Polynomial.C t) *
                (Polynomial.X + Polynomial.C t) + Polynomial.C a -
                  (q * Polynomial.X + Polynomial.C a) := by ring

/-- The finite divided-difference program satisfies its exact polynomial
identity after specialization; the proof is a Horner-list induction and does
not use equality at every field element. -/
theorem atParameter_dividedDifference_identity (p : Polynomial K) (t : K) :
    Polynomial.C t * atParameter t (dividedDifference p) =
      p.comp (Polynomial.X + Polynomial.C t) - p := by
  have h := dividedDifferenceFold_polynomialInvariant t p.coeffList
    (zero, zero) 0 (atParameter_zero t) (by simp [atParameter_zero])
  have hround : p.coeffList.foldl
      (fun acc a ↦ acc * Polynomial.X + Polynomial.C a) 0 = p := by
    have hsparse := polynomialOfHighCoeffs_coeffList p
    change (⟨p.coeffList⟩ : DensePolynomial K).toPolynomial = p at hsparse
    exact (DensePolynomial.toPolynomial_eq_foldl_horner
      (⟨p.coeffList⟩ : DensePolynomial K)).symm.trans hsparse
  simpa only [dividedDifference, hround] using h

/-- The Sylvester matrix, with dense inner-polynomial entries. -/
def sylvester (f g : DenseBivariate K) (m n : ℕ) :
    Matrix (Fin (m + n)) (Fin (m + n)) (DensePolynomial K) :=
  Matrix.of fun i j ↦ j.addCases
    (fun j₁ ↦
      if (j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + n then
        coeff g ((i : ℕ) - j₁)
      else 0)
    (fun j₁ ↦
      if (j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + m then
        coeff f ((i : ℕ) - j₁)
      else 0)

def product (coeffs : List (DensePolynomial K)) : DensePolynomial K :=
  coeffs.foldl (· * ·) (DensePolynomial.constant 1)

/-- Delete row `i` and the first column from a displayed square matrix. -/
def firstColumnMinor {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (DensePolynomial K))
    (i : Fin (n + 1)) : Matrix (Fin n) (Fin n) (DensePolynomial K) :=
  fun row column ↦ M (i.succAbove row) column.succ

/-- Executable Laplace determinant.  Recursion is on the displayed dimension
and every cofactor sum is a finite `List.ofFn` fold. -/
def determinant : (n : ℕ) →
    Matrix (Fin n) (Fin n) (DensePolynomial K) → DensePolynomial K
  | 0, _ => DensePolynomial.constant 1
  | n + 1, M =>
      (List.ofFn fun i : Fin (n + 1) ↦
        DensePolynomial.scale ((-1 : K) ^ (i : ℕ))
          (M i 0 * determinant n (firstColumnMinor M i))).foldl (· + ·) 0

def resultant (f g : DenseBivariate K) (m n : ℕ) : DensePolynomial K :=
  determinant (m + n) (sylvester f g m n)

private theorem eval_foldl_add (t : K) (coeffs : List (DensePolynomial K))
    (acc : DensePolynomial K) :
    (coeffs.foldl (· + ·) acc).eval t =
      (coeffs.map (·.eval t)).foldl (· + ·) (acc.eval t) := by
  induction coeffs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, DensePolynomial.eval_add]

omit [DecidableEq K] in
private theorem foldl_add_eq_sum (coeffs : List K) :
    coeffs.foldl (· + ·) 0 = coeffs.sum := by
  calc
    coeffs.foldl (· + ·) 0 = coeffs.foldr (· + ·) 0 :=
      List.foldr_eq_foldl.symm
    _ = coeffs.sum := List.sum_eq_foldr.symm

/-- Evaluation of the executable dense determinant is the ordinary scalar
determinant of the entrywise evaluations. -/
theorem eval_determinant (t : K) : (n : ℕ) →
    (M : Matrix (Fin n) (Fin n) (DensePolynomial K)) →
    (determinant n M).eval t = Matrix.det (fun i j ↦ (M i j).eval t)
  | 0, M => by simp [determinant]
  | n + 1, M => by
      rw [determinant, eval_foldl_add, DensePolynomial.eval_zero,
        foldl_add_eq_sum, List.map_ofFn, List.sum_ofFn,
        Matrix.det_succ_column_zero]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply, DensePolynomial.eval_scale,
        DensePolynomial.eval_mul]
      rw [eval_determinant t n (firstColumnMinor M i)]
      rw [mul_assoc]
      congr 2

/-- The executable dense resultant specializes to the determinant of the
entrywise specialized Sylvester matrix. -/
theorem eval_resultant (f g : DenseBivariate K) (m n : ℕ) (t : K) :
    (resultant f g m n).eval t =
      Matrix.det (fun i j ↦ (sylvester f g m n i j).eval t) :=
  eval_determinant t (m + n) (sylvester f g m n)

theorem evaluated_sylvester (f g : DenseBivariate K) (m n : ℕ) (t : K) :
    (fun i j ↦ (sylvester f g m n i j).eval t) =
      Polynomial.sylvester (atParameter t f) (atParameter t g) m n := by
  ext i j
  induction j using Fin.addCases <;>
    simp only [sylvester, Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right, coeff_atParameter] <;>
    split <;> simp_all

/-- Sparse univariate specification of the executable resultant after any
coefficient specialization. -/
theorem eval_toPolynomial_resultant
    (f g : DenseBivariate K) (m n : ℕ) (t : K) :
    Polynomial.eval t (resultant f g m n).toPolynomial =
      (atParameter t f).resultant (atParameter t g) m n := by
  rw [DensePolynomial.eval_toPolynomial, eval_resultant, Polynomial.resultant,
    evaluated_sylvester]

end DenseBivariate

end FTA.ExecutableBivariate
