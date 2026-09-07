import FTA.ComputablePolynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.List.ToFinsupp
import Mathlib.Tactic.FieldSimp

/-!
# Semantic bridge for executable dense polynomials

Algorithms use the computable high-to-low coefficient representation from
`FTA.ComputablePolynomial`.  This module maps that representation to Mathlib's
theorem-oriented `Polynomial` type and proves exact agreement of evaluation.
The map itself is used only in specifications; executable searches continue to
run on dense coefficient lists.
-/

namespace FTA.ComputablePolynomial.DensePolynomial

open Polynomial

variable {K : Type*} [Field K]

/-- Computable conversion into Mathlib's sparse polynomial model.  Constructing
the underlying finitely supported coefficient function directly avoids the
theorem-oriented sparse arithmetic instances. -/
def toPolynomial (p : DensePolynomial K) [DecidableEq K] : Polynomial K :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff p.coeffs.reverse.toFinsupp)

private theorem coeff_foldl_horner (cs : List K) (n : ℕ) :
    (cs.foldl (fun acc a => acc * X + C a) 0).coeff n =
      cs.reverse.getD n 0 := by
  induction cs using List.reverseRecOn generalizing n with
  | nil => simp
  | append_singleton cs a ih =>
      cases n with
      | zero => simp [List.foldl_append]
      | succ n => simp [List.foldl_append, ih]

/-- The sparse specification exposes exactly the reversed dense coefficient
list, including representation-only leading zeros. -/
theorem coeff_toPolynomial [DecidableEq K]
    (p : DensePolynomial K) (n : ℕ) :
    p.toPolynomial.coeff n = p.coeffs.reverse.getD n 0 := by
  rfl

/-- The computable coefficient construction agrees extensionally with the
usual Horner expression used in sparse-polynomial specifications. -/
theorem toPolynomial_eq_foldl_horner [DecidableEq K]
    (p : DensePolynomial K) :
    p.toPolynomial = p.coeffs.foldl (fun acc a => acc * X + C a) 0 := by
  apply Polynomial.ext
  intro n
  rw [coeff_toPolynomial]
  exact (coeff_foldl_horner p.coeffs n).symm

private theorem foldl_horner_dropWhile_zero [DecidableEq K] (cs : List K) :
    (cs.dropWhile (· = 0)).foldl (fun acc a => acc * X + C a) 0 =
      cs.foldl (fun acc a => acc * X + C a) 0 := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a = 0
      · subst a
        rw [List.dropWhile_cons_of_pos (by simp), List.foldl_cons]
        simp only [map_zero, add_zero]
        exact ih
      · rw [List.dropWhile_cons_of_neg (by simpa using ha)]

/-- Removing representation-only leading zeros leaves the specification
polynomial unchanged. -/
theorem toPolynomial_normalize [DecidableEq K] (p : DensePolynomial K) :
    p.normalize.toPolynomial = p.toPolynomial := by
  rw [toPolynomial_eq_foldl_horner, toPolynomial_eq_foldl_horner]
  exact foldl_horner_dropWhile_zero p.coeffs

private theorem eval_foldl_toPolynomial (x : K) (cs : List K) (p : Polynomial K) :
    Polynomial.eval x (cs.foldl (fun acc a => acc * X + C a) p) =
      cs.foldl (fun acc a => acc * x + a) (Polynomial.eval x p) := by
  induction cs generalizing p with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp

/-- The specification polynomial and executable Horner evaluator agree at
every field element. -/
theorem eval_toPolynomial [DecidableEq K]
    (p : DensePolynomial K) (x : K) :
    Polynomial.eval x p.toPolynomial = p.eval x := by
  rw [toPolynomial_eq_foldl_horner, eval_foldl_toPolynomial]
  simp only [Polynomial.eval_zero]
  rfl

private theorem rationalPolynomial_eq_zero_of_consecutive_evals
    (p : Polynomial ℚ) (a : ℚ) (sampleCount : ℕ)
    (degree_lt : p.natDegree < sampleCount)
    (eval_zero : ∀ i : ℕ, i < sampleCount → p.eval (a + i) = 0) :
    p = 0 := by
  induction sampleCount generalizing p a with
  | zero => omega
  | succ sampleCount ih =>
      have root_at_a : p.IsRoot a := by
        rw [Polynomial.IsRoot]
        simpa using eval_zero 0 (Nat.zero_lt_succ sampleCount)
      obtain ⟨q, hp⟩ := Polynomial.dvd_iff_isRoot.mpr root_at_a
      rw [hp]
      by_cases q_zero : q = 0
      · simp [q_zero]
      have quotient_degree_lt : q.natDegree < sampleCount := by
        rw [hp, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) q_zero,
          Polynomial.natDegree_X_sub_C] at degree_lt
        omega
      have quotient_eval_zero : ∀ i : ℕ, i < sampleCount →
          q.eval ((a + 1) + i) = 0 := by
        intro i i_lt
        have product_zero := eval_zero (i + 1) (Nat.succ_lt_succ i_lt)
        rw [hp, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C] at product_zero
        have factor_ne_zero : a + (i + 1 : ℕ) - a ≠ (0 : ℚ) := by
          rw [show a + (i + 1 : ℕ) - a = ((i + 1 : ℕ) : ℚ) by ring]
          exact_mod_cast Nat.succ_ne_zero i
        have q_zero_at_point := (mul_eq_zero.mp product_zero).resolve_left factor_ne_zero
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
          using q_zero_at_point
      rw [ih q (a + 1) quotient_degree_lt quotient_eval_zero]
      simp

/-- A rational polynomial that vanishes on more explicitly listed, distinct
points than its degree is zero.  The proof removes the named points one at a
time with the factor theorem; it does not construct or count a global root
collection. -/
theorem polynomial_eq_zero_of_eval_zero_on_list [DecidableEq K]
    (p : Polynomial K) (xs : List K) (nodup : xs.Nodup)
    (degree_lt : p.natDegree < xs.length)
    (eval_zero : ∀ x ∈ xs, p.eval x = 0) : p = 0 := by
  induction xs generalizing p with
  | nil => simp at degree_lt
  | cons a xs ih =>
      have root_at_a : p.IsRoot a := by
        rw [Polynomial.IsRoot]
        exact eval_zero a (by simp)
      obtain ⟨q, hp⟩ := Polynomial.dvd_iff_isRoot.mpr root_at_a
      rw [hp]
      by_cases q_zero : q = 0
      · simp [q_zero]
      have quotient_degree_lt : q.natDegree < xs.length := by
        rw [hp, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) q_zero,
          Polynomial.natDegree_X_sub_C] at degree_lt
        simp only [List.length_cons] at degree_lt
        omega
      have quotient_eval_zero : ∀ x ∈ xs, q.eval x = 0 := by
        intro x hx
        have product_zero := eval_zero x (by simp [hx])
        rw [hp, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C] at product_zero
        have factor_ne_zero : x - a ≠ 0 := sub_ne_zero.mpr <| by
          intro x_eq_a
          exact (List.nodup_cons.mp nodup).1 (x_eq_a ▸ hx)
        exact (mul_eq_zero.mp product_zero).resolve_left factor_ne_zero
      rw [ih q (List.nodup_cons.mp nodup).2 quotient_degree_lt quotient_eval_zero]
      simp

/-- Finite interpolation over `ℚ`, proved here by repeated factorisation at
the explicitly indexed sample points.  It does not use `Polynomial.roots`, a
root multiset, cardinality of the coefficient field, or existence of roots. -/
theorem rationalPolynomial_eq_of_eval_eq_on_fin (p q : Polynomial ℚ)
    (h : ∀ i : Fin (max p.natDegree q.natDegree + 1),
      p.eval ((i : ℕ) : ℚ) = q.eval ((i : ℕ) : ℚ)) :
    p = q := by
  rw [← sub_eq_zero]
  apply rationalPolynomial_eq_zero_of_consecutive_evals
      (p - q) 0 (max p.natDegree q.natDegree + 1)
  · exact (Polynomial.natDegree_sub_le p q).trans_lt (Nat.lt_succ_self _)
  · intro i i_lt
    rw [Polynomial.eval_sub]
    simpa only [zero_add] using sub_eq_zero.mpr (h ⟨i, i_lt⟩)

/-- Zero-specialized finite interpolation, with a sample index whose size does
not depend on a second polynomial expression. -/
theorem rationalPolynomial_eq_zero_of_eval_eq_on_fin (p : Polynomial ℚ)
    (h : ∀ i : Fin (p.natDegree + 1), p.eval ((i : ℕ) : ℚ) = 0) :
    p = 0 := by
  apply rationalPolynomial_eq_zero_of_consecutive_evals p 0 (p.natDegree + 1)
  · omega
  · intro i i_lt
    simpa only [zero_add] using h ⟨i, i_lt⟩

private theorem foldl_horner_natDegree (cs : List K) (p : Polynomial K) (hp : p ≠ 0) :
    (cs.foldl (fun acc a => acc * X + C a) p).natDegree =
      p.natDegree + cs.length := by
  induction cs generalizing p with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldl_cons, List.length_cons]
      let q := p * X + C a
      have hqDegree : q.natDegree = p.natDegree + 1 := by
        dsimp only [q]
        rw [Polynomial.natDegree_add_C, Polynomial.natDegree_mul_X hp]
      have hq : q ≠ 0 := by
        intro hzero
        rw [hzero, Polynomial.natDegree_zero] at hqDegree
        omega
      rw [ih q hq, hqDegree]
      omega

private theorem foldl_horner_leadingCoeff (cs : List K) (p : Polynomial K) (hp : p ≠ 0) :
    (cs.foldl (fun acc a => acc * X + C a) p).leadingCoeff = p.leadingCoeff := by
  induction cs generalizing p with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      let q := p * X + C a
      have hpX : p * X ≠ 0 := mul_ne_zero hp Polynomial.X_ne_zero
      have hpXPos : (0 : WithBot ℕ) < (p * X).degree := by
        rw [Polynomial.degree_eq_natDegree hpX, Polynomial.natDegree_mul_X hp]
        exact_mod_cast Nat.succ_pos p.natDegree
      have hconstant : (C a).degree < (p * X).degree :=
        Polynomial.degree_C_le.trans_lt hpXPos
      have hqLeading : q.leadingCoeff = p.leadingCoeff := by
        dsimp only [q]
        rw [Polynomial.leadingCoeff_add_of_degree_lt' hconstant,
          Polynomial.leadingCoeff_mul_X]
      have hq : q ≠ 0 := by
        intro hzero
        have := congrArg Polynomial.leadingCoeff hzero
        rw [Polynomial.leadingCoeff_zero, hqLeading] at this
        exact Polynomial.leadingCoeff_ne_zero.mpr hp this
      exact (ih q hq).trans hqLeading

/-- A nonzero dense polynomial and its sparse specification have exactly the
same natural degree. -/
theorem natDegree_toPolynomial [DecidableEq K] {p : DensePolynomial K}
    (hp : p.isZero = false) :
    p.toPolynomial.natDegree = p.natDegree := by
  have hpne : p.normalize.coeffs ≠ [] := by simpa [isZero] using hp
  cases hcoeffs : p.normalize.coeffs with
  | nil => exact (hpne hcoeffs).elim
  | cons a as =>
      have hdrop : p.coeffs.dropWhile (· = 0) = a :: as := hcoeffs
      have ha : a ≠ 0 := by
        have hlc := leadingCoeff_ne_zero hp
        rw [leadingCoeff, normalize, hdrop] at hlc
        simpa using hlc
      rw [← toPolynomial_normalize p]
      rw [toPolynomial_eq_foldl_horner]
      rw [hcoeffs, List.foldl_cons]
      simp only [zero_mul, zero_add]
      rw [foldl_horner_natDegree as (C a) (Polynomial.C_ne_zero.mpr ha)]
      simp only [Polynomial.natDegree_C, zero_add]
      dsimp [DensePolynomial.natDegree, degreeCount]
      rw [hdrop]
      simp

/-- The specification polynomial also preserves the normalized leading
coefficient. -/
theorem leadingCoeff_toPolynomial [DecidableEq K] {p : DensePolynomial K}
    (hp : p.isZero = false) :
    p.toPolynomial.leadingCoeff = p.leadingCoeff := by
  have hpne : p.normalize.coeffs ≠ [] := by simpa [isZero] using hp
  cases hcoeffs : p.normalize.coeffs with
  | nil => exact (hpne hcoeffs).elim
  | cons a as =>
      have hdrop : p.coeffs.dropWhile (· = 0) = a :: as := hcoeffs
      have ha : a ≠ 0 := by
        have hlc := leadingCoeff_ne_zero hp
        rw [leadingCoeff, normalize, hdrop] at hlc
        simpa using hlc
      rw [← toPolynomial_normalize p]
      rw [toPolynomial_eq_foldl_horner]
      rw [hcoeffs, List.foldl_cons]
      simp only [zero_mul, zero_add]
      rw [foldl_horner_leadingCoeff as (C a) (Polynomial.C_ne_zero.mpr ha),
        Polynomial.leadingCoeff_C]
      rw [leadingCoeff, normalize, hdrop]
      rfl

theorem toPolynomial_ne_zero_of_isZero_false [DecidableEq K]
    {p : DensePolynomial K} (hp : p.isZero = false) : p.toPolynomial ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [leadingCoeff_toPolynomial hp]
  exact leadingCoeff_ne_zero hp

theorem toPolynomial_eq_zero_iff_isZero [DecidableEq K] (p : DensePolynomial K) :
    p.toPolynomial = 0 ↔ p.isZero = true := by
  constructor
  · intro hpoly
    cases hp : p.isZero with
    | false => exact (toPolynomial_ne_zero_of_isZero_false hp hpoly).elim
    | true => rfl
  · intro hp
    have hempty : p.normalize.coeffs = [] := by simpa [isZero] using hp
    rw [← toPolynomial_normalize p]
    rw [toPolynomial_eq_foldl_horner, hempty]
    rfl

/-- Sparse equality determines the canonical normalized dense representation.
This lets algebraic polynomial identities be transported back to exact states
of the executable long-division program. -/
theorem normalize_eq_normalize_of_toPolynomial_eq [DecidableEq K]
    {p q : DensePolynomial K} (hpoly : p.toPolynomial = q.toPolynomial) :
    p.normalize = q.normalize := by
  by_cases hp : p.isZero = true
  · have hpPoly : p.toPolynomial = 0 := (toPolynomial_eq_zero_iff_isZero p).2 hp
    have hqPoly : q.toPolynomial = 0 := hpoly.symm.trans hpPoly
    have hq : q.isZero = true := (toPolynomial_eq_zero_iff_isZero q).1 hqPoly
    have hpEmpty : p.normalize.coeffs = [] := by simpa [isZero] using hp
    have hqEmpty : q.normalize.coeffs = [] := by simpa [isZero] using hq
    apply ext
    exact hpEmpty.trans hqEmpty.symm
  · have hpFalse : p.isZero = false := by simpa using hp
    have hqFalse : q.isZero = false := by
      by_contra hq
      have hqTrue : q.isZero = true := by simpa using hq
      have hqPoly : q.toPolynomial = 0 := (toPolynomial_eq_zero_iff_isZero q).2 hqTrue
      exact toPolynomial_ne_zero_of_isZero_false hpFalse (hpoly.trans hqPoly)
    have hdegree : p.natDegree = q.natDegree := by
      rw [← natDegree_toPolynomial hpFalse, ← natDegree_toPolynomial hqFalse,
        hpoly]
    have hlength : p.normalize.coeffs.length = q.normalize.coeffs.length := by
      change p.degreeCount = q.degreeCount
      have hpCount := natDegree_add_one_eq_degreeCount hpFalse
      have hqCount := natDegree_add_one_eq_degreeCount hqFalse
      omega
    apply ext
    apply List.reverse_injective
    apply List.ext_getElem
    · simpa using hlength
    · intro n hpBound hqBound
      rw [← List.getD_eq_getElem _ 0 hpBound,
        ← List.getD_eq_getElem _ 0 hqBound,
        ← coeff_toPolynomial p.normalize, ← coeff_toPolynomial q.normalize,
        toPolynomial_normalize, toPolynomial_normalize, hpoly]

@[simp] theorem toPolynomial_zero [DecidableEq K] :
    (0 : DensePolynomial K).toPolynomial = 0 := by
  apply Polynomial.ext
  intro n
  rw [coeff_toPolynomial, Polynomial.coeff_zero]
  change ([] : List K).reverse.getD n 0 = 0
  simp

@[simp] theorem toPolynomial_constant [DecidableEq K] (a : K) :
    (constant a).toPolynomial = C a := by
  apply Polynomial.ext
  intro n
  cases n <;> simp [coeff_toPolynomial, constant]

private theorem foldl_horner_replicate_zero_append (n : ℕ) (cs : List K) :
    (List.replicate n 0 ++ cs).foldl (fun acc a => acc * X + C a) 0 =
      cs.foldl (fun acc a => acc * X + C a) 0 := by
  rw [List.foldl_append]
  have hzero :
      (List.replicate n 0).foldl
          (fun (acc : Polynomial K) (a : K) => acc * X + C a) 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  rw [hzero]

private theorem foldl_zipWith_add_horner :
    ∀ (as bs : List K) (accA accB : Polynomial K), as.length = bs.length →
      (List.zipWith (· + ·) as bs).foldl
          (fun acc a => acc * X + C a) (accA + accB) =
        as.foldl (fun acc a => acc * X + C a) accA +
          bs.foldl (fun acc b => acc * X + C b) accB
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, accA, accB, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.zipWith_cons_cons, List.foldl_cons]
      rw [show (accA + accB) * X + C (a + b) =
          (accA * X + C a) + (accB * X + C b) by simp [map_add]; ring]
      exact foldl_zipWith_add_horner as bs
        (accA * X + C a) (accB * X + C b) h

theorem toPolynomial_add [DecidableEq K] (p q : DensePolynomial K) :
    (p + q).toPolynomial = p.toPolynomial + q.toPolynomial := by
  let n := max p.coeffs.length q.coeffs.length
  let ps := padLeft (n - p.coeffs.length) p.coeffs
  let qs := padLeft (n - q.coeffs.length) q.coeffs
  have hp : p.coeffs.length ≤ n := le_max_left _ _
  have hq : q.coeffs.length ≤ n := le_max_right _ _
  have hps : ps.length = n := by
    simp [ps, padLeft, Nat.sub_add_cancel hp]
  have hqs : qs.length = n := by
    simp [qs, padLeft, Nat.sub_add_cancel hq]
  change (normalize ⟨List.zipWith (· + ·) ps qs⟩).toPolynomial = _
  rw [toPolynomial_normalize, toPolynomial_eq_foldl_horner,
    toPolynomial_eq_foldl_horner, toPolynomial_eq_foldl_horner]
  change (List.zipWith (· + ·) ps qs).foldl
      (fun acc a => acc * X + C a) 0 = _
  have hadd :
      (List.zipWith (· + ·) ps qs).foldl
          (fun acc a => acc * X + C a) 0 =
        ps.foldl (fun acc a => acc * X + C a) 0 +
          qs.foldl (fun acc a => acc * X + C a) 0 := by
    simpa only [zero_add] using
      foldl_zipWith_add_horner ps qs 0 0 (hps.trans hqs.symm)
  rw [hadd]
  dsimp only [ps, qs, padLeft]
  rw [foldl_horner_replicate_zero_append,
    foldl_horner_replicate_zero_append]

private theorem foldl_map_neg_horner : ∀ (cs : List K) (acc : Polynomial K),
    (cs.map (-·)).foldl (fun value a => value * X + C a) (-acc) =
      -cs.foldl (fun value a => value * X + C a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      rw [show -acc * X + C (-a) = -(acc * X + C a) by simp; ring]
      exact foldl_map_neg_horner as (acc * X + C a)

theorem toPolynomial_neg [DecidableEq K] (p : DensePolynomial K) :
    (-p).toPolynomial = -p.toPolynomial := by
  change (normalize ⟨p.coeffs.map (-·)⟩).toPolynomial = _
  rw [toPolynomial_normalize, toPolynomial_eq_foldl_horner,
    toPolynomial_eq_foldl_horner]
  simpa only [neg_zero] using foldl_map_neg_horner p.coeffs 0

theorem toPolynomial_sub [DecidableEq K] (p q : DensePolynomial K) :
    (p - q).toPolynomial = p.toPolynomial - q.toPolynomial := by
  change (p + -q).toPolynomial = _
  rw [toPolynomial_add, toPolynomial_neg, sub_eq_add_neg]

private theorem foldl_map_scale_horner (c : K) :
    ∀ (cs : List K) (acc : Polynomial K),
      (cs.map (c * ·)).foldl (fun value a => value * X + C a) (C c * acc) =
        C c * cs.foldl (fun value a => value * X + C a) acc
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons]
      rw [show C c * acc * X + C (c * a) =
          C c * (acc * X + C a) by simp [map_mul]; ring]
      exact foldl_map_scale_horner c as (acc * X + C a)

theorem toPolynomial_scale [DecidableEq K] (c : K) (p : DensePolynomial K) :
    (scale c p).toPolynomial = C c * p.toPolynomial := by
  change (normalize ⟨p.coeffs.map (c * ·)⟩).toPolynomial = _
  rw [toPolynomial_normalize, toPolynomial_eq_foldl_horner,
    toPolynomial_eq_foldl_horner]
  simpa only [mul_zero] using foldl_map_scale_horner c p.coeffs 0

private theorem foldl_replicate_zero_horner (n : ℕ) (acc : Polynomial K) :
    (List.replicate n 0).foldl
        (fun (value : Polynomial K) (a : K) => value * X + C a) acc =
      acc * X ^ n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, map_zero, add_zero, ih, pow_succ]
      ring

theorem toPolynomial_shift [DecidableEq K] (n : ℕ) (p : DensePolynomial K) :
    (shift n p).toPolynomial = p.toPolynomial * X ^ n := by
  rw [shift]
  split
  · rename_i hp
    rw [(toPolynomial_eq_zero_iff_isZero p).2 hp]
    simp
  · rw [toPolynomial_eq_foldl_horner, List.foldl_append,
      foldl_replicate_zero_horner, ← toPolynomial_eq_foldl_horner,
      toPolynomial_normalize]

private theorem toPolynomial_foldl_mulPolynomial [DecidableEq K]
    (q : DensePolynomial K) : ∀ (cs : List K) (acc : DensePolynomial K),
      (cs.foldl (fun value a => shift 1 value + scale a q) acc).toPolynomial =
        cs.foldl (fun value a => value * X + C a * q.toPolynomial)
          acc.toPolynomial
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.foldl_cons]
      rw [toPolynomial_foldl_mulPolynomial q as,
        toPolynomial_add, toPolynomial_shift, toPolynomial_scale, pow_one]

private theorem foldl_scaled_horner_polynomial (q : Polynomial K) :
    ∀ (cs : List K) (acc : Polynomial K),
      cs.foldl (fun value a => value * X + C a * q) (acc * q) =
        cs.foldl (fun value a => value * X + C a) acc * q
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.foldl_cons]
      rw [show acc * q * X + C a * q = (acc * X + C a) * q by ring]
      exact foldl_scaled_horner_polynomial q as (acc * X + C a)

theorem toPolynomial_mul [DecidableEq K] (p q : DensePolynomial K) :
    (p * q).toPolynomial = p.toPolynomial * q.toPolynomial := by
  change (mulPolynomial p q).toPolynomial = _
  rw [mulPolynomial, toPolynomial_foldl_mulPolynomial q]
  rw [toPolynomial_zero]
  simpa only [zero_mul, toPolynomial_eq_foldl_horner] using
    foldl_scaled_horner_polynomial q.toPolynomial p.coeffs 0

section Rational

theorem toPolynomial_cancelLead [DecidableEq K] (p q : DensePolynomial K) :
    (cancelLead p q).toPolynomial = p.toPolynomial -
      (C (p.leadingCoeff / q.leadingCoeff) * q.toPolynomial) *
        X ^ (p.natDegree - q.natDegree) := by
  rw [cancelLead, toPolynomial_sub, toPolynomial_shift, toPolynomial_scale]

/-- Negating the dividend negates every exact cancellation state. -/
theorem cancelLead_neg_left (p q : DensePolynomial ℚ) :
    cancelLead (-p) q = -(cancelLead p q) := by
  have hpoly : (cancelLead (-p) q).toPolynomial =
      (-(cancelLead p q)).toPolynomial := by
    rw [toPolynomial_cancelLead (-p) q, toPolynomial_neg (cancelLead p q),
      toPolynomial_cancelLead p q, toPolynomial_neg p, leadingCoeff_neg,
      natDegree_neg]
    simp only [neg_div, map_neg]
    ring
  simpa using normalize_eq_normalize_of_toPolynomial_eq hpoly

/-- At every fuel depth, negating the dividend negates the executable
remainder. -/
theorem divLoop_remainder_neg_left (fuel : ℕ)
    (p q quotientNeg quotient : DensePolynomial ℚ) :
    (divLoop fuel (-p) q quotientNeg).remainder =
      -((divLoop fuel p q quotient).remainder) := by
  induction fuel generalizing p quotientNeg quotient with
  | zero => rfl
  | succ fuel ih =>
      rw [divLoop, divLoop]
      simp only [isZero_neg, natDegree_neg]
      split
      · rfl
      · dsimp only
        rw [cancelLead_neg_left]
        exact ih (cancelLead p q)
          (quotientNeg + leadQuotient (-p) q)
          (quotient + leadQuotient p q)

theorem divMod_remainder_neg_left (p q : DensePolynomial ℚ) :
    (divMod (-p) q).remainder = -((divMod p q).remainder) := by
  have h := divLoop_remainder_neg_left (p.degreeCount + 1) p.normalize q.normalize 0 0
  rw [divMod, divMod, degreeCount_neg, normalize_neg]
  rw [neg_normalize p] at h
  exact h

theorem divMod_remainder_neg_both (p q : DensePolynomial ℚ)
    (hq : q.isZero = false) :
    (divMod (-p) (-q)).remainder = -((divMod p q).remainder) := by
  rw [divMod_remainder_neg_left, divMod_remainder_neg_right p q hq]

theorem toPolynomial_leadQuotient [DecidableEq K] (p q : DensePolynomial K) :
    (leadQuotient p q).toPolynomial =
      C (p.leadingCoeff / q.leadingCoeff) *
        X ^ (p.natDegree - q.natDegree) := by
  change (shift (p.natDegree - q.natDegree)
    (constant (p.leadingCoeff / q.leadingCoeff))).toPolynomial = _
  rw [toPolynomial_shift, toPolynomial_constant]

private theorem divLoop_toPolynomial_equation (fuel : ℕ)
    [DecidableEq K] (p q quotient : DensePolynomial K) :
    let result := divLoop fuel p q quotient
    result.remainder.toPolynomial + q.toPolynomial * result.quotient.toPolynomial =
      p.toPolynomial + q.toPolynomial * quotient.toPolynomial := by
  induction fuel generalizing p quotient with
  | zero => rfl
  | succ fuel ih =>
      rw [divLoop]
      split
      · rfl
      · dsimp only
        rw [ih, toPolynomial_cancelLead, toPolynomial_add,
          toPolynomial_leadQuotient]
        ring

/-- Sparse specification of the executable quotient/remainder equation. -/
theorem divMod_toPolynomial_equation [DecidableEq K]
    (p q : DensePolynomial K) :
    p.toPolynomial = q.toPolynomial * (divMod p q).quotient.toPolynomial +
      (divMod p q).remainder.toPolynomial := by
  have h := divLoop_toPolynomial_equation (p.degreeCount + 1)
    p.normalize q.normalize 0
  simp only [toPolynomial_normalize, toPolynomial_zero, mul_zero, add_zero] at h
  change p.toPolynomial = q.toPolynomial *
    (divLoop (p.degreeCount + 1) p.normalize q.normalize 0).quotient.toPolynomial +
      (divLoop (p.degreeCount + 1) p.normalize q.normalize 0).remainder.toPolynomial
  rw [← h]
  ring

/-- One nonterminal long-division cancellation strictly lowers the
specification-polynomial degree. -/
theorem degree_toPolynomial_cancelLead_lt {p q : DensePolynomial ℚ}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).toPolynomial.degree < p.toPolynomial.degree := by
  let c := p.leadingCoeff / q.leadingCoeff
  let e := p.natDegree - q.natDegree
  let T := (C c * q.toPolynomial) * X ^ e
  have hpP : p.toPolynomial ≠ 0 := toPolynomial_ne_zero_of_isZero_false hp
  have hqP : q.toPolynomial ≠ 0 := toPolynomial_ne_zero_of_isZero_false hq
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
  have hbase : C c * q.toPolynomial ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hqP
  have hT : T ≠ 0 := by
    exact mul_ne_zero hbase (pow_ne_zero _ Polynomial.X_ne_zero)
  have hTnat : T.natDegree = p.natDegree := by
    dsimp only [T, e]
    rw [Polynomial.natDegree_mul_X_pow _ hbase, Polynomial.natDegree_C_mul hc,
      natDegree_toPolynomial hq]
    omega
  have hdegreeEq : p.toPolynomial.degree = T.degree := by
    rw [Polynomial.degree_eq_natDegree hpP, Polynomial.degree_eq_natDegree hT,
      natDegree_toPolynomial hp, hTnat]
  have hleadingEq : p.toPolynomial.leadingCoeff = T.leadingCoeff := by
    dsimp only [T, c]
    rw [Polynomial.leadingCoeff_mul_X_pow, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, leadingCoeff_toPolynomial hq,
      leadingCoeff_toPolynomial hp]
    field_simp [leadingCoeff_ne_zero hq]
  rw [toPolynomial_cancelLead]
  exact Polynomial.degree_sub_lt hdegreeEq hpP hleadingEq

/-- The executable normalized coefficient count strictly decreases at every
nonterminal cancellation step. -/
theorem degreeCount_cancelLead_lt {p q : DensePolynomial ℚ}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).degreeCount < p.degreeCount := by
  by_cases hnext : (cancelLead p q).isZero = true
  · rw [degreeCount_eq_zero_of_isZero hnext]
    exact degreeCount_pos_of_isZero_false hp
  · have hnextFalse : (cancelLead p q).isZero = false := by
      simpa using hnext
    have hdegreePoly := degree_toPolynomial_cancelLead_lt hp hq hdegree
    have hpP : p.toPolynomial ≠ 0 := toPolynomial_ne_zero_of_isZero_false hp
    have hnextP : (cancelLead p q).toPolynomial ≠ 0 :=
      toPolynomial_ne_zero_of_isZero_false hnextFalse
    rw [Polynomial.degree_eq_natDegree hnextP, Polynomial.degree_eq_natDegree hpP,
      natDegree_toPolynomial hnextFalse, natDegree_toPolynomial hp] at hdegreePoly
    have hdegreeNat : (cancelLead p q).natDegree < p.natDegree := by
      exact_mod_cast hdegreePoly
    have hnextCount := natDegree_add_one_eq_degreeCount hnextFalse
    have hpCount := natDegree_add_one_eq_degreeCount hp
    omega

/-- Sufficient fuel carries strict degree descent through the whole executable
division loop.  The returned remainder is zero or has degree below the fixed
nonzero divisor. -/
theorem divLoop_remainder_small (fuel : ℕ) (p q quotient : DensePolynomial ℚ)
    (hq : q.isZero = false) (hfuel : p.degreeCount < fuel) :
    (divLoop fuel p q quotient).remainder.isZero = true ∨
      (divLoop fuel p q quotient).remainder.natDegree < q.natDegree := by
  induction fuel generalizing p quotient with
  | zero => omega
  | succ fuel ih =>
      rw [divLoop]
      split
      · rename_i hstop
        dsimp only
        simp [hq] at hstop
        rcases hstop with hpZero | hdegree
        · exact Or.inl hpZero
        · exact Or.inr hdegree
      · rename_i hcontinue
        dsimp only
        have hcont : p.isZero = false ∧ q.natDegree ≤ p.natDegree := by
          simpa [hq] using hcontinue
        apply ih (p := cancelLead p q) (quotient := quotient + leadQuotient p q)
        have hdrop := degreeCount_cancelLead_lt hcont.1 hq hcont.2
        omega

/-- Executable Euclidean division returns a genuinely smaller nonzero
remainder, not merely a fuel-truncated result. -/
theorem divMod_remainder_small (p q : DensePolynomial ℚ) (hq : q.isZero = false) :
    (divMod p q).remainder.isZero = true ∨
      (divMod p q).remainder.natDegree < q.natDegree := by
  have h := divLoop_remainder_small (p.degreeCount + 1) p.normalize q.normalize 0
    (by simpa using hq) (by simp)
  simpa [divMod] using h

private theorem divMod_remainder_toPolynomial_small (p q : DensePolynomial ℚ)
    (hq : q.isZero = false) :
    (divMod p q).remainder.toPolynomial = 0 ∨
      (divMod p q).remainder.toPolynomial.degree < q.toPolynomial.degree := by
  rcases divMod_remainder_small p q hq with remainderZero | remainderDegree
  · exact Or.inl ((toPolynomial_eq_zero_iff_isZero _).2 remainderZero)
  · by_cases remainderZero : (divMod p q).remainder.isZero = true
    · exact Or.inl ((toPolynomial_eq_zero_iff_isZero _).2 remainderZero)
    · have remainderNonzero : (divMod p q).remainder.isZero = false := by
        simpa using remainderZero
      apply Or.inr
      rw [Polynomial.degree_eq_natDegree
          (toPolynomial_ne_zero_of_isZero_false remainderNonzero),
        Polynomial.degree_eq_natDegree
          (toPolynomial_ne_zero_of_isZero_false hq),
        natDegree_toPolynomial remainderNonzero, natDegree_toPolynomial hq]
      exact_mod_cast remainderDegree

private theorem polynomial_remainder_unique
    {P Q quotientLeft quotientRight remainderLeft remainderRight : Polynomial ℚ}
    (leftEquation : P = Q * quotientLeft + remainderLeft)
    (rightEquation : P = Q * quotientRight + remainderRight)
    (leftSmall : remainderLeft = 0 ∨ remainderLeft.degree < Q.degree)
    (rightSmall : remainderRight = 0 ∨ remainderRight.degree < Q.degree) :
    remainderLeft = remainderRight := by
  have differenceDivisible : Q ∣ remainderLeft - remainderRight := by
    refine ⟨quotientRight - quotientLeft, ?_⟩
    have leftRest : remainderLeft = P - Q * quotientLeft := by
      rw [leftEquation]
      ring
    have rightRest : remainderRight = P - Q * quotientRight := by
      rw [rightEquation]
      ring
    rw [leftRest, rightRest]
    ring
  by_cases differenceZero : remainderLeft - remainderRight = 0
  · exact sub_eq_zero.mp differenceZero
  have differenceSmall :
      (remainderLeft - remainderRight).degree < Q.degree := by
    rcases leftSmall with leftZero | leftDegree
    · rcases rightSmall with rightZero | rightDegree
      · exact (differenceZero (by rw [leftZero, rightZero, sub_self])).elim
      · simpa only [leftZero, zero_sub, Polynomial.degree_neg] using rightDegree
    · rcases rightSmall with rightZero | rightDegree
      · simpa only [rightZero, sub_zero] using leftDegree
      · exact (Polynomial.degree_sub_le remainderLeft remainderRight).trans_lt
          (max_lt leftDegree rightDegree)
  exact ((not_le_of_gt differenceSmall)
    (Polynomial.degree_le_of_dvd differenceDivisible differenceZero)).elim

/-- If the sparse divisor divides the sparse dividend, executable long
division returns the zero remainder.  This follows from the exact quotient
equation and strict degree descent, without sparse Euclidean `%` or roots. -/
theorem divMod_remainder_isZero_of_toPolynomial_dvd
    {p q : DensePolynomial ℚ} (hq : q.isZero = false)
    (divides : q.toPolynomial ∣ p.toPolynomial) :
    (divMod p q).remainder.isZero = true := by
  rcases divides with ⟨quotient, equation⟩
  apply (toPolynomial_eq_zero_iff_isZero _).1
  apply polynomial_remainder_unique
      (divMod_toPolynomial_equation p q)
      (by simpa only [add_zero] using equation)
      (divMod_remainder_toPolynomial_small p q hq)
      (Or.inl rfl)

theorem scale_isZero_false {c : ℚ} {p : DensePolynomial ℚ}
    (hc : c ≠ 0) (hp : p.isZero = false) : (scale c p).isZero = false := by
  by_contra hscale
  have hscaleTrue : (scale c p).isZero = true := by simpa using hscale
  have hzero := (toPolynomial_eq_zero_iff_isZero (scale c p)).2 hscaleTrue
  rw [toPolynomial_scale] at hzero
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
    (toPolynomial_ne_zero_of_isZero_false hp) hzero

theorem isZero_scale_of_ne_zero {c : ℚ} (hc : c ≠ 0)
    (p : DensePolynomial ℚ) : (scale c p).isZero = p.isZero := by
  cases hp : p.isZero with
  | false => exact scale_isZero_false hc hp
  | true =>
      have hpPoly := (toPolynomial_eq_zero_iff_isZero p).2 hp
      have hscalePoly : (scale c p).toPolynomial = 0 := by
        rw [toPolynomial_scale, hpPoly, mul_zero]
      exact (toPolynomial_eq_zero_iff_isZero (scale c p)).1 hscalePoly

theorem scale_neg (c : ℚ) (p : DensePolynomial ℚ) :
    scale c (-p) = -(scale c p) := by
  have hpoly : (scale c (-p)).toPolynomial = (-(scale c p)).toPolynomial := by
    rw [toPolynomial_scale, toPolynomial_neg, toPolynomial_neg,
      toPolynomial_scale]
    ring
  have equality := normalize_eq_normalize_of_toPolynomial_eq hpoly
  rw [normalize_scale, normalize_neg] at equality
  exact equality

/-- Scaling dividend and divisor by arbitrary nonzero rationals scales the
executable remainder by the dividend scalar. -/
theorem divMod_remainder_scale (p q : DensePolynomial ℚ) {a b : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : q.isZero = false) :
    (divMod (scale a p) (scale b q)).remainder =
      scale a (divMod p q).remainder := by
  have hqScaled := scale_isZero_false hb hq
  have scalar : b * (a / b) = a := by field_simp
  have constantScalar : C b * C (a / b) = (C a : Polynomial ℚ) := by
    rw [← map_mul, scalar]
  have rightEquation :
      (scale a p).toPolynomial =
        (scale b q).toPolynomial *
            (C (a / b) * (divMod p q).quotient.toPolynomial) +
          (scale a (divMod p q).remainder).toPolynomial := by
    rw [toPolynomial_scale, toPolynomial_scale, toPolynomial_scale,
      divMod_toPolynomial_equation p q]
    calc
      C a * (q.toPolynomial * (divMod p q).quotient.toPolynomial +
          (divMod p q).remainder.toPolynomial) =
          C a * q.toPolynomial * (divMod p q).quotient.toPolynomial +
            C a * (divMod p q).remainder.toPolynomial := by ring
      _ = (C b * C (a / b)) * q.toPolynomial *
            (divMod p q).quotient.toPolynomial +
            C a * (divMod p q).remainder.toPolynomial := by
          rw [constantScalar]
      _ = C b * q.toPolynomial *
            (C (a / b) * (divMod p q).quotient.toPolynomial) +
            C a * (divMod p q).remainder.toPolynomial := by ring
  have rightSmall :
      (scale a (divMod p q).remainder).toPolynomial = 0 ∨
        (scale a (divMod p q).remainder).toPolynomial.degree <
          (scale b q).toPolynomial.degree := by
    rcases divMod_remainder_toPolynomial_small p q hq with remainderZero |
        remainderDegree
    · left
      rw [toPolynomial_scale, remainderZero, mul_zero]
    · right
      rw [toPolynomial_scale, toPolynomial_scale,
        Polynomial.degree_C_mul ha, Polynomial.degree_C_mul hb]
      exact remainderDegree
  have hpoly : (divMod (scale a p) (scale b q)).remainder.toPolynomial =
      (scale a (divMod p q).remainder).toPolynomial := by
    apply polynomial_remainder_unique
        (divMod_toPolynomial_equation (scale a p) (scale b q))
        rightEquation
        (divMod_remainder_toPolynomial_small (scale a p) (scale b q) hqScaled)
        rightSmall
  simpa using normalize_eq_normalize_of_toPolynomial_eq hpoly

/-- Equal-degree division performs exactly one leading cancellation before its
remainder is already smaller than the divisor. -/
theorem divMod_remainder_eq_cancelLead_of_natDegree_eq
    {p q : DensePolynomial ℚ} (hp : p.isZero = false)
    (hq : q.isZero = false) (hdegree : p.natDegree = q.natDegree) :
    (divMod p q).remainder = cancelLead p q := by
  have hpPoly := toPolynomial_ne_zero_of_isZero_false hp
  have hqPoly := toPolynomial_ne_zero_of_isZero_false hq
  have hdegrees : p.toPolynomial.degree = q.toPolynomial.degree := by
    rw [Polynomial.degree_eq_natDegree hpPoly,
      Polynomial.degree_eq_natDegree hqPoly,
      natDegree_toPolynomial hp, natDegree_toPolynomial hq, hdegree]
  have hcancelSmall : (cancelLead p q).toPolynomial.degree <
      q.toPolynomial.degree := by
    rw [← hdegrees]
    exact degree_toPolynomial_cancelLead_lt hp hq (by omega)
  have rightEquation : p.toPolynomial =
      q.toPolynomial * C (p.leadingCoeff / q.leadingCoeff) +
        (cancelLead p q).toPolynomial := by
    rw [toPolynomial_cancelLead, hdegree]
    simp
    ring
  have hpoly : (divMod p q).remainder.toPolynomial =
      (cancelLead p q).toPolynomial := by
    apply polynomial_remainder_unique
        (divMod_toPolynomial_equation p q)
        rightEquation
        (divMod_remainder_toPolynomial_small p q hq)
        (Or.inr hcancelSmall)
  simpa using normalize_eq_normalize_of_toPolynomial_eq hpoly

/-- For equal nonzero degrees, the first signed remainder of the reversed
pair is a fixed nonzero scalar multiple of the forward signed remainder. -/
theorem signedRemainder_swap_of_natDegree_eq
    {p q : DensePolynomial ℚ} (hp : p.isZero = false)
    (hq : q.isZero = false) (hdegree : p.natDegree = q.natDegree) :
    -((divMod q p).remainder) =
      scale (-(q.leadingCoeff / p.leadingCoeff))
        (-((divMod p q).remainder)) := by
  rw [divMod_remainder_eq_cancelLead_of_natDegree_eq hq hp hdegree.symm,
    divMod_remainder_eq_cancelLead_of_natDegree_eq hp hq hdegree]
  have hpoly : (-(cancelLead q p)).toPolynomial =
      (scale (-(q.leadingCoeff / p.leadingCoeff))
        (-(cancelLead p q))).toPolynomial := by
    rw [toPolynomial_neg, toPolynomial_cancelLead,
      toPolynomial_scale, toPolynomial_neg, toPolynomial_cancelLead,
      hdegree, hdegree.symm]
    simp only [Nat.sub_self, pow_zero, mul_one, map_neg]
    have hscalar :
        (q.leadingCoeff / p.leadingCoeff) *
          (p.leadingCoeff / q.leadingCoeff) = 1 := by
      field_simp [leadingCoeff_ne_zero hp, leadingCoeff_ne_zero hq]
    have hconstant :
        C (q.leadingCoeff / p.leadingCoeff) *
          C (p.leadingCoeff / q.leadingCoeff) = (1 : Polynomial ℚ) := by
      rw [← map_mul, hscalar, map_one]
    calc
      -(q.toPolynomial - C (q.leadingCoeff / p.leadingCoeff) * p.toPolynomial) =
          C (q.leadingCoeff / p.leadingCoeff) * p.toPolynomial -
            q.toPolynomial := by ring
      _ = C (q.leadingCoeff / p.leadingCoeff) * p.toPolynomial -
          (C (q.leadingCoeff / p.leadingCoeff) *
            C (p.leadingCoeff / q.leadingCoeff)) * q.toPolynomial := by
            rw [hconstant, one_mul]
      _ = -C (q.leadingCoeff / p.leadingCoeff) *
          -(p.toPolynomial - C (p.leadingCoeff / q.leadingCoeff) *
            q.toPolynomial) := by ring
  simpa using normalize_eq_normalize_of_toPolynomial_eq hpoly

/-- After the equal-degree first step, the next reverse remainder is the
oppositely alternating scalar multiple of the forward remainder. -/
theorem divMod_remainder_equalDegree_tail
    {p q : DensePolynomial ℚ} (hp : p.isZero = false)
    (hq : q.isZero = false) (hdegree : p.natDegree = q.natDegree)
    (hr : (-((divMod p q).remainder)).isZero = false) :
    let r := -((divMod p q).remainder)
    let c := p.leadingCoeff / q.leadingCoeff
    let k := -(q.leadingCoeff / p.leadingCoeff)
    (divMod p (scale k r)).remainder =
      scale c (divMod q r).remainder := by
  dsimp only
  let r := -((divMod p q).remainder)
  let c := p.leadingCoeff / q.leadingCoeff
  let k := -(q.leadingCoeff / p.leadingCoeff)
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
  have hk : k ≠ 0 := neg_ne_zero.mpr
    (div_ne_zero (leadingCoeff_ne_zero hq) (leadingCoeff_ne_zero hp))
  have hscaledR : (scale k r).isZero = false := scale_isZero_false hk hr
  have hrelation : p.toPolynomial = C c * q.toPolynomial - r.toPolynomial := by
    dsimp only [r, c]
    rw [divMod_remainder_eq_cancelLead_of_natDegree_eq hp hq hdegree,
      toPolynomial_neg, toPolynomial_cancelLead, hdegree]
    simp
  have constantInverse : C k * C k⁻¹ = (1 : Polynomial ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hk, map_one]
  have rightEquation : p.toPolynomial =
      (scale k r).toPolynomial *
          (C k⁻¹ *
            (C c * (divMod q r).quotient.toPolynomial - 1)) +
        (scale c (divMod q r).remainder).toPolynomial := by
    rw [toPolynomial_scale, toPolynomial_scale, hrelation,
      divMod_toPolynomial_equation q r]
    calc
      C c * (r.toPolynomial * (divMod q r).quotient.toPolynomial +
          (divMod q r).remainder.toPolynomial) - r.toPolynomial =
          r.toPolynomial *
              (C c * (divMod q r).quotient.toPolynomial - 1) +
            C c * (divMod q r).remainder.toPolynomial := by ring
      _ = (C k * C k⁻¹) * r.toPolynomial *
              (C c * (divMod q r).quotient.toPolynomial - 1) +
            C c * (divMod q r).remainder.toPolynomial := by
          rw [constantInverse, one_mul]
      _ = C k * r.toPolynomial *
              (C k⁻¹ *
                (C c * (divMod q r).quotient.toPolynomial - 1)) +
            C c * (divMod q r).remainder.toPolynomial := by ring
  have rightSmall :
      (scale c (divMod q r).remainder).toPolynomial = 0 ∨
        (scale c (divMod q r).remainder).toPolynomial.degree <
          (scale k r).toPolynomial.degree := by
    rcases divMod_remainder_toPolynomial_small q r hr with remainderZero |
        remainderDegree
    · left
      rw [toPolynomial_scale, remainderZero, mul_zero]
    · right
      rw [toPolynomial_scale, toPolynomial_scale,
        Polynomial.degree_C_mul hc, Polynomial.degree_C_mul hk]
      exact remainderDegree
  have hpoly : (divMod p (scale k r)).remainder.toPolynomial =
      (scale c (divMod q r).remainder).toPolynomial := by
    apply polynomial_remainder_unique
        (divMod_toPolynomial_equation p (scale k r))
        rightEquation
        (divMod_remainder_toPolynomial_small p (scale k r) hscaledR)
        rightSmall
  simpa using normalize_eq_normalize_of_toPolynomial_eq hpoly

theorem eval_eq_of_natDegree_zero {p : DensePolynomial ℚ}
    (hp : p.isZero = false) (hdegree : p.natDegree = 0) (x y : ℚ) :
    p.eval x = p.eval y := by
  have hpPoly := toPolynomial_ne_zero_of_isZero_false hp
  have hspecDegree : p.toPolynomial.natDegree = 0 := by
    rw [natDegree_toPolynomial hp, hdegree]
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hspecDegree
  rw [← eval_toPolynomial, ← eval_toPolynomial, hconstant]
  simp

end Rational

end FTA.ComputablePolynomial.DensePolynomial
