import FTA.DensePolynomialBridge
import Mathlib.Tactic.Positivity

/-!
# Bounded rational safe-candidate search

This is the finite pigeonhole engine used in the central-third searches of
Theorem 3.2(d), Theorem 3.4, and Lemma 5.2.  The program evaluates an
executable dense rational polynomial from left to right.  A semantic bridge to
Mathlib proves that a nonzero degree-`D` polynomial cannot reject all `D+1`
distinct candidates.
-/

namespace FTA.SafeCandidates

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial

abbrev RatPolynomial := DensePolynomial ℚ

/-- Return the first candidate at which `p` is exactly nonzero. -/
def firstNonzero (p : RatPolynomial) : List ℚ → Option ℚ
  | [] => none
  | x :: xs => if p.eval x = 0 then firstNonzero p xs else some x

theorem firstNonzero_some_spec {p : RatPolynomial} {xs : List ℚ} {x : ℚ}
    (h : firstNonzero p xs = some x) : x ∈ xs ∧ p.eval x ≠ 0 := by
  induction xs with
  | nil => simp [firstNonzero] at h
  | cons a as ih =>
      by_cases ha : p.eval a = 0
      · rw [firstNonzero, if_pos ha] at h
        rcases ih h with ⟨hx, hpx⟩
        exact ⟨List.mem_cons_of_mem a hx, hpx⟩
      · rw [firstNonzero, if_neg ha] at h
        injection h with hax
        subst x
        exact ⟨by simp, ha⟩

theorem firstNonzero_eq_none_iff (p : RatPolynomial) (xs : List ℚ) :
    firstNonzero p xs = none ↔ ∀ x ∈ xs, p.eval x = 0 := by
  induction xs with
  | nil => simp [firstNonzero]
  | cons a as ih =>
      by_cases ha : p.eval a = 0
      · simp [firstNonzero, ha, ih]
      · simp [firstNonzero, ha]

/-- A nonzero specification polynomial of degree below the candidate-list
length makes the executable search succeed. -/
theorem firstNonzero_exists (p : RatPolynomial) (xs : List ℚ)
    (hp : p.toPolynomial ≠ 0) (hxs : xs.Nodup)
    (hdegree : p.toPolynomial.natDegree < xs.length) :
    ∃ x, firstNonzero p xs = some x := by
  cases hsearch : firstNonzero p xs with
  | none =>
      have hall := (firstNonzero_eq_none_iff p xs).mp hsearch
      have hpzero : p.toPolynomial = 0 := by
        apply polynomial_eq_zero_of_eval_zero_on_list
            p.toPolynomial xs hxs hdegree
        intro x hx
        rw [eval_toPolynomial]
        exact hall x hx
      exact (hp hpzero).elim
  | some x => exact ⟨x, rfl⟩

/-- Left endpoint of the central third of `[a,b]`. -/
def centralLeft (a b : ℚ) : ℚ := (2 * a + b) / 3

/-- Right endpoint of the central third of `[a,b]`. -/
def centralRight (a b : ℚ) : ℚ := (a + 2 * b) / 3

/-- Spacing for `D+1` interior points of the central third. -/
def centralStep (a b : ℚ) (D : ℕ) : ℚ :=
  (b - a) / (3 * (D + 2 : ℕ))

/-- Candidate `k` among `D+1` equally spaced points strictly inside the
central third. -/
def centralCandidate (a b : ℚ) (D : ℕ) (k : Fin (D + 1)) : ℚ :=
  centralLeft a b + (k.val + 1 : ℕ) * centralStep a b D

def centralCandidates (a b : ℚ) (D : ℕ) : List ℚ :=
  List.ofFn (centralCandidate a b D)

theorem centralStep_pos {a b : ℚ} (hab : a < b) (D : ℕ) :
    0 < centralStep a b D := by
  dsimp [centralStep]
  positivity

theorem centralCandidate_injective {a b : ℚ} (hab : a < b) (D : ℕ) :
    Function.Injective (centralCandidate a b D) := by
  intro i j hij
  apply Fin.ext
  have hstep := centralStep_pos hab D
  have hmul : ((i.val + 1 : ℕ) : ℚ) * centralStep a b D =
      ((j.val + 1 : ℕ) : ℚ) * centralStep a b D := by
    dsimp [centralCandidate] at hij
    linarith
  have hcoeff := mul_right_cancel₀ hstep.ne' hmul
  have hnat : i.val + 1 = j.val + 1 := by exact_mod_cast hcoeff
  omega

theorem centralCandidates_nodup {a b : ℚ} (hab : a < b) (D : ℕ) :
    (centralCandidates a b D).Nodup := by
  exact List.nodup_ofFn.mpr (centralCandidate_injective hab D)

@[simp] theorem centralCandidates_length (a b : ℚ) (D : ℕ) :
    (centralCandidates a b D).length = D + 1 := by
  simp [centralCandidates]

theorem centralCandidate_bounds {a b : ℚ} (hab : a < b) (D : ℕ)
    (k : Fin (D + 1)) :
    centralLeft a b < centralCandidate a b D k ∧
      centralCandidate a b D k < centralRight a b := by
  have hstep := centralStep_pos hab D
  have hkNat : k.val + 1 < D + 2 := by omega
  have hkRat : ((k.val + 1 : ℕ) : ℚ) < (D + 2 : ℕ) := by
    exact_mod_cast hkNat
  have hscale : ((D + 2 : ℕ) : ℚ) * centralStep a b D = (b - a) / 3 := by
    dsimp [centralStep]
    field_simp
  have hoffset : ((k.val + 1 : ℕ) : ℚ) * centralStep a b D < (b - a) / 3 := by
    have hmul := mul_lt_mul_of_pos_right hkRat hstep
    rw [hscale] at hmul
    exact hmul
  dsimp only [centralCandidate]
  constructor
  · have hkPos : (0 : ℚ) < (k.val + 1 : ℕ) := by positivity
    nlinarith
  · dsimp [centralLeft, centralRight] at hoffset ⊢
    linarith

/-- The bounded central-third search program used by safe subdivision. -/
def centralSearch (p : RatPolynomial) (a b : ℚ) (D : ℕ) : Option ℚ :=
  firstNonzero p (centralCandidates a b D)

theorem centralSearch_some_spec {p : RatPolynomial} {a b : ℚ} {D : ℕ}
    (hab : a < b) {c : ℚ} (hc : centralSearch p a b D = some c) :
    c ∈ centralCandidates a b D ∧ p.eval c ≠ 0 ∧
      centralLeft a b < c ∧ c < centralRight a b := by
  rcases firstNonzero_some_spec hc with ⟨hmem, hnonzero⟩
  rw [centralCandidates, List.mem_ofFn'] at hmem
  rcases hmem with ⟨k, rfl⟩
  exact ⟨List.mem_ofFn.mpr ⟨k, rfl⟩, hnonzero, centralCandidate_bounds hab D k⟩

theorem centralSearch_succeeds (p : RatPolynomial) {a b : ℚ} (D : ℕ)
    (hab : a < b) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    ∃ c, centralSearch p a b D = some c := by
  exact firstNonzero_exists p (centralCandidates a b D) hp
    (centralCandidates_nodup hab D) (by simpa using Nat.lt_succ_of_le hdegree)

theorem centralSearch_isSome (p : RatPolynomial) {a b : ℚ} (D : ℕ)
    (hab : a < b) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    (centralSearch p a b D).isSome := by
  rcases centralSearch_succeeds p D hab hp hdegree with ⟨c, hc⟩
  rw [hc]
  rfl

/-- Total executable projection of the successful bounded candidate search.
The proof argument is erased; the returned rational is computed by the same
finite `firstNonzero` scan. -/
def centralSearchValue (p : RatPolynomial) {a b : ℚ} (D : ℕ)
    (hab : a < b) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) : ℚ :=
  (centralSearch p a b D).get (centralSearch_isSome p D hab hp hdegree)

theorem centralSearchValue_spec
    (p : RatPolynomial) {a b : ℚ} (D : ℕ)
    (hab : a < b) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    p.eval (centralSearchValue p D hab hp hdegree) ≠ 0 ∧
      centralLeft a b < centralSearchValue p D hab hp hdegree ∧
      centralSearchValue p D hab hp hdegree < centralRight a b := by
  let search := centralSearch p a b D
  have hsome : search.isSome := centralSearch_isSome p D hab hp hdegree
  have hget : search = some (search.get hsome) :=
    Option.eq_some_of_isSome hsome
  have hspec := centralSearch_some_spec hab hget
  simpa only [search, centralSearchValue] using hspec.2

/-- Lemma 5.2's bounded-search core: exact evaluation of `D+1` displayed
central-third candidates finds a nonzero value for every nonzero polynomial of
degree at most `D`. -/
theorem exists_nonzero_central_candidate (p : RatPolynomial) {a b : ℚ} (D : ℕ)
    (hab : a < b) (hp : p.toPolynomial ≠ 0)
    (hdegree : p.toPolynomial.natDegree ≤ D) :
    ∃ c, c ∈ centralCandidates a b D ∧ p.eval c ≠ 0 ∧
      centralLeft a b < c ∧ c < centralRight a b := by
  have hsearch := centralSearch_succeeds p D hab hp hdegree
  rcases hsearch with ⟨c, hc⟩
  exact ⟨c, centralSearch_some_spec hab hc⟩

end FTA.SafeCandidates
