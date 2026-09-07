import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Finite prefix gauges and the two-witness minimax theorem

This module proves the combinatorial content of Theorem 7.1 for raw finite bit
words.  It defines the longest common prefix recursively, rather than appealing
to infinite streams or cylinders as sets.
-/

namespace CCL

namespace Prefix

abbrev Word := List Bool

/-- The longest common prefix of two finite bit words. -/
def lcp : Word → Word → Word
  | b :: u, c :: v => if b = c then b :: lcp u v else []
  | _, _ => []

@[simp] theorem lcp_nil_left (v : Word) : lcp [] v = [] := by cases v <;> rfl
@[simp] theorem lcp_nil_right (u : Word) : lcp u [] = [] := by cases u <;> rfl
@[simp] theorem lcp_cons_same (b : Bool) (u v : Word) :
    lcp (b :: u) (b :: v) = b :: lcp u v := by simp [lcp]
@[simp] theorem lcp_false_true (u v : Word) : lcp (false :: u) (true :: v) = [] := rfl
@[simp] theorem lcp_true_false (u v : Word) : lcp (true :: u) (false :: v) = [] := rfl

theorem lcp_append (w u v : Word) :
    lcp (w ++ u) (w ++ v) = w ++ lcp u v := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]

theorem lcp_prefix_left (u v : Word) : lcp u v <+: u := by
  induction u generalizing v with
  | nil => simp
  | cons b u ih =>
      cases v with
      | nil => simp
      | cons c v =>
          by_cases h : b = c
          · subst c
            simpa [lcp] using ih v
          · simp [lcp, h]

theorem lcp_prefix_right (u v : Word) : lcp u v <+: v := by
  induction u generalizing v with
  | nil => simp
  | cons b u ih =>
      cases v with
      | nil => simp
      | cons c v =>
          by_cases h : b = c
          · subst c
            simpa [lcp] using ih v
          · simp [lcp, h]

theorem lcp_eq_left_of_prefix {u v : Word} (h : u <+: v) : lcp u v = u := by
  rcases h with ⟨t, rfl⟩
  simpa using lcp_append u [] t

theorem prefix_lcp_of_common {w u v : Word} (hu : w <+: u) (hv : w <+: v) :
    w <+: lcp u v := by
  rcases hu with ⟨s, rfl⟩
  rcases hv with ⟨t, h⟩
  rw [← h, lcp_append]
  exact List.prefix_append w (lcp s t)

/-- A positive rational gauge that strictly decreases after either child bit. -/
structure Gauge where
  value : Word → ℚ
  positive : ∀ w, 0 < value w
  child_lt : ∀ w b, value (w ++ [b]) < value w

namespace Gauge

theorem append_lt (G : Gauge) (w : Word) {t : Word} (ht : t ≠ []) :
    G.value (w ++ t) < G.value w := by
  induction t generalizing w with
  | nil => contradiction
  | cons b t ih =>
      cases t with
      | nil => simpa using G.child_lt w b
      | cons c t =>
          have htail : G.value ((w ++ [b]) ++ (c :: t)) < G.value (w ++ [b]) :=
            ih (w := w ++ [b]) (by simp)
          have hchild := G.child_lt w b
          calc
            G.value (w ++ b :: c :: t) = G.value ((w ++ [b]) ++ (c :: t)) := by
              simp only [List.append_assoc, List.singleton_append]
            _ < G.value (w ++ [b]) := htail
            _ < G.value w := hchild

theorem antitone_of_prefix (G : Gauge) {u v : Word} (h : u <+: v) :
    G.value v ≤ G.value u := by
  rcases h with ⟨t, rfl⟩
  cases t with
  | nil => simp
  | cons b t => exact (G.append_lt u (by simp)).le

theorem strictAnti_of_prefix (G : Gauge) {u v : Word} (h : u <+: v) (hne : u ≠ v) :
    G.value v < G.value u := by
  rcases h with ⟨t, rfl⟩
  apply G.append_lt
  intro ht
  subst t
  simp at hne

end Gauge

/-- Formula (7.4) on finite binary tags. -/
def distance (G : Gauge) (a x : Word) : ℚ :=
  if a = x then 0 else G.value (lcp a x)

/-- The finite two-witness radius from Theorem 7.1. -/
def radius (G : Gauge) (a x₀ x₁ : Word) : ℚ :=
  max (distance G a x₀) (distance G a x₁)

theorem distance_nonneg (G : Gauge) (a x : Word) : 0 ≤ distance G a x := by
  unfold distance
  split_ifs
  · exact le_rfl
  · exact (G.positive _).le

theorem distance_le_of_common {G : Gauge} {w a x : Word}
    (ha : w <+: a) (hx : w <+: x) : distance G a x ≤ G.value w := by
  unfold distance
  split_ifs
  · exact (G.positive w).le
  · exact G.antitone_of_prefix (prefix_lcp_of_common ha hx)

theorem distance_gt_of_missed_prefix {G : Gauge} {w a x : Word}
    (ha : ¬w <+: a) (hx : w <+: x) : G.value w < distance G a x := by
  have hax : a ≠ x := by
    intro h
    subst x
    exact ha hx
  rw [distance, if_neg hax]
  have hlx : lcp a x <+: x := lcp_prefix_right a x
  have hla : lcp a x <+: a := lcp_prefix_left a x
  have hlw : lcp a x <+: w := by
    rcases List.prefix_or_prefix_of_prefix hlx hx with h | h
    · exact h
    · exfalso
      exact ha (h.trans hla)
  have hne : lcp a x ≠ w := by
    intro h
    subst w
    exact ha hla
  exact G.strictAnti_of_prefix hlw hne

private theorem one_split_distance_exact (G : Gauge) {w a x₀ x₁ : Word}
    (ha : w <+: a) (hx₀ : w ++ [false] <+: x₀)
    (hx₁ : w ++ [true] <+: x₁) :
    distance G a x₀ = G.value w ∨ distance G a x₁ = G.value w := by
  rcases ha with ⟨t, rfl⟩
  cases t with
  | nil =>
      left
      have hwx : w <+: x₀ := (List.prefix_append w [false]).trans hx₀
      have hne : w ≠ x₀ := by
        intro h
        subst x₀
        have hlen := hx₀.length_le
        simp at hlen
      simp [distance, hne, lcp_eq_left_of_prefix hwx]
  | cons b t =>
      cases b with
      | false =>
          right
          rcases hx₁ with ⟨u, rfl⟩
          simp [distance, lcp_append, List.append_assoc]
      | true =>
          left
          rcases hx₀ with ⟨u, rfl⟩
          simp [distance, lcp_append, List.append_assoc]

/-- Theorem 7.1 for raw finite bit tags.

The hypotheses are the two rational-witness consequences actually used by the
paper: one terminal code continues through `w0`, and another through `w1`.
-/
theorem two_witness_minimax (G : Gauge) {w a x₀ x₁ : Word}
    (hx₀ : w ++ [false] <+: x₀) (hx₁ : w ++ [true] <+: x₁) :
    (w <+: a →
      radius G a x₀ x₁ = G.value w ∧
      ∀ x, w <+: x → distance G a x ≤ G.value w) ∧
    (¬w <+: a → G.value w < radius G a x₀ x₁) := by
  constructor
  · intro ha
    have hwx₀ : w <+: x₀ := (List.prefix_append w [false]).trans hx₀
    have hwx₁ : w <+: x₁ := (List.prefix_append w [true]).trans hx₁
    have h₀ := distance_le_of_common (G := G) ha hwx₀
    have h₁ := distance_le_of_common (G := G) ha hwx₁
    constructor
    · rcases one_split_distance_exact G ha hx₀ hx₁ with heq | heq
      · simp [radius, heq, max_eq_left h₁]
      · simp [radius, heq, max_eq_right h₀]
    · intro x hx
      exact distance_le_of_common ha hx
  · intro ha
    have hwx₀ : w <+: x₀ := (List.prefix_append w [false]).trans hx₀
    have hgt := distance_gt_of_missed_prefix (G := G) ha hwx₀
    exact hgt.trans_le (le_max_left _ _)

/-- The pointwise bit gauge `2^{-|w|}` from Corollary 7.2. -/
def bitGauge : Gauge where
  value w := 1 / (2 : ℚ) ^ w.length
  positive w := by positivity
  child_lt w b := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_one,
      pow_succ]
    have hp : 0 < (2 : ℚ) ^ w.length := by positivity
    field_simp
    nlinarith

@[simp] theorem bitGauge_value (w : Word) :
    bitGauge.value w = 1 / (2 : ℚ) ^ w.length := rfl

/-- Corollary 7.2, with the pointwise bit budget written explicitly. -/
theorem bit_two_witness_minimax {w a x₀ x₁ : Word}
    (hx₀ : w ++ [false] <+: x₀) (hx₁ : w ++ [true] <+: x₁) :
    (w <+: a →
      radius bitGauge a x₀ x₁ = 1 / (2 : ℚ) ^ w.length) ∧
    (¬w <+: a → 1 / (2 : ℚ) ^ w.length < radius bitGauge a x₀ x₁) := by
  constructor
  · intro ha
    exact ((two_witness_minimax bitGauge (a := a) hx₀ hx₁).1 ha).1
  · exact (two_witness_minimax bitGauge (a := a) hx₀ hx₁).2

/-- Consecutive entries of the finite prefix tower are nested. -/
theorem take_prefix_succ (v : Word) (n : ℕ) : v.take n <+: v.take (n + 1) := by
  exact List.take_isPrefix_take.mpr (Or.inl (Nat.le_succ n))

/-- Every entry of the finite prefix tower is compatible with its completed
word, which is the cylinder assertion used in Proposition 7.3. -/
theorem take_prefix_word (v : Word) (n : ℕ) : v.take n <+: v :=
  List.take_prefix n v

/-- Before the completed word, a prefix is at exactly its gauge radius from
that word. -/
theorem distance_take_exact (G : Gauge) (v : Word) {n : ℕ} (hn : n < v.length) :
    distance G (v.take n) v = G.value (v.take n) := by
  have hp : v.take n <+: v := List.take_prefix n v
  have hne : v.take n ≠ v := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_take] at hlen
    omega
  rw [distance, if_neg hne, lcp_eq_left_of_prefix hp]

end Prefix

end CCL
