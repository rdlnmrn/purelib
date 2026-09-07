import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.RawParser

/-!
# Finite prefix minimax over the pure CCL bitstream

This module formalizes the information-theoretic theorem of Section 7.  It is
only about finite `List Bool` tags.  Chordal geometry, boxed names, arithmetic
sidecars, completed streams, and collections of all compatible values do not
occur here.
-/

namespace CCL.PrefixMinimax

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Word := List Bool

/-- Longest common finite binary prefix. -/
def lcp : Word → Word → Word
  | left :: leftRest, right :: rightRest =>
      if left = right then left :: lcp leftRest rightRest else []
  | _, _ => []

@[simp] theorem lcp_nil_left (word : Word) : lcp [] word = [] := rfl
@[simp] theorem lcp_nil_right (word : Word) : lcp word [] = [] := by
  cases word <;> rfl

theorem lcp_append_same (stem left right : Word) :
    lcp (stem ++ left) (stem ++ right) = stem ++ lcp left right := by
  induction stem with
  | nil => rfl
  | cons bit remaining inductionHypothesis =>
      simp only [List.cons_append, lcp, if_pos, inductionHypothesis]

theorem lcp_prefix_left (left right : Word) :
    (lcp left right).IsPrefix left := by
  induction left generalizing right with
  | nil => exact List.prefix_refl []
  | cons leftBit leftRest inductionHypothesis =>
      cases right with
      | nil => exact List.nil_prefix
      | cons rightBit rightRest =>
          by_cases equal : leftBit = rightBit
          · subst rightBit
            rcases inductionHypothesis rightRest with ⟨suffix, identity⟩
            exact ⟨suffix, by
              simp only [lcp, if_pos, List.cons_append, identity]⟩
          · rw [lcp, if_neg equal]
            exact List.nil_prefix

theorem lcp_prefix_right (left right : Word) :
    (lcp left right).IsPrefix right := by
  induction left generalizing right with
  | nil => exact List.nil_prefix
  | cons leftBit leftRest inductionHypothesis =>
      cases right with
      | nil => exact List.prefix_refl []
      | cons rightBit rightRest =>
          by_cases equal : leftBit = rightBit
          · subst rightBit
            rcases inductionHypothesis rightRest with ⟨suffix, identity⟩
            exact ⟨suffix, by
              simp only [lcp, if_pos, List.cons_append, identity]⟩
          · rw [lcp, if_neg equal]
            exact List.nil_prefix

/-- Extending the right word beyond a prefix which the left word has already
left cannot change their longest common prefix. -/
theorem lcp_append_right_of_not_prefix (left stem suffix : Word)
    (notPrefix : ¬stem.IsPrefix left) :
    lcp left (stem ++ suffix) = lcp left stem := by
  induction stem generalizing left with
  | nil => exact (notPrefix List.nil_prefix).elim
  | cons prefixBit prefixRest inductionHypothesis =>
      cases left with
      | nil => rfl
      | cons leftBit leftRest =>
          by_cases equal : leftBit = prefixBit
          · subst leftBit
            have tailNotPrefix : ¬prefixRest.IsPrefix leftRest := by
              intro tailPrefix
              rcases tailPrefix with ⟨remaining, identity⟩
              apply notPrefix
              exact ⟨remaining, by
                simpa only [List.cons_append] using
                  congrArg (List.cons prefixBit) identity⟩
            simp only [List.cons_append, lcp, if_pos]
            rw [inductionHypothesis leftRest tailNotPrefix]
          · simp only [List.cons_append, lcp, if_neg equal]

/-- Positive finite gauges which strictly shrink at either binary child. -/
structure Gauge where
  value : Word → Coordinate
  positive : ∀ word, 0 < value word
  child_lt : ∀ word bit, value (word ++ [bit]) < value word

namespace Gauge

theorem append_le (gauge : Gauge) (word suffix : Word) :
    gauge.value (word ++ suffix) ≤ gauge.value word := by
  induction suffix generalizing word with
  | nil =>
      simp only [List.append_nil]
      exact le_rfl
  | cons bit remaining inductionHypothesis =>
      calc
        gauge.value (word ++ bit :: remaining) =
            gauge.value ((word ++ [bit]) ++ remaining) := by
          congr 1
          simp only [List.append_assoc, List.singleton_append]
        _ ≤ gauge.value (word ++ [bit]) :=
          inductionHypothesis (word ++ [bit])
        _ ≤ gauge.value word := (gauge.child_lt word bit).le

theorem append_lt_of_nonempty (gauge : Gauge) (word suffix : Word)
    (nonempty : suffix ≠ []) :
    gauge.value (word ++ suffix) < gauge.value word := by
  cases suffix with
  | nil => exact (nonempty rfl).elim
  | cons bit remaining =>
      calc
        gauge.value (word ++ bit :: remaining) =
            gauge.value ((word ++ [bit]) ++ remaining) := by
          congr 1
          simp only [List.append_assoc, List.singleton_append]
        _ ≤ gauge.value (word ++ [bit]) :=
          gauge.append_le (word ++ [bit]) remaining
        _ < gauge.value word := gauge.child_lt word bit

theorem lt_of_strict_prefix (gauge : Gauge) {shorter longer : Word}
    (isPrefix : shorter.IsPrefix longer) (different : shorter ≠ longer) :
    gauge.value longer < gauge.value shorter := by
  rcases isPrefix with ⟨suffix, identity⟩
  have suffixNonempty : suffix ≠ [] := by
    intro suffixEmpty
    apply different
    rw [← identity, suffixEmpty, List.append_nil]
  rw [← identity]
  exact gauge.append_lt_of_nonempty shorter suffix suffixNonempty

end Gauge

/-- Finite cylindrical distance induced by the longest common binary prefix. -/
def distance (gauge : Gauge) (left right : Word) : Coordinate :=
  if left = right then 0 else gauge.value (lcp left right)

/-- Maximum distance from one finite candidate tag to two displayed witness
tags. -/
def twoWitnessRadius (gauge : Gauge) (candidate left right : Word) :
    Coordinate :=
  max (distance gauge candidate left) (distance gauge candidate right)

theorem distance_nonneg (gauge : Gauge) (left right : Word) :
    0 ≤ distance gauge left right := by
  unfold distance
  split
  · exact le_rfl
  · exact (gauge.positive _).le

theorem distance_le_of_common_prefix (gauge : Gauge)
    {stem left right : Word}
    (leftPrefix : stem.IsPrefix left)
    (rightPrefix : stem.IsPrefix right) :
    distance gauge left right ≤ gauge.value stem := by
  rcases leftPrefix with ⟨leftSuffix, rfl⟩
  rcases rightPrefix with ⟨rightSuffix, rfl⟩
  unfold distance
  split
  · exact (gauge.positive stem).le
  · rw [lcp_append_same]
    exact gauge.append_le stem (lcp leftSuffix rightSuffix)

/-- A strict finite extension is at exactly the gauge radius of its displayed
prefix.  For a terminated rational name this is the manuscript's
`d_g(w_n, enc(z)⊣) = g(w_n)` clause before the final prefix. -/
theorem distance_prefix_child (gauge : Gauge)
    (stem tail : Word) (bit : Bool) :
    distance gauge stem (stem ++ bit :: tail) = gauge.value stem := by
  have different : stem ≠ stem ++ bit :: tail := by
    intro equal
    have lengths := congrArg List.length equal
    have strict : stem.length < (stem ++ bit :: tail).length := by
      rw [List.length_append, List.length_cons]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ tail.length)
    exact (Nat.ne_of_lt strict) lengths
  rw [distance, if_neg different]
  have lcpIdentity : lcp stem (stem ++ bit :: tail) = stem := by
    calc
      lcp stem (stem ++ bit :: tail) =
          lcp (stem ++ []) (stem ++ bit :: tail) := by
        rw [List.append_nil]
      _ = stem ++ lcp [] (bit :: tail) := lcp_append_same _ _ _
      _ = stem := by simp only [lcp_nil_left, List.append_nil]
  rw [lcpIdentity]

private theorem distance_opposite_child (gauge : Gauge)
    (stem leftTail rightTail : Word) (bit : Bool) :
    distance gauge (stem ++ bit :: leftTail)
        (stem ++ (!bit) :: rightTail) = gauge.value stem := by
  cases bit with
  | false =>
      have different : stem ++ false :: leftTail ≠
          stem ++ true :: rightTail := by
        intro equal
        have cancelled := List.append_cancel_left equal
        simp only [List.cons.injEq, Bool.false_eq_true, false_and] at cancelled
      simp only [Bool.not_false]
      rw [distance, if_neg different, lcp_append_same]
      simp only [lcp, Bool.false_eq_true, if_false, List.append_nil]
  | true =>
      have different : stem ++ true :: leftTail ≠
          stem ++ false :: rightTail := by
        intro equal
        have cancelled := List.append_cancel_left equal
        simp only [List.cons.injEq, Bool.true_eq_false, false_and] at cancelled
      simp only [Bool.not_true]
      rw [distance, if_neg different, lcp_append_same]
      simp only [lcp, Bool.true_eq_false, if_false, List.append_nil]

/-- Finite two-witness minimax theorem.  `leftTail` and `rightTail` are the
remainders of two explicitly displayed tags in the opposite children of
`prefix`; no family of all compatible tags is formed. -/
theorem finite_twoWitness_minimax (gauge : Gauge)
    (stem candidate leftTail rightTail : Word) :
    let leftWitness := stem ++ false :: leftTail
    let rightWitness := stem ++ true :: rightTail
    (stem.IsPrefix candidate →
      twoWitnessRadius gauge candidate leftWitness rightWitness =
        gauge.value stem) ∧
    (¬stem.IsPrefix candidate →
      gauge.value stem <
        twoWitnessRadius gauge candidate leftWitness rightWitness) := by
  dsimp only
  constructor
  · intro candidatePrefix
    rcases candidatePrefix with ⟨candidateTail, rfl⟩
    have leftUpper :
        distance gauge (stem ++ candidateTail)
            (stem ++ false :: leftTail) ≤ gauge.value stem :=
      distance_le_of_common_prefix gauge
        (List.prefix_append _ _) (List.prefix_append _ _)
    have rightUpper :
        distance gauge (stem ++ candidateTail)
            (stem ++ true :: rightTail) ≤ gauge.value stem :=
      distance_le_of_common_prefix gauge
        (List.prefix_append _ _) (List.prefix_append _ _)
    apply le_antisymm
    · exact max_le leftUpper rightUpper
    · cases candidateTail with
      | nil =>
          rw [List.append_nil]
          calc
            gauge.value stem =
                distance gauge stem (stem ++ false :: leftTail) :=
              (distance_prefix_child gauge stem leftTail false).symm
            _ ≤ max
                (distance gauge stem (stem ++ false :: leftTail))
                (distance gauge stem (stem ++ true :: rightTail)) :=
              le_max_left _ _
      | cons bit remaining =>
          cases bit with
          | false =>
              calc
                gauge.value stem = distance gauge
                    (stem ++ false :: remaining)
                    (stem ++ true :: rightTail) :=
                  (distance_opposite_child gauge stem remaining rightTail
                    false).symm
                _ ≤ max
                    (distance gauge (stem ++ false :: remaining)
                      (stem ++ false :: leftTail))
                    (distance gauge (stem ++ false :: remaining)
                      (stem ++ true :: rightTail)) := le_max_right _ _
          | true =>
              calc
                gauge.value stem = distance gauge
                    (stem ++ true :: remaining)
                    (stem ++ false :: leftTail) :=
                  (distance_opposite_child gauge stem remaining leftTail
                    true).symm
                _ ≤ max
                    (distance gauge (stem ++ true :: remaining)
                      (stem ++ false :: leftTail))
                    (distance gauge (stem ++ true :: remaining)
                      (stem ++ true :: rightTail)) := le_max_left _ _
  · intro notPrefix
    let common := lcp candidate stem
    have commonPrefix : common.IsPrefix stem := lcp_prefix_right _ _
    have commonDifferent : common ≠ stem := by
      intro equal
      apply notPrefix
      rw [← equal]
      exact lcp_prefix_left candidate stem
    have gaugeStrict : gauge.value stem < gauge.value common :=
      gauge.lt_of_strict_prefix commonPrefix commonDifferent
    have candidateDifferent :
        candidate ≠ stem ++ false :: leftTail := by
      intro equal
      apply notPrefix
      rw [equal]
      exact List.prefix_append _ _
    have leftDistance :
        distance gauge candidate (stem ++ false :: leftTail) =
          gauge.value common := by
      rw [distance, if_neg candidateDifferent,
        lcp_append_right_of_not_prefix candidate stem
          (false :: leftTail) notPrefix]
    exact gaugeStrict.trans_le (leftDistance.ge.trans (le_max_left _ _))

/-- The paper's dyadic bit gauge. -/
def bitGauge : Gauge where
  value word := (1 / 2 : Coordinate) ^ word.length
  positive word :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) word.length
  child_lt word bit := by
    rw [List.length_append, List.length_singleton, pow_succ]
    let power := (1 / 2 : Coordinate) ^ word.length
    have powerPositive : 0 < power :=
      RFAP.ConstructiveFraction.pow_pos_direct (by decide) word.length
    calc
      power * (1 / 2 : Coordinate) = (1 / 2 : Coordinate) * power := by
        ring1
      _ < 1 * power :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) powerPositive
      _ = power := RFAP.ConstructiveFraction.one_mul _

/-- Pointwise finite bit-budget corollary at a genuine binary branch. -/
theorem bitGauge_twoWitness_radius
    (stem candidate leftTail rightTail : Word)
    (candidatePrefix : stem.IsPrefix candidate) :
    twoWitnessRadius bitGauge candidate
        (stem ++ false :: leftTail) (stem ++ true :: rightTail) =
      (1 / 2 : Coordinate) ^ stem.length := by
  exact (finite_twoWitness_minimax bitGauge stem candidate
    leftTail rightTail).1 candidatePrefix

end CCL.PrefixMinimax
