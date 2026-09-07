import CCL.Knot.FiniteBraid

/-!
# Constructive Artin relations on finite braid words

The braid relation is represented by finite local rewrites under displayed
word contexts.  Its reflexive, symmetric, transitive closure is an explicit
proof object rather than a quotient.  The main soundness theorems show that
every such proof preserves both the executable strand permutation and the
integer writhe.
-/

namespace CCL.Knot.ArtinRelations

open CCL.Knot.FiniteBraid

abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection

/-! ## Permutation lemmas -/

theorem swapIndices_commute_of_disjoint {count : Nat}
    {firstLeft firstRight secondLeft secondRight : Fin count}
    (leftLeft : firstLeft ≠ secondLeft)
    (leftRight : firstLeft ≠ secondRight)
    (rightLeft : firstRight ≠ secondLeft)
    (rightRight : firstRight ≠ secondRight)
    (index : Fin count) :
    swapIndices secondLeft secondRight
        (swapIndices firstLeft firstRight index) =
      swapIndices firstLeft firstRight
        (swapIndices secondLeft secondRight index) := by
  by_cases atFirstLeft : index = firstLeft
  · subst index
    calc
      swapIndices secondLeft secondRight
          (swapIndices firstLeft firstRight firstLeft) =
        swapIndices secondLeft secondRight firstRight := by
          rw [swapIndices_left]
      _ = firstRight := swapIndices_of_ne rightLeft rightRight
      _ = swapIndices firstLeft firstRight firstLeft :=
        (swapIndices_left firstLeft firstRight).symm
      _ = swapIndices firstLeft firstRight
          (swapIndices secondLeft secondRight firstLeft) := by
        rw [swapIndices_of_ne leftLeft leftRight]
  · by_cases atFirstRight : index = firstRight
    · subst index
      calc
        swapIndices secondLeft secondRight
            (swapIndices firstLeft firstRight firstRight) =
          swapIndices secondLeft secondRight firstLeft := by
            rw [swapIndices_right]
        _ = firstLeft := swapIndices_of_ne leftLeft leftRight
        _ = swapIndices firstLeft firstRight firstRight :=
          (swapIndices_right firstLeft firstRight).symm
        _ = swapIndices firstLeft firstRight
            (swapIndices secondLeft secondRight firstRight) := by
          rw [swapIndices_of_ne rightLeft rightRight]
    · by_cases atSecondLeft : index = secondLeft
      · subst index
        calc
          swapIndices secondLeft secondRight
              (swapIndices firstLeft firstRight secondLeft) =
            swapIndices secondLeft secondRight secondLeft := by
              rw [swapIndices_of_ne leftLeft.symm rightLeft.symm]
          _ = secondRight := swapIndices_left secondLeft secondRight
          _ = swapIndices firstLeft firstRight secondRight :=
            (swapIndices_of_ne leftRight.symm rightRight.symm).symm
          _ = swapIndices firstLeft firstRight
              (swapIndices secondLeft secondRight secondLeft) := by
            rw [swapIndices_left]
      · by_cases atSecondRight : index = secondRight
        · subst index
          calc
            swapIndices secondLeft secondRight
                (swapIndices firstLeft firstRight secondRight) =
              swapIndices secondLeft secondRight secondRight := by
                rw [swapIndices_of_ne leftRight.symm rightRight.symm]
            _ = secondLeft := swapIndices_right secondLeft secondRight
            _ = swapIndices firstLeft firstRight secondLeft :=
              (swapIndices_of_ne leftLeft.symm rightLeft.symm).symm
            _ = swapIndices firstLeft firstRight
                (swapIndices secondLeft secondRight secondRight) := by
              rw [swapIndices_right]
        · calc
          swapIndices secondLeft secondRight
              (swapIndices firstLeft firstRight index) =
            swapIndices secondLeft secondRight index := by
              rw [swapIndices_of_ne atFirstLeft atFirstRight]
          _ = index := swapIndices_of_ne atSecondLeft atSecondRight
          _ = swapIndices firstLeft firstRight index :=
            (swapIndices_of_ne atFirstLeft atFirstRight).symm
          _ = swapIndices firstLeft firstRight
              (swapIndices secondLeft secondRight index) := by
            rw [swapIndices_of_ne atSecondLeft atSecondRight]

theorem swapIndices_braid {count : Nat} {left middle right : Fin count}
    (leftMiddle : left ≠ middle) (leftRight : left ≠ right)
    (middleRight : middle ≠ right) (index : Fin count) :
    swapIndices left middle
        (swapIndices middle right (swapIndices left middle index)) =
      swapIndices middle right
        (swapIndices left middle (swapIndices middle right index)) := by
  by_cases atLeft : index = left
  · subst index
    have leftEvaluation :
        swapIndices left middle
            (swapIndices middle right (swapIndices left middle left)) =
          right := by
      calc
        _ = swapIndices left middle
            (swapIndices middle right middle) := by rw [swapIndices_left]
        _ = swapIndices left middle right := by rw [swapIndices_left]
        _ = right := swapIndices_of_ne leftRight.symm middleRight.symm
    have rightEvaluation :
        swapIndices middle right
            (swapIndices left middle (swapIndices middle right left)) =
          right := by
      calc
        _ = swapIndices middle right (swapIndices left middle left) := by
          rw [swapIndices_of_ne leftMiddle leftRight]
        _ = swapIndices middle right middle := by rw [swapIndices_left]
        _ = right := swapIndices_left middle right
    exact leftEvaluation.trans rightEvaluation.symm
  · by_cases atMiddle : index = middle
    · subst index
      have leftEvaluation :
          swapIndices left middle
              (swapIndices middle right
                (swapIndices left middle middle)) = middle := by
        calc
          _ = swapIndices left middle
              (swapIndices middle right left) := by rw [swapIndices_right]
          _ = swapIndices left middle left := by
            rw [swapIndices_of_ne leftMiddle leftRight]
          _ = middle := swapIndices_left left middle
      have rightEvaluation :
          swapIndices middle right
              (swapIndices left middle
                (swapIndices middle right middle)) = middle := by
        calc
          _ = swapIndices middle right
              (swapIndices left middle right) := by rw [swapIndices_left]
          _ = swapIndices middle right right := by
            rw [swapIndices_of_ne leftRight.symm middleRight.symm]
          _ = middle := swapIndices_right middle right
      exact leftEvaluation.trans rightEvaluation.symm
    · by_cases atRight : index = right
      · subst index
        have leftEvaluation :
            swapIndices left middle
                (swapIndices middle right
                  (swapIndices left middle right)) = left := by
          calc
            _ = swapIndices left middle
                (swapIndices middle right right) := by
              rw [swapIndices_of_ne leftRight.symm middleRight.symm]
            _ = swapIndices left middle middle := by rw [swapIndices_right]
            _ = left := swapIndices_right left middle
        have rightEvaluation :
            swapIndices middle right
                (swapIndices left middle
                  (swapIndices middle right right)) = left := by
          calc
            _ = swapIndices middle right
                (swapIndices left middle middle) := by rw [swapIndices_right]
            _ = swapIndices middle right left := by rw [swapIndices_right]
            _ = left := swapIndices_of_ne leftMiddle leftRight
        exact leftEvaluation.trans rightEvaluation.symm
      · have firstFixed : swapIndices left middle index = index :=
          swapIndices_of_ne atLeft atMiddle
        have secondFixed : swapIndices middle right index = index :=
          swapIndices_of_ne atMiddle atRight
        simp only [firstFixed, secondFixed]

namespace Generator

/-- The lower generator in one displayed adjacent Artin pair. -/
def lower {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) : Generator strands :=
  { index := ⟨index.val, by omega⟩
    sign := sign }

/-- The upper generator in one displayed adjacent Artin pair. -/
def upper {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) : Generator strands :=
  { index := ⟨index.val + 1, by omega⟩
    sign := sign }

theorem lower_right_eq_upper_left {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (lower index sign).right = (upper index sign).left := by
  apply Fin.ext
  rfl

theorem lower_left_ne_upper_right {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (lower index sign).left ≠ (upper index sign).right := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 1 + 1 at values
  omega

/-- Two generator indices separated by at least one untouched strand have
disjoint transposition endpoints. -/
theorem disjoint_of_far {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    first.left ≠ second.left ∧ first.left ≠ second.right ∧
      first.right ≠ second.left ∧ first.right ≠ second.right := by
  rcases far with forward | backward
  · constructor
    · intro equal
      have values := congrArg Fin.val equal
      change first.index.val = second.index.val at values
      omega
    · constructor
      · intro equal
        have values := congrArg Fin.val equal
        change first.index.val = second.index.val + 1 at values
        omega
      · constructor
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val at values
          omega
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val + 1 at values
          omega
  · constructor
    · intro equal
      have values := congrArg Fin.val equal
      change first.index.val = second.index.val at values
      omega
    · constructor
      · intro equal
        have values := congrArg Fin.val equal
        change first.index.val = second.index.val + 1 at values
        omega
      · constructor
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val at values
          omega
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val + 1 at values
          omega

end Generator

namespace Word

def PermutationSame {strands : Nat} (left right : Word strands) : Prop :=
  CCL.FiniteMonodromy.FiniteBijection.Same
    left.permutation right.permutation

theorem permutationSame_refl {strands : Nat} (word : Word strands) :
    PermutationSame word word := fun _ => rfl

theorem permutationSame_symm {strands : Nat} {left right : Word strands}
    (same : PermutationSame left right) : PermutationSame right left :=
  CCL.FiniteMonodromy.FiniteBijection.same_symm same

theorem permutationSame_trans {strands : Nat} {first second third : Word strands}
    (firstSecond : PermutationSame first second)
    (secondThird : PermutationSame second third) :
    PermutationSame first third :=
  CCL.FiniteMonodromy.FiniteBijection.same_trans firstSecond secondThird

theorem permutationSame_append_left {strands : Nat}
    (before : Word strands) {left right : Word strands}
    (same : PermutationSame left right) :
    PermutationSame (before ++ left) (before ++ right) := by
  intro index
  calc
    (before ++ left).permutation.forward index =
        left.permutation.forward (before.permutation.forward index) :=
      CCL.Knot.FiniteBraid.Word.permutation_append before left index
    _ = right.permutation.forward (before.permutation.forward index) :=
      same (before.permutation.forward index)
    _ = (before ++ right).permutation.forward index :=
      (CCL.Knot.FiniteBraid.Word.permutation_append before right index).symm

theorem permutationSame_append_right {strands : Nat}
    {left right : Word strands} (suffix : Word strands)
    (same : PermutationSame left right) :
    PermutationSame (left ++ suffix) (right ++ suffix) := by
  intro index
  calc
    (left ++ suffix).permutation.forward index =
        suffix.permutation.forward (left.permutation.forward index) :=
      CCL.Knot.FiniteBraid.Word.permutation_append left suffix index
    _ = suffix.permutation.forward (right.permutation.forward index) := by
      rw [same]
    _ = (right ++ suffix).permutation.forward index :=
      (CCL.Knot.FiniteBraid.Word.permutation_append right suffix index).symm

theorem permutationSame_context {strands : Nat}
    (before after : Word strands) {left right : Word strands}
    (same : PermutationSame left right) :
    PermutationSame (before ++ left ++ after)
      (before ++ right ++ after) :=
  permutationSame_append_right after
    (permutationSame_append_left before same)

theorem cancellation_permutationSame {strands : Nat}
    (generator : Generator strands) :
    PermutationSame [generator, generator.reverse] [] := by
  intro index
  change swapIndices generator.left generator.right
      (swapIndices generator.left generator.right index) = index
  exact swapIndices_involutive generator.left generator.right index

theorem far_permutationSame {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    PermutationSame [first, second] [second, first] := by
  intro index
  change swapIndices second.left second.right
      (swapIndices first.left first.right index) =
    swapIndices first.left first.right
      (swapIndices second.left second.right index)
  obtain ⟨leftLeft, leftRight, rightLeft, rightRight⟩ :=
    Generator.disjoint_of_far first second far
  exact swapIndices_commute_of_disjoint leftLeft leftRight rightLeft
    rightRight index

theorem artin_permutationSame {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    PermutationSame
      [Generator.lower index sign, Generator.upper index sign,
        Generator.lower index sign]
      [Generator.upper index sign, Generator.lower index sign,
        Generator.upper index sign] := by
  intro strand
  let lower := Generator.lower index sign
  let upper := Generator.upper index sign
  have shared : lower.right = upper.left :=
    Generator.lower_right_eq_upper_left index sign
  have outside : lower.left ≠ upper.right :=
    Generator.lower_left_ne_upper_right index sign
  change swapIndices lower.left lower.right
      (swapIndices upper.left upper.right
        (swapIndices lower.left lower.right strand)) =
    swapIndices upper.left upper.right
      (swapIndices lower.left lower.right
        (swapIndices upper.left upper.right strand))
  rw [← shared]
  exact swapIndices_braid lower.left_ne_right outside upper.left_ne_right strand

end Word

/-! ## Local rewrites and their finite closure -/

inductive Rewrite {strands : Nat} : Word strands → Word strands → Prop
  | cancel (before after : Word strands) (generator : Generator strands) :
      Rewrite (before ++ [generator, generator.reverse] ++ after)
        (before ++ after)
  | far (before after : Word strands) (first second : Generator strands)
      (separated : first.index.val + 1 < second.index.val ∨
        second.index.val + 1 < first.index.val) :
      Rewrite (before ++ [first, second] ++ after)
        (before ++ [second, first] ++ after)
  | artin (before after : Word strands) (index : Fin (strands - 2))
      (sign : CrossingSign) :
      Rewrite
        (before ++ [Generator.lower index sign, Generator.upper index sign,
          Generator.lower index sign] ++ after)
        (before ++ [Generator.upper index sign, Generator.lower index sign,
          Generator.upper index sign] ++ after)

namespace Rewrite

theorem append_right {strands : Nat} {left right : Word strands}
    (rewrite : Rewrite left right) (suffix : Word strands) :
    Rewrite (left ++ suffix) (right ++ suffix) := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [List.append_assoc] using
        Rewrite.cancel before (after ++ suffix) generator
  | far before after first second separated =>
      simpa only [List.append_assoc] using
        Rewrite.far before (after ++ suffix) first second separated
  | artin before after index sign =>
      simpa only [List.append_assoc] using
        Rewrite.artin before (after ++ suffix) index sign

theorem append_left {strands : Nat} (beforeWord : Word strands)
    {left right : Word strands} (rewrite : Rewrite left right) :
    Rewrite (beforeWord ++ left) (beforeWord ++ right) := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [List.append_assoc] using
        Rewrite.cancel (beforeWord ++ before) after generator
  | far before after first second separated =>
      simpa only [List.append_assoc] using
        Rewrite.far (beforeWord ++ before) after first second separated
  | artin before after index sign =>
      simpa only [List.append_assoc] using
        Rewrite.artin (beforeWord ++ before) after index sign

theorem permutationSame {strands : Nat} {left right : Word strands}
    (rewrite : Rewrite left right) : Word.PermutationSame left right := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [List.append_nil] using
        Word.permutationSame_context before after
          (Word.cancellation_permutationSame generator)
  | far before after first second separated =>
      exact Word.permutationSame_context before after
        (Word.far_permutationSame first second separated)
  | artin before after index sign =>
      exact Word.permutationSame_context before after
        (Word.artin_permutationSame index sign)

theorem writhe_eq {strands : Nat} {left right : Word strands}
    (rewrite : Rewrite left right) : left.writhe = right.writhe := by
  cases rewrite with
  | cancel before after generator =>
      simp only [CCL.Knot.FiniteBraid.Word.writhe_append,
        CCL.Knot.FiniteBraid.Word.writhe_cons,
        CCL.Knot.FiniteBraid.Word.writhe_nil, add_zero,
        CCL.Knot.FiniteBraid.Generator.weight_reverse]
      omega
  | far before after first second separated =>
      simp only [CCL.Knot.FiniteBraid.Word.writhe_append,
        CCL.Knot.FiniteBraid.Word.writhe_cons,
        CCL.Knot.FiniteBraid.Word.writhe_nil, add_zero]
      omega
  | artin before after index sign =>
      simp only [CCL.Knot.FiniteBraid.Word.writhe_append,
        CCL.Knot.FiniteBraid.Word.writhe_cons,
        CCL.Knot.FiniteBraid.Word.writhe_nil, add_zero,
        CCL.Knot.FiniteBraid.Generator.weight,
        Generator.lower, Generator.upper]

end Rewrite

/-- Constructive equivalence generated by the finite Artin rewrites. -/
inductive Equivalent {strands : Nat} : Word strands → Word strands → Prop
  | refl (word : Word strands) : Equivalent word word
  | step {left right : Word strands} (rewrite : Rewrite left right) :
      Equivalent left right
  | symm {left right : Word strands} (relation : Equivalent left right) :
      Equivalent right left
  | trans {first second third : Word strands}
      (firstSecond : Equivalent first second)
      (secondThird : Equivalent second third) : Equivalent first third

namespace Equivalent

theorem append_right {strands : Nat} {left right : Word strands}
    (relation : Equivalent left right) (suffix : Word strands) :
    Equivalent (left ++ suffix) (right ++ suffix) := by
  induction relation with
  | refl word => exact .refl _
  | step rewrite => exact .step (rewrite.append_right suffix)
  | symm relation inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

theorem append_left {strands : Nat} (beforeWord : Word strands)
    {left right : Word strands} (relation : Equivalent left right) :
    Equivalent (beforeWord ++ left) (beforeWord ++ right) := by
  induction relation with
  | refl word => exact .refl _
  | step rewrite => exact .step (rewrite.append_left beforeWord)
  | symm relation inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

theorem append {strands : Nat}
    {firstLeft firstRight secondLeft secondRight : Word strands}
    (first : Equivalent firstLeft firstRight)
    (second : Equivalent secondLeft secondRight) :
    Equivalent (firstLeft ++ secondLeft) (firstRight ++ secondRight) :=
  .trans (first.append_right secondLeft) (second.append_left firstRight)

/-- A word followed by its explicitly reversed signed word cancels by a
finite sequence of local cancellation rewrites. -/
theorem append_inverse {strands : Nat} :
    ∀ word : Word strands,
      Equivalent (word ++ CCL.Knot.FiniteBraid.Word.inverse word) []
  | [] => .refl []
  | generator :: remaining => by
      have middle := (append_inverse remaining).append_left [generator]
      have context := middle.append_right [generator.reverse]
      have reduceMiddle : Equivalent
          ([generator] ++ (remaining ++
            CCL.Knot.FiniteBraid.Word.inverse remaining) ++
            [generator.reverse])
          ([generator] ++ [] ++ [generator.reverse]) := by
        simpa only [List.append_assoc] using context
      have cancel : Equivalent
          ([generator] ++ [] ++ [generator.reverse]) [] := by
        simpa only [List.nil_append, List.append_nil, List.cons_append] using
          Equivalent.step (Rewrite.cancel [] [] generator)
      have normalized :
          (generator :: remaining) ++
              CCL.Knot.FiniteBraid.Word.inverse (generator :: remaining) =
            [generator] ++ (remaining ++
              CCL.Knot.FiniteBraid.Word.inverse remaining) ++
              [generator.reverse] := by
        simp only [CCL.Knot.FiniteBraid.Word.inverse_cons,
          List.cons_append, List.nil_append, List.append_assoc]
      rw [normalized]
      exact .trans reduceMiddle cancel

theorem permutationSame {strands : Nat} {left right : Word strands}
    (relation : Equivalent left right) : Word.PermutationSame left right := by
  induction relation with
  | refl word => exact Word.permutationSame_refl word
  | step rewrite => exact rewrite.permutationSame
  | symm relation inductionHypothesis =>
      exact Word.permutationSame_symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact Word.permutationSame_trans firstHypothesis secondHypothesis

theorem writhe_eq {strands : Nat} {left right : Word strands}
    (relation : Equivalent left right) : left.writhe = right.writhe := by
  induction relation with
  | refl word => rfl
  | step rewrite => exact rewrite.writhe_eq
  | symm relation inductionHypothesis => exact inductionHypothesis.symm
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

end Equivalent

end CCL.Knot.ArtinRelations
