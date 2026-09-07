import CCL.Progressive.FiniteMonodromy

/-!
# Finite braid words and combinatorial closures

This file supplies the finite combinatorial target for certified polynomial
root motion.  A braid word is a displayed list of signed adjacent
transpositions.  Its strand action is evaluated into the explicit finite
bijections used by `CCL.FiniteMonodromy`; no quotient group, infinite
configuration space, or choice of representatives is introduced.

The closure predicate deliberately records the exact finite condition needed
to distinguish a knot from a multi-component link: the evaluated strand
permutation is one cycle.  A `CertifiedLoopBraid` then joins a word to the
monodromy of one finite chamber loop by pointwise equality of their displayed
permutations.
-/

namespace CCL.Knot.FiniteBraid

abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection
abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame
abbrev ChamberPath := CCL.FiniteMonodromy.ChamberPath

/-! ## Explicit finite transpositions -/

/-- Swap two displayed finite indices.  The definition is executable and is
its own inverse, including in the harmless degenerate case `left = right`. -/
def swapIndices {count : Nat} (left right index : Fin count) : Fin count :=
  if index = left then right else if index = right then left else index

@[simp] theorem swapIndices_left {count : Nat} (left right : Fin count) :
    swapIndices left right left = right := by
  simp only [swapIndices, ↓reduceIte]

theorem swapIndices_right {count : Nat} (left right : Fin count) :
    swapIndices left right right = left := by
  by_cases same : right = left
  · subst right
    simp only [swapIndices, ↓reduceIte]
  · simp only [swapIndices, same, ↓reduceIte]

theorem swapIndices_of_ne {count : Nat} {left right index : Fin count}
    (notLeft : index ≠ left) (notRight : index ≠ right) :
    swapIndices left right index = index := by
  simp only [swapIndices, notLeft, notRight, ↓reduceIte]

@[simp] theorem swapIndices_involutive {count : Nat}
    (left right index : Fin count) :
    swapIndices left right (swapIndices left right index) = index := by
  by_cases same : left = right
  · subst right
    simp only [swapIndices]
    by_cases atLeft : index = left
    · simp only [atLeft, ↓reduceIte]
    · simp only [atLeft, ↓reduceIte]
  · by_cases atLeft : index = left
    · subst index
      rw [swapIndices_left, swapIndices_right]
    · by_cases atRight : index = right
      · subst index
        rw [swapIndices_right, swapIndices_left]
      · rw [swapIndices_of_ne atLeft atRight,
          swapIndices_of_ne atLeft atRight]

/-- The explicit finite bijection associated to one transposition. -/
def transposition {count : Nat} (left right : Fin count) :
    FiniteBijection count count where
  forward := swapIndices left right
  backward := swapIndices left right
  backward_forward := swapIndices_involutive left right
  forward_backward := swapIndices_involutive left right

@[simp] theorem transposition_forward {count : Nat}
    (left right index : Fin count) :
    (transposition left right).forward index = swapIndices left right index :=
  rfl

theorem transposition_reverse {count : Nat} (left right : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.Same
      (transposition left right).reverse
      (transposition left right) :=
  fun _ => rfl

theorem iterateForward_same {count : Nat}
    {left right : FiniteBijection count count}
    (same : CCL.FiniteMonodromy.FiniteBijection.Same left right)
    (steps : Nat) (index : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward left steps index =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward right steps index := by
  induction steps with
  | zero => rfl
  | succ prior inductionHypothesis =>
      rw [CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        CCL.FiniteMonodromy.FiniteBijection.iterateForward_succ,
        inductionHypothesis, same]

theorem reverse_same {count : Nat}
    {left right : FiniteBijection count count}
    (same : CCL.FiniteMonodromy.FiniteBijection.Same left right) :
    CCL.FiniteMonodromy.FiniteBijection.Same left.reverse right.reverse := by
  intro target
  change left.backward target = right.backward target
  have forwardEqual := same (left.backward target)
  rw [left.forward_backward] at forwardEqual
  have pulledBack := congrArg right.backward forwardEqual
  rw [right.backward_forward] at pulledBack
  exact pulledBack.symm

/-! ## Signed Artin generators -/

inductive CrossingSign
  | positive
  | negative
deriving DecidableEq, Repr

namespace CrossingSign

def reverse : CrossingSign → CrossingSign
  | .positive => .negative
  | .negative => .positive

@[simp] theorem reverse_reverse (sign : CrossingSign) :
    sign.reverse.reverse = sign := by
  cases sign <;> rfl

/-- Algebraic crossing contribution.  This finite integer is the writhe
contribution of a displayed generator. -/
def weight : CrossingSign → Int
  | .positive => 1
  | .negative => -1

@[simp] theorem weight_reverse (sign : CrossingSign) :
    sign.reverse.weight = -sign.weight := by
  cases sign <;> rfl

end CrossingSign

/-- One signed adjacent crossing on `strands` displayed strands.  The index
type is empty when fewer than two strands are available. -/
structure Generator (strands : Nat) where
  index : Fin (strands - 1)
  sign : CrossingSign
deriving DecidableEq, Repr

namespace Generator

def left {strands : Nat} (generator : Generator strands) : Fin strands :=
  ⟨generator.index.val, by omega⟩

def right {strands : Nat} (generator : Generator strands) : Fin strands :=
  ⟨generator.index.val + 1, by omega⟩

theorem left_ne_right {strands : Nat} (generator : Generator strands) :
    generator.left ≠ generator.right := by
  intro equal
  have values := congrArg Fin.val equal
  change generator.index.val = generator.index.val + 1 at values
  omega

/-- Crossing sign affects over/under data but not endpoint permutation. -/
def permutation {strands : Nat} (generator : Generator strands) :
    FiniteBijection strands strands :=
  transposition generator.left generator.right

@[simp] theorem permutation_involutive {strands : Nat}
    (generator : Generator strands) (index : Fin strands) :
    generator.permutation.forward
        (generator.permutation.forward index) = index :=
  swapIndices_involutive generator.left generator.right index

def reverse {strands : Nat} (generator : Generator strands) :
    Generator strands :=
  { index := generator.index
    sign := generator.sign.reverse }

@[simp] theorem reverse_index {strands : Nat}
    (generator : Generator strands) : generator.reverse.index = generator.index :=
  rfl

@[simp] theorem reverse_sign {strands : Nat}
    (generator : Generator strands) :
    generator.reverse.sign = generator.sign.reverse := rfl

@[simp] theorem reverse_reverse {strands : Nat}
    (generator : Generator strands) : generator.reverse.reverse = generator := by
  cases generator with
  | mk index sign =>
      simp only [reverse, CrossingSign.reverse_reverse]

theorem permutation_reverse {strands : Nat}
    (generator : Generator strands) :
    CCL.FiniteMonodromy.FiniteBijection.Same generator.reverse.permutation
      generator.permutation.reverse :=
  fun _ => rfl

def weight {strands : Nat} (generator : Generator strands) : Int :=
  generator.sign.weight

@[simp] theorem weight_reverse {strands : Nat}
    (generator : Generator strands) :
    generator.reverse.weight = -generator.weight :=
  CrossingSign.weight_reverse generator.sign

end Generator

/-! ## Executable braid words -/

abbrev Word (strands : Nat) := List (Generator strands)

namespace Word

/-- Evaluate a word in traversal order: the head crossing acts first. -/
def permutation {strands : Nat} : Word strands → FiniteBijection strands strands
  | [] => CCL.FiniteMonodromy.FiniteBijection.identity strands
  | generator :: remaining =>
      CCL.FiniteMonodromy.FiniteBijection.comp
        (permutation remaining) generator.permutation

@[simp] theorem permutation_nil (strands : Nat) :
    permutation ([] : Word strands) =
      CCL.FiniteMonodromy.FiniteBijection.identity strands := rfl

@[simp] theorem permutation_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    permutation (generator :: remaining) =
      CCL.FiniteMonodromy.FiniteBijection.comp
        (permutation remaining) generator.permutation := rfl

theorem permutation_append {strands : Nat} (first second : Word strands) :
    CCL.FiniteMonodromy.FiniteBijection.Same
      (permutation (first ++ second))
      (CCL.FiniteMonodromy.FiniteBijection.comp
        (permutation second) (permutation first)) := by
  intro index
  induction first generalizing index with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change (permutation (remaining ++ second)).forward
          (generator.permutation.forward index) =
        (permutation second).forward
          ((permutation remaining).forward
            (generator.permutation.forward index))
      exact inductionHypothesis (generator.permutation.forward index)

/-- Reverse traversal and invert every signed crossing. -/
def inverse {strands : Nat} (word : Word strands) : Word strands :=
  (List.reverse word).map Generator.reverse

@[simp] theorem inverse_nil (strands : Nat) :
    inverse ([] : Word strands) = [] := rfl

@[simp] theorem inverse_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    inverse (generator :: remaining) =
      inverse remaining ++ [generator.reverse] := by
  simp only [inverse, List.reverse_cons, List.map_append, List.map_cons,
    List.map_nil]

@[simp] theorem inverse_append {strands : Nat}
    (first second : Word strands) :
    inverse (first ++ second) = inverse second ++ inverse first := by
  unfold inverse
  rw [List.reverse_append, List.map_append]

@[simp] theorem inverse_inverse {strands : Nat} (word : Word strands) :
    inverse (inverse word) = word := by
  unfold inverse
  rw [← List.map_reverse, List.reverse_reverse, List.map_map]
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change generator.reverse.reverse ::
          List.map (Generator.reverse ∘ Generator.reverse) remaining =
        generator :: remaining
      rw [Generator.reverse_reverse, inductionHypothesis]

theorem permutation_inverse {strands : Nat} (word : Word strands) :
    CCL.FiniteMonodromy.FiniteBijection.Same
      word.inverse.permutation word.permutation.reverse := by
  intro index
  induction word generalizing index with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [inverse_cons, permutation_append]
      change generator.reverse.permutation.forward
          ((permutation (inverse remaining)).forward index) =
        generator.permutation.backward
          ((permutation remaining).backward index)
      rw [inductionHypothesis]
      exact generator.permutation_reverse _

/-- Finite algebraic crossing count. -/
def writhe {strands : Nat} (word : Word strands) : Int :=
  word.foldr (fun generator total => generator.weight + total) 0

@[simp] theorem writhe_nil (strands : Nat) :
    writhe ([] : Word strands) = 0 := rfl

@[simp] theorem writhe_cons {strands : Nat}
    (generator : Generator strands) (remaining : Word strands) :
    writhe (generator :: remaining) = generator.weight + remaining.writhe :=
  rfl

theorem writhe_append {strands : Nat} (first second : Word strands) :
    writhe (first ++ second) = writhe first + writhe second := by
  induction first with
  | nil => simp only [List.nil_append, writhe_nil, zero_add]
  | cons generator remaining inductionHypothesis =>
      simp only [List.cons_append, writhe_cons, inductionHypothesis]
      omega

theorem writhe_inverse {strands : Nat} (word : Word strands) :
    writhe (inverse word) = -writhe word := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      rw [inverse_cons, writhe_append, inductionHypothesis]
      simp only [writhe_cons, writhe_nil, add_zero, Generator.weight_reverse]
      omega

end Word

/-! ## Finite closures and certified root braids -/

/-- A finite combinatorial braid closure.  Later invariants consume the word
and its executable strand permutation directly. -/
structure Closure where
  strands : Nat
  word : Word strands
deriving Repr

namespace Closure

def permutation (closure : Closure) :
    FiniteBijection closure.strands closure.strands :=
  closure.word.permutation

/-- The closure is a knot exactly when its displayed strand permutation is
one cycle.  Otherwise it is a multi-component link. -/
def IsKnot (closure : Closure) : Prop :=
  CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle closure.permutation

end Closure

/-- A certified braid extraction for one closed finite root path.  The word
is useful combinatorial output; `agrees` is the finite certificate that its
strand action is exactly the root-owner monodromy. -/
structure CertifiedLoopBraid (frame : ChamberFrame)
    (loop : ChamberPath frame frame) where
  word : Word frame.degree
  agrees : CCL.FiniteMonodromy.FiniteBijection.Same
    word.permutation loop.monodromy

namespace CertifiedLoopBraid

def identity (frame : ChamberFrame) :
    CertifiedLoopBraid frame (.nil frame) where
  word := []
  agrees := fun _ => rfl

/-- Concatenate two certified extractions without recomputing any root
matching. -/
def append {frame : ChamberFrame} {first second : ChamberPath frame frame}
    (firstBraid : CertifiedLoopBraid frame first)
    (secondBraid : CertifiedLoopBraid frame second) :
    CertifiedLoopBraid frame (first.append second) where
  word := firstBraid.word ++ secondBraid.word
  agrees := by
    intro index
    calc
      (firstBraid.word ++ secondBraid.word).permutation.forward index =
          secondBraid.word.permutation.forward
            (firstBraid.word.permutation.forward index) :=
        Word.permutation_append firstBraid.word secondBraid.word index
      _ = second.monodromy.forward (first.monodromy.forward index) := by
        rw [firstBraid.agrees, secondBraid.agrees]
      _ = (first.append second).monodromy.forward index :=
        (CCL.FiniteMonodromy.ChamberPath.monodromy_append
          first second index).symm

def reverse {frame : ChamberFrame} {loop : ChamberPath frame frame}
    (braid : CertifiedLoopBraid frame loop) :
    CertifiedLoopBraid frame loop.reverse where
  word := braid.word.inverse
  agrees := CCL.FiniteMonodromy.FiniteBijection.same_trans
    braid.word.permutation_inverse
    (CCL.FiniteMonodromy.FiniteBijection.same_trans
      (reverse_same braid.agrees)
      (CCL.FiniteMonodromy.FiniteBijection.same_symm
        loop.monodromy_reverse))

def closure {frame : ChamberFrame} {loop : ChamberPath frame frame}
    (braid : CertifiedLoopBraid frame loop) : Closure :=
  { strands := frame.degree
    word := braid.word }

theorem closure_isKnot_of_monodromy_isSingleCycle
    {frame : ChamberFrame} {loop : ChamberPath frame frame}
    (braid : CertifiedLoopBraid frame loop)
    (single : CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle
      loop.monodromy) :
    braid.closure.IsKnot := by
  refine
    { return_at_count := ?_
      no_early_return := ?_ }
  · intro index
    change CCL.FiniteMonodromy.FiniteBijection.iterateForward
      braid.word.permutation frame.degree index = index
    rw [iterateForward_same braid.agrees]
    exact single.return_at_count index
  · intro index steps positive small returned
    apply single.no_early_return index steps positive small
    change CCL.FiniteMonodromy.FiniteBijection.iterateForward
      braid.word.permutation steps index = index at returned
    rw [← iterateForward_same braid.agrees]
    exact returned

end CertifiedLoopBraid

end CCL.Knot.FiniteBraid
