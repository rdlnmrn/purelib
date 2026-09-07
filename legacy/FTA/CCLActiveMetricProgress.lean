import FTA.CCLActiveBoundarySectorStep

/-!
# Total finite progress for the active CCL metric track

The history-free active controller supplies one constructive raw bit at a
time.  This module packages that controller with the independently refinable
winding box and iterates it by structural recursion on a requested bit count.
It is the direct active-invariant analogue of the older persistent-machine
progress interface.
-/

namespace FTA
namespace CCLActiveMetricProgress

open CCL
open FTA.AxisSafeCuts
open FTA.CCLActiveMetricTrack
open FTA.CCLClearanceExclusion
open FTA.CCLGeometry
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Joint refinement order for active metric states: the numerical box
shrinks and the raw CCL word only grows by appending bits. -/
structure StateRefines
    {p : GaussianPolynomial} {ambient : RatBox}
    (inner outer : State p ambient) : Prop where
  box : inner.core.numerical.box.Refines outer.core.numerical.box
  word : outer.core.word <+: inner.core.word

theorem stateRefines_refl
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : StateRefines state state :=
  ⟨RatBox.refines_refl state.core.numerical.box, List.prefix_refl _⟩

theorem StateRefines.trans
    {p : GaussianPolynomial} {ambient : RatBox}
    {inner middle outer : State p ambient}
    (innerMiddle : StateRefines inner middle)
    (middleOuter : StateRefines middle outer) : StateRefines inner outer :=
  ⟨innerMiddle.box.trans middleOuter.box,
    middleOuter.word.trans innerMiddle.word⟩

/-- The empty word has a constant decoder denominator, so every winding-one
track constructively seeds an active sample provider without a preliminary
search. -/
def initialSeparation
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) :
    CCLDenominator.SeparationOutput p ambient track.initial
      (adjugate (RawParser.parse []).matrix) :=
  CCLDenominator.separateConstantDenominator track.initial
    (adjugate (RawParser.parse []).matrix) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate]) (by
      simp [RawParser.parse, RawParser.initialState, RawParser.identityMatrix,
        adjugate])

/-- Canonical active state at the empty raw word. -/
def initialState
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) : State p ambient :=
  CCLActiveMetricTrack.ofInitialSeparation (initialSeparation track)

@[simp] theorem initialState_word
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) :
    (initialState track).core.word = [] := rfl

theorem initialState_box
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) :
    (initialState track).core.numerical.box = track.initial.box := by
  simp [initialState, initialSeparation,
    CCLActiveMetricTrack.ofInitialSeparation,
    CCLDenominator.separateConstantDenominator]

/-- All fixed constructive data needed to repeat the total active controller
on one nonzero winding-one root track. -/
structure Machine
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R) where
  track : WindingOneTrack p (RatBox.symmetric R hR)
  clearOwnerLabel : Bool
  squarefree : GaussianSquarefreeCertificate p
  degreeNonzero : p.toPolynomial.natDegree ≠ 0
  zeroNonzero : p.eval 0 ≠ 0
  eliminationDegree : ℕ
  elimination : AxisEliminationCertificate p eliminationDegree

/-- Refine only the winding box, retaining the current raw CCL word and its
active sample provider. -/
def Machine.refine
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (positive : 0 < epsilon) :
    State p (RatBox.symmetric R hR) :=
  current.refine
    (machine.track.refine current.core.numerical epsilon positive)
    (machine.track.nested current.core.numerical epsilon positive)

theorem Machine.refine_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (positive : 0 < epsilon) :
    StateRefines (machine.refine current epsilon positive) current := by
  refine ⟨machine.track.nested current.core.numerical epsilon positive, ?_⟩
  change current.core.word <+: current.core.word
  exact List.prefix_refl _

theorem Machine.refine_accurate
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (positive : 0 < epsilon) :
    (machine.refine current epsilon positive).core.numerical.box.diagonalSq ≤
      epsilon ^ 2 := by
  change
    (machine.track.refine current.core.numerical epsilon positive).box.diagonalSq ≤
      epsilon ^ 2
  exact machine.track.accurate current.core.numerical epsilon positive

@[simp] theorem Machine.refine_word
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (positive : 0 < epsilon) :
    (machine.refine current epsilon positive).core.word = current.core.word :=
  rfl

/-- One total x--y Sturm/curve-count bit decision using only the active
history-free invariant. -/
def Machine.step
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR)) : StepResult current :=
  CCLActiveMetricTrack.totalStep machine.track current machine.clearOwnerLabel
    machine.squarefree machine.degreeNonzero machine.zeroNonzero
      machine.elimination

/-- Result after requesting exactly `count` further nonterminal raw bits. -/
inductive AdvanceResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) : ℕ → Type where
  | zero {count : ℕ} (root : p.eval 0 = 0) : AdvanceResult current count
  | terminal {count : ℕ} (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      AdvanceResult current count
  | advanced {count : ℕ} (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (bits : Prefix.Word)
      (bits_length : bits.length = count)
      (word_eq : state.core.word = current.core.word ++ bits)
      (length_eq : state.core.word.length = current.core.word.length + count) :
      AdvanceResult current count

/-- Structural recursion on the requested finite bit count. -/
def advanceBits
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR)) :
    (count : ℕ) → AdvanceResult current count
  | 0 => .advanced current (stateRefines_refl current) [] rfl (by simp) (by simp)
  | count + 1 =>
      match machine.step current with
      | .zero root => .zero root
      | .terminal point root nonzero completeWord complete contains =>
          .terminal point root nonzero completeWord complete contains
      | .next bit next boxRefines wordEq =>
          match advanceBits machine next count with
          | .zero root => .zero root
          | .terminal point root nonzero completeWord complete contains =>
              .terminal point root nonzero completeWord complete
                (boxRefines.contains contains)
          | .advanced final finalRefines finalBits finalBitsLength
              finalWord finalLength =>
              have nextRefines : StateRefines next current := by
                refine ⟨boxRefines, ?_⟩
                rw [wordEq]
                exact List.prefix_append _ _
              .advanced final (finalRefines.trans nextRefines)
                (bit :: finalBits) (by simp [finalBitsLength]) (by
                  rw [finalWord, wordEq]
                  simp [List.append_assoc]) (by
                have nextLength :
                    next.core.word.length = current.core.word.length + 1 := by
                  rw [wordEq]
                  simp
                omega)

/-- Joint finite request: independently contract the winding box and then
construct exactly the requested number of further raw CCL bits unless an
exact rational root is encountered first. -/
inductive RequestResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (count : ℕ) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point)
  | nonterminal (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (accurate : state.core.numerical.box.diagonalSq ≤ epsilon ^ 2)
      (length_eq : state.core.word.length = current.core.word.length + count)

def request
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) (count : ℕ) :
    RequestResult current epsilon count := by
  let accurate := machine.refine current epsilon epsilonPositive
  let run := advanceBits machine accurate count
  match run with
  | .zero root => exact .zero root
  | .terminal point root nonzero completeWord complete contains =>
      exact .terminal point root nonzero completeWord complete
        ((machine.refine_refines current epsilon epsilonPositive).box.contains
          contains)
  | .advanced final finalRefines _bits _bitsLength _wordEq finalLength =>
      have refinesCurrent : StateRefines final current :=
        finalRefines.trans
          (machine.refine_refines current epsilon epsilonPositive)
      have diagonalMonotone : final.core.numerical.box.diagonalSq ≤
          accurate.core.numerical.box.diagonalSq :=
        RatBox.diagonalSq_le_of_refines finalRefines.box
      have accurateBound : accurate.core.numerical.box.diagonalSq ≤
          epsilon ^ 2 :=
        machine.refine_accurate current epsilon epsilonPositive
      exact .nonterminal final refinesCurrent
        (diagonalMonotone.trans accurateBound) (by
          rw [finalLength, Machine.refine_word])

end CCLActiveMetricProgress
end FTA
