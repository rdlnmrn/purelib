import CCL.Knot.TorusBraid
import CCL.Progressive.PowerMonodromy

/-!
# The quadratic power loop realizes the positive two-strand generator

`CCL.PowerMonodromy.unitCircuitLoop` is the existing fully explicit rational
coefficient loop for `Z^d-w`: four stereographic rational quarter-arcs,
finitely subdivided until every root-owner Rouché bound is satisfied.  Its
finite winding calculation proves that the owner monodromy is one full
`d`-cycle.

Here `d=2`.  On two displayed indices, a fixed-point-free bijection is the
unique transposition.  Consequently the positive one-circuit power loop has
the same strand action as the one-letter word `[sigma_1]`.  The positive sign
is backed by the already calculated positive parameter winding `4`, not by an
arbitrary sign choice.
-/

namespace CCL.Knot.PowerGenerator

open CCL.Knot.FiniteBraid

abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame
abbrev ChamberPath := CCL.FiniteMonodromy.ChamberPath
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection

def degree : CCL.RootPowers.RootDegree := CCL.RootPowers.squareRootDegree

@[simp] theorem degree_value : degree.value = 2 := rfl

theorem degreeAtLeastTwo : 2 ≤ degree.value := by decide

def baseVertex : CCL.PowerMonodromy.UnitVertex :=
  CCL.PowerMonodromy.unitCircuitVertex .first degree degreeAtLeastTwo 0

/-- The exact simple-root chamber at the base parameter `w=1`. -/
def frame : ChamberFrame := baseVertex.frame degree degreeAtLeastTwo

@[simp] theorem frame_degree : frame.degree = 2 := by
  unfold frame CCL.PowerMonodromy.UnitVertex.frame
  rw [CCL.PowerMonodromy.robustChamberFrame_degree]
  rfl

/-- The explicit rational polynomial loop `Z^2-w` over one positive unit
circuit. -/
def loop : ChamberPath frame frame :=
  CCL.PowerMonodromy.unitCircuitLoop degree degreeAtLeastTwo

theorem loop_isSingleCycle :
    CCL.FiniteMonodromy.FiniteBijection.IsSingleCycle loop.monodromy := by
  unfold loop
  exact CCL.PowerMonodromy.unitCircuitMonodromy_isSingleCycle
    degree degreeAtLeastTwo

/-- The unique adjacent generator on the two displayed strands. -/
def positiveGenerator : Generator frame.degree where
  index := ⟨0, by rw [frame_degree]; decide⟩
  sign := .positive

def word : Word frame.degree := [positiveGenerator]

theorem index_eq_left_or_right (index : Fin frame.degree) :
    index = positiveGenerator.left ∨ index = positiveGenerator.right := by
  by_cases atLeft : index = positiveGenerator.left
  · exact Or.inl atLeft
  · right
    apply Fin.ext
    have indexBound : index.val < 2 := by
      simpa only [frame_degree] using index.isLt
    have indexNonzero : index.val ≠ 0 := by
      intro zero
      apply atLeft
      apply Fin.ext
      exact zero
    change index.val = positiveGenerator.index.val + 1
    change index.val = 0 + 1
    omega

theorem generator_has_no_fixed_point (index : Fin frame.degree) :
    positiveGenerator.permutation.forward index ≠ index := by
  rcases index_eq_left_or_right index with atLeft | atRight
  · subst index
    rw [Generator.permutation, transposition_forward, swapIndices_left]
    exact positiveGenerator.left_ne_right.symm
  · subst index
    rw [Generator.permutation, transposition_forward, swapIndices_right]
    exact positiveGenerator.left_ne_right

theorem iterateForward_one {count : Nat}
    (bijection : FiniteBijection count count) (index : Fin count) :
    CCL.FiniteMonodromy.FiniteBijection.iterateForward bijection 1 index =
      bijection.forward index := rfl

theorem monodromy_has_no_fixed_point (index : Fin frame.degree) :
    loop.monodromy.forward index ≠ index := by
  have noEarly := loop_isSingleCycle.no_early_return index 1 (by decide) (by
    rw [frame_degree]
    decide)
  rw [iterateForward_one] at noEarly
  exact noEarly

/-- In a two-element finite type, both elements distinct from the same pivot
are equal. -/
theorem fin_two_unique_other {left right pivot : Fin frame.degree}
    (leftDifferent : left ≠ pivot) (rightDifferent : right ≠ pivot) :
    left = right := by
  apply Fin.ext
  have leftBound : left.val < 2 := by
    simpa only [frame_degree] using left.isLt
  have rightBound : right.val < 2 := by
    simpa only [frame_degree] using right.isLt
  have pivotBound : pivot.val < 2 := by
    simpa only [frame_degree] using pivot.isLt
  have leftValueDifferent : left.val ≠ pivot.val := by
    intro same
    exact leftDifferent (Fin.ext same)
  have rightValueDifferent : right.val ≠ pivot.val := by
    intro same
    exact rightDifferent (Fin.ext same)
  omega

/-- Exact agreement between the one-letter positive Artin word and the
owner monodromy computed by the rational quadratic power loop. -/
theorem word_agrees (index : Fin frame.degree) :
    word.permutation.forward index = loop.monodromy.forward index := by
  apply fin_two_unique_other
  · exact generator_has_no_fixed_point index
  · exact monodromy_has_no_fixed_point index

/-- The degree-two power circuit as an existing `CertifiedLoopBraid`. -/
def certifiedBraid : CertifiedLoopBraid frame loop where
  word := word
  agrees := word_agrees

/-- Reversing the same rational coefficient circuit realizes the negative
two-strand generator. -/
def negativeBraid : CertifiedLoopBraid frame loop.reverse :=
  certifiedBraid.reverse

@[simp] theorem negativeBraid_word :
    negativeBraid.word = [positiveGenerator.reverse] := rfl

@[simp] theorem negativeBraid_writhe : negativeBraid.word.writhe = -1 := rfl

/-- The parameter polygon is positively oriented once.  Raw winding is four
times normalized winding in the RFAP convention. -/
theorem positive_parameter_winding :
    CCL.PowerMonodromy.UnitChain.parameterRaw
        RFAP.GlobalWinding.coordinatePolynomial
        (CCL.PowerMonodromy.unitCircuitChain degree degreeAtLeastTwo) = 4 :=
  CCL.PowerMonodromy.unitCircuitChain_parameterRaw_eq_four
    degree degreeAtLeastTwo

/-! ## Repeated quadratic circuits -/

/-- Traverse the same explicit rational coefficient circuit a displayed
number of times.  This is the polynomial family `Z^2 = w^q` restricted to
the unit parameter circuit. -/
def repeatedLoop : Nat → ChamberPath frame frame
  | 0 => .nil frame
  | circuits + 1 => (repeatedLoop circuits).append loop

/-- Repeat the certified positive generator in lockstep with the rational
polynomial circuit. -/
def repeatedBraid : (circuits : Nat) →
    CertifiedLoopBraid frame (repeatedLoop circuits)
  | 0 => .identity frame
  | circuits + 1 => (repeatedBraid circuits).append certifiedBraid

@[simp] theorem repeatedBraid_word (circuits : Nat) :
    (repeatedBraid circuits).word =
      CCL.Knot.TorusBraid.repeatWord word circuits := by
  induction circuits with
  | zero => rfl
  | succ circuits inductionHypothesis =>
      simp only [repeatedBraid,
        CCL.Knot.FiniteBraid.CertifiedLoopBraid.append,
        CCL.Knot.TorusBraid.repeatWord_succ, inductionHypothesis,
        certifiedBraid]

@[simp] theorem repeatedBraid_crossingCount (circuits : Nat) :
    (repeatedBraid circuits).word.length = circuits := by
  rw [repeatedBraid_word, CCL.Knot.TorusBraid.repeatWord_length]
  simp only [word, List.length_cons, List.length_nil]
  omega

@[simp] theorem repeatedBraid_writhe (circuits : Nat) :
    (repeatedBraid circuits).word.writhe = (circuits : Int) := by
  rw [repeatedBraid_word, CCL.Knot.TorusBraid.repeatWord_writhe]
  simp only [word, CCL.Knot.FiniteBraid.Word.writhe_cons,
    CCL.Knot.FiniteBraid.Word.writhe_nil,
    CCL.Knot.FiniteBraid.Generator.weight, positiveGenerator,
    CrossingSign.weight, add_zero, mul_one]

theorem closure_isKnot : certifiedBraid.closure.IsKnot :=
  certifiedBraid.closure_isKnot_of_monodromy_isSingleCycle
    loop_isSingleCycle

end CCL.Knot.PowerGenerator
