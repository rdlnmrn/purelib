module
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Basic
import Purelib.RootIsolation.Power.Unit.Chain.Rotation
public import Purelib.RootIsolation.Power.Unit.Chain.Winding
import Purelib.RootIsolation.Power.Unit.Circuit.Chain
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Power.Unit.Circuit.Winding
public import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Loop
import Purelib.RootIsolation.Progressive.Power.Unit.Circuit.Monodromy
import Purelib.RootIsolation.Progressive.Power.Unit.Frame
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.RootIsolation.Progressive.Braid.Certified
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Topology.Knot.Braid.Basic
public import Purelib.Topology.Knot.Braid.Word.Power
import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Topology.Knot.Closure.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.RootIsolation.Progressive.Braid.Certified (CertifiedLoopBraid)

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# The quadratic power loop realizes the positive two-strand generator

`Purelib.CCL.Progressive.PowerMonodromy.unitCircuitLoop` is the existing fully explicit rational
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

namespace Purelib.RootIsolation.Progressive.Braid.Power.Quadratic

open Purelib.Topology.Knot.Braid

/-- The retained positive root degree of the quadratic power family. -/
def degree : Data.Nat.Positive.RootDegree :=
  Data.Nat.Positive.squareRootDegree

/-- The retained quadratic root degree has value two. -/
@[simp] theorem degree_value :
  degree.value = 2 := rfl

/-- The retained quadratic root degree satisfies the unit-circuit lower bound. -/
theorem degreeAtLeastTwo : 2 ≤
  degree.value := by decide

/-- The exact initial rational unit vertex of the quadratic power circuit. -/
def baseVertex :
  Geometry.Gaussian.UnitCircle.Basic.UnitVertex :=
  Power.Unit.Circuit.Vertex.unitCircuitVertex .first degree
    degreeAtLeastTwo 0

/-- The exact simple-root chamber at the base parameter `w=1`. -/
def frame : Progressive.Chamber.Frame.ChamberFrame :=
  baseVertex.frame degree
  degreeAtLeastTwo

/-- The quadratic robust chamber has exactly two retained owner indices. -/
@[simp] theorem frame_degree :
  frame.degree = 2 := by
  unfold frame Geometry.Gaussian.UnitCircle.Basic.UnitVertex.frame
  rw [Progressive.Power.Unit.Frame.robustChamberFrame_degree]
  rfl

/-- The explicit rational polynomial loop `Z^2-w` over one positive unit
circuit. -/
def loop : Progressive.Chamber.Path.Basic.ChamberPath
  frame frame :=
  Progressive.Power.Unit.Circuit.Loop.unitCircuitLoop degree
    degreeAtLeastTwo

/-- The explicit quadratic parameter loop permutes its two retained root owners in one cycle. -/
theorem loop_isSingleCycle :
    Data.Fin.Bijection.IsSingleCycle loop.monodromy := by
  unfold loop
  exact Progressive.Power.Unit.Circuit.Monodromy.unitCircuitMonodromy_isSingleCycle
    degree degreeAtLeastTwo

/-- The unique adjacent generator on the two displayed strands. -/
def positiveGenerator : Generator
  frame.degree where
  index := ⟨0, by rw [frame_degree]; decide⟩
  sign := .positive

/-- The one-letter positive Artin word on the original quadratic chamber's two strands. -/
def word : Word
  frame.degree := [positiveGenerator]

/-- Every retained quadratic owner index is one of the positive generator's two endpoints. -/
theorem index_eq_left_or_right (index : Fin
  frame.degree) :
    index = positiveGenerator.left ∨ index =
      positiveGenerator.right := by
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

/-- The retained positive quadratic generator moves every owner index. -/
theorem generator_has_no_fixed_point (index : Fin
  frame.degree) :
    positiveGenerator.permutation.forward index ≠ index := by
  rcases index_eq_left_or_right index with atLeft | atRight
  · subst index
    rw [Generator.permutation, Data.Fin.Bijection.Transposition.transposition_forward,
      Data.Fin.Bijection.Transposition.swapIndices_left]
    exact positiveGenerator.left_ne_right.symm
  · subst index
    rw [Generator.permutation, Data.Fin.Bijection.Transposition.transposition_forward,
      Data.Fin.Bijection.Transposition.swapIndices_right]
    exact positiveGenerator.left_ne_right

/-- The original quadratic loop monodromy moves every owner index. -/
theorem monodromy_has_no_fixed_point (index : Fin
  frame.degree) :
    loop.monodromy.forward index ≠ index := by
  have noEarly := loop_isSingleCycle.no_early_return index 1 (by decide) (by
    rw [frame_degree]
    decide)
  rw [Data.Fin.Bijection.Iteration.iterateForward_one] at noEarly
  exact noEarly

/-- In a two-element finite type, both elements distinct from the same pivot
are equal. -/
theorem fin_two_unique_other {left right pivot : Fin
  frame.degree}
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
theorem word_agrees (index : Fin
  frame.degree) :
    word.permutation.forward index =
      loop.monodromy.forward index := by
  apply fin_two_unique_other
  · exact generator_has_no_fixed_point index
  · exact monodromy_has_no_fixed_point index

/-- The degree-two power circuit as an existing `CertifiedLoopBraid`. -/
def certifiedBraid :
  CertifiedLoopBraid frame
  loop where
  word := word
  agrees := word_agrees

/-- Reversing the same rational coefficient circuit realizes the negative
two-strand generator. -/
def negativeBraid :
  CertifiedLoopBraid frame
  loop.reverse :=
  certifiedBraid.reverse

/-- Reversing the certified quadratic loop gives the original reversed one-letter generator word. -/
@[simp] theorem negativeBraid_word :
    negativeBraid.word = [positiveGenerator.reverse]
      := rfl

/-- The reversed quadratic circuit's certified word has writhe negative one. -/
@[simp] theorem negativeBraid_writhe :
  negativeBraid.word.writhe = -1 := rfl

/-- The parameter polygon is positively oriented once.  Raw winding is four
times normalized winding in the RFAP convention. -/
theorem positive_parameter_winding :
    Power.Unit.Chain.Basic.UnitChain.parameterRaw
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
        (Power.Unit.Circuit.Chain.unitCircuitChain degree
          degreeAtLeastTwo) = 4 :=
  Power.Unit.Circuit.Winding.unitCircuitChain_parameterRaw_eq_four
    degree degreeAtLeastTwo

/-! ## Repeated quadratic circuits -/

/-- Traverse the same explicit rational coefficient circuit a displayed
number of times.  This is the polynomial family `Z^2 = w^q` restricted to
the unit parameter circuit. -/
def repeatedLoop : Nat →
  Progressive.Chamber.Path.Basic.ChamberPath frame
  frame
  | 0 => .nil frame
  | circuits + 1 => (repeatedLoop circuits).append
    loop

/-- Repeat the certified positive generator in lockstep with the rational
polynomial circuit. -/
def repeatedBraid : (circuits : Nat) →
    CertifiedLoopBraid frame
      (repeatedLoop circuits)
  | 0 => .identity frame
  | circuits + 1 => (repeatedBraid circuits).append
    certifiedBraid

/-- Repeating the certified quadratic circuit retains exactly the corresponding repeated original word. -/
@[simp] theorem repeatedBraid_word (circuits : Nat) :
    (repeatedBraid circuits).word =
      Topology.Knot.Braid.Word.repeatWord word circuits := by
  induction circuits with
  | zero => rfl
  | succ circuits inductionHypothesis =>
      simp only [-eq_self, -iff_self, repeatedBraid,
        CertifiedLoopBraid.append,
        Topology.Knot.Braid.Word.repeatWord_succ, inductionHypothesis,
        certifiedBraid]
      rfl

/-- The repeated quadratic circuit's word has one crossing for each retained circuit. -/
@[simp] theorem repeatedBraid_crossingCount (circuits :
  Nat) :
    (repeatedBraid circuits).word.length = circuits := by
  rw [repeatedBraid_word, Topology.Knot.Braid.Word.repeatWord_length]
  simp only [word, List.length_cons, List.length_nil]
  omega

/-- The repeated positive quadratic circuit's word has writhe equal to its finite circuit count. -/
@[simp] theorem repeatedBraid_writhe (circuits : Nat) :
    (repeatedBraid circuits).word.writhe = (circuits : Int) := by
  rw [repeatedBraid_word, Topology.Knot.Braid.Word.repeatWord_writhe]
  simp only [-eq_self, -iff_self, word, Topology.Knot.Braid.Word.writhe_cons,
    Topology.Knot.Braid.Word.writhe_nil,
    Topology.Knot.Braid.Generator.weight, positiveGenerator,
    CrossingSign.weight, add_zero, mul_one]
  rfl

/-- The original certified quadratic circuit has a one-component braid closure. -/
theorem closure_isKnot :
  certifiedBraid.closure.IsKnot :=
  certifiedBraid.closure_isKnot_of_monodromy_isSingleCycle
    loop_isSingleCycle

end Purelib.RootIsolation.Progressive.Braid.Power.Quadratic

end
