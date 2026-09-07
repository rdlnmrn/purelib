import CCL.Arithmetic.BoxedNameProcess
import CCL.Progressive.MachineSemantics
import RFAP.Isolation.ShrinkingTrack

/-!
# Winding-one tracks as progressive arithmetic processes

Paper I supplies independently shrinking rational boxes without asserting a
completed root.  This module exposes each such finite track directly through
the CCL-2 squared-error process interface.  The possibility predicate is
the current box predicate itself; no point is selected from an intersection.
-/

namespace CCL.TrackProcess

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Named := CCL.ProgressiveTransducer.Named

/-- Convert one Paper-I winding-one track into an arbitrarily accurate finite
ball process. -/
def toProcess {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) : Process where
  State := WindingOneState p ambient
  ball state := CCL.ArithmeticEnclosures.Ball.ofBox state.box
  Possible state value := state.box.Contains value
  witness state := ⟨state.box.anchor, state.box.contains_anchor⟩
  possible_inside := by
    intro state value inside
    exact CCL.ArithmeticEnclosures.Ball.contains_ofBox inside
  refine state target positive :=
    track.refine state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value inside
    exact (track.nested state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive)).contains
        inside
  accurate := by
    intro state target positive
    exact (track.accurate state
      (CCL.BoxedNameProcess.accuracyRadius target)
      (CCL.BoxedNameProcess.accuracyRadius_pos positive)).trans_lt
        (CCL.BoxedNameProcess.accuracyRadius_sq_lt positive)
  centerBound := ambient.normSqBound
  centerBound_nonneg := ambient.normSqBound_nonneg
  center_bounded := by
    intro state
    exact ambient.normSq_le_normSqBound
      (state.refinesAmbient.contains state.box.contains_anchor)

@[simp] theorem toProcess_ball
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient) :
    (toProcess track).ball state =
      CCL.ArithmeticEnclosures.Ball.ofBox state.box := rfl

/-- Arithmetic entry point at any displayed state of the track. -/
def toNamedAt {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient) :
    Named :=
  { process := toProcess track
    state := state }

/-- Arithmetic entry point at the track's initial finite box. -/
def initialNamed {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) : Named :=
  toNamedAt track track.initial

/-- Start an arithmetic cursor at one explicitly requested later box of the
winding track.  This is the finite box-descent/CCL handoff used by CCL-2. -/
def refinedNamed
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) : Named :=
  toNamedAt track (track.refine state epsilon positive)

theorem initial_productive {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (count : Nat) :
    (initialNamed track).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (initialNamed track).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (initialNamed track).machine count).emitted.length = count :=
  (initialNamed track).productive count

theorem initial_grammar {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (initialNamed track).machine count) :=
  CCL.ProgressiveTransducerGrammar.Named.machine_advance_invariant
    (initialNamed track) count

/-- The finite arithmetic cursor started from any displayed winding box is
exact for a rational point admitted by that box. -/
theorem toNamedAt_exact
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient)
    (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (toProcess track) state
      (CCL.ProgressiveTransducer.advance
        (toNamedAt track state).machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact
    (toNamedAt track state) count

/-- Pointwise box/cursor compatibility: every quantitative tail after a
finite bit request reconstructs a displayed rational point of the source
winding box through the unchanged raw parser. -/
theorem toNamedAt_candidate_exact
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient)
    (count : Nat)
    {tail : RFAP.ConstructiveGaussian.Gaussian}
    (possible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (toNamedAt track state).machine count).mode tail) :
    ∃ value : RFAP.ConstructiveGaussian.Gaussian,
      state.box.Contains value ∧
        (CCL.Mat2.act
          (CCL.RawParser.parse
            (CCL.ProgressiveTransducerGrammar.Machine.committed
              (CCL.ProgressiveTransducer.advance
                (toNamedAt track state).machine count))).matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            (CCL.ProgressiveTransducer.advance
              (toNamedAt track state).machine count).mode tail)).Equivalent
                (CCL.Proj.affine value) := by
  exact CCL.ProgressiveMachineSemantics.Named.advance_candidate_exact
    (toNamedAt track state) count possible

/-- The exact raw-parser images of any two sidecar candidates after the same
finite request have squared chordal separation at most the source winding
box's squared diagonal.  This is the direct finite compatibility between the
box shrinker and the arithmetic CCL cursor. -/
theorem toNamedAt_cursor_chordalSq_le_box_diagonal
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient)
    (count : Nat) {leftTail rightTail : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (toNamedAt track state).machine count).mode leftTail)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (toNamedAt track state).machine count).mode rightTail) :
    let machine := CCL.ProgressiveTransducer.advance
      (toNamedAt track state).machine count
    let parser := CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
    CCL.Chordal.chordalSq
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode leftTail))
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ state.box.diagonalSq := by
  let machine := CCL.ProgressiveTransducer.advance
    (toNamedAt track state).machine count
  let parser := CCL.RawParser.parse
    (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
  rcases toNamedAt_candidate_exact track state count leftPossible with
    ⟨leftValue, leftInside, leftExact⟩
  rcases toNamedAt_candidate_exact track state count rightPossible with
    ⟨rightValue, rightInside, rightExact⟩
  have parserDeterminant :
      CCL.Chordal.Mat2.det parser.matrix ≠ 0 :=
    CCL.RawParser.parse_det_ne
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
  have leftValid := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    parserDeterminant
    (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail_valid
      machine.mode leftTail)
  have rightValid := CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    parserDeterminant
    (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail_valid
      machine.mode rightTail)
  dsimp only
  calc
    CCL.Chordal.chordalSq
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode leftTail))
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode rightTail)) =
        CCL.Chordal.chordalSq (CCL.Proj.affine leftValue)
          (CCL.Mat2.act parser.matrix
            (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
              machine.mode rightTail)) :=
      CCL.Chordal.chordalSq_eq_of_equivalent_left
        leftValid
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate leftValue)
        leftExact _
    _ = CCL.Chordal.chordalSq (CCL.Proj.affine leftValue)
        (CCL.Proj.affine rightValue) :=
      CCL.Chordal.chordalSq_eq_of_equivalent_right
        rightValid
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate rightValue)
        rightExact _
    _ ≤ state.box.diagonalSq :=
      CCL.Chordal.chordalSq_affine_le_box_diagonal
        leftInside rightInside

/-- At any requested box-descent accuracy, the corresponding arithmetic CCL
cursor has projective diameter at most the same displayed `epsilon^2`, for
every finite output length and every pair of admitted sidecar tails. -/
theorem refinedNamed_cursor_chordalSq_le_requested
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat)
    {leftTail rightTail : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (refinedNamed track state epsilon positive).machine count).mode
        leftTail)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (refinedNamed track state epsilon positive).machine count).mode
        rightTail) :
    let machine := CCL.ProgressiveTransducer.advance
      (refinedNamed track state epsilon positive).machine count
    let parser := CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
    CCL.Chordal.chordalSq
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode leftTail))
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ epsilon ^ 2 :=
  (toNamedAt_cursor_chordalSq_le_box_diagonal track
    (track.refine state epsilon positive) count leftPossible
      rightPossible).trans (track.accurate state epsilon positive)

/-- Initial-track specialization used by the RFAP bridge. -/
theorem initial_exact
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (toProcess track) track.initial
      (CCL.ProgressiveTransducer.advance
        (initialNamed track).machine count) :=
  toNamedAt_exact track track.initial count

end CCL.TrackProcess
