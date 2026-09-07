import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Transducer
import RFAP.Isolation.BoxFTA
import CCL.Bridge.TrackProcess
import CCL.Persistent.Track

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace CCL.BoxRFAPBridge

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.BoxFTA.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Frac := CCL.Integral.Frac
abbrev Block := CCL.Cylinder.Block
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Word := List Bool
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev BlockEncoding := CCL.Encoder.BlockEncoding
abbrev EncodingTransducer := CCL.Transducer.EncodingTransducer
abbrev PrefixState := CCL.Transducer.PrefixState

open CCL.Cylinder

/-- Coefficient-computable multiplier for the polynomial residual of any
nonzero rational sample returned from a winding-one box. -/
def residualConstant (p : GaussianPolynomial) (ambient : Box) : Coordinate :=
  4 * RFAP.PolynomialBounds.denseLipschitzBound p ambient

theorem residualConstant_nonneg (p : GaussianPolynomial) (ambient : Box) :
    0 ≤ residualConstant p ambient :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.PolynomialBounds.denseLipschitzBound_pos p ambient).le

/-- Complete finite CCL data for an exact nonzero Gaussian-rational root. -/
structure NonzeroTerminal (p : GaussianPolynomial) where
  point : Gaussian
  root : p.eval point = 0
  nonzero : point ≠ 0
  fraction : Frac
  fractionValue : fraction.value = point
  numeratorNonzero : fraction.num ≠ 0
  encoding : BlockEncoding fraction
  word : Word
  word_eq : word = rawWord encoding.blocks

/-- Construct the exact terminal record by running the terminating rational
CCL encoder once. -/
def nonzeroTerminal
    {p : GaussianPolynomial} (point : Gaussian) (root : p.eval point = 0)
    (nonzero : point ≠ 0) : NonzeroTerminal p := by
  let fraction := CCL.Integral.Frac.ofGaussian point
  let numeratorNonzero :=
    CCL.Integral.Frac.ofGaussian_num_ne_zero nonzero
  let encoding := CCL.Encoder.encodeBlocks fraction
    numeratorNonzero
  exact
    { point := point
      root := root
      nonzero := nonzero
      fraction := fraction
      fractionValue := CCL.Integral.Frac.ofGaussian_value point
      numeratorNonzero := numeratorNonzero
      encoding := encoding
      word := CCL.Encoder.encode fraction numeratorNonzero
      word_eq := CCL.Encoder.encode_eq_rawWord fraction
        numeratorNonzero }

namespace NonzeroTerminal

/-- Coherent incremental cursor through the exact terminal's complete CCL
word. -/
def transducer {p : GaussianPolynomial} (data : NonzeroTerminal p) :
    EncodingTransducer data.fraction :=
  CCL.Transducer.EncodingTransducer.initial data.encoding

theorem transducer_completeWord
    {p : GaussianPolynomial} (data : NonzeroTerminal p) :
    rawWord data.transducer.encoding.blocks = data.word :=
  data.word_eq.symm

end NonzeroTerminal

/-- Exact finite terminal state.  Zero has a distinguished tag because the
CCL encoder's input contract is nonzero. -/
inductive Terminal (p : GaussianPolynomial) where
  | zero (root : p.eval 0 = 0)
  | nonzero (data : NonzeroTerminal p)

/-- Turn any displayed exact root into the appropriate finite terminal tag. -/
def terminalOfExactRoot
    {p : GaussianPolynomial} (root : RFAP.BoxFTA.ExactRoot p) :
    Terminal p := by
  by_cases zero : root.point = 0
  · exact .zero (by simpa only [zero] using root.root)
  · exact .nonzero (nonzeroTerminal root.point root.root zero)

namespace Terminal

def point {p : GaussianPolynomial} : Terminal p → Gaussian
  | .zero _ => 0
  | .nonzero data => data.point

def word? {p : GaussianPolynomial} : Terminal p → Option Word
  | .zero _ => none
  | .nonzero data => some data.word

theorem eval_point {p : GaussianPolynomial} (terminal : Terminal p) :
    p.eval terminal.point = 0 := by
  cases terminal with
  | zero root => exact root
  | nonzero data => exact data.root

/-- Terminal states have exact zero polynomial residual. -/
theorem residual_zero {p : GaussianPolynomial} (terminal : Terminal p) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval terminal.point) = 0 := by
  rw [terminal.eval_point,
    RFAP.ConstructiveGaussian.Gaussian.normSq_zero]

/-- A nonzero terminal's completed blocks reconstruct its exact root. -/
theorem reconstruct
    {p : GaussianPolynomial} (data : NonzeroTerminal p) :
    data.encoding.point.Equivalent (CCL.Proj.affine data.point) := by
  rw [← data.fractionValue]
  exact data.encoding.reconstruct

end Terminal

/-! ## Unified exact terminal transducer -/

/-- A distinguished zero terminal, or a coherently advancing cursor through
the complete finite encoding of an exact nonzero rational root. -/
inductive TerminalTransducer (p : GaussianPolynomial) where
  | zero (root : p.eval 0 = 0)
  | nonzero (data : NonzeroTerminal p)
      (state : PrefixState (rawWord data.encoding.blocks))

namespace TerminalTransducer

def ofTerminal {p : GaussianPolynomial} : Terminal p → TerminalTransducer p
  | .zero root => .zero root
  | .nonzero data => .nonzero data data.transducer.state

def advance {p : GaussianPolynomial} :
    TerminalTransducer p → Nat → TerminalTransducer p
  | .zero root, _ => .zero root
  | .nonzero data state, count => .nonzero data (state.advance count)

def emitted? {p : GaussianPolynomial} : TerminalTransducer p → Option Word
  | .zero _ => none
  | .nonzero _ state => some state.emitted

def emittedLength {p : GaussianPolynomial} : TerminalTransducer p → Nat
  | .zero _ => 0
  | .nonzero _ state => state.emitted.length

def IsTerminal {p : GaussianPolynomial} : TerminalTransducer p → Prop
  | .zero _ => True
  | .nonzero _ state => state.IsTerminal

def remaining {p : GaussianPolynomial} : TerminalTransducer p → Nat
  | .zero _ => 0
  | .nonzero _ state => state.pending.length

/-- Prefix coherence also covers the distinguished zero state: it remains
the same non-word terminal under every request. -/
theorem advance_prefix {p : GaussianPolynomial}
    (transducer : TerminalTransducer p) (count : Nat) :
    match transducer.emitted?, (transducer.advance count).emitted? with
    | none, none => True
    | some earlier, some later => earlier.IsPrefix later
    | _, _ => False := by
  cases transducer with
  | zero root => exact True.intro
  | nonzero data state =>
      rcases state.advance_extends count with
        ⟨extension, extensionIdentity⟩
      exact ⟨extension, extensionIdentity.symm⟩

/-- Every exact-root transducer reaches a certified terminal state after its
explicit finite pending length; zero is terminal immediately. -/
theorem advance_remaining_terminal {p : GaussianPolynomial}
    (transducer : TerminalTransducer p) :
    (transducer.advance transducer.remaining).IsTerminal := by
  cases transducer with
  | zero root => exact True.intro
  | nonzero data state => exact state.advance_remaining_terminal

/-- Each exact-terminal request either appends exactly the requested number
of bits or reaches the terminal state. -/
theorem advance_progress_or_terminal {p : GaussianPolynomial}
    (transducer : TerminalTransducer p) (count : Nat) :
    (transducer.advance count).emittedLength =
        transducer.emittedLength + count ∨
      (transducer.advance count).IsTerminal := by
  cases transducer with
  | zero root => exact Or.inr True.intro
  | nonzero data state => exact state.advance_progress_or_terminal count

/-- At a nonzero terminal state all bits have been emitted and the stored
projective realization reconstructs the exact root. -/
theorem nonzero_terminal_spec
    {p : GaussianPolynomial} (data : NonzeroTerminal p)
    (state : PrefixState (rawWord data.encoding.blocks))
    (terminal : state.IsTerminal) :
    state.emitted = data.word ∧
      data.encoding.point.Equivalent (CCL.Proj.affine data.point) := by
  constructor
  · rw [state.emitted_eq_complete_of_terminal terminal]
    exact data.word_eq.symm
  · rw [← data.fractionValue]
    exact data.encoding.reconstruct

end TerminalTransducer

/-- One total finite box-refinement request together with the exact CCL code
of a displayed nonzero sample of the returned box. -/
structure Request
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) where
  next : WindingOneState p ambient
  nested : next.box.Refines current.box
  accurate : next.box.diagonalSq ≤ epsilon ^ 2
  sample : RFAP.Boxes.Box.NonzeroSample next.box
  fraction : Frac
  fractionValue : fraction.value = sample.point
  numeratorNonzero : fraction.num ≠ 0
  encoding : BlockEncoding fraction
  word : Word
  word_eq : word = rawWord encoding.blocks

/-- Execute a coupled request using only the supplied track's finite
refinement program and the choice-free canonical fraction representative. -/
def request
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Request track current epsilon positive := by
  let next := track.refine current epsilon positive
  let sample := next.box.nonzeroSample next.proper
  let fraction := CCL.Integral.Frac.ofGaussian sample.point
  let numeratorNonzero :=
    CCL.Integral.Frac.ofGaussian_num_ne_zero sample.nonzero
  let encoding := CCL.Encoder.encodeBlocks fraction
    numeratorNonzero
  let word := CCL.Encoder.encode fraction numeratorNonzero
  exact
    { next := next
      nested := track.nested current epsilon positive
      accurate := track.accurate current epsilon positive
      sample := sample
      fraction := fraction
      fractionValue := CCL.Integral.Frac.ofGaussian_value
        sample.point
      numeratorNonzero := numeratorNonzero
      encoding := encoding
      word := word
      word_eq := CCL.Encoder.encode_eq_rawWord fraction
        numeratorNonzero }

namespace Request

/-- Coherent incremental cursor through this request's exact finite sample
encoding. -/
def transducer
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive) :
    EncodingTransducer result.fraction :=
  CCL.Transducer.EncodingTransducer.initial result.encoding

theorem transducer_completeWord
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive) :
    rawWord result.transducer.encoding.blocks = result.word :=
  result.word_eq.symm

theorem transducer_advance_extends
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive) (count : Nat) :
    ∃ extension : Word,
      (result.transducer.advance count).state.emitted =
        result.transducer.state.emitted ++ extension :=
  result.transducer.advance_extends count

theorem transducer_reaches_terminal
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive) :
    (result.transducer.advance
      result.transducer.state.pending.length).IsTerminal :=
  result.transducer.advance_remaining_terminal

/-- The CCL homogeneous realization reconstructs the displayed box sample. -/
theorem reconstructSample
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive) :
    result.encoding.point.Equivalent
      (CCL.Proj.affine result.sample.point) := by
  rw [← result.fractionValue]
  exact result.encoding.reconstruct

/-- Every explicitly supplied point in the returned root box is within its
squared diagonal of the encoded rational sample. -/
theorem boxError
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    {point : Gaussian} (inside : result.next.box.Contains point) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point - result.sample.point) ≤ result.next.box.diagonalSq :=
  RFAP.Boxes.Box.normSq_sub_le_diagonalSq
    inside result.sample.inside

/-- The numerical part of a coupled request meets the requested error. -/
theorem boxError_le_requested
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    {point : Gaussian} (inside : result.next.box.Contains point) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (point - result.sample.point) ≤ epsilon ^ 2 :=
  (result.boxError inside).trans result.accurate

/-- Any second finite realization of the same completed block list lies in
the explicit shrinking projective cylinder around this request. -/
theorem cylinderBound
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    {other : Proj}
    (otherRealizes : ProjectiveRealizes result.encoding.blocks other) :
    CCL.Chordal.chordalSq result.encoding.point other ≤
      (1 / 2 : Coordinate) ^ result.encoding.blocks.length :=
  ProjectiveRealizes.chordalSq_le_half_pow
    result.encoding.realizes otherRealizes

/-- A CCL request's displayed rational sample has residual of the same
coefficient-linear order as the squared diagonal of its winding-one box. -/
theorem sampleResidual
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    (degreePositive : 0 < p.natDegree) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval result.sample.point) ≤
      residualConstant p ambient * result.next.box.diagonalSq := by
  let bound :=
    RFAP.LocalExtraction.anchorResidualBound
      p ambient result.next.box
  have anchorResidual :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval result.next.box.anchor) ≤ bound :=
    RFAP.LocalExtraction.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      p degreePositive result.next.refinesAmbient result.next.proper
        result.next.raw.rawWinding_ne
  have variation :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval result.sample.point - p.eval result.next.box.anchor) ≤
        bound :=
    RFAP.LocalExtraction.normSq_eval_sub_anchor_le
      p result.next.refinesAmbient result.sample.inside
  have decomposition :
      (p.eval result.sample.point - p.eval result.next.box.anchor) +
          p.eval result.next.box.anchor = p.eval result.sample.point := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;>
      ring1
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval result.sample.point) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          ((p.eval result.sample.point - p.eval result.next.box.anchor) +
            p.eval result.next.box.anchor) := by rw [decomposition]
    _ ≤ 2 *
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            (p.eval result.sample.point - p.eval result.next.box.anchor) +
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (p.eval result.next.box.anchor)) :=
      RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
    _ ≤ 2 * (bound + bound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add variation anchorResidual) (by decide)
    _ = residualConstant p ambient * result.next.box.diagonalSq := by
      simp only [bound,
        RFAP.LocalExtraction.anchorResidualBound,
        residualConstant]
      ring1

/-- The residual certificate also meets the requested squared accuracy after
scaling by the fixed coefficient-computable constant. -/
theorem sampleResidual_le_requested
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    (degreePositive : 0 < p.natDegree) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval result.sample.point) ≤
      residualConstant p ambient * epsilon ^ 2 :=
  (result.sampleResidual degreePositive).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      result.accurate (residualConstant_nonneg p ambient))

/-- Consecutive CCL requests move their displayed rational samples by at
most the squared diagonal of the earlier returned box. -/
theorem nextSampleMovement
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    {nextEpsilon : Coordinate} {nextPositive : 0 < nextEpsilon}
    (later : Request track result.next nextEpsilon nextPositive) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (later.sample.point - result.sample.point) ≤
      result.next.box.diagonalSq :=
  RFAP.Boxes.Box.normSq_sub_le_diagonalSq
    (later.nested.contains later.sample.inside) result.sample.inside

/-- Consecutive returned samples therefore move by at most the earlier
request's squared accuracy target. -/
theorem nextSampleMovement_le_requested
    {p : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack p ambient}
    {current : WindingOneState p ambient}
    {epsilon : Coordinate} {positive : 0 < epsilon}
    (result : Request track current epsilon positive)
    {nextEpsilon : Coordinate} {nextPositive : 0 < nextEpsilon}
    (later : Request track result.next nextEpsilon nextPositive) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (later.sample.point - result.sample.point) ≤ epsilon ^ 2 :=
  (result.nextSampleMovement later).trans result.accurate

end Request

/-- Public coupled result.  Its numerical family is exactly the standalone
box result; the CCL request interface adds finite encodings without changing
the root count or maximality theorem. -/
structure Result (p : GaussianPolynomial) where
  boxes : RFAP.BoxFTA.Result p

/-- Unified positive-degree CCL result: an exact finite terminal for a
linear polynomial, or the degree-many active family in higher degree. -/
inductive PositiveResult (p : GaussianPolynomial) where
  | terminal (state : Terminal p) (degree : p.natDegree = 1)
  | higher (result : Result p) (degree : 2 ≤ p.natDegree)

/-- Choice-free degree-many box isolation equipped with finite CCL requests. -/
def prove {p : GaussianPolynomial}
    (input : RFAP.BoxFTA.Input p) : Result p :=
  ⟨RFAP.BoxFTA.prove input⟩

/-- Degree-greater-than-one specialization from explicit finite squarefree
Bézout data. -/
def proveDegreeGtOne {p : GaussianPolynomial}
    (squarefree : RFAP.BoxFTA.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : Result p :=
  prove ⟨squarefree, degree⟩

/-- Integrate exact linear terminals with the box/CCL family constructor. -/
def provePositive {p : GaussianPolynomial}
    (input : RFAP.BoxFTA.PositiveInput p) : PositiveResult p :=
  match RFAP.BoxFTA.provePositive input with
  | .linear root degree => .terminal (terminalOfExactRoot root) degree
  | .higher boxes degree => .higher ⟨boxes⟩ degree

/-- Degree-greater-than-one specialization of the unified result. -/
def provePositiveDegreeGtOne
    {p : GaussianPolynomial}
    (squarefree : RFAP.BoxFTA.SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : PositiveResult p :=
  .higher (proveDegreeGtOne squarefree degree) degree

namespace Result

/-- Degree-indexed access to the independently shrinking numerical track. -/
def trackAt {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) :
    WindingOneTrack p (RFAP.GlobalWinding.largeSquareBox p) :=
  result.boxes.isolation.trackAt index

/-- Persistent joint box/cylinder state for one degree-indexed higher root
site.  The state is intended to be fed back into every later request. -/
abbrev PersistentStateAt {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) :=
  CCL.PersistentTrack.State (result.trackAt index)

/-- Begin the joint request history at the track's initial isolated box and
the empty raw prefix. -/
def persistentStateAt {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) : result.PersistentStateAt index :=
  CCL.PersistentTrack.State.initial (result.trackAt index)

/-- Refine the preceding numerical box, append exactly `count` bits to the
same arithmetic cursor, and contract its quantitative cylinder below the
same displayed `epsilon^2`. -/
def persistentRequestAt
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    result.PersistentStateAt index :=
  current.request epsilon positive count

theorem persistentRequestAt_refines
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    CCL.PersistentTrack.Refines
      (result.persistentRequestAt index current epsilon positive count)
      current :=
  current.request_refines epsilon positive count

theorem persistentRequestAt_box_accurate
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    (result.persistentRequestAt index current epsilon positive count).numerical.box.diagonalSq
      ≤ epsilon ^ 2 :=
  current.request_box_accurate epsilon positive count

theorem persistentRequestAt_word_length
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat) :
    (result.persistentRequestAt index current epsilon positive count).cursor.machine.emitted.length =
      current.cursor.machine.emitted.length + count :=
  current.request_word_length epsilon positive count

theorem persistentRequestAt_cylinder_accurate
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat)
    {left right : Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          left)
        (CCL.PersistentProgressive.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          right) ≤ epsilon ^ 2 :=
  current.request_cylinder_accurate epsilon positive count
    leftPossible rightPossible

/-- Every admitted cylinder candidate remains owned by this degree-indexed
initial isolated region.  This is the finite compatibility assertion used to
identify the persistent cylinder with the same Paper-I site. -/
theorem persistentRequestAt_candidate_in_initial_box
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat)
    {tail : Gaussian}
    (possible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        tail) :
    ∃ value : Gaussian,
      (result.trackAt index).initial.box.Contains value ∧
        (CCL.PersistentProgressive.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          tail).Equivalent (CCL.Proj.affine value) :=
  (result.persistentRequestAt index current epsilon positive count).candidate_in_initial_box
    possible

/-- A higher-degree Paper-I root track, exposed directly as a progressive
squared-error arithmetic name without extracting a completed root. -/
def arithmeticNameAt {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) :
    CCL.ProgressiveTransducer.Named :=
  CCL.TrackProcess.initialNamed (result.trackAt index)

/-- Start the CCL arithmetic cursor at an explicitly requested later RFAP
root box. -/
def refinedArithmeticNameAt
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree)
    (current : WindingOneState p (RFAP.GlobalWinding.largeSquareBox p))
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    CCL.ProgressiveTransducer.Named :=
  CCL.TrackProcess.refinedNamed (result.trackAt index)
    current epsilon positive

theorem arithmeticNameAt_productive
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (count : Nat) :
    (result.arithmeticNameAt index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (result.arithmeticNameAt index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (result.arithmeticNameAt index).machine count).emitted.length =
        count :=
  CCL.TrackProcess.initial_productive (result.trackAt index) count

theorem arithmeticNameAt_grammar
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (count : Nat) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (CCL.ProgressiveTransducer.advance
        (result.arithmeticNameAt index).machine count) :=
  CCL.TrackProcess.initial_grammar (result.trackAt index) count

/-- The productive arithmetic cursor of every degree-indexed RFAP root track
also carries the exact projective semantics of that track's initial box. -/
theorem arithmeticNameAt_exact
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (CCL.TrackProcess.toProcess (result.trackAt index))
      (result.trackAt index).initial
      (CCL.ProgressiveTransducer.advance
        (result.arithmeticNameAt index).machine count) :=
  CCL.TrackProcess.initial_exact (result.trackAt index) count

/-- Pointwise form: every admitted arithmetic tail after a finite request
reconstructs a rational point inside the corresponding Paper-I initial root
box.  It does not assert the existence of a completed root value. -/
theorem arithmeticNameAt_candidate_exact
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (count : Nat)
    {tail : Gaussian}
    (possible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (result.arithmeticNameAt index).machine count).mode tail) :
    ∃ value : Gaussian,
      (result.trackAt index).initial.box.Contains value ∧
        (CCL.Mat2.act
          (CCL.RawParser.parse
            (CCL.ProgressiveTransducerGrammar.Machine.committed
              (CCL.ProgressiveTransducer.advance
                (result.arithmeticNameAt index).machine count))).matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            (CCL.ProgressiveTransducer.advance
              (result.arithmeticNameAt index).machine count).mode tail)).Equivalent
                (CCL.Proj.affine value) :=
  CCL.TrackProcess.toNamedAt_candidate_exact
    (result.trackAt index) (result.trackAt index).initial count possible

/-- The projective diameter represented by any two quantitative tails of one
RFAP root cursor is bounded by that root track's initial box diagonal. -/
theorem arithmeticNameAt_cursor_chordalSq_le_box_diagonal
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree) (count : Nat)
    {leftTail rightTail : Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (result.arithmeticNameAt index).machine count).mode leftTail)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (result.arithmeticNameAt index).machine count).mode rightTail) :
    let machine := CCL.ProgressiveTransducer.advance
      (result.arithmeticNameAt index).machine count
    let parser := CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
    CCL.Chordal.chordalSq
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode leftTail))
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤
      (result.trackAt index).initial.box.diagonalSq :=
  CCL.TrackProcess.toNamedAt_cursor_chordalSq_le_box_diagonal
    (result.trackAt index) (result.trackAt index).initial count
      leftPossible rightPossible

/-- The box descent and arithmetic cursor can be coupled at every displayed
accuracy: all admitted parser images lie within squared chordal diameter
`epsilon^2`. -/
theorem refinedArithmeticNameAt_cursor_chordalSq_le_requested
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree)
    (current : WindingOneState p (RFAP.GlobalWinding.largeSquareBox p))
    (epsilon : Coordinate) (positive : 0 < epsilon) (count : Nat)
    {leftTail rightTail : Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (result.refinedArithmeticNameAt index current epsilon positive).machine
          count).mode leftTail)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (CCL.ProgressiveTransducer.advance
          (result.refinedArithmeticNameAt index current epsilon positive).machine
          count).mode rightTail) :
    let machine := CCL.ProgressiveTransducer.advance
      (result.refinedArithmeticNameAt index current epsilon positive).machine
      count
    let parser := CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine)
    CCL.Chordal.chordalSq
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode leftTail))
        (CCL.Mat2.act parser.matrix
          (CCL.ProgressiveMachineSemantics.SemanticMode.parserTail
            machine.mode rightTail)) ≤ epsilon ^ 2 :=
  CCL.TrackProcess.refinedNamed_cursor_chordalSq_le_requested
    (result.trackAt index) current epsilon positive count
      leftPossible rightPossible

theorem trackAt_pairwiseSeparated
    {p : GaussianPolynomial} (result : Result p)
    (left right : Fin p.natDegree) (different : left ≠ right) :
    (result.trackAt left).initial.box.Separated
      (result.trackAt right).initial.box :=
  result.boxes.isolation.trackAt_pairwiseSeparated left right different

/-- Run a finite box/CCL request from any current state of one output track. -/
def requestAt
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree)
    (current : WindingOneState p
      (RFAP.GlobalWinding.largeSquareBox p))
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Request (result.trackAt index) current epsilon positive :=
  request (result.trackAt index) current epsilon positive

/-- First coupled request on a selected degree-indexed output track. -/
def initialRequestAt
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Request (result.trackAt index) (result.trackAt index).initial
      epsilon positive :=
  result.requestAt index (result.trackAt index).initial epsilon positive

/-- Public degree-indexed residual bound, with degree positivity recovered
constructively from the displayed finite index. -/
theorem requestAt_sampleResidual
    {p : GaussianPolynomial} (result : Result p)
    (index : Fin p.natDegree)
    (current : WindingOneState p
      (RFAP.GlobalWinding.largeSquareBox p))
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (result.requestAt index current epsilon positive).sample.point) ≤
      residualConstant p
          (RFAP.GlobalWinding.largeSquareBox p) *
        (result.requestAt index current epsilon positive).next.box.diagonalSq :=
  (result.requestAt index current epsilon positive).sampleResidual
    (Nat.zero_lt_of_lt index.isLt)

end Result

/-- Two first requests on distinct tracks, retaining the finite positive
box-separation certificate and the resulting distinct encoded samples. -/
structure PairRequest
    {p : GaussianPolynomial} (result : Result p)
    (left right : Fin p.natDegree) (different : left ≠ right)
    (leftEpsilon rightEpsilon : Coordinate)
    (leftPositive : 0 < leftEpsilon)
    (rightPositive : 0 < rightEpsilon) where
  leftRequest : Request (result.trackAt left)
    (result.trackAt left).initial leftEpsilon leftPositive
  rightRequest : Request (result.trackAt right)
    (result.trackAt right).initial rightEpsilon rightPositive
  boxesSeparated : leftRequest.next.box.Separated rightRequest.next.box
  samplesDifferent : leftRequest.sample.point ≠ rightRequest.sample.point

/-- Independently refine and encode two distinct degree-indexed tracks. -/
def Result.requestPairAt
    {p : GaussianPolynomial} (result : Result p)
    (left right : Fin p.natDegree) (different : left ≠ right)
    (leftEpsilon rightEpsilon : Coordinate)
    (leftPositive : 0 < leftEpsilon)
    (rightPositive : 0 < rightEpsilon) :
    PairRequest result left right different leftEpsilon rightEpsilon
      leftPositive rightPositive := by
  let leftRequest := result.initialRequestAt left leftEpsilon leftPositive
  let rightRequest := result.initialRequestAt right rightEpsilon rightPositive
  have boxesSeparated : leftRequest.next.box.Separated
      rightRequest.next.box :=
    RFAP.Boxes.Box.Separated.of_refines
      (result.trackAt_pairwiseSeparated left right different)
      leftRequest.nested rightRequest.nested
  exact
    { leftRequest := leftRequest
      rightRequest := rightRequest
      boxesSeparated := boxesSeparated
      samplesDifferent := boxesSeparated.points_ne
        leftRequest.sample.inside rightRequest.sample.inside }

end CCL.BoxRFAPBridge
