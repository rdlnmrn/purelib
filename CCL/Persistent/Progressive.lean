import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.MachineSemantics

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace CCL.PersistentProgressive

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Mode := CCL.ProgressiveTransducer.Mode
abbrev Machine := CCL.ProgressiveTransducer.Machine
abbrev ExactCursor :=
  CCL.ProgressiveMachineSemantics.ExactCursor

open RFAP.ConstructiveGaussian.Gaussian
open CCL.ProgressiveTransducer
open CCL.ProgressiveMachineSemantics

namespace Mode

/-- The rational ball displayed by the finite process state in one live mode. -/
def ball : Mode → CCL.ArithmeticEnclosures.Ball
  | .initial current => current.process.ball current.state
  | .low current => current.process.ball current.state
  | .loop current => current.process.ball current.state
  | .residual current => current.process.ball current.state

/-- Refine only the live finite process state.  Syntax counters, chart data,
and every raw bit remain unchanged. -/
def refine : (mode : Mode) → (target : Coordinate) → 0 < target → Mode
  | .initial current, target, positive =>
      .initial
        { process := current.process
          state := current.process.refine current.state target positive }
  | .low current, target, positive =>
      .low
        { count := current.count
          process := current.process
          state := current.process.refine current.state target positive
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                possible) }
  | .loop current, target, positive =>
      .loop
        { kind := current.kind
          count := current.count
          process := current.process
          state := current.process.refine current.state target positive
          domain := current.domain }
  | .residual current, target, positive =>
      .residual
        { process := current.process
          state := current.process.refine current.state target positive
          count := current.count
          upper := current.upper
          upperBound := by
            intro value possible
            exact current.upperBound
              (current.process.refine_persists current.state target positive
                possible)
          upperStrict := current.upperStrict }

theorem refine_possible
    (mode : Mode) (target : Coordinate) (positive : 0 < target)
    {value : Gaussian}
    (possible : SemanticMode.possible (Mode.refine mode target positive) value) :
    SemanticMode.possible mode value := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.refine_persists current.state target positive
        possible

theorem refine_ball_radiusSq_lt
    (mode : Mode) (target : Coordinate) (positive : 0 < target) :
    (Mode.ball (Mode.refine mode target positive)).radiusSq < target := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.accurate current.state target positive

theorem possible_inside
    (mode : Mode) {value : Gaussian}
    (possible : SemanticMode.possible mode value) :
    (Mode.ball mode).Contains value := by
  cases mode with
  | initial current | low current | loop current | residual current =>
      exact current.process.possible_inside possible

@[simp] theorem refine_parserTail
    (mode : Mode) (target : Coordinate) (positive : 0 < target)
    (value : Gaussian) :
    SemanticMode.parserTail (Mode.refine mode target positive) value =
      SemanticMode.parserTail mode value := by
  cases mode <;> rfl

@[simp] theorem refine_rawPhase
    (mode : Mode) (target : Coordinate) (positive : 0 < target) :
    CCL.ProgressiveTransducerGrammar.modeRawPhase
        (Mode.refine mode target positive) =
      CCL.ProgressiveTransducerGrammar.modeRawPhase mode := by
  cases mode <;> rfl

/-- Linear homogeneous chart which turns an affine live-process candidate
into the projective tail prescribed by the current mode. -/
def tailMatrix : Mode → Mat2
  | .initial _ => CCL.RawParser.identityMatrix
  | .low current =>
      CCL.Mat2.scale
        (RFAP.ConstructiveGaussian.Gaussian.natPow gamma current.count)⁻¹
  | .loop current =>
      CCL.Mat2.scale
        (RFAP.ConstructiveGaussian.Gaussian.natPow gamma current.count)
  | .residual _ => CCL.Mat2.invert gamma

theorem tailMatrix_act (mode : Mode) (value : Gaussian) :
    CCL.Mat2.act (Mode.tailMatrix mode) (CCL.Proj.affine value) =
      SemanticMode.parserTail mode value := by
  cases mode with
  | initial current =>
      apply CCL.Proj.ext <;>
        simp [tailMatrix, CCL.RawParser.identityMatrix,
          CCL.Mat2.act, CCL.Proj.affine,
          CCL.ProgressiveMachineSemantics.SemanticMode.parserTail]
  | low current | loop current =>
      apply CCL.Proj.ext <;>
        simp [tailMatrix, CCL.Mat2.act, CCL.Mat2.scale, CCL.Proj.affine,
          CCL.ProgressiveMachineSemantics.SemanticMode.parserTail]
  | residual current =>
      apply CCL.Proj.ext <;>
        simp [tailMatrix, CCL.Mat2.act, CCL.Mat2.invert, CCL.Proj.affine,
          CCL.ProgressiveMachineSemantics.SemanticMode.parserTail]

theorem tailMatrix_det_ne (mode : Mode) :
    CCL.Chordal.Mat2.det (Mode.tailMatrix mode) ≠ 0 := by
  cases mode with
  | initial current =>
      simp [tailMatrix, CCL.RawParser.identityMatrix,
        CCL.Chordal.Mat2.det]
  | low current =>
      simp only [tailMatrix, CCL.Mat2.scale,
        CCL.Chordal.Mat2.det,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.sub_zero]
      exact RFAP.ConstructiveGaussian.Gaussian.inv_ne_zero_direct
        (RFAP.ConstructiveGaussian.Gaussian.natPow_ne_zero_direct gamma
          (by decide) current.count)
  | loop current =>
      simp only [tailMatrix, CCL.Mat2.scale,
        CCL.Chordal.Mat2.det,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.sub_zero]
      exact RFAP.ConstructiveGaussian.Gaussian.natPow_ne_zero_direct gamma
        (by decide) current.count
  | residual current =>
      simp only [tailMatrix, CCL.Mat2.invert,
        CCL.Chordal.Mat2.det,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]
      exact RFAP.ConstructiveGaussian.Gaussian.neg_ne_zero_direct
        (show gamma ≠ 0 by decide)

@[simp] theorem refine_tailMatrix
    (mode : Mode) (target : Coordinate) (positive : 0 < target) :
    Mode.tailMatrix (Mode.refine mode target positive) = Mode.tailMatrix mode := by
  cases mode <;> rfl

end Mode

namespace Machine

/-- Refine the quantitative sidecar of an already-running cursor without
changing its finite raw word or buffer. -/
def refine (machine : Machine) (target : Coordinate) (positive : 0 < target) :
    Machine :=
  { mode := Mode.refine machine.mode target positive
    emitted := machine.emitted
    pending := machine.pending }

@[simp] theorem refine_emitted
    (machine : Machine) (target : Coordinate) (positive : 0 < target) :
    (machine.refine target positive).emitted = machine.emitted := rfl

@[simp] theorem refine_pending
    (machine : Machine) (target : Coordinate) (positive : 0 < target) :
    (machine.refine target positive).pending = machine.pending := rfl

@[simp] theorem refine_committed
    (machine : Machine) (target : Coordinate) (positive : 0 < target) :
    CCL.ProgressiveTransducerGrammar.Machine.committed
        (machine.refine target positive) =
      CCL.ProgressiveTransducerGrammar.Machine.committed machine :=
  rfl

theorem refine_grammar
    (machine : Machine) (target : Coordinate) (positive : 0 < target)
    (grammar :
      CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
        machine) :
    CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
      (machine.refine target positive) := by
  unfold CCL.ProgressiveTransducerGrammar.Machine.GrammarInvariant
    at grammar ⊢
  change
    (CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed
        machine)).phase =
      CCL.ProgressiveTransducerGrammar.modeRawPhase
        (Mode.refine machine.mode target positive)
  rw [Mode.refine_rawPhase]
  exact grammar

/-- The single matrix taking an affine live-process candidate to the current
ordinary raw-parser image. -/
def imageMatrix (machine : Machine) : Mat2 :=
  CCL.Mat2.mul
    (CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed
        machine)).matrix
    (Mode.tailMatrix machine.mode)

/-- Projective point represented by one admitted quantitative candidate of
the current finite cursor. -/
def image (machine : Machine) (value : Gaussian) : Proj :=
  CCL.Mat2.act
    (CCL.RawParser.parse
      (CCL.ProgressiveTransducerGrammar.Machine.committed
        machine)).matrix
    (SemanticMode.parserTail machine.mode value)

theorem image_eq_act_imageMatrix (machine : Machine) (value : Gaussian) :
    machine.image value =
      CCL.Mat2.act machine.imageMatrix (CCL.Proj.affine value) := by
  rw [image, imageMatrix, CCL.Mat2.act_mul, Mode.tailMatrix_act]

theorem imageMatrix_det_ne (machine : Machine) :
    CCL.Chordal.Mat2.det machine.imageMatrix ≠ 0 := by
  rw [imageMatrix, CCL.RawParser.det_mul]
  exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (CCL.RawParser.parse_det_ne
      (CCL.ProgressiveTransducerGrammar.Machine.committed machine))
    (Mode.tailMatrix_det_ne machine.mode)

@[simp] theorem refine_imageMatrix
    (machine : Machine) (target : Coordinate) (positive : 0 < target) :
    (machine.refine target positive).imageMatrix = machine.imageMatrix := by
  change CCL.Mat2.mul
      (CCL.RawParser.parse
        (CCL.ProgressiveTransducerGrammar.Machine.committed
          machine)).matrix
      (Mode.tailMatrix (Mode.refine machine.mode target positive)) =
    CCL.Mat2.mul
      (CCL.RawParser.parse
        (CCL.ProgressiveTransducerGrammar.Machine.committed
          machine)).matrix
      (Mode.tailMatrix machine.mode)
  rw [Mode.refine_tailMatrix]

/-- Positive rational radius request which absorbs the exact finite
condition coefficient of the cursor's current projective chart. -/
def cylinderBallTarget (machine : Machine) (epsilonSq : Coordinate) :
    Coordinate :=
  epsilonSq /
    (4 * CCL.TerminalPadding.transportCoefficient
      machine.imageMatrix)

theorem cylinderBallTarget_pos
    (machine : Machine) {epsilonSq : Coordinate} (positive : 0 < epsilonSq) :
    0 < machine.cylinderBallTarget epsilonSq := by
  apply RFAP.ConstructiveFraction.div_pos_direct positive
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    (CCL.TerminalPadding.transportCoefficient_pos
      machine.imageMatrix machine.imageMatrix_det_ne)

/-- Accuracy-only request on one persistent cursor. -/
def refineCylinder
    (machine : Machine) (epsilonSq : Coordinate) (positive : 0 < epsilonSq) :
    Machine :=
  machine.refine (machine.cylinderBallTarget epsilonSq)
    (machine.cylinderBallTarget_pos positive)

@[simp] theorem refineCylinder_emitted
    (machine : Machine) (epsilonSq : Coordinate) (positive : 0 < epsilonSq) :
    (machine.refineCylinder epsilonSq positive).emitted = machine.emitted := rfl

@[simp] theorem refineCylinder_committed
    (machine : Machine) (epsilonSq : Coordinate) (positive : 0 < epsilonSq) :
    CCL.ProgressiveTransducerGrammar.Machine.committed
        (machine.refineCylinder epsilonSq positive) =
      CCL.ProgressiveTransducerGrammar.Machine.committed machine :=
  rfl

/-- Every two candidates admitted after the accuracy-only refinement have
the requested squared-chordal diameter through the same persistent raw
prefix. -/
theorem refineCylinder_pair_chordalSq_le
    (machine : Machine) (epsilonSq : Coordinate) (positive : 0 < epsilonSq)
    {left right : Gaussian}
    (leftPossible : SemanticMode.possible
      (machine.refineCylinder epsilonSq positive).mode left)
    (rightPossible : SemanticMode.possible
      (machine.refineCylinder epsilonSq positive).mode right) :
    CCL.Chordal.chordalSq
        ((machine.refineCylinder epsilonSq positive).image left)
        ((machine.refineCylinder epsilonSq positive).image right) ≤
      epsilonSq := by
  let coefficient :=
    CCL.TerminalPadding.transportCoefficient machine.imageMatrix
  let target := machine.cylinderBallTarget epsilonSq
  let refined := machine.refineCylinder epsilonSq positive
  have coefficientPositive : 0 < coefficient :=
    CCL.TerminalPadding.transportCoefficient_pos
      machine.imageMatrix machine.imageMatrix_det_ne
  have targetPositive : 0 < target := machine.cylinderBallTarget_pos positive
  have radiusSmall : (Mode.ball refined.mode).radiusSq < target := by
    exact Mode.refine_ball_radiusSq_lt machine.mode target targetPositive
  have leftInside := Mode.possible_inside refined.mode leftPossible
  have rightInside := Mode.possible_inside refined.mode rightPossible
  have centerRight :
      normSq ((Mode.ball refined.mode).center - right) =
        normSq (right - (Mode.ball refined.mode).center) := by
    have negated : (Mode.ball refined.mode).center - right =
        -(right - (Mode.ball refined.mode).center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
        ring1
    rw [negated, normSq_neg]
  have pairDistance : normSq (left - right) ≤
      4 * (Mode.ball refined.mode).radiusSq := by
    calc
      normSq (left - right) ≤
          2 * (normSq (left - (Mode.ball refined.mode).center) +
            normSq ((Mode.ball refined.mode).center - right)) :=
        normSq_sub_le_via left (Mode.ball refined.mode).center right
      _ = 2 * (normSq (left - (Mode.ball refined.mode).center) +
            normSq (right - (Mode.ball refined.mode).center)) := by
        rw [centerRight]
      _ ≤ 2 * ((Mode.ball refined.mode).radiusSq +
            (Mode.ball refined.mode).radiusSq) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftInside rightInside) (by decide)
      _ = 4 * (Mode.ball refined.mode).radiusSq := by ring1
  have scaledRadius :
      (Mode.ball refined.mode).radiusSq * (4 * coefficient) < epsilonSq := by
    exact (RFAP.ConstructiveFraction.lt_div_iff_pos
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        coefficientPositive)).1 radiusSmall
  have transported :=
    CCL.TerminalPadding.chordalSq_act_le_transportCoefficient
      machine.imageMatrix machine.imageMatrix_det_ne
      (CCL.Proj.affine left) (CCL.Proj.affine right)
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate left)
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate right)
  change CCL.Chordal.chordalSq
      (refined.image left) (refined.image right) ≤ epsilonSq
  apply le_of_lt
  calc
    CCL.Chordal.chordalSq (refined.image left)
        (refined.image right) =
        CCL.Chordal.chordalSq
          (CCL.Mat2.act machine.imageMatrix (CCL.Proj.affine left))
          (CCL.Mat2.act machine.imageMatrix (CCL.Proj.affine right)) := by
      rw [refined.image_eq_act_imageMatrix,
        refined.image_eq_act_imageMatrix]
      simp only [refined, refineCylinder, Machine.refine_imageMatrix]
    _ ≤ coefficient *
        CCL.Chordal.chordalSq
          (CCL.Proj.affine left) (CCL.Proj.affine right) := transported
    _ ≤ coefficient * normSq (left - right) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (CCL.Chordal.chordalSq_affine_le_normSq left right)
        coefficientPositive.le
    _ ≤ coefficient * (4 * (Mode.ball refined.mode).radiusSq) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        pairDistance coefficientPositive.le
    _ < epsilonSq := by
      calc
        coefficient * (4 * (Mode.ball refined.mode).radiusSq) =
            (Mode.ball refined.mode).radiusSq * (4 * coefficient) := by ring1
        _ < epsilonSq := scaledRadius

end Machine

namespace ExactCursor

/-- Refining only the sidecar preserves exact parser semantics for the same
origin finite state. -/
theorem refine
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine)
    (target : Coordinate) (positive : 0 < target) :
    ExactCursor origin originState (machine.refine target positive) := by
  refine
    { grammar := machine.refine_grammar target positive cursor.grammar
      exact := ?_ }
  intro tail possible
  change SemanticMode.possible
    (Mode.refine machine.mode target positive) tail at possible
  have previousPossible :=
    Mode.refine_possible machine.mode target positive possible
  change ∃ value : Gaussian,
    origin.Possible originState value ∧
      (CCL.Mat2.act
        (CCL.RawParser.parse
          (CCL.ProgressiveTransducerGrammar.Machine.committed
            machine)).matrix
        (SemanticMode.parserTail
          (Mode.refine machine.mode target positive) tail)).Equivalent
            (CCL.Proj.affine value)
  rw [Mode.refine_parserTail]
  exact cursor.exact previousPossible

theorem refineCylinder
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : ExactCursor origin originState machine)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) :
    ExactCursor origin originState
      (machine.refineCylinder epsilonSq positive) :=
  cursor.refine (machine.cylinderBallTarget epsilonSq)
    (machine.cylinderBallTarget_pos positive)

end ExactCursor

/-- One proof-bearing persistent cursor.  Later requests mutate only finite
machine data while retaining exact semantics relative to the same displayed
origin state. -/
structure Cursor (origin : Process) (originState : origin.State) where
  machine : Machine
  exact : ExactCursor origin originState machine

namespace Cursor

def initial (origin : Process) (originState : origin.State) :
    Cursor origin originState :=
  { machine := Machine.initial origin originState
    exact := ExactCursor.initial origin originState }

/-- Append exactly `count` visible bits and then refine the live sidecar to
the requested squared-chordal diameter. -/
def request
    {origin : Process} {originState : origin.State}
    (cursor : Cursor origin originState)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    Cursor origin originState :=
  let advanced := CCL.ProgressiveTransducer.advance
    cursor.machine count
  { machine := Machine.refineCylinder advanced epsilonSq positive
    exact := ExactCursor.refineCylinder (cursor.exact.advance count)
      epsilonSq positive }

theorem request_extends
    {origin : Process} {originState : origin.State}
    (cursor : Cursor origin originState)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    cursor.machine.emitted.IsPrefix
      (cursor.request epsilonSq positive count).machine.emitted := by
  simpa only [request, Machine.refineCylinder_emitted] using
    CCL.ProgressiveTransducer.advance_extends cursor.machine count

theorem request_length
    {origin : Process} {originState : origin.State}
    (cursor : Cursor origin originState)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat) :
    (cursor.request epsilonSq positive count).machine.emitted.length =
      cursor.machine.emitted.length + count := by
  simpa only [request, Machine.refineCylinder_emitted] using
    CCL.ProgressiveTransducer.advance_length cursor.machine count

theorem request_pair_chordalSq_le
    {origin : Process} {originState : origin.State}
    (cursor : Cursor origin originState)
    (epsilonSq : Coordinate) (positive : 0 < epsilonSq) (count : Nat)
    {left right : Gaussian}
    (leftPossible : SemanticMode.possible
      (cursor.request epsilonSq positive count).machine.mode left)
    (rightPossible : SemanticMode.possible
      (cursor.request epsilonSq positive count).machine.mode right) :
    CCL.Chordal.chordalSq
        ((cursor.request epsilonSq positive count).machine.image left)
        ((cursor.request epsilonSq positive count).machine.image right) ≤
      epsilonSq := by
  exact Machine.refineCylinder_pair_chordalSq_le
    (CCL.ProgressiveTransducer.advance cursor.machine count)
    epsilonSq positive leftPossible rightPossible

end Cursor

end CCL.PersistentProgressive
