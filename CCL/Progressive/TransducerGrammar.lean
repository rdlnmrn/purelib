import CCL.Progressive.Transducer
import CCL.Encoding.RawParser

/-!
# Raw-grammar certificate for progressive arithmetic output

The progressive arithmetic controller carries quantitative enclosure data,
but its visible output remains the original pure CCL bitstream.  This module
is the one-way bridge: it proves that each buffered controller chunk advances
the unchanged syntax-only raw parser to exactly the phase recorded by the
controller.  Nothing in the canonical parser depends on the sidecar.
-/

namespace CCL.ProgressiveTransducerGrammar

open CCL.ProgressiveTransducer
open CCL.RawParser
open CCL.ProgressiveCharts

def regularRawPhase :
    CCL.ProgressiveTransducer.RegularKind → Nat → Phase
  | .initialHigh, count => .highUnary count
  | .loop, count => .loopUnary count

/-- The phase of the original raw CCL grammar after every bit committed by a
controller mode, including bits currently buffered by its one-bit cursor. -/
def modeRawPhase : Mode → Phase
  | .initial _ => .initial
  | .low state => .lowUnary state.count
  | .loop state => regularRawPhase state.kind state.count
  | .residual state => .loopUnary state.count

/-- A whole nonempty controller chunk follows the original raw grammar. -/
def EmissionFollows (mode : Mode) (emission : Emission) : Prop :=
  Phase.consume (modeRawPhase mode) emission.bits =
    modeRawPhase emission.next

@[simp] theorem consume_initial_high :
    Phase.consume .initial [true] = .highUnary 1 := rfl

@[simp] theorem consume_initial_low_unary :
    Phase.consume .initial [false, true] = .lowUnary 1 := rfl

@[simp] theorem consume_initial_low_sector
    (sector : CCL.Sectors.Sector) :
    Phase.consume .initial (false :: false :: sector.code) =
      .loopUnary 0 := by
  cases sector <;> rfl

@[simp] theorem consume_low_unary (count : Nat) :
    Phase.consume (.lowUnary count) [true] = .lowUnary (count + 1) := rfl

@[simp] theorem consume_low_sector (count : Nat)
    (sector : CCL.Sectors.Sector) :
    Phase.consume (.lowUnary count) (false :: sector.code) =
      .loopUnary 0 := by
  cases sector <;> rfl

@[simp] theorem consume_regular_unary (kind : RegularKind) (count : Nat) :
    Phase.consume (regularRawPhase kind count) [true] =
      regularRawPhase kind (count + 1) := by
  cases kind <;> rfl

@[simp] theorem consume_regular_sector (kind : RegularKind) (count : Nat)
    (sector : CCL.Sectors.Sector) :
    Phase.consume (regularRawPhase kind count) (false :: sector.code) =
      .loopUnary 0 := by
  cases kind <;> cases sector <;> rfl

@[simp] theorem consume_residual_unary (count : Nat) :
    Phase.consume (.loopUnary count) [true] = .loopUnary (count + 1) := rfl

theorem loopStep_follows (current : LoopState) :
    EmissionFollows (.loop current) (loopStep current) := by
  unfold EmissionFollows loopStep
  split
  · simp [modeRawPhase]
  · simp [modeRawPhase]

/-- Every quantitative decision produces a chunk accepted by the original
raw CCL grammar, independently of the candidate values in its enclosure. -/
theorem step_follows (mode : Mode) : EmissionFollows mode (step mode) := by
  cases mode with
  | initial current =>
      change EmissionFollows (.initial current) (initialStep current)
      unfold EmissionFollows
      simp only [initialStep]
      split
      · split
        · rfl
        · rename_i sector certificate decision
          exact consume_initial_low_sector sector
      · simp [modeRawPhase]
  | low current =>
      change EmissionFollows (.low current) (lowStep current)
      unfold EmissionFollows
      simp only [lowStep]
      split
      · exact consume_low_sector current.count _
      · simp [modeRawPhase]
  | loop current => exact loopStep_follows current
  | residual current =>
      change EmissionFollows (.residual current) (residualStep current)
      unfold EmissionFollows
      simp only [residualStep]
      split
      · simp [modeRawPhase]
      · rename_i certificate decision
        let requestedCount := current.count + 1
        let refined :=
          CCL.ArithmeticController.residualState
            current.process current.state requestedCount
        have upperBoundAtRefined : ∀
            {value : RFAP.ConstructiveGaussian.Gaussian},
            current.process.Possible refined value →
              RFAP.ConstructiveGaussian.Gaussian.normSq value ≤
                current.upper := by
          intro value possible
          exact current.upperBound
            (current.process.refine_persists current.state _ _ possible)
        let nextProcess := normalizedInverseProcess current.process refined
          certificate current.count
        let nextState := normalizedInverseInitial current.process refined
          certificate current.count
        let nextDomain := normalizedInverseLoopDomain current.process refined
          certificate current.count current.upper upperBoundAtRefined
          current.upperStrict
        let next : LoopState :=
          { kind := .loop
            count := current.count
            process := nextProcess
            state := nextState
            domain := nextDomain }
        change Phase.consume (.loopUnary current.count)
            (loopStep next).bits = modeRawPhase (loopStep next).next
        simpa [EmissionFollows, modeRawPhase, regularRawPhase] using
          loopStep_follows next

namespace Machine

/-- Bits already exposed followed by the remainder of the current certified
chunk.  The mode describes the parser phase after this complete committed
word, even while the cursor is exposing that word one bit at a time. -/
def committed (machine : Machine) : List Bool :=
  machine.emitted ++ machine.pending

/-- Persistent relationship between a buffered controller and the unchanged
raw parser. -/
def GrammarInvariant (machine : Machine) : Prop :=
  (CCL.RawParser.parse (Machine.committed machine)).phase =
    modeRawPhase machine.mode

end Machine

theorem consumeEmission_committed (emitted : List Bool)
    (emission : Emission) :
    Machine.committed (consumeEmission emitted emission).2 =
      emitted ++ emission.bits := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | nil => exact (nonempty rfl).elim
      | cons bit rest =>
          simp [consumeEmission, Machine.committed, List.append_assoc]

theorem consumeEmission_mode (emitted : List Bool) (emission : Emission) :
    (consumeEmission emitted emission).2.mode = emission.next := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | nil => exact (nonempty rfl).elim
      | cons bit rest => rfl

theorem consumeEmission_invariant (mode : Mode) (emitted : List Bool)
    (emission : Emission)
    (before : (CCL.RawParser.parse emitted).phase =
      modeRawPhase mode)
    (follows : EmissionFollows mode emission) :
    Machine.GrammarInvariant (consumeEmission emitted emission).2 := by
  unfold Machine.GrammarInvariant
  rw [consumeEmission_committed,
    CCL.RawParser.parse_append_phase, before,
    consumeEmission_mode]
  exact follows

@[simp] theorem Machine.initial_invariant
    (process : CCL.ProgressiveTransducer.Process)
    (state : process.State) :
    Machine.GrammarInvariant (Machine.initial process state) := rfl

theorem nextBit_invariant (machine : Machine)
    (invariant : Machine.GrammarInvariant machine) :
    Machine.GrammarInvariant (nextBit machine).2 := by
  cases machine with
  | mk mode emitted pending =>
      cases pending with
      | nil =>
          apply consumeEmission_invariant mode emitted (step mode)
          · simpa [Machine.GrammarInvariant, Machine.committed] using invariant
          · exact step_follows mode
      | cons bit rest =>
          simpa [Machine.GrammarInvariant, Machine.committed, nextBit,
            List.append_assoc] using invariant

theorem advance_invariant (machine : Machine)
    (invariant : Machine.GrammarInvariant machine) : ∀ count : Nat,
    Machine.GrammarInvariant (advance machine count)
  | 0 => invariant
  | count + 1 =>
      advance_invariant (nextBit machine).2
        (nextBit_invariant machine invariant) count

theorem Machine.initial_advance_invariant
    (process : CCL.ProgressiveTransducer.Process)
    (state : process.State) (count : Nat) :
    Machine.GrammarInvariant
      (advance (Machine.initial process state) count) :=
  advance_invariant _ (Machine.initial_invariant process state) count

theorem Named.machine_advance_invariant (name : Named) (count : Nat) :
    Machine.GrammarInvariant (advance name.machine count) :=
  Machine.initial_advance_invariant name.process name.state count

end CCL.ProgressiveTransducerGrammar
