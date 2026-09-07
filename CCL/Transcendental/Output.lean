import CCL.Progressive.ExpRange
import CCL.Transcendental.ComplexLogChart
import CCL.Progressive.LogPositive
import CCL.Progressive.MachineSemantics

/-!
# Computing exponential and logarithm as CCL names

The purpose of this module is not merely to expose Horner approximants.  It
proves that exponential and certified logarithm are computable operations on
the repository's arithmetic CCL representation: a productive raw CCL cursor
together with its finite rational accuracy sidechannel.

Each request first refines the constructed output process to one displayed
rational ball whose squared radius is below the requested positive rational
target.  The ordinary productive CCL cursor is then started at that same
finite state and returns exactly the requested number of bits.  Its
exact-cursor certificate ties every admitted parser tail back to an explicitly
possible rational value at that same refined state.  Thus the enclosure and
the CCL word are two synchronized observations of one output name.  The bare
raw word alone is intentionally not claimed to carry enough accuracy data.
The construction returns only finite rational data; it does not name a
completed transcendental value.
-/

namespace CCL.TranscendentalOutput

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Named := CCL.ProgressiveTransducer.Named

/-- Rebase a progressive output at one explicitly requested finite-error
state. -/
def refined (output : Named) (target : Coordinate) (positive : 0 < target) :
    Named :=
  { process := output.process
    state := output.process.refine output.state target positive }

theorem refined_error (output : Named) (target : Coordinate)
    (positive : 0 < target) :
    ((refined output target positive).process.ball
      (refined output target positive).state).radiusSq < target :=
  output.process.accurate output.state target positive

theorem refined_productive (output : Named) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    (refined output target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (refined output target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (refined output target positive).machine count).emitted.length = count :=
  (refined output target positive).productive count

/-- The complete finite-request contract shared by every output process:
strict rational squared error, exact visible bit count, prefix preservation,
and exact ordinary raw-parser semantics for the same refined state. -/
theorem refined_bitstream_and_error (output : Named) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    ((refined output target positive).process.ball
        (refined output target positive).state).radiusSq < target ∧
      (refined output target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (refined output target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (refined output target positive).machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (refined output target positive).process
        (refined output target positive).state
        (CCL.ProgressiveTransducer.advance
          (refined output target positive).machine count) :=
  ⟨refined_error output target positive,
    (refined_productive output target positive count).1,
    (refined_productive output target positive count).2,
    CCL.ProgressiveMachineSemantics.Named.advance_exact
      (refined output target positive) count⟩

def expOutput (input : Named) : Named :=
  CCL.ProgressiveExpRange.named input

def expRequest (input : Named) (target : Coordinate) (positive : 0 < target) :
    Named :=
  refined (expOutput input) target positive

/-- End-to-end CCL computation of exponential.  From any arithmetic CCL name
`input`, `expOutput input` is another arithmetic CCL name.  Every finite
observation returns both a certified rational exponential enclosure and
exactly the requested number of raw CCL bits, with exact parser semantics for
the same output state.  This is the formal computability claim; the finite
Horner and range-reduction modules construct the output sidechannel consumed
by the productive CCL controller. -/
theorem exp_bitstream_and_error (input : Named) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    ((expRequest input target positive).process.ball
        (expRequest input target positive).state).radiusSq < target ∧
      (expRequest input target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (expRequest input target positive).process
        (expRequest input target positive).state
        (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count) :=
  refined_bitstream_and_error (expOutput input) target positive count

/-- Explicitly named paper-facing form of `exp_bitstream_and_error`: the
exponential is computable in the CCL-with-accuracy-sidechannel
representation. -/
theorem exp_ccl_computable (input : Named) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    ((expRequest input target positive).process.ball
        (expRequest input target positive).state).radiusSq < target ∧
      (expRequest input target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (expRequest input target positive).process
        (expRequest input target positive).state
        (CCL.ProgressiveTransducer.advance
          (expRequest input target positive).machine count) :=
  exp_bitstream_and_error input target positive count

def logOutput (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input) :
    Named :=
  CCL.ProgressiveLogPositive.named input positive

def logRequest (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input)
    (target : Coordinate) (targetPositive : 0 < target) : Named :=
  refined (logOutput input positive) target targetPositive

/-- End-to-end CCL computation of positive-real logarithm.  The finite
positive-real certificate lets the implementation construct its dyadic chart
automatically; `logOutput input positive` is another arithmetic CCL name.
Every observation synchronizes a certified rational logarithm enclosure with
exactly the requested raw CCL bits and exact parser semantics at the same
output state. -/
theorem log_bitstream_and_error (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input)
    (target : Coordinate) (targetPositive : 0 < target) (count : Nat) :
    ((logRequest input positive target targetPositive).process.ball
        (logRequest input positive target targetPositive).state).radiusSq <
          target ∧
      (logRequest input positive target targetPositive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (logRequest input positive target targetPositive).process
        (logRequest input positive target targetPositive).state
        (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count) :=
  refined_bitstream_and_error (logOutput input positive) target targetPositive count

/-- Explicit paper-facing statement that positive-real logarithm is
computable in the CCL-with-accuracy-sidechannel representation. -/
theorem log_ccl_computable (input : Named)
    (positive : CCL.ProgressiveLogPositive.PositiveReal input)
    (target : Coordinate) (targetPositive : 0 < target) (count : Nat) :
    ((logRequest input positive target targetPositive).process.ball
        (logRequest input positive target targetPositive).state).radiusSq <
          target ∧
      (logRequest input positive target targetPositive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (logRequest input positive target targetPositive).process
        (logRequest input positive target targetPositive).state
        (CCL.ProgressiveTransducer.advance
          (logRequest input positive target targetPositive).machine count) :=
  log_bitstream_and_error input positive target targetPositive count

/-- One certified application of the proposed transcendental generator
`g(x,y) = ExpName(x) - LogName(y)`.  Further applications may be nested, but
every value used as a logarithm argument must carry its own finite branch
certificate. -/
def gOutput (x y : Named)
    (positiveY : CCL.ProgressiveLogPositive.PositiveReal y) :
    Named :=
  CCL.ProgressiveTransducer.Named.sub
    (expOutput x) (logOutput y positiveY)

def gRequest (x y : Named)
    (positiveY : CCL.ProgressiveLogPositive.PositiveReal y)
    (target : Coordinate) (targetPositive : 0 < target) : Named :=
  refined (gOutput x y positiveY) target targetPositive

/-- Every certified finite application of `g` has the same combined
bitstream, squared-error, and exact-parser contract as exponential and
positive-real logarithm. -/
theorem g_bitstream_and_error (x y : Named)
    (positiveY : CCL.ProgressiveLogPositive.PositiveReal y)
    (target : Coordinate) (targetPositive : 0 < target) (count : Nat) :
    ((gRequest x y positiveY target targetPositive).process.ball
        (gRequest x y positiveY target targetPositive).state).radiusSq < target ∧
      (gRequest x y positiveY target targetPositive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (gRequest x y positiveY target targetPositive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (gRequest x y positiveY target targetPositive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (gRequest x y positiveY target targetPositive).process
        (gRequest x y positiveY target targetPositive).state
        (CCL.ProgressiveTransducer.advance
          (gRequest x y positiveY target targetPositive).machine count) :=
  refined_bitstream_and_error (gOutput x y positiveY) target targetPositive count

/-! ## Explicitly charted complex logarithm -/

def complexLogOutput (input : Named)
    (chart : CCL.ComplexLogChart.Chart input) : Named :=
  CCL.ComplexLogChart.named input chart

def complexLogRequest (input : Named)
    (chart : CCL.ComplexLogChart.Chart input)
    (target : Coordinate) (positive : 0 < target) : Named :=
  refined (complexLogOutput input chart) target positive

/-- A caller-supplied branch-safe complex chart produces the same finite
squared-error, productive-bitstream, and exact-parser contract as the
positive-real logarithm.  The chart exposes rather than guesses the branch
normalization. -/
theorem complex_log_bitstream_and_error (input : Named)
    (chart : CCL.ComplexLogChart.Chart input)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    ((complexLogRequest input chart target positive).process.ball
        (complexLogRequest input chart target positive).state).radiusSq < target ∧
      (complexLogRequest input chart target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (complexLogRequest input chart target positive).process
        (complexLogRequest input chart target positive).state
        (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count) :=
  refined_bitstream_and_error (complexLogOutput input chart) target positive count

/-- Explicit paper-facing statement that a branch-charted complex logarithm
is computable in the CCL-with-accuracy-sidechannel representation. -/
theorem complex_log_ccl_computable (input : Named)
    (chart : CCL.ComplexLogChart.Chart input)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    ((complexLogRequest input chart target positive).process.ball
        (complexLogRequest input chart target positive).state).radiusSq < target ∧
      (complexLogRequest input chart target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (complexLogRequest input chart target positive).process
        (complexLogRequest input chart target positive).state
        (CCL.ProgressiveTransducer.advance
          (complexLogRequest input chart target positive).machine count) :=
  complex_log_bitstream_and_error input chart target positive count

/-- The charted complex extension of `g(x,y) = ExpName(x) - LogName(y)`. -/
def complexGOutput (x y : Named)
    (chartY : CCL.ComplexLogChart.Chart y) : Named :=
  CCL.ProgressiveTransducer.Named.sub
    (expOutput x) (complexLogOutput y chartY)

def complexGRequest (x y : Named)
    (chartY : CCL.ComplexLogChart.Chart y)
    (target : Coordinate) (positive : 0 < target) : Named :=
  refined (complexGOutput x y chartY) target positive

/-- Every finite application of the charted complex `g` has a requested
rational enclosure, exactly the requested number of CCL bits, and exact
ordinary raw-parser semantics at the same refined state. -/
theorem complex_g_bitstream_and_error (x y : Named)
    (chartY : CCL.ComplexLogChart.Chart y)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    ((complexGRequest x y chartY target positive).process.ball
        (complexGRequest x y chartY target positive).state).radiusSq < target ∧
      (complexGRequest x y chartY target positive).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (complexGRequest x y chartY target positive).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (complexGRequest x y chartY target positive).machine count).emitted.length =
        count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        (complexGRequest x y chartY target positive).process
        (complexGRequest x y chartY target positive).state
        (CCL.ProgressiveTransducer.advance
          (complexGRequest x y chartY target positive).machine count) :=
  refined_bitstream_and_error (complexGOutput x y chartY) target positive count

end CCL.TranscendentalOutput
