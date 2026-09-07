import mathlib.Tactic.QuotientFreeOmega
import CCL.Transcendental.LogBranchCalculus
import CCL.Transcendental.Output

/-!
# Certified finite CCL expression trees

This indexed syntax packages exactly the side conditions needed at each
operation: coherence is carried by every node, division stores finite
denominator apartness, and a complex-log node stores an anchored chart.  An
expression denotes its constructed progressive process, not a completed
complex value.
-/

namespace CCL.CertifiedExpression

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

/-- A finite certified expression package.  The public constructors below
compute the coherent output and increment this explicit finite node count. -/
structure Expression where
  output : CoherentNamed
  nodeCount : Nat
  nodeCount_pos : 0 < nodeCount

namespace Expression

/-- Insert an already coherent arithmetic CCL input as one leaf. -/
def leaf (value : CoherentNamed) : Expression :=
  { output := value, nodeCount := 1, nodeCount_pos := by decide }

/-- Insert one displayed terminating Gaussian rational. -/
def exact (value : Gaussian) : Expression :=
  leaf (CCL.ProgressiveCoherence.CoherentNamed.exact value)

def add (left right : Expression) : Expression :=
  { output := CCL.ProgressiveCoherence.CoherentNamed.add
      left.output right.output
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }

def neg (value : Expression) : Expression :=
  { output := CCL.ProgressiveCoherence.CoherentNamed.neg
      value.output
    nodeCount := value.nodeCount + 1
    nodeCount_pos := by omega }

def mul (left right : Expression) : Expression :=
  { output := CCL.ProgressiveCoherence.CoherentNamed.mul
      left.output right.output
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }

/-- Division is constructible only from the displayed finite apartness
certificate for the actual denominator expression. -/
def div (left right : Expression)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      right.output.name) : Expression :=
  { output := CCL.ProgressiveCoherence.CoherentNamed.div
      left.output right.output apart
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }

def exponential (input : Expression) : Expression :=
  { output := CCL.TranscendentalCoherence.exp input.output.name
    nodeCount := input.nodeCount + 1
    nodeCount_pos := by omega }

/-- A complex logarithm node cannot be constructed without the anchored
finite chart for its actual input expression. -/
def logarithm (input : Expression) (branch : AnchoredChart input.output) :
    Expression :=
  { output := branch.output
    nodeCount := input.nodeCount + 1
    nodeCount_pos := by omega }

/-- The closed rational request modulus supplied by the coherence sidecar of
the constructed output process. -/
def requestAllowance (expression : Expression)
    (target : Coordinate) : Coordinate :=
  expression.output.coherent.accuracyRequest target

theorem requestAllowance_pos (expression : Expression) {target : Coordinate}
    (positive : 0 < target) :
    0 < expression.requestAllowance target :=
  expression.output.coherent.accuracyRequest_pos positive

/-- A request below the displayed modulus makes the semantic coherence
allowance, not merely the enclosure radius, smaller than the target. -/
theorem refined_allowance_lt (expression : Expression)
    {target request : Coordinate}
    (targetPositive : 0 < target) (requestPositive : 0 < request)
    (requestSmall : request < expression.requestAllowance target) :
    expression.output.coherent.allowance
        (expression.output.name.process.refine expression.output.name.state
          request requestPositive) < target :=
  expression.output.coherent.refine_accurate expression.output.name.state
    target targetPositive
    request requestPositive requestSmall

/-- Every typed finite expression answers a simultaneous rational-error and
raw-bit request, including exact parser semantics at the same refined state. -/
theorem bitstream_and_error (expression : Expression) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      expression.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance
          refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    expression.output.name target positive count

end Expression

end CCL.CertifiedExpression
