module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Expression.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Certified finite CCL expression trees

This indexed syntax packages exactly the side conditions needed at each
operation: coherence is carried by every node, division stores finite
denominator apartness, and a complex-log node stores an anchored chart.  An
expression denotes its constructed progressive process, not a completed
complex value.
-/

namespace Purelib.Approximation.Gaussian.Expression
section Expression

/-- Every typed finite expression answers a simultaneous rational-error and raw-bit request, including exact parser
semantics at the same refined state. -/
theorem bitstream_and_error (expression :
  Expression) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    let refined := Refinement.refined
      expression.output.name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Advance.advance
          refined.machine count).emitted ∧
      (Advance.advance
          refined.machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        refined.process refined.state
        (Advance.advance
          refined.machine count) :=
  CCL.Contract.refined_bitstream_and_error
    expression.output.name target positive count

end Expression

end Purelib.Approximation.Gaussian.Expression

end
