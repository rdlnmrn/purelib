module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

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

namespace Purelib.Approximation.Gaussian

set_option genInjectivity false in
/-- A finite certified expression package. The public constructors below compute the coherent output and increment this
explicit finite node count. -/
structure Expression where
  /-- The computed coherent Gaussian process name of the certified expression. -/ output :
    CoherentNamed
  /-- The retained positive finite number of expression nodes. -/ nodeCount : Nat
  /-- The expression has at least one retained node. -/ nodeCount_pos : 0 < nodeCount

constructive_injectivity Expression

namespace Expression.mk

end Expression.mk

namespace Expression

/-- Insert an already coherent arithmetic CCL input as one leaf. -/
def leaf (value :
  CoherentNamed) : Expression :=
  { output := value, nodeCount := 1, nodeCount_pos := by decide }

/-- Insert one displayed terminating Gaussian rational. -/
def exact (value : Data.Gaussian.Basic.Canonical) :
  Expression :=
  leaf (Coherence.exact value)

/-- Construct the sum of two certified expressions, retaining their coherent sum and adding one operation node. -/
def add (left right :
  Expression) : Expression :=
  { output := CoherentNamed.add
      left.output right.output
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }

/-- Construct the negation of a certified expression and add one operation node. -/
def neg (value :
  Expression) : Expression :=
  { output := CoherentNamed.neg
      value.output
    nodeCount := value.nodeCount + 1
    nodeCount_pos := by omega }

/-- Construct the product of two certified expressions, retaining their coherent product and adding one operation node.
-/
def mul (left right :
  Expression) : Expression :=
  { output := CoherentNamed.mul
      left.output right.output
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }

/-- Division is constructible only from the displayed finite apartness certificate for the actual denominator
expression. -/
def div (left right :
  Expression)
    (apart : Named.Apart
      right.output.name) : Expression :=
  { output := CoherentNamed.div
      left.output right.output apart
    nodeCount := left.nodeCount + right.nodeCount + 1
    nodeCount_pos := by omega }
end Expression

end Purelib.Approximation.Gaussian

end
