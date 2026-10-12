module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Line
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

/-!
# Divine Proportions, Chapter 14 examples

The prime-field exclusions are stated through the exact finite Frobenius law
used by Euler's square test.  This avoids enumerating a carrier or searching
globally for roots.  The positive examples retain the literal source lines.
-/

namespace Purelib.Geometry.Plane.Reflection.Iteration.Line

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] in
/-- Propagate two finite line equivalences through one executable reflection step. -/
public theorem next_equivalent
    (initial : Iteration.ReflectionPair K) (index : Nat)
    (previous current next : Purelib.Geometry.Plane.Line K)
    (previousEquivalent :
      (Iteration.reflectionLineAt initial index).Equivalent previous)
    (currentEquivalent :
      (Iteration.reflectionLineAt initial (index + 1)).Equivalent current)
    (currentNonNull : ¬ current.IsNull)
    (printedStep : (Line.reflectLine current previous currentNonNull).Equivalent next) :
    (Iteration.reflectionLineAt initial (index + 2)).Equivalent next := by
  rw [Iteration.reflectionLineAt_succ_succ]
  exact Relations.line_equivalent_trans
    (Line.reflectLine_equivalent_of_equivalent
      (Iteration.reflectionLineAt initial (index + 1)) current
      (Iteration.reflectionLineAt initial index) previous
      (Iteration.reflectionLineAt_nonNull initial (index + 1)) currentNonNull
      currentEquivalent previousEquivalent)
    printedStep

end

end

end Purelib.Geometry.Plane.Reflection.Iteration.Line

end
