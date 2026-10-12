module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Normalized
public import Purelib.Geometry.Plane.Reflection.Line
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

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

namespace Purelib.Geometry.Plane.Reflection.Line.Normalized

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

/-- One literal slope calculation certifies a reflection step between the printed origin lines. -/
public theorem reflect_printedLine
    (mirrorSlope targetSlope resultSlope : K)
    (mirrorNonNull : ¬ (Normalized.printedLine mirrorSlope).IsNull)
    (slopeEquation :
      (mirrorSlope ^ 2 - 1) * targetSlope + 2 * mirrorSlope =
        resultSlope *
          (2 * mirrorSlope * targetSlope - (mirrorSlope ^ 2 - 1))) :
    (Line.reflectLine (Normalized.printedLine mirrorSlope) (Normalized.printedLine targetSlope)
      mirrorNonNull).Equivalent (Normalized.printedLine resultSlope) := by
  unfold Line.Equivalent Line.reflectLine Normalized.printedLine Line.reflectedLineA
    Line.reflectedLineB Line.reflectedLineC Line.Basic.lineNorm
  constructor
  · simpa only [one_pow, mul_one, one_mul, mul_zero, add_zero, sub_zero]
      using slopeEquation
  · constructor <;> ring1

end

end

end Purelib.Geometry.Plane.Reflection.Line.Normalized

end
