module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Finite.CountArithmetic

open Purelib.Algebra

open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, Exercises 3.2 and 3.13

The source phrases both exercises as cardinalities of complete finite-field
carriers.  Such global enumerations are outside this project's proof boundary.
The incidence content is instead made executable through finite charts:

* every line through a point is either one uniquely determined slope line or
  the vertical line;
* every point on a line is obtained uniquely from one scalar parameter, using
  whichever displayed direction coefficient is nonzero.

These are the constructive bijection data behind the counts `p+1` and `p`.
For triangles, the usual counting proof is retained as exact cleared integer
identities.  It subtracts collinear triples from all triples and, in the null
case, subtracts the double-counted triangles having two null sides.  No list
of all points, lines, or triangles is constructed.
-/

namespace formalisations.DivineProportions.Chapters.Examples

namespace ChapterThreeCounting

variable {K : Type*} [Field.ExplicitField K] [Nontrivial K]
namespace ExerciseThreeThirteen

/-- Closed checks of the formulas at the first four odd prime labels.  These
are arithmetic evaluations, not enumerations of their fields. -/
theorem first_count_values :
    Finite.CountArithmetic.triangleCount 3 = 72 ∧ Finite.CountArithmetic.triangleCount 5 = 2000 ∧
      Finite.CountArithmetic.triangleCount 7 = 16464 ∧ Finite.CountArithmetic.triangleCount 11 = 266200 ∧
      Finite.CountArithmetic.nullTriangleCountWithNullLines 5 = 1600 ∧
      Finite.CountArithmetic.nullTriangleCountWithNullLines 13 = 292032 := by
  decide

end ExerciseThreeThirteen

end ChapterThreeCounting

end formalisations.DivineProportions.Chapters.Examples

end

end
