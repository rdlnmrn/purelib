module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, Examples 14.11 and 14.12

The pentagon and hexagon are represented by five and six executable vertices.
The generic construction proves their radial incidences, equal radii,
successive-reflection equations, and closure.  This file supplies the two
finite distinctness arguments from the source: doubling permutes the five
radial lines, while the three opposite hexagon pairs use perpendicular
mirrors and central rotation.
-/

namespace Purelib.Geometry.Plane.Line.Parallel

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K] [DecidableEq K]

omit [Nontrivial K] [DecidableEq K] in
/-- Nonparallelism is preserved when both displayed lines are replaced by equivalent representatives. -/
public theorem nonparallel_of_equivalent_pairs
    (actualFirst displayedFirst actualSecond displayedSecond : Purelib.Geometry.Plane.Line K)
    (firstEquivalent : actualFirst.Equivalent displayedFirst)
    (secondEquivalent : actualSecond.Equivalent displayedSecond)
    (displayedNonparallel : ¬ displayedFirst.Parallel displayedSecond) :
    ¬ actualFirst.Parallel actualSecond := by
  intro actualParallel
  apply displayedNonparallel
  exact Relations.line_parallel_trans
    (Purelib.Geometry.Plane.Line.parallel_symm (Relations.line_parallel_of_equivalent firstEquivalent))
    (Relations.line_parallel_trans actualParallel
      (Relations.line_parallel_of_equivalent secondEquivalent))

end Purelib.Geometry.Plane.Line.Parallel

end
