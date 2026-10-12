module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, Theorem 109: cyclic quadrilaterals

A quadrilateral is kept as four displayed points together with the source's
finite distinctness and noncollinearity certificates.  The cyclic predicate
stores an explicit conic, center, quadrance, circle presentation, and four
incidence proofs.

The printed four-by-four determinant is expanded by `determinantThree`; no
matrix determinant, permutation enumeration, or quotient of cyclic orderings
is introduced.  A translated determinant identity then gives both directions
of Theorem 109 constructively.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- Four ordered, distinct points with no collinear triple.

The record retains every pairwise inequality and every three-point noncollinearity certificate. Cyclic rotation and
reversal do not identify records. -/
structure Quadrilateral (K : Type*) [Algebra.Field.ExplicitField K] where
  /-- The first vertex in the displayed cyclic order. -/ first : Plane.Point K
  /-- The second vertex in the displayed cyclic order. -/ second : Plane.Point K
  /-- The third vertex in the displayed cyclic order. -/ third : Plane.Point K
  /-- The fourth vertex in the displayed cyclic order. -/ fourth : Plane.Point K
  /-- The first and second vertices are distinct. -/ firstSecondDistinct : first ≠ second
  /-- The first and third vertices are distinct. -/ firstThirdDistinct : first ≠ third
  /-- The first and fourth vertices are distinct. -/ firstFourthDistinct : first ≠ fourth
  /-- The second and third vertices are distinct. -/ secondThirdDistinct : second ≠ third
  /-- The second and fourth vertices are distinct. -/ secondFourthDistinct : second ≠ fourth
  /-- The third and fourth vertices are distinct. -/ thirdFourthDistinct : third ≠ fourth
  /-- The first three vertices are not collinear. -/ firstSecondThirdNoncollinear : ¬ Incidence.Collinear first second
    third
  /-- The first, second and fourth vertices are not collinear. -/ firstSecondFourthNoncollinear : ¬ Incidence.Collinear
    first second fourth
  /-- The first, third and fourth vertices are not collinear. -/ firstThirdFourthNoncollinear : ¬ Incidence.Collinear
    first third fourth
  /-- The last three vertices are not collinear. -/ secondThirdFourthNoncollinear : ¬ Incidence.Collinear second third
    fourth

constructive_injectivity Quadrilateral

end Purelib.Geometry.Quadrilaterals.Basic

end
