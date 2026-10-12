module

public import Purelib.Algebra.Field.ExplicitField
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace Purelib.Geometry.Plane

variable {K : Type*}

section

set_option genInjectivity false in
/-- A Cartesian point is an ordered pair of field elements. -/
@[ext]
structure Point (K : Type*) where
  /-- First Cartesian coordinate. -/ x : K
  /-- Second Cartesian coordinate. -/ y : K
deriving DecidableEq

constructive_injectivity Point

end

section

end

end Purelib.Geometry.Plane

end

end

section
/-!
# Divine Proportions, Exercise 16.7: projective-circle rays

Line equality remains the explicit cross-product relation `Line.Equivalent`;
no quotient of coefficient triples is introduced.  The canonical ray for a
parameter `λ` is `⟨-1:λ:0⟩`.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section Conic

/-- The distinguished origin on the projective circle. -/
def projectiveCircleOrigin : Geometry.Plane.Point K := ⟨0, 0⟩
end Conic

end Purelib.Curves.Plane.Conic

end

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 16.8: rational polar form

A Cartesian point is used as a finite Gaussian pair.  Multiplication and
scaling are explicit coordinate operations; no completed complex carrier is
introduced.  The unit-circle parameter is recovered by the finite quotient
`y / (1+x)`, and the chord through `-1` has the displayed equation
`lambda*x-y+lambda=0`.

The multiplication theorem uses the same `turnComposition` operation as
Exercise 9.2.  Its premise `1-lambda₁*lambda₂ != 0` is essential: when it
vanishes, the product unit point is the excluded point `[-1,0]`, so the finite
chart has no resulting parameter.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section Conic

/-- The imaginary-axis point `i*lambda`. -/
def imaginaryParameterPoint (parameter : K) :
  Geometry.Plane.Point K :=
  ⟨0, parameter⟩
end Conic

end Purelib.Curves.Plane.Conic

end

section
/-!
# Divine Proportions, §16.3: the unit circle

The source's map `[x,y] ↦ [2y-1,2x]` is stored as an executable point
transformation.  Its unit-circle equation is exactly four times the
projective-circle equation, so Theorem 108 follows from Theorem 107 with one
visible characteristic-two exclusion in the reverse direction.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section Conic

/-- The unit circle's displayed center. -/
def unitCircleCenter : Geometry.Plane.Point K := ⟨0, 0⟩
end Conic

end Purelib.Curves.Plane.Conic

end

end

section
/-!
# Divine Proportions, §13.1 and Theorem 91: finite plane isometries

An isometry carries both an executable point map and an executable inverse.
Its metric law is the finite equality asserting preservation of quadrance;
there is no completed space, infinite carrier argument, or selected inverse.

Theorem 91 follows exactly the source proof through the Triple-quad formula.
The hypothesis `2 ≠ 0` is exposed because over characteristic two the book's
quadrance degenerates and no longer detects collinearity.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Point.Basic

variable {K : Type*} [ExplicitField K]

section

/-- The origin `O ≡ [0,0]`. -/
def planeOrigin : Point K := ⟨0, 0⟩

end

end Purelib.Geometry.Plane.Point.Basic

end

end

section
/-!
# Divine Proportions, Theorem 92: specifying an isometry

The proof is the source's three finite quadrance equations.  Subtracting the
equations at the origin and the two coordinate points recovers twice each
coordinate; the explicit inverse of two then cancels that factor.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Point.Basic

variable {K : Type*} [ExplicitField K]

section

/-- The reference point `I₁ ≡ [1,0]`. -/
def firstAxisPoint : Point K := ⟨1, 0⟩

/-- The reference point `I₂ ≡ [0,1]`. -/
def secondAxisPoint : Point K := ⟨0, 1⟩

end

end Purelib.Geometry.Plane.Point.Basic

end

end
