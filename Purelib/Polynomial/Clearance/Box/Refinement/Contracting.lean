module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
/-!
# Choice-free raw-winding safe subdivision

Central-third eliminant-certified cuts split a clear box into four clear
children.  A finite first-nonzero scan retains raw winding while every round
contracts squared diagonal by `4/9`.
-/

@[expose] public section

namespace Purelib.Polynomial.Clearance.Box.Refinement.Contracting

set_option genInjectivity false in
/-- A clear child, before the deterministic nonzero-winding choice. -/
structure RawChild
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient parent : Box) where
  /-- The retained clear child box. -/ box : Box
  /-- The child refines the original parent box. -/ refinesParent : box.Refines parent
  /-- The child retains refinement into the fixed ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The child has positive width in both coordinates. -/ proper : box.Proper
  /-- The polynomial's retained quantitative clearance on the child boundary. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The child squared diagonal is at most four ninths of the parent squared diagonal. -/ contracts : box.diagonalSq ≤
    (4 / 9 : Fraction.Rational) * parent.diagonalSq

constructive_injectivity RawChild

end Purelib.Polynomial.Clearance.Box.Refinement.Contracting

end
