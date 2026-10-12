module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination
public import Purelib.RootIsolation.Subdivision.Raw.Selection

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.RootIsolation.Subdivision.Raw.Grid

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
/-!
# Choice-free raw-winding safe subdivision

Central-third eliminant-certified cuts split a clear box into four clear
children.  A finite first-nonzero scan retains raw winding while every round
contracts squared diagonal by `4/9`.
-/

@[expose] public section

namespace Purelib.RootIsolation.Subdivision.Raw.Step

/-- One deterministic raw-winding-preserving safe refinement. -/
def refineOnce
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) : RawWindingState p ambient :=
  let grid := Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state
  let child := Subdivision.Raw.Selection.firstNonzeroChild grid
  { box := child.box
    refinesAmbient := child.refinesAmbient
    proper := child.proper
    clearance := child.clearance
    rawWinding_ne := Subdivision.Raw.Selection.firstNonzeroChild_rawWinding_ne grid }

/-- The selected nonzero-winding child refines the original parent box. -/
theorem refineOnce_refines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.Refines state.box :=
  (Subdivision.Raw.Selection.firstNonzeroChild (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination
    state)).refinesParent

/-- One safe raw subdivision contracts the squared diagonal by at least the factor four ninths. -/
theorem refineOnce_contracts
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (refineOnce elimination state).box.diagonalSq ≤
      (4 / 9 : Fraction.Rational) * state.box.diagonalSq :=
  (Subdivision.Raw.Selection.firstNonzeroChild (Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination
    state)).contracts
end Purelib.RootIsolation.Subdivision.Raw.Step

end
