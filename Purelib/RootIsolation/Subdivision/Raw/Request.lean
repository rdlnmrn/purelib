module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib

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

namespace Purelib.RootIsolation.Subdivision.Raw.Request

/-- Compute the finite geometric-contraction depth for the original squared diagonal and requested threshold. -/
def refinementDepth
    {p : CoefficientPolynomial} {ambient : Box}
    (state : RawWindingState p ambient) (threshold : Fraction.Rational) : Nat :=
  Approximation.Rational.Contraction.geometricDepth
    state.box.diagonalSq threshold

/-- Total finite refinement to a requested positive squared diagonal. -/
def refineTo
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) (threshold : Fraction.Rational) :
    RawWindingState p ambient :=
  Subdivision.Raw.Iteration.Forward.refineForwardN elimination (refinementDepth state threshold)
    state

/-- A positive requested threshold bounds the squared diagonal of the retained finite subdivision result. -/
theorem refineTo_diagonalSq_le
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) {threshold : Fraction.Rational}
    (thresholdPositive : 0 < threshold) :
    (refineTo elimination state threshold).box.diagonalSq ≤ threshold := by
  let depth := refinementDepth state threshold
  have raw := Subdivision.Raw.Iteration.Forward.refineForwardN_diagonalSq_le elimination depth state
  have powerBound : (4 / 9 : Fraction.Rational) ^ depth ≤
      (2 / 3 : Fraction.Rational) ^ depth :=
    Fraction.Order.Arithmetic.pow_le_pow_direct (by decide) (by decide) depth
  have scaledPower :
      (4 / 9 : Fraction.Rational) ^ depth * state.box.diagonalSq ≤
        (2 / 3 : Fraction.Rational) ^ depth * state.box.diagonalSq :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      powerBound state.box.diagonalSq_nonneg
  exact raw.trans (scaledPower.trans (by
    simpa only [depth, refinementDepth] using
      Approximation.Rational.Contraction.geometricDepth_sufficient
        state.box.diagonalSq_nonneg thresholdPositive))

/-- The finite raw-subdivision request refines the original input box. -/
theorem refineTo_refines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) (threshold : Fraction.Rational) :
    (refineTo elimination state threshold).box.Refines state.box :=
  Subdivision.Raw.Iteration.Forward.refineForwardN_refines elimination (refinementDepth state
    threshold) state

end Purelib.RootIsolation.Subdivision.Raw.Request

end
