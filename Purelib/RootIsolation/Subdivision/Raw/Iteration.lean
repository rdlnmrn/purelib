module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Step

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Tactic.Ring

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

namespace Purelib.RootIsolation.Subdivision.Raw.Iteration

/-- Fixed-depth iteration of safe raw refinement. -/
def refineN
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    Nat → RawWindingState p ambient → RawWindingState p ambient
  | 0, state => state
  | depth + 1, state => Subdivision.Raw.Step.refineOnce elimination
    (refineN elimination depth state)

/-- Every fixed-depth raw subdivision state refines the original input box. -/
theorem refineN_refines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineN elimination depth state).box.Refines state.box := by
  induction depth with
  | zero => exact Box.refines_refl _
  | succ depth inductionHypothesis =>
      exact (Subdivision.Raw.Step.refineOnce_refines elimination
        (refineN elimination depth state)).trans inductionHypothesis

/-- After the retained finite depth, the box's squared diagonal is at most four ninths to that depth times the original
squared diagonal. -/
theorem refineN_diagonalSq_le
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : RawWindingState p ambient) :
    (refineN elimination depth state).box.diagonalSq ≤
      (4 / 9 : Fraction.Rational) ^ depth * state.box.diagonalSq := by
  induction depth with
  | zero =>
      simp only [refineN, -eq_self, -iff_self]
      rewrite [pow_zero, Fraction.one_mul]
      exact Fraction.Order.Basic.le_refl _
  | succ depth inductionHypothesis =>
      calc
        (refineN elimination (depth + 1) state).box.diagonalSq ≤
            (4 / 9 : Fraction.Rational) *
              (refineN elimination depth state).box.diagonalSq :=
          Subdivision.Raw.Step.refineOnce_contracts elimination (refineN elimination depth
            state)
        _ ≤ (4 / 9 : Fraction.Rational) *
              ((4 / 9 : Fraction.Rational) ^ depth * state.box.diagonalSq) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            inductionHypothesis (by decide)
        _ = (4 / 9 : Fraction.Rational) ^ (depth + 1) *
              state.box.diagonalSq := by
          rw [pow_succ]
          ring1
end Purelib.RootIsolation.Subdivision.Raw.Iteration

end
