module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Step

import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Tactic.Ring

/-!
# Forward iteration of raw-winding refinement

Each step uses the retained axis-elimination certificate to select a clear
child with nonzero raw winding. Forward recursion advances the current state
before processing the remaining depth and retains the squared-diagonal bound.
-/

public section

namespace Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Iterate raw refinement forward through a specified finite depth.

Each successor advances the current state before the recursive call. Compiled
evaluation uses constant call-stack space while retaining the same polynomial,
ambient box and axis-elimination certificate throughout the iteration.
-/
@[expose] def refineForwardN
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) :
    Nat → State.Raw.RawWindingState p ambient → State.Raw.RawWindingState p ambient
  | 0, state => state
  | depth + 1, state =>
      refineForwardN elimination depth (Subdivision.Raw.Step.refineOnce elimination state)

/-- Every forward-iterated raw state refines the original input box.

Each selected child refines its retained parent. Transitivity carries this relation
through the specified finite depth over the same polynomial and ambient box. -/
theorem refineForwardN_refines
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : State.Raw.RawWindingState p ambient) :
    (refineForwardN elimination depth state).box.Refines state.box := by
  induction depth generalizing state with
  | zero => exact Box.refines_refl _
  | succ depth inductionHypothesis =>
      exact (inductionHypothesis (Subdivision.Raw.Step.refineOnce elimination state)).trans
        (Subdivision.Raw.Step.refineOnce_refines elimination state)

/-- Forward iteration contracts the squared diagonal by at most four ninths per retained step.

The bound multiplies the original squared diagonal by the corresponding rational
power. Every successor uses the same selected child and its retained contraction
certificate. -/
theorem refineForwardN_diagonalSq_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (depth : Nat) (state : State.Raw.RawWindingState p ambient) :
    (refineForwardN elimination depth state).box.diagonalSq ≤
      (4 / 9 : Fraction.Rational) ^ depth * state.box.diagonalSq := by
  induction depth generalizing state with
  | zero =>
      change state.box.diagonalSq ≤ (4 / 9 : Fraction.Rational) ^ 0 * state.box.diagonalSq
      rewrite [pow_zero, one_mul]
      exact Fraction.Order.Basic.le_refl _
  | succ depth inductionHypothesis =>
      let next := Subdivision.Raw.Step.refineOnce elimination state
      have recursive := inductionHypothesis next
      calc
        (refineForwardN elimination (depth + 1) state).box.diagonalSq =
            (refineForwardN elimination depth next).box.diagonalSq := rfl
        _ ≤ (4 / 9 : Fraction.Rational) ^ depth * next.box.diagonalSq := recursive
        _ ≤ (4 / 9 : Fraction.Rational) ^ depth *
              ((4 / 9 : Fraction.Rational) * state.box.diagonalSq) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Subdivision.Raw.Step.refineOnce_contracts elimination state)
            (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)
        _ = (4 / 9 : Fraction.Rational) ^ (depth + 1) *
              state.box.diagonalSq := by
          rw [pow_succ]
          ring1
end Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward
