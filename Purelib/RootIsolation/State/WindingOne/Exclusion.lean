module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Nearby
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual.Nearby
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Excluding a displayed clear point from a winding-one track

A fixed rational point at which the polynomial is nonzero cannot remain in
an arbitrarily small nonzero-winding box.  The proof uses the existing finite
constant-dominance homotopy: if the point were inside, its nonzero value and
the box's coefficient-computed variation bound would force winding zero.

This is the terminal-point part of the persistent CCL equality handler.  A
local CCL terminal is either an exact polynomial root, or one explicit track
refinement excludes that displayed rational point.
-/

namespace Purelib.RootIsolation.State.WindingOne.Exclusion

/-- A displayed clear point whose value dominates the current box variation
cannot lie in a winding-one box. -/
theorem not_contains_of_margin
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (current : State.WindingOne.Basic.WindingOneState p ambient) (point : Gaussian.Basic.Canonical)
    (margin : Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient p ambient * current.box.diagonalSq <
      Data.Gaussian.Norm.Basic.normSq (p.eval point)) :
    ¬current.box.Contains point := by
  intro inside
  let certificate :
      Dense.Gaussian.Bounds.Box.Residual.Nearby.NearbyClearPointCertificate
        p ambient current.box :=
    { point := point
      point_mem := current.refinesAmbient.contains inside
      clearance := Data.Gaussian.Norm.Basic.normSq (p.eval point)
      radiusSq := current.box.diagonalSq
      clearance_lower := le_rfl
      anchor_distance := current.box.normSq_sub_anchor_le inside
      dominates := by
        calc
          2 *
              (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound
                  p ambient current.box +
                Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * current.box.diagonalSq) =
              Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient p ambient * current.box.diagonalSq := by
            simp only [Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound,
              Dense.Gaussian.Bounds.Box.Exclusion.Uniform.exclusionCoefficient]
            ring1
          _ < Data.Gaussian.Norm.Basic.normSq (p.eval point) := margin }
  have windingZero :=
    Winding.Box.Residual.Nearby.quadrupledBoxWinding_eq_zero_of_nearby_clear_point
      p degreePositive current.refinesAmbient current.proper certificate
  have fourZero : (4 : Int) = 0 := by
    calc
      4 = Winding.Box.Basic.quadrupledBoxWinding p current.box := current.rawWindingFour.symm
      _ = 0 := windingZero
  exact (show (4 : Int) ≠ 0 by decide) fourZero
end Purelib.RootIsolation.State.WindingOne.Exclusion

end
