module
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Riemann.Periods.PeriodCurves
import Purelib.Data.Fin.Cases
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.RootIsolation.SquareRoot.Subdivision.Dyadic.Eight
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.Riemann.Periods

section
public section

/-!
# Dyadic displacement certificates for the quartic connector

This module identifies the 64 canonical centred edges of the explicit
A-backward horizontal path with the independently generated rational root
and sample data.  The reversed stationary prefix is handled separately as a
zero-displacement path.
-/

namespace Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement
section ABackward

open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Rat.Fraction renaming Rational -> Q

/-- Every eighth-step edge has squared displacement one over 1024.

The retained clear segment has total squared displacement one over 16; the eight canonical dyadic edges divide its
parameter uniformly. -/
theorem aBackwardDyadicStepMovement
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullMovement : Gaussian.Norm.Basic.normSq
      (segment.pointAt 1 - segment.pointAt 0) = (1 / 16 : Q))
    (edge : Fin 8) :
    Gaussian.Norm.Basic.normSq
        (segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter) =
      (1 / 1024 : Q) := by
  have fullFormula := segment.normSq_pointAt_sub_pointAt 1 0
  have endpointMovement :
      Gaussian.Norm.Basic.normSq (finish - start) =
        (1 / 16 : Q) := by
    have formula :
        Gaussian.Norm.Basic.normSq
            (segment.pointAt 1 - segment.pointAt 0) =
          Gaussian.Norm.Basic.normSq (finish - start) := by
      simpa only [show (1 : Q) - 0 = 1 by decide, one_pow, one_mul] using fullFormula
    exact formula.symm.trans fullMovement
  rw [segment.normSq_pointAt_sub_pointAt, endpointMovement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference, pow_two,
    Fraction.Field.div_mul_div_direct]
  rw [show (1 : Q) * 1 = 1 by ring1,
    show (8 : Q) * 8 = 64 by ring1,
    Fraction.Field.div_mul_div_direct]
  rw [show (1 : Q) * 1 = 1 by ring1,
    show (64 : Q) * 16 = 1024 by ring1]

/-- A horizontal displacement of minus one quarter divides into steps of minus one thirty-second.

Each canonical eighth-step edge retains the same clear segment and exact affine interpolation. -/
theorem aBackwardDyadicStepDisplacement
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullDisplacement : segment.pointAt 1 - segment.pointAt 0 =
      point (-1 / 4) 0)
    (edge : Fin 8) :
    segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
        segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
      point (-1 / 32) 0 := by
  have endpointDisplacement : finish - start = point (-1 / 4) 0 := by
    rw [segment.pointAt_sub_pointAt] at fullDisplacement
    apply Gaussian.Basic.ext
    · have real := congrArg Gaussian.Basic.re
          fullDisplacement
      change 1 * (finish - start).re = (point (-1 / 4) 0).re at real
      change (finish - start).re = (point (-1 / 4) 0).re
      simpa only [one_mul] using real
    · have imaginary := congrArg Gaussian.Basic.im
          fullDisplacement
      change 1 * (finish - start).im = (point (-1 / 4) 0).im at imaginary
      change (finish - start).im = (point (-1 / 4) 0).im
      simpa only [one_mul] using imaginary
  rw [segment.pointAt_sub_pointAt, endpointDisplacement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference]
  apply Gaussian.Basic.ext <;>
    with_unfolding_all decide
end ABackward
end Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement

end

section
public section

/-!
# Generated sample certificates for the quartic B-backward connector

This module connects the 128 generated rational root and quotient samples to
the canonical centred edges already cached by the explicit B-backward bank.
The prepared-cell accessors keep these proofs from reconstructing the
dependent owner thread.
-/

namespace Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement
section BBackward

open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Rat.Fraction renaming Rational -> Q

/-- A vertical displacement of minus one eighth divides into steps of minus one sixty-fourth.

The equality holds for every canonical eighth-step edge of the retained clear segment. -/
theorem bBackwardVerticalDyadicStepDisplacement
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullDisplacement : segment.pointAt 1 - segment.pointAt 0 =
      point 0 (-1 / 8))
    (edge : Fin 8) :
    segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
        segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
      point 0 (-1 / 64) := by
  have endpointDisplacement : finish - start = point 0 (-1 / 8) := by
    rw [segment.pointAt_sub_pointAt] at fullDisplacement
    apply Gaussian.Basic.ext
    · have real := congrArg Gaussian.Basic.re
          fullDisplacement
      change 1 * (finish - start).re = (point 0 (-1 / 8)).re at real
      simpa only [one_mul] using real
    · have imaginary := congrArg Gaussian.Basic.im
          fullDisplacement
      change 1 * (finish - start).im = (point 0 (-1 / 8)).im at imaginary
      simpa only [one_mul] using imaginary
  rw [segment.pointAt_sub_pointAt, endpointDisplacement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference]
  apply Gaussian.Basic.ext
  · change (1 / 8 : Q) * 0 = 0
    ring1
  · change (1 / 8 : Q) * (-1 / 8) = -1 / 64
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by decide)).ne'
    ring1

/-- A horizontal displacement of minus one eighth divides into steps of minus one sixty-fourth.

The equality holds for every canonical eighth-step edge of the retained clear segment. -/
theorem bBackwardHorizontalDyadicStepDisplacement
    {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullDisplacement : segment.pointAt 1 - segment.pointAt 0 =
      point (-1 / 8) 0)
    (edge : Fin 8) :
    segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
        segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
      point (-1 / 64) 0 := by
  have endpointDisplacement : finish - start = point (-1 / 8) 0 := by
    rw [segment.pointAt_sub_pointAt] at fullDisplacement
    apply Gaussian.Basic.ext
    · have real := congrArg Gaussian.Basic.re
          fullDisplacement
      change 1 * (finish - start).re = (point (-1 / 8) 0).re at real
      simpa only [one_mul] using real
    · have imaginary := congrArg Gaussian.Basic.im
          fullDisplacement
      change 1 * (finish - start).im = (point (-1 / 8) 0).im at imaginary
      simpa only [one_mul] using imaginary
  rw [segment.pointAt_sub_pointAt, endpointDisplacement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference]
  apply Gaussian.Basic.ext
  · change (1 / 8 : Q) * (-1 / 8) = -1 / 64
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by decide)).ne'
    ring1
  · change (1 / 8 : Q) * 0 = 0
    ring1
end BBackward
end Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement

end

section
public section

/-! # Generated sample certificates for the quartic B-forward connector -/

namespace Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement
section BForward

open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Rat.Fraction renaming Rational -> Q

/-- A horizontal displacement of plus one eighth divides into steps of plus one sixty-fourth.

The equality holds for every canonical eighth-step edge of the retained clear segment. -/
theorem bForwardHorizontalDyadicStepDisplacement
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullDisplacement : segment.pointAt 1 - segment.pointAt 0 =
      point (1 / 8) 0)
    (edge : Fin 8) :
    segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
        segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
      point (1 / 64) 0 := by
  have endpointDisplacement : finish - start = point (1 / 8) 0 := by
    rw [segment.pointAt_sub_pointAt] at fullDisplacement
    apply Gaussian.Basic.ext
    · have real := congrArg Gaussian.Basic.re
          fullDisplacement
      change 1 * (finish - start).re = (point (1 / 8) 0).re at real
      simpa only [one_mul] using real
    · have imaginary := congrArg Gaussian.Basic.im
          fullDisplacement
      change 1 * (finish - start).im = (point (1 / 8) 0).im at imaginary
      simpa only [one_mul] using imaginary
  rw [segment.pointAt_sub_pointAt, endpointDisplacement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference]
  apply Gaussian.Basic.ext
  · change (1 / 8 : Q) * (1 / 8) = 1 / 64
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by decide)).ne'
    ring1
  · change (1 / 8 : Q) * 0 = 0
    ring1

/-- A vertical displacement of plus one eighth divides into steps of plus one sixty-fourth.

The equality holds for every canonical eighth-step edge of the retained clear segment. -/
theorem bForwardVerticalDyadicStepDisplacement
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment PeriodCurves.quarticCurve.polynomial
      ambient start finish)
    (fullDisplacement : segment.pointAt 1 - segment.pointAt 0 =
      point 0 (1 / 8))
    (edge : Fin 8) :
    segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
        segment.pointAt (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
      point 0 (1 / 64) := by
  have endpointDisplacement : finish - start = point 0 (1 / 8) := by
    rw [segment.pointAt_sub_pointAt] at fullDisplacement
    apply Gaussian.Basic.ext
    · have real := congrArg Gaussian.Basic.re
          fullDisplacement
      change 1 * (finish - start).re = (point 0 (1 / 8)).re at real
      simpa only [one_mul] using real
    · have imaginary := congrArg Gaussian.Basic.im
          fullDisplacement
      change 1 * (finish - start).im = (point 0 (1 / 8)).im at imaginary
      simpa only [one_mul] using imaginary
  rw [segment.pointAt_sub_pointAt, endpointDisplacement]
  have parameterDifference :
      (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
        (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget edge)).parameter -
          (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint
            (RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource edge)).parameter =
        (1 / 8 : Q) := by
    rw [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondMeshEndpoint_parameter]
    rcases Data.Fin.Cases.ExplicitQuarticPreparedALeftSampleCertificatesPart1.aLeftBoundaryFinEightCases edge with
      h | h | h | h | h | h | h | h
    all_goals subst edge
    all_goals simp only [RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeTarget,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondEdgeSource,
      RootIsolation.SquareRoot.Subdivision.Dyadic.Eight.secondGridEndpoint,
      Fraction.Field.div_eq_mul_inv_direct]
    all_goals ring1
  rw [parameterDifference]
  apply Gaussian.Basic.ext
  · change (1 / 8 : Q) * 0 = 0
    ring1
  · change (1 / 8 : Q) * (1 / 8) = 1 / 64
    rw [Fraction.Field.div_mul_div_direct]
    apply Fraction.Field.div_eq_div_of_cross_mul
      (Fraction.Field.mul_ne_zero_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne')
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by decide)).ne'
    ring1
end BForward
end Purelib.Polynomial.Special.QuarticMinusOne.ClearPath.DyadicDisplacement

end
