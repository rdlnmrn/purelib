module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

public import Purelib.Riemann.Paths.RectangularTraceParameterReadings
public import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Tactic.Ring

public section

/-! Read the exact parent-parameter increments of the retained dyadic
physical trace. The parent interval's width scales the physical trace steps. -/
namespace Purelib.Riemann.Paths.RectangularParentTraceSteps
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Paths.RectangularTraceParameterReadings (ParentParameters)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadic dyadicCount)
open Purelib.Data.Rat.Fraction.Compatibility
variable {lc lr rc rr genus depth : Nat} {lg : Geometry lc lr} {rg : Geometry rc rr}
  {piece : PairedSegmentPiece lg rg} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential
    : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : CenteredEdge curve differential} {first last : Coordinate}

/-- The retained trace transport starts at its original first parent parameter. -/
theorem first_parameter {count : Nat} {trace : Trace piece count}
    (transport : ParentParameters trace parent first last) : transport.parameters 0 = first := by
  rw [transport.parameters_eq, trace.first_eq]
  ring1

/-- Each retained parent-parameter step is the physical trace step times the original parameter span. -/
theorem step_eq {count : Nat} {trace : Trace piece count}
    (transport : ParentParameters trace parent first last) (edge : Fin count) :
    transport.parameters edge.succ - transport.parameters edge.castSucc =
      (trace.parameters edge.succ - trace.parameters edge.castSucc) * (last - first) := by
  rw [transport.parameters_eq, transport.parameters_eq]
  ring1

open Purelib.Integration in
open Purelib.Data in
/-- Every step of the actual retained dyadic trace has parameter width one half to its depth. -/
private theorem dyadic_parameter_step (edge : Fin (dyadicCount depth)) :
    (dyadic piece depth).parameters edge.succ - (dyadic piece depth).parameters edge.castSucc =
      (1 / 2 : Coordinate)^depth := by
  dsimp only [dyadic, Trace.build]
  rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  have step := (Path.Dyadic.DyadicSteps.tail_steps depth 0 1).indexed edge
  exact step.trans (by ring1)

/-- Read the exact parent-parameter increment from equality with the retained dyadic trace.

The original parent interval width multiplies the physical dyadic width, preserving both endpoint parameters and the
actual trace identity. -/
theorem dyadic_step {trace : Trace piece (dyadicCount depth)}
    (transport : ParentParameters trace parent first last) (retained : trace = dyadic piece depth)
    (edge : Fin (dyadicCount depth)) :
    transport.parameters edge.succ - transport.parameters edge.castSucc =
      (1 / 2 : Coordinate)^depth * (last - first) := by
  rw [step_eq transport edge, retained, dyadic_parameter_step]

open Purelib.Data in
/-- A parent interval contained in the unit interval scales dyadic steps by at most one.

The bound uses the retained trace equality and original endpoint inequalities, independently of any fragment count. -/
theorem dyadic_step_le {trace : Trace piece (dyadicCount depth)}
    (transport : ParentParameters trace parent first last) (retained : trace = dyadic piece depth)
    (firstNonnegative : 0 ≤ first) (lastLe : last ≤ 1) (edge : Fin (dyadicCount depth)) :
    transport.parameters edge.succ - transport.parameters edge.castSucc ≤ (1 / 2 : Coordinate)^depth := by
  rw [dyadic_step transport retained edge]
  have span : last - first ≤ 1 := (Rat.Fraction.Order.Arithmetic.sub_le_sub_direct lastLe firstNonnegative).trans_eq (by
    ring1)
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct span
    (Rat.Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth)).trans_eq (mul_one _)

end Purelib.Riemann.Paths.RectangularParentTraceSteps
