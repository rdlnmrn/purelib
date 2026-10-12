module
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Comparison
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace Purelib.Measure.CCL.Prefix
namespace PrefixFamilyProcess

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Two current-state realizations of a squared-sensitive probe have powered L2 distance bounded by expected scaled
cylinder spread. -/
theorem probe_poweredL2Distance_le_of_squaredSensitive {index : Type}
    (process : Cylinder.PrefixFamilyProcess index)
    (distribution : Measure.Distribution index)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (state : process.State) (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes (process.blocks state atom.item)
        (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun item => probe (leftPoints item))
        (fun item => probe (rightPoints item)) ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item) := by
  change distribution.expectation (fun item =>
      (probe (leftPoints item) - probe (rightPoints item)) ^ 2) ≤
    distribution.expectation fun item =>
      factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item)
  apply distribution.expectation_mono
  intro atom member
  rw [← Distance.NaturalLp.rationalSeparation_sq]
  exact Approximation.CCL.Prefix.realized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
open Purelib.Riemann.Integration in
/-- The squared-probe block request makes any two realizing expectations strictly closer than epsilon.

The positive sensitivity factor and epsilon determine the original process's requested state; both families realize that
same state's blocks. -/
theorem request_squaredProbeExpectations_pairwise_separation_lt
    {index : Type} (process : Cylinder.PrefixFamilyProcess index)
    (distribution : Measure.Distribution index)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (state : process.State) (epsilon : Fraction.Rational)
    (epsilonPositive : 0 < epsilon)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes
        (process.blocks
          (process.request state
            (Budget.requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => probe (leftPoints item))
        (distribution.expectation fun item => probe (rightPoints item)) <
      epsilon := by
  let requested := process.request state
    (Budget.requiredSquaredProbeBlockCount epsilon factor)
  have poweredL2Le := CCL.Prefix.PrefixFamilyProcess.probe_poweredL2Distance_le_of_squaredSensitive process
    distribution probe factor factorPositive.le sensitive requested
    leftPoints rightPoints leftRealizes rightRealizes
  have squaredLe :=
    (distribution.expectation_separation_sq_le_poweredL2Distance
      (fun item => probe (leftPoints item))
      (fun item => probe (rightPoints item))).trans poweredL2Le
  have budgetLe : distribution.expectation (fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested item)) ≤
      epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks requested item)) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive
          (process.request_length state
            (Budget.requiredSquaredProbeBlockCount epsilon factor) atom.item)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
