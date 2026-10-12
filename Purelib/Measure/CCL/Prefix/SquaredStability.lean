module
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.Comparison
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
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

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Two completed-prefix realizations of a squared-sensitive probe have powered L2 distance bounded by expected scaled
cylinder spread. -/
theorem prefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
    (distribution : Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  change distribution.expectation (fun certificate =>
      (probe (leftPoints certificate) - probe (rightPoints certificate)) ^ 2) ≤
    distribution.expectation fun certificate =>
      factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  rw [← Distance.NaturalLp.rationalSeparation_sq]
  exact Approximation.CCL.Prefix.realized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

/-- Two projective-prefix realizations have squared-probe powered L2 distance bounded by expected scaled cylinder
spread. -/
theorem projectivePrefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : Cylinder.CompletedProjectivePrefixCertificate →
      Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  change distribution.expectation (fun certificate =>
      (probe (leftPoints certificate) - probe (rightPoints certificate)) ^ 2) ≤
    distribution.expectation fun certificate =>
      factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  rw [← Distance.NaturalLp.rationalSeparation_sq]
  exact Approximation.CCL.Prefix.projectiveRealized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

end

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Squared expectation separation between completed-prefix realizations is bounded by expected scaled spread. -/
theorem prefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
    (distribution : Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ^ 2 ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (CCL.Prefix.prefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
        distribution probe factor factorNonnegative sensitive
        leftPoints rightPoints leftRealizes rightRealizes)

/-- Squared expectation separation between projective-prefix realizations is bounded by expected scaled spread. -/
theorem projectivePrefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : Cylinder.CompletedProjectivePrefixCertificate →
      Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ^ 2 ≤
      distribution.expectation fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (CCL.Prefix.projectivePrefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
        distribution probe factor factorNonnegative sensitive
        leftPoints rightPoints leftRealizes rightRealizes)

end

open Purelib
open Purelib.Approximation.Rational
open Purelib.CCL.Measure
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
open Purelib.Riemann.Integration
/-- The requested squared-probe block budget makes two completed-prefix realizing expectations strictly closer than
epsilon. -/
theorem prefixFamilySquaredProbe_expectations_pairwise_separation_lt_requested
    (distribution : Measure.Distribution
      Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Basic.Realizes atom.item.blocks (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) < epsilon := by
  have squaredLe :=
    CCL.Prefix.prefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
      distribution probe factor factorPositive.le sensitive
      leftPoints rightPoints leftRealizes rightRealizes
  have budgetLe : distribution.expectation (fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

/-- The requested squared-probe block budget makes two projective-prefix realizing expectations strictly closer than
epsilon. -/
theorem projectivePrefixFamilySquaredProbe_expectations_pairwise_separation_lt_requested
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : Cylinder.CompletedProjectivePrefixCertificate →
      Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) < epsilon := by
  have squaredLe :=
    CCL.Prefix.projectivePrefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
      distribution probe factor factorPositive.le sensitive
      leftPoints rightPoints leftRealizes rightRealizes
  have budgetLe : distribution.expectation (fun certificate =>
        factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

end Purelib.Measure.CCL.Prefix

end
