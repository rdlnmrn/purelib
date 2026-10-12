module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Schedule.Common
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.CCL.Program
public import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone quarterRadius_weighted_sum)

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Integration.Program.Comparison.Scheduled

open Purelib.Data in
open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Program in
open Purelib.Riemann.Periods in
/-- Compare two original integration outputs through retained common-schedule sample bounds.

The certificate selects sufficiently late original schedule indices and combines both programs' own decay bounds with
the separate bridge scale to meet each positive target. -/
def scheduledProgram_output_equivalent
    (left right : Gaussian.Basic.RefinementProgram) (schedule : Approximation.Schedule.Common.CommonSchedule)
    (bridgeScale : Fraction.Rational) (bridgeScale_nonnegative : 0 ≤ bridgeScale)
    (samples : forall request,
      Data.Gaussian.Norm.Basic.normSq
          (((left.model (schedule.targetIndex request)).integralSample) -
            ((right.model (schedule.comparisonIndex request)).integralSample)) ≤
        Geometric.Basic.quarterRadius bridgeScale request) :
    Equivalence.NamedEquivalent left.output.name right.output.name := by
  let totalScale : Fraction.Rational :=
    2 * (left.errorScale + 2 * (bridgeScale + right.errorScale))
  have totalScale_nonnegative : 0 ≤ totalScale :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg bridgeScale_nonnegative right.errorScale_nonneg)))
  have equivalent : Equivalence.Equivalent
      left.approximation right.approximation := by
    refine { compare := ?_ }
    intro leftStart rightStart target positive
    let common := Geometric.Search.firstQuarterBelow totalScale
      (max leftStart rightStart) target
    have common_ge_left : leftStart ≤ common :=
      (Nat.Order.le_max_left leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have common_ge_right : rightStart ≤ common :=
      (Nat.Order.le_max_right leftStart rightStart).trans
        (Geometric.Search.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have totalSmall : Geometric.Basic.quarterRadius totalScale common <
        target :=
      Geometric.Search.firstQuarterBelow_accurate totalScale
        totalScale_nonnegative (max leftStart rightStart) target positive
    exact
      { leftIndex := schedule.targetIndex common
        rightIndex := schedule.comparisonIndex common
        left_ge := common_ge_left.trans (schedule.target_ge common)
        right_ge := common_ge_right.trans (schedule.comparison_ge common)
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftEarlier := schedule.targetIndex common
          let rightEarlier := schedule.comparisonIndex common
          have leftClose : Data.Gaussian.Norm.Basic.normSq
              ((left.model leftLater).integralSample -
                (left.model leftEarlier).integralSample) ≤
              Geometric.Basic.quarterRadius left.errorScale common :=
            by
              have scalar := left.later_close leftOrder
              rw [← Norm.Basic.normSq_eq_canonical] at scalar
              exact scalar.trans
                (quarterRadius_antitone left.errorScale_nonneg
                  (schedule.target_ge common))
          have middleClose := samples common
          have rightForward := right.later_close rightOrder
          rw [← Norm.Basic.normSq_eq_canonical] at rightForward
          have rightClose : Data.Gaussian.Norm.Basic.normSq
              ((right.model rightEarlier).integralSample -
                (right.model rightLater).integralSample) ≤
              Geometric.Basic.quarterRadius right.errorScale common := by
            rw [Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_symm]
            exact rightForward.trans
              (quarterRadius_antitone right.errorScale_nonneg
                (schedule.comparison_ge common))
          change Data.Gaussian.Norm.Basic.normSq
              ((left.model leftLater).integralSample -
                (right.model rightLater).integralSample) < target
          apply (Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_weighted_sum
            (left.model leftLater).integralSample
            (left.model leftEarlier).integralSample
            (right.model rightEarlier).integralSample
            (right.model rightLater).integralSample
            (Geometric.Basic.quarterRadius left.errorScale common)
            (Geometric.Basic.quarterRadius bridgeScale common)
            (Geometric.Basic.quarterRadius right.errorScale common)
            leftClose middleClose rightClose).trans_lt
          rw [quarterRadius_weighted_sum]
          exact totalSmall }
  simpa only [Gaussian.Basic.RefinementProgram.output,
    CertifiedProgram.Program.output,
    Gaussian.Basic.RefinementProgram.approximation,
    Name.Coherent.CoherentNamed.ofApproximation] using
    Sequence.Name.Equivalence.approximationEquivalent_toNamed equivalent

end Purelib.Integration.Program.Comparison.Scheduled

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Integration.Program.Comparison.Scheduled

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Program.Comparison in
/-- Lift retained common-schedule carrier sample bounds to equivalence of the two original coherent names.

Each original name remains linked to its own exact carrier output, and the bridge scale is applied at the same retained
requests. -/
def namedEquivalent_of_scheduled_samples
    (left right : Name.Coherent.CoherentNamed) (schedule : Approximation.Schedule.Common.CommonSchedule)
    (bridgeScale : Fraction.Rational) (bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall request,
      Data.Gaussian.Norm.Basic.normSq
          (((Gaussian.Basic.RefinementProgram.ofCoherentNamed left).model
              (schedule.targetIndex request)).integralSample -
            ((Gaussian.Basic.RefinementProgram.ofCoherentNamed right).model
              (schedule.comparisonIndex request)).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale request) :
    Equivalence.NamedEquivalent left.name right.name := by
  have leftCarrier : Equivalence.NamedEquivalent left.name
      (Gaussian.Basic.RefinementProgram.ofCoherentNamed left).output.name :=
    Integration.Program.Comparison.ofCoherentNamed_output_equivalent left
  have carriers : Equivalence.NamedEquivalent (Gaussian.Basic.RefinementProgram.ofCoherentNamed
    left).output.name
      (Gaussian.Basic.RefinementProgram.ofCoherentNamed right).output.name :=
    scheduledProgram_output_equivalent
      (Gaussian.Basic.RefinementProgram.ofCoherentNamed
        left) (Gaussian.Basic.RefinementProgram.ofCoherentNamed right) schedule bridgeScale
      bridgeScale_nonnegative samples
  have rightCarrier : Equivalence.NamedEquivalent right.name
      (Gaussian.Basic.RefinementProgram.ofCoherentNamed right).output.name :=
    Integration.Program.Comparison.ofCoherentNamed_output_equivalent right
  exact Equivalence.NamedEquivalent.trans leftCarrier
    (Equivalence.NamedEquivalent.trans carriers
      (Equivalence.NamedEquivalent.symm rightCarrier))

end Purelib.Integration.Program.Comparison.Scheduled

end
