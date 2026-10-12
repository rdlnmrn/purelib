module
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Index
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Sturm.Count.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Subdivision

open Purelib.Data.Rat.Interval.Proper (Cell)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Constructive root events on rationally parameterized curves

The constant-gcd branch of `CurveClear` excludes a polynomial
root everywhere on a rational curve.  This module handles the complementary
finite cases.  If both cleared coordinates vanish identically it records that
degeneracy explicitly.  Otherwise a nonconstant gcd is an ordinary nonzero
coordinate polynomial, so its derivative/gcd Sturm chain has the executable
event partition constructed in `ConstructiveSturmEventPartition`.
-/

namespace Purelib.RootIsolation.Curve.Event

/-- The finite reduced Sturm-event partition for the original curve-substitution gcd and its derivative on a retained
root cell. -/
abbrev EventPartition
    (p : CoefficientPolynomial) (curve : Curve.RationalCurve)
      (root : Cell) :=
  Dense.Rational.CauchyIndex.EventPartition.Basic.Partition
    (Dense.Derivative.derivative
      (Curve.Substitution.gcdPolynomial p curve))
    (Curve.Substitution.gcdPolynomial p curve) root

/-- Classify every leaf of a nonconstant curve-gcd Sturm calculation. -/
def eventPartition
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (data : Curve.Event.Nontrivial p curve) (root : Cell) :
    EventPartition p curve root :=
  Dense.Rational.CauchyIndex.EventPartition.Basic.classifyEvents
    (Dense.Derivative.derivative
      (Curve.Substitution.gcdPolynomial p curve))
    (Curve.Substitution.gcdPolynomial p curve)
    data.gcdNonzero root

/-- The parent doubled Sturm count is exactly the finite sum of its classified
leaf counts. -/
theorem eventPartition_count_sum
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (data : Curve.Event.Nontrivial p curve) (root : Cell) :
    Sturm.Count.Basic.sturmRootCount2
        (Curve.Substitution.gcdPolynomial p curve)
        root.interval.lower root.interval.upper =
      (((eventPartition data root).tree.leaves.map fun leaf =>
        Sturm.Count.Basic.sturmRootCount2
          (Curve.Substitution.gcdPolynomial p curve)
          leaf.interval.lower leaf.interval.upper).sum) := by
  exact Dense.Rational.CauchyIndex.EventPartition.Index.eventSubdivision_cellIndex2_sum
    (Dense.Derivative.derivative
      (Curve.Substitution.gcdPolynomial p curve))
    (Curve.Substitution.gcdPolynomial p curve)
    data.gcdNonzero root

end Purelib.RootIsolation.Curve.Event

end
