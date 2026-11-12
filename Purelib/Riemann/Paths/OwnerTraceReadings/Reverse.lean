module

public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Reversing a retained stationary owner comparison

The two original tails and all selected comparison floors are reused.
Equality of their intrinsic lower targets is an explicit scalar input;
actual acquired tails at the same radicand derive it from acquisition.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTraceReadings.OwnerJoin

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation.SquareRootTrace

variable {parameter : Canonical} {left right : Owner parameter}

/-- Assemble an original join from its GIVEN two complete tails and one already selected comparison.

The constructor performs no tail acquisition or comparison selection.
-/
@[expose] def ofComparison (leftTail : OwnerTail left) (rightTail : OwnerTail right)
    (compared : Equivalence.Comparison (ownerApproximation left) (ownerApproximation right)
      leftTail.first rightTail.first (leftTail.lower / 1024)) : OwnerJoin left right :=
  ⟨leftTail, rightTail, compared⟩

/-- Reverse the SAME two tails and their actual comparison, transporting only the equal scalar lower target. -/
@[expose] def symm (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower) :
    OwnerJoin right left :=
  ofComparison join.rightTail join.leftTail
    (join.comparison.symm.castTarget (congrArg (fun lower : Rational => lower / 1024) sameLower))

/-- The reverse join retains the entire original right tail verbatim. -/
theorem symm_leftTail (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower) :
    (join.symm sameLower).leftTail = join.rightTail := rfl

/-- The reverse join retains the entire original left tail verbatim. -/
theorem symm_rightTail (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower) :
    (join.symm sameLower).rightTail = join.leftTail := rfl

/-- The reverse join reuses the exact selected original right floor, with no new comparison. -/
theorem symm_leftIndex (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower) :
    (join.symm sameLower).comparison.leftIndex = join.comparison.rightIndex := by
  exact (join.comparison.symm.castTarget_leftIndex
    (congrArg (fun lower : Rational => lower / 1024) sameLower)).trans join.comparison.symm_leftIndex

/-- The reverse join reuses the exact selected original left floor, with no new comparison. -/
theorem symm_rightIndex (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower) :
    (join.symm sameLower).comparison.rightIndex = join.comparison.leftIndex := by
  exact (join.comparison.symm.castTarget_rightIndex
    (congrArg (fun lower : Rational => lower / 1024) sameLower)).trans join.comparison.symm_rightIndex

/-- The entire reverse comparison is the original symmetric comparison under its scalar target transport. -/
theorem symm_comparison_heq (join : OwnerJoin left right)
    (sameLower : join.leftTail.lower = join.rightTail.lower) :
    HEq (join.symm sameLower).comparison join.comparison.symm := by
  exact join.comparison.symm.castTarget_heq (congrArg (fun lower : Rational => lower / 1024) sameLower)

end Purelib.Riemann.Paths.OwnerTraceReadings.OwnerJoin

end
