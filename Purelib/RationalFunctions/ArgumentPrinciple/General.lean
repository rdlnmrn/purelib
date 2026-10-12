module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
public import Purelib.RationalFunctions.Reduction.Build
import Purelib.RationalFunctions.Reduction.Nonzero
import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RootIsolation.Multiplicity.Side.Basic
public import Purelib.RootIsolation.Multiplicity.Side.Build
public import Purelib.RootIsolation.Multiplicity.Side.Separation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RationalFunctions.Bounds.Outer.Box
public import Purelib.RationalFunctions.Winding.Box.Outer
public import Purelib.RationalFunctions.Reduction.Coprime
public import Purelib.RootIsolation.Multiplicity.Side.Degree

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.General

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- Finite zero and pole sites for a nonzero reduced rational function.

Retain the exact cancellation input, both multiplicity-bearing site families, their degree balances and cross
separation, and the signed winding of the common outer square. -/
structure NonzeroResult
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The retained cancellation result with nonzero reduced numerator and denominator. -/ input :
    Reduction.Nonzero.NonzeroReducedInput
    numerator denominator
  /-- The zero-site family for the reduced numerator protected from the denominator. -/ numeratorSites :
    Multiplicity.Side.Basic.SideResult input.reduction.numeratorReduced
    input.reduction.denominatorReduced
  /-- The pole-site family for the reduced denominator protected from the numerator. -/ denominatorSites :
    Multiplicity.Side.Basic.SideResult input.reduction.denominatorReduced
    input.reduction.numeratorReduced
  /-- The total zero multiplicity equals the reduced numerator degree. -/ numeratorMultiplicityDegree :
    (Multiplicity.Side.Basic.SideResult.multiplicityDegree numeratorSites) =
      input.reduction.numeratorReduced.natDegree
  /-- The total pole multiplicity equals the reduced denominator degree. -/ denominatorMultiplicityDegree :
    (Multiplicity.Side.Basic.SideResult.multiplicityDegree denominatorSites) =
      input.reduction.denominatorReduced.natDegree
  /-- The retained zero and pole site families are separated. -/ jointSeparation :
    Multiplicity.Side.Separation.SidesSeparated numeratorSites denominatorSites
  /-- Ordinary winding on the common outer square equals the signed reduced degree difference. -/ outerDegreeDifference
    :
    Winding.Box.Basic.rationalBoxWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        (Reduction.Nonzero.NonzeroReducedInput.outerBox input) =
      (input.reduction.numeratorReduced.natDegree : Int) -
        input.reduction.denominatorReduced.natDegree

constructive_injectivity NonzeroResult

namespace NonzeroResult

open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Quadrupled outer winding is four times the reduced numerator degree minus four times denominator degree. -/
theorem outerWinding
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.General.NonzeroResult numerator denominator) :
    Winding.Box.Basic.rationalQuadrupledWinding
        result.input.reduction.numeratorReduced
        result.input.reduction.denominatorReduced (Reduction.Nonzero.NonzeroReducedInput.outerBox result.input) =
      (4 : Int) * result.input.reduction.numeratorReduced.natDegree -
        (4 : Int) * result.input.reduction.denominatorReduced.natDegree :=
  (Reduction.Nonzero.NonzeroReducedInput.outer_rationalWinding_eq_degreeDifference result.input)

/-- Read the retained ordinary outer winding identity for the reduced degree difference. -/
theorem outerBoxWinding
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : ArgumentPrinciple.General.NonzeroResult numerator denominator) :
    Winding.Box.Basic.rationalBoxWinding
        result.input.reduction.numeratorReduced
        result.input.reduction.denominatorReduced (Reduction.Nonzero.NonzeroReducedInput.outerBox result.input) =
      (result.input.reduction.numeratorReduced.natDegree : Int) -
        result.input.reduction.denominatorReduced.natDegree :=
  result.outerDegreeDifference

end NonzeroResult

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A total finite argument-principle outcome for a polynomial quotient.

An identically zero numerator retains the denominator nonzeroness proof separately. Otherwise the outcome carries the
complete reduced zero/pole site result. -/
inductive Result (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  : Type where
  /-- Report an identically zero numerator together with a nonzero denominator. -/ | zeroNumerator
      (numeratorZero : numerator.isZero = true)
      (denominatorNonzero : denominator.isZero = false)
  /-- Retain the complete finite result for a nonzero reduced quotient. -/ | nonzero (result :
    Purelib.RationalFunctions.ArgumentPrinciple.General.NonzeroResult numerator denominator)

constructive_injectivity Result

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Compute cancellation and the finite zero/pole site result for a quotient with nonzero denominator.

Handle a zero numerator explicitly. Otherwise retain both reduced multiplicity site families, their exact degree
balances, cross separation and common outer winding. -/
@[expose] def prove
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    ArgumentPrinciple.General.Result numerator denominator := by
  if numeratorZero : numerator.isZero = true then
    exact .zeroNumerator numeratorZero denominatorNonzero
  else
    have numeratorNonzero : numerator.isZero = false := by
      cases retained : numerator.isZero with
      | false => exact Eq.refl false
      | true => exact False.elim (numeratorZero retained)
    let reduction := Reduction.Build.reduce
      numerator denominator denominatorNonzero
    let input : Reduction.Nonzero.NonzeroReducedInput
        numerator denominator :=
      { reduction := reduction
        numeratorReducedNonzero :=
          reduction.numeratorReduced_nonzero numeratorNonzero }
    let numeratorSites := Multiplicity.Side.Build.buildSide input.reduction.numeratorReduced
      input.reduction.denominatorReduced
      input.reduction.numeratorReduced_normalized
      input.numeratorReducedNonzero input.denominatorReducedNonzero
      (Reduction.Basic.ReducedPair.coprime input.reduction)
    let symmetric :=
      Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
        (Reduction.Basic.ReducedPair.coprime input.reduction)
    let denominatorSites := Multiplicity.Side.Build.buildSide input.reduction.denominatorReduced
      input.reduction.numeratorReduced
      input.reduction.denominatorReduced_normalized
      input.denominatorReducedNonzero input.numeratorReducedNonzero symmetric
    exact .nonzero
      { input := input
        numeratorSites := numeratorSites
        denominatorSites := denominatorSites
        numeratorMultiplicityDegree :=
          numeratorSites.multiplicityDegree_eq_natDegree
        denominatorMultiplicityDegree :=
          denominatorSites.multiplicityDegree_eq_natDegree
        jointSeparation := Multiplicity.Side.Separation.separateSides numeratorSites denominatorSites
        outerDegreeDifference :=
          (Reduction.Nonzero.NonzeroReducedInput.outer_boxWinding_eq_degreeDifference input) }

end Purelib.RationalFunctions.ArgumentPrinciple.General

end
