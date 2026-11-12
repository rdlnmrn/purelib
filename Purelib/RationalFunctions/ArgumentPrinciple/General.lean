module
import Purelib.Data.Rat.Fraction.Basic
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

open Purelib.Data.Rat.Fraction (Rational)

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

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

universe u

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

/-- Attach degree, separation and outer winding certificates to the same retained reduced site families.

The original cancellation input and both actual multiplicity-bearing sides
are retained directly. All certificates consume those same stored sides;
neither a side constructor nor a root isolation producer is called here.
-/
@[expose] def fromSides {numerator denominator : CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator)
    (numeratorSites : Multiplicity.Side.Basic.SideResult input.reduction.numeratorReduced
      input.reduction.denominatorReduced)
    (denominatorSites : Multiplicity.Side.Basic.SideResult input.reduction.denominatorReduced
      input.reduction.numeratorReduced) : NonzeroResult numerator denominator :=
  { input := input
    numeratorSites := numeratorSites
    denominatorSites := denominatorSites
    numeratorMultiplicityDegree := numeratorSites.multiplicityDegree_eq_natDegree
    denominatorMultiplicityDegree := denominatorSites.multiplicityDegree_eq_natDegree
    jointSeparation := Multiplicity.Side.Separation.separateSides numeratorSites denominatorSites
    outerDegreeDifference := input.outer_boxWinding_eq_degreeDifference }

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

/-- Compute the original cancellation input once for a nonzero polynomial quotient.

The retained extended-Euclid result owns both reduced cofactors and their
original polynomial identities. Nonzeroness is derived from the same result.
-/
@[expose] def reducedInput (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (numeratorNonzero : numerator.isZero = false) :
    Reduction.Nonzero.NonzeroReducedInput numerator denominator :=
  let reduction := Reduction.Build.reduce numerator denominator denominatorNonzero
  { reduction := reduction
    numeratorReducedNonzero := reduction.numeratorReduced_nonzero numeratorNonzero }

/-- Construct the original numerator side from the same retained cancellation input. -/
@[expose] def numeratorSide {numerator denominator : CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator)
    (request : Option Rational := none) :
    Multiplicity.Side.Basic.SideResult input.reduction.numeratorReduced input.reduction.denominatorReduced :=
  Multiplicity.Side.Build.buildSide input.reduction.numeratorReduced input.reduction.denominatorReduced
    input.reduction.numeratorReduced_normalized input.numeratorReducedNonzero
    input.denominatorReducedNonzero (Reduction.Basic.ReducedPair.coprime input.reduction) request

/-- Construct the original denominator side from the same retained cancellation input. -/
@[expose] def denominatorSide {numerator denominator : CoefficientPolynomial}
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator)
    (request : Option Rational := none) :
    Multiplicity.Side.Basic.SideResult input.reduction.denominatorReduced input.reduction.numeratorReduced :=
  Multiplicity.Side.Build.buildSide input.reduction.denominatorReduced input.reduction.numeratorReduced
    input.reduction.denominatorReduced_normalized input.denominatorReducedNonzero
    input.numeratorReducedNonzero
    (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      (Reduction.Basic.ReducedPair.coprime input.reduction)) request

/-- Consume the original zero-numerator branch or its once computed nonzero cancellation input.

Both pure construction and checked replay use this same branch logic.
The nonzero callback receives the actual cached reduction together with
its complete original-input identity.
-/
@[expose] def withInput {α : Sort u} (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (zero : numerator.isZero = true → α)
    (nonzero : (numeratorNonzero : numerator.isZero = false) →
      (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator) →
      input = reducedInput numerator denominator denominatorNonzero numeratorNonzero → α) : α := by
  if numeratorZero : numerator.isZero = true then
    exact zero numeratorZero
  else
    have numeratorNonzero : numerator.isZero = false := by
      cases retained : numerator.isZero with
      | false => exact Eq.refl false
      | true => exact False.elim (numeratorZero retained)
    let input := reducedInput numerator denominator denominatorNonzero numeratorNonzero
    exact nonzero numeratorNonzero input rfl

/-- Compute cancellation and the finite zero/pole site result for a quotient with nonzero denominator.

Handle a zero numerator explicitly. Otherwise the shared branch constructor
retains its original reduction, zero/pole families, degree balances,
cross separation and common outer winding.
-/
@[expose] def prove (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (request : Option Rational := none) :
    Result numerator denominator :=
  withInput numerator denominator denominatorNonzero
    (fun numeratorZero => .zeroNumerator numeratorZero denominatorNonzero)
    (fun _ input _ => .nonzero
      (NonzeroResult.fromSides input (numeratorSide input request) (denominatorSide input request)))

/-- The original zero-numerator test gives exactly its complete zero outcome. -/
theorem prove_eq_zero (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (numeratorZero : numerator.isZero = true)
    (request : Option Rational := none) :
    prove numerator denominator denominatorNonzero request = .zeroNumerator numeratorZero denominatorNonzero := by
  unfold prove withInput
  split
  · rfl
  · exact False.elim (‹¬ numerator.isZero = true› numeratorZero)

/-- Retained original reduction and both complete original side readbacks preserve the full nonzero result. -/
theorem prove_eq_nonzero (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (numeratorNonzero : numerator.isZero = false)
    (input : Reduction.Nonzero.NonzeroReducedInput numerator denominator)
    (same : input = reducedInput numerator denominator denominatorNonzero numeratorNonzero)
    {request : Option Rational}
    (numeratorSites : Multiplicity.Side.Basic.SideResult input.reduction.numeratorReduced
      input.reduction.denominatorReduced) (numeratorSame : numeratorSites = numeratorSide input request)
    (denominatorSites : Multiplicity.Side.Basic.SideResult input.reduction.denominatorReduced
      input.reduction.numeratorReduced) (denominatorSame : denominatorSites = denominatorSide input request) :
    prove numerator denominator denominatorNonzero request =
      .nonzero (NonzeroResult.fromSides input numeratorSites denominatorSites) := by
  cases same
  rewrite [numeratorSame, denominatorSame]
  unfold prove withInput
  split
  · have impossible : false = true := numeratorNonzero.symm.trans ‹numerator.isZero = true›
    exact Bool.noConfusion impossible
  · rfl

/-- The absent event request preserves the complete original zero test, reduction and both retained sides. -/
theorem prove_none (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    prove numerator denominator denominatorNonzero none =
      withInput numerator denominator denominatorNonzero
        (fun numeratorZero => .zeroNumerator numeratorZero denominatorNonzero)
        (fun _ input _ => .nonzero
          (NonzeroResult.fromSides input (numeratorSide input) (denominatorSide input))) := rfl

namespace Result

/-- Both original reduced sides retain the complete Newton origins of all their higher root tracks. -/
@[expose] def NewtonOrigins {numerator denominator : CoefficientPolynomial} : Result numerator denominator → Prop
  | .zeroNumerator _ _ => True
  | .nonzero result => result.numeratorSites.NewtonOrigins ∧ result.denominatorSites.NewtonOrigins

end Result

/-- The original argument-principle constructor preserves exact Newton origins through cancellation and both sides. -/
theorem prove_newtonOrigins (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false) (request : Option Rational) :
    (prove numerator denominator denominatorNonzero request).NewtonOrigins := by
  unfold prove withInput
  split
  · exact True.intro
  · constructor
    · exact Multiplicity.Side.Build.buildSide_newtonOrigins _ _ _ _ _ _ request
    · exact Multiplicity.Side.Build.buildSide_newtonOrigins _ _ _ _ _ _ request

end Purelib.RationalFunctions.ArgumentPrinciple.General

end
