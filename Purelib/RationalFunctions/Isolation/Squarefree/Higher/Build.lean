module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Dense.Gaussian.Degree
public import Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
import Purelib.RationalFunctions.Reduction.Nonzero
import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Build
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RationalFunctions.Bounds.Outer.Box

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Reduction.Nonzero (NonzeroReducedInput)

section
@[expose] public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic
namespace HigherSquarefreeInput

section
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- Construct winding-one isolation boxes for the reduced squarefree numerator.

Use the retained executable squarefree certificate and degree-at-least-two evidence with the polynomial box
construction. -/
def numeratorBoxes
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    FTA.Squarefree.BoxResult input.reduction.numeratorReduced :=
  FTA.Squarefree.Build.BoxFTA.prove
    { squarefree := input.numeratorSquarefree
      degreeAtLeastTwo := input.numeratorDegreeAtLeastTwo }

/-- Construct winding-one isolation boxes for the reduced squarefree denominator.

Use the retained executable squarefree certificate and degree-at-least-two evidence with the polynomial box
construction. -/
def denominatorBoxes
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    FTA.Squarefree.BoxResult input.reduction.denominatorReduced :=
  FTA.Squarefree.Build.BoxFTA.prove
    { squarefree := input.denominatorSquarefree
      degreeAtLeastTwo := input.denominatorDegreeAtLeastTwo }

/-- Select a reduced-numerator winding-one track by its retained degree-bounded index. -/
def numeratorTrack
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    Track.Basic.WindingOneTrack input.reduction.numeratorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.numeratorReduced) :=
  input.numeratorBoxes.isolation.trackAt index

/-- Select a reduced-denominator winding-one track by its retained degree-bounded index. -/
def denominatorTrack
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    Track.Basic.WindingOneTrack input.reduction.denominatorReduced
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        input.reduction.denominatorReduced) :=
  input.denominatorBoxes.isolation.trackAt index

end

open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Forget squarefreeness and higher-degree evidence while retaining the same reduction and numerator nonzeroness. -/
def nonzeroInput
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
    NonzeroReducedInput numerator denominator where
  reduction := input.reduction
  numeratorReducedNonzero :=
    Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos
      input.numeratorDegreePositive

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RationalFunctions in
/-- Read the common outer radius of the exact retained nonzero reduced pair. -/
abbrev commonOuterRadius
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) : Rat.Fraction.Rational :=
  (NonzeroReducedInput.outerRadius input.nonzeroInput)

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Read the common outer square of the exact retained nonzero reduced pair. -/
abbrev commonOuterBox
    {numerator denominator : CoefficientPolynomial}
    (input : Isolation.Squarefree.Higher.Basic.HigherSquarefreeInput numerator denominator) :
      Rational.Box :=
  (NonzeroReducedInput.outerBox input.nonzeroInput)
end HigherSquarefreeInput

end Purelib.RationalFunctions.Isolation.Squarefree.Higher.Basic

end
