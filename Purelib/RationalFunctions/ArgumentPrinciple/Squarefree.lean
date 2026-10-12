module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RationalFunctions.Reduction.Nonzero
import Purelib.RationalFunctions.Winding.Box.Basic
public import Purelib.RootIsolation.Squarefree.Observation.Certified
public import Purelib.RootIsolation.Squarefree.Observation.Separation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RationalFunctions.Bounds.Outer.Box
public import Purelib.RationalFunctions.Winding.Box.Outer
public import Purelib.RationalFunctions.Reduction.Coprime

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Reduction.Basic (ReducedPair)
open Purelib.RationalFunctions.Reduction.Nonzero (NonzeroReducedInput)

section
public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RationalFunctions.ArgumentPrinciple.Squarefree

open Purelib.Polynomial in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- A nonzero reduced quotient with executable squarefree certificates for both cofactors. -/
structure SquarefreeInput
    (numerator denominator : CoefficientPolynomial) where
  /-- The exact retained nonzero reduction of the original polynomial pair. -/ nonzero :
    NonzeroReducedInput numerator denominator
  /-- The executable squarefree certificate of the reduced numerator. -/ numeratorSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      nonzero.reduction.numeratorReduced
  /-- The executable squarefree certificate of the reduced denominator. -/ denominatorSquarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      nonzero.reduction.denominatorReduced

constructive_injectivity SquarefreeInput

namespace SquarefreeInput

open Purelib.Polynomial
open Purelib.RationalFunctions
/-- Package the squarefree numerator with denominator nonzeroness and the retained coprimality certificate. -/
@[expose] def numeratorSide
    {numerator denominator : CoefficientPolynomial}
    (input : ArgumentPrinciple.Squarefree.SquarefreeInput numerator denominator) :
    Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput input.nonzero.reduction.numeratorReduced
      input.nonzero.reduction.denominatorReduced where
  sourceSquarefree := input.numeratorSquarefree
  sourceNonzero := input.nonzero.numeratorReducedNonzero
  oppositeNonzero := input.nonzero.denominatorReducedNonzero
  sourceOppositeCoprime := (ReducedPair.coprime input.nonzero.reduction)

/-- Package the squarefree denominator with numerator nonzeroness and the symmetric coprimality certificate. -/
@[expose] def denominatorSide
    {numerator denominator : CoefficientPolynomial}
    (input : ArgumentPrinciple.Squarefree.SquarefreeInput numerator denominator) :
    Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput input.nonzero.reduction.denominatorReduced
      input.nonzero.reduction.numeratorReduced where
  sourceSquarefree := input.denominatorSquarefree
  sourceNonzero := input.nonzero.denominatorReducedNonzero
  oppositeNonzero := input.nonzero.numeratorReducedNonzero
  sourceOppositeCoprime :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      (ReducedPair.coprime input.nonzero.reduction)

end SquarefreeInput

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
set_option genInjectivity false in
/-- Degree-exact squarefree zero and pole observations with joint separation and outer winding.

Both finite side results retain the same reduced input, including constant and linear cases. The common outer square has
the signed reduced degree-difference winding. -/
structure SquarefreeResult
    (numerator denominator : CoefficientPolynomial) where
  /-- The exact squarefree reduced input retained by both observation families. -/ input :
    SquarefreeInput numerator denominator
  /-- Certified squarefree zero observations for the retained numerator side. -/ numeratorSites :
    Squarefree.Observation.Certified.SquarefreeSideResult input.numeratorSide
  /-- Certified squarefree pole observations for the retained denominator side. -/ denominatorSites :
    Squarefree.Observation.Certified.SquarefreeSideResult input.denominatorSide
  /-- Separation of the retained numerator and denominator observations. -/ jointSeparation :
    Squarefree.Observation.Separation.SquarefreeObservationsSeparated
    numeratorSites.observation denominatorSites.observation
  /-- Quadrupled winding on the common outer square equals four times the reduced degree difference. -/ outerWinding :
    Winding.Box.Basic.rationalQuadrupledWinding
        input.nonzero.reduction.numeratorReduced
        input.nonzero.reduction.denominatorReduced (NonzeroReducedInput.outerBox input.nonzero) =
      (4 : Int) * input.nonzero.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.nonzero.reduction.denominatorReduced.natDegree
  /-- Ordinary winding on the common outer square equals the reduced degree difference. -/ outerBoxWinding :
    Winding.Box.Basic.rationalBoxWinding
        input.nonzero.reduction.numeratorReduced
        input.nonzero.reduction.denominatorReduced (NonzeroReducedInput.outerBox input.nonzero) =
      (input.nonzero.reduction.numeratorReduced.natDegree : Int) -
        input.nonzero.reduction.denominatorReduced.natDegree

constructive_injectivity SquarefreeResult

open Purelib.Polynomial in
open Purelib.RootIsolation in
open Purelib.RationalFunctions in
/-- Construct both certified squarefree observation families and their rational-function winding result.

Use the retained reduced coprimality certificate for cross separation and the exact common outer square for both winding
normalizations. -/
@[expose] def proveSquarefree
    {numerator denominator : CoefficientPolynomial}
    (input : SquarefreeInput numerator denominator) :
    SquarefreeResult numerator denominator :=
  let numeratorSites := Squarefree.Observation.Certified.proveSquarefreeSide input.numeratorSide
  let denominatorSites := Squarefree.Observation.Certified.proveSquarefreeSide input.denominatorSide
  { input := input
    numeratorSites := numeratorSites
    denominatorSites := denominatorSites
    jointSeparation := Squarefree.Observation.Separation.separateSquarefreeObservations
      numeratorSites.observation denominatorSites.observation
      (ReducedPair.coprime input.nonzero.reduction)
    outerWinding := (NonzeroReducedInput.outer_rationalWinding_eq_degreeDifference input.nonzero)
    outerBoxWinding := (NonzeroReducedInput.outer_boxWinding_eq_degreeDifference input.nonzero) }

end Purelib.RationalFunctions.ArgumentPrinciple.Squarefree

end
