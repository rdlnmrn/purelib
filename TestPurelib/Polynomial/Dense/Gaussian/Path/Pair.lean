module

public import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-! # Exact edge records with shared affine coordinate construction -/

namespace TestPurelib.Polynomial.Dense.Gaussian.Path.Pair

open Purelib
open Purelib.Data
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Reproduce the former edge producer with its separate original coordinate substitutions. -/
private def original (p : CoefficientPolynomial) (origin direction : Canonical) (start stop : Rational) :
    PolynomialEdge where
  realPart := Dense.Gaussian.Path.Components.pathReal p origin direction
  imagPart := Dense.Gaussian.Path.Components.pathImag p origin direction
  start := start
  stop := stop

/-- The shared producer retains the complete former edge record for every source and endpoint pair. -/
private theorem agreement (p : CoefficientPolynomial) (origin direction : Canonical) (start stop : Rational) :
    PolynomialEdge.ofLine p origin direction start stop = original p origin direction start stop :=
  PolynomialEdge.ofLine_eq p origin direction start stop

/-- Materialize one original or shared edge at an explicit native timing boundary. -/
@[noinline] private def produce (cached : Bool) (p : CoefficientPolynomial)
    (origin direction : Canonical) (start stop : Rational) : IO PolynomialEdge :=
  pure (if cached then PolynomialEdge.ofLine p origin direction start stop
    else original p origin direction start stop)

/-- Check the complete same edge and its finite winding in both native timing orders. -/
private def compare (p : CoefficientPolynomial) (origin direction : Canonical)
    (start stop : Rational) (label : String) : IO Unit := do
  let began ← IO.monoNanosNow
  let former ← produce false p origin direction start stop
  let first ← IO.monoNanosNow
  let shared ← produce true p origin direction start stop
  let second ← IO.monoNanosNow
  unless former = shared do
    throw (IO.userError "shared affine coordinates changed the original complete edge record")
  let third ← IO.monoNanosNow
  let sharedAgain ← produce true p origin direction start stop
  let fourth ← IO.monoNanosNow
  let formerAgain ← produce false p origin direction start stop
  let fifth ← IO.monoNanosNow
  unless formerAgain = sharedAgain && former.doubledWinding = shared.doubledWinding do
    throw (IO.userError "shared affine coordinates changed an original edge or its winding")
  System.IO.println s!"same original factor degree={p.natDegree} edge={label}: \
    original_ns={first-began} shared_ns={second-first}; \
    reverse_shared_ns={fourth-third} reverse_original_ns={fifth-fourth}; complete edge and winding agree"
  (← IO.getStdout).flush

/-- Compare all four oriented coefficient-square edges on one same retained original factor. -/
private def compareFactor (p : CoefficientPolynomial) : IO Unit := do
  let box := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  compare p (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
    box.xLower box.xUpper "bottom"
  compare p (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
    box.yLower box.yUpper "right"
  compare p (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
    box.xUpper box.xLower "top"
  compare p (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
    box.yUpper box.yLower "left"

/-- Check exact edges on the positive factors computed by the original nonlinear localization preprocessing.

The original polynomial and degree evidence determine the same normalized
squarefree decomposition and positive multiplicity entries as production.
Timing covers only edge construction; neither factor isolation nor a complete
operational-equivalence decision is replaced by this phase measurement.
-/
public def profile (p : CoefficientPolynomial) (positive : 0 < p.natDegree) : IO Unit := do
  let nonzero := Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos positive
  let decomposition := Dense.Gaussian.Squarefree.Decomposition.Compute.decomposeNormalized p.normalize
    (Dense.Basic.DensePolynomial.normalize_normalize p)
    (by rewrite [Dense.Basic.DensePolynomial.isZero_normalize]; exact nonzero)
    (by rewrite [Dense.Basic.DensePolynomial.natDegree_normalize]; exact positive)
  let entries := decomposition.positiveMultiplicityEntries
  unless !entries.isEmpty do
    throw (IO.userError "original localization preprocessing returned no positive factor")
  for entry in entries do
    compareFactor entry.part.polynomial

end TestPurelib.Polynomial.Dense.Gaussian.Path.Pair
