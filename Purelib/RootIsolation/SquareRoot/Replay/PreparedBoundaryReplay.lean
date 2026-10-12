module

import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Path
public import Purelib.Polynomial.Clearance.Pair.Replay
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.SquareRootDegree
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.Elab.Deriving.Repr
import Purelib.Geometry.Rational.Box.Intervals
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Restoring an original root-box boundary certificate

Four finite cofactor witnesses prove the original saved bound on the four
sides.  The new proof may differ, but the certificate's sole executable field
is unchanged.  This restores boundary clearance, not missing ambient-line
bounds or the root owner's construction history.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

open Purelib.Riemann.Integration

open Purelib.Polynomial.Geometry.BoxClearance
open Purelib.Polynomial.Path
open Purelib.RootIsolation.Winding

/-- The rational coordinate field for checked boundary-clearance bounds. -/
abbrev Coordinate := Fraction.Rational
/-- The dense Gaussian polynomial type checked on the retained boundary. -/
abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The rational rectangular box whose four sides are checked. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original finite polynomial-pair witness used by a side-clearance check. -/
abbrev Witness := Clearance.Pair.Replay.Witness

set_option genInjectivity false in
/-- Four retained polynomial-pair witnesses, one for each ordered side of the box.

The four fields retain the original cofactor tables in left, right, bottom and top order until each corresponding side
check certifies them. -/
structure Witnesses where
  /-- The retained polynomial-pair witness for the original box's left side. -/ left :
    SquareRoot.Replay.PreparedBoundaryReplay.Witness
  /-- The retained polynomial-pair witness for the original box's right side. -/ right :
    SquareRoot.Replay.PreparedBoundaryReplay.Witness
  /-- The retained polynomial-pair witness for the original box's bottom side. -/ bottom :
    SquareRoot.Replay.PreparedBoundaryReplay.Witness
  /-- The retained polynomial-pair witness for the original box's top side. -/ top :
    SquareRoot.Replay.PreparedBoundaryReplay.Witness

constructive_injectivity Witnesses

/-- The side of the original rectangular box associated with a check or failure. -/
inductive Side where
  /-- The original box's left side. -/ | left /-- The original box's right side. -/ | right /-- The original box's
    bottom side. -/ | bottom /-- The original box's top side. -/ | top
deriving DecidableEq
derive_exposed_repr Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay.Side

set_option genInjectivity false in
/-- The exact boundary-check request and its failing side and polynomial-pair reason.

The original polynomial, box and requested bound remain attached to the actual failing side and its retained
polynomial-pair rejection evidence. -/
structure Failure where
  /-- The exact polynomial supplied to the failed boundary check. -/ polynomial :
    SquareRoot.Replay.PreparedBoundaryReplay.Polynomial
  /-- The exact box supplied to the failed boundary check. -/ box : SquareRoot.Replay.PreparedBoundaryReplay.Box
  /-- The requested rational boundary-clearance bound. -/ requested :
    SquareRoot.Replay.PreparedBoundaryReplay.Coordinate
  /-- The original side on which checking failed. -/ side : SquareRoot.Replay.PreparedBoundaryReplay.Side
  /-- The retained polynomial-pair checking failure on that side. -/ reason : Clearance.Pair.Replay.Failure

constructive_injectivity Failure

set_option genInjectivity false in
/-- A boundary-clearance certificate with exactly the supplied polynomial, box and requested bound.

The certificate concerns the same retained polynomial and box; its bound equality preserves the exact original requested
rational value. -/
structure Checked (polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial) (box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box) (bound : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate) where
  /-- The actual reconstructed boundary-clearance certificate. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance polynomial box
  /-- The reconstructed certificate retains the requested bound exactly. -/ bound_eq : clearance.bound = bound

constructive_injectivity Checked

/-- Check the four retained side witnesses and reconstruct the requested boundary clearance.

Coprimality and interval bounds are checked on the exact vertical and horizontal restrictions; failure retains the
original request and side, while success preserves the requested bound exactly. -/
@[expose] def check (polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial) (box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box) (bound : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate)
    (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) : Except
      SquareRoot.Replay.PreparedBoundaryReplay.Failure (SquareRoot.Replay.PreparedBoundaryReplay.Checked polynomial box
      bound) := do
  let leftCoprime ← (Clearance.Pair.Replay.checkCoprime
    (Dense.Gaussian.Path.Components.pathReal polynomial (Gaussian.Cast.Winding.verticalBase box.xLower)
      Gaussian.Constants.imaginaryUnit)
    (Dense.Gaussian.Path.Components.pathImag polynomial (Gaussian.Cast.Winding.verticalBase box.xLower)
      Gaussian.Constants.imaginaryUnit)
    witnesses.left).mapError (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .left)
  let rightCoprime ← (Clearance.Pair.Replay.checkCoprime
    (Dense.Gaussian.Path.Components.pathReal polynomial (Gaussian.Cast.Winding.verticalBase box.xUpper)
      Gaussian.Constants.imaginaryUnit)
    (Dense.Gaussian.Path.Components.pathImag polynomial (Gaussian.Cast.Winding.verticalBase box.xUpper)
      Gaussian.Constants.imaginaryUnit)
    witnesses.right).mapError (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .right)
  let bottomCoprime ← (Clearance.Pair.Replay.checkCoprime
    (Dense.Gaussian.Path.Components.pathReal polynomial (Gaussian.Cast.Imaginary.horizontalBase box.yLower)
      Gaussian.Constants.horizontalDirection)
    (Dense.Gaussian.Path.Components.pathImag polynomial (Gaussian.Cast.Imaginary.horizontalBase box.yLower)
      Gaussian.Constants.horizontalDirection)
    witnesses.bottom).mapError (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .bottom)
  let topCoprime ← (Clearance.Pair.Replay.checkCoprime
    (Dense.Gaussian.Path.Components.pathReal polynomial (Gaussian.Cast.Imaginary.horizontalBase box.yUpper)
      Gaussian.Constants.horizontalDirection)
    (Dense.Gaussian.Path.Components.pathImag polynomial (Gaussian.Cast.Imaginary.horizontalBase box.yUpper)
      Gaussian.Constants.horizontalDirection)
    witnesses.top).mapError (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .top)
  let left ← (Clearance.Pair.Replay.checkCertified leftCoprime (Box.Intervals.verticalInterval box) bound).mapError
    (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .left)
  let right ← (Clearance.Pair.Replay.checkCertified rightCoprime (Box.Intervals.verticalInterval box) bound).mapError
    (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .right)
  let bottom ← (Clearance.Pair.Replay.checkCertified bottomCoprime (Box.Intervals.horizontalInterval box)
    bound).mapError
    (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .bottom)
  let top ← (Clearance.Pair.Replay.checkCertified topCoprime (Box.Intervals.horizontalInterval box) bound).mapError
    (SquareRoot.Replay.PreparedBoundaryReplay.Failure.mk polynomial box bound .top)
  let clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
    (Clearance.Box.Line.Path.verticalOfPathCertificate polynomial box box.xLower left.certificate)
    (Clearance.Box.Line.Path.verticalOfPathCertificate polynomial box box.xUpper right.certificate)
    (Clearance.Box.Line.Path.horizontalOfPathCertificate polynomial box box.yLower bottom.certificate)
    (Clearance.Box.Line.Path.horizontalOfPathCertificate polynomial box box.yUpper top.certificate)
  return ⟨clearance, by
    change min left.certificate.bound (min right.certificate.bound
      (min bottom.certificate.bound top.certificate.bound)) = bound
    rw [left.bound_eq, right.bound_eq, bottom.bound_eq, top.bound_eq, min_self, min_self, min_self]⟩

/-- Boundary-clearance certificates on the same polynomial and box are equal when their bounds agree. -/
theorem boundary_eq_of_bound_eq {polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial} {box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box}
    (first second : Clearance.Box.Boundary.Basic.BoundaryClearance polynomial box) (same : first.bound = second.bound) :
    first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Once the saved polynomial, box and bound are the original data, a
successful check restores the entire original boundary certificate.  No
equality of proof terms, root selection, or analytic assumption is requested. -/
theorem Checked.eq_original {polynomial : SquareRoot.Replay.PreparedBoundaryReplay.Polynomial} {box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box}
    (original : Clearance.Box.Boundary.Basic.BoundaryClearance polynomial box)
    (restored : SquareRoot.Replay.PreparedBoundaryReplay.Checked polynomial box original.bound) : restored.clearance =
      original :=
  SquareRoot.Replay.PreparedBoundaryReplay.boundary_eq_of_bound_eq restored.clearance original restored.bound_eq

/-- The exact Gaussian parameter type of the quadratic root polynomial. -/
abbrev Gaussian := Gaussian.Basic.Canonical

/-- Construct the degree-two root polynomial for the supplied Gaussian parameter. -/
@[expose] def rootPolynomial (parameter : SquareRoot.Replay.PreparedBoundaryReplay.Gaussian) : Polynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter Riemann.RootContinuation.SquareRootDegree.degreeTwo

/-- The finite method that established the exact requested quadratic boundary bound. -/
inductive Method where
  /-- The supplied finite Bézout witnesses establish the requested bound. -/ | bezout /-- The exact quadratic
    coefficient and gap bound establishes the requested bound. -/ | quadratic
derive_exposed_repr Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay.Method

set_option genInjectivity false in
/-- The checked quadratic boundary certificate together with the method establishing its bound.

The original parameter, box and requested bound identify the retained boundary certificate, and the method records which
finite route established that same bound. -/
structure QuadraticChecked (parameter : SquareRoot.Replay.PreparedBoundaryReplay.Gaussian) (box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box) (bound : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate) where
  /-- The retained certificate for the same quadratic polynomial, box and bound. -/ result :
    SquareRoot.Replay.PreparedBoundaryReplay.Checked (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
    box bound
  /-- The actual successful finite route used to certify this bound. -/ method :
    SquareRoot.Replay.PreparedBoundaryReplay.Method

constructive_injectivity QuadraticChecked

set_option genInjectivity false in
/-- A retained failure of both applicable routes to the requested quadratic clearance.

Distinguish nonpositive requests, invalid witnesses and an insufficient Bézout bound whose coefficient-based fallback
also misses. -/
inductive QuadraticFailure (parameter : SquareRoot.Replay.PreparedBoundaryReplay.Gaussian) (box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box) (bound : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate)
    (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) where
  /-- The requested clearance bound fails positivity. -/ | nonpositive (failed : ¬ 0 < bound)
  /-- The original witness check reports invalid finite data, retaining its exact procedure equation. -/ |
    invalidWitness (failure : SquareRoot.Replay.PreparedBoundaryReplay.Failure)
      (procedure : SquareRoot.Replay.PreparedBoundaryReplay.check
        (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) box bound witnesses = .error failure)
  /-- Retain the failed witness bound, its procedure equation, the exact quadratic ceiling and the failed comparison
    against that ceiling. -/ | insufficient (failure : SquareRoot.Replay.PreparedBoundaryReplay.Failure)
      (procedure : SquareRoot.Replay.PreparedBoundaryReplay.check
        (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) box bound witnesses = .error failure)
      (ceiling : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate)
      (ceiling_eq : ceiling = SquareRoot.Clearance.QuadraticCoefficientClearance.boundaryBound parameter box)
      (failed : ¬ bound ≤ ceiling)

constructive_injectivity QuadraticFailure

set_option backward.match.sparseCases false in
/-- Reuse the existing finite quadratic coefficient/gap theorem when a
valid Bézout witness has an insufficient majorant.  This preserves the saved
bound exactly; it does not replace the original owner by a strengthened one.
Malformed witnesses remain invalid, and a miss retains both failed methods.

The retained original witness check is consumed before any coefficient
fallback. Its exact procedure equation, computed ceiling and typed failure
or certificate remain tied to the same original request. -/
@[expose] def checkQuadratic (parameter : SquareRoot.Replay.PreparedBoundaryReplay.Gaussian) (box :
  SquareRoot.Replay.PreparedBoundaryReplay.Box) (bound : SquareRoot.Replay.PreparedBoundaryReplay.Coordinate)
    (witnesses : SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) :
    Except (SquareRoot.Replay.PreparedBoundaryReplay.QuadraticFailure parameter box bound witnesses)
      (SquareRoot.Replay.PreparedBoundaryReplay.QuadraticChecked parameter box bound) :=
  if positive : 0 < bound then
    match attempted : SquareRoot.Replay.PreparedBoundaryReplay.check
      (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) box bound witnesses with
    | .ok verified => .ok ⟨verified, .bezout⟩
    | .error failure =>
        match failure.reason with
        | .insufficient .. =>
            let ceiling := SquareRoot.Clearance.QuadraticCoefficientClearance.boundaryBound parameter box
            if carries : bound ≤ ceiling then
              let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
                (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) box :=
                { bound := bound
                  positive := positive
                  lower := fun point boundary => carries.trans
                    (by
                      have lower := SquareRoot.Clearance.QuadraticCoefficientClearance.boundary_lower parameter box
                        point boundary
                      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, ceiling,
                        SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial,
                        SquareRoot.Clearance.QuadraticCoefficientClearance.rootPolynomial] using lower) }
              .ok ⟨⟨clearance, rfl⟩, .quadratic⟩
            else .error (.insufficient failure attempted ceiling rfl carries)
        | _ => .error (.invalidWitness failure attempted)
  else .error (.nonpositive positive)

end Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay

end
