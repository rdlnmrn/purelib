module
import Purelib.Polynomial.Ascending.Gaussian.Restriction.Integral
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!+# Generated, cached polynomial path partitions

The source is a finite ordered list of oriented polynomial segments.  A
partition restricts the polynomial as well as its geometry: the geometric
displacement supplies the Jacobian exactly once.  The constructors cache the
restricted polynomials, their samples and the assembled path model.  The
proof-facing integral is the existing Gaussian integration kernel's integral.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Segment.Basic

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A Gaussian polynomial in a segment's local unit parameter with retained oriented endpoints.

No continuity or endpoint-order assumption is imposed; displacement transports the exact polynomial integral onto this
oriented segment. -/
structure PolynomialSegment where
  /-- The retained oriented segment start. -/ start : Basic.Canonical
  /-- The retained oriented segment finish. -/ finish : Basic.Canonical
  /-- The exact Gaussian polynomial in the local segment parameter. -/ polynomial :
    Polynomial.Ascending.Gaussian.CoefficientPolynomial
deriving DecidableEq

constructive_injectivity PolynomialSegment

namespace PolynomialSegment

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- The original segment's Gaussian finish minus start. -/
def displacement (source :
  Gaussian.Segment.Basic.PolynomialSegment) : Basic.Canonical := source.finish - source.start

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Affinely evaluate the retained segment at the supplied rational parameter. -/
def point (source :
  Gaussian.Segment.Basic.PolynomialSegment) (input : Fraction.Rational) : Basic.Canonical :=
  source.start + source.displacement * RationalEmbedding.parameter input

open Purelib.Integration.Polynomial in
/-- Read the original segment as an exact polynomial cell with zero allowance and no observations. -/
def model (source :
  Gaussian.Segment.Basic.PolynomialSegment) : Gaussian.Cell.Basic.CellModel :=
  Gaussian.Cell.Basic.CellModel.exact source.start source.finish source.polynomial

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Multiply the retained segment displacement by the polynomial's exact unit integral. -/
def integralSample (source :
  Gaussian.Segment.Basic.PolynomialSegment) : Basic.Canonical :=
  source.displacement * Gaussian.Integral.definiteIntegral source.polynomial 0 1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- The difference of two affine segment points equals displacement times their embedded parameter difference. -/
theorem point_displacement (source :
  Gaussian.Segment.Basic.PolynomialSegment) (start finish : Fraction.Rational) :
    source.point finish - source.point start =
      source.displacement * (RationalEmbedding.parameter finish - RationalEmbedding.parameter start) := by
  unfold Gaussian.Segment.Basic.PolynomialSegment.point
  ring1

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial
/-- The segment's zero-parameter point is its original start. -/
@[simp] theorem point_zero (source :
  Gaussian.Segment.Basic.PolynomialSegment) : source.point 0 = source.start := by
  unfold Gaussian.Segment.Basic.PolynomialSegment.point
  rw [RationalEmbedding.parameter_zero, Basic.mul_zero, Basic.add_zero]

/-- The segment's unit-parameter point is its original finish. -/
@[simp] theorem point_one (source :
  Gaussian.Segment.Basic.PolynomialSegment) : source.point 1 = source.finish := by
  unfold Gaussian.Segment.Basic.PolynomialSegment.point Gaussian.Segment.Basic.PolynomialSegment.displacement
  rw [RationalEmbedding.parameter_one, Basic.mul_one]
  ring1

end

open Purelib.Integration.Polynomial in
/-- The exact cell model retains the original segment's integral sample. -/
@[simp] theorem model_integralSample
  (source : Gaussian.Segment.Basic.PolynomialSegment) :
    source.model.integralSample = source.integralSample := rfl
open Purelib.Integration.Polynomial
open Purelib.Polynomial.Ascending
/-- Reverse the original segment endpoints and its polynomial parameterization together. -/
def reversed (source :
  Gaussian.Segment.Basic.PolynomialSegment) : Gaussian.Segment.Basic.PolynomialSegment :=
  ⟨source.finish, source.start, Gaussian.Restriction.Basic.reverse source.polynomial⟩

/-- The exactly reversed original polynomial segment has the negative integral sample. -/
theorem reversed_integralSample (source :
  Gaussian.Segment.Basic.PolynomialSegment) :
    source.reversed.integralSample = -source.integralSample := by
  unfold Gaussian.Segment.Basic.PolynomialSegment.integralSample Gaussian.Segment.Basic.PolynomialSegment.displacement
    Gaussian.Segment.Basic.PolynomialSegment.reversed
  rw [Gaussian.Restriction.Integral.definiteIntegral_reverse_parameter]
  ring1

end PolynomialSegment
end Purelib.Integration.Polynomial.Gaussian.Segment.Basic

end
