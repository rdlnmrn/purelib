module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
public import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Actual unit and second-kind remainder primitives on the original Legendre cap

Both finite numerators multiply the same supplied regular inverse model.
The ordinary value uses -2; after the retained second-kind reduction the
weighted value's regular remainder uses -2λw. These are independently built
primitive caches, not a holomorphic Fin-one disguise for x dx/y.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The full regular numerator of the ordinary dx/y cap pullback. -/
def unitNumerator : Coefficients := constant (-2)

/-- The full regular numerator left after the actual second-kind exact-term reduction. -/
def remainderNumerator (parameter : Canonical) : Coefficients := shift 1 (constant (-2 * parameter))

/-- The ordinary cap numerator evaluates to its exact signed degree factor. -/
private theorem packaged_unitNumerator_eval (point : Canonical) : unitNumerator.eval point = -2 := by
  exact eval_constant (-2) point

/-- The ordinary cap numerator evaluates to its exact signed degree factor. -/
theorem unitNumerator_eval (point : Canonical) : unitNumerator.eval point = -2 :=
  packaged_unitNumerator_eval point

/-- The retained second-kind remainder numerator is the exact full linear polynomial at w. -/
private theorem packaged_remainderNumerator_eval (parameter point : Canonical) :
    (remainderNumerator parameter).eval point = -2 * parameter * point := by
  unfold remainderNumerator
  rewrite [eval_shift, eval_constant, pow_one]
  ring1

/-- The retained second-kind remainder numerator is the exact full linear polynomial at w. -/
theorem remainderNumerator_eval (parameter point : Canonical) :
    (remainderNumerator parameter).eval point = -2 * parameter * point :=
  packaged_remainderNumerator_eval parameter point

/-- The actual frame-selected cubic has the ramified reciprocal origin.

Only its original polynomial/degree readbacks are used. The even-degree
alternative contradicts that same original cubic degree, without reducing
or replacing the opaque whole frame-selected curve constructor.
-/
private theorem packaged_frame_originOrder {parameter : Canonical} (frame : Paths.Frame parameter) :
    HyperellipticReciprocal.originOrder (Fibre.frameCurve frame) = 1 := by
  cases shape : (Fibre.frameCurve frame).degreeShape with
  | odd _ => rewrite [HyperellipticReciprocal.originOrder, shape]; rfl
  | even degree =>
    have original : (Fibre.frameCurve frame).polynomial.natDegree = 3 :=
      (congrArg (fun polynomial : Coefficients => polynomial.natDegree)
        (Fibre.frameCurve_polynomial frame)).trans (Paths.polynomial_natDegree parameter)
    have impossible : (3 : Nat) = 4 := original.symm.trans degree
    exact False.elim ((by decide +kernel : (3 : Nat) ≠ 4) impossible)

/-- The actual frame-selected cubic has the ramified reciprocal origin. -/
theorem frame_originOrder {parameter : Canonical} (frame : Paths.Frame parameter) :
    HyperellipticReciprocal.originOrder (Fibre.frameCurve frame) = 1 := packaged_frame_originOrder frame

/-- Construct the ordinary value's actual paid request, sample and quotient endpoint on the same retained cap.

The selected model stage comes from the actual original inverse request;
its sample and operational endpoint are retained together. No stage or
accuracy conclusion is supplied by the caller.
-/
def unitCap {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {data : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap data point owner) (target : Rational) (positive : 0 < target)
    (floor : Nat) (box : Box) :
    PolynomialSample.PaidEndpoint overlap (frame_originOrder frame) unitNumerator target positive floor box :=
  PolynomialSample.paidEndpoint (genus := 1) (curve := Fibre.frameCurve frame) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap (frame_originOrder frame) unitNumerator target positive floor box

/-- Construct the full second-kind remainder's actual paid request, sample and same quotient endpoint.

Only the regular remainder is constructed. The meromorphic exact term
2r/t retains its separate signed endpoint and oriented cancellation
obligation before an x dx/y period comparison follows.
-/
def remainderCap {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {data : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap data point owner) (target : Rational) (positive : 0 < target)
    (floor : Nat) (box : Box) : PolynomialSample.PaidEndpoint overlap (frame_originOrder frame)
      (remainderNumerator parameter) target positive floor box :=
  PolynomialSample.paidEndpoint (genus := 1) (curve := Fibre.frameCurve frame) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap (frame_originOrder frame) (remainderNumerator parameter)
    target positive floor box

end Purelib.Curves.Legendre.Polynomial.Reciprocal

end
