module
public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Sign.ComplexProduct.Center.Basic
public import Purelib.Data.Sign.ComplexProduct.Center.Search
public import Purelib.Geometry.Rational.Plane.Turn.Basic
import Purelib.Geometry.Rational.Plane.Turn.Center
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Sign.ComplexProduct.Center.Admissible

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

section

section

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

/-- Admissibility of formal product center signs for six polynomial endpoint values.

The finite sign relation is evaluated at both endpoints of the retained rational interval. -/
def Admissible
    (centers : Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns)
    (A B C D E H : CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) : Prop :=
  centers.AdmissibleSigns
    (Data.Sign.ofCoordinate (A.eval interval.lower))
    (Data.Sign.ofCoordinate (B.eval interval.lower))
    (Data.Sign.ofCoordinate (C.eval interval.lower))
    (Data.Sign.ofCoordinate (D.eval interval.lower))
    (Data.Sign.ofCoordinate (E.eval interval.lower))
    (Data.Sign.ofCoordinate (H.eval interval.lower))
    (Data.Sign.ofCoordinate (A.eval interval.upper))
    (Data.Sign.ofCoordinate (B.eval interval.upper))
    (Data.Sign.ofCoordinate (C.eval interval.upper))
    (Data.Sign.ofCoordinate (D.eval interval.upper))
    (Data.Sign.ofCoordinate (E.eval interval.upper))
    (Data.Sign.ofCoordinate (H.eval interval.upper))

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

namespace Purelib.RootIsolation.Cauchy.ProductCells.ProductCenterSigns

/-- Decide center-sign admissibility from the finite polynomial endpoint signs. -/
instance (centers : Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns)
    (A B C D E H : CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Decidable (centers.Admissible A B C D E H interval) := by
  unfold Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns.Admissible
  infer_instance

end Purelib.RootIsolation.Cauchy.ProductCells.ProductCenterSigns

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

/-- Search the finite center-sign table against the six polynomials at both endpoints.

Return the first admissible center record, or no record when the finite search finds none. -/
def search?
    (A B C D E H : CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Option Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns :=
  Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns.signSearch?
    (Data.Sign.ofCoordinate (A.eval interval.lower))
    (Data.Sign.ofCoordinate (B.eval interval.lower))
    (Data.Sign.ofCoordinate (C.eval interval.lower))
    (Data.Sign.ofCoordinate (D.eval interval.lower))
    (Data.Sign.ofCoordinate (E.eval interval.lower))
    (Data.Sign.ofCoordinate (H.eval interval.lower))
    (Data.Sign.ofCoordinate (A.eval interval.upper))
    (Data.Sign.ofCoordinate (B.eval interval.upper))
    (Data.Sign.ofCoordinate (C.eval interval.upper))
    (Data.Sign.ofCoordinate (D.eval interval.upper))
    (Data.Sign.ofCoordinate (E.eval interval.upper))
    (Data.Sign.ofCoordinate (H.eval interval.upper))

/-- A returned center-sign record is admissible for the actual polynomial endpoints. -/
theorem search?_some_admissible
    {A B C D E H : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    {centers : Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns}
    (found : search? A B C D E H interval = some centers) :
    centers.Admissible A B C D E H interval := by
  exact Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns.signSearch?_some_admissible found

/-- The finite center-sign search succeeds for two narrow endpoint turns.

Every factor and product coordinate must be nonzero at both endpoints, and the four displayed equalities must identify
the product coordinates. -/
theorem search?_isSome_of_narrowTurns
    {A B C D E H : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (AₗNonzero : A.eval interval.lower ≠ 0)
    (BₗNonzero : B.eval interval.lower ≠ 0)
    (CₗNonzero : C.eval interval.lower ≠ 0)
    (DₗNonzero : D.eval interval.lower ≠ 0)
    (EₗNonzero : E.eval interval.lower ≠ 0)
    (HₗNonzero : H.eval interval.lower ≠ 0)
    (AᵣNonzero : A.eval interval.upper ≠ 0)
    (BᵣNonzero : B.eval interval.upper ≠ 0)
    (CᵣNonzero : C.eval interval.upper ≠ 0)
    (DᵣNonzero : D.eval interval.upper ≠ 0)
    (EᵣNonzero : E.eval interval.upper ≠ 0)
    (HᵣNonzero : H.eval interval.upper ≠ 0)
    (productRealLowerEq : E.eval interval.lower =
      A.eval interval.lower * C.eval interval.lower -
        B.eval interval.lower * D.eval interval.lower)
    (productImagLowerEq : H.eval interval.lower =
      A.eval interval.lower * D.eval interval.lower +
        B.eval interval.lower * C.eval interval.lower)
    (productRealUpperEq : E.eval interval.upper =
      A.eval interval.upper * C.eval interval.upper -
        B.eval interval.upper * D.eval interval.upper)
    (productImagUpperEq : H.eval interval.upper =
      A.eval interval.upper * D.eval interval.upper +
        B.eval interval.upper * C.eval interval.upper)
    (leftNarrow : Geometry.Rational.Plane.Turn.Basic.NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : Geometry.Rational.Plane.Turn.Basic.NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper)) :
    (search? A B C D E H interval).isSome := by
  unfold search?
  rw [productRealLowerEq, productImagLowerEq,
    productRealUpperEq, productImagUpperEq]
  exact Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns.signSearch?_isSome_of_narrowTurns
    AₗNonzero BₗNonzero CₗNonzero DₗNonzero
    (by simpa only [← productRealLowerEq] using EₗNonzero)
    (by simpa only [← productImagLowerEq] using HₗNonzero)
    AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero
    (by simpa only [← productRealUpperEq] using EᵣNonzero)
    (by simpa only [← productImagUpperEq] using HᵣNonzero)
    leftNarrow rightNarrow

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

end
end

end
