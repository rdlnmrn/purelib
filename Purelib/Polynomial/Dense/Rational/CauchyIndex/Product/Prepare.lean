module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Prepare
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Center
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Event
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Sign.Basic
import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.ComplexProduct.Center.Basic
import Purelib.Data.Sign.Stability
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Prepare

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)

/-- Execute the local product-event searches and endpoint checks, retaining their selected certificate.

Three original event searches run in left, right and product order before
the finite center search. Success retains their exact returned records,
checks six imaginary endpoint values and four coordinate identities, and
constructs the corresponding recentered local event certificate. -/
@[expose] public def localEventData?
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Option (CauchyIndex.Product.Event.LocalEventData A B C D E H interval) := by
  match leftFound : CauchyIndex.Events.Prepare.cauchyEventSigns? A B interval with
  | none => exact none
  | some left =>
    match rightFound : CauchyIndex.Events.Prepare.cauchyEventSigns? C D interval with
    | none => exact none
    | some right =>
      match productFound : CauchyIndex.Events.Prepare.cauchyEventSigns? E H interval with
      | none => exact none
      | some product =>
        match centerFound : ProductCenterSigns.search?
            A B C D E H interval with
        | none => exact none
        | some centers =>
          if admissible : centers.Admissible A B C D E H interval then
            if leftImagLower : B.eval interval.lower ≠ 0 then
              if rightImagLower : D.eval interval.lower ≠ 0 then
                if productImagLower : H.eval interval.lower ≠ 0 then
                  if leftImagUpper : B.eval interval.upper ≠ 0 then
                    if rightImagUpper : D.eval interval.upper ≠ 0 then
                      if productImagUpper : H.eval interval.upper ≠ 0 then
                        if productRealLowerEq : E.eval interval.lower =
                            A.eval interval.lower * C.eval interval.lower -
                              B.eval interval.lower * D.eval interval.lower then
                          if productImagLowerEq : H.eval interval.lower =
                              A.eval interval.lower * D.eval interval.lower +
                                B.eval interval.lower * C.eval interval.lower then
                            if productRealUpperEq : E.eval interval.upper =
                                A.eval interval.upper * C.eval interval.upper -
                                  B.eval interval.upper * D.eval interval.upper then
                              if productImagUpperEq : H.eval interval.upper =
                                  A.eval interval.upper * D.eval interval.upper +
                                    B.eval interval.upper * C.eval interval.upper then
                                exact some (CauchyIndex.Product.Event.LocalEventData.ofRecenteredFactors
                                  left right product
                                  centers.factorLeftReal centers.factorLeftImag
                                  centers.factorRightReal centers.factorRightImag
                                  admissible.1 admissible.2.1 admissible.2.2
                                  leftImagLower rightImagLower productImagLower
                                  leftImagUpper rightImagUpper productImagUpper
                                  productRealLowerEq productImagLowerEq
                                  productRealUpperEq productImagUpperEq)
                              else exact none
                            else exact none
                          else exact none
                        else exact none
                      else exact none
                    else exact none
                  else exact none
                else exact none
              else exact none
            else exact none
          else exact none

/-- The local product-event classifier succeeds when its finite searches and endpoint checks succeed.

The hypotheses retain three event-sign results, a center-sign result, six nonzero imaginary endpoints and the four
product-coordinate identities. -/
public theorem localEventData?_isSome
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (leftFound : (CauchyIndex.Events.Prepare.cauchyEventSigns? A B interval).isSome = true)
    (rightFound : (CauchyIndex.Events.Prepare.cauchyEventSigns? C D interval).isSome = true)
    (productFound : (CauchyIndex.Events.Prepare.cauchyEventSigns? E H interval).isSome = true)
    (centerFound :
      (ProductCenterSigns.search? A B C D E H interval).isSome = true)
    (leftImagLower : B.eval interval.lower ≠ 0)
    (rightImagLower : D.eval interval.lower ≠ 0)
    (productImagLower : H.eval interval.lower ≠ 0)
    (leftImagUpper : B.eval interval.upper ≠ 0)
    (rightImagUpper : D.eval interval.upper ≠ 0)
    (productImagUpper : H.eval interval.upper ≠ 0)
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
        B.eval interval.upper * C.eval interval.upper) :
    (localEventData? A B C D E H interval).isSome = true := by
  cases leftEquation : CauchyIndex.Events.Prepare.cauchyEventSigns? A B interval with
  | none =>
    have impossible : (false : Bool) = true :=
      (congrArg Option.isSome leftEquation).symm.trans leftFound
    cases impossible
  | some left =>
    cases rightEquation : CauchyIndex.Events.Prepare.cauchyEventSigns? C D interval with
    | none =>
      have impossible : (false : Bool) = true :=
        (congrArg Option.isSome rightEquation).symm.trans rightFound
      cases impossible
    | some right =>
      cases productEquation : CauchyIndex.Events.Prepare.cauchyEventSigns? E H interval with
      | none =>
        have impossible : (false : Bool) = true :=
          (congrArg Option.isSome productEquation).symm.trans productFound
        cases impossible
      | some product =>
        cases centerEquation : ProductCenterSigns.search?
            A B C D E H interval with
        | none =>
          have impossible : (false : Bool) = true :=
            (congrArg Option.isSome centerEquation).symm.trans centerFound
          cases impossible
        | some centers =>
          have admissible : centers.Admissible A B C D E H interval :=
            ProductCenterSigns.search?_some_admissible centerEquation
          unfold localEventData?
          rw [leftEquation, rightEquation, productEquation, centerEquation]
          dsimp only
          rw [dif_pos admissible, dif_pos leftImagLower,
            dif_pos rightImagLower, dif_pos productImagLower,
            dif_pos leftImagUpper, dif_pos rightImagUpper,
            dif_pos productImagUpper, dif_pos productRealLowerEq,
            dif_pos productImagLowerEq, dif_pos productRealUpperEq,
            dif_pos productImagUpperEq]
          rfl

/-- Test whether the finite local product-event classifier returns certified event data.

The Boolean is precisely the `isSome` reading of the retained local
event-data procedure for the same six coordinate polynomials and interval.
It does not run a separate search or replace the selected event record. -/
@[expose] public def localProductCell?
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) : Bool :=
  (localEventData? A B C D E H interval).isSome

/-- A successful local product-cell check supplies the auxiliary Cauchy product formula on the displayed interval.

The check is the `isSome` reading of the same retained event-data procedure.
Its actual successful certificate supplies the formula without replacing
any selected event, center-sign record or polynomial input. -/
public theorem auxiliaryProductFormula_of_localProductCell
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds)
    (checked : localProductCell? A B C D E H interval = true) :
    CauchyIndex.Product.Basic.AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  unfold localProductCell? at checked
  cases found : localEventData? A B C D E H interval with
  | none =>
    have impossible : (false : Bool) = true :=
      (congrArg Option.isSome found).symm.trans checked
    cases impossible
  | some data => exact data.auxiliaryProductFormula

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Prepare
