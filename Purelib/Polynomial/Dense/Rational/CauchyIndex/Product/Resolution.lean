module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Prepare
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Center
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Prepare
public import Purelib.Polynomial.Dense.Rational.Pair.Turn.Bounds
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Radius
import Purelib.Data.Rat.Interval.Radius
public import Purelib.Polynomial.Clearance.Pair.Product
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Operations
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Sign.ComplexProduct.Center.Basic

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)

/-- One positive squared-radius threshold covers all three finite Cauchy
scanners and the two factor-turn checks used by the local product cell.

The same factor certificates construct the product clearance. Three swapped
signed-chain thresholds and two factor-turn thresholds are combined by their
original nested minima, preserving their input order and exact rational value. -/
@[expose] public def localProductResolutionRadiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Fraction.Rational :=
  let product := left.complexProduct right realIdentity imagIdentity
  min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq B A left.swap)
    (min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq D C right.swap)
      (min (SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq H E product.swap)
        (min (Pair.Turn.Bounds.narrowTurnResolutionRadiusSq left)
          (Pair.Turn.Bounds.narrowTurnResolutionRadiusSq right))))

/-- The common threshold for the three event scans and two factor-turn checks is strictly positive.

The original three scanner thresholds and two turn thresholds are strictly
positive for the supplied clearance certificates. Nested rational minimum
positivity therefore proves the common threshold positive. -/
public theorem localProductResolutionRadiusSq_pos
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < localProductResolutionRadiusSq left right
      realIdentity imagIdentity := by
  let product := left.complexProduct right realIdentity imagIdentity
  unfold localProductResolutionRadiusSq
  apply Fraction.Order.Basic.lt_min
  · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos B A left.swap
  · apply Fraction.Order.Basic.lt_min
    · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos D C right.swap
    · apply Fraction.Order.Basic.lt_min
      · exact SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq_pos H E product.swap
      · apply Fraction.Order.Basic.lt_min
        · exact Pair.Turn.Bounds.narrowTurnResolutionRadiusSq_pos left
        · exact Pair.Turn.Bounds.narrowTurnResolutionRadiusSq_pos right

/-- Every clear refinement below the combined squared radius makes the
complete executable local product-cell classifier return `true`.

The same three event searches and finite center search are retained. The
refinement bound supplies their scanner and turn conditions, while the twelve
coordinate nonzero conditions and four product identities validate the data. -/
public theorem localProductCell?_eq_true_of_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      localProductResolutionRadiusSq left right realIdentity imagIdentity)
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
    (HᵣNonzero : H.eval interval.upper ≠ 0) :
    CauchyIndex.Product.Prepare.localProductCell?
      A B C D E H interval = true := by
  let product := left.complexProduct right realIdentity imagIdentity
  have leftRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq B A left.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact Fraction.Order.Basic.min_le_left _ _)
  have rightRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq D C right.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have productRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      SignedRemainder.Signs.Radius.signedChainResolutionRadiusSq H E product.swap :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))
  have leftTurnRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      Pair.Turn.Bounds.narrowTurnResolutionRadiusSq left :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))
  have rightTurnRadius : Interval.Radius.sampleRadiusSq interval interval.lower <
      Pair.Turn.Bounds.narrowTurnResolutionRadiusSq right :=
    radius.trans_le (by
      unfold localProductResolutionRadiusSq
      exact (Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))))
  have leftFound := CauchyIndex.Events.Resolution.cauchyEventSigns?_isSome_of_refined_radiusSq
    left.swap refines leftRadius
  have rightFound := CauchyIndex.Events.Resolution.cauchyEventSigns?_isSome_of_refined_radiusSq
    right.swap refines rightRadius
  have productFound := CauchyIndex.Events.Resolution.cauchyEventSigns?_isSome_of_refined_radiusSq
    product.swap refines productRadius
  have leftNarrow := Pair.Turn.Bounds.narrowComplexTurn_of_refined_radiusSq
    left refines leftTurnRadius
  have rightNarrow := Pair.Turn.Bounds.narrowComplexTurn_of_refined_radiusSq
    right refines rightTurnRadius
  have centerFound :=
    ProductCenterSigns.search?_isSome_of_narrowTurns
      AₗNonzero BₗNonzero CₗNonzero DₗNonzero EₗNonzero HₗNonzero
      AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero EᵣNonzero HᵣNonzero
      (realIdentity interval.lower) (imagIdentity interval.lower)
      (realIdentity interval.upper) (imagIdentity interval.upper)
      leftNarrow rightNarrow
  have eventDataFound :=
    CauchyIndex.Product.Prepare.localEventData?_isSome
      leftFound rightFound productFound centerFound
      BₗNonzero DₗNonzero HₗNonzero BᵣNonzero DᵣNonzero HᵣNonzero
      (realIdentity interval.lower) (imagIdentity interval.lower)
      (realIdentity interval.upper) (imagIdentity interval.upper)
  exact eventDataFound

/-- The coefficient-finite shrinking-radius construction proves the complete
local doubled Cauchy-product formula on every clear refined cell.

The radius condition and endpoint coordinate evidence establish success of
the retained complete local classifier. Its selected event data certify the
doubled Cauchy-product formula for the same six polynomials and interval. -/
public theorem auxiliaryProductFormula_of_refined_radiusSq
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial} {root interval : Data.Rat.Interval.Bounds}
    (left : Clearance.Pair.Basic.Certificate A B root)
    (right : Clearance.Pair.Basic.Certificate C D root)
    (realIdentity : ∀ x : Fraction.Rational,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Fraction.Rational,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (radius : Interval.Radius.sampleRadiusSq interval interval.lower <
      localProductResolutionRadiusSq left right realIdentity imagIdentity)
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
    (HᵣNonzero : H.eval interval.upper ≠ 0) :
    CauchyIndex.Product.Basic.AuxiliaryProductFormula
      A B C D E H interval.lower interval.upper := by
  apply CauchyIndex.Product.Prepare.auxiliaryProductFormula_of_localProductCell
    A B C D E H interval
  exact localProductCell?_eq_true_of_refined_radiusSq left right
    realIdentity imagIdentity refines radius
    AₗNonzero BₗNonzero CₗNonzero DₗNonzero EₗNonzero HₗNonzero
    AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero EᵣNonzero HᵣNonzero

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Resolution
