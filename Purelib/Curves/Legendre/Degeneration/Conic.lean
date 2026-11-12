module

public import Purelib.Curves.Legendre.Degeneration.Coordinates
import Purelib.Polynomial.Quadratic.Split
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Negation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Data.Gaussian.Norm.Parallelogram
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original cubic channels constructed from Gaussian conic points

An exact point on the computed conic determines the original displayed cubic
coordinate and one coherent ordinate. Its original signed cofactor owner is
acquired internally and cached once. The forward coordinate programs reuse
that same certificate and recover both original conic coordinates operationally.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Algebra.Field

open Purelib.Data.Rat.Fraction

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Polynomial.Quadratic
open Purelib.Data.Rat
open Purelib.Geometry.Rational

/-- The computed half-width-one-eighth square for each original conic coordinate. -/
@[expose] def coordinateBox : Box :=
  Box.Square.Centered.Affine.centeredSquare 0 (1 / 8) (by decide +kernel)

/-- Bounds on the original four summands bound their half-sum with the same center. -/
private theorem halfSum_bounds (center parameter first last value : Fraction.Rational)
    (equation : value * 2 = (center + parameter) + (first + last))
    (parameterBounds : center - 1 / 4 ≤ parameter ∧ parameter ≤ center + 1 / 4)
    (firstBounds : -(1 / 8) ≤ first ∧ first ≤ 1 / 8)
    (lastBounds : -(1 / 8) ≤ last ∧ last ≤ 1 / 8) :
    center - 1 / 4 ≤ value ∧ value ≤ center + 1 / 4 := by
  have lower := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl center) parameterBounds.1)
    (Order.Arithmetic.add_le_add_direct firstBounds.1 lastBounds.1)
  have upper := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl center) parameterBounds.2)
    (Order.Arithmetic.add_le_add_direct firstBounds.2 lastBounds.2)
  have lowerIdentity : (center + (center - 1 / 4)) + (-(1 / 8) + -(1 / 8)) =
      (center - 1 / 4) * 2 := by
    rewrite [show (-(1 / 8) + -(1 / 8) : Fraction.Rational) = -(1 / 4) by decide +kernel]
    ring1
  have upperIdentity : (center + (center + 1 / 4)) + (1 / 8 + 1 / 8) =
      (center + 1 / 4) * 2 := by
    rewrite [show (1 / 8 + 1 / 8 : Fraction.Rational) = 1 / 4 by decide +kernel]
    ring1
  rewrite [lowerIdentity, ← equation] at lower
  rewrite [upperIdentity, ← equation] at upper
  exact ⟨Order.Arithmetic.le_of_mul_le_mul_right_direct lower (by decide +kernel),
    Order.Arithmetic.le_of_mul_le_mul_right_direct upper (by decide +kernel)⟩

set_option genInjectivity false in
/-- An exact Gaussian point on the original computed nodal conic.

The ordered coordinates retain their defining product at the same original
Legendre parameter and collision site. They need not be apart or distinct;
the singular conic and the two zero-ordinate branch points are included.
-/
structure Point (site : Fin 2) (parameter : Canonical) where
  /-- The original first conic coordinate. -/ plus : Canonical
  /-- The original second conic coordinate. -/ minus : Canonical
  /-- Their exact product is the original smoothing parameter. -/ equation : plus * minus = smoothing site parameter

constructive_injectivity Point

namespace Point

open Purelib.Data.Gaussian

variable {site : Fin 2} {parameter : Canonical}

/-- Equality of the two original conic coordinate readings identifies their complete point owners. -/
theorem coordinates_eq {site : Fin 2} {parameter : Canonical} {first last : Point site parameter}
    (plus : first.plus = last.plus) (minus : first.minus = last.minus) : first = last := by
  cases first with
  | mk firstPlus firstMinus firstEquation =>
    cases last with
    | mk lastPlus lastMinus lastEquation =>
      change firstPlus = lastPlus at plus
      change firstMinus = lastMinus at minus
      cases plus
      cases minus
      rfl

/-- Construct the exact conic point from its nonzero first coordinate and the original smoothing value. -/
def ofPlus (site : Fin 2) (parameter plus : Canonical) (nonzero : plus ≠ 0) : Point site parameter :=
  { plus := plus
    minus := smoothing site parameter / plus
    equation := (Data.Gaussian.Basic.mul_comm _ _).trans
      (ExplicitField.div_mul_cancel _ nonzero) }

/-- The parametrized conic retains the original first coordinate. -/
theorem ofPlus_plus (site : Fin 2) (parameter plus : Canonical) (nonzero : plus ≠ 0) :
    (ofPlus site parameter plus nonzero).plus = plus := by
  unfold ofPlus
  rfl

/-- The parametrized conic uses the exact quotient of the original smoothing by that same first coordinate. -/
theorem ofPlus_minus (site : Fin 2) (parameter plus : Canonical) (nonzero : plus ≠ 0) :
    (ofPlus site parameter plus nonzero).minus = smoothing site parameter / plus := by
  unfold ofPlus
  rfl

/-- Every conic point on a regular labelled fibre has a nonzero first coordinate. -/
theorem plus_ne_zero (point : Point site parameter) (regular : parameter ≠ criticalValue site) : point.plus ≠ 0 := by
  intro zero
  have equation := point.equation.symm
  rewrite [zero, Data.Gaussian.Basic.zero_mul] at equation
  exact smoothing_ne_zero site regular equation

/-- Every conic point on a regular labelled fibre has a nonzero second coordinate. -/
theorem minus_ne_zero (point : Point site parameter) (regular : parameter ≠ criticalValue site) : point.minus ≠ 0 := by
  intro zero
  have equation := point.equation.symm
  rewrite [zero, Data.Gaussian.Basic.mul_zero] at equation
  exact smoothing_ne_zero site regular equation

/-- The original conic product determines its second coordinate from its supplied nonzero first coordinate. -/
theorem minus_eq_div (point : Point site parameter) (nonzero : point.plus ≠ 0) :
    point.minus = smoothing site parameter / point.plus := by
  apply ExplicitField.eq_of_mul_eq_mul_right nonzero
  exact ((Data.Gaussian.Basic.mul_comm _ _).trans point.equation).trans
    (ExplicitField.div_mul_cancel _ nonzero).symm

/-- Reconstructing an original conic point from its first coordinate preserves that full exact point. -/
theorem ofPlus_original (point : Point site parameter) (nonzero : point.plus ≠ 0) :
    ofPlus site parameter point.plus nonzero = point := by
  have second := point.minus_eq_div nonzero
  cases point with
  | mk plus minus equation =>
    change minus = smoothing site parameter / plus at second
    cases second
    unfold ofPlus
    rfl

/-- Exchange the original conic coordinates, retaining the same labelled fibre and product. -/
@[expose] def exchange (point : Point site parameter) : Point site parameter :=
  { plus := point.minus
    minus := point.plus
    equation := (Data.Gaussian.Basic.mul_comm _ _).trans point.equation }

/-- Two exchanges return the complete original exact conic point. -/
theorem exchange_exchange (point : Point site parameter) : point.exchange.exchange = point := by
  cases point
  rfl

/-- The centered base coordinate computed from the same ordered conic inputs. -/
@[expose] def abscissa (point : Point site parameter) : Canonical := Split.center point.minus point.plus

/-- A common quadrance bound on both original conic coordinates bounds their recovered centered base.

The exact half-sum identity retains both inputs. Dropping its nonnegative
half-difference term gives the same bound without choosing a square root
or comparing any sheet Owners.
-/
theorem abscissa_normSq_le (point : Point site parameter) (bound : Fraction.Rational)
    (plusBound : Norm.Basic.normSq point.plus ≤ bound)
    (minusBound : Norm.Basic.normSq point.minus ≤ bound) :
    Norm.Basic.normSq point.abscissa ≤ bound := by
  have midpoint : point.abscissa = (1 / 2 : Canonical) * (point.minus + point.plus) := by
    calc
      _ = (point.minus + point.plus) * (2 : Canonical)⁻¹ :=
        Algebra.Field.ExplicitField.div_eq_mul_inv _ _
      _ = ((1 : Canonical) * (2 : Canonical)⁻¹) * (point.minus + point.plus) := by ring1
      _ = _ := congrArg (fun value : Canonical => value * (point.minus + point.plus))
        (Algebra.Field.ExplicitField.div_eq_mul_inv (1 : Canonical) 2).symm
  have nonnegative := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl
      (Norm.Basic.normSq ((1 / 2 : Canonical) * (point.minus + point.plus))))
    (Norm.Basic.normSq_nonneg ((1 / 2 : Canonical) * (point.minus - point.plus)))
  have first := (show Norm.Basic.normSq ((1 / 2 : Canonical) * (point.minus + point.plus)) =
      Norm.Basic.normSq ((1 / 2 : Canonical) * (point.minus + point.plus)) + 0 by ring1).trans_le
    (nonnegative.trans_eq (Norm.Parallelogram.half_sum_difference point.minus point.plus))
  have last := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct minusBound plusBound)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 2)
  have final : (1 / 2 : Fraction.Rational) * (bound + bound) = bound := by
    calc
      _ = ((1 / 2 : Fraction.Rational) * 2) * bound := by ring1
      _ = 1 * bound := congrArg (fun value : Fraction.Rational => value * bound)
        (by decide +kernel : (1 / 2 : Fraction.Rational) * 2 = 1)
      _ = bound := Fraction.Field.one_mul _
  exact (congrArg Norm.Basic.normSq midpoint).trans_le
    (first.trans (last.trans_eq final))

/-- The normalized ordinate computed from the same ordered conic inputs. -/
@[expose] def ordinate (point : Point site parameter) : Canonical := Split.halfGap point.minus point.plus

/-- The original cubic base coordinate recovered using the same collision midpoint. -/
@[expose] def base (point : Point site parameter) : Canonical := center site parameter + point.abscissa

/-- Exchanging the conic coordinates preserves the original cubic base coordinate exactly. -/
theorem exchange_base (point : Point site parameter) : point.exchange.base = point.base := by
  unfold base abscissa Split.center exchange
  rewrite [Data.Gaussian.Basic.add_comm point.plus point.minus]
  rfl

/-- Exchanging the conic coordinates reverses the exact normalized cubic ordinate. -/
theorem exchange_ordinate (point : Point site parameter) : point.exchange.ordinate = -point.ordinate := by
  apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (2 : Canonical) ≠ 0)
  have original : point.ordinate * 2 = point.plus - point.minus :=
    Split.halfGap_mul_two _ _ (by decide +kernel)
  calc
    point.exchange.ordinate * 2 = point.minus - point.plus :=
      Split.halfGap_mul_two _ _ (by decide +kernel)
    _ = -(point.plus - point.minus) := by ring1
    _ = -point.ordinate * 2 := by
      rewrite [← original]
      ring1

/-- Twice the recovered base is the sum of the original root and conic coordinate pairs. -/
theorem base_mul_two (point : Point site parameter) :
    point.base * 2 = (criticalValue site + parameter) + (point.minus + point.plus) := by
  unfold base center abscissa Split.center
  calc
    _ = (criticalValue site + parameter) / 2 * 2 + (point.minus + point.plus) / 2 * 2 := by ring1
    _ = _ := by
      rewrite [ExplicitField.div_mul_cancel _ (by decide +kernel : (2 : Canonical) ≠ 0),
        ExplicitField.div_mul_cancel _ (by decide +kernel : (2 : Canonical) ≠ 0)]
      rfl

/-- Bounded original conic coordinates recover a base in the smaller original parameter square.

The bounds use both coordinates over the whole displayed square. The computed
half-sum leaves a quarter-width margin before the remaining-factor boundary;
no root search or supplied cofactor-clearance certificate is needed.
-/
theorem base_parameter_inside (point : Point site parameter)
    (parameterInside : (parameterBox site).Contains parameter)
    (plusInside : coordinateBox.Contains point.plus) (minusInside : coordinateBox.Contains point.minus) :
    (parameterBox site).Contains point.base := by
  change (criticalValue site).re - 1 / 4 ≤ parameter.re ∧ parameter.re ≤ (criticalValue site).re + 1 / 4 ∧
    (criticalValue site).im - 1 / 4 ≤ parameter.im ∧ parameter.im ≤ (criticalValue site).im + 1 / 4 at parameterInside
  change (0 : Fraction.Rational) - 1 / 8 ≤ point.plus.re ∧ point.plus.re ≤ 0 + 1 / 8 ∧
    (0 : Fraction.Rational) - 1 / 8 ≤ point.plus.im ∧ point.plus.im ≤ 0 + 1 / 8 at plusInside
  change (0 : Fraction.Rational) - 1 / 8 ≤ point.minus.re ∧ point.minus.re ≤ 0 + 1 / 8 ∧
    (0 : Fraction.Rational) - 1 / 8 ≤ point.minus.im ∧ point.minus.im ≤ 0 + 1 / 8 at minusInside
  have zeroSub : (0 : Fraction.Rational) - 1 / 8 = -(1 / 8) := by ring1
  rewrite [zeroSub, Fraction.Field.zero_add] at plusInside minusInside
  have twoReal : (2 : Canonical).re = 2 := by decide +kernel
  have twoImaginary : (2 : Canonical).im = 0 := by decide +kernel
  have real := congrArg (fun value : Canonical => value.re) point.base_mul_two
  rewrite [Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_re,
    Data.Gaussian.Basic.add_re, twoReal, twoImaginary, Fraction.Field.mul_zero_direct] at real
  have realEquation : point.base.re * 2 =
      ((criticalValue site).re + parameter.re) + (point.minus.re + point.plus.re) := by
    calc
      point.base.re * 2 = point.base.re * 2 - 0 := by ring1
      _ = _ := real
  have imaginary := congrArg (fun value : Canonical => value.im) point.base_mul_two
  rewrite [Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.add_im,
    Data.Gaussian.Basic.add_im, twoReal, twoImaginary, Fraction.Field.mul_zero_direct,
    Fraction.Field.zero_add] at imaginary
  have realBounds := halfSum_bounds (criticalValue site).re parameter.re point.minus.re point.plus.re point.base.re
    realEquation ⟨parameterInside.1, parameterInside.2.1⟩ ⟨minusInside.1, minusInside.2.1⟩
    ⟨plusInside.1, plusInside.2.1⟩
  have imaginaryBounds := halfSum_bounds (criticalValue site).im parameter.im point.minus.im point.plus.im point.base.im
    imaginary ⟨parameterInside.2.2.1, parameterInside.2.2.2⟩ ⟨minusInside.2.2.1, minusInside.2.2.2⟩
    ⟨plusInside.2.2.1, plusInside.2.2.2⟩
  exact ⟨realBounds.1, realBounds.2, imaginaryBounds.1, imaginaryBounds.2⟩

/-- Bounded conic inputs internally admit their original cubic base to the signed cofactor patch. -/
theorem base_inside (point : Point site parameter) (parameterInside : (parameterBox site).Contains parameter)
    (plusInside : coordinateBox.Contains point.plus) (minusInside : coordinateBox.Contains point.minus) :
    (spatialBox site).Contains point.base := by
  have strict := moving_strictContains site (point.base_parameter_inside parameterInside plusInside minusInside)
  exact ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le, strict.2.2.2.le⟩

/-- The recovered cubic point has the same original centered base coordinate. -/
theorem coordinate_base (point : Point site parameter) : coordinate site parameter point.base = point.abscissa := by
  unfold coordinate base
  ring1

/-- The computed centered base and ordinate recover the original first conic input exactly. -/
theorem plus_eq (point : Point site parameter) : point.abscissa + point.ordinate = point.plus :=
  Split.center_add_halfGap _ _ (by decide +kernel)

/-- The computed centered base and ordinate recover the original second conic input exactly. -/
theorem minus_eq (point : Point site parameter) : point.abscissa - point.ordinate = point.minus :=
  Split.center_sub_halfGap _ _ (by decide +kernel)

/-- The recovered normalized ordinate satisfies the original quadratic nodal equation. -/
theorem quadratic (point : Point site parameter) :
    point.ordinate ^ 2 = point.abscissa ^ 2 - smoothing site parameter := by
  have product : (point.abscissa + point.ordinate) * (point.abscissa - point.ordinate) =
      smoothing site parameter := by
    rewrite [point.plus_eq, point.minus_eq]
    exact point.equation
  calc
    point.ordinate ^ 2 = point.abscissa ^ 2 -
        (point.abscissa + point.ordinate) * (point.abscissa - point.ordinate) := by ring1
    _ = point.abscissa ^ 2 - smoothing site parameter :=
      congrArg (fun value => point.abscissa ^ 2 - value) product

/-- The original cubic value is the same signed cofactor times the exact conic ordinate squared. -/
theorem cubic (point : Point site parameter) :
    (unitPolynomial site).eval point.base * point.ordinate ^ 2 = (Paths.polynomial parameter).eval point.base := by
  rewrite [polynomial_centered, point.coordinate_base, ← point.quadratic]
  exact Data.Gaussian.Basic.mul_comm _ _

/-- A displayed cofactor reading has exactly the scaled original cubic square residual. -/
theorem product_residual (point : Point site parameter) (root : Canonical) :
    Norm.Basic.normSq ((root * point.ordinate) * (root * point.ordinate) -
        (Paths.polynomial parameter).eval point.base) =
      Norm.Basic.normSq (root * root - (unitPolynomial site).eval point.base) *
        Norm.Basic.normSq point.ordinate ^ 2 := by
  have identity : (root * point.ordinate) * (root * point.ordinate) -
      (Paths.polynomial parameter).eval point.base =
      (root * root - (unitPolynomial site).eval point.base) * (point.ordinate * point.ordinate) := by
    rewrite [← point.cubic, pow_two]
    ring1
  rewrite [identity, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, pow_two]
  rfl

end Point

namespace Lift

/-- The signed cofactor parameter at the same original conic point. -/
@[expose] def cofactor {site : Fin 2} {parameter : Canonical} (point : Point site parameter) : Canonical :=
  (unitPolynomial site).eval point.base

/-- The original signed cofactor owner at the retained conic point. -/
@[expose] def CofactorOwner {site : Fin 2} {parameter : Canonical} (point : Point site parameter) : Type :=
  Owner (cofactor point)

/-- The original complete root certificate at the retained cofactor parameter. -/
@[expose] def CofactorRoot {site : Fin 2} {parameter : Canonical} (point : Point site parameter) : Type 1 :=
  CertifiedSquareRoot.Certificate (cofactor point)

/-- The full cached root is the certificate of the same original cofactor owner. -/
@[expose] def RootEquation {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (unit : CofactorOwner point) (root : CofactorRoot point) : Prop :=
  root = unit.certificate unit.parameterNonzero

/-- The retained ordinate is the product of the same cofactor root and exact conic ordinate. -/
@[expose] def ValueEquation {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (root : CofactorRoot point) (value : CoherentNamed) : Prop :=
  value = root.value.mul (Coherence.exact point.ordinate)

/-- The original cubic equation for the retained ordinate at the same conic point. -/
@[expose] def SquareComparison {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (value : CoherentNamed) : Type :=
  NamedEquivalent (value.mul value).name (Named.exact ((Paths.polynomial parameter).eval point.base))

/-- The forward coordinate programs retain the same original cubic ordinate and cofactor owner. -/
@[expose] def Coordinates {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (value : CoherentNamed) (unit : CofactorOwner point) : Type 1 :=
  CoordinateChannels site parameter point.base value unit

/-- The forward coordinate construction consumes the same complete cached root certificate. -/
@[expose] def CoordinateRootEquation {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (value : CoherentNamed) (unit : CofactorOwner point) (coordinates : Coordinates point value unit)
    (root : CofactorRoot point) : Prop := coordinates.unitRoot = root

/-- The first forward coordinate recovers the same original conic input. -/
@[expose] def PlusComparison {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (value : CoherentNamed) (unit : CofactorOwner point) (coordinates : Coordinates point value unit) : Type :=
  NamedEquivalent coordinates.plus.name (Named.exact point.plus)

/-- The second forward coordinate recovers the same original conic input. -/
@[expose] def MinusComparison {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (value : CoherentNamed) (unit : CofactorOwner point) (coordinates : Coordinates point value unit) : Type :=
  NamedEquivalent coordinates.minus.name (Named.exact point.minus)

end Lift

section

attribute [local irreducible] Lift.cofactor Lift.CofactorOwner Lift.CofactorRoot Lift.Coordinates
  Lift.RootEquation Lift.ValueEquation Lift.SquareComparison
  Lift.CoordinateRootEquation Lift.PlusComparison Lift.MinusComparison

set_option genInjectivity false in
/-- Actual original cubic channels and forward coordinates retaining one exact Gaussian conic point.

The original conic inputs remain indices. The signed cofactor owner, its full
certificate and actual cubic ordinate are cached once; both the curve-square
comparison and the forward conic comparisons consume those same data.
-/
structure Lift {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (unit : Lift.CofactorOwner point) where
  /-- The actual original signed cofactor owner at the recovered cubic coordinate. -/
  unitOwner : Lift.CofactorOwner point
  /-- The cache is the complete original supplied owner at that same coordinate. -/
  unitOwner_eq : unitOwner = unit
  /-- The full original cofactor certificate cached on that owner. -/
  unitRoot : Lift.CofactorRoot point
  /-- The cache belongs to the exact retained owner. -/
  unitRoot_eq : Lift.RootEquation point unitOwner unitRoot
  /-- The actual original cubic ordinate program. -/
  value : CoherentNamed
  /-- The program multiplies the same cofactor channel by the recovered exact conic ordinate. -/
  value_eq : Lift.ValueEquation point unitRoot value
  /-- The original cubic equation holds for the retained actual ordinate. -/
  square : Lift.SquareComparison point value
  /-- The actual forward coordinate programs of this same original cubic point. -/
  coordinates : Lift.Coordinates point value unitOwner
  /-- The forward construction consumes the identical retained cofactor certificate. -/
  coordinates_unitRoot : Lift.CoordinateRootEquation point value unitOwner coordinates unitRoot
  /-- The first forward program recovers the original first conic input operationally. -/
  plus_agrees : Lift.PlusComparison point value unitOwner coordinates
  /-- The second forward program recovers the original second conic input operationally. -/
  minus_agrees : Lift.MinusComparison point value unitOwner coordinates

constructive_injectivity Lift

end

namespace Lift

/-- Construct actual cubic channels from an original conic point and exact cached cofactor certificate.

The full supplied owner may be an actual transported occurrence. Its cached
certificate is passed unchanged to the forward constructor; exact conic
algebra and the original cubic factorization derive the curve equation and
both forward comparisons without another root isolation or supplied sample bounds.
-/
def ofRoot {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (unit : Owner ((unitPolynomial site).eval point.base))
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point.base))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero) : Lift point unit := by
  let unitOwner := unit
  let exactOrdinate := Coherence.exact point.ordinate
  let value := unitRoot.value.mul exactOrdinate
  have ordinateSquare : NamedEquivalent (exactOrdinate.mul exactOrdinate).name
      (Named.exact (point.ordinate ^ 2)) := by
    rewrite [pow_two]
    exact Name.Coherent.Exact.Arithmetic.exact_mul _ _
  have originalProduct := point.cubic
  have square : NamedEquivalent (value.mul value).name
      (Named.exact ((Paths.polynomial parameter).eval point.base)) :=
    (Product.Laws.coherentMul_squares_interchange unitRoot.value exactOrdinate).symm.trans
      ((Product.Congruence.coherentMul_respects (unitRoot.value.mul unitRoot.value)
        (Coherence.exact ((unitPolynomial site).eval point.base)) (exactOrdinate.mul exactOrdinate)
        (Coherence.exact (point.ordinate ^ 2)) unitRoot.square ordinateSquare).trans
        (NamedEquivalent.transport rfl (congrArg Named.exact originalProduct)
          (Name.Coherent.Exact.Arithmetic.exact_mul _ _)))
  let coordinates := CoordinateChannels.ofRoot site parameter point.base value square unitOwner unitRoot unitRoot_eq
  have rootEq : coordinates.unitRoot = unitRoot := CoordinateChannels.ofRoot_unitRoot _ _ _ _ _ _ _ _
  have normalized : NamedEquivalent coordinates.ordinate.name exactOrdinate.name := by
    have recovered := coordinates.recovers
    rewrite [rootEq] at recovered
    have returnValue := (Product.Laws.coherentMul_comm
      unitRoot.value coordinates.ordinate).trans recovered
    exact Division.Cancellation.coherentMul_cancel_left unitRoot.value coordinates.ordinate exactOrdinate
      unitRoot.apart returnValue
  have first : NamedEquivalent coordinates.plus.name (Named.exact point.plus) := by
    rewrite [coordinates.plus_eq, point.coordinate_base]
    exact (Sum.Congruence.coherentAdd_respects (Coherence.exact point.abscissa)
      (Coherence.exact point.abscissa) coordinates.ordinate exactOrdinate (NamedEquivalent.refl _) normalized).trans
      (NamedEquivalent.transport rfl (congrArg Named.exact point.plus_eq)
        (Name.Coherent.Exact.Arithmetic.exact_add _ _))
  have second : NamedEquivalent coordinates.minus.name (Named.exact point.minus) := by
    rewrite [coordinates.minus_eq, point.coordinate_base]
    have negative := Coherent.Additive.coherentNeg_respects coordinates.ordinate exactOrdinate normalized
    have replace := Sum.Congruence.coherentAdd_respects (Coherence.exact point.abscissa)
      (Coherence.exact point.abscissa) coordinates.ordinate.neg exactOrdinate.neg (NamedEquivalent.refl _) negative
    have exactNegative := Arithmetic.Neg.exactNeg point.ordinate
    have exactSum := Sum.Congruence.coherentAdd_respects (Coherence.exact point.abscissa)
      (Coherence.exact point.abscissa) exactOrdinate.neg (Coherence.exact (-point.ordinate))
      (NamedEquivalent.refl _) exactNegative
    have scalar : point.abscissa + -point.ordinate = point.minus := by
      calc
        _ = point.abscissa - point.ordinate := by ring1
        _ = point.minus := point.minus_eq
    exact replace.trans (exactSum.trans (NamedEquivalent.transport rfl (congrArg Named.exact scalar)
      (Name.Coherent.Exact.Arithmetic.exact_add _ _)))
  exact
    { unitOwner := unitOwner
      unitOwner_eq := rfl
      unitRoot := unitRoot
      unitRoot_eq := unitRoot_eq
      value := value
      value_eq := rfl
      square := square
      coordinates := coordinates
      coordinates_unitRoot := rootEq
      plus_agrees := first
      minus_agrees := second }

/-- The general cubic lift retains the exact full supplied cofactor certificate. -/
theorem ofRoot_unitRoot {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (unit : Owner ((unitPolynomial site).eval point.base))
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point.base))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero) :
    (ofRoot point unit unitRoot unitRoot_eq).unitRoot = unitRoot := by
  unfold ofRoot
  rfl

/-- Construct actual cubic channels while acquiring the supplied full cofactor owner's certificate once. -/
def ofUnit {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (unit : Owner ((unitPolynomial site).eval point.base)) : Lift point unit :=
  ofRoot point unit (unit.certificate unit.parameterNonzero) rfl

/-- Construct an actual cubic lift by acquiring the original signed cofactor owner internally on its spatial patch. -/
def build {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (inside : (spatialBox site).Contains point.base) : Lift point (UnitRoot.owner site point.base inside) :=
  ofUnit point (UnitRoot.owner site point.base inside)

/-- Read the retained cofactor certificate on its complete original owner index. -/
theorem unitRoot_name {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)} (lift : Lift point unit) :
    lift.unitRoot.value.name = ownerRootName unit.parameterNonzero unit := by
  rewrite [lift.unitRoot_eq, lift.unitOwner_eq]
  rfl

/-- Read the actual paired product state beneath the original complete cubic channel. -/
@[expose] def productState {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)} (lift : Lift point unit)
    (state : lift.value.name.process.State) :
    (lift.unitRoot.value.mul (Coherence.exact point.ordinate)).name.process.State :=
  CoherentNamed.castState lift.value_eq state

/-- Every actual cubic candidate retains its original cofactor candidate and the same exact conic ordinate. -/
theorem candidate_factors {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)} (lift : Lift point unit)
    {state : lift.value.name.process.State} {candidate : Canonical}
    (possible : lift.value.name.process.Possible state candidate) :
    ∃ cofactor : Canonical,
      lift.unitRoot.value.name.process.Possible (lift.productState state).1 cofactor ∧
        candidate = cofactor * point.ordinate := by
  have original := CoherentNamed.possible_castState lift.value_eq state possible
  rcases original with ⟨cofactor, ordinate, cofactorPossible, ordinatePossible, equal⟩
  change ordinate = point.ordinate at ordinatePossible
  exact ⟨cofactor, cofactorPossible, equal.trans (congrArg (fun value => cofactor * value) ordinatePossible)⟩

/-- A possible original cofactor reading gives a possible reading of the same complete cubic product channel. -/
theorem product_possible {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)} (lift : Lift point unit)
    {state : lift.unitRoot.value.name.process.State} {candidate : Canonical}
    (possible : lift.unitRoot.value.name.process.Possible state candidate) :
    lift.value.name.process.Possible
      (CoherentNamed.castState lift.value_eq.symm ⟨state, (Coherence.exact point.ordinate).name.state⟩)
      (candidate * point.ordinate) :=
  CoherentNamed.possible_castState lift.value_eq.symm _
    ⟨candidate, point.ordinate, possible, rfl, rfl⟩

/-- The exact conic factor scales the actual retained cofactor-state radius in the same original cubic product.

Only the original complete value equation transports the supplied state.
The exact ordinate has zero radius, so the original multiplication ball
reduces to its actual single moving-factor term; no root is sampled again.
-/
theorem product_radius {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)} (lift : Lift point unit)
    (state : lift.unitRoot.value.name.process.State) :
    (lift.value.name.process.ball (CoherentNamed.castState lift.value_eq.symm
      ⟨state, (Coherence.exact point.ordinate).name.state⟩)).radiusSq =
        4 * (lift.unitRoot.value.name.process.ball state).radiusSq * Norm.Basic.normSq point.ordinate := by
  have transported := congrArg (fun ball : Enclosure.Ball => ball.radiusSq)
    (CoherentNamed.castState_ball lift.value_eq.symm ⟨state, (Coherence.exact point.ordinate).name.state⟩)
  exact transported.trans (by
    change 4 * ((lift.unitRoot.value.name.process.ball state).radiusSq * Norm.Basic.normSq point.ordinate +
      Norm.Basic.normSq (lift.unitRoot.value.name.process.ball state).center * 0) +
      2 * ((lift.unitRoot.value.name.process.ball state).radiusSq * 0) = _
    ring1)

/-- A comparison of the two retained cofactor channels compares the two original cubic lift channels. -/
def value_agrees {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {firstUnit secondUnit : Owner ((unitPolynomial site).eval point.base)}
    (first : Lift point firstUnit) (second : Lift point secondUnit)
    (unit : NamedEquivalent first.unitRoot.value.name second.unitRoot.value.name) :
    NamedEquivalent first.value.name second.value.name := by
  rewrite [first.value_eq, second.value_eq]
  exact Product.Congruence.coherentMul_respects _ _ _ _ unit (NamedEquivalent.refl _)

/-- Construct original cubic channels from bounded conic inputs with internally derived patch clearance. -/
def onPatch {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (parameterInside : (parameterBox site).Contains parameter)
    (plusInside : coordinateBox.Contains point.plus) (minusInside : coordinateBox.Contains point.minus) :
    Lift point (UnitRoot.owner site point.base (point.base_inside parameterInside plusInside minusInside)) :=
  build point (point.base_inside parameterInside plusInside minusInside)

/-- Coordinate exchange preserves the actual cached cofactor channel of two original signed cubic lifts. -/
theorem exchange_unitRoot_value {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {inside : (spatialBox site).Contains point.base} {exchangedInside : (spatialBox site).Contains point.exchange.base}
    (original : Lift point (UnitRoot.owner site point.base inside))
    (exchanged : Lift point.exchange (UnitRoot.owner site point.exchange.base exchangedInside)) :
    exchanged.unitRoot.value = original.unitRoot.value := by
  rewrite [exchanged.unitRoot_eq, original.unitRoot_eq, exchanged.unitOwner_eq, original.unitOwner_eq]
  let channel (value : Canonical) (admission : (spatialBox site).Contains value) :=
    let owner := UnitRoot.owner site value admission
    (owner.certificate owner.parameterNonzero).value
  have same (first last : Canonical) (equal : first = last)
      (firstInside : (spatialBox site).Contains first) (lastInside : (spatialBox site).Contains last) :
      channel first firstInside = channel last lastInside := by
    cases equal
    rfl
  exact same _ _ point.exchange_base exchangedInside inside

/-- The actual cubic channel of an exchanged conic lift agrees with the negated original cubic channel.

Both original lift owners and caches remain inputs. Their supplied cofactor
comparison and exact exchanged ordinate determine the shared operational
product-negation comparison, including zero ordinates.
-/
def exchange_value_agrees {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {unit : Owner ((unitPolynomial site).eval point.base)}
    {exchangedUnit : Owner ((unitPolynomial site).eval point.exchange.base)}
    (original : Lift point unit) (exchanged : Lift point.exchange exchangedUnit)
    (unitAgreement : NamedEquivalent exchanged.unitRoot.value.name original.unitRoot.value.name) :
    NamedEquivalent exchanged.value.name original.value.neg.name := by
  rewrite [exchanged.value_eq, original.value_eq, point.exchange_ordinate]
  have changeRoot := Product.Congruence.coherentMul_respects
    exchanged.unitRoot.value original.unitRoot.value (Coherence.exact (-point.ordinate))
    (Coherence.exact (-point.ordinate)) unitAgreement (NamedEquivalent.refl _)
  have changeFactor := Product.Congruence.coherentMul_respects
    original.unitRoot.value original.unitRoot.value (Coherence.exact (-point.ordinate))
    (Coherence.exact point.ordinate).neg (NamedEquivalent.refl _) (Arithmetic.Neg.exactNeg point.ordinate).symm
  exact changeRoot.trans (changeFactor.trans (Product.Negation.neg_right _ _))

/-- Original signed patch lifts derive their exchanged cubic-channel agreement internally from their same base. -/
def exchange_patch_agrees {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
    {inside : (spatialBox site).Contains point.base} {exchangedInside : (spatialBox site).Contains point.exchange.base}
    (original : Lift point (UnitRoot.owner site point.base inside))
    (exchanged : Lift point.exchange (UnitRoot.owner site point.exchange.base exchangedInside)) :
    NamedEquivalent exchanged.value.name original.value.neg.name :=
  exchange_value_agrees original exchanged
    (NamedEquivalent.transport
      (congrArg (fun value : CoherentNamed => value.name) (exchange_unitRoot_value original exchanged)).symm rfl
      (NamedEquivalent.refl _))

end Lift

end Purelib.Curves.Legendre.Degeneration.Conic
