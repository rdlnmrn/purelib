module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Tangent
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Differential pullbacks across the original cubic waist branch points

The original cubic tangent factors through its normalized ordinate. Cancelling
that exact factor constructs the pullback using only the retained apart
cofactor root, including at zero cubic ordinates. Off the branch points, an
operational comparison identifies this channel with the original differential
evaluator multiplied by the same chart tangent.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter} {time : Fraction.Rational}
variable {regular : parameter ≠ criticalValue site}
variable {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {unit : Owner ((unitPolynomial site).eval (point site parameter (direction quarter time) regular bound).base)}

/-- Pull back an original first-odd-power differential using the identical cached cofactor certificate.

The zero pair count restricts the original differential to `scale * numerator(x) dx/y`.
The numerator and logarithmic chart velocity are exact; only the supplied lift's
apart cofactor root is divided out. No cubic-ordinate apartness is required.
-/
@[expose] def value (differential : OddPowerDifferential radicand) (_simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter time) regular bound) unit) : CoherentNamed :=
  (Coherence.exact (differential.scale * differential.numerator.eval
    (point site parameter (direction quarter time) regular bound).base *
      Stereographic.Tangent.logarithmicVelocity time)).div lift.unitRoot.value lift.unitRoot.apart

/-- Two original waist lifts with agreeing retained cofactor channels give agreeing differential pullbacks.

Both actual lifts, their distinct original owners and their apartness payments
are retained by the general operational quotient comparison.
-/
def value_respects (differential : OddPowerDifferential radicand) (simple : differential.denominatorPairs = 0)
    {firstUnit secondUnit :
      Owner ((unitPolynomial site).eval (point site parameter (direction quarter time) regular bound).base)}
    (first : Conic.Lift (point site parameter (direction quarter time) regular bound) firstUnit)
    (second : Conic.Lift (point site parameter (direction quarter time) regular bound) secondUnit)
    (cofactor : NamedEquivalent first.unitRoot.value.name second.unitRoot.value.name) :
    NamedEquivalent (value differential simple first).name (value differential simple second).name :=
  Name.Coherent.Division.Equivalence.coherentDiv_respects _ _ _ _
    first.unitRoot.apart second.unitRoot.apart (NamedEquivalent.refl _) cofactor

/-- The original cubic ordinate clears the actual pullback to the original numerator times its exact tangent.

This operational comparison uses the supplied lift and its cached cofactor
certificate unchanged. It holds at both branch points as well as elsewhere.
-/
def value_cleared (differential : OddPowerDifferential radicand) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter time) regular bound) unit) :
    NamedEquivalent (lift.value.mul (value differential simple lift)).name
      (Named.exact (differential.scale * differential.numerator.eval
        (point site parameter (direction quarter time) regular bound).base *
          Tangent.baseVelocity site parameter quarter time)) := by
  let waistPoint := point site parameter (direction quarter time) regular bound
  let numerator := differential.scale * differential.numerator.eval waistPoint.base
  let velocity := Stereographic.Tangent.logarithmicVelocity time
  let exactNumerator := Coherence.exact (numerator * velocity)
  let exactOrdinate := Coherence.exact waistPoint.ordinate
  let coefficient := value differential simple lift
  have cancelled : NamedEquivalent (coefficient.mul lift.unitRoot.value).name exactNumerator.name :=
    Division.Cancellation.coherentDiv_mul_cancel exactNumerator lift.unitRoot.value lift.unitRoot.apart
  have rearranged : NamedEquivalent
      ((lift.unitRoot.value.mul exactOrdinate).mul coefficient).name
      (Named.exact ((numerator * velocity) * waistPoint.ordinate)) :=
    (Product.Laws.coherentMul_comm (lift.unitRoot.value.mul exactOrdinate) coefficient).trans
      ((Product.Laws.coherentMul_assoc coefficient lift.unitRoot.value exactOrdinate).symm.trans
        ((Product.Congruence.coherentMul_respects (coefficient.mul lift.unitRoot.value) exactNumerator
          exactOrdinate exactOrdinate cancelled (NamedEquivalent.refl _)).trans
            (Exact.Arithmetic.exact_mul (numerator * velocity) waistPoint.ordinate)))
  have scalar : (numerator * velocity) * waistPoint.ordinate =
      numerator * Tangent.baseVelocity site parameter quarter time := by
    rewrite [Tangent.baseVelocity_eq_ordinate_mul site parameter quarter regular bound time]
    ring1
  rewrite [lift.value_eq]
  exact NamedEquivalent.transport rfl (congrArg Named.exact scalar) rearranged

/-- Wherever the original cubic ordinate is apart, its ordinary evaluator gives the same actual pullback.

The comparison retains the original differential and actual lifted sheet.
Operational product and division laws compare the two finite process trees;
no equality of their finite samples or newly selected square root is assumed.
-/
def value_agrees (differential : OddPowerDifferential radicand) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter time) regular bound) unit)
    (apart : Named.Apart lift.value.name) :
    NamedEquivalent ((differential.value
      (point site parameter (direction quarter time) regular bound).base lift.value apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter quarter time))).name
      (value differential simple lift).name := by
  let waistPoint := point site parameter (direction quarter time) regular bound
  let numerator := Coherence.exact (differential.scale * differential.numerator.eval waistPoint.base)
  let reciprocal := (Coherence.exact 1).div lift.value apart
  let tangent := Coherence.exact (Tangent.baseVelocity site parameter quarter time)
  let ordinary := differential.value waistPoint.base lift.value apart
  have evaluator : NamedEquivalent ordinary.name (numerator.mul reciprocal).name := by
    unfold ordinary OddPowerDifferential.value OddPowerDifferential.denominatorExponent
    rewrite [simple]
    exact Product.Congruence.coherentMul_respects numerator numerator
      (Power.namedPower reciprocal 1) reciprocal (NamedEquivalent.refl _) (Power.namedPower_one reciprocal)
  have reciprocalCancelled : NamedEquivalent (lift.value.mul reciprocal).name (Named.exact 1) :=
    (Product.Laws.coherentMul_comm lift.value reciprocal).trans
      (Division.Cancellation.reciprocal_mul_cancel lift.value apart)
  have numeratorCancelled : NamedEquivalent (lift.value.mul (numerator.mul reciprocal)).name numerator.name :=
    (Product.Congruence.coherentMul_respects lift.value lift.value (numerator.mul reciprocal)
      (reciprocal.mul numerator) (NamedEquivalent.refl _) (Product.Laws.coherentMul_comm numerator reciprocal)).trans
      ((Product.Laws.coherentMul_assoc lift.value reciprocal numerator).symm.trans
        ((Product.Congruence.coherentMul_respects (lift.value.mul reciprocal) (Coherence.exact 1)
          numerator numerator reciprocalCancelled (NamedEquivalent.refl _)).trans (Mul.coherentMul_one_left numerator)))
  have cleared : NamedEquivalent (lift.value.mul ((numerator.mul reciprocal).mul tangent)).name
      (Named.exact (differential.scale * differential.numerator.eval waistPoint.base *
        Tangent.baseVelocity site parameter quarter time)) :=
    (Product.Laws.coherentMul_assoc lift.value (numerator.mul reciprocal) tangent).symm.trans
      ((Product.Congruence.coherentMul_respects (lift.value.mul (numerator.mul reciprocal)) numerator
        tangent tangent numeratorCancelled (NamedEquivalent.refl _)).trans
          (Exact.Arithmetic.exact_mul _ _))
  have originalCleared : NamedEquivalent (lift.value.mul (ordinary.mul tangent)).name
      (Named.exact (differential.scale * differential.numerator.eval waistPoint.base *
        Tangent.baseVelocity site parameter quarter time)) :=
    (Product.Congruence.coherentMul_respects lift.value lift.value (ordinary.mul tangent)
      ((numerator.mul reciprocal).mul tangent) (NamedEquivalent.refl _)
      (Product.Congruence.coherentMul_respects ordinary (numerator.mul reciprocal) tangent tangent
        evaluator (NamedEquivalent.refl _))).trans cleared
  exact Division.Cancellation.coherentMul_cancel_left lift.value (ordinary.mul tangent)
    (value differential simple lift) apart (originalCleared.trans (value_cleared differential simple lift).symm)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential
