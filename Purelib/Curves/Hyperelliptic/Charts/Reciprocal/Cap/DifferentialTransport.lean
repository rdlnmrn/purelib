module
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Semiring.Normalization
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.InverseSquareRoot
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Differential transport through the actual reciprocal cap coordinate

Odd degree uses the retained quotient coordinate t with t²=w and tangent
2t. Even degree retains the actual sheet sign whose square is one. These
operational identities compare the original collar channel with the regular
cap expression, including the reciprocal orientation sign. Rational readings
are not treated as exact roots or as exact points on the ramified boundary.
-/

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Approximation.Gaussian.Name.Coherent.Power (namedPower)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_comm coherentMul_assoc)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate Overlap)

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

/-- Cancel the retained coordinate against the original reciprocal root. The numerator may itself be an operational
polynomial expression.

The supplied regular-quotient view retains that whole original guarded
channel. The literal former quotient is the default; both cancellation
routes consume the supplied view without rebuilding it at this owner.
-/
def cancel_quotient {first second target : ReciprocalRootNames.Gaussian} {numerator : CertifiedSquareRoot.Certificate
  first} {denominator : CertifiedSquareRoot.Certificate second}
    (coordinate : RootCoordinates.RootCoordinate numerator denominator target) (value : Coherent.CoherentNamed)
    (regularCache : { quotient : CoherentNamed //
      quotient = div value denominator.value denominator.apart } :=
        ⟨div value denominator.value denominator.apart, rfl⟩) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul coordinate.prepared.denominator (CoherentNamed.div value
      numerator.value numerator.apart)).name
      regularCache.val.name := by
  let factor := coordinate.prepared.denominator
  let quotient := CoherentNamed.div value numerator.value numerator.apart
  let regular := regularCache.val
  have left : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul denominator.value (CoherentNamed.mul factor
    quotient)).name value.name :=
    (Laws.coherentMul_assoc denominator.value factor quotient).symm.trans
      ((Congruence.coherentMul_respects (CoherentNamed.mul denominator.value factor) numerator.value quotient quotient
        ((Laws.coherentMul_comm denominator.value factor).trans coordinate.reconstruct) (NamedEquivalent.refl _)).trans
        ((Laws.coherentMul_comm numerator.value quotient).trans
          (Cancellation.coherentDiv_mul_cancel value numerator.value numerator.apart)))
  have regularCancel : NamedEquivalent (regular.mul denominator.value).name value.name :=
    NamedEquivalent.transport
      (congrArg (fun quotient : CoherentNamed => (quotient.mul denominator.value).name) regularCache.property.symm)
      rfl (Cancellation.coherentDiv_mul_cancel value denominator.value denominator.apart)
  have right : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul denominator.value regular).name value.name :=
    (Laws.coherentMul_comm denominator.value regular).trans regularCancel
  exact Cancellation.coherentMul_cancel_left denominator.value (CoherentNamed.mul factor quotient) regular
    denominator.apart (left.trans right.symm)

/-- A coordinate whose actual square is one carries a reciprocal quotient to its regular-root quotient.

The original coordinate, numerator and denominator root certificates remain
fixed. Its actual square-one identity and original reconstruction comparison
cancel that same coordinate, without testing equality of opaque channels.
The same supplied whole regular-quotient view passes through both routes.
-/
def cancel_quotient_of_square_one {first second target : ReciprocalRootNames.Gaussian}
    {numerator : Certificate first} {denominator : Certificate second}
    (coordinate : RootCoordinates.RootCoordinate numerator denominator target) (value : CoherentNamed)
    (square : SquareIdentity coordinate.prepared.denominator 1)
    (regularCache : { quotient : CoherentNamed //
      quotient = div value denominator.value denominator.apart } :=
        ⟨div value denominator.value denominator.apart, rfl⟩) :
    NamedEquivalent (div value numerator.value numerator.apart).name
      (coordinate.prepared.denominator.mul regularCache.val).name := by
  let factor := coordinate.prepared.denominator
  let quotient := div value numerator.value numerator.apart
  let regular := regularCache.val
  exact (Mul.coherentMul_one_left quotient).symm.trans
    ((coherentMul_respects (Coherence.exact 1) (factor.mul factor) quotient quotient
      square.symm (NamedEquivalent.refl _)).trans
      ((Laws.coherentMul_assoc factor factor quotient).trans
        (coherentMul_respects factor factor (factor.mul quotient) regular
          (NamedEquivalent.refl _) (coordinate.cancel_quotient value regularCache))))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

section GeneralPullback

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)

/-- Pull an original zero-pair odd-power differential back through the same actual reciprocal root occurrence.

The supplied affine presentation is the original reciprocal certificate
scaled by `w^(-g-1)`, with its retained exact target equation and original
guards. The original evaluator and original inverse-coordinate Jacobian
agree with one guarded quotient at the supplied reciprocal channel. Its
actual numerator reading is shared, without choosing another root or sheet.
The optional whole evaluator view is consumed as the original congruence
operand; its default remains the literal original evaluator.
-/
def reciprocalPullback (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (valueCache : { value : CoherentNamed //
      value = differential.value point⁻¹ affine.certificate.value affine.certificate.apart } :=
        ⟨differential.value point⁻¹ affine.certificate.value affine.certificate.apart, rfl⟩) :
    NamedEquivalent
      ((Coherence.exact (-((point⁻¹) ^ 2))).mul
        valueCache.val).name
      (div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
        overlap.reciprocal.value overlap.reciprocal.apart).name := by
  let jacobian := -((point⁻¹) ^ 2)
  let numerator := reading.val
  let transformed := point ^ (genus + 1) * (jacobian * numerator)
  have original := differential.value_zero_pairs pairs point⁻¹ affine.certificate.value affine.certificate.apart
    reading
  have actual := NamedEquivalent.transport (congrArg CoherentNamed.name valueCache.property.symm) rfl original
  have first := coherentMul_respects (Coherence.exact jacobian) (Coherence.exact jacobian)
    valueCache.val
    (div (Coherence.exact numerator) affine.certificate.value affine.certificate.apart)
    (NamedEquivalent.refl _) actual
  have scaled := ReciprocalRootNames.constant_mul_quotient jacobian numerator
    affine.certificate.value affine.certificate.apart
  have inverse : (point⁻¹) ^ (genus + 1) * transformed = jacobian * numerator := by
    dsimp only [transformed]
    calc
      _ = ((point⁻¹) ^ (genus + 1) * point ^ (genus + 1)) * (jacobian * numerator) := by ring1
      _ = (point⁻¹ * point) ^ (genus + 1) * (jacobian * numerator) := by
        rewrite [Algebra.Semiring.Normalization.product_pow]
        rfl
      _ = _ := by
        rewrite [Data.Gaussian.Basic.Canonical.inv_mul_cancel point nonzero, one_pow, Data.Gaussian.Basic.one_mul]
        rfl
  exact first.trans (scaled.trans
    (ReciprocalRootNames.quotient_scaled overlap.reciprocal.value overlap.reciprocal.apart
      ((point⁻¹) ^ (genus + 1)) (jacobian * numerator) transformed affine.prepared inverse))

/-- The original general affine form pulls back to the actual retained even-chart sheet coefficient.

The same scaled affine presentation supplies the original evaluator. The
original coordinate's square-one law changes its reciprocal denominator
to the actual stored regular root, retaining the coordinate sheet factor.
Supplied exact evaluator and regular-quotient views are passed directly to
the original comparisons, while their defaults retain the former channels.
-/
def even_pullback (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (valueCache : { value : CoherentNamed //
      value = differential.value point⁻¹ affine.certificate.value affine.certificate.apart } :=
        ⟨differential.value point⁻¹ affine.certificate.value affine.certificate.apart, rfl⟩)
    (regularCache : { value : CoherentNamed //
      value = div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
        overlap.regularRoot.value overlap.regularRoot.apart } :=
          ⟨div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
            overlap.regularRoot.value overlap.regularRoot.apart, rfl⟩) :
    NamedEquivalent
      ((Coherence.exact (-((point⁻¹) ^ 2))).mul
        valueCache.val).name
      (overlap.coordinate.prepared.denominator.mul
        regularCache.val).name := by
  have square : SquareIdentity overlap.coordinate.prepared.denominator 1 := by
    simpa only [regularChart, pow_zero] using overlap.coordinate.square
  exact (reciprocalPullback overlap nonzero differential pairs affine reading valueCache).trans
    (overlap.coordinate.cancel_quotient_of_square_one
      (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val))) square regularCache)

/-- The original ramified tangent carries the general affine form to its actual regular-root cap coefficient.

The retained coordinate has square `w`, and its actual tangent is `2t`.
Original coordinate reconstruction cancels the same reciprocal root, so
no exactness is asserted of a finite rational coordinate reading.
Exact evaluator, Jacobian-product and regular-quotient views retain those
whole channels through the comparison; the literal former channels are
the defaults.
-/
def odd_pullback (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (_branch : HyperellipticReciprocal.originOrder curve = 1)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (valueCache : { value : CoherentNamed //
      value = differential.value point⁻¹ affine.certificate.value affine.certificate.apart } :=
        ⟨differential.value point⁻¹ affine.certificate.value affine.certificate.apart, rfl⟩)
    (originalCache : { value : CoherentNamed //
      value = (Coherence.exact (-((point⁻¹) ^ 2))).mul valueCache.val } :=
        ⟨(Coherence.exact (-((point⁻¹) ^ 2))).mul valueCache.val, rfl⟩)
    (regularCache : { value : CoherentNamed //
      value = div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
        overlap.regularRoot.value overlap.regularRoot.apart } :=
          ⟨div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
            overlap.regularRoot.value overlap.regularRoot.apart, rfl⟩) :
    NamedEquivalent
      (((Coherence.exact 2).mul overlap.coordinate.prepared.denominator).mul
        originalCache.val).name
      ((Coherence.exact 2).mul
        regularCache.val).name := by
  let transformed := Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val))
  let original := originalCache.val
  let reciprocal := div transformed overlap.reciprocal.value overlap.reciprocal.apart
  let regular := regularCache.val
  let factor := overlap.coordinate.prepared.denominator
  have pulled := NamedEquivalent.transport (congrArg CoherentNamed.name originalCache.property.symm) rfl
    (reciprocalPullback overlap nonzero differential pairs affine reading valueCache)
  have first := coherentMul_respects ((Coherence.exact 2).mul factor) ((Coherence.exact 2).mul factor)
    original reciprocal (NamedEquivalent.refl _) pulled
  exact first.trans ((Laws.coherentMul_assoc (Coherence.exact 2) factor reciprocal).trans
    (coherentMul_respects (Coherence.exact 2) (Coherence.exact 2) (factor.mul reciprocal) regular
      (NamedEquivalent.refl _) (overlap.coordinate.cancel_quotient transformed regularCache)))

end GeneralPullback

/-- Minus the reversed differential coefficient, before multiplying by the cap-coordinate tangent. The denominator is
the actual collar root. -/
def collarCoefficient (overlap : RootCoordinates.Overlap cap point owner) (differential :
  Differentials.Basic.Differential genus) : CoherentNamed :=
  CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
    (HyperellipticReciprocal.reversedDifferential differential).exponent)) overlap.reciprocal.value
      overlap.reciprocal.apart)

/-- A polynomial numerator in t, regular at t=0, over the retained model's regular-factor root. This is the operational
odd-chart cap expression. -/
def oddCoefficient (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) : CoherentNamed :=
  CoherentNamed.mul (Coherence.exact (-(Primitives.degree curve : ReciprocalRootNames.Gaussian)))
    (CoherentNamed.div (Power.namedPower overlap.coordinate.prepared.denominator
    (Primitives.degree curve * (HyperellipticReciprocal.reversedDifferential differential).exponent))
      overlap.regularRoot.value overlap.regularRoot.apart)

/-- Move an exact Gaussian scalar outside a product of the original coherent channels. -/
public def move_constant (constant : ReciprocalRootNames.Gaussian) (factor value : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul factor (CoherentNamed.mul (Coherence.exact constant)
      value)).name
      (CoherentNamed.mul (Coherence.exact constant) (CoherentNamed.mul factor value)).name :=
  (Laws.coherentMul_comm factor (CoherentNamed.mul (Coherence.exact constant) value)).trans
    ((Laws.coherentMul_assoc (Coherence.exact constant) value factor).trans
      (Congruence.coherentMul_respects (Coherence.exact constant) (Coherence.exact constant) (CoherentNamed.mul value
        factor) (CoherentNamed.mul factor value)
        (NamedEquivalent.refl _) (Laws.coherentMul_comm value factor)))

/-- The tangent 2t cancels the coordinate factor in the retained reciprocal root. The square law then turns w^m into the
finite polynomial t^(2m). -/
def odd_transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (overlap.collarCoefficient differential)).name
      (overlap.oddCoefficient differential).name := by
  let factor := overlap.coordinate.prepared.denominator
  let numerator := Coherence.exact (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
  let quotient := CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart
  let regular := CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart
  let polynomial := CoherentNamed.div (Power.namedPower factor (2 * (HyperellipticReciprocal.reversedDifferential
    differential).exponent))
    overlap.regularRoot.value overlap.regularRoot.apart
  have square : SquareRootProvenance.SquareIdentity factor point := by
    simpa only [branch, pow_one] using overlap.coordinate.square
  have powers := Purelib.Riemann.RootContinuation.SquareRootProvenance.SquareIdentity.even_power square
    (HyperellipticReciprocal.reversedDifferential differential).exponent
  have regularPolynomial :=
    Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects numerator
    (Power.namedPower factor (2 * (HyperellipticReciprocal.reversedDifferential differential).exponent))
    overlap.regularRoot.value overlap.regularRoot.value overlap.regularRoot.apart overlap.regularRoot.apart
    powers.symm (NamedEquivalent.refl _)
  have normalized := (Laws.coherentMul_assoc (Coherence.exact 2) factor (CoherentNamed.mul (Coherence.exact (-1))
    quotient)).trans
    ((Congruence.coherentMul_respects (Coherence.exact 2) (Coherence.exact 2) (CoherentNamed.mul factor
      (CoherentNamed.mul (Coherence.exact (-1)) quotient))
      (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.mul factor quotient)) (NamedEquivalent.refl _)
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.move_constant (-1) factor
        quotient)).trans
      ((Laws.coherentMul_assoc (Coherence.exact 2) (Coherence.exact (-1)) (CoherentNamed.mul factor
        quotient)).symm.trans
        (Congruence.coherentMul_respects (CoherentNamed.mul (Coherence.exact 2) (Coherence.exact (-1))) (Coherence.exact
          (-2)) (CoherentNamed.mul factor quotient) regular
          (by simpa only [show (2 : ReciprocalRootNames.Gaussian) * (-1) = -2 by ring1] using
            Exact.Arithmetic.exact_mul (2 : ReciprocalRootNames.Gaussian) (-1))
          (overlap.coordinate.cancel_quotient numerator))))
  have degree_eq : Primitives.degree curve = 2 := by
    rw [Primitives.degree, branch]
  simpa only [Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.oddCoefficient, degree_eq, show ((2 :
    Nat) : ReciprocalRootNames.Gaussian) = 2 by rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.collarCoefficient, factor, numerator, quotient,
      regular, polynomial,
    CoherentNamed.mul] using
    normalized.trans (Congruence.coherentMul_respects (Coherence.exact (-2)) (Coherence.exact (-2)) regular polynomial
      (NamedEquivalent.refl _) regularPolynomial)

/-- In even degree the quotient coordinate is a sheet sign. Its square law supplies the inverse sign, with no equality
test on opaque channels. -/
def even_transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0) :
    Gaussian.Equivalence.NamedEquivalent (overlap.collarCoefficient differential).name
      (CoherentNamed.mul overlap.coordinate.prepared.denominator
        (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
          (HyperellipticReciprocal.reversedDifferential differential).exponent))
            overlap.regularRoot.value overlap.regularRoot.apart))).name := by
  let factor := overlap.coordinate.prepared.denominator
  let numerator := Coherence.exact (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
  let quotient := CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart
  let regular := CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart
  have square : SquareRootProvenance.SquareIdentity factor 1 := by
    simpa only [regularChart, pow_zero] using overlap.coordinate.square
  have inverse : NamedEquivalent quotient.name (factor.mul regular).name :=
    overlap.coordinate.cancel_quotient_of_square_one numerator square
  exact (Congruence.coherentMul_respects (Coherence.exact (-1)) (Coherence.exact (-1)) quotient (CoherentNamed.mul
    factor regular)
    (NamedEquivalent.refl _) inverse).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.move_constant (-1) factor regular).symm

set_option genInjectivity false in
/-- The intrinsic degree shape chooses the proved transport law. Both outcomes retain the actual coefficient comparison,
not a parity flag alone. -/
inductive Transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) where
  /-- Retain the zero origin order and actual coefficient equivalence through the original sheet-sign coordinate. -/ |
    even (order : HyperellipticReciprocal.originOrder curve = 0)
      (equivalent : Gaussian.Equivalence.NamedEquivalent (overlap.collarCoefficient differential).name
        (CoherentNamed.mul overlap.coordinate.prepared.denominator
          (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
            (HyperellipticReciprocal.reversedDifferential differential).exponent))
              overlap.regularRoot.value overlap.regularRoot.apart))).name)
  /-- Retain the unit origin order and actual tangent-weighted coefficient equivalence through the original ramified
    coordinate. -/ | odd (order : HyperellipticReciprocal.originOrder curve = 1)
      (equivalent : Gaussian.Equivalence.NamedEquivalent
        (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
          (overlap.collarCoefficient differential)).name
        (overlap.oddCoefficient differential).name)

constructive_injectivity Transport

/-- Select the certified differential transport law from the original reciprocal origin order.

Both degree branches retain the actual operational coefficient comparison on the original cap coordinate and root
channels. -/
def transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Transport overlap differential :=
  if regular : HyperellipticReciprocal.originOrder curve = 0 then
    .even regular (overlap.even_transport differential regular)
  else
    let branch := (HyperellipticReciprocal.origin_factor curve).2.resolve_left regular
    .odd branch (overlap.odd_transport differential branch)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

end

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

section GeneralJetPullback

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation.Gaussian
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {point : Gaussian} {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((HyperellipticReciprocal.polynomial curve).eval point)}

/-- The actual inverse-coordinate Jacobian and omitted jet power cancel to the retained padded numerator. -/
theorem padded_numerator (differential : OddPowerDifferential curve.polynomial)
    (nonzero : point ≠ 0) (bound : differential.numerator.natDegree ≤ 2 * genus)
    (polynomial : { value : Coefficients // value = Reciprocal.padded differential.numerator (2 * genus) })
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ })
    (polynomialReading : { value : Gaussian // value = polynomial.val.eval point }) :
    (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)) * point ^ (genus + 1) =
      -differential.scale * polynomialReading.val := by
  have exponents : (genus + 1) + (genus + 1) = 2 * genus + 2 := by omega0
  have cancel : (point ^ (genus + 1) * point ^ (genus + 1)) * (point⁻¹) ^ 2 =
      point ^ (2 * genus) := by
    rewrite [← pow_add, exponents, pow_add]
    calc
      _ = point ^ (2 * genus) * (point * point⁻¹) ^ 2 := by
        rewrite [Algebra.Semiring.Normalization.product_pow]
        ring1
      _ = _ := by
        rewrite [Data.Gaussian.Basic.Canonical.mul_inv_cancel point nonzero, one_pow,
          Data.Gaussian.Basic.mul_one]
        rfl
  have reciprocal : polynomialReading.val = point ^ (2 * genus) * differential.numerator.eval point⁻¹ :=
    polynomialReading.property.trans ((congrArg (fun p : Coefficients => p.eval point)
      polynomial.property).trans (Reciprocal.padded_identity differential.numerator (2 * genus) bound point nonzero))
  rewrite [reading.property, reciprocal]
  calc
    _ = -differential.scale *
        (((point ^ (genus + 1) * point ^ (genus + 1)) * (point⁻¹) ^ 2) *
          differential.numerator.eval point⁻¹) := by ring1
    _ = _ := by rewrite [cancel]; rfl

/-- Expand the original even-chart form with the retained finite inverse-root jet and a polynomial error coefficient.

The actual affine-root presentation, original sheet coordinate, origin root,
jet readings, residual reading and prepared rationalizing factor are shared
with the original pullback and inverse-root remainder. The supplied original
padded polynomial is retained once; its readback removes every negative
coordinate power from the omitted part.
-/
def evenJetPullback (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (bound : differential.numerator.degreeCount ≤ 2 * genus + 1)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (polynomial : { value : Coefficients // value = Reciprocal.padded differential.numerator (2 * genus) } :=
      ⟨Reciprocal.padded differential.numerator (2 * genus), rfl⟩)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (polynomialReading : { value : Gaussian // value = polynomial.val.eval point } :=
      ⟨polynomial.val.eval point, rfl⟩) :
    (retained : Owners.Point.JetRemainder overlap.regular
      ⟨overlap.regularRoot, overlap.regularRoot_eq⟩ origin jet remainder coefficientCache residualCache factor) ×
      NamedEquivalent
        ((Coherence.exact (-((point⁻¹) ^ 2))).mul
          (differential.value point⁻¹ affine.certificate.value affine.certificate.apart)).name
        (overlap.coordinate.prepared.denominator.mul
          ((div (Coherence.exact ((point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)) * coefficientCache.val))
            origin.certificate.value origin.certificate.apart).add
              ((Coherence.exact (-differential.scale * polynomialReading.val)).mul retained.error))).name := by
  have degree : differential.numerator.natDegree ≤ 2 * genus := by
    change differential.numerator.degreeCount - 1 ≤ 2 * genus
    omega0
  let numerator := point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)
  let cleared := -differential.scale * polynomialReading.val
  let retained := overlap.regular.quotientJetRemainder ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor
    numerator cleared (padded_numerator differential nonzero degree polynomial reading polynomialReading)
  let first := overlap.even_pullback nonzero differential pairs regularChart affine reading
  exact ⟨retained.1, first.trans
    (coherentMul_respects overlap.coordinate.prepared.denominator overlap.coordinate.prepared.denominator
      (div (Coherence.exact numerator) overlap.regularRoot.value overlap.regularRoot.apart)
      ((div (Coherence.exact (numerator * coefficientCache.val)) origin.certificate.value origin.certificate.apart).add
        ((Coherence.exact cleared).mul retained.1.error)) (NamedEquivalent.refl _) retained.2)⟩

/-- Expand the actual ramified tangent form with the same finite jet and original guarded error program.

The original `2t` tangent and coordinate reconstruction first cancel the
reciprocal root. The same retained padded polynomial clears the omitted
jet power. Under the reduced odd-degree coefficient bound that polynomial
vanishes at the origin, as certified by its original reciprocal owner.
-/
def oddJetPullback (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (bound : differential.numerator.degreeCount ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (polynomial : { value : Coefficients // value = Reciprocal.padded differential.numerator (2 * genus) } :=
      ⟨Reciprocal.padded differential.numerator (2 * genus), rfl⟩)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (polynomialReading : { value : Gaussian // value = polynomial.val.eval point } :=
      ⟨polynomial.val.eval point, rfl⟩) :
    (retained : Owners.Point.JetRemainder overlap.regular
      ⟨overlap.regularRoot, overlap.regularRoot_eq⟩ origin jet remainder coefficientCache residualCache factor) ×
      NamedEquivalent
        (((Coherence.exact 2).mul overlap.coordinate.prepared.denominator).mul
          ((Coherence.exact (-((point⁻¹) ^ 2))).mul
            (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name
        ((Coherence.exact 2).mul
          ((div (Coherence.exact ((point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)) * coefficientCache.val))
            origin.certificate.value origin.certificate.apart).add
              ((Coherence.exact (-differential.scale * polynomialReading.val)).mul retained.error))).name := by
  have degree : differential.numerator.natDegree ≤ 2 * genus := by
    change differential.numerator.degreeCount - 1 ≤ 2 * genus
    omega0
  let numerator := point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)
  let cleared := -differential.scale * polynomialReading.val
  let retained := overlap.regular.quotientJetRemainder ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor
    numerator cleared (padded_numerator differential nonzero degree polynomial reading polynomialReading)
  let first := overlap.odd_pullback nonzero differential pairs branch affine reading
  exact ⟨retained.1, first.trans
    (coherentMul_respects (Coherence.exact 2) (Coherence.exact 2)
      (div (Coherence.exact numerator) overlap.regularRoot.value overlap.regularRoot.apart)
      ((div (Coherence.exact (numerator * coefficientCache.val)) origin.certificate.value origin.certificate.apart).add
        ((Coherence.exact cleared).mul retained.1.error)) (NamedEquivalent.refl _) retained.2)⟩

/-- The expanded chart form retains literally the original inverse-root remainder program. -/
theorem evenJetPullback_error (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (bound : differential.numerator.degreeCount ≤ 2 * genus + 1)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (polynomial : { value : Coefficients // value = Reciprocal.padded differential.numerator (2 * genus) } :=
      ⟨Reciprocal.padded differential.numerator (2 * genus), rfl⟩)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (polynomialReading : { value : Gaussian // value = polynomial.val.eval point } :=
      ⟨polynomial.val.eval point, rfl⟩) :
    (evenJetPullback overlap nonzero differential pairs regularChart bound
      origin jet remainder coefficientCache residualCache factor polynomial affine reading polynomialReading).1.error =
      (overlap.regular.inverseJetRemainder ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor).error := by
  unfold evenJetPullback
  exact overlap.regular.quotientJetRemainder_error ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor _ _ _

/-- The expanded chart form retains literally the original inverse-root remainder program. -/
theorem oddJetPullback_error (overlap : RootCoordinates.Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (bound : differential.numerator.degreeCount ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (polynomial : { value : Coefficients // value = Reciprocal.padded differential.numerator (2 * genus) } :=
      ⟨Reciprocal.padded differential.numerator (2 * genus), rfl⟩)
    (affine : ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ := overlap.affineRoot nonzero)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ } :=
      ⟨differential.scale * differential.numerator.eval point⁻¹, rfl⟩)
    (polynomialReading : { value : Gaussian // value = polynomial.val.eval point } :=
      ⟨polynomial.val.eval point, rfl⟩) :
    (oddJetPullback overlap nonzero differential pairs branch bound
      origin jet remainder coefficientCache residualCache factor polynomial affine reading polynomialReading).1.error =
      (overlap.regular.inverseJetRemainder ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor).error := by
  dsimp only [oddJetPullback]
  exact overlap.regular.quotientJetRemainder_error ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    origin jet remainder coefficientCache residualCache factor
    (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)) (-differential.scale * polynomialReading.val)
    (padded_numerator differential nonzero (by
      change differential.numerator.degreeCount - 1 ≤ 2 * genus
      omega0) polynomial reading polynomialReading)

end GeneralJetPullback

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

end

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Scaled

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar}

/-- The actual even-chart tangent and supplied affine form pull back with their retained signed source factor.

The original scaled source and attachment determine the factor comparison.
The supplied affine-root and numerator-reading caches feed the original
pullback; the actual regular denominator and coordinate remain unchanged.
This applies to both explicitly constructed even sheets without inferring
any constant sign from a squared-coordinate identity.
-/
def even_pullback {point factor : Gaussian} {regular : Owners.Point cap point}
    (retained : Overlap.Scaled regular factor) (nonzero : point ≠ 0)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (affine : ReciprocalRootNames.ScaledRoot retained.overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹)
    (reading : { value : Gaussian // value = differential.scale * differential.numerator.eval point⁻¹ }) :
    NamedEquivalent
      ((exact (Primitives.tangent curve point)).mul
        ((exact (-((point⁻¹) ^ 2))).mul
          (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name
      ((exact factor).mul
        (div (exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
          retained.overlap.regularRoot.value retained.overlap.regularRoot.apart)).name := by
  have tangent : Primitives.tangent curve point = 1 := by
    unfold Primitives.tangent Primitives.degree
    rewrite [parity, pow_zero]
    rfl
  rewrite [tangent]
  let valueCache : { value : CoherentNamed //
      value = differential.value point⁻¹ affine.certificate.value affine.certificate.apart } :=
    ⟨differential.value point⁻¹ affine.certificate.value affine.certificate.apart, rfl⟩
  let original := (exact (-((point⁻¹) ^ 2))).mul valueCache.val
  let quotient := div (exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
    retained.overlap.regularRoot.value retained.overlap.regularRoot.apart
  have signed := coherentMul_respects retained.overlap.coordinate.prepared.denominator (exact factor)
    quotient quotient (Scaled.factor_agrees retained) (NamedEquivalent.refl _)
  exact (Mul.coherentMul_one_left original).trans
    ((retained.overlap.even_pullback nonzero differential pairs parity affine reading
      valueCache ⟨quotient, rfl⟩).trans signed)

/-- The actual squared-uniformizer chart tangent pulls the supplied affine form to its same regular-root quotient.

The original chart tangent is exactly twice the supplied uniformizer.
The retained scaled source identifies that actual uniformizer with the
original prepared coordinate before the original ramified pullback is used.
Both original affine-root and numerator-reading caches are supplied directly;
no root, successful chart comparison or independent sheet choice is input.
-/
def odd_pullback (uniformizer : Gaussian) (nonzero : uniformizer ≠ 0)
    {regular : Owners.Point cap (uniformizer ^ 2)} (retained : Overlap.Scaled regular uniformizer)
    (parity : HyperellipticReciprocal.originOrder curve = 1)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (affine : ReciprocalRootNames.ScaledRoot retained.overlap.reciprocal
      (((uniformizer ^ 2)⁻¹) ^ (genus + 1)) curve.polynomial (uniformizer ^ 2)⁻¹)
    (reading : { value : Gaussian //
      value = differential.scale * differential.numerator.eval (uniformizer ^ 2)⁻¹ }) :
    NamedEquivalent
      ((exact (Primitives.tangent curve uniformizer)).mul
        ((exact (-(((uniformizer ^ 2)⁻¹) ^ 2))).mul
          (differential.value (uniformizer ^ 2)⁻¹ affine.certificate.value affine.certificate.apart))).name
      ((exact 2).mul
        (div (exact ((uniformizer ^ 2) ^ (genus + 1) * (-(((uniformizer ^ 2)⁻¹) ^ 2) * reading.val)))
          retained.overlap.regularRoot.value retained.overlap.regularRoot.apart)).name := by
  have tangent : Primitives.tangent curve uniformizer = 2 * uniformizer := by
    unfold Primitives.tangent Primitives.degree
    rewrite [parity, pow_one]
    rfl
  rewrite [tangent]
  let valueCache : { value : CoherentNamed //
      value = differential.value (uniformizer ^ 2)⁻¹ affine.certificate.value affine.certificate.apart } :=
    ⟨differential.value (uniformizer ^ 2)⁻¹ affine.certificate.value affine.certificate.apart, rfl⟩
  let original := (exact (-(((uniformizer ^ 2)⁻¹) ^ 2))).mul valueCache.val
  have factor := (coherentMul_respects (exact 2) (exact 2)
    retained.overlap.coordinate.prepared.denominator (exact uniformizer)
    (NamedEquivalent.refl _) (Scaled.factor_agrees retained)).trans
      (Coherent.Exact.Arithmetic.exact_mul 2 uniformizer)
  have first := coherentMul_respects (exact (2 * uniformizer))
    ((exact 2).mul retained.overlap.coordinate.prepared.denominator) original original
    factor.symm (NamedEquivalent.refl _)
  exact first.trans (retained.overlap.odd_pullback
    (Data.Gaussian.Power.pow_ne_zero_direct uniformizer nonzero 2) differential pairs parity affine reading
      valueCache ⟨original, rfl⟩)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Scaled

end
