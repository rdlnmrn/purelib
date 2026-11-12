module
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
public import Purelib.Approximation.Gaussian.Division.InverseDifference
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Arithmetic.Distributive
public import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation

public section

/-!
# Owners of the reciprocal cap's actual regular-factor model

The retained polynomial model determines each operational root through its
sheet-consistent finite Newton samples. The attached winding owner names that
same channel. The actual collar fiber selects the endpoint; the quotient
coordinate then matches its reciprocal root to this regular model root.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Data)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

set_option genInjectivity false in
/-- The retained regular-factor root channel at one original reciprocal cap coordinate.

Its nominal parent is the cached inverse-root model on the original collar box. -/
structure Point (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) where
  /-- The retained root channel of the exact original inverse-root model at this coordinate. -/ channel :
    InverseModelRootChannels.RootChannel data.model point

constructive_injectivity Point

namespace Point

/-- Construct the root channel from the retained model bound at a point inside its original collar box. -/
@[expose] def build (data : ReciprocalInnerInverse.Data curve collar) (point : InverseRootPolynomial.Gaussian) (inside :
  collar.box.Contains point)
    (cached : RootChannel.Preparation data.model data.model_small point inside :=
      RootChannel.prepare data.model data.model_small point inside) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data point :=
  ⟨RootChannel.build data.model data.model_small point inside cached⟩

/-- Read the regular origin root from the same retained cap model without choosing another sheet.

The original symmetric collar box contains zero by its intrinsic radius
positivity. The ordinary point constructor uses the same cached model,
polynomial and seed as every other cap point.
-/
@[expose] def atOrigin (data : ReciprocalInnerInverse.Data curve collar) : Point data 0 :=
  Point.build data 0 (by
    rewrite [collar.box_eq]
    have positive := ReciprocalExteriorCollar.innerRadius_positive curve
    have negative := Purelib.Data.Rat.Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
    change -ReciprocalExteriorCollar.innerRadius curve ≤ (0 : Purelib.Data.Rat.Fraction.Rational) at negative
    exact ⟨negative, positive.le, negative, positive.le⟩)

/-- Read the square-root certificate from the retained original regular-factor root channel. -/
@[expose] def certificate {data : ReciprocalInnerInverse.Data curve collar} {point : InverseRootPolynomial.Gaussian}
  (owned : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data point) :
    CertifiedSquareRoot.Certificate (data.polynomial.eval point) := owned.channel.certificate

/-- The complete point constructor retains the exact supplied numerical root certificate. -/
theorem build_certificate (data : ReciprocalInnerInverse.Data curve collar) (point : Gaussian)
    (inside : collar.box.Contains point)
    (cached : RootChannel.Preparation data.model data.model_small point inside) :
    (build data point inside cached).certificate = cached.certificate := rfl

section InverseJet

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence (coherentAdd_respects)
open Purelib.Approximation.Gaussian.Coherent.Additive (coherentNeg_respects)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)
open Purelib.Polynomial.Ascending.Gaussian

variable {cap : Data curve collar} {point : Gaussian}

/-- The actual retained cap polynomial has the original finite jet radicand at every displayed coordinate. -/
private theorem cap_radicand_eval (cap : ReciprocalInnerInverse.Data curve collar) (point : Gaussian) :
    cap.polynomial.eval point =
      Evaluation.eval (InfinityCoefficients.radicand curve) point :=
  (congrArg (fun polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial =>
    polynomial.eval point)
      (cap.polynomial_eq.trans (InfinityCoefficients.radicand_toDense curve).symm)).trans
    (Polynomial.Ascending.Gaussian.Dense.Evaluation.toDense_eval (InfinityCoefficients.radicand curve) point)

/-- Cache the actual cleared inverse-root jet mismatch and its exact original finite-tail reading.

Both square-root channels come from the supplied original cap owners. The
retained regular certificate is an exact view of its same-model Point; that
original Point exists at the origin as well as at punctured overlaps. The
finite jet, residual factor and optional exact Horner reading are supplied actual caches. Horner values,
quotients and the composite channel are computed once; the original rational
sidecar records the computed omitted-power reading and its operational law.
The additional factor is multiplied, not divided, so this result alone does
not claim its uniform neighborhood apartness.
-/
@[expose] def inverseJetCleared (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor
      (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point } :=
      ⟨Evaluation.eval jet.val point, rfl⟩)
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point } :=
      ⟨Evaluation.eval remainder.val point, rfl⟩) :
    (channel : CoherentNamed) × Provenance.Rational.Basic.RationalSidecar channel := by
  let root := certificate.val.value
  let initial := origin.certificate.value
  let coefficient := coefficientCache.val
  let exactCoefficient := Coherence.exact coefficient
  let inverse := div (Coherence.exact 1) root certificate.val.apart
  let quotient := div exactCoefficient initial origin.certificate.apart
  let channel := ((inverse.add quotient.neg).mul (initial.mul root)).mul
    (initial.add (root.mul exactCoefficient))
  let reading := point ^ (genus + 1) * residualCache.val
  have first := Cancellation.inverse_difference_cleared root initial exactCoefficient
    certificate.val.apart origin.certificate.apart
  have coefficientSquare := Coherent.Exact.Arithmetic.exact_mul coefficient coefficient
  have product : NamedEquivalent
      ((root.mul root).mul (exactCoefficient.mul exactCoefficient)).name
      (Coherence.exact (cap.polynomial.eval point * (coefficient * coefficient))).name :=
    (coherentMul_respects (root.mul root) (Coherence.exact (cap.polynomial.eval point))
      (exactCoefficient.mul exactCoefficient) (Coherence.exact (coefficient * coefficient))
      certificate.val.square coefficientSquare).trans
      (Coherent.Exact.Arithmetic.exact_mul (cap.polynomial.eval point) (coefficient * coefficient))
  have negative := (coherentNeg_respects _ _ product).trans
    (Arithmetic.Neg.exactNeg (cap.polynomial.eval point * (coefficient * coefficient)))
  have exactResult :=
    (coherentAdd_respects (initial.mul initial) (Coherence.exact (cap.polynomial.eval 0))
      ((root.mul root).mul (exactCoefficient.mul exactCoefficient)).neg
      (Coherence.exact (-(cap.polynomial.eval point * (coefficient * coefficient))))
      origin.certificate.square negative).trans
        (Coherent.Exact.Arithmetic.exact_add (cap.polynomial.eval 0)
          (-(cap.polynomial.eval point * (coefficient * coefficient))))
  have scalar : cap.polynomial.eval 0 + -(cap.polynomial.eval point * (coefficient * coefficient)) = reading := by
    calc
      _ = Coefficient.coefficient (InfinityCoefficients.radicand curve) 0 -
          Evaluation.eval (InfinityCoefficients.radicand curve) point *
            (Evaluation.eval jet.val point) ^ 2 := by
        dsimp only [coefficient]
        rewrite [coefficientCache.property, cap_radicand_eval cap 0, Evaluation.eval_at_zero,
          cap_radicand_eval cap point, pow_two]
        rfl
      _ = _ := (remainder.property point).trans
        (congrArg (fun value => point ^ (genus + 1) * value) residualCache.property.symm)
  refine ⟨channel, reading, ?_⟩
  exact Equivalence.NamedEquivalent.transport rfl (congrArg (fun value => (Coherence.exact value).name) scalar)
    (first.trans exactResult)

namespace JetRemainder

/-- The exact operational equation of a guarded finite inverse-root expansion.

The original root certificate and origin guard fix both quotient programs.
The three displayed scalar readings retain the numerator, principal part
and omitted coefficient of the actual error channel.
-/
@[expose] def Equation (certificate : Certificate (cap.polynomial.eval point)) (origin : Point cap 0)
    (numerator coefficient power : Gaussian) (error : CoherentNamed) : Type :=
  NamedEquivalent (div (Coherence.exact numerator) certificate.value certificate.apart).name
    ((div (Coherence.exact coefficient) origin.certificate.value origin.certificate.apart).add
      ((Coherence.exact power).mul error)).name

/-- The original error and its complete guarded finite-expansion equation as one dependent pair. -/
@[expose] def Result (certificate : Certificate (cap.polynomial.eval point)) (origin : Point cap 0)
    (numerator coefficient power : Gaussian) : Type 1 :=
  (error : CoherentNamed) × Equation certificate origin numerator coefficient power error

/-- Scale a retained finite inverse-root expansion using its complete original error and comparison.

The supplied clearing equation fixes the omitted coefficient. The original
root and origin guards, error program and operational comparison are consumed
directly; distribution computes only the new scalar numerator and principal part.
-/
def Result.scale (certificate : Certificate (cap.polynomial.eval point)) (origin : Point cap 0)
    (coefficient omittedPower : Gaussian) (retained : Result certificate origin 1 coefficient omittedPower)
    (numerator cleared : Gaussian) (clearing : numerator * omittedPower = cleared) :
    Equation certificate origin numerator (numerator * coefficient) cleared retained.1 := by
  let inverse := div (Coherence.exact 1) certificate.value certificate.apart
  let principal := div (Coherence.exact coefficient) origin.certificate.value origin.certificate.apart
  let exactNumerator := Coherence.exact numerator
  let power := Coherence.exact omittedPower
  have quotient : NamedEquivalent
      (div exactNumerator certificate.value certificate.apart).name
      (exactNumerator.mul inverse).name := by
    have move := ReciprocalRootNames.constant_mul_quotient numerator 1
      certificate.value certificate.apart
    rewrite [Data.Gaussian.Basic.mul_one] at move
    exact move.symm
  have expand := coherentMul_respects exactNumerator exactNumerator inverse
    (principal.add (power.mul retained.1)) (Equivalence.NamedEquivalent.refl _) retained.2
  have distribute := Arithmetic.Distributive.coherentMul_add_left exactNumerator principal (power.mul retained.1)
  have first := ReciprocalRootNames.constant_mul_quotient numerator coefficient
    origin.certificate.value origin.certificate.apart
  have product : NamedEquivalent (exactNumerator.mul power).name (Coherence.exact cleared).name := by
    have evaluated := Coherent.Exact.Arithmetic.exact_mul numerator omittedPower
    rewrite [clearing] at evaluated
    exact evaluated
  have last := (Laws.coherentMul_assoc exactNumerator power retained.1).symm.trans
    (coherentMul_respects (exactNumerator.mul power) (Coherence.exact cleared) retained.1 retained.1
      product (Equivalence.NamedEquivalent.refl _))
  exact quotient.trans (expand.trans (distribute.trans
    (coherentAdd_respects (exactNumerator.mul principal)
      (div (Coherence.exact (numerator * coefficient)) origin.certificate.value origin.certificate.apart)
      (exactNumerator.mul (power.mul retained.1)) ((Coherence.exact cleared).mul retained.1) first last)))

end JetRemainder

set_option genInjectivity false in
/-- The retained quotient chain and operational identity of one actual inverse-root jet remainder.

The same original Point, stored certificate, origin, H/E readings and factor
preparation index every cached quotient. Each defining equality fixes the
whole original guarded value. Subsequent comparisons consume these actual
intermediate values rather than reconstructing the quotient chain.
-/
structure JetRemainder (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val)))) where
  /-- The original exact residual name shared by the quotient chain. -/
  residual : CoherentNamed
  /-- The cached source is exactly the supplied residual reading. -/
  residual_eq : residual = Coherence.exact residualCache.val
  /-- The original residual divided by its retained rationalizing factor. -/
  factorQuotient : CoherentNamed
  /-- The cached first quotient is exactly the original guarded construction. -/
  factorQuotient_eq : factorQuotient = div residual factor.denominator factor.apart
  /-- The cached first quotient divided by the actual nearby regular root. -/
  rootQuotient : CoherentNamed
  /-- The cached second quotient consumes the same actual first quotient. -/
  rootQuotient_eq : rootQuotient = div factorQuotient certificate.val.value certificate.val.apart
  /-- The complete original error and its operational finite-jet identity. -/
  result : JetRemainder.Result certificate.val origin 1 coefficientCache.val (point ^ (genus + 1))
  /-- The retained result consumes the actual second quotient and original origin guard. -/
  error_eq : result.1 = div rootQuotient origin.certificate.value origin.certificate.apart

constructive_injectivity JetRemainder

namespace JetRemainder

variable {regular : Point cap point}
  {certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate }}
  {origin : Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point }}
  {residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point }}
  {factor : Division.Prepared (origin.certificate.value.add
    (certificate.val.value.mul (Coherence.exact coefficientCache.val)))}

/-- The actual error is the original result pair's first entry, stored once. -/
abbrev error (retained : JetRemainder regular certificate origin jet remainder coefficientCache residualCache factor) :
    CoherentNamed := retained.result.1

/-- The retained operational identity is the same original result pair's second entry. -/
abbrev equivalent
    (retained : JetRemainder regular certificate origin jet remainder coefficientCache residualCache factor) :=
  retained.result.2

end JetRemainder

/-- Retain an actual local inverse-root remainder using the same supplied jet, residual tail and guarded factor.

The finite cleared identity is cancelled successively by the actual prepared
rationalizing factor, the actual regular root and the actual origin root.
All three original guards remain attached to those same channels. The
actual omitted-power coefficient and residual readings are shared caches;
three original quotient operations build the retained remainder once.
The result is an operational finite jet identity, without a completed germ.
-/
def inverseJetRemainder (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val)))) :
    JetRemainder regular certificate origin jet remainder coefficientCache residualCache factor := by
  let root := certificate.val.value
  let initial := origin.certificate.value
  let coefficient := Coherence.exact coefficientCache.val
  let power := Coherence.exact (point ^ (genus + 1))
  let residual := Coherence.exact residualCache.val
  let product := initial.mul root
  let inverse := div (Coherence.exact 1) root certificate.val.apart
  let quotient := div coefficient initial origin.certificate.apart
  let difference := inverse.add quotient.neg
  let reading := Coherence.exact (point ^ (genus + 1) * residualCache.val)
  let first := div residual factor.denominator factor.apart
  let second := div first root certificate.val.apart
  let error := div second initial origin.certificate.apart
  let cleared := inverseJetCleared regular certificate origin jet remainder coefficientCache residualCache
  have clearing : NamedEquivalent ((difference.mul product).mul factor.denominator).name reading.name :=
    (coherentMul_respects (difference.mul product) (difference.mul product)
      factor.denominator (initial.add (root.mul coefficient)) (Equivalence.NamedEquivalent.refl _)
      factor.equivalent.symm).trans cleared.2.equivalent
  let firstReading := div reading factor.denominator factor.apart
  have cancelFactor : NamedEquivalent (difference.mul product).name firstReading.name :=
    Cancellation.coherentDiv_of_mul (difference.mul product) factor.denominator reading factor.apart clearing
  let secondReading := div firstReading root certificate.val.apart
  have cancelRoot : NamedEquivalent (difference.mul initial).name secondReading.name :=
    Cancellation.coherentDiv_of_mul (difference.mul initial) root firstReading certificate.val.apart
      ((Laws.coherentMul_assoc difference initial root).trans cancelFactor)
  have cancelOrigin : NamedEquivalent difference.name
      (div secondReading initial origin.certificate.apart).name :=
    Cancellation.coherentDiv_of_mul difference initial secondReading origin.certificate.apart cancelRoot
  have exactProduct : NamedEquivalent reading.name (power.mul residual).name :=
    (Coherent.Exact.Arithmetic.exact_mul (point ^ (genus + 1)) residualCache.val).symm
  have firstPower : NamedEquivalent firstReading.name (power.mul first).name :=
    (Coherent.Division.Equivalence.coherentDiv_respects reading (power.mul residual)
      factor.denominator factor.denominator factor.apart factor.apart exactProduct
      (Equivalence.NamedEquivalent.refl _)).trans
        (Cancellation.coherentDiv_mul_left power residual factor.denominator factor.apart)
  have secondPower : NamedEquivalent secondReading.name (power.mul second).name :=
    (Coherent.Division.Equivalence.coherentDiv_respects firstReading (power.mul first) root root
      certificate.val.apart certificate.val.apart firstPower (Equivalence.NamedEquivalent.refl _)).trans
        (Cancellation.coherentDiv_mul_left power first root certificate.val.apart)
  have lastPower : NamedEquivalent (div secondReading initial origin.certificate.apart).name
      (power.mul error).name :=
    (Coherent.Division.Equivalence.coherentDiv_respects secondReading (power.mul second) initial initial
      origin.certificate.apart origin.certificate.apart secondPower (Equivalence.NamedEquivalent.refl _)).trans
        (Cancellation.coherentDiv_mul_left power second initial origin.certificate.apart)
  have remainderIdentity := cancelOrigin.trans lastPower
  have recover : NamedEquivalent (difference.add quotient).name inverse.name :=
    (Arithmetic.Add.coherentAdd_assoc inverse quotient.neg quotient).trans
      ((coherentAdd_respects inverse inverse (quotient.neg.add quotient) (Coherence.exact 0)
        (Equivalence.NamedEquivalent.refl _) (Arithmetic.Neg.coherentAdd_neg_left quotient)).trans
        (Arithmetic.Add.coherentAdd_zero_right inverse))
  exact ⟨residual, rfl, first, rfl, second, rfl, ⟨error, recover.symm.trans
    ((coherentAdd_respects difference (power.mul error) quotient quotient remainderIdentity
      (Equivalence.NamedEquivalent.refl _)).trans (Arithmetic.Add.coherentAdd_comm (power.mul error) quotient))⟩, rfl⟩

/-- Multiply the retained inverse-root jet by an exact numerator and retain the same original guarded error.

The supplied scalar clearing equation identifies the actual omitted-power
coefficient. Distribution changes no root, preparation, finite coefficient
cache or residual cache. Both chart parities consume this same operation.
-/
def quotientJetRemainder (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val))))
    (numerator cleared : Gaussian) (clearing : numerator * point ^ (genus + 1) = cleared)
    (retained : JetRemainder regular certificate origin jet remainder coefficientCache residualCache factor :=
      inverseJetRemainder regular certificate origin jet remainder coefficientCache residualCache factor) :
    (retained : JetRemainder regular certificate origin jet remainder coefficientCache residualCache factor) ×
      JetRemainder.Equation certificate.val origin numerator (numerator * coefficientCache.val) cleared
        retained.error := by
  exact ⟨retained, JetRemainder.Result.scale certificate.val origin coefficientCache.val (point ^ (genus + 1))
    retained.result numerator cleared clearing⟩

/-- Multiplying the finite jet retains literally the original inverse-root error program. -/
theorem quotientJetRemainder_error (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val))))
    (numerator cleared : Gaussian) (clearing : numerator * point ^ (genus + 1) = cleared) :
    (quotientJetRemainder regular certificate origin jet remainder coefficientCache residualCache factor
      numerator cleared clearing).1.error =
      (inverseJetRemainder regular certificate origin jet remainder coefficientCache residualCache factor).error := by
  unfold quotientJetRemainder
  rfl

/-- The retained error uses the actual residual reading and the same three original guarded quotient programs. -/
theorem inverseJetRemainder_error (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point })
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val)))) :
    (inverseJetRemainder regular certificate origin jet remainder coefficientCache residualCache factor).error =
      div (div (div (Coherence.exact residualCache.val) factor.denominator factor.apart)
        certificate.val.value certificate.val.apart) origin.certificate.value origin.certificate.apart := by
  unfold inverseJetRemainder
  rfl

/-- Supplying the same actual jet reading preserves the complete original cleared channel and sidecar.

The cache equations fix the original coefficient and residual values.
Substituting both scalar equations identifies the entire original channel, original reading
and retained operational certificate with the default construction.
-/
theorem inverseJetCleared_cache_eq (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor
      (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point })
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point } :=
      ⟨Evaluation.eval remainder.val point, rfl⟩) :
    inverseJetCleared regular certificate origin jet remainder coefficientCache residualCache =
      inverseJetCleared regular certificate origin jet remainder := by
  rcases coefficientCache with ⟨coefficient, same⟩
  cases same
  rcases residualCache with ⟨residual, residualSame⟩
  cases residualSame
  rfl

/-- The exact sidecar reads the supplied original residual tail at the same original cap coordinate. -/
theorem inverseJetCleared_value (regular : Point cap point)
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate })
    (origin : Point cap 0)
    (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor
      (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point } :=
      ⟨Evaluation.eval jet.val point, rfl⟩)
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point } :=
      ⟨Evaluation.eval remainder.val point, rfl⟩) :
    (inverseJetCleared regular certificate origin jet remainder coefficientCache residualCache).2.value =
      point ^ (genus + 1) * Evaluation.eval remainder.val point :=
  congrArg (fun value => point ^ (genus + 1) * value) residualCache.property

end InverseJet

end Point

/-- Reuse the actual collar endpoint and the retained regular model. -/
@[expose] def atFiber (data : ReciprocalInnerInverse.Data curve collar) {source : InverseRootPolynomial.Gaussian} (fiber
  : ReciprocalCollarTransport.Fiber collar source) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point data (collar.sidePoint source) :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners.Point.build data _ (by
    rw [collar.box_eq, collar.sidePoint_eq]
    exact ReciprocalExteriorCollar.chord_contains curve fiber.boundary.1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
