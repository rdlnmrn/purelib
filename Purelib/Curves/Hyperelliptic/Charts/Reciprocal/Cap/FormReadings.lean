module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

/-!
# Finite observations of the actual cap-form coefficient

The same model samples prepare the regular root before any winding
attachment. The original cap parameter, its exact root scale and the
reciprocal-to-affine scale construct the actual numerical sheet once.
The complete original odd-power differential and both coordinate
Jacobians then supply one original finite process observation.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.InverseModelRootChannels
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence.Observation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar}
  {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}

/-- The cap's actual power-coordinate factor has the exact original reciprocal radicand.

The finite reciprocal polynomial identity uses the actual curve's
retained origin order, which is zero or one;
no square-root comparison or sheet selection is assumed.
-/
private theorem radicand_eq (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical) :
    parameter ^ HyperellipticReciprocal.originOrder curve *
      parameter ^ HyperellipticReciprocal.originOrder curve *
        cap.polynomial.eval (Primitives.point curve parameter) =
          (HyperellipticReciprocal.polynomial curve).eval (Primitives.point curve parameter) := by
  rewrite [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval]
  dsimp only [Primitives.point, Primitives.degree]
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rewrite [regular, pow_zero, pow_one]
    ring1
  · rewrite [branch, pow_one, pow_two]
    ring1

/-- The actual original regular preparation, reciprocal scale and affine scale at one cap parameter.

All three supplied caches retain their original dependent parents. The
coordinate is the original cap power map, and the signed power factor is
fixed before a numerical query. A winding attachment is not part of this
numerical presentation.
-/
abbrev Preparation (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (factor : Canonical := parameter ^ HyperellipticReciprocal.originOrder curve) :=
  (regular : RootChannel.Preparation cap.model cap.model_small (Primitives.point curve parameter) inside) ×
  (reciprocal : ReciprocalRootNames.ScaledRoot regular.certificate factor
    (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter)) ×
    ReciprocalRootNames.ScaledRoot reciprocal.certificate
      (((Primitives.point curve parameter)⁻¹) ^ (genus + 1))
      curve.polynomial (Primitives.point curve parameter)⁻¹

namespace Preparation

/-- A supplied whole reciprocal scaling of the same retained regular numerical root.

The existing dependent pair records its exact factor and original scaled
root, including its prepared denominator, square law, algebraic cache and
inverse. The regular numerical preparation is the literal source index.
-/
abbrev Scaling (regular : RootChannel.Preparation cap.model cap.model_small
    (Primitives.point curve parameter) inside) :=
  (factor : Canonical) × ReciprocalRootNames.ScaledRoot regular.certificate factor
    (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter)

/-- Select the supplied exact scale index, retaining the canonical cap power when none is supplied. -/
abbrev factor {regular : RootChannel.Preparation cap.model cap.model_small
    (Primitives.point curve parameter) inside} (supplied : Option (Scaling regular)) : Canonical :=
  match supplied with
  | none => parameter ^ HyperellipticReciprocal.originOrder curve
  | some actual => actual.1

end Preparation

/-- Prepare the same original model root and both exact coordinate scalings once at a nonzero cap parameter.

A supplied whole reciprocal scale is consumed under its exact regular-root
parent. With no supplied scale, the original canonical reciprocal builder
runs unchanged; both branches build the affine scale from that retained
reciprocal certificate exactly once.
-/
def prepare (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (regular : RootChannel.Preparation cap.model cap.model_small (Primitives.point curve parameter) inside :=
      RootChannel.prepare cap.model cap.model_small (Primitives.point curve parameter) inside)
    (supplied : Option (Preparation.Scaling regular) := none) :
    Preparation cap parameter inside (Preparation.factor supplied) :=
  let reciprocal : ReciprocalRootNames.ScaledRoot regular.certificate (Preparation.factor supplied)
      (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter) :=
    match supplied with
    | none => ReciprocalRootNames.ScaledRoot.build regular.certificate
        (parameter ^ HyperellipticReciprocal.originOrder curve)
        (Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero nonzero _)
        (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter) (radicand_eq cap parameter)
    | some actual => actual.2
  let affine := ReciprocalRootNames.ScaledRoot.affine reciprocal.certificate
    (Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero nonzero _)
  ⟨regular, reciprocal, affine⟩

/-- Preparing both coordinate scalings retains the whole supplied original regular numerical cache. -/
theorem prepare_regular (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (regular : RootChannel.Preparation cap.model cap.model_small (Primitives.point curve parameter) inside) :
    (prepare cap parameter nonzero inside regular).1 = regular := by
  unfold prepare
  rfl

/-- Supplying a whole scale retains that same scale and regular cache in the complete two-scale preparation. -/
theorem prepare_supplied (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (regular : RootChannel.Preparation cap.model cap.model_small (Primitives.point curve parameter) inside)
    (actual : Preparation.Scaling regular) :
    prepare cap parameter nonzero inside regular (some actual) =
      ⟨regular, actual.2, ReciprocalRootNames.ScaledRoot.affine actual.2.certificate
        (Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero nonzero _)⟩ := (rfl)

variable {factor : Canonical}

namespace Preparation

/-- Read the same actual affine root certificate from the supplied two-scale presentation. -/
@[expose] def certificate (prepared : Preparation cap parameter inside factor) :
    Riemann.RootContinuation.CertifiedSquareRoot.Certificate
      (curve.polynomial.eval (Primitives.point curve parameter)⁻¹) := prepared.2.2.certificate

end Preparation

/-- The retained scalar numerator and complete original affine-form channel with its actual cap Jacobian.

The original differential, same prepared sheet and parameter remain exact
indices. Both complete channels carry their actual defining equalities;
the original scalar numerator is evaluated once and passed to its original
numerical evaluator.
-/
abbrev Coefficient (differential : OddPowerDifferential curve.polynomial)
    (prepared : Preparation cap parameter inside factor) :=
  (reading : { value : Canonical //
    value = differential.scale * differential.numerator.eval (Primitives.point curve parameter)⁻¹ }) ×
  (value : { channel : CoherentNamed //
    channel = differential.value (Primitives.point curve parameter)⁻¹
      prepared.certificate.value prepared.certificate.apart reading }) ×
    { channel : CoherentNamed //
      channel = (Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul value.val) }

/-- Compute the complete original form and exact Jacobian from the supplied numerical presentation and scalar cache.

The optional scalar cache retains the displayed original numerator value.
Its default evaluates that same numerator once; a supplied value is passed
literally to the original differential evaluator.
-/
@[expose] def coefficient (differential : OddPowerDifferential curve.polynomial)
    (prepared : Preparation cap parameter inside factor)
    (retained : { value : Canonical //
      value = differential.scale * differential.numerator.eval (Primitives.point curve parameter)⁻¹ } :=
        ⟨differential.scale * differential.numerator.eval (Primitives.point curve parameter)⁻¹, rfl⟩) :
    Coefficient differential prepared :=
  let point := Primitives.point curve parameter
  let value := differential.value point⁻¹ prepared.certificate.value prepared.certificate.apart retained
  let jacobian := -((point⁻¹) ^ 2)
  let pulled := (Coherence.exact (Primitives.tangent curve parameter)).mul
    ((Coherence.exact jacobian).mul value)
  ⟨retained, ⟨value, rfl⟩, ⟨pulled, rfl⟩⟩

namespace Coefficient

/-- Project the complete actual cap-form channel retained with the original numerator and affine sheet. -/
@[expose] def channel {differential : OddPowerDifferential curve.polynomial}
    {prepared : Preparation cap parameter inside factor} (cached : Coefficient differential prepared) :
    CoherentNamed := cached.2.2.val

/-- The retained complete coefficient is the original affine form with the original exact cap Jacobian. -/
theorem channel_eq {differential : OddPowerDifferential curve.polynomial}
    {prepared : Preparation cap parameter inside factor} (cached : Coefficient differential prepared) :
    cached.channel =
      (Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul
          (differential.value (Primitives.point curve parameter)⁻¹
            prepared.certificate.value prepared.certificate.apart)) := by
  exact cached.2.2.property.trans (congrArg
    (fun value : CoherentNamed =>
      (Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul value))
    (cached.2.1.property.trans
      (differential.value_reading _ prepared.certificate.value prepared.certificate.apart cached.1)))

/-- The same retained whole form agrees with one quotient on its original regular model root.

The zero-pair evaluator uses the actual numerator cache and the two actual
stored scale preparations. The displayed cleared scalar identity moves
both scale factors into the numerator; it never chooses a sheet or drops
either original denominator guard.
-/
def quotient_equivalent {differential : OddPowerDifferential curve.polynomial}
    {prepared : Preparation cap parameter inside factor} (cached : Coefficient differential prepared)
    (pairs : differential.denominatorPairs = 0) (numerator : Canonical)
    (cleared : ((Primitives.point curve parameter)⁻¹) ^ (genus + 1) *
      (factor * numerator) =
      Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val)) :
    NamedEquivalent cached.channel.name
      (div (Coherence.exact numerator) prepared.1.certificate.value prepared.1.certificate.apart).name := by
  let tangent := Primitives.tangent curve parameter
  let jacobian := -(((Primitives.point curve parameter)⁻¹) ^ 2)
  let affine := prepared.2.2
  let reciprocal := prepared.2.1
  have original := differential.value_zero_pairs pairs (Primitives.point curve parameter)⁻¹
    affine.certificate.value affine.certificate.apart cached.1
  have valueEq := cached.2.1.property.trans
    (differential.value_reading _ affine.certificate.value affine.certificate.apart cached.1)
  have actual := NamedEquivalent.transport (congrArg CoherentNamed.name valueEq.symm) rfl original
  have inner := coherentMul_respects (Coherence.exact jacobian) (Coherence.exact jacobian)
    cached.2.1.val (div (Coherence.exact cached.1.val) affine.certificate.value affine.certificate.apart)
    (NamedEquivalent.refl _) actual
  have first := coherentMul_respects (Coherence.exact tangent) (Coherence.exact tangent)
    ((Coherence.exact jacobian).mul cached.2.1.val)
    ((Coherence.exact jacobian).mul
      (div (Coherence.exact cached.1.val) affine.certificate.value affine.certificate.apart))
    (NamedEquivalent.refl _) inner
  have innerScalar := ReciprocalRootNames.constant_mul_quotient jacobian cached.1.val
    affine.certificate.value affine.certificate.apart
  have second := coherentMul_respects (Coherence.exact tangent) (Coherence.exact tangent)
    ((Coherence.exact jacobian).mul
      (div (Coherence.exact cached.1.val) affine.certificate.value affine.certificate.apart))
    (div (Coherence.exact (jacobian * cached.1.val)) affine.certificate.value affine.certificate.apart)
    (NamedEquivalent.refl _) innerScalar
  have third := ReciprocalRootNames.constant_mul_quotient tangent (jacobian * cached.1.val)
    affine.certificate.value affine.certificate.apart
  have fourth := ReciprocalRootNames.quotient_scaled reciprocal.certificate.value reciprocal.certificate.apart
    (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) (tangent * (jacobian * cached.1.val))
    (factor * numerator) affine.prepared cleared
  have fifth := ReciprocalRootNames.quotient_scaled prepared.1.certificate.value prepared.1.certificate.apart
    factor (factor * numerator) numerator reciprocal.prepared rfl
  have body := first.trans (second.trans (third.trans (fourth.trans fifth)))
  exact NamedEquivalent.transport (congrArg CoherentNamed.name cached.2.2.property.symm) rfl body

end Coefficient

/-- A finite original process request retaining the actual numerical presentation and whole cap-form coefficient. -/
abbrev Reading (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (inside : collar.box.Contains (Primitives.point curve parameter)) (target : Rational)
    (factor : Canonical := parameter ^ HyperellipticReciprocal.originOrder curve) :=
  (prepared : Preparation cap parameter inside factor) ×
  (cached : Coefficient differential prepared) ×
    Request cached.channel target

namespace Reading

/-- Observe the complete supplied coefficient on its exact prepared sheet and retain both whole caches.

The actual request is built once from that coefficient's original channel.
The scale remains the original preparation's index; the operation performs
no root preparation, coordinate scaling or winding attachment.
-/
def observe (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target)
    (prepared : Preparation cap parameter inside factor) (cached : Coefficient differential prepared) :
    Reading differential cap parameter inside target factor :=
  let observed := Request.build cached.channel target positive
  ⟨prepared, cached, observed⟩

/-- The complete supplied-sheet observation retains the exact preparation, coefficient and original request factory. -/
theorem observe_eq (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target)
    (prepared : Preparation cap parameter inside factor) (cached : Coefficient differential prepared) :
    observe differential cap parameter inside target positive prepared cached =
      ⟨prepared, cached, Request.build cached.channel target positive⟩ := (rfl)

end Reading

/-- Pay one actual finite whole-form observation on the original cap coordinate and retained numerical sheet.

The original request refines that complete channel and retains its actual
state, witness and visible radius. No Laurent coefficient functional or
assumed successful pullback comparison replaces the observed program.
-/
def read (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target)
    (prepared : Preparation cap parameter inside := prepare cap parameter nonzero inside)
    (cached : Coefficient differential prepared := coefficient differential prepared) :
    Reading differential cap parameter inside target :=
  Reading.observe differential cap parameter inside target positive prepared cached

/-- The complete reading constructor retains both supplied caches and requests their same actual whole channel. -/
theorem read_eq (differential : OddPowerDifferential curve.polynomial)
    (cap : ReciprocalInnerInverse.Data curve collar) (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target)
    (prepared : Preparation cap parameter inside) (cached : Coefficient differential prepared) :
    read differential cap parameter nonzero inside target positive prepared cached =
      ⟨prepared, cached, Request.build cached.channel target positive⟩ := by
  exact Reading.observe_eq differential cap parameter inside target positive prepared cached

namespace Reading

/-- Read the actual original observation request of the supplied whole-form coefficient cache. -/
@[expose] def request {differential : OddPowerDifferential curve.polynomial} {target : Rational}
    (reading : Reading differential cap parameter inside target factor) : Request reading.2.1.channel target :=
  reading.2.2

/-- The actual finite whole-form observation has the retained requested visible squared radius. -/
theorem radius_lt {differential : OddPowerDifferential curve.polynomial} {target : Rational}
    (reading : Reading differential cap parameter inside target factor) : reading.request.reading.radius < target :=
  reading.request.radius_lt

end Reading

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings

end
