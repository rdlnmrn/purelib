module
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Bridge
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Data.Rat.SmallWidth
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Fraction.Power.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Name.Apart.Exact
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.ClearBoxPaths

public section

/-!
# Cap coordinates from the actual reciprocal collar root

Divide the retained reciprocal root by the root of the retained regular model.
The resulting channel squares to w^originOrder: it is the ramified coordinate
in odd degree and the sheet sign in even degree. Its prepared presentation
and attached winding owner both reconstruct the original reciprocal root.
The pointwise constructor retains the supplied root occurrence and model root channel;
the boundary constructor also retains the original collar crossing.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Riemann.Paths

open Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian CoherentNamed NamedEquivalent
  Prepared)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_comm
  coherentMul_squares_interchange)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence (coherentAdd_respects)
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)

/-- The quotient of the two retained root channels squares to the exact target fixed by their parameter identity.

The supplied certificates retain both channels and the denominator apartness.
Their product identity and exact target equality give the same quotient square. -/
@[expose] def quotient_square {first second : Gaussian} (numerator : Certificate first)
    (denominator : Certificate second) (target : Gaussian) (identity : second * target = first) :
    SquareIdentity (div numerator.value denominator.value denominator.apart)
      target := by
  let quotient := div numerator.value denominator.value denominator.apart
  let scalar := exact second
  have cancel : NamedEquivalent (mul denominator.value quotient).name numerator.value.name :=
    (Laws.coherentMul_comm denominator.value quotient).trans
      (Cancellation.coherentDiv_mul_cancel numerator.value denominator.value denominator.apart)
  have left : NamedEquivalent (mul scalar (mul quotient quotient)).name
    (exact first).name :=
    (coherentMul_respects scalar (mul denominator.value
      denominator.value) (mul quotient quotient) (mul quotient quotient)
      denominator.square.symm (Equivalence.NamedEquivalent.refl _)).trans
      ((Laws.coherentMul_squares_interchange denominator.value quotient).trans
        ((coherentMul_respects (mul denominator.value
          quotient) numerator.value
          (mul denominator.value quotient) numerator.value cancel cancel).trans
            numerator.square))
  have right : NamedEquivalent (mul scalar (exact target)).name
    (exact first).name := by
    rw [← identity]
    exact Coherent.Exact.Arithmetic.exact_mul second target
  exact Cancellation.coherentMul_cancel_left scalar (mul quotient quotient)
    (exact target)
    (exactApart second (SquareRootChannelOwnership.parameter_nonzero denominator))
    (left.trans right.symm)

set_option genInjectivity false in
/-- The ratio, its division-safe presentation and its reconstruction law are retained together.

The indexed numerator and denominator certificates fix both root occurrences.
The cached quotient and its prepared form retain that same pair of channels. -/
structure RootCoordinate {first second : Gaussian} (numerator : Certificate first)
    (denominator : Certificate second) (target : Gaussian) where
  /-- The cached original operational quotient of the supplied numerator and denominator root channels. -/ quotient :
    CoherentNamed
  /-- The cached quotient uses exactly the two original root channels and the original denominator apartness. -/
    quotient_eq : quotient = div numerator.value denominator.value denominator.apart
  /-- The retained division-ready presentation of the same cached quotient. -/ prepared :
    Division.Prepared quotient
  /-- The retained prepared coordinate channel squares operationally to its original target. -/ square :
    SquareIdentity prepared.denominator target
  /-- Multiplying the retained coordinate channel by the original regular root reconstructs the original reciprocal
    root. -/ reconstruct : NamedEquivalent (mul prepared.denominator denominator.value).name
    numerator.value.name

constructive_injectivity RootCoordinate

namespace RootCoordinate

/-- Cache the quotient of the supplied original root channels and construct its prepared coordinate certificate and
reconstruction law. -/
@[expose] def build {first second : Gaussian} (numerator : Certificate first) (denominator :
  Certificate second)
    (target : Gaussian) (nonzero : target ≠ 0) (identity : second * target = first) :
    RootCoordinate numerator denominator target := by
  let quotient := div numerator.value denominator.value denominator.apart
  let square := quotient_square numerator denominator target
    identity
  let prepared := SquareRootProvenance.prepared_of_square square nonzero
  exact ⟨quotient, rfl, prepared,
    (coherentMul_respects prepared.denominator quotient prepared.denominator
      quotient
      prepared.equivalent.symm prepared.equivalent.symm).trans square,
    (coherentMul_respects prepared.denominator quotient denominator.value
      denominator.value
      prepared.equivalent.symm (Equivalence.NamedEquivalent.refl _)).trans
      (Cancellation.coherentDiv_mul_cancel numerator.value denominator.value denominator.apart)⟩

/-- A retained numerator factorization identifies the actual prepared root coordinate by guarded cancellation.

The comparison consumes the original cached reconstruction and denominator
apartness. It constructs no new quotient of the original root operands.
-/
def factor_agrees {first second target : Gaussian} {numerator : Certificate first}
    {denominator : Certificate second} (coordinate : RootCoordinate numerator denominator target)
    (factor : CoherentNamed)
    (product : NamedEquivalent (factor.mul denominator.value).name numerator.value.name) :
    NamedEquivalent coordinate.prepared.denominator.name factor.name :=
  Cancellation.coherentMul_cancel_left denominator.value coordinate.prepared.denominator factor denominator.apart
    ((Laws.coherentMul_comm denominator.value coordinate.prepared.denominator).trans
      (coordinate.reconstruct.trans (product.symm.trans (Laws.coherentMul_comm factor denominator.value))))

/-- Read the square-root certificate from the retained prepared coordinate channel. -/
@[expose] def certificate {first second target : Gaussian} {numerator : Certificate first}
  {denominator : Certificate second}
    (coordinate : RootCoordinate numerator denominator
      target) : Certificate target :=
  ⟨coordinate.prepared.denominator, coordinate.prepared.apart, coordinate.square⟩

end RootCoordinate

open Purelib.Data.Rat.Fraction

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  ReciprocalExteriorCollar.Data curve}
  {source : Gaussian}

set_option genInjectivity false in
/-- The retained coordinate comparison between an original reciprocal owner and the same cap model's regular root.

Both original certificates, their exact readbacks, prepared quotient coordinate and attached winding owner remain
linked. -/
structure Overlap (cap : ReciprocalInnerInverse.Data curve collar)
    (point : Gaussian)
    (reciprocalOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) where
  /-- The retained original cap-model root channel at the overlap point. -/ regular : Owners.Point cap point
  /-- The cached certificate of the supplied original reciprocal winding owner. -/ reciprocal :
    Certificate ((HyperellipticReciprocal.polynomial curve).eval point)
  /-- The cached reciprocal certificate is exactly the supplied original owner's certificate. -/ reciprocal_eq :
    reciprocal = reciprocalOwner.certificate reciprocalOwner.parameterNonzero
  /-- The cached original regular cap-model root certificate. -/ regularRoot : Certificate
    (cap.polynomial.eval point)
  /-- The cached regular certificate is exactly the retained original model channel's certificate. -/ regularRoot_eq :
    regularRoot = regular.certificate
  /-- The prepared quotient of these exact original root certificates, squaring to the reciprocal origin factor. -/
    coordinate : RootCoordinate reciprocal regularRoot (point
    ^ HyperellipticReciprocal.originOrder curve)
  /-- The winding owner attached to this exact retained prepared coordinate channel. -/ attached :
    SquareRootChannelOwnership.Attachment coordinate.prepared.denominator
    (point ^ HyperellipticReciprocal.originOrder curve)

constructive_injectivity Overlap

namespace Overlap

/-- Construct the quotient coordinate from the original reciprocal owner and actual regular-model point.

The supplied point is consumed as the original regular cache. Omitting it
keeps the literal original same-model point construction as the default.
-/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) (point : Gaussian) (inside : collar.box.Contains
  point)
    (reciprocalOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point))
    (actualRegular : Owners.Point cap point := Owners.Point.build cap point inside) :
    Overlap cap point reciprocalOwner :=
  let regular := actualRegular
  let reciprocal := reciprocalOwner.certificate reciprocalOwner.parameterNonzero
  let regularRoot := regular.certificate
  have identity : cap.polynomial.eval point * point ^ HyperellipticReciprocal.originOrder curve =
      (HyperellipticReciprocal.polynomial curve).eval point := by
    rw [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval]
  have nonzero : point ^ HyperellipticReciprocal.originOrder curve ≠ 0 := by
    intro zero
    apply reciprocalOwner.parameterNonzero
    exact identity.symm.trans (by rw [zero, Data.Gaussian.Basic.mul_zero])
  let coordinate := RootCoordinate.build reciprocal
    regularRoot _ nonzero identity
  ⟨regular, reciprocal, rfl, regularRoot, rfl, coordinate, SquareRootChannelOwnership.attach coordinate.certificate⟩

/-- The overlap retains the complete actual supplied regular-model point without constructing another one. -/
theorem build_regular (cap : ReciprocalInnerInverse.Data curve collar) (point : Gaussian)
    (inside : collar.box.Contains point)
    (reciprocalOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point))
    (regular : Owners.Point cap point) : (build cap point inside reciprocalOwner regular).regular = regular := rfl

/-- Construct the original overlap from the actual scaled regular root and its actual attached winding owner.

The supplied original point supplies the regular certificate and containment.
The retained attachment supplies the reciprocal owner. Their exact original
caches determine the same original quotient and coordinate presentation.
-/
@[expose] def ofScaled {cap : ReciprocalInnerInverse.Data curve collar} {point factor : Gaussian}
    (regular : Owners.Point cap point)
    (root : ReciprocalRootNames.ScaledRoot regular.certificate factor
      (HyperellipticReciprocal.polynomial curve) point)
    (attached : SquareRootChannelOwnership.Attachment root.certificate.value
      ((HyperellipticReciprocal.polynomial curve).eval point)) : Overlap cap point attached.owner :=
  build cap point regular.channel.inside attached.owner regular

/-- The prepared coordinate of the actual scaled-root overlap agrees with its original exact factor.

Both operational identifications come from the retained scaled preparation
and retained attachment. The cached coordinate reconstruction then cancels
the same original regular denominator; no square-one sign choice is used.
-/
def scaled_factor {cap : ReciprocalInnerInverse.Data curve collar} {point factor : Gaussian}
    (regular : Owners.Point cap point)
    (root : ReciprocalRootNames.ScaledRoot regular.certificate factor
      (HyperellipticReciprocal.polynomial curve) point)
    (attached : SquareRootChannelOwnership.Attachment root.certificate.value
      ((HyperellipticReciprocal.polynomial curve).eval point))
    (overlap : Overlap cap point attached.owner) (same : overlap.regular = regular) :
    NamedEquivalent overlap.coordinate.prepared.denominator.name (exact factor).name := by
  have originalRoot : overlap.regularRoot = regular.certificate :=
    overlap.regularRoot_eq.trans (congrArg Owners.Point.certificate same)
  have product : NamedEquivalent ((exact factor).mul overlap.regularRoot.value).name overlap.reciprocal.value.name := by
    rewrite [originalRoot, overlap.reciprocal_eq]
    exact root.prepared.equivalent.trans attached.equivalent
  exact overlap.coordinate.factor_agrees (exact factor) product

/-- The original scaled root, its once-attached owner and its exact same-point overlap retained together.

The nested dependent pairs use the existing three original owners. The
regular-model point and factor remain actual indices, and the final subtype
retains the complete original overlap construction.
-/
abbrev Scaled {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    (regular : Owners.Point cap point) (factor : Gaussian) :=
  (root : ReciprocalRootNames.ScaledRoot regular.certificate factor
    (HyperellipticReciprocal.polynomial curve) point) ×
  (attached : SquareRootChannelOwnership.Attachment root.certificate.value
    ((HyperellipticReciprocal.polynomial curve).eval point)) ×
    { value : Overlap cap point attached.owner // value = ofScaled regular root attached }

/-- Materialize one original scaled root, one actual attached owner and its same-regular-point overlap.

The polynomial identity concerns the actual reciprocal polynomial at the
actual point. The original scaled-root constructor computes its caches once;
the original overlap consumes those supplied owners and the supplied point.
-/
@[expose] def Scaled.build {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    (regular : Owners.Point cap point) (factor : Gaussian) (nonzero : factor ≠ 0)
    (identity : factor * factor * cap.polynomial.eval point =
      (HyperellipticReciprocal.polynomial curve).eval point) : Scaled regular factor :=
  let root := ReciprocalRootNames.ScaledRoot.build regular.certificate factor nonzero
    (HyperellipticReciprocal.polynomial curve) point identity
  let attached := ReciprocalRootOwners.attach root
  let overlap := ofScaled regular root attached
  ⟨root, attached, ⟨overlap, rfl⟩⟩

/-- Read the complete actual overlap from the supplied original scaled-root and attachment cache pair. -/
@[expose] def Scaled.overlap {cap : ReciprocalInnerInverse.Data curve collar} {point factor : Gaussian}
    {regular : Owners.Point cap point} (retained : Scaled regular factor) :
    Overlap cap point retained.2.1.owner := retained.2.2.val

/-- The materialized scaled overlap retains the complete supplied original regular-model point. -/
theorem Scaled.regular {cap : ReciprocalInnerInverse.Data curve collar} {point factor : Gaussian}
    {regular : Owners.Point cap point} (retained : Scaled regular factor) : retained.2.2.val.regular = regular := by
  rewrite [retained.2.2.property]
  rfl

/-- The materialized overlap's actual prepared coordinate agrees operationally with its original exact factor. -/
def Scaled.factor_agrees {cap : ReciprocalInnerInverse.Data curve collar} {point factor : Gaussian}
    {regular : Owners.Point cap point} (retained : Scaled regular factor) :
    NamedEquivalent retained.2.2.val.coordinate.prepared.denominator.name (exact factor).name := by
  exact scaled_factor regular retained.1 retained.2.1 retained.2.2.val (Scaled.regular retained)

/-- Attach the actual regular-model root as the positive even-degree reciprocal sheet.

The exact original reciprocal identity with origin order zero derives the
scaled-root parameter equation. The resulting coordinate agrees with one
by its actual attachment and reconstruction, not by its squared value alone.
-/
@[expose] def Scaled.even {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    (regular : Owners.Point cap point) (parity : HyperellipticReciprocal.originOrder curve = 0) : Scaled regular 1 :=
  Scaled.build regular 1 (by decide +kernel) (by
    rewrite [Data.Gaussian.Basic.one_mul, Data.Gaussian.Basic.one_mul]
    rewrite [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval, parity, pow_zero,
      Data.Gaussian.Basic.mul_one]
    rfl)

/-- Attach the negative of the same actual regular-model root as the other even-degree reciprocal sheet.

The original nonzero exact factor minus one fixes this signed occurrence.
The original scaled-root construction and attached owner retain that sign;
no independent square-root or pointwise sign selection is introduced.
-/
@[expose] def Scaled.evenNegative {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    (regular : Owners.Point cap point) (parity : HyperellipticReciprocal.originOrder curve = 0) : Scaled regular (-1) :=
  Scaled.build regular (-1) (by decide +kernel) (by
    have one : (-1 : Gaussian) * (-1) = 1 := by decide +kernel
    rewrite [one, Data.Gaussian.Basic.one_mul]
    rewrite [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval, parity, pow_zero,
      Data.Gaussian.Basic.mul_one]
    rfl)

/-- Attach the actual uniformizer times the same regular-model root in the odd-degree reciprocal chart.

The point is the actual squared uniformizer and its nonzero guard is
explicit. Origin order one derives the original reciprocal polynomial
identity; the resulting prepared coordinate agrees with that same supplied
uniformizer through the actual cached reconstruction and denominator guard.
-/
@[expose] def Scaled.odd {cap : ReciprocalInnerInverse.Data curve collar} (uniformizer : Gaussian)
    (nonzero : uniformizer ≠ 0) (regular : Owners.Point cap (uniformizer ^ 2))
    (parity : HyperellipticReciprocal.originOrder curve = 1) : Scaled regular uniformizer :=
  Scaled.build regular uniformizer nonzero (by
    rewrite [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval, parity, pow_one, pow_two]
    ring1)

/-- Multiplying the retained coordinate channel by the original regular root reconstructs the original reciprocal root.
-/
@[expose] def reconstruct {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Overlap cap point owner) :
    let root := overlap.attached.owner.certificate overlap.attached.owner.parameterNonzero
    NamedEquivalent (mul root.value overlap.regularRoot.value).name overlap.reciprocal.value.name
      := by
  let root := overlap.attached.owner.certificate overlap.attached.owner.parameterNonzero
  exact (coherentMul_respects root.value overlap.coordinate.prepared.denominator
    overlap.regularRoot.value overlap.regularRoot.value overlap.attached.equivalent.symm
      (Equivalence.NamedEquivalent.refl _)).trans overlap.coordinate.reconstruct

end Overlap

section InverseJet

open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

variable {cap : ReciprocalInnerInverse.Data curve collar}

/-- The square of a doubled original coherent channel is four times its same original square. -/
private def double_square (value : CoherentNamed) :
    NamedEquivalent ((value.add value).mul (value.add value)).name
      ((Coherence.exact 4).mul (value.mul value)).name := by
  let bindings : Fin 1 → CoherentNamed := fun _ => value
  let original := Normalized.atom bindings 0
  let four := Normalized.constant bindings 4
  let source := (original.add original).mul (original.add original)
  let target := four.mul (original.mul original)
  have same : source.form.terms = target.form.terms := by
    dsimp only [source, target, original, four]
    simp only [Normalized.mul_form,
      Normalized.add_form,
      Normalized.atom_form,
      Normalized.constant_form, -eq_self, -iff_self]
    decide +kernel
  exact source.compare target same

/-- The additional rationalizing factor at the actual same-model origin, using the retained finite jet value. -/
def originJetFactor (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) : CoherentNamed :=
  let value := origin.certificate.value
  let coefficient := Evaluation.eval jet.val 0
  value.add (value.mul (Coherence.exact coefficient))

/-- The actual origin factor agrees with twice the same original root by the retained jet's constant-one law. -/
def originJetFactor_double (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) :
    NamedEquivalent (originJetFactor origin jet).name
      (origin.certificate.value.add origin.certificate.value).name := by
  let value := origin.certificate.value
  have constant : Evaluation.eval jet.val 0 = 1 :=
    (Evaluation.eval_at_zero jet.val).trans jet.property.2.1
  unfold originJetFactor
  rewrite [constant]
  exact coherentAdd_respects value value (value.mul (Coherence.exact 1)) value
    (Equivalence.NamedEquivalent.refl _) (Arithmetic.Mul.coherentMul_one_right value)

/-- The same-model origin makes the rationalizing factor intrinsically division safe.

The supplied cache has constant one and the actual origin root is apart.
Its additional factor therefore squares to four times that original root
parameter. The original square-provenance preparation retains this same
factor; no independent root or successful regularity assumption is used.
-/
def originJetFactor_prepared (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) :
    Division.Prepared (originJetFactor origin jet) := by
  let value := origin.certificate.value
  let same := originJetFactor_double origin jet
  have squared : SquareIdentity (originJetFactor origin jet) (4 * cap.polynomial.eval 0) :=
    (coherentMul_respects (originJetFactor origin jet) (value.add value)
      (originJetFactor origin jet) (value.add value) same same).trans
      ((double_square value).trans
        ((coherentMul_respects (Coherence.exact 4) (Coherence.exact 4)
          (value.mul value) (Coherence.exact (cap.polynomial.eval 0))
          (Equivalence.NamedEquivalent.refl _) origin.certificate.square).trans
          (Coherent.Exact.Arithmetic.exact_mul 4 (cap.polynomial.eval 0))))
  exact SquareRootProvenance.prepared_of_square squared
    (Data.Gaussian.Field.mul_ne_zero_direct (by decide +kernel)
      (SquareRootChannelOwnership.parameter_nonzero origin.certificate))

section JetFactorComparison

open Purelib.Riemann.Normalization
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum (sampledSumApproximation_sample)

/-- A uniform squared spatial coefficient for the actual finite jet's rationalizing factor.

The coefficient retains the supplied root-derivative ceiling, the original
origin sampler's magnitude and both components of the same jet's Horner
cache. It bounds the actual factor's departure from its same-sheet origin.
-/
def jetFactorCoefficient
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {jet : InfinityCoefficients.Jet curve}
    (jetBounds : jet.Bounds collar.box) : Fraction.Rational :=
  let magnitude := 2 * (1 + jetBounds.val.value)
  let reference := (Name.Sampling.approximation origin.certificate.value.name).centerBound
  1024 * bounds.bound * (1 + 2 * magnitude) + 32 * (1 + 2 * reference) * jetBounds.val.slope

/-- The actual retained root, sampler and jet bounds give a nonnegative uniform factor coefficient. -/
theorem jetFactorCoefficient_nonnegative
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {jet : InfinityCoefficients.Jet curve}
    (jetBounds : jet.Bounds collar.box) : 0 ≤ jetFactorCoefficient bounds origin jetBounds := by
  let magnitude := 2 * (1 + jetBounds.val.value)
  let reference := (Name.Sampling.approximation origin.certificate.value.name).centerBound
  have magnitudeNonnegative : (0 : Fraction.Rational) ≤ magnitude :=
    Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) jetBounds.value_nonnegative)
  have referenceNonnegative : (0 : Fraction.Rational) ≤ reference :=
    (Name.Sampling.approximation origin.certificate.value.name).centerBound_nonneg
  have first : (0 : Fraction.Rational) ≤ 1024 * bounds.bound :=
    Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 1024) (by decide)) bounds.bound_nonnegative
  have second : (0 : Fraction.Rational) ≤ 1 + 2 * magnitude :=
    add_nonneg (by decide) (Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have third : (0 : Fraction.Rational) ≤ 32 * (1 + 2 * reference) :=
    Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 32) (by decide))
      (add_nonneg (by decide) (Order.Arithmetic.mul_nonneg_direct (by decide) referenceNonnegative))
  exact add_nonneg (Order.Arithmetic.mul_nonneg_direct first second)
    (Order.Arithmetic.mul_nonneg_direct third jetBounds.slope_nonnegative)

/-- Compare the actual nearby rationalizing factor with its guarded same-sheet origin factor.

Both root channels use the original retained cap model. The actual supplied
jet is evaluated once, and the same original jet's retained Horner cache
bounds its value and departure from one. Actual sum and product bridges
consume paid comparisons with the two requested starts. A finite scalar
request pays their combined error; no local regularity is assumed.
-/
def compareJetFactor
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {point : Gaussian} (regular : Owners.Point cap point)
    (jet : InfinityCoefficients.Jet curve) (jetBounds : jet.Bounds collar.box)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy)
    (reading : { value : Gaussian // value = Evaluation.eval jet.val point } :=
      ⟨Evaluation.eval jet.val point, rfl⟩)
    (cached : RootChannel.PreparationView regular.channel := ⟨regular.channel.preparation, rfl⟩) :
    let coefficient := reading.val
    Equivalence.Comparison
      (Name.Sampling.approximation
        (origin.certificate.value.add (cached.val.certificate.value.mul (Coherence.exact coefficient))).name)
      (Name.Sampling.approximation (originJetFactor origin jet).name) leftStart rightStart
      (jetFactorCoefficient bounds origin jetBounds * Norm.Basic.normSq point + accuracy) := by
  let initial := origin.certificate.value
  let value := cached.val.certificate.value
  let coefficient := reading.val
  let magnitude := (Name.Sampling.approximation (Coherence.exact coefficient).name).centerBound
  let reference := (Name.Sampling.approximation initial.name).centerBound
  let precision := SmallWidth.shrinkingWidth 22 accuracy
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 22) positive
  let firstBridge := (Sum.Bridge.coherentAdd_toSampled initial (value.mul (Coherence.exact coefficient))).compare
    leftStart 0 precision precisionPositive
  let lastBridge := ((Sum.Bridge.coherentAdd_toSampled initial initial).symm.trans
    (originJetFactor_double origin jet).symm).compare 0 rightStart precision precisionPositive
  let initialComparison := (Equivalence.NamedEquivalent.refl initial.name).compare 0 0 precision precisionPositive
  let scaledComparison := RootChannel.Preparation.compareScaled bounds origin.channel.preparation cached.val
    coefficient 0 0 precision precisionPositive
  let added := Sequence.Arithmetic.Sum.Congruence.pointwiseComparison initialComparison scaledComparison
    (sampledSumApproximation_sample initial.name (value.mul (Coherence.exact coefficient)).name)
    (sampledSumApproximation_sample initial.name initial.name)
  let combined := firstBridge.trans (added.trans lastBridge)
  have same : 2 * (precision + 2 *
      (2 * (precision + (128 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq (point - 0) +
        4 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + precision)) + precision)) =
      1024 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq point +
        32 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + 22 * precision := by
    rewrite [Data.Gaussian.Basic.sub_zero]
    ring1
  have magnitudeBound : magnitude ≤ 2 * (1 + jetBounds.val.value) := by
    change 2 * (1 + Norm.Basic.normSq coefficient) ≤ _
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 1)
        (by
          change Norm.Basic.normSq reading.val ≤ _
          rewrite [reading.property]
          exact jetBounds.value_le regular.channel.inside)) (by decide)
  have coefficientBound : Norm.Basic.normSq (coefficient - 1) ≤
      jetBounds.val.slope * Norm.Basic.normSq point := by
    change Norm.Basic.normSq (reading.val - 1) ≤ _
    rewrite [reading.property]
    exact jetBounds.increment_le origin.channel.inside regular.channel.inside
  have scaledMagnitude :
      1024 * bounds.bound * (1 + 2 * magnitude) ≤
        1024 * bounds.bound * (1 + 2 * (2 * (1 + jetBounds.val.value))) :=
    Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl 1)
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct magnitudeBound
        (by decide : (0 : Fraction.Rational) ≤ 2)))
    (Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 1024) (by decide))
      bounds.bound_nonnegative)
  have spatialBound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaledMagnitude
    (Norm.Basic.normSq_nonneg point)
  have weightNonnegative : (0 : Fraction.Rational) ≤ 32 * (1 + 2 * reference) :=
    Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 32) (by decide))
      (add_nonneg (by decide : (0 : Fraction.Rational) ≤ 1)
        (Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
          (Name.Sampling.approximation initial.name).centerBound_nonneg))
  have differenceBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound
    weightNonnegative
  exact combined.weaken _ (by
    change 2 * (precision + 2 *
      (2 * (precision + (128 * bounds.bound * (1 + 2 * magnitude) * Norm.Basic.normSq (point - 0) +
        4 * (1 + 2 * reference) * Norm.Basic.normSq (coefficient - 1) + precision)) + precision)) ≤ _
    rewrite [same]
    have bounded := Order.Arithmetic.add_le_add_direct spatialBound differenceBound
    have collected :
        1024 * bounds.bound * (1 + 2 * (2 * (1 + jetBounds.val.value))) * Norm.Basic.normSq point +
          32 * (1 + 2 * reference) * (jetBounds.val.slope * Norm.Basic.normSq point) =
            jetFactorCoefficient bounds origin jetBounds * Norm.Basic.normSq point := by
      unfold jetFactorCoefficient
      ring1
    rewrite [collected] at bounded
    exact (Order.Arithmetic.add_le_add_direct bounded (Fraction.Order.Basic.le_refl _)).trans
      (Order.Arithmetic.add_lt_add_left_direct paid _).le)

/-- A positive local coordinate radius paid from the actual origin factor's retained apartness.

The radius is bounded by the original collar radius. Its second finite
minimum pays the squared spatial factor comparison against one eighth
of the actual prepared origin's lower bound, leaving explicit bridge error.
-/
def jetFactorRadius
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {jet : InfinityCoefficients.Jet curve}
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (originJetFactor origin jet)) : Fraction.Rational :=
  min (ReciprocalExteriorCollar.innerRadius curve)
    (SmallWidth.shrinkingWidth (4 * jetFactorCoefficient bounds origin jetBounds)
      (anchor.apart.certificate.lowerSq / 8))

/-- The radius computed from the actual retained positive lower bound and finite caches is strictly positive. -/
theorem jetFactorRadius_positive
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {jet : InfinityCoefficients.Jet curve}
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (originJetFactor origin jet)) :
    0 < jetFactorRadius bounds origin jetBounds anchor :=
  Fraction.Order.Basic.lt_min (ReciprocalExteriorCollar.innerRadius_positive curve)
    (SmallWidth.shrinkingWidth_pos
      (Order.Arithmetic.mul_nonneg_direct (by decide)
        (jetFactorCoefficient_nonnegative bounds origin jetBounds))
      (Fraction.Order.Field.div_pos_direct anchor.apart.certificate.positive (by decide)))

/-- The actual positive local square is contained in the same original reciprocal collar box. -/
theorem jetFactorRadius_contains
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {jet : InfinityCoefficients.Jet curve}
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (originJetFactor origin jet))
    {point : Gaussian}
    (inside : (Geometry.Rational.Box.symmetric (jetFactorRadius bounds origin jetBounds anchor)
      (jetFactorRadius_positive bounds origin jetBounds anchor).le).Contains point) :
    collar.box.Contains point := by
  let radius := jetFactorRadius bounds origin jetBounds anchor
  have radiusLe : radius ≤ ReciprocalExteriorCollar.innerRadius curve := Fraction.Order.Basic.min_le_left _ _
  have negative := Order.Arithmetic.neg_le_neg_direct radiusLe
  rewrite [collar.box_eq]
  exact ⟨negative.trans inside.1, inside.2.1.trans radiusLe,
    negative.trans inside.2.2.1, inside.2.2.2.trans radiusLe⟩

/-- Prepare the actual nearby jet factor from the computed local square and original same-sheet origin.

The supplied regular root, original jet, actual Horner cache and guarded
origin factor are retained. The computed radius derives a successful finite
comparison below the original anchor's quarter lower bound. The original
comparison-based preparation consumes those exact paid observations; there
is no successful search or local regularity premise.
-/
def prepareJetFactor
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {point : Gaussian} (regular : Owners.Point cap point)
    (jet : InfinityCoefficients.Jet curve) (jetBounds : jet.Bounds collar.box)
    (anchor : Division.Prepared (originJetFactor origin jet))
    (inside : (Geometry.Rational.Box.symmetric (jetFactorRadius bounds origin jetBounds anchor)
      (jetFactorRadius_positive bounds origin jetBounds anchor).le).Contains point)
    (reading : { value : Gaussian // value = Evaluation.eval jet.val point } :=
      ⟨Evaluation.eval jet.val point, rfl⟩)
    (cached : RootChannel.PreparationView regular.channel := ⟨regular.channel.preparation, rfl⟩) :
    let coefficient := reading.val
    Division.Prepared (origin.certificate.value.add
      (cached.val.certificate.value.mul (Coherence.exact coefficient))) := by
  let channel := origin.certificate.value.add
    (cached.val.certificate.value.mul (Coherence.exact reading.val))
  let coefficient := jetFactorCoefficient bounds origin jetBounds
  let radius := jetFactorRadius bounds origin jetBounds anchor
  let lower := anchor.apart.certificate.lowerSq
  let accuracy := lower / 32
  have accuracyPositive : 0 < accuracy :=
    Fraction.Order.Field.div_pos_direct anchor.apart.certificate.positive
      (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide))
  let factorComparison := compareJetFactor bounds origin regular jet jetBounds 0 0 accuracy accuracyPositive
    reading cached
  let anchorComparison := anchor.equivalent.compare 0 0 accuracy accuracyPositive
  let combined := factorComparison.trans anchorComparison
  have coefficientNonnegative : 0 ≤ coefficient := jetFactorCoefficient_nonnegative bounds origin jetBounds
  have normUpper : Norm.Basic.normSq point ≤ 2 * radius ^ 2 :=
    Geometry.Rational.Box.normSq_le_symmetric
      (jetFactorRadius_positive bounds origin jetBounds anchor).le inside
  have radiusPositive : 0 < radius := jetFactorRadius_positive bounds origin jetBounds anchor
  let width := SmallWidth.shrinkingWidth (4 * coefficient) (lower / 8)
  have radiusLe : radius ≤ width := Fraction.Order.Basic.min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ width ^ 2 := by
    rewrite [pow_two, pow_two]
    exact Order.Arithmetic.mul_le_mul_direct radiusLe radiusLe radiusPositive.le
      (radiusPositive.le.trans radiusLe)
  have weighted : coefficient * Norm.Basic.normSq point ≤ 2 * coefficient * width ^ 2 := by
    have small := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (normUpper.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquareLe (by decide)))
      coefficientNonnegative
    exact small.trans_eq (by ring1)
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
    (Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) coefficientNonnegative)
    (Fraction.Order.Field.div_pos_direct anchor.apart.certificate.positive (by decide : (0 : Fraction.Rational) < 8))
  have close : 2 * (coefficient * Norm.Basic.normSq point + accuracy + accuracy) < lower / 4 := by
    calc
      _ = 2 * (coefficient * Norm.Basic.normSq point) + 4 * accuracy := by ring1
      _ ≤ 4 * coefficient * width ^ 2 + 4 * accuracy := by
        have spatial := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weighted
          (by decide : (0 : Fraction.Rational) ≤ 2)
        have collected : 2 * (2 * coefficient * width ^ 2) = 4 * coefficient * width ^ 2 := by ring1
        rewrite [collected] at spatial
        exact Order.Arithmetic.add_le_add_direct spatial (Fraction.Order.Basic.le_refl _)
      _ < lower / 8 + 4 * accuracy :=
        Order.Arithmetic.add_lt_add_right_direct paid _
      _ = lower / 4 := by
        dsimp only [accuracy]
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
        have fourThirtySeconds :
            (4 : Fraction.Rational) * (32 : Fraction.Rational)⁻¹ = 1 / 8 := by
          decide +kernel
        calc
          lower * (8 : Fraction.Rational)⁻¹ + 4 * (lower * (32 : Fraction.Rational)⁻¹) =
              lower * ((8 : Fraction.Rational)⁻¹ + 4 * (32 : Fraction.Rational)⁻¹) := by ring1
          _ = lower * (4 : Fraction.Rational)⁻¹ := by
            rewrite [fourThirtySeconds]
            have equal : (8 : Fraction.Rational)⁻¹ + 1 / 8 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
            rewrite [equal]
            rfl
  exact Division.Prepared.ofComparison channel anchor.denominator anchor.apart
    (combined.weaken (lower / 4) close.le)

/-- The actual jet-factor preparation retains the same fixed origin-anchor lower bound at every nearby point. -/
private theorem prepareJetFactor_lowerSq
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {point : Gaussian} (regular : Owners.Point cap point)
    (jet : InfinityCoefficients.Jet curve) (jetBounds : jet.Bounds collar.box)
    (anchor : Division.Prepared (originJetFactor origin jet))
    (inside : (Geometry.Rational.Box.symmetric (jetFactorRadius bounds origin jetBounds anchor)
      (jetFactorRadius_positive bounds origin jetBounds anchor).le).Contains point)
    (reading : { value : Gaussian // value = Evaluation.eval jet.val point } :=
      ⟨Evaluation.eval jet.val point, rfl⟩)
    (cached : RootChannel.PreparationView regular.channel := ⟨regular.channel.preparation, rfl⟩) :
    (prepareJetFactor bounds origin regular jet jetBounds anchor inside reading cached).apart.certificate.lowerSq =
      (anchor.apart.certificate.lowerSq / 4) / 8 := by
  unfold prepareJetFactor
  exact Division.Prepared.ofComparison_lowerSq _ _ _ _

end JetFactorComparison

namespace Overlap

variable {point : Gaussian}
  {reciprocalOwner : SquareRootContinuationChain.Owner
    ((HyperellipticReciprocal.polynomial curve).eval point)}

/-- Recover the affine presentation by scaling the actual retained reciprocal root occurrence.

The original reciprocal chart identity proves the exact target equation at
`1/w`. The nonzero coordinate supplies the original scale guard. The original
ScaledRoot constructor prepares that same scaled source and retains its actual
coefficient/inverse caches; no independent root or sheet is selected.
-/
def affineRoot (overlap : Overlap cap point reciprocalOwner) (nonzero : point ≠ 0) :
    ReciprocalRootNames.ScaledRoot overlap.reciprocal ((point⁻¹) ^ (genus + 1))
      curve.polynomial point⁻¹ :=
  ReciprocalRootNames.ScaledRoot.affine overlap.reciprocal nonzero

end Overlap

section LocalJetFactors

open Purelib.Riemann.Normalization
open Purelib.Data.Rat
open Purelib.Data.Gaussian

/-- A positive width paying the same-model root displacement against the actual origin lower bound. -/
private def rootGuardWidth
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) : Fraction.Rational :=
  SmallWidth.shrinkingWidth (64 * bounds.bound) (origin.certificate.apart.certificate.lowerSq / 8)

/-- The width selected from the actual origin guard and retained root derivative cache is positive. -/
private theorem rootGuardWidth_positive
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) : 0 < rootGuardWidth bounds origin :=
  SmallWidth.shrinkingWidth_pos
    (Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 64) (by decide)) bounds.bound_nonnegative)
    (Fraction.Order.Field.div_pos_direct origin.certificate.apart.certificate.positive (by decide))

/-- Prepare the actual nearby same-model root using its internally paid comparison with the original origin.

The retained root comparison and finite symmetric-square bound give the
anchor quarter budget. The returned original preparation carries the fixed
lower bound needed for uniform quotient estimates, independently of the
nearby point's original apartness lower bound.
-/
private def prepareRootNearOrigin
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (origin : Owners.Point cap 0) {point : Gaussian} (regular : Owners.Point cap point)
    (inside : (Geometry.Rational.Box.symmetric (rootGuardWidth bounds origin)
      (rootGuardWidth_positive bounds origin).le).Contains point) :
    { prepared : Division.Prepared regular.certificate.value //
      prepared.apart.certificate.lowerSq = (origin.certificate.apart.certificate.lowerSq / 4) / 8 } := by
  let lower := origin.certificate.apart.certificate.lowerSq
  let accuracy := lower / 8
  have accuracyPositive : 0 < accuracy :=
    Fraction.Order.Field.div_pos_direct origin.certificate.apart.certificate.positive (by decide)
  let compared := origin.channel.comparePoints bounds regular.channel 0 0 accuracy accuracyPositive
  have normBound := Geometry.Rational.Box.normSq_le_symmetric (rootGuardWidth_positive bounds origin).le inside
  have coefficientNonnegative : 0 ≤ 32 * bounds.bound :=
    Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 32) (by decide)) bounds.bound_nonnegative
  have spatial : 32 * bounds.bound * Norm.Basic.normSq point < lower / 8 := by
    have paid : 64 * bounds.bound * rootGuardWidth bounds origin ^ 2 < lower / 8 :=
      SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
      (Order.Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 64) (by decide))
        bounds.bound_nonnegative)
      (Fraction.Order.Field.div_pos_direct origin.certificate.apart.certificate.positive
        (by decide : (0 : Fraction.Rational) < 8))
    have weighted := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normBound coefficientNonnegative
    have collected : 32 * bounds.bound * (2 * rootGuardWidth bounds origin ^ 2) =
        64 * bounds.bound * rootGuardWidth bounds origin ^ 2 := by ring1
    rewrite [collected] at weighted
    exact weighted.trans_lt paid
  have close : 32 * bounds.bound * Data.Gaussian.Basic.Canonical.normSq (point - 0) + accuracy < lower / 4 := by
    rewrite [Data.Gaussian.Basic.sub_zero]
    rewrite [← Norm.Basic.normSq_eq_canonical]
    calc
      _ < lower / 8 + accuracy := Order.Arithmetic.add_lt_add_right_direct spatial accuracy
      _ = lower / 4 := by
        dsimp only [accuracy]
        rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
        calc
          _ = lower * ((8 : Fraction.Rational)⁻¹ + (8 : Fraction.Rational)⁻¹) := by ring1
          _ = _ := by
            rewrite [show (8 : Fraction.Rational)⁻¹ + (8 : Fraction.Rational)⁻¹ = (4 : Fraction.Rational)⁻¹ by
              decide +kernel]
            rfl
  let paid := compared.weaken (lower / 4) close.le
  exact ⟨Division.Prepared.ofComparison regular.certificate.value origin.certificate.value
      origin.certificate.apart paid,
    Division.Prepared.ofComparison_lowerSq regular.certificate.value origin.certificate.value
      origin.certificate.apart paid⟩

/-- The original positive factor square and guarded handler on an actual retained numerical preparation.

The original cap, origin and finite jet index the same factor operation.
Each handler consumes its supplied whole numerical preparation directly;
its original certificate is the factor's actual root operand. The full
Point-indexed view retains the original nominal parent separately.
-/
abbrev JetFactors (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) :=
  Sigma fun radius : { value : Fraction.Rational // 0 < value } =>
    (point : Gaussian) → (inCollar : collar.box.Contains point) →
      (cached : RootChannel.Preparation cap.model cap.model_small point inCollar) →
      (reading : { value : Gaussian // value = Evaluation.eval jet.val point }) →
      (Geometry.Rational.Box.symmetric radius.val radius.property.le).Contains point →
        Division.Prepared (origin.certificate.value.add
          (cached.certificate.value.mul (Coherence.exact reading.val)))

namespace JetFactors

/-- The complete original Point-indexed pair is an exact view of the same supplied numerical factor operation.

The original regular Point, supplied certificate and numerical cache keep
their nominal parent equalities. Only the dependent factor index is
transported; the same saved numerical handler is consumed.
-/
def full (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve) (setup : JetFactors origin jet) :
    Sigma fun radius : { value : Fraction.Rational // 0 < value } =>
      (point : Gaussian) → (regular : Owners.Point cap point) →
        (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate }) →
        (reading : { value : Gaussian // value = Evaluation.eval jet.val point }) →
        (Geometry.Rational.Box.symmetric radius.val radius.property.le).Contains point →
        (cached : optParam (RootChannel.PreparationView regular.channel)
          ⟨regular.channel.preparation, rfl⟩) →
          Division.Prepared (origin.certificate.value.add
            (certificate.val.value.mul (Coherence.exact reading.val))) := by
  refine ⟨setup.1, ?_⟩
  intro point regular certificate reading inside cached
  let prepared := setup.2 point regular.channel.inside cached.val reading inside
  have certificateEq : cached.val.certificate = regular.certificate :=
    congrArg (fun value : RootChannel.Preparation cap.model regular.channel.small point regular.channel.inside =>
      value.certificate) cached.property
  have same : origin.certificate.value.add (certificate.val.value.mul (Coherence.exact reading.val)) =
      origin.certificate.value.add (cached.val.certificate.value.mul (Coherence.exact reading.val)) :=
    congrArg (fun certificate : Certificate (cap.polynomial.eval point) =>
      origin.certificate.value.add (certificate.value.mul (Coherence.exact reading.val)))
      (certificate.property.trans certificateEq.symm)
  exact Eq.mp (congrArg Division.Prepared same.symm) prepared

end JetFactors

/-- Compute a positive square and retain its guarded handler on the actual same-model numerical preparation.

The original model derivative bounds, numerator-product bounds, actual jet
Horner pair and actual origin preparation are constructed once outside the
point handler. Its supplied whole numerical preparation retains the exact
sample, apart and square caches. The Point is needed only as a nominal
proof index of the original factor operation, so direct execution does not
construct its winding attachment. The complete original Point/certificate
interface is the exact full view of this same retained handler.
-/
@[inline] def prepareJetFactors (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model :=
      InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial :=
      InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial)
    (jetBounds : jet.Bounds collar.box := jet.bounds collar.box)
    (anchor : Division.Prepared (originJetFactor origin jet) := originJetFactor_prepared origin jet) :
    JetFactors origin jet := by
  let radius := jetFactorRadius bounds origin jetBounds anchor
  have positive := jetFactorRadius_positive bounds origin jetBounds anchor
  refine ⟨⟨radius, positive⟩, ?_⟩
  intro point inCollar cached reading inside
  let regular := Owners.Point.build cap point inCollar cached
  have preparationEq : cached = regular.channel.preparation :=
    (RootChannel.build_preparation cap.model cap.model_small point inCollar cached).symm
  exact prepareJetFactor bounds origin regular jet jetBounds anchor inside reading ⟨cached, preparationEq⟩

namespace JetFactors

/-- The same supplied whole factor setup with its exact original producer and all actual numerical cache parents. -/
@[expose] def View (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (originJetFactor origin jet)) :=
  { value : JetFactors origin jet // value = prepareJetFactors origin jet root bounds jetBounds anchor }

end JetFactors

/-- A uniform finite tail bound on the same original guarded inverse-jet error throughout a retained square.

Each request retains its actual Point, stored certificate view, coefficient
and residual caches, supplied original factor preparation and exact original
error program. Its result is one bounded Comparison with zero, including
independent starts and requested accuracy; it asserts no equivalence to zero.
The default output is the supplied error itself. The same exact function
view also retains the actual coordinate-scaled error in a decay estimate.
-/
abbrev JetErrorBound (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (radius : Fraction.Rational) (nonnegative : 0 ≤ radius) (upper : Fraction.Rational)
    (output : Gaussian → CoherentNamed → CoherentNamed := fun _ error => error) :=
  (point : Gaussian) → (regular : Owners.Point cap point) →
    (certificate : { value : Certificate (cap.polynomial.eval point) // value = regular.certificate }) →
    (coefficientCache : { value : Gaussian // value = Evaluation.eval jet.val point }) →
    (residualCache : { value : Gaussian // value = Evaluation.eval remainder.val point }) →
    (factor : Division.Prepared (origin.certificate.value.add
      (certificate.val.value.mul (Coherence.exact coefficientCache.val)))) →
    (retained : Owners.Point.JetRemainder regular certificate origin jet remainder
      coefficientCache residualCache factor) →
    (Geometry.Rational.Box.symmetric radius nonnegative).Contains point →
    (leftStart rightStart : Nat) → (accuracy : Fraction.Rational) → 0 < accuracy →
      Equivalence.Comparison (Sampling.approximation (output point retained.error).name)
        (Sampling.approximation (Coherence.exact 0).name) leftStart rightStart (upper + accuracy)

/-- Compute a positive neighborhood and uniform finite tail bound for the actual guarded inverse-jet error.

Original root derivative bounds, jet bounds, residual-polynomial bounds and
origin preparation are computed once. Two internally paid comparisons
prepare the actual nearby root and its jet factor with fixed anchor lower
bounds. Quotient congruence compares the supplied actual error with these
presentations. The retained residual bound then pays one bounded Comparison,
without assuming local regularity or turning boundedness into vanishing.
-/
def prepareJetErrorBound (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val) :
    (radius : { value : Fraction.Rational // 0 < value }) ×
      (upper : { value : Fraction.Rational // 0 < value }) ×
        JetErrorBound origin jet remainder radius.val radius.property.le upper.val := by
  let root := InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model
  let bounds := InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial
  let jetBounds := jet.bounds collar.box
  let anchor := originJetFactor_prepared origin jet
  let factors := JetFactors.full origin jet (prepareJetFactors origin jet root bounds jetBounds anchor)
  let radius := min factors.1.val (rootGuardWidth bounds origin)
  have radiusPositive : 0 < radius := Fraction.Order.Basic.lt_min factors.1.property
    (rootGuardWidth_positive bounds origin)
  let residualPolynomial := Polynomial.Ascending.Gaussian.Dense.Evaluation.toDense remainder.val
  let residualBounds := Polynomial.Dense.Gaussian.Bounds.Box.denseHornerNormBounds residualPolynomial collar.box
  let residualUpper := residualBounds.value
  have residualNonnegative : 0 ≤ residualUpper :=
    (Polynomial.Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg residualPolynomial collar.box).1
  let factorLower := (anchor.apart.certificate.lowerSq / 4) / 8
  let rootLower := (origin.certificate.apart.certificate.lowerSq / 4) / 8
  let originLower := origin.certificate.apart.certificate.lowerSq
  have factorPositive : 0 < factorLower := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct anchor.apart.certificate.positive (by decide)) (by decide)
  have rootPositive : 0 < rootLower := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct origin.certificate.apart.certificate.positive (by decide)) (by decide)
  have originPositive : 0 < originLower := origin.certificate.apart.certificate.positive
  let processUpper := ((residualUpper / factorLower) / rootLower) / originLower
  have processNonnegative : 0 ≤ processUpper := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Field.div_nonneg_direct residualNonnegative factorPositive.le) rootPositive.le) originPositive.le
  let sampleUpper := 2 * (1 + processUpper)
  have samplePositive : 0 < sampleUpper := Order.Arithmetic.mul_pos_direct (by decide)
    (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) processNonnegative)
  let upper := 2 * sampleUpper
  have upperPositive : 0 < upper := Order.Arithmetic.mul_pos_direct (by decide) samplePositive
  refine ⟨⟨radius, radiusPositive⟩, ⟨upper, upperPositive⟩, ?_⟩
  intro point regular certificate coefficientCache residualCache factor retained inside
    leftStart rightStart accuracy positive
  rcases certificate with ⟨cached, same⟩
  cases same
  have factorRadius : radius ≤ factors.1.val := Fraction.Order.Basic.min_le_left _ _
  have rootRadius : radius ≤ rootGuardWidth bounds origin := Fraction.Order.Basic.min_le_right _ _
  have factorInside : (Geometry.Rational.Box.symmetric factors.1.val factors.1.property.le).Contains point :=
    (Geometry.Rational.Box.symmetric_refines radiusPositive.le factors.1.property.le factorRadius).contains inside
  have rootInside : (Geometry.Rational.Box.symmetric (rootGuardWidth bounds origin)
      (rootGuardWidth_positive bounds origin).le).Contains point :=
    (Geometry.Rational.Box.symmetric_refines radiusPositive.le (rootGuardWidth_positive bounds origin).le
      rootRadius).contains inside
  let preparedFactor := factors.2 point regular ⟨regular.certificate, rfl⟩ coefficientCache factorInside
  let preparedRoot := prepareRootNearOrigin bounds origin regular rootInside
  have factorReadback : preparedFactor.apart.certificate.lowerSq = factorLower := by
    dsimp only [preparedFactor, factors, JetFactors.full, prepareJetFactors]
    exact prepareJetFactor_lowerSq bounds origin regular jet jetBounds anchor factorInside coefficientCache
  have rootReadback : preparedRoot.val.apart.certificate.lowerSq = rootLower := preparedRoot.property
  have inCollar : collar.box.Contains point :=
    jetFactorRadius_contains bounds origin jetBounds anchor factorInside
  have numeratorBound : Norm.Basic.normSq residualCache.val ≤ residualUpper := by
    rewrite [residualCache.property]
    have estimate := Polynomial.Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
      residualPolynomial inCollar
    rewrite [Polynomial.Ascending.Gaussian.Dense.Evaluation.toDense_eval] at estimate
    exact estimate
  let firstBounded := div retained.residual preparedFactor.denominator preparedFactor.apart
  let secondBounded := div firstBounded preparedRoot.val.denominator preparedRoot.val.apart
  let boundedError := div secondBounded origin.certificate.value origin.certificate.apart
  have originalFirst := Coherent.Division.Equivalence.coherentDiv_respects
    retained.residual retained.residual
    factor.denominator preparedFactor.denominator factor.apart preparedFactor.apart
    (Equivalence.NamedEquivalent.refl _) (factor.equivalent.symm.trans preparedFactor.equivalent)
  have firstEquivalent : NamedEquivalent retained.factorQuotient.name firstBounded.name :=
    Equivalence.NamedEquivalent.transport
      (congrArg (fun value : CoherentNamed => value.name) retained.factorQuotient_eq.symm) rfl originalFirst
  have originalSecond := Coherent.Division.Equivalence.coherentDiv_respects retained.factorQuotient firstBounded
    regular.certificate.value preparedRoot.val.denominator regular.certificate.apart preparedRoot.val.apart
    firstEquivalent preparedRoot.val.equivalent
  have secondEquivalent : NamedEquivalent retained.rootQuotient.name secondBounded.name :=
    Equivalence.NamedEquivalent.transport
      (congrArg (fun value : CoherentNamed => value.name) retained.rootQuotient_eq.symm) rfl originalSecond
  have originalThird := Coherent.Division.Equivalence.coherentDiv_respects retained.rootQuotient secondBounded
    origin.certificate.value origin.certificate.value origin.certificate.apart origin.certificate.apart
    secondEquivalent (Equivalence.NamedEquivalent.refl _)
  have equivalent : NamedEquivalent retained.error.name boundedError.name :=
    Equivalence.NamedEquivalent.transport
      (congrArg (fun value : CoherentNamed => value.name) retained.error_eq.symm) rfl originalThird
  have processBound : boundedError.name.process.centerBound ≤ processUpper := by
    change ((retained.residual.name.process.centerBound / preparedFactor.apart.certificate.lowerSq) /
      preparedRoot.val.apart.certificate.lowerSq) / originLower ≤ processUpper
    rewrite [retained.residual_eq]
    change ((Norm.Basic.normSq residualCache.val / preparedFactor.apart.certificate.lowerSq) /
      preparedRoot.val.apart.certificate.lowerSq) / originLower ≤ processUpper
    rewrite [factorReadback, rootReadback]
    dsimp only [processUpper]
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
    exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorBound
          (Fraction.Order.Field.inv_pos_direct factorPositive).le)
        (Fraction.Order.Field.inv_pos_direct rootPositive).le)
      (Fraction.Order.Field.inv_pos_direct originPositive).le
  have sampleBound : ∀ index,
      Norm.Basic.normSq ((Sampling.approximation boundedError.name).sample index) ≤ sampleUpper := by
    intro index
    apply ((Sampling.approximation boundedError.name).sample_bounded index).trans
    change 2 * (1 + boundedError.name.process.centerBound) ≤ 2 * (1 + processUpper)
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) processBound) (by decide)
  have halfPositive : 0 < accuracy / 2 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let comparison := Equivalence.Equivalent.compare_zero_of_bound equivalent sampleUpper sampleBound leftStart rightStart
    (accuracy / 2) halfPositive
  have target : 2 * (accuracy / 2 + sampleUpper) = upper + accuracy := by
    dsimp only [upper]
    rewrite [Fraction.Field.div_eq_mul_inv_direct]
    have inverse : (2 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹ = 1 := by decide +kernel
    calc
      _ = (2 * (2 : Fraction.Rational)⁻¹) * accuracy + 2 * sampleUpper := by ring1
      _ = _ := by rewrite [inverse]; ring1
  exact comparison.weaken _ target.le

/-- Pay a requested uniform coordinate-scaled inverse-jet error bound on an internally computed square.

The original finite error-bound producer is retained once. Its positive
ceiling and the requested tolerance determine a smaller positive square.
The actual positive coordinate power supplies the vanishing factor, and
original multiplication comparisons pay the independently started samples.
The result is one requested neighborhood estimate, never an equivalence of
the nonzero-point remainder to zero.
-/
def prepareJetDecay (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (target : Fraction.Rational) (positive : 0 < target) :
    (radius : { value : Fraction.Rational // 0 < value }) ×
      JetErrorBound origin jet remainder radius.val radius.property.le (target / 2)
        (fun point error => (Coherence.exact (point ^ (genus + 1))).mul error) := by
  let prepared := prepareJetErrorBound origin jet remainder
  let upper := prepared.2.1.val
  have upperPositive : 0 < upper := prepared.2.1.property
  have inputPositive : 0 < upper + 1 :=
    Order.Arithmetic.add_pos_of_pos_of_nonneg_direct upperPositive (by decide)
  have coefficientNonnegative : 0 ≤ 8 * (upper + 1) :=
    Order.Arithmetic.mul_nonneg_direct (by decide) inputPositive.le
  have halfPositive : 0 < target / 2 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let width := SmallWidth.shrinkingWidth (8 * (upper + 1)) (target / 2)
  have widthPositive : 0 < width := SmallWidth.shrinkingWidth_pos coefficientNonnegative halfPositive
  let radius := min prepared.1.val (min (1 / 2) width)
  have radiusPositive : 0 < radius := Fraction.Order.Basic.lt_min prepared.1.property
    (Fraction.Order.Basic.lt_min (by decide) widthPositive)
  have radiusBase : radius ≤ prepared.1.val := Fraction.Order.Basic.min_le_left _ _
  have radiusOther : radius ≤ min (1 / 2) width := Fraction.Order.Basic.min_le_right _ _
  have radiusHalf : radius ≤ 1 / 2 := radiusOther.trans (Fraction.Order.Basic.min_le_left _ _)
  have radiusWidth : radius ≤ width := radiusOther.trans (Fraction.Order.Basic.min_le_right _ _)
  refine ⟨⟨radius, radiusPositive⟩, ?_⟩
  intro point regular certificate coefficientCache residualCache factor retained inside leftStart rightStart
    accuracy accurate
  have insideBase :=
    (Geometry.Rational.Box.symmetric_refines radiusPositive.le prepared.1.property.le radiusBase).contains inside
  let errorComparison := prepared.2.2 point regular certificate coefficientCache residualCache factor retained
    insideBase 0 rightStart 1 (by decide)
  let compared := Congruence.compare_exact_mul_zero (point ^ (genus + 1)) retained.error errorComparison
    leftStart accuracy accurate
  have normBound := Geometry.Rational.Box.normSq_le_symmetric radiusPositive.le inside
  have radiusSquare := Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusHalf 2
  have normUnit : Norm.Basic.normSq point ≤ 1 := by
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusSquare
      (show (0 : Fraction.Rational) ≤ 2 by decide)
    exact normBound.trans (scaled.trans (by decide : (2 : Fraction.Rational) * (1 / 2) ^ 2 ≤ 1))
  have powerNorm : Norm.Basic.normSq (point ^ (genus + 1)) ≤ Norm.Basic.normSq point := by
    rewrite [Norm.Power.normSq_pow]
    exact Fraction.Power.Order.pow_le_self_of_nonnegative_le_one (Norm.Basic.normSq_nonneg point) normUnit
      (Nat.zero_lt_succ genus)
  have weightedNorm := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (powerNorm.trans normBound)
    (Order.Arithmetic.mul_nonneg_direct (show (0 : Fraction.Rational) ≤ 4 by decide) inputPositive.le)
  have radiusPaid := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt coefficientNonnegative halfPositive
  have radiusSquared := Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusWidth 2
  have scaledRadius := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    radiusSquared coefficientNonnegative
  have collected : 4 * (upper + 1) * (2 * radius ^ 2) = 8 * (upper + 1) * radius ^ 2 := by ring1
  have paid : 4 * (Norm.Basic.normSq (point ^ (genus + 1)) * (upper + 1)) ≤ target / 2 := by
    have rearranged : 4 * (Norm.Basic.normSq (point ^ (genus + 1)) * (upper + 1)) =
        4 * (upper + 1) * Norm.Basic.normSq (point ^ (genus + 1)) := by ring1
    rewrite [rearranged]
    exact weightedNorm.trans (collected.le.trans (scaledRadius.trans radiusPaid.le))
  exact compared.weaken _ (Order.Arithmetic.add_le_add_right_direct paid accuracy)

end LocalJetFactors

end InverseJet

set_option genInjectivity false in
/-- An affine owner supplies the entire overlap: scaling, its attached reciprocal owner, the actual collar crossing and
the cap coordinate.

The indexed fields retain the supplied owners, channels and exact cached
data. Their identities bind each displayed field to those same inputs. -/
structure BoundaryOverlap (cap : ReciprocalInnerInverse.Data curve collar)
    (fiber : ReciprocalCollarTransport.Fiber collar source)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) where
  /-- The winding owner attached to the reciprocal scaling of the exact original affine boundary root. -/ attached :
    SquareRootChannelOwnership.Attachment
    (ReciprocalRootNames.ofBoundaryOwner curve source fiber.boundary original).prepared.denominator
    ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)
  /-- The retained trace of the actual collar route from the attached reciprocal owner. -/ collarTrace :
    PreparedPathTrace.TracedPath fiber.route.path attached.owner
  /-- The coordinate comparison at the actual retained collar-trace finishing owner. -/ coordinates :
    Overlap cap (collar.sidePoint source)
    collarTrace.finishOwner

constructive_injectivity BoundaryOverlap

/-- Retain the original affine-to-reciprocal crossing and construct cap coordinates from its actual finishing owner. -/
@[expose] def BoundaryOverlap.build (cap : ReciprocalInnerInverse.Data curve collar)
    (fiber : ReciprocalCollarTransport.Fiber collar source)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
      BoundaryOverlap cap fiber original :=
  let crossed := ReciprocalRootOwners.cross fiber original
  ⟨crossed.1, crossed.2, Overlap.build cap (collar.sidePoint
    source) (by
    rw [collar.box_eq, collar.sidePoint_eq]
    exact ReciprocalExteriorCollar.chord_contains curve fiber.boundary.1) crossed.2.finishOwner⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
