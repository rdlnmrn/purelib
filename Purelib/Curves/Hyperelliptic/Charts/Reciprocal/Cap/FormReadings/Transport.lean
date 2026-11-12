module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Comparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
public import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.Transport
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Semiring.Normalization
import Purelib.Tactic.Ring

/-! # Numerical form observations of an actual retained signed cap sheet

The original scaled-root and attached-owner cache supplies the numerical
reciprocal root literally. Its own affine scale feeds the complete form
observation. The even negative-sheet comparison relates that same numerical
coefficient to the original attached chart's supplied affine-root cache.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.InverseModelRootChannels
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence.Observation (Request)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.Field
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}

namespace Preparation

/-- Prepare the actual supplied signed reciprocal root without constructing a numerical root or winding attachment.

The same retained model point supplies its complete numerical preparation.
The original scaled root is passed literally to the optional scale input;
only its guarded affine scaling is constructed by the original factory.
-/
def ofScaled (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter)) {factor : Canonical}
    (retained : RootCoordinates.Overlap.Scaled regular factor) :
    Preparation cap parameter regular.channel.inside factor :=
  prepare cap parameter nonzero regular.channel.inside regular.channel.preparation (some ⟨factor, retained.1⟩)

/-- The complete signed numerical preparation retains both supplied original caches and its actual affine scale. -/
theorem ofScaled_eq (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter)) {factor : Canonical}
    (retained : RootCoordinates.Overlap.Scaled regular factor) :
    ofScaled parameter nonzero regular retained =
      ⟨regular.channel.preparation, retained.1, ReciprocalRootNames.ScaledRoot.affine retained.1.certificate
        (ExplicitField.pow_ne_zero_of_ne_zero nonzero _)⟩ := by
  unfold ofScaled
  exact prepare_supplied cap parameter nonzero regular.channel.inside regular.channel.preparation
    ⟨factor, retained.1⟩

end Preparation

namespace Reading

/-- Observe the original complete form on the same supplied signed root and retain its whole numerical preparation.

The original coefficient and request constructors consume that preparation
once. Its regular root, reciprocal scale and original signed attachment
are supplied rather than reacquired during observation setup.
-/
def ofScaled (differential : OddPowerDifferential curve.polynomial)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter)) {factor : Canonical}
    (retained : RootCoordinates.Overlap.Scaled regular factor)
    (target : Rational) (positive : 0 < target) :
    Reading differential cap parameter regular.channel.inside target factor :=
  let prepared := Preparation.ofScaled parameter nonzero regular retained
  let cached := coefficient differential prepared
  observe differential cap parameter regular.channel.inside target positive prepared cached

/-- The complete signed reading is the original request on its retained preparation and whole coefficient. -/
theorem ofScaled_eq (differential : OddPowerDifferential curve.polynomial)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter)) {factor : Canonical}
    (retained : RootCoordinates.Overlap.Scaled regular factor)
    (target : Rational) (positive : 0 < target) :
    ofScaled differential parameter nonzero regular retained target positive =
      let prepared := Preparation.ofScaled parameter nonzero regular retained
      let cached := coefficient differential prepared
      ⟨prepared, cached, Request.build cached.channel target positive⟩ := by
  unfold ofScaled
  exact observe_eq differential cap parameter regular.channel.inside target positive _ _

end Reading

namespace Coefficient

/-- The actual negative even-chart pullback agrees with the supplied numerical coefficient on that same signed source.

Both affine-root caches are retained inputs: one belongs to the original
attached chart and the other to the numerical preparation. Their actual
negative source factor and the original two guarded quotient comparisons
identify the complete forms. No independent sheet comparison is assumed.
-/
def evenNegative_pullback (differential : OddPowerDifferential curve.polynomial)
    (pairs : differential.denominatorPairs = 0)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter))
    (retained : RootCoordinates.Overlap.Scaled regular (-1))
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (prepared : Preparation cap parameter regular.channel.inside (-1))
    (same : prepared = Preparation.ofScaled parameter nonzero regular retained)
    (cached : Coefficient differential prepared)
    (affine : ReciprocalRootNames.ScaledRoot retained.overlap.reciprocal
      (((Primitives.point curve parameter)⁻¹) ^ (genus + 1))
      curve.polynomial (Primitives.point curve parameter)⁻¹) :
    NamedEquivalent
      ((Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul
          (differential.value (Primitives.point curve parameter)⁻¹
            affine.certificate.value affine.certificate.apart))).name cached.channel.name := by
  let point := Primitives.point curve parameter
  let jacobian := -((point⁻¹) ^ 2)
  let power := point ^ (genus + 1)
  let inversePower := (point⁻¹) ^ (genus + 1)
  let numerator := power * (jacobian * cached.1.val)
  have tangent (actual : Canonical) : Primitives.tangent curve actual = 1 := by
    unfold Primitives.tangent Primitives.degree
    rewrite [parity, pow_zero]
    rfl
  have pointNonzero : point ≠ 0 := ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  have inverseCancel : inversePower * power = (1 : Canonical) := by
    change (point⁻¹) ^ (genus + 1) * point ^ (genus + 1) = 1
    rewrite [← Algebra.Semiring.Normalization.product_pow,
      Canonical.inv_mul_cancel point pointNonzero, one_pow]
    rfl
  have cleared : inversePower * ((-1 : Canonical) * ((-1 : Canonical) * numerator)) =
      Primitives.tangent curve parameter * (jacobian * cached.1.val) := by
    calc
      _ = (inversePower * power) * (jacobian * cached.1.val) := by
        dsimp only [numerator]
        ring1
      _ = 1 * (jacobian * cached.1.val) :=
        congrArg (fun scalar : Canonical => scalar * (jacobian * cached.1.val)) inverseCancel
      _ = _ := congrArg (fun scalar : Canonical => scalar * (jacobian * cached.1.val))
        (tangent parameter).symm
  have numerical := cached.quotient_equivalent pairs ((-1 : Canonical) * numerator) cleared
  have regularEq : prepared.1 = regular.channel.preparation :=
    (congrArg (fun value : Preparation cap parameter regular.channel.inside (-1) => value.1) same).trans
      (congrArg (fun value : Preparation cap parameter regular.channel.inside (-1) => value.1)
        (Preparation.ofScaled_eq parameter nonzero regular retained))
  have denominatorEq : prepared.1.certificate = regular.certificate :=
    congrArg RootChannel.Preparation.certificate regularEq
  have chartRootEq : retained.overlap.regularRoot = regular.certificate :=
    retained.overlap.regularRoot_eq.trans
      (congrArg Owners.Point.certificate (RootCoordinates.Overlap.Scaled.regular retained))
  have geometric := retained.even_pullback pointNonzero parity differential pairs affine cached.1
  rewrite [tangent point, chartRootEq] at geometric
  have constant := ReciprocalRootNames.constant_mul_quotient (-1) numerator
    regular.certificate.value regular.certificate.apart
  have numericalRoot : NamedEquivalent cached.channel.name
      (div (Coherence.exact ((-1 : Canonical) * numerator))
        regular.certificate.value regular.certificate.apart).name := by
    rewrite [← denominatorEq]
    exact numerical
  have sourceEq :
      ((Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact jacobian).mul
          (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name =
      ((Coherence.exact 1).mul ((Coherence.exact jacobian).mul
        (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name :=
    congrArg (fun scalar : Canonical => ((Coherence.exact scalar).mul ((Coherence.exact jacobian).mul
      (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name) (tangent parameter)
  exact NamedEquivalent.transport sourceEq.symm rfl ((geometric.trans constant).trans numericalRoot.symm)

end Coefficient

namespace Reading

/-- The same actual signed observation retains the original negative-sheet chart comparison.

The complete factory equality identifies its retained preparation and
coefficient with the actual signed producer. The original comparison
consumes those supplied fields directly, together with the attached
chart's independent affine-root cache; no observation or preparation
factory runs again to construct this comparison.
-/
def evenNegative_pullback (differential : OddPowerDifferential curve.polynomial)
    (pairs : differential.denominatorPairs = 0)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (regular : Owners.Point cap (Primitives.point curve parameter))
    (retained : RootCoordinates.Overlap.Scaled regular (-1))
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (target : Rational) (positive : 0 < target)
    (actual : { value : Reading differential cap parameter regular.channel.inside target (-1) //
      value = ofScaled differential parameter nonzero regular retained target positive })
    (affine : ReciprocalRootNames.ScaledRoot retained.overlap.reciprocal
      (((Primitives.point curve parameter)⁻¹) ^ (genus + 1))
      curve.polynomial (Primitives.point curve parameter)⁻¹) :
    NamedEquivalent
      ((Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul
          (differential.value (Primitives.point curve parameter)⁻¹
            affine.certificate.value affine.certificate.apart))).name actual.val.2.1.channel.name := by
  have supplied := congrArg
    (fun value : Reading differential cap parameter regular.channel.inside target (-1) => value.1)
    actual.property
  have built := congrArg
    (fun value : Reading differential cap parameter regular.channel.inside target (-1) => value.1)
    (ofScaled_eq differential parameter nonzero regular retained target positive)
  exact Coefficient.evenNegative_pullback differential pairs parameter nonzero regular retained parity
    actual.val.1 (supplied.trans built) actual.val.2.1 affine

end Reading

namespace Preparation

/-- Prepare the negative even sheet from the same supplied regular numerical root and its actual reciprocal radicand.

The retained canonical scale supplies the radicand identity. Parity makes
that original scale one, so the same regular root can be scaled by minus
one. No numerical root preparation or winding attachment is reacquired.
-/
def evenNegative (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (original : Preparation cap parameter inside)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    Preparation cap parameter inside (-1) := by
  have power : parameter ^ HyperellipticReciprocal.originOrder curve = 1 := by
    rewrite [parity, pow_zero]
    rfl
  have identity := original.2.1.targetValue_eq.symm.trans original.2.1.radicand_eq
  change parameter ^ HyperellipticReciprocal.originOrder curve *
    parameter ^ HyperellipticReciprocal.originOrder curve *
      cap.polynomial.eval (Primitives.point curve parameter) =
        (HyperellipticReciprocal.polynomial curve).eval (Primitives.point curve parameter) at identity
  rewrite [power, Canonical.one_mul, Canonical.one_mul] at identity
  have negative : (-1 : Canonical) ≠ 0 := by decide
  have scaled : (-1 : Canonical) * (-1) * cap.polynomial.eval (Primitives.point curve parameter) =
      (HyperellipticReciprocal.polynomial curve).eval (Primitives.point curve parameter) := by
    calc
      _ = cap.polynomial.eval (Primitives.point curve parameter) := by ring1
      _ = _ := identity
  let reciprocal := ReciprocalRootNames.ScaledRoot.build original.1.certificate (-1) negative
    (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter) scaled
  exact prepare cap parameter nonzero inside original.1 (some ⟨-1, reciprocal⟩)

/-- The negative-sheet preparation retains the complete supplied original regular numerical cache. -/
theorem evenNegative_regular (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (original : Preparation cap parameter inside)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    (evenNegative parameter nonzero inside original parity).1 = original.1 := by
  unfold evenNegative
  exact congrArg (fun actual : Preparation cap parameter inside (-1) => actual.1)
    (prepare_supplied cap parameter nonzero inside original.1 ⟨-1, _⟩)

end Preparation

namespace Coefficient

/-- Opposite even-sheet and scalar signs compare the two actual whole coefficient channels on their same regular root.

Both supplied affine-form caches retain their own differential and scaled
sheet. Their cleared numerators have the same regular-root quotient, so
the original two guarded comparisons compose without a new observation.
-/
def evenNegative_equivalent
    (differential reference : OddPowerDifferential curve.polynomial)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (originalPrepared : Preparation cap parameter inside)
    (negativePrepared : Preparation cap parameter inside (-1))
    (sameRegular : negativePrepared.1 = originalPrepared.1)
    (original : Coefficient reference originalPrepared)
    (negative : Coefficient differential negativePrepared)
    (opposite : negative.1.val = -original.1.val)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    NamedEquivalent negative.channel.name original.channel.name := by
  let numerator := original.numerator
  have power : parameter ^ HyperellipticReciprocal.originOrder curve = 1 := by
    rewrite [parity, pow_zero]
    rfl
  have originalCleared := original.numerator_cleared nonzero
  have cleared : (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * numerator =
      Primitives.tangent curve parameter *
        (-(((Primitives.point curve parameter)⁻¹) ^ 2) * original.1.val) := by
    calc
      _ = (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * (1 * numerator) :=
        congrArg (fun value : Canonical => (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * value)
          (Canonical.one_mul numerator).symm
      _ = (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) *
          (parameter ^ HyperellipticReciprocal.originOrder curve * numerator) :=
        congrArg (fun factor : Canonical =>
          (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * (factor * numerator)) power.symm
      _ = _ := originalCleared
  have negativeCleared :
      (((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * ((-1 : Canonical) * numerator) =
        Primitives.tangent curve parameter *
          (-(((Primitives.point curve parameter)⁻¹) ^ 2) * negative.1.val) := by
    calc
      _ = -((((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) * numerator) := by ring1
      _ = -(Primitives.tangent curve parameter *
          (-(((Primitives.point curve parameter)⁻¹) ^ 2) * original.1.val)) :=
        congrArg (fun value : Canonical => -value) cleared
      _ = _ := by
        rewrite [opposite]
        ring1
  have first := negative.quotient_equivalent pairs numerator negativeCleared
  have second := original.quotient_equivalent referencePairs numerator originalCleared
  have denominator := congrArg
    (fun regular : RootChannel.Preparation cap.model cap.model_small (Primitives.point curve parameter) inside =>
      (div (Coherence.exact numerator) regular.certificate.value regular.certificate.apart).name) sameRegular
  exact (NamedEquivalent.transport rfl denominator first).trans second.symm

end Coefficient

namespace Reading

/-- Observe the negative even sheet using the actual source preparation and the opposite retained scalar numerator.

The supplied reference differential has the same numerator and the opposite
scale. Its already computed scalar is negated once and supplied to the
original coefficient factory. The result retains the actual negative-sheet
observation together with its original shared-root coefficient comparison.
-/
def evenNegative (differential reference : OddPowerDifferential curve.polynomial)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (target : Rational) (positive : 0 < target)
    (original : Reading reference cap parameter inside target) :
    (actual : Reading differential cap parameter inside target (-1)) ×
      NamedEquivalent actual.2.1.channel.name original.2.1.channel.name := by
  let prepared := Preparation.evenNegative parameter nonzero inside original.1 parity
  have scalar : -original.2.1.1.val =
      differential.scale * differential.numerator.eval (Primitives.point curve parameter)⁻¹ := by
    rewrite [original.2.1.1.property, sameNumerator, oppositeScale]
    ring1
  let cached := coefficient differential prepared ⟨-original.2.1.1.val, scalar⟩
  let actual := observe differential cap parameter inside target positive prepared cached
  have compared := Coefficient.evenNegative_equivalent differential reference pairs referencePairs
    parameter nonzero inside original.1 prepared
    (Preparation.evenNegative_regular parameter nonzero inside original.1 parity)
    original.2.1 cached rfl parity
  have cache := congrArg
    (fun value : Reading differential cap parameter inside target (-1) => value.2.1.channel.name)
    (observe_eq differential cap parameter inside target positive prepared cached)
  exact ⟨actual, NamedEquivalent.transport cache.symm rfl compared⟩

end Reading

section AttachedChart

variable {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}
    {factor : Canonical}

namespace Preparation

/-- The original point, signed overlap and affine root retained from one actual numerical preparation.

The complete regular preparation and reciprocal root remain tied to the
supplied caches. The affine root has the overlap's actual reciprocal
owner as parent and retains the same complete numerical certificate.
-/
abbrev Attached (prepared : Preparation cap parameter inside factor) :=
  (regular : { value : Owners.Point cap (Primitives.point curve parameter) //
    value.channel.preparation = prepared.1 }) ×
  (retained : RootCoordinates.Overlap.Scaled regular.val factor) ×
    { affine : ReciprocalRootNames.ScaledRoot retained.overlap.reciprocal
        (((Primitives.point curve parameter)⁻¹) ^ (genus + 1))
        curve.polynomial (Primitives.point curve parameter)⁻¹ //
      HEq retained.1 prepared.2.1 ∧ affine.certificate = prepared.certificate }

/-- The actual retained cap model aligns with the winding owner attached to its same numerical preparation.

The original model samples compare to the complete regular channel, then
its saved attachment compares that numerical root to its actual winding
owner. No comparison model, continued root or new attachment is acquired.
The resulting predicate concerns this exact cap model at every independent
continued representative of that same owner.
-/
theorem Attached.aligned {prepared : Preparation cap parameter inside factor}
    (retained : Attached prepared) (index : Nat) :
    RootAligned (Model.overlapRefine cap.model index) (Primitives.point curve parameter)
      (retained.1.val.channel.attachment.owner.certificate
        retained.1.val.channel.attachment.owner.parameterNonzero).value.name := by
  let channel := retained.1.val.channel
  have numerical : RootAligned (Model.overlapRefine cap.model index) (Primitives.point curve parameter)
      channel.certificate.value.name :=
    RootAligned.ofSamples
      channel.samples channel.small channel.inside channel.certificate.value.name
      channel.samples_equivalent index
  intro count patch patchInside sample roots refinement
  exact numerical patch patchInside sample (channel.owner_equivalent.symm.trans roots) refinement

/-- Compare an actual terminal cap reading with the exact owner of its retained prepared continuation.

The source attachment aligns the original cap model. Its same complete
segment and primitive mesh propagate that alignment to the actual finish
owner at every model index. The supplied terminal Point retains its own
query relation; independent numerical requests then compare the original
terminal channel without reacquiring either root or preparation.
-/
def Attached.completeSegment_equivalent {prepared : Preparation cap parameter inside factor}
    (retained : Attached prepared) {finishParameter : Canonical}
    (finish : Owners.Point cap (Primitives.point curve finishParameter)) {ambient : Box}
    (segment : ClearSegment cap.polynomial ambient
      (Primitives.point curve parameter) (Primitives.point curve finishParameter))
    (within : segment.WithinAmbient) (enclosure : ambient.Refines collar.box)
    (continued : CompleteSegment segment within retained.1.val.channel.attachment.owner)
    (bounds : Bounds segment) (mesh : Mesh bounds)
    (meshEq : continued.subdivision.parameterEdges = mesh.edges)
    {count : Nat} (patch : ContinuedNeighborhood cap.polynomial count)
    (patchInside : patch.box.Contains (Primitives.point curve finishParameter))
    (sample : ContinuedNeighborhood.Point patch (Primitives.point curve finishParameter))
    (queried : NamedEquivalent
      (ownerRootName continued.finishOwner.parameterNonzero continued.finishOwner)
      sample.certificate.value.name) :
    NamedEquivalent finish.certificate.value.name
      (ownerRootName continued.finishOwner.parameterNonzero continued.finishOwner) := by
  let owner := continued.finishOwner
  have aligned (index : Nat) :
      RootAligned (Model.overlapRefine cap.model index) (Primitives.point curve finishParameter)
        (ownerRootName owner.parameterNonzero owner) := by
    apply RootAligned.completeSegment segment within enclosure continued bounds mesh meshEq
    intro entries neighborhood localInside current roots refinement
    exact retained.aligned index neighborhood localInside current roots refinement
  let channel := finish.channel
  let compared := PreparedPolynomialSheetReadings.rootEquivalent channel.samples channel.small channel.inside
    patch patchInside sample (owner.certificate owner.parameterNonzero) queried aligned
  exact channel.samples_equivalent.symm.trans compared

/-- Attach the supplied numerical caches to their actual original chart owners once.

The regular point consumes the whole supplied numerical preparation. Its
same reciprocal root is attached and passed to the original overlap; the
saved affine root is reparented along that actual attachment comparison.
No numerical root, numerator observation or affine scaled-root factory
runs again. The existing inverse channel is retained; the exact coordinate
scale is still read at this attachment boundary.
-/
def attach (prepared : Preparation cap parameter inside factor) : Attached prepared := by
  let regular : { value : Owners.Point cap (Primitives.point curve parameter) //
      value.channel.preparation = prepared.1 } :=
    ⟨Owners.Point.build cap (Primitives.point curve parameter) inside prepared.1,
      RootChannel.build_preparation cap.model cap.model_small (Primitives.point curve parameter) inside prepared.1⟩
  let reciprocal : ReciprocalRootNames.ScaledRoot regular.val.certificate factor
      (HyperellipticReciprocal.polynomial curve) (Primitives.point curve parameter) := prepared.2.1
  let attached := ReciprocalRootOwners.attach reciprocal
  let overlap := RootCoordinates.Overlap.ofScaled regular.val reciprocal attached
  let retained : RootCoordinates.Overlap.Scaled regular.val factor :=
    ⟨reciprocal, attached, ⟨overlap, rfl⟩⟩
  have equivalent : NamedEquivalent prepared.2.1.certificate.value.name retained.overlap.reciprocal.value.name :=
    attached.equivalent
  let affine := prepared.2.2.transport equivalent
  exact ⟨regular, retained, ⟨affine, ⟨HEq.rfl, prepared.2.2.transport_certificate equivalent⟩⟩⟩

/-- Equal actual cap parameters join two retained signed chart coordinates from the same original factor function.

Both supplied attachments keep their original numerical preparations,
scaled roots and winding owners. Their cached factor reconstruction laws
derive the coordinate comparison; no root agreement is assumed or acquired.
-/
def Attached.join {factors : Canonical → Canonical} {firstParameter lastParameter : Canonical}
    {firstInside : collar.box.Contains (Primitives.point curve firstParameter)}
    {lastInside : collar.box.Contains (Primitives.point curve lastParameter)}
    {firstPrepared : Preparation cap firstParameter firstInside (factors firstParameter)}
    {lastPrepared : Preparation cap lastParameter lastInside (factors lastParameter)}
    (first : Attached firstPrepared) (last : Attached lastPrepared) (equal : firstParameter = lastParameter) :
    RootCoordinates.Overlap.Join first.2.1.overlap last.2.1.overlap := by
  cases equal
  exact ⟨rfl, first.2.1.factor_agrees.trans last.2.1.factor_agrees.symm⟩

/-- Transport the same complete numerical preparation and attached chart cache to an equal actual parameter.

The signed factor is the same supplied function at both parameters. Only
equality elimination changes the dependent indices; every regular root,
scaled certificate and original winding attachment remains the supplied one.
-/
def transportAttached {factors : Canonical → Canonical} {firstParameter lastParameter : Canonical}
    {firstInside : collar.box.Contains (Primitives.point curve firstParameter)}
    {lastInside : collar.box.Contains (Primitives.point curve lastParameter)}
    (equal : firstParameter = lastParameter)
    (retained : (prepared : Preparation cap firstParameter firstInside (factors firstParameter)) × Attached prepared) :
    (prepared : Preparation cap lastParameter lastInside (factors lastParameter)) × Attached prepared := by
  cases equal
  exact retained

/-- Equal-parameter transport retains the entire supplied preparation-and-attachment pair. -/
theorem transportAttached_heq {factors : Canonical → Canonical} {firstParameter lastParameter : Canonical}
    {firstInside : collar.box.Contains (Primitives.point curve firstParameter)}
    {lastInside : collar.box.Contains (Primitives.point curve lastParameter)}
    (equal : firstParameter = lastParameter)
    (retained : (prepared : Preparation cap firstParameter firstInside (factors firstParameter)) × Attached prepared) :
    HEq (transportAttached (lastInside := lastInside) equal retained) retained := by
  cases equal
  exact HEq.rfl

/-- The original affine form and both exact Jacobians at the actual attached chart's retained affine root.

This reducible view fixes the original point and complete certificate.
It is used as a type index when the already paid numerical request is
transported; that transport does not execute another form observation.
-/
abbrev Attached.pullback {prepared : Preparation cap parameter inside factor}
    (retained : Attached prepared) (differential : OddPowerDifferential curve.polynomial) : CoherentNamed :=
  (Coherence.exact (Primitives.tangent curve parameter)).mul
    ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul
      (differential.value (Primitives.point curve parameter)⁻¹
        retained.2.2.val.certificate.value retained.2.2.val.certificate.apart))

end Preparation

namespace Coefficient

/-- The same complete numerical coefficient is the actual attached affine-chart pullback.

Only the original whole coefficient readback and the transported affine
certificate identity are composed. Both source and chart keep their
actual retained roots, scalar numerator and original Jacobian factors.
-/
theorem attached_channel {differential : OddPowerDifferential curve.polynomial}
    {prepared : Preparation cap parameter inside factor} (cached : Coefficient differential prepared)
    (retained : Preparation.Attached prepared) : cached.channel = retained.pullback differential :=
  cached.channel_eq.trans (congrArg
    (fun certificate : Riemann.RootContinuation.CertifiedSquareRoot.Certificate
        (curve.polynomial.eval (Primitives.point curve parameter)⁻¹) =>
      (Coherence.exact (Primitives.tangent curve parameter)).mul
        ((Coherence.exact (-(((Primitives.point curve parameter)⁻¹) ^ 2))).mul
          (differential.value (Primitives.point curve parameter)⁻¹ certificate.value certificate.apart)))
    retained.2.2.property.2.symm)

end Coefficient

namespace Reading

/-- One actual attached chart view with the identical whole original paid request.

The request's exact source index is transported by the coefficient's whole
channel equality. Its full state, witness, radius, tolerance and owner
remain the supplied actual request; no refinement or observation runs.
-/
abbrev Attached {differential : OddPowerDifferential curve.polynomial} {target : Rational}
    (actual : Reading differential cap parameter inside target factor) :=
  (retained : Preparation.Attached actual.1) ×
    { request : Request (retained.pullback differential) target //
      HEq request actual.2.2 ∧ request.reading.value = actual.2.2.reading.value }

/-- Attach an actual form reading and retain its complete paid request on that same affine-chart pullback. -/
def attach {differential : OddPowerDifferential curve.polynomial} {target : Rational}
    (actual : Reading differential cap parameter inside target factor) : Attached actual := by
  let retained := Preparation.attach actual.1
  have same := Coefficient.attached_channel actual.2.1 retained
  let request := Eq.mp (congrArg (fun channel : CoherentNamed => Request channel target) same) actual.2.2
  have value : request.reading.value = actual.2.2.reading.value :=
    Eq.recOn (motive := fun channel (same : actual.2.1.channel = channel) =>
      (Eq.mp (congrArg (fun value : CoherentNamed => Request value target) same)
        actual.2.2).reading.value = actual.2.2.reading.value) same rfl
  exact ⟨retained, ⟨request, ⟨cast_heq _ _, value⟩⟩⟩

/-- The attached chart request reads the identical actual Gaussian value of its original complete paid request. -/
theorem Attached.value_eq {differential : OddPowerDifferential curve.polynomial} {target : Rational}
    {actual : Reading differential cap parameter inside target factor} (retained : Attached actual) :
    retained.2.val.reading.value = actual.2.2.reading.value := retained.2.property.2

end Reading

end AttachedChart

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings

end
