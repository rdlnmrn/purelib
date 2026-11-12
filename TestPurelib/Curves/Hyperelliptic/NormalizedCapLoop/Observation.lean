module

-- Fixture proofs reduce the original private finite preparation and affine-scaling bodies.
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Approximation.Gaussian.Name.Coherent
import all Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Partition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Algebra.Field.ExplicitField
import Purelib.RationalFunctions.Curve.Canonical.Circle.Tangent
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import all Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Program
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Power.Gaussian.Candidates
import Purelib.Data.List.Search
import Purelib.Data.List.Map
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Residual.Global.Bounds
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
import Purelib.Integration.CCL.Program
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Int.Decimal
import Purelib.System.IO
import Init.Util

/-! # A nonzero full-form cap-loop request on an exact genus-zero curve -/

namespace TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.Observation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
open Purelib.Approximation.Rational
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Equivalence

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian

/-- The exact linear polynomial defining the nonzero form's original genus-zero curve. -/
private def polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[1, 0]⟩

/-- The actual curve y²=x, with the original computed Euclidean squarefree certificate. -/
private def curve : HyperellipticCurve 0 where
  polynomial := polynomial
  nonzero := by decide +kernel
  squarefree :=
    Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
      polynomial (Dense.Gaussian.GCD.derivative polynomial)
      (Dense.Gaussian.GCD.extendedGCD polynomial (Dense.Gaussian.GCD.derivative polynomial))
      rfl (by decide +kernel) (by decide +kernel)
  degreeShape := .odd (by decide +kernel)

/-- The nonzero differential dx/y retains its original indexed coefficient expression. -/
private def differential : OddPowerDifferential curve.polynomial :=
  OddPowerDifferential.ofCoefficients curve.polynomial ⟨[1]⟩ 0 1

/-- The original coefficient-derived collar is computed without a supplied radius. -/
private def collar : ReciprocalExteriorCollar.Data curve := ReciprocalExteriorCollar.Data.build curve

/-- Both exact form-polynomial tables are retained before any curve or stage entry. -/
private def data := FormReadings.Circle.polynomials differential

/-- The coefficient cache is built from the original exact curve once. -/
private def jet := InfinityCoefficients.prepare curve

/-- The original residual tail consumes that same retained finite jet. -/
private def remainder := jet.property.remainder

/-- The principal convolution consumes the same original padded numerator and scale. -/
private def principal := jet.principal data.1.val differential.scale

/-- The actual substituted table is retained independently of every later circuit radius. -/
private def table : { value : CoefficientPolynomial // value = Primitives.parameterPolynomial principal } :=
  ⟨Primitives.parameterPolynomial principal, rfl⟩

/-- The original polar primitive is computed from the same retained principal coefficients. -/
private def primitive := Antiderivative.reciprocalPrimitive principal.val 0

/-- The finite jet's original box bounds are computed once on the same collar. -/
private def jetBounds := jet.bounds collar.box

/-- The original zero-depth coarse edges preserve the canonical endpoints and ordered quarter parents. -/
private def edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish :=
  ⟨dyadicEdges 0 Circle.Loop.start Circle.Loop.finish, rfl⟩

/-- This nonzero form has the exact original pair count required by the full cap programme. -/
private theorem pairs : differential.denominatorPairs = 0 := (rfl)

/-- The same constant numerator has the exact genus-zero degree bound. -/
private theorem degreeBound : differential.numerator.natDegree ≤ 2 * 0 := by decide +kernel

/-- Complete the same original cap factory before entering a numerical-origin phase. -/
@[noinline] private def withCap (sheet : Fin 2)
    (next : ReciprocalInnerInverse.Data curve collar → IO Unit) : IO Unit :=
  next (ReciprocalInnerInverse.Data.build curve collar sheet)

/-- The original origin-point construction supplies its own collar containment certificate. -/
private theorem originInside (cap : ReciprocalInnerInverse.Data curve collar) : collar.box.Contains 0 :=
  (Owners.Point.atOrigin cap).channel.inside

/-- The original numerical origin preparation retains the actual cap model and containment. -/
private abbrev OriginPreparation (cap : ReciprocalInnerInverse.Data curve collar) :=
  InverseModelRootChannels.RootChannel.Preparation cap.model cap.model_small 0 (originInside cap)

/-- Complete the original numerical origin preparation before calling the IO continuation. -/
@[noinline] private def withPreparedOrigin (cap : ReciprocalInnerInverse.Data curve collar)
    (next : OriginPreparation cap → IO Unit) : IO Unit :=
  next (InverseModelRootChannels.RootChannel.prepare cap.model cap.model_small 0 (originInside cap))

/-- Build the original whole point with the literal supplied cache before its IO continuation. -/
@[noinline] private def withAttachedOrigin (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) (next : Owners.Point cap 0 → IO Unit) : IO Unit :=
  next (Owners.Point.build cap 0 (originInside cap) cached)

/-- Splitting the two original phases preserves the complete former origin continuation. -/
private theorem splitOrigin_eq (cap : ReciprocalInnerInverse.Data curve collar)
    (next : Owners.Point cap 0 → IO Unit) :
    withPreparedOrigin cap (fun cached => withAttachedOrigin cap cached next) =
      next (Owners.Point.atOrigin cap) := (rfl)

/-- The original attachment anchor keeps the same source certificate and exact polynomial parameter. -/
private abbrev OriginAnchor (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap) :=
  SquareRootChannelOwnership.Anchor cached.certificate.value (cap.polynomial.eval 0)

/-- Complete the original source anchor before calling the IO continuation. -/
@[noinline] private def withOriginAnchor (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) (next : OriginAnchor cap cached → IO Unit) : IO Unit :=
  next (SquareRootChannelOwnership.Anchor.build cached.certificate)

/-- Complete original inside assignment using the literal supplied anchor and retain its whole winding owner. -/
@[noinline] private def withAssignedOrigin (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) (anchor : OriginAnchor cap cached)
    (next : SquareRootChannelOwnership.Owner (cap.polynomial.eval 0) → IO Unit) : IO Unit :=
  let assigned := RootIsolation.Residual.Global.Assignment.assignInside
    (SquareRootReconditioning.isolationInput anchor.nonzero) anchor.value
    anchor.inside anchor.radiusPositive
    (by simpa only [Norm.Basic.normSq_eq_canonical] using anchor.residual)
  next
    { parameterNonzero := anchor.nonzero
      ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
        (SquareRootReconditioning.rootPolynomial (cap.polynomial.eval 0))
      track := assigned.track }

/-- Splitting anchor and assignment preserves the complete original attachment-owner continuation. -/
private theorem splitAttachmentOwner_eq (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap)
    (next : SquareRootChannelOwnership.Owner (cap.polynomial.eval 0) → IO Unit) :
    withOriginAnchor cap cached (fun anchor => withAssignedOrigin cap cached anchor next) =
      next (SquareRootChannelOwnership.attach cached.certificate).owner := (rfl)

/-- The original attachment radius computed from this actual certificate's retained lower bound. -/
private def anchorRadius (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap) :=
  Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
    (cached.certificate.apart.certificate.lowerSq / 1024)

/-- The same original radius is strictly positive. -/
private theorem anchorRadius_positive (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) : 0 < anchorRadius cap cached :=
  Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _

/-- The original residual target uses this same source certificate and its actual retained radius. -/
private def anchorTarget (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap)
    (radius : Fraction.Rational) :=
  min (RootIsolation.Residual.Global.Bounds.outsideResidualThreshold
      (SquareRootReconditioning.rootPolynomial (cap.polynomial.eval 0)))
    (RootIsolation.Residual.Global.Assignment.insideResidualTarget
      (SquareRootReconditioning.isolationInput
        (SquareRootChannelOwnership.parameter_nonzero cached.certificate)) radius)

/-- The original inside/outside residual minimum is positive at every positive supplied radius. -/
private theorem anchorTarget_positive (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap)
    (radius : Fraction.Rational) (positive : 0 < radius) : 0 < anchorTarget cap cached radius :=
  Fraction.Order.Basic.lt_min
    (RootIsolation.Residual.Global.Bounds.outsideResidualThreshold_pos
      (SquareRootReconditioning.isolationInput (SquareRootChannelOwnership.parameter_nonzero
        cached.certificate)).degreePositive)
    (RootIsolation.Residual.Global.Assignment.insideResidualTarget_pos
      (SquareRootReconditioning.isolationInput
        (SquareRootChannelOwnership.parameter_nonzero cached.certificate)) positive)

/-- The exact original sampled-square comparison remains indexed by its actual retained radius. -/
private abbrev AnchorComparison (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap)
    (radius : Fraction.Rational) :=
  Equivalence.Comparison
    (Sequence.Arithmetic.Product.sampledProductApproximation
      cached.certificate.value.name cached.certificate.value.name)
    (Name.Sampling.approximation (Name.Coherent.CoherentNamed.Coherence.exact (cap.polynomial.eval 0)).name)
    0 0 (anchorTarget cap cached radius)

/-- The request cache consists solely of exact views of the original radius, comparison, sampler and selected index. -/
private abbrev AnchorRequest (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap) :=
  (radius : { value : Fraction.Rational // value = anchorRadius cap cached }) ×
    (compared : { value : AnchorComparison cap cached radius.val // value =
      (SquareRootProvenance.sampled_square cached.certificate.square).compare 0 0 (anchorTarget cap cached radius.val)
        (anchorTarget_positive cap cached radius.val (by
          rewrite [radius.property]
          exact anchorRadius_positive cap cached)) }) ×
    (source : { value : Sequence.ApproximationData //
      value = Name.Sampling.approximation cached.certificate.value.name }) ×
      { index : Nat // index = source.val.refineIndex compared.val.leftIndex
          (cached.certificate.apart.certificate.lowerSq / 8)
          (Fraction.Order.Field.div_pos_direct cached.certificate.apart.certificate.positive (by decide +kernel)) }

/-- Complete the original anchor request and final index before entering its separate sample-reading continuation. -/
@[noinline] private def withAnchorRequest (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) (next : AnchorRequest cap cached → IO Unit) : IO Unit :=
  let radius := anchorRadius cap cached
  let target := anchorTarget cap cached radius
  let compared := (SquareRootProvenance.sampled_square cached.certificate.square).compare 0 0 target
    (anchorTarget_positive cap cached radius (anchorRadius_positive cap cached))
  let source := Name.Sampling.approximation cached.certificate.value.name
  let index := source.refineIndex compared.leftIndex (cached.certificate.apart.certificate.lowerSq / 8)
    (Fraction.Order.Field.div_pos_direct cached.certificate.apart.certificate.positive (by decide +kernel))
  next ⟨⟨radius, rfl⟩, ⟨compared, rfl⟩, ⟨source, rfl⟩, ⟨index, rfl⟩⟩

/-- Read the actual cached sampler/index and retain the complete original attachment anchor. -/
@[noinline] private def withAnchorSample (cap : ReciprocalInnerInverse.Data curve collar)
    (cached : OriginPreparation cap) (request : AnchorRequest cap cached)
    (next : OriginAnchor cap cached → IO Unit) : IO Unit := by
  let original := SquareRootChannelOwnership.Anchor.build cached.certificate
  let index := request.2.2.2.val
  let value := request.2.2.1.val.sample index
  have index_eq : index = original.index := by
    rcases request with ⟨⟨radius, radius_eq⟩, ⟨compared, compared_eq⟩, ⟨source, source_eq⟩, ⟨index, index_eq⟩⟩
    cases radius_eq
    cases compared_eq
    cases source_eq
    cases index_eq
    rfl
  have value_eq : value = original.value := by
    change request.2.2.1.val.sample index = original.value
    rewrite [request.2.2.1.property, index_eq]
    rfl
  exact next
    { nonzero := original.nonzero
      lower := cached.certificate.apart.certificate.lowerSq
      positive := cached.certificate.apart.certificate.positive
      radius := request.1.val
      radiusPositive := by rewrite [request.1.property]; exact original.radiusPositive
      radiusSmall := by rewrite [request.1.property]; exact original.radiusSmall
      index := index
      value := value
      value_eq := congrArg (fun source : Sequence.ApproximationData => source.sample index) request.2.2.1.property
      tailNear := by
        intro later order
        rewrite [index_eq] at order
        rewrite [value_eq]
        exact original.tailNear later order
      inside := by rewrite [value_eq]; exact original.inside
      residual := by rewrite [value_eq, request.1.property]; exact original.residual }

/-- Splitting request and sample preserves the complete original attachment-anchor continuation. -/
private theorem splitAnchor_eq (cap : ReciprocalInnerInverse.Data curve collar) (cached : OriginPreparation cap)
    (next : OriginAnchor cap cached → IO Unit) :
    withAnchorRequest cap cached (fun request => withAnchorSample cap cached request next) =
      next (SquareRootChannelOwnership.Anchor.build cached.certificate) := (rfl)

/-- Render both exact coordinates of a retained Gaussian sample without changing its numerical representation. -/
private def sampleText (value : Canonical) : String :=
  s!"{Data.Int.Decimal.repr value.re.num}/{Data.Nat.Decimal.repr value.re.den}," ++
    s!"{Data.Int.Decimal.repr value.im.num}/{Data.Nat.Decimal.repr value.im.den}"

/-- Pay both actual endpoint samples selected by one original finite comparison and check its strict scalar bound. -/
private def pay {left right : Sequence.ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (compared : Equivalence.Comparison left right leftStart rightStart target)
    (cached : Option
      ({ value : Canonical // value = left.sample compared.leftIndex } ×
        { value : Canonical // value = right.sample compared.rightIndex }) := none) : IO Unit := do
  Purelib.System.IO.println s!"CAP_PHASE_PAID_INDICES left={compared.leftIndex} right={compared.rightIndex}"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_LEFT_PHYSICAL_SAMPLE"
  (← IO.getStdout).flush
  let first := match cached with
    | none => left.sample compared.leftIndex
    | some readings => readings.1.val
  Purelib.System.IO.println s!"CAP_LEFT_SAMPLE {sampleText first}"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_RIGHT_COEFFICIENT_SAMPLE"
  let last := match cached with
    | none => right.sample compared.rightIndex
    | some readings => readings.2.val
  Purelib.System.IO.println s!"CAP_RIGHT_SAMPLE {sampleText last}"
  let squared := Norm.Basic.normSq (first - last)
  unless squared < target do throw (IO.userError "the original retained comparison failed its actual sample bound")
  Purelib.System.IO.println "CAP_NORMALIZED_FULL_FORM_PASS"
  (← IO.getStdout).flush

/-- Pay both actual endpoint samples selected by one original finite comparison and check its strict scalar bound. -/
private def formerPay {left right : Sequence.ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (compared : Equivalence.Comparison left right leftStart rightStart target) :
    IO Unit := do
  Purelib.System.IO.println s!"CAP_PHASE_PAID_INDICES left={compared.leftIndex} right={compared.rightIndex}"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_LEFT_PHYSICAL_SAMPLE"
  (← IO.getStdout).flush
  let first := left.sample compared.leftIndex
  Purelib.System.IO.println s!"CAP_LEFT_SAMPLE {sampleText first}"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_RIGHT_COEFFICIENT_SAMPLE"
  let last := right.sample compared.rightIndex
  Purelib.System.IO.println s!"CAP_RIGHT_SAMPLE {sampleText last}"
  let squared := Norm.Basic.normSq (first - last)
  unless squared < target do throw (IO.userError "the original retained comparison failed its actual sample bound")
  Purelib.System.IO.println "CAP_NORMALIZED_FULL_FORM_PASS"
  (← IO.getStdout).flush

/-- Omitting certified endpoint caches preserves the complete original payment action. -/
private theorem pay_none_eq_former {left right : Sequence.ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (compared : Equivalence.Comparison left right leftStart rightStart target) :
    pay compared none = formerPay compared := (rfl)

/-- Supplied exact endpoint caches preserve the complete original payment action. -/
private theorem pay_cached_eq_default {left right : Sequence.ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (compared : Equivalence.Comparison left right leftStart rightStart target)
    (cached : { value : Canonical // value = left.sample compared.leftIndex } ×
      { value : Canonical // value = right.sample compared.rightIndex }) :
    pay compared (some cached) = pay compared none := by
  rcases cached with ⟨⟨first, firstEq⟩, ⟨last, lastEq⟩⟩
  cases firstEq
  cases lastEq
  rfl

/-- Check the finite original coefficient inputs before any numerical model or physical source is demanded. -/
public def checkInputs : IO Unit := do
  unless curve.polynomial.coeffs == [1, 0] && differential.numerator.eval 0 == 1 &&
      differential.denominatorPairs == 0 && differential.scale == 1 do
    throw (IO.userError "nonzero full-form input changed")
  unless Coefficient.coefficient table.val (Primitives.parameterOrder curve) == 0 do
    throw (IO.userError "ramified coefficient readback changed")
  Purelib.System.IO.println "CAP_NONZERO_FORM_INPUTS_PASS"

/-- Execute only the original numerical origin preparation, preserving the same actual cap factory. -/
public def checkOriginPreparation (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_MODEL_PASS"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_BEGIN"
    (← IO.getStdout).flush
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println s!"CAP_ORIGIN_NUMERIC_PASS parameter={sampleText cached.samples.parameter}"
      (← IO.getStdout).flush

/-- Attach the original winding owner only after completing and passing its literal numerical preparation. -/
public def checkOriginAttachment (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_MODEL_PASS"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_BEGIN"
    (← IO.getStdout).flush
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println s!"CAP_ORIGIN_NUMERIC_PASS parameter={sampleText cached.samples.parameter}"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_BEGIN"
      (← IO.getStdout).flush
      withAttachedOrigin cap cached fun origin => do
        Purelib.System.IO.println s!"CAP_ORIGIN_ATTACHMENT_PASS parameter={sampleText origin.channel.samples.parameter}"
        (← IO.getStdout).flush

/-- Execute only the original attachment anchor on the same prepared numerical root. -/
public def checkOriginAnchor (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_MODEL_PASS"
    (← IO.getStdout).flush
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_PASS"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_ORIGIN_ANCHOR_BEGIN"
      (← IO.getStdout).flush
      withOriginAnchor cap cached fun anchor => do
        Purelib.System.IO.println s!"CAP_ORIGIN_ANCHOR_PASS index={anchor.index} value={sampleText anchor.value}"
        (← IO.getStdout).flush

/-- Execute original inside assignment on the literal same-source attachment anchor. -/
public def checkOriginAssignment (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_MODEL_PASS"
    (← IO.getStdout).flush
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_PASS"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_ORIGIN_ANCHOR_BEGIN"
      (← IO.getStdout).flush
      withOriginAnchor cap cached fun anchor => do
        Purelib.System.IO.println s!"CAP_ORIGIN_ANCHOR_PASS index={anchor.index} value={sampleText anchor.value}"
        (← IO.getStdout).flush
        Purelib.System.IO.println "CAP_ORIGIN_ASSIGNMENT_BEGIN"
        (← IO.getStdout).flush
        withAssignedOrigin cap cached anchor fun owner => do
          Purelib.System.IO.println s!"CAP_ORIGIN_ASSIGNMENT_PASS anchor={sampleText owner.track.initial.box.anchor}"
          (← IO.getStdout).flush

/-- Read only already retained model/seed values, without constructing an attachment or taking a named sample. -/
public def checkOriginReadings (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println s!"CAP_RETAINED_ROOT_SAMPLE {sampleText cap.seed.rootSample}"
      Purelib.System.IO.println s!"CAP_RETAINED_INVERSE_SEED {sampleText cap.seed.value}"
      Purelib.System.IO.println s!"CAP_RETAINED_MODEL_INITIAL {sampleText cached.samples.initial}"
      let diagonal := cap.owner.track.initial.box.diagonalSq
      Purelib.System.IO.println s!"CAP_RETAINED_OWNER_DIAGONAL {Data.Int.Decimal.repr diagonal.num}/{diagonal.den}"
      (← IO.getStdout).flush

/-- Execute the actual anchor residual request and index selection without reading its final named sample. -/
public def checkAnchorRequest (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println "CAP_ANCHOR_REQUEST_BEGIN"
      (← IO.getStdout).flush
      withAnchorRequest cap cached fun request => do
        Purelib.System.IO.println s!"CAP_ANCHOR_REQUEST_PASS left={request.2.1.val.leftIndex}"
        Purelib.System.IO.println s!"CAP_ANCHOR_REQUEST_RIGHT {request.2.1.val.rightIndex}"
        Purelib.System.IO.println s!"CAP_ANCHOR_SAMPLE_INDEX {request.2.2.2.val}"
        (← IO.getStdout).flush

/-- Read the original anchor sample only after the actual retained request/index cache has completed. -/
public def checkAnchorSample (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println "CAP_ANCHOR_REQUEST_BEGIN"
      (← IO.getStdout).flush
      withAnchorRequest cap cached fun request => do
        Purelib.System.IO.println s!"CAP_ANCHOR_REQUEST_PASS left={request.2.1.val.leftIndex}"
        Purelib.System.IO.println s!"CAP_ANCHOR_REQUEST_RIGHT {request.2.1.val.rightIndex}"
        Purelib.System.IO.println s!"CAP_ANCHOR_SAMPLE_INDEX {request.2.2.2.val}"
        (← IO.getStdout).flush
        Purelib.System.IO.println "CAP_ANCHOR_SAMPLE_BEGIN"
        (← IO.getStdout).flush
        withAnchorSample cap cached request fun anchor => do
          Purelib.System.IO.println s!"CAP_ANCHOR_SAMPLE_PASS {sampleText anchor.value}"
          (← IO.getStdout).flush

/-- The automatically certified exact candidates retain the actual leading coefficient and original degree two. -/
private abbrev ExactCandidate :=
  Purelib.Algebra.Power.Gaussian.ExactRoot curve.polynomial.leadingCoeff SquareRootDegree.degreeTwo

/-- Check membership in the same original owner box and a literal zero squared residual. -/
private def exactSeedAccepts (cap : ReciprocalInnerInverse.Data curve collar) (root : ExactCandidate) : Bool :=
  decide (cap.owner.track.initial.box.Contains root.point ∧
    Norm.Basic.normSq (root.point * root.point - curve.polynomial.leadingCoeff) = 0)

/-- The finite attempt retains the complete automatic bank and the exact original ordered-search result. -/
private abbrev ExactSeedAttempt (cap : ReciprocalInnerInverse.Data curve collar) :=
  (bank : List ExactCandidate) ×
    { selected : Option ExactCandidate // selected = bank.find? (exactSeedAccepts cap) }

/-- A supplied seed retains the literal original owner, an actual automatic candidate occurrence and zero residual. -/
private abbrev ExactSeed (cap : ReciprocalInnerInverse.Data curve collar) (bank : List ExactCandidate) :=
  { seed : OwnerSeededInverseRoot.Seed curve.polynomial.leadingCoeff //
    seed.owner = cap.owner ∧ seed.rootSample ∈ bank.map Purelib.Algebra.Power.Gaussian.ExactRoot.point ∧
      Norm.Basic.normSq (seed.rootSample * seed.rootSample - curve.polynomial.leadingCoeff) = 0 }

/-- Compute one automatic candidate bank and one finite membership/residual check against the same retained owner.

An unsuccessful attempt retains its whole bank and exact none result. A
successful branch passes the actual checked candidate to original Seed.ofSample;
no independent track or owner is substituted.
-/
@[noinline] private def withExactSeed (cap : ReciprocalInnerInverse.Data curve collar)
    (next : (attempt : ExactSeedAttempt cap) → Option (ExactSeed cap attempt.1) → IO Unit) : IO Unit := by
  let bank := Power.Gaussian.Candidates.automaticExactRoots
    curve.polynomial.leadingCoeff SquareRootDegree.degreeTwo
  let selected := bank.find? (exactSeedAccepts cap)
  let attempt : ExactSeedAttempt cap := ⟨bank, ⟨selected, rfl⟩⟩
  match found : selected with
  | none => exact next attempt none
  | some root =>
      have accepted := Data.List.Search.find?_eq_some_accepts_certificate found
      have checked : cap.owner.track.initial.box.Contains root.point ∧
          Norm.Basic.normSq (root.point * root.point - curve.polynomial.leadingCoeff) = 0 :=
        of_decide_eq_true accepted
      let seed := OwnerSeededInverseRoot.Seed.ofSample cap.owner root.point checked.1 (by
        have bound : Norm.Basic.normSq (root.point * root.point - curve.polynomial.leadingCoeff) ≤
            Norm.Basic.normSq curve.polynomial.leadingCoeff / 64 := by
          rewrite [checked.2]
          exact Fraction.Order.Field.div_nonneg_direct (Norm.Basic.normSq_nonneg _) (by decide +kernel)
        simpa only [Norm.Basic.normSq_eq_canonical] using bound)
      have member : root.point ∈ bank.map Purelib.Algebra.Power.Gaussian.ExactRoot.point :=
        Data.List.Map.mem_map.mpr ⟨root, Data.List.Search.find?_eq_some_mem_certificate found, rfl⟩
      exact next attempt (some ⟨seed, rfl, member, checked.2⟩)

/-- The original supplied-seed cap constructor retains this exact original leading-sheet owner. -/
private theorem suppliedSeed_owner (cap : ReciprocalInnerInverse.Data curve collar)
    (bank : List ExactCandidate) (seed : ExactSeed cap bank) :
    (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).owner = cap.owner :=
  seed.property.1

/-! Exact identities for the original supplied-seed physical sampler.

The private fixture retains the original cap owner, finite root banks,
four complete quarter programmes, stored normalizing quotient and named
sampling states. All finite physical samples are computed by their proved
original values; no replacement output channel is constructed.
-/

namespace Symmetry

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Riemann.Normalization.InverseModelRootSamples (RootSamples refineValue_fixed)

/-- The original linear curve's retained leading coefficient is exactly one. -/
private theorem leading_eq_one : curve.polynomial.leadingCoeff = 1 := (rfl)

/-- The actual reversed coefficient table evaluates to one at every original parameter. -/
private theorem reversed_eval_one (point : Canonical) :
    (Polynomial.Dense.Gaussian.Reciprocal.reversed curve.polynomial).eval point = 1 := by
  rewrite [Polynomial.Dense.Gaussian.Reciprocal.reversed_eval]
  change (1 + point * (0 + point * 0) : Canonical) = 1
  ring1

/-- The actual accepted zero-residual seed is an exact fixed inverse value for this leading coefficient. -/
private theorem seed_squared {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) : seed.val.value ^ 2 = 1 := by
  have rootSquare : seed.val.rootSample * seed.val.rootSample = curve.polynomial.leadingCoeff :=
    Basic.gaussian_eq_of_sub_eq_zero (Norm.Basic.normSq_eq_zero.mp seed.property.2.2)
  have inverse : curve.polynomial.leadingCoeff⁻¹ = (1 : Canonical) :=
    (congrArg (fun parameter : Canonical => parameter⁻¹) leading_eq_one).trans Field.inv_one_direct
  have value : seed.val.value = seed.val.rootSample := seed.val.value_eq.trans
    ((congrArg (fun factor : Canonical => seed.val.rootSample * factor) inverse).trans
      (Basic.mul_one seed.val.rootSample))
  exact (congrArg (fun point : Canonical => point ^ 2) value).trans
    ((show seed.val.rootSample ^ 2 = seed.val.rootSample * seed.val.rootSample by ring1).trans
      (rootSquare.trans leading_eq_one))

/-- The actual supplied cap polynomial cache evaluates to one without changing its retained coefficient table. -/
private theorem supplied_parameter {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (point : Canonical) :
    (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).polynomial.eval point = 1 := by
  let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
  exact (congrArg (fun polynomial => polynomial.eval point) supplied.polynomial_eq).trans
    (reversed_eval_one point)

/-- Seven original corrections of the accepted exact seed retain that same seed at every point. -/
private theorem supplied_model {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (point : Canonical) :
    (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model.value.eval point = seed.val.value := by
  let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
  have fixed : (1 : Canonical) * seed.val.value ^ 2 = 1 := by
    rewrite [seed_squared seed, Basic.one_mul]
    rfl
  have actual := supplied.model_eq point
  rewrite [supplied_parameter seed point] at actual
  exact actual.trans (refineValue_fixed 1 seed.val.value fixed 7)

/-- Every original retained root-sample cache has the same exact sample at every finite refinement index. -/
private theorem supplied_sample {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (point : Canonical)
    (actual : RootSamples (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model point)
    (index : Nat) : actual.sample index = seed.val.value := by
  have parameter : actual.parameter = 1 := actual.parameter_eq.trans (supplied_parameter seed point)
  have initial : actual.initial = seed.val.value := actual.initial_eq.trans (supplied_model seed point)
  have fixed : actual.parameter * actual.initial ^ 2 = 1 := by
    rewrite [parameter, initial, seed_squared seed, Basic.one_mul]
    rfl
  rewrite [actual.sample_fixed fixed index, parameter, initial, Basic.one_mul]
  rfl

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Every candidate of the original square-based preparation is possible at its original input name.

The actual apart state retains its based source state. That source is a
later sample of the original name, so original sample persistence supplies
the stated same-input relation without constructing a new comparison.
-/
private theorem square_prepared_possible {channel : CoherentNamed} {parameter : Canonical}
    (square : SquareRootProvenance.SquareIdentity channel parameter) (nonzero : parameter ≠ 0)
    (state : (SquareRootProvenance.prepared_of_square square nonzero).denominator.name.process.State)
    {candidate : Canonical}
    (possible : (SquareRootProvenance.prepared_of_square square nonzero).denominator.name.process.Possible
      state candidate) : channel.name.process.Possible channel.name.state candidate := by
  change (Name.Sampling.approximation channel.name).Possible state.source.source candidate at possible
  rcases possible with ⟨index, _order, equal⟩
  rewrite [equal]
  exact Process.Sampling.witnessAt_possible_start channel.name.process channel.name.state index

/-- Every possible reading of the actual supplied-model numerical preparation is the same exact seed.

This is a semantic readback of the original preparation and its actual
cached raw samples. The original guarded channel, state and finite request
are retained rather than replaced by an exact rational name.
-/
private theorem supplied_prepared_possible {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (point : Canonical)
    (inside : collar.box.Contains point)
    (state : (InverseModelRootChannels.RootChannel.prepare
      (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model
      (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model_small
      point inside).certificate.value.name.process.State)
    {candidate : Canonical}
    (possible : (InverseModelRootChannels.RootChannel.prepare
      (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model
      (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val).model_small
      point inside).certificate.value.name.process.Possible
        state candidate) : candidate = seed.val.value := by
  let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
  let samples := RootSamples.build supplied.model point
  have original := square_prepared_possible
    (InverseModelRootChannels.RootSamples.square samples supplied.model_small inside)
    (InverseModelRootChannels.parameter_nonzero supplied.model point inside) state possible
  change (samples.approximation supplied.model_small inside).Possible 0 candidate at original
  rcases original with ⟨index, _order, equal⟩
  exact equal.trans (supplied_sample seed point samples index)

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Sequence.Arithmetic

/-- Original scaled-root preparation preserves the exact value of every possible original source reading.

The prepared process keeps its own actual product sample and apart state.
Each product sample uses the exact factor and an actual sampled witness of
the original input, with no numerical-channel identification or new guard.
-/
private theorem scaled_prepared_possible (factor : Canonical) (nonzero : factor ≠ 0)
    (source : CoherentNamed) (apart : Name.Basic.Named.Apart source.name)
    (point : Canonical)
    (fixed : ∀ (state : source.name.process.State) {value : Canonical},
      source.name.process.Possible state value → value = point)
    (state : (ReciprocalRootNames.prepareScaled factor nonzero source apart).denominator.name.process.State)
    {candidate : Canonical}
    (possible : (ReciprocalRootNames.prepareScaled factor nonzero source apart).denominator.name.process.Possible
      state candidate) : candidate = factor * point := by
  change (Product.sampledProductApproximation (Coherence.exact factor).name source.name).Possible
    state.source candidate at possible
  rcases possible with ⟨index, _order, equal⟩
  have sourceValue := fixed source.name.state
    (Process.Sampling.witnessAt_possible_start source.name.process source.name.state index)
  have productValue : (Product.sampledProductApproximation (Coherence.exact factor).name source.name).sample index =
      factor * point := by
    rewrite [Product.sampledProductApproximation_sample]
    change factor * (Name.Sampling.approximation source.name).sample index = factor * point
    exact congrArg (fun value : Canonical => factor * value) sourceValue
  exact equal.trans productValue

/-- The exact original two-scale numerical presentation at the supplied cap's original parameter. -/
private abbrev actualPrepared {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter)) :=
  FormReadings.prepare (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val) parameter nonzero inside

/-- The exact two original scalar factors applied to the retained fixed seed. -/
private def affineValue {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical) : Canonical :=
  ((Primitives.point curve parameter)⁻¹) ^ (0 + 1) *
    (parameter ^ HyperellipticReciprocal.originOrder curve * seed.val.value)

/-- Every candidate of the actual two-scale affine presentation is its original two factors times the exact seed.

Both actual scale preparations and their original channels stay retained.
The first factor consumes the original numerical root cache, and the second
consumes the first prepared channel, including its actual apart state.
-/
private theorem actual_affine_possible {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (state : (actualPrepared seed parameter nonzero inside).certificate.value.name.process.State)
    {candidate : Canonical}
    (possible : (actualPrepared seed parameter nonzero inside).certificate.value.name.process.Possible
      state candidate) : candidate = affineValue seed parameter := by
  let prepared := actualPrepared seed parameter nonzero inside
  have reciprocal : ∀ (state : prepared.2.1.certificate.value.name.process.State) {value : Canonical},
      prepared.2.1.certificate.value.name.process.Possible state value →
        value = parameter ^ HyperellipticReciprocal.originOrder curve * seed.val.value := by
    intro state value possible
    exact scaled_prepared_possible (parameter ^ HyperellipticReciprocal.originOrder curve)
      (ExplicitField.pow_ne_zero_of_ne_zero nonzero _) prepared.1.certificate.value
      prepared.1.certificate.apart seed.val.value
      (supplied_prepared_possible seed (Primitives.point curve parameter) inside) state possible
  have pointNonzero : Primitives.point curve parameter ≠ 0 :=
    ExplicitField.pow_ne_zero_of_ne_zero nonzero (Primitives.degree curve)
  exact scaled_prepared_possible (((Primitives.point curve parameter)⁻¹) ^ (0 + 1))
    (ExplicitField.pow_ne_zero_of_ne_zero
      (ExplicitField.inv_ne_zero pointNonzero) _) prepared.2.1.certificate.value
    prepared.2.1.certificate.apart
    (parameter ^ HyperellipticReciprocal.originOrder curve * seed.val.value) reciprocal state possible

/-- The exact original full-form coefficient cache at this supplied numerical presentation. -/
private abbrev actualCoefficient {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter)) :=
  FormReadings.coefficient differential (actualPrepared seed parameter nonzero inside)

/-- The exact scalar readback of the original full coefficient and both original coordinate Jacobians. -/
private def coefficientValue {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical) : Canonical :=
  Primitives.tangent curve parameter *
    (-(((Primitives.point curve parameter)⁻¹) ^ 2) * (1 / affineValue seed parameter))

/-- The original retained numerator reading is one at every actual affine coordinate. -/
private theorem numerator_one (point : Canonical) :
    differential.scale * differential.numerator.eval point = 1 := by
  change (1 : Canonical) * (constant (1 : Canonical)).eval point = 1
  rewrite [eval_constant, Basic.one_mul]
  rfl

/-- Every possible original full-form coefficient reading is its exact two-Jacobian scalar value.

All original numerical channels, apartness guards and paired input states
remain in the original multiplication, reciprocal and finite power tree.
The actual retained affine candidates supply the exact denominator value;
no Laurent coefficient or operational comparison replaces this reading.
-/
private theorem actual_coefficient_possible {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (state : (actualCoefficient seed parameter nonzero inside).channel.name.process.State)
    {candidate : Canonical}
    (possible : (actualCoefficient seed parameter nonzero inside).channel.name.process.Possible
      state candidate) : candidate = coefficientValue seed parameter := by
  rcases possible with ⟨tangent, inner, tangentPossible, innerPossible, rfl⟩
  change tangent = Primitives.tangent curve parameter at tangentPossible
  rcases innerPossible with ⟨jacobian, form, jacobianPossible, formPossible, rfl⟩
  change jacobian = -(((Primitives.point curve parameter)⁻¹) ^ 2) at jacobianPossible
  rcases formPossible with ⟨numerator, power, numeratorPossible, powerPossible, rfl⟩
  change numerator = differential.scale * differential.numerator.eval (Primitives.point curve parameter)⁻¹
    at numeratorPossible
  rcases powerPossible with ⟨unit, reciprocal, unitPossible, reciprocalPossible, rfl⟩
  change unit = (1 : Canonical) at unitPossible
  rcases reciprocalPossible with ⟨one, denominator, onePossible, denominatorPossible, rfl⟩
  change one = (1 : Canonical) at onePossible
  have denominatorEqual := actual_affine_possible seed parameter nonzero inside _ denominatorPossible
  rewrite [tangentPossible, jacobianPossible, numeratorPossible,
    numerator_one, unitPossible, onePossible, denominatorEqual]
  change Primitives.tangent curve parameter *
    (-(((Primitives.point curve parameter)⁻¹) ^ 2) * (1 * (1 * (1 / affineValue seed parameter)))) =
      coefficientValue seed parameter
  unfold coefficientValue
  ring1

/-- The original odd chart maps the two opposite parameters to the same actual reciprocal coordinate. -/
private theorem point_neg (parameter : Canonical) :
    Primitives.point curve (-parameter) = Primitives.point curve parameter := by
  change (-parameter) ^ 2 = parameter ^ 2
  ring1

/-- The original tangent of the odd squared chart negates under an opposite parameter. -/
private theorem tangent_neg (parameter : Canonical) :
    Primitives.tangent curve (-parameter) = -(Primitives.tangent curve parameter) := by
  change (2 : Canonical) * (-parameter) ^ 1 = -((2 : Canonical) * parameter ^ 1)
  ring1

/-- Both original coordinate factors give opposite affine scalar readings at opposite parameters. -/
private theorem affineValue_neg {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical) :
    affineValue seed (-parameter) = -(affineValue seed parameter) := by
  unfold affineValue
  rewrite [point_neg]
  change ((Primitives.point curve parameter)⁻¹) ^ 1 * ((-parameter) ^ 1 * seed.val.value) =
    -(((Primitives.point curve parameter)⁻¹) ^ 1 * (parameter ^ 1 * seed.val.value))
  ring1

/-- The actual full-form scalar coefficient is even in the odd cap parameter.

The same original reciprocal coordinate has opposite tangent and affine
root factors. Their two signs cancel in the original guarded coefficient
readback; no equality of the two nominal root channels is asserted.
-/
private theorem coefficientValue_neg {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical) :
    coefficientValue seed (-parameter) = coefficientValue seed parameter := by
  unfold coefficientValue
  rewrite [point_neg, tangent_neg, affineValue_neg]
  change -(Primitives.tangent curve parameter) *
    (-(((Primitives.point curve parameter)⁻¹) ^ 2) * (1 * (-(affineValue seed parameter))⁻¹)) = _
  rewrite [Basic.Canonical.inv_neg]
  change -(Primitives.tangent curve parameter) *
    (-(((Primitives.point curve parameter)⁻¹) ^ 2) * (1 * -((affineValue seed parameter)⁻¹))) =
      Primitives.tangent curve parameter *
        (-(((Primitives.point curve parameter)⁻¹) ^ 2) * (1 * (affineValue seed parameter)⁻¹))
  ring1

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Branches.ClearSheetContinuation

/-- The actual original finite whole-form request reads its exact coefficient at every positive target. -/
private theorem actual_reading_value {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (parameter : Canonical)
    (nonzero : parameter ≠ 0) (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target) :
    (FormReadings.read differential (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val)
      parameter nonzero inside target positive).request.reading.value = coefficientValue seed parameter := by
  exact actual_coefficient_possible seed parameter nonzero inside _
    (FormReadings.read differential (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val)
      parameter nonzero inside target positive).request.reading.possible

/-- The actual canonical whole reading bank retains its exact seed-based producer and original bounded dyadic mesh. -/
private abbrev canonicalBank {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Rational) (positive : 0 < target) :=
  FormReadings.Circle.readings differential (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val)
    base nonzero unitBound collarBound actual depth left right target positive

/-- Every actual stored canonical bank occurrence has the exact full-form reading at its original left endpoint. -/
private theorem canonical_reading_value {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Rational) (positive : 0 < target)
    (index : Fin (dyadicEdges depth left right).length) :
    ((canonicalBank seed base nonzero unitBound collarBound actual depth left right target positive).get
      index).request.reading.value = coefficientValue seed
        (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) := by
  rewrite [Circle.Readings.get_readings]
  exact actual_reading_value seed _ _ _ target positive

/-- Read the integral sample of the actual ordered canonical bank with its retained allowance. -/
private abbrev canonicalSample {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Rational) (positive : 0 < target)
    (allowance : Option { value : Rational // 0 ≤ value }) :=
  ((canonicalBank seed base nonzero unitBound collarBound actual depth left right target positive).model
    allowance).integralSample

/-- The actual depth-zero bank contributes its original cell displacement, tangent and exact stored reading. -/
private theorem canonical_sample_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (left right : Endpoint) (target : Rational) (positive : 0 < target)
    (allowance : Option { value : Rational // 0 ≤ value }) :
    canonicalSample seed base nonzero unitBound collarBound actual 0 left right target positive allowance =
      Geometry.Gaussian.UnitCircle.Stereographic.Tangent.increment (right.parameter - left.parameter) *
        (velocity base left.parameter * coefficientValue seed (actual.val.point left.parameter)) := by
  change (PathModel.mk ((canonicalBank seed base nonzero unitBound collarBound actual 0 left right
    target positive).cells none allowance)).integralSample = _
  rewrite [Circle.Readings.cells_zero, PathModel.singleton_integralSample,
    FormReadings.Circle.readingCell.integralSample]
  exact congrArg (fun value : Canonical =>
      Geometry.Gaussian.UnitCircle.Stereographic.Tangent.increment (right.parameter - left.parameter) *
        (velocity base left.parameter * value))
    (canonical_reading_value seed base nonzero unitBound collarBound actual 0 left right target positive
      ⟨0, Nat.zero_lt_succ 0⟩)

/-- The original same-depth subdivision adds its exact two canonical half-bank samples in the original order. -/
private theorem canonical_sample_succ {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (depth : Nat) (left right : Endpoint) (target : Rational) (positive : 0 < target)
    (allowance : Option { value : Rational // 0 ≤ value }) :
    let middle : Endpoint :=
      ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
    canonicalSample seed base nonzero unitBound collarBound actual
        (depth + 1) left right target positive allowance =
      canonicalSample seed base nonzero unitBound collarBound actual depth left middle target positive allowance +
        canonicalSample seed base nonzero unitBound collarBound actual
          depth middle right target positive allowance := by
  dsimp only
  let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
  let middle : Endpoint :=
    ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
  let stored := canonicalBank seed base nonzero unitBound collarBound actual
    (depth + 1) left right target positive
  have cells := Circle.Readings.split_cells stored none allowance
  have halves := Circle.Readings.split_readings differential supplied base nonzero
    unitBound collarBound actual depth left right target positive
  have leftBank := congrArg Prod.fst halves
  have rightBank := congrArg Prod.snd halves
  have leftSample := congrArg
    (fun bank : Circle.Readings differential supplied base unitBound collarBound actual
        depth left middle target => (bank.model allowance).integralSample) leftBank
  have rightSample := congrArg
    (fun bank : Circle.Readings differential supplied base unitBound collarBound actual
        depth middle right target => (bank.model allowance).integralSample) rightBank
  have sameCells := congrArg
    (fun cells => (PathModel.mk cells).integralSample) cells
  exact sameCells.trans ((PathModel.integralSample_mk_append _ _).trans
    (congrArg₂ (fun first last : Canonical => first + last) leftSample rightSample))

/-- Actual circle caches on opposite retained bases have opposite points at each original scalar parameter. -/
private theorem circle_point_neg (base : Canonical)
    (actual : { value : RationalCurve // value = circle base })
    (opposite : { value : RationalCurve // value = circle (-base) }) (time : Rational) :
    opposite.val.point time = -(actual.val.point time) := by
  rewrite [opposite.property, actual.property, point_eq_base_mul, point_eq_base_mul]
  ring1

/-- The original circle tangent negates at the same parameter on the opposite retained base. -/
private theorem velocity_neg (base : Canonical) (time : Rational) :
    velocity (-base) time = -(velocity base time) := by
  unfold velocity
  ring1

/-- Opposite actual quarter banks have opposite complete finite samples at every common depth.

The original endpoint records, two independent requests and allowances
remain distinct. The same original partition laws retain both canonical
half banks, and each actual scalar cell cancels using the proved even
full-form reading and opposite original tangent.
-/
private theorem opposite_quarter_sample {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base oppositeBase : Canonical)
    (same : oppositeBase = -base) (nonzero : base ≠ 0)
    (oppositeNonzero : oppositeBase ≠ 0) (unitBound : Norm.Basic.normSq base ≤ 1)
    (oppositeUnitBound : Norm.Basic.normSq oppositeBase ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (oppositeCollarBound : Norm.Basic.normSq oppositeBase ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (actual : { value : RationalCurve // value = circle base })
    (opposite : { value : RationalCurve // value = circle oppositeBase })
    (depth : Nat) (left right : Endpoint) (firstTarget lastTarget : Rational)
    (firstPositive : 0 < firstTarget) (lastPositive : 0 < lastTarget)
    (firstAllowance lastAllowance : Option { value : Rational // 0 ≤ value }) :
    canonicalSample seed oppositeBase oppositeNonzero oppositeUnitBound oppositeCollarBound opposite
        depth left right lastTarget lastPositive lastAllowance =
      -(canonicalSample seed base nonzero unitBound collarBound actual
        depth left right firstTarget firstPositive firstAllowance) := by
  cases same
  induction depth generalizing left right with
  | zero =>
      rewrite [canonical_sample_zero, canonical_sample_zero,
        circle_point_neg base actual opposite left.parameter, coefficientValue_neg, velocity_neg]
      ring1
  | succ depth previous =>
      rewrite [canonical_sample_succ, canonical_sample_succ, previous, previous]
      ring1

/-- The exact same supplied cap value retained throughout the original loop programmes. -/
private abbrev suppliedCap {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) :=
  ReciprocalInnerInverse.Data.ofSeed curve collar seed.val

/-- A built original quarter stage reads its same canonical numerical bank and literal saved budget. -/
private theorem actual_quarter_sample {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish)
    (quarter : Fin Integral.quarters.length) (index : Nat) :
    let quarterValue := (Circle.Loop.programs (differential := differential)
      (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges).get quarter
    (quarterValue.2.2.stage index).sample =
      canonicalSample seed (Integral.quarterBase base (Integral.quarters[quarter.val]'quarter.isLt))
        (Integral.quarterBase_ne_zero base nonzero _) ((Integral.quarterBase_normSq base _).trans_le unitBound)
        ((Integral.quarterBase_normSq base _).trans_le collarBound) (entries.get quarter).1 index
        Circle.Loop.start Circle.Loop.finish
        (Geometric.Basic.quarterRadius 1 index)
        (Geometric.Basic.quarterRadius_pos (by decide) index)
        (some ⟨quarterValue.2.1.val.val * Geometric.Basic.quarterRadius 1 index,
          Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct quarterValue.2.1.val.property
            (Geometric.Basic.quarterRadius_nonneg (by decide) index)⟩) := by
  let quarterKind := Circle.Loop.QuarterProgram (differential := differential)
    (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
    cached bounds (Integral.quarters[quarter.val]'quarter.isLt) (entries.get quarter) edges
  let sampleReadback := fun value : quarterKind =>
    (value.2.2.stage index).sample =
      canonicalSample seed (Integral.quarterBase base (Integral.quarters[quarter.val]'quarter.isLt))
        (Integral.quarterBase_ne_zero base nonzero _) ((Integral.quarterBase_normSq base _).trans_le unitBound)
        ((Integral.quarterBase_normSq base _).trans_le collarBound) (entries.get quarter).1 index
        Circle.Loop.start Circle.Loop.finish
        (Geometric.Basic.quarterRadius 1 index)
        (Geometric.Basic.quarterRadius_pos (by decide) index)
        (some ⟨value.2.1.val.val * Geometric.Basic.quarterRadius 1 index,
          Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct value.2.1.val.property
            (Geometric.Basic.quarterRadius_nonneg (by decide) index)⟩)
  have whole := Programs.get_programs (differential := differential)
    (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
    entries cached pairs degreeBound bounds edges quarter
  have canonical := FormReadings.Circle.program_stage_sample
    (differential := differential) (cap := suppliedCap seed)
    (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
    (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
    (actual := (entries.get quarter).1) (cached.onQuarter _) (Integral.quarterBase_ne_zero base nonzero _)
    pairs degreeBound bounds Circle.Loop.start Circle.Loop.finish edges index
  exact Eq.mpr (congrArg sampleReadback whole) canonical

/-- The actual original four-quarter full-form programme has exactly zero sample at every finite stage.

The complete original quarter programmes, numerical banks, independent
budgets and ordered balanced sum remain unchanged. Two exact scalar base
identities pair their same-depth original reading cells antipodally.
-/
private theorem loop_sample_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish) (index : Nat) :
    (((Circle.Loop.programs (differential := differential)
      (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges).concatenate.1.stage index).sample) = 0 := by
  let stored := Circle.Loop.programs (differential := differential)
    (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
    entries cached pairs degreeBound bounds edges
  let first : Fin Integral.quarters.length := ⟨0, by decide +kernel⟩
  let second : Fin Integral.quarters.length := ⟨1, by decide +kernel⟩
  let third : Fin Integral.quarters.length := ⟨2, by decide +kernel⟩
  let fourth : Fin Integral.quarters.length := ⟨3, by decide +kernel⟩
  let firstValue := ((stored.get first).2.2.stage index).sample
  let secondValue := ((stored.get second).2.2.stage index).sample
  let thirdValue := ((stored.get third).2.2.stage index).sample
  let fourthValue := ((stored.get fourth).2.2.stage index).sample
  have firstReadback := actual_quarter_sample seed base nonzero unitBound collarBound bounds
    entries cached edges first index
  have secondReadback := actual_quarter_sample seed base nonzero unitBound collarBound bounds
    entries cached edges second index
  have thirdReadback := actual_quarter_sample seed base nonzero unitBound collarBound bounds
    entries cached edges third index
  have fourthReadback := actual_quarter_sample seed base nonzero unitBound collarBound bounds
    entries cached edges fourth index
  have thirdBase : Integral.quarterBase base (Integral.quarters[third.val]'third.isLt) =
      -(Integral.quarterBase base (Integral.quarters[first.val]'first.isLt)) := by
    change base * (-1 : Canonical) = -(base * (1 : Canonical))
    ring1
  have fourthBase : Integral.quarterBase base (Integral.quarters[fourth.val]'fourth.isLt) =
      -(Integral.quarterBase base (Integral.quarters[second.val]'second.isLt)) := by
    change base * (⟨0, -1⟩ : Canonical) = -(base * (⟨0, 1⟩ : Canonical))
    have scalar : (⟨0, -1⟩ : Canonical) = -(⟨0, 1⟩ : Canonical) := by decide +kernel
    exact (congrArg (fun value : Canonical => base * value) scalar).trans (by ring1)
  let precision := Geometric.Basic.quarterRadius 1 index
  have precisionPositive : 0 < precision :=
    Geometric.Basic.quarterRadius_pos (by decide) index
  let allowance := fun quarter : Fin Integral.quarters.length =>
    (some ⟨(stored.get quarter).2.1.val.val * precision,
      Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (stored.get quarter).2.1.val.property
        precisionPositive.le⟩ : Option { value : Rational // 0 ≤ value })
  have upper := opposite_quarter_sample seed _ _ thirdBase
    (Integral.quarterBase_ne_zero base nonzero _) (Integral.quarterBase_ne_zero base nonzero _)
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    (entries.get first).1 (entries.get third).1 index Circle.Loop.start Circle.Loop.finish
    precision precision precisionPositive precisionPositive (allowance first) (allowance third)
  have lower := opposite_quarter_sample seed _ _ fourthBase
    (Integral.quarterBase_ne_zero base nonzero _) (Integral.quarterBase_ne_zero base nonzero _)
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    (entries.get second).1 (entries.get fourth).1 index Circle.Loop.start Circle.Loop.finish
    precision precision precisionPositive precisionPositive (allowance second) (allowance fourth)
  have upperValue : thirdValue = -firstValue :=
    thirdReadback.trans (upper.trans (congrArg (fun value : Canonical => -value) firstReadback.symm))
  have lowerValue : fourthValue = -secondValue :=
    fourthReadback.trans (lower.trans (congrArg (fun value : Canonical => -value) secondReadback.symm))
  exact (Programs.concatenate_sample stored index).trans (by
    change (firstValue + secondValue) + (thirdValue + fourthValue) = 0
    rewrite [upperValue, lowerValue]
    ring1)

/-- Whole retained source and programme equalities preserve the same zero finite samples.

The exact supplied programme bank and complete produced result remain the
retained values. Their original factory equations transport the proved
scalar sample without rebuilding any bank, stage or comparison.
-/
private theorem retained_loop_sample_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish)
    (stored : Programs.Built (differential := differential)
      (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges)
    (source : { value : stored.val.Result // value = stored.val.concatenate }) (index : Nat) :
    (source.val.1.stage index).sample = 0 := by
  have sameSource := congrArg (fun value : stored.val.Result => (value.1.stage index).sample) source.property
  have samePrograms := congrArg
    (fun value : Programs (differential := differential)
      (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
      entries cached bounds edges => (value.concatenate.1.stage index).sample) stored.property
  exact sameSource.trans (samePrograms.trans
    (loop_sample_zero seed base nonzero unitBound collarBound bounds entries cached edges index))

/-- Every possible value of the actual retained total-form output is its proved exact zero sample.

The output keeps the same certified programme and original sequence-backed
state. Its explicit finite later-sample witness consumes that same
retained source's all-index finite-sample identity.
-/
private theorem retained_output_possible_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish)
    (stored : Programs.Built (differential := differential)
      (cap := suppliedCap seed) (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges)
    (source : { value : stored.val.Result // value = stored.val.concatenate })
    (state : source.val.1.output.name.process.State) {candidate : Canonical}
    (possible : source.val.1.output.name.process.Possible state candidate) : candidate = 0 := by
  change source.val.1.approximation.Possible state candidate at possible
  rcases possible with ⟨index, _order, equal⟩
  exact equal.trans
    (retained_loop_sample_zero seed base nonzero unitBound collarBound bounds
      entries cached edges stored source index)

/-- Every possible value of the original stored normalized quotient output is exactly zero.

The complete coherent-name equality transports the same original state to
that literal cached quotient. Its original division tree retains both the
zero numerator and the actual guarded logarithmic denominator; the latter
is not replaced or identified with a coefficient channel.
-/
private theorem normalized_output_possible_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish)
    (retained : Programs.Normalization.Sources
      (differential := differential) (cap := suppliedCap seed) (data := data)
      nonzero unitBound collarBound pairs degreeBound bounds edges)
    (state : retained.channel.name.process.State) {candidate : Canonical}
    (possible : retained.channel.name.process.Possible state candidate) : candidate = 0 := by
  have channelEq : retained.channel =
      Name.Coherent.CoherentNamed.div retained.source.val.1.output
        retained.quotient.val.prepared.denominator retained.quotient.val.prepared.apart :=
    retained.channel_output.trans retained.quotient.val.output_eq
  have original := Name.Coherent.CoherentNamed.possible_castState channelEq state possible
  rcases original with ⟨numerator, denominator, numeratorPossible, _denominatorPossible, equal⟩
  have zero := retained_output_possible_zero seed base nonzero unitBound collarBound bounds
    retained.circuit.1 retained.cached edges retained.programs retained.source _ numeratorPossible
  exact equal.trans ((congrArg (fun value : Canonical => value / denominator) zero).trans
    (ExplicitField.zero_div denominator))

/-- Every original normalized physical name sample is exactly zero at its same actual finite index.

The original sampling state and its original finite possible witness are
unchanged. The whole physical-loop identity supplies the exact numerical
readback of that same witness, without enumerating a replacement mesh or
substituting another output name.
-/
private theorem normalized_sample_zero {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds (suppliedCap seed).clearance (suppliedCap seed).model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root (suppliedCap seed).polynomial)
    (edges : DyadicEdges 0 Circle.Loop.start Circle.Loop.finish)
    (retained : Programs.Normalization.Sources
      (differential := differential) (cap := suppliedCap seed) (data := data)
      nonzero unitBound collarBound pairs degreeBound bounds edges) (index : Nat) :
    (Name.Sampling.approximation retained.channel.name).sample index = 0 := by
  exact normalized_output_possible_zero seed base nonzero unitBound collarBound bounds edges retained _
    (Process.Sampling.witnessAt_possible retained.channel.name.process retained.channel.name.state index)

end Symmetry

/-- Inspect an actual automatically found exact sample before constructing its separately requested model. -/
public def checkExactSeed (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          withPreparedOrigin supplied fun cached => do
            Purelib.System.IO.println s!"CAP_EXACT_SEED_MODEL_INITIAL {sampleText cached.samples.initial}"
            (← IO.getStdout).flush

/-- Pay the original anchor on the newly requested exact-seed model, retaining the same original leading-sheet owner. -/
public def checkExactSeedAnchor (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          (← IO.getStdout).flush
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          withPreparedOrigin supplied fun cached => do
            Purelib.System.IO.println s!"CAP_EXACT_SEED_MODEL_INITIAL {sampleText cached.samples.initial}"
            (← IO.getStdout).flush
            withAnchorRequest supplied cached fun request => do
              Purelib.System.IO.println
                s!"CAP_EXACT_SEED_ANCHOR_REQUEST {request.2.1.val.leftIndex},{request.2.1.val.rightIndex}"
              Purelib.System.IO.println s!"CAP_EXACT_SEED_ANCHOR_INDEX {request.2.2.2.val}"
              (← IO.getStdout).flush
              Purelib.System.IO.println "CAP_EXACT_SEED_ANCHOR_SAMPLE_BEGIN"
              (← IO.getStdout).flush
              withAnchorSample supplied cached request fun anchor => do
                Purelib.System.IO.println s!"CAP_EXACT_SEED_ANCHOR_PASS {sampleText anchor.value}"
                (← IO.getStdout).flush

/-- Assign the original winding owner using the actual anchor from the separately requested same-owner exact model. -/
public def checkExactSeedAssignment (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          (← IO.getStdout).flush
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          withPreparedOrigin supplied fun cached => do
            Purelib.System.IO.println s!"CAP_EXACT_SEED_MODEL_INITIAL {sampleText cached.samples.initial}"
            (← IO.getStdout).flush
            withAnchorRequest supplied cached fun request => do
              Purelib.System.IO.println s!"CAP_EXACT_SEED_ANCHOR_INDEX {request.2.2.2.val}"
              (← IO.getStdout).flush
              withAnchorSample supplied cached request fun anchor => do
                Purelib.System.IO.println s!"CAP_EXACT_SEED_ANCHOR_PASS {sampleText anchor.value}"
                (← IO.getStdout).flush
                Purelib.System.IO.println "CAP_EXACT_SEED_ASSIGNMENT_BEGIN"
                (← IO.getStdout).flush
                withAssignedOrigin supplied cached anchor fun owner => do
                  Purelib.System.IO.println
                    s!"CAP_EXACT_SEED_ASSIGNMENT_PASS {sampleText owner.track.initial.box.anchor}"
                  (← IO.getStdout).flush

/-- Complete original Point.build with the literal numerical cache of the same-owner exact model. -/
public def checkExactSeedAttachment (sheet : Fin 2) : IO Unit := do
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          (← IO.getStdout).flush
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          withPreparedOrigin supplied fun cached => do
            Purelib.System.IO.println s!"CAP_EXACT_SEED_MODEL_INITIAL {sampleText cached.samples.initial}"
            (← IO.getStdout).flush
            Purelib.System.IO.println "CAP_EXACT_SEED_ATTACHMENT_BEGIN"
            (← IO.getStdout).flush
            withAttachedOrigin supplied cached fun origin => do
              Purelib.System.IO.println
                s!"CAP_EXACT_SEED_ATTACHMENT_PASS {sampleText origin.channel.samples.initial}"
              (← IO.getStdout).flush

/-- Transport the original actual sampled quotient state through its retained complete output equation. -/
private def formerQuotientSampleState {Model : Type u} {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel) (index : Nat) :
    (quotient.prepared.quotient program.output).name.process.State :=
  Process.Sampling.castState
    (congrArg (fun output : Name.Coherent.CoherentNamed => output.name.process) quotient.output_eq)
    (Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index)

/-- Transport the original actual sampled quotient state through its retained complete output equation. -/
private def quotientSampleState {Model : Type u} {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel) (index : Nat)
    (cached : { value : quotient.output.name.process.State // value =
      Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index } :=
        ⟨Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index, rfl⟩) :
    (quotient.prepared.quotient program.output).name.process.State :=
  Process.Sampling.castState
    (congrArg (fun output : Name.Coherent.CoherentNamed => output.name.process) quotient.output_eq)
    cached.val

/-- Omission preserves the original complete same-index quotient-state transport. -/
private theorem quotientSampleState_default_eq_former {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel) (index : Nat) :
    quotientSampleState program quotient index = formerQuotientSampleState program quotient index := (rfl)

/-- A supplied same-index state is consumed literally and retains the original complete transported state. -/
private theorem quotientSampleState_cached_eq_default {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel) (index : Nat)
    (cached : { value : quotient.output.name.process.State // value =
      Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index }) :
    quotientSampleState program quotient index cached = quotientSampleState program quotient index := by
  rcases cached with ⟨value, same⟩
  cases same
  rfl

/-- The original quotient sample reads its actual selected original stage and retained denominator witness. -/
private theorem quotient_sample_readback {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel) (index : Nat) :
    (Name.Sampling.approximation quotient.output.name).sample index =
      (program.stage (quotientSampleState program quotient index).1).sample /
        (quotient.prepared.denominator.name.process.witness
          (quotientSampleState program quotient index).2).val := by
  cases quotient with
  | mk prepared output same =>
      cases same
      rfl

/-- Read the actual first retained quarter curve's initial point as the original circuit radius. -/
private def retainedBase {base : Canonical} {nonzero : base ≠ 0} (circuit : Integral.Circuit base nonzero) :
    Canonical :=
  (circuit.1.get ⟨0, by decide +kernel⟩).1.val.point 0

/-- The original quarter-start readback identifies that literal retained point with its circuit base. -/
private theorem retainedBase_eq {base : Canonical} {nonzero : base ≠ 0}
    (circuit : Integral.Circuit base nonzero) : retainedBase circuit = base := by
  unfold retainedBase
  rewrite [Integral.Entries.start]
  change base * 1 = base
  exact Basic.mul_one base

/-- Retain an original quotient reading at its actual requested state using a proved exact numerator sample.

The stored radius is the original division radius after cancellation of
the unchanged guarded denominator centre. The state, value and radius
are those of the actual quotient; neither input channel is replaced.
-/
private def physicalReading {Model : Type u} {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel)
    (zero : ∀ index, (program.stage index).sample = 0) (index : Nat) :
    Observation.Reading quotient.output := by
  let state := Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index
  let actual := quotientSampleState program quotient index ⟨state, rfl⟩
  have sampleEq : (Name.Sampling.approximation quotient.output.name).sample index = 0 :=
    (quotient_sample_readback program quotient index).trans
      ((congrArg (fun value : Canonical => value /
        (quotient.prepared.denominator.name.process.witness actual.2).val) (zero actual.1)).trans
        (ExplicitField.zero_div _))
  have possible := Process.Sampling.witnessAt_possible quotient.output.name.process quotient.output.name.state index
  have zeroPossible : quotient.output.name.process.Possible state 0 :=
    Eq.mp (congrArg (fun value : Canonical => quotient.output.name.process.Possible state value) sampleEq) possible
  refine ⟨state, 0, zeroPossible,
    2 * program.approximation.radiusSq actual.1 / quotient.prepared.apart.certificate.lowerSq, ?_⟩
  cases quotient with
  | mk prepared output same =>
      cases same
      exact (Enclosure.Ball.div_radiusSq_of_center_zero
        (program.output.name.process.ball actual.1)
        (prepared.denominator.name.process.ball actual.2)
        (Process.Apart.atState prepared.apart.certificate actual.2) (zero actual.1)).symm

/-- The retained physical reading has the exact original requested sampling state. -/
private theorem physicalReading_state {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel)
    (zero : ∀ index, (program.stage index).sample = 0) (index : Nat) :
    (physicalReading program quotient zero index).state =
      Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index := (rfl)

/-- The same original reading is the actual original quotient's finite sample value. -/
private theorem physicalReading_value {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel)
    (zero : ∀ index, (program.stage index).sample = 0) (index : Nat) :
    (physicalReading program quotient zero index).value =
      (Name.Sampling.approximation quotient.output.name).sample index := by
  change 0 = _
  rewrite [quotient_sample_readback program quotient index, zero, ExplicitField.zero_div]
  rfl

/-- Certified physical evaluation preserves the complete original same-state reading constructor.

The supplied physical identity only selects the same original finite
witness value. The radius readback proves whole reading equality,
including the unchanged state and original visible squared radius.
-/
private theorem physicalReading_eq_original {Model : Type u}
    {operations : Integration.CertifiedProgram.ModelOperations Model}
    (program : Integration.CertifiedProgram.Program operations) {channel : Name.Coherent.CoherentNamed}
    (quotient : Division.Prepared.Quotient program.output channel)
    (zero : ∀ index, (program.stage index).sample = 0) (index : Nat) :
    physicalReading program quotient zero index =
      Observation.Reading.retain quotient.output
        (Process.Sampling.stateAt quotient.output.name.process quotient.output.name.state index)
        ((Name.Sampling.approximation quotient.output.name).sample index)
        (Process.Sampling.witnessAt_possible quotient.output.name.process quotient.output.name.state index) := by
  let reading := physicalReading program quotient zero index
  have valueEq := physicalReading_value program quotient zero index
  have actual :
      (⟨reading.value, reading.possible⟩ :
        { value : Canonical // quotient.output.name.process.Possible reading.state value }) =
      quotient.output.name.process.witness reading.state :=
    Subtype.ext valueEq
  exact (Observation.Reading.eq_retain reading).trans
    (congrArg (fun value : { value : Canonical // quotient.output.name.process.Possible reading.state value } =>
      Observation.Reading.retain quotient.output reading.state value.val value.property) actual)

/-- The actual retained ramified coefficient pivot vanishes by its original table theorem. -/
private theorem coefficient_pivot_zero :
    Coefficient.coefficient table.val (Primitives.parameterOrder curve) = 0 :=
  Primitives.parameterPolynomial_odd_pivot principal (by decide +kernel) table

/-- Every possible reading of the actual origin-dependent coefficient product is zero.

The reciprocal keeps its original origin channel and guard. The original
right factor is the exact pivot from the retained table, whose scalar
readback is supplied by the original odd-pivot theorem.
-/
private theorem coefficient_possible_zero {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0)
    (state : (Programs.Normalization.coefficientChannel
      (origin := origin) table).name.process.State) {candidate : Canonical}
    (possible : (Programs.Normalization.coefficientChannel
      (origin := origin) table).name.process.Possible state candidate) : candidate = 0 := by
  rcases possible with ⟨first, last, _firstPossible, lastPossible, same⟩
  exact same.trans ((congrArg (fun value : Canonical => first * value)
    (lastPossible.trans coefficient_pivot_zero)).trans (Basic.mul_zero first))

/-- The actual original coefficient channel has zero visible radius at every one of its own retained states. -/
private theorem coefficient_radius_zero {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0)
    (state : (Programs.Normalization.coefficientChannel (origin := origin) table).name.process.State) :
    ((Programs.Normalization.coefficientChannel (origin := origin) table).name.process.ball state).radiusSq = 0 := by
  change 4 * (_ * Norm.Basic.normSq (Coefficient.coefficient table.val (Primitives.parameterOrder curve)) +
    _ * 0) + 2 * (_ * 0) = 0
  rewrite [coefficient_pivot_zero, Norm.Basic.normSq_zero]
  ring1

/-- Retain the original coefficient sample, supplied whole channel and exact radius at the requested state.

The final cache is the actual coefficient-channel construction, with its
whole factory equality. Sampling consumes that supplied channel once;
the retained state transport preserves the original nominal endpoint.
Omission keeps the original complete coefficient-reading constructor.
-/
private def coefficientReading {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat)
    (cached : { value : Name.Coherent.CoherentNamed //
      value = Programs.Normalization.coefficientChannel (origin := origin) table } :=
        ⟨Programs.Normalization.coefficientChannel (origin := origin) table, rfl⟩) :
    Observation.Reading
      (Programs.Normalization.coefficientChannel (origin := origin) table) := by
  let channel := Programs.Normalization.coefficientChannel (origin := origin) table
  let actual := Process.Sampling.stateAt cached.val.name.process cached.val.name.state index
  let state := Name.Coherent.CoherentNamed.castState cached.property actual
  have stateEq : state = Process.Sampling.stateAt channel.name.process channel.name.state index := by
    rcases cached with ⟨value, same⟩
    cases same
    rfl
  have possible := Process.Sampling.witnessAt_possible channel.name.process channel.name.state index
  have sampleEq : (Name.Sampling.approximation channel.name).sample index = 0 :=
    coefficient_possible_zero origin _ possible
  have zeroPossible : channel.name.process.Possible state 0 := by
    rewrite [stateEq]
    exact Eq.mp (congrArg (fun value : Canonical => channel.name.process.Possible
      (Process.Sampling.stateAt channel.name.process channel.name.state index) value) sampleEq) possible
  exact ⟨state, 0, zeroPossible, 0, (coefficient_radius_zero origin state).symm⟩

/-- Verification-only complete former coefficient reading at its original requested state. -/
private def formerCoefficientReading {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat) :
    Observation.Reading
      (Programs.Normalization.coefficientChannel (origin := origin) table) := by
  let channel := Programs.Normalization.coefficientChannel (origin := origin) table
  let state := Process.Sampling.stateAt channel.name.process channel.name.state index
  have possible := Process.Sampling.witnessAt_possible channel.name.process channel.name.state index
  have sampleEq : (Name.Sampling.approximation channel.name).sample index = 0 :=
    coefficient_possible_zero origin state possible
  have zeroPossible : channel.name.process.Possible state 0 :=
    Eq.mp (congrArg (fun value : Canonical => channel.name.process.Possible state value) sampleEq) possible
  refine ⟨state, 0, zeroPossible, 0, ?_⟩
  change 0 = 4 * (_ * Norm.Basic.normSq (Coefficient.coefficient table.val (Primitives.parameterOrder curve)) +
    _ * 0) + 2 * (_ * 0)
  rewrite [coefficient_pivot_zero, Norm.Basic.normSq_zero]
  ring1

/-- Omission retains the complete former coefficient reading for every actual origin and index. -/
private theorem coefficientReading_default_eq_former {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat) :
    coefficientReading origin index = formerCoefficientReading origin index := (rfl)

/-- Supplying the actual coefficient channel retains the complete original same-index reading. -/
private theorem coefficientReading_cached_eq_default {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat)
    (cached : { value : Name.Coherent.CoherentNamed //
      value = Programs.Normalization.coefficientChannel (origin := origin) table }) :
    coefficientReading origin index cached = coefficientReading origin index := by
  rcases cached with ⟨value, same⟩
  cases same
  rfl

/-- The reading state consumes the supplied whole coefficient channel's actual original indexed state literally. -/
private theorem coefficientReading_state {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat)
    (cached : { value : Name.Coherent.CoherentNamed //
      value = Programs.Normalization.coefficientChannel (origin := origin) table }) :
    (coefficientReading origin index cached).state = Name.Coherent.CoherentNamed.castState cached.property
      (Process.Sampling.stateAt cached.val.name.process cached.val.name.state index) := (rfl)

/-- The retained coefficient reading is the same original channel sample at its actual requested index. -/
private theorem coefficientReading_value {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat)
    (cached : { value : Name.Coherent.CoherentNamed //
      value = Programs.Normalization.coefficientChannel (origin := origin) table } :=
        ⟨Programs.Normalization.coefficientChannel (origin := origin) table, rfl⟩) :
    (coefficientReading origin index cached).value =
      (Name.Sampling.approximation
        (Programs.Normalization.coefficientChannel
          (origin := origin) table).name).sample index :=
  (coefficient_possible_zero origin _
    (Process.Sampling.witnessAt_possible _ _ index)).symm

/-- Certified coefficient evaluation preserves the complete original same-state reading constructor. -/
private theorem coefficientReading_eq_original {cap : ReciprocalInnerInverse.Data curve collar}
    (origin : Owners.Point cap 0) (index : Nat) :
    coefficientReading origin index = Observation.Reading.retain
      (Programs.Normalization.coefficientChannel (origin := origin) table)
      (Process.Sampling.stateAt
        (Programs.Normalization.coefficientChannel (origin := origin) table).name.process
        (Programs.Normalization.coefficientChannel (origin := origin) table).name.state index)
      ((Name.Sampling.approximation
        (Programs.Normalization.coefficientChannel
          (origin := origin) table).name).sample index)
      (Process.Sampling.witnessAt_possible _ _ index) := by
  let channel := Programs.Normalization.coefficientChannel (origin := origin) table
  let reading := coefficientReading origin index
  have actual :
      (⟨reading.value, reading.possible⟩ : { value : Canonical // channel.name.process.Possible reading.state value }) =
      channel.name.process.witness reading.state :=
    Subtype.ext (coefficientReading_value origin index)
  exact (Observation.Reading.eq_retain reading).trans
    (congrArg (fun value : { value : Canonical // channel.name.process.Possible reading.state value } =>
      Observation.Reading.retain channel reading.state value.val value.property) actual)

/-- Every actual retained total-form source has zero original finite samples on this supplied cap.

This compact proposition retains the original source/programme indices
and factory equalities. It is an optional certified evaluation request,
not a different physical channel or a replacement integration programme.
-/
private def PhysicalZero (cap : ReciprocalInnerInverse.Data curve collar) : Prop :=
  ∀ {base : Canonical} (nonzero : base ≠ 0) (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (retained : Programs.Normalization.Sources
      (differential := differential) (cap := cap) (data := data)
      nonzero unitBound collarBound pairs degreeBound bounds edges)
    (index : Nat), (retained.source.val.1.stage index).sample = 0

/-- The same-owner exact seed proves the original physical-sample certificate for every retained request source. -/
private theorem physicalZero_of_seed {cap : ReciprocalInnerInverse.Data curve collar}
    {bank : List ExactCandidate} (seed : ExactSeed cap bank) :
    PhysicalZero (ReciprocalInnerInverse.Data.ofSeed curve collar seed.val) := by
  intro base nonzero unitBound collarBound root bounds retained index
  exact Symmetry.retained_loop_sample_zero seed base nonzero unitBound collarBound bounds
    retained.circuit.1 retained.cached edges retained.programs retained.source index

/-- Execute the original full-form loop body on the literal supplied cap and its own actual retained owners. -/
@[noinline] private def formerRunCap (cap : ReciprocalInnerInverse.Data curve collar)
    (inspectOnly : Bool := false) : IO Unit := do
  Purelib.System.IO.println "CAP_MODEL_PASS"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_ROOT_BOUNDS"
  (← IO.getStdout).flush
  let root := InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model
  let bounds := InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial
  Purelib.System.IO.println "CAP_PHASE_ORIGIN"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_BEGIN"
  (← IO.getStdout).flush
  withPreparedOrigin cap fun cached => do
    Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_PASS"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_BEGIN"
    (← IO.getStdout).flush
    withAttachedOrigin cap cached fun origin => do
      Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_PASS"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_PHASE_FACTOR_ANCHOR"
      (← IO.getStdout).flush
      let anchor := RootCoordinates.originJetFactor_prepared origin jet
      let setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor :=
        ⟨RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor, rfl⟩
      Purelib.System.IO.println "CAP_PHASE_ERROR_BOUNDS"
      (← IO.getStdout).flush
      let errorBounds := Circle.Readings.Jets.prepareErrorBound origin jet remainder data.1
      Purelib.System.IO.println "CAP_PHASE_FULL_FORM_REQUEST"
      (← IO.getStdout).flush
      let retained := Programs.Normalization.request
        (data := data) (principal := principal) (primitive := primitive) (remainder := remainder)
        origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds 0 0 1 (by decide +kernel)
      let quotient := retained.1.quotient.val
      let reference := Programs.Normalization.coefficientChannel (origin := origin) table
      let compared := retained.2.withSamples (Name.Sampling.approximation quotient.output.name)
        (Name.Sampling.approximation reference.name)
        (fun index => congrArg (fun value : Name.Coherent.CoherentNamed =>
          (Name.Sampling.approximation value.name).sample index) retained.1.channel_output.symm) (fun _ => rfl)
      if inspectOnly then
        let source := retained.1.source.val.1
        let actualQuotient := retained.1.quotient.val
        let state := quotientSampleState source actualQuotient compared.leftIndex
        let depth : Nat := state.1
        Purelib.System.IO.println s!"CAP_PAYMENT_BASE {sampleText (retainedBase retained.1.circuit)}"
        Purelib.System.IO.println s!"CAP_PAYMENT_ERROR_SCALE {source.errorScale.num}/{source.errorScale.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_CENTER_BOUND {source.centerBound.num}/{source.centerBound.den}"
        let denominator := actualQuotient.prepared.denominator.name.process.centerBound
        let lower := actualQuotient.prepared.apart.certificate.lowerSq
        Purelib.System.IO.println s!"CAP_PAYMENT_DENOMINATOR_BOUND {denominator.num}/{denominator.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_LOWER_SQ {lower.num}/{lower.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_NUMERATOR_DEPTH {depth}"
        Purelib.System.IO.println s!"CAP_PAYMENT_CELLS_PER_QUARTER {2 ^ depth}"
        Purelib.System.IO.println "CAP_PAYMENT_METADATA_PASS"
        (← IO.getStdout).flush
      else
        formerPay compared

/-- Execute the original full-form loop body on the literal supplied cap and its own actual retained owners. -/
@[noinline] private def runCap (cap : ReciprocalInnerInverse.Data curve collar)
    (inspectOnly : Bool := false) (certified : Option (PLift (PhysicalZero cap)) := none) : IO Unit := do
  Purelib.System.IO.println "CAP_MODEL_PASS"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_ROOT_BOUNDS"
  (← IO.getStdout).flush
  let root := InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model
  let bounds := InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial
  Purelib.System.IO.println "CAP_PHASE_ORIGIN"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_BEGIN"
  (← IO.getStdout).flush
  withPreparedOrigin cap fun cached => do
    Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_PASS"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_BEGIN"
    (← IO.getStdout).flush
    withAttachedOrigin cap cached fun origin => do
      Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_PASS"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_PHASE_FACTOR_ANCHOR"
      (← IO.getStdout).flush
      let anchor := RootCoordinates.originJetFactor_prepared origin jet
      let setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor :=
        ⟨RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor, rfl⟩
      Purelib.System.IO.println "CAP_PHASE_ERROR_BOUNDS"
      (← IO.getStdout).flush
      let errorBounds := Circle.Readings.Jets.prepareErrorBound origin jet remainder data.1
      Purelib.System.IO.println "CAP_PHASE_FULL_FORM_REQUEST"
      (← IO.getStdout).flush
      let retained := Programs.Normalization.request
        (data := data) (principal := principal) (primitive := primitive) (remainder := remainder)
        origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds 0 0 1 (by decide +kernel)
      let quotient := retained.1.quotient.val
      let reference := Programs.Normalization.coefficientChannel (origin := origin) table
      let compared := retained.2.withSamples (Name.Sampling.approximation quotient.output.name)
        (Name.Sampling.approximation reference.name)
        (fun index => congrArg (fun value : Name.Coherent.CoherentNamed =>
          (Name.Sampling.approximation value.name).sample index) retained.1.channel_output.symm) (fun _ => rfl)
      if inspectOnly then
        let source := retained.1.source.val.1
        let actualQuotient := retained.1.quotient.val
        let state := quotientSampleState source actualQuotient compared.leftIndex
        let depth : Nat := state.1
        Purelib.System.IO.println s!"CAP_PAYMENT_BASE {sampleText (retainedBase retained.1.circuit)}"
        Purelib.System.IO.println s!"CAP_PAYMENT_ERROR_SCALE {source.errorScale.num}/{source.errorScale.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_CENTER_BOUND {source.centerBound.num}/{source.centerBound.den}"
        let denominator := actualQuotient.prepared.denominator.name.process.centerBound
        let lower := actualQuotient.prepared.apart.certificate.lowerSq
        Purelib.System.IO.println s!"CAP_PAYMENT_DENOMINATOR_BOUND {denominator.num}/{denominator.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_LOWER_SQ {lower.num}/{lower.den}"
        Purelib.System.IO.println s!"CAP_PAYMENT_NUMERATOR_DEPTH {depth}"
        Purelib.System.IO.println s!"CAP_PAYMENT_CELLS_PER_QUARTER {2 ^ depth}"
        Purelib.System.IO.println "CAP_PAYMENT_METADATA_PASS"
        (← IO.getStdout).flush
      else
        match certified with
        | none => pay compared
        | some checked =>
            let source := retained.1.source.val.1
            let first := physicalReading source quotient
              (checked.down _ _ _ bounds retained.1) compared.leftIndex
            let last := coefficientReading origin compared.rightIndex ⟨reference, rfl⟩
            Purelib.System.IO.println s!"CAP_CERTIFIED_PHYSICAL_RADIUS {first.radius.num}/{first.radius.den}"
            Purelib.System.IO.println s!"CAP_CERTIFIED_COEFFICIENT_RADIUS {last.radius.num}/{last.radius.den}"
            (← IO.getStdout).flush
            pay compared (some
              ⟨⟨first.value, physicalReading_value source quotient
                (checked.down _ _ _ bounds retained.1) compared.leftIndex⟩,
                ⟨last.value, coefficientReading_value origin compared.rightIndex ⟨reference, rfl⟩⟩⟩)

/-- Omitting certified readings preserves the complete historical supplied-cap action for every original cap. -/
private theorem runCap_none_eq_former (cap : ReciprocalInnerInverse.Data curve collar) (inspectOnly : Bool) :
    runCap cap inspectOnly none = formerRunCap cap inspectOnly := (rfl)

/-- Verification-only whole historical fixture action retained before factoring its cap input. -/
private def formerRun (sheet : Fin 2) : IO Unit := do
  Purelib.System.IO.println "CAP_PHASE_BEGIN floors=0,0 target=1"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_MODEL"
  (← IO.getStdout).flush
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_MODEL_PASS"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_PHASE_ROOT_BOUNDS"
    (← IO.getStdout).flush
    let root := InverseModelDerivativeBounds.DerivativeBounds.build cap.clearance cap.model
    let bounds := InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build root cap.polynomial
    Purelib.System.IO.println "CAP_PHASE_ORIGIN"
    (← IO.getStdout).flush
    Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_BEGIN"
    (← IO.getStdout).flush
    withPreparedOrigin cap fun cached => do
      Purelib.System.IO.println "CAP_ORIGIN_NUMERIC_PASS"
      (← IO.getStdout).flush
      Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_BEGIN"
      (← IO.getStdout).flush
      withAttachedOrigin cap cached fun origin => do
        Purelib.System.IO.println "CAP_ORIGIN_ATTACHMENT_PASS"
        (← IO.getStdout).flush
        Purelib.System.IO.println "CAP_PHASE_FACTOR_ANCHOR"
        (← IO.getStdout).flush
        let anchor := RootCoordinates.originJetFactor_prepared origin jet
        let setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor :=
          ⟨RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor, rfl⟩
        Purelib.System.IO.println "CAP_PHASE_ERROR_BOUNDS"
        (← IO.getStdout).flush
        let errorBounds := Circle.Readings.Jets.prepareErrorBound origin jet remainder data.1
        Purelib.System.IO.println "CAP_PHASE_FULL_FORM_REQUEST"
        (← IO.getStdout).flush
        let retained := Programs.Normalization.request
          (data := data) (principal := principal) (primitive := primitive) (remainder := remainder)
          origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds 0 0 1 (by decide +kernel)
        let quotient := retained.1.quotient.val
        let reference := Programs.Normalization.coefficientChannel (origin := origin) table
        let compared := retained.2.withSamples (Name.Sampling.approximation quotient.output.name)
          (Name.Sampling.approximation reference.name)
          (fun index => congrArg (fun value : Name.Coherent.CoherentNamed =>
            (Name.Sampling.approximation value.name).sample index) retained.1.channel_output.symm) (fun _ => rfl)
        pay compared

/-- Execute one original full-form normalized-loop request without replacing it by its coefficient channel.

Every original model, root, table and setup remains a local retained value.
Both endpoint samples come from the same internally computed comparison;
the left endpoint reads its actual stored quotient. Keeping the coefficient
endpoint explicit also avoids rebuilding a type-indexed origin factory.
-/
public def run (sheet : Fin 2) : IO Unit := do
  Purelib.System.IO.println "CAP_PHASE_BEGIN floors=0,0 target=1"
  (← IO.getStdout).flush
  Purelib.System.IO.println "CAP_PHASE_MODEL"
  (← IO.getStdout).flush
  withCap sheet (fun cap => runCap cap false)

/-- Factoring the retained cap preserves the complete original default fixture action at every sheet. -/
private theorem run_eq_former (sheet : Fin 2) : run sheet = formerRun sheet := (rfl)

/-- Pay the same full-form normalized-loop request on the newly requested same-owner exact-seed model. -/
public def runExactSeed (sheet : Fin 2) (inspectOnly : Bool := false)
    (certifiedSamples : Bool := false) : IO Unit := do
  Purelib.System.IO.println "CAP_EXACT_LOOP_BEGIN floors=0,0 target=1"
  (← IO.getStdout).flush
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          (← IO.getStdout).flush
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          runCap supplied inspectOnly
            (if certifiedSamples then some ⟨physicalZero_of_seed seed⟩ else none)

/-- Pay the same full-form normalized-loop request on the newly requested same-owner exact-seed model. -/
private def formerRunExactSeed (sheet : Fin 2) (inspectOnly : Bool := false) : IO Unit := do
  Purelib.System.IO.println "CAP_EXACT_LOOP_BEGIN floors=0,0 target=1"
  (← IO.getStdout).flush
  withCap sheet fun cap => do
    Purelib.System.IO.println "CAP_EXACT_SEED_SEARCH_BEGIN"
    (← IO.getStdout).flush
    withExactSeed cap fun attempt result => do
      Purelib.System.IO.println s!"CAP_EXACT_SEED_BANK {attempt.1.length}"
      match result with
      | none => throw (IO.userError "automatic exact seed inconclusive in the retained original owner box")
      | some seed =>
          Purelib.System.IO.println s!"CAP_EXACT_SEED_PASS {sampleText seed.val.rootSample}"
          (← IO.getStdout).flush
          let supplied := ReciprocalInnerInverse.Data.ofSeed curve collar seed.val
          formerRunCap supplied inspectOnly

/-- Omitting certified physical evaluation preserves the complete former supplied-seed fixture action. -/
private theorem runExactSeed_false_eq_former (sheet : Fin 2) (inspectOnly : Bool) :
    runExactSeed sheet inspectOnly false = formerRunExactSeed sheet inspectOnly := (rfl)

end TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.Observation
