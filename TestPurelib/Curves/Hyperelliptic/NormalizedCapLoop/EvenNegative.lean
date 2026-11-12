module

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Transport
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Continuation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Attachment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Basis

/-! # Actual original cap-programme input for the signed transport -/

namespace TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.EvenNegative

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential reference : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}

/-- Construct the signed programme comparison from the actual original canonical cap programme and its own index law. -/
private def signedProgram
    {data : Polynomials reference} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (degreeBound : reference.numerator.natDegree ≤ 2 * genus)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right) :=
  let source := program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
    cached nonzero referencePairs degreeBound bounds left right cachedEdges
  Program.evenNegative (differential := differential) (reference := reference)
    nonzero pairs referencePairs sameNumerator oppositeScale parity left right source.2.1.val source.2.2
    (program_stage_index cached nonzero referencePairs degreeBound bounds left right cachedEdges)

/-- The actual signed programme stage retains the same saved sample and its attached affine-chart quadrature. -/
private def signedStageAttached
    {data : Polynomials reference} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (degreeBound : reference.numerator.natDegree ≤ 2 * genus)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right) (index : Nat) :=
  let signed := signedProgram (differential := differential) (reference := reference)
    (cap := cap) (actual := actual) (unitBound := unitBound) (collarBound := collarBound)
    cached nonzero pairs referencePairs degreeBound sameNumerator oppositeScale
    parity bounds left right cachedEdges
  let retained := signed.1.stage index
  let attached := Model.EvenNegative.attach (differential := differential) (reference := reference)
    (cap := cap) (base := base) (unitBound := unitBound) (collarBound := collarBound) (actual := actual) retained
  (signed, retained, attached, PLift.up (Model.EvenNegative.attached_sample retained attached))

/-- The original canonical programme has the same actual chart-stage correspondence in either degree parity. -/
private def canonicalStageAttached
    {data : Polynomials reference} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (referencePairs : reference.denominatorPairs = 0) (degreeBound : reference.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (left right : Endpoint) (cachedEdges : DyadicEdges 0 left right) (index : Nat) :=
  let original := program (unitBound := unitBound) (collarBound := collarBound) (actual := actual)
    cached nonzero referencePairs degreeBound bounds left right cachedEdges
  let retained := original.2.2.stage index
  let attached := Stage.attach (differential := reference) (cap := cap) (base := base)
    (unitBound := unitBound) (collarBound := collarBound) (actual := actual) retained.model.2
  (original, retained, attached, PLift.up (Stage.attached_integralSample retained.model.2 attached))

/-- Ordinary downstream reduction recovers the exact original signed model after local construction opacity ends. -/
private theorem quarterModel_eq {data : Polynomials reference} {cached : data.Bounds base}
    {nonzero : base ≠ 0}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {entries : Integral.Entries base nonzero} {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :
    Programs.EvenNegativeQuarterModel (differential := differential) stored index =
      Model.EvenNegative differential reference cap
        (Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
        ((Integral.quarterBase_normSq base _).trans_le unitBound)
        ((Integral.quarterBase_normSq base _).trans_le collarBound)
        (entries.get index).1 start finish (stored.get index).2.1.val := (rfl)

/-- Construct the signed normalized loop from one actual original four-quarter source factory and its saved quotient. -/
private def signedLoop {data : Polynomials reference} (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (degreeBound : reference.numerator.natDegree ≤ 2 * genus)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) :=
  let original := Normalization.sources (data := data) base nonzero unitBound collarBound
    referencePairs degreeBound bounds edges
  Normalization.Sources.evenNegative original pairs sameNumerator oppositeScale parity

/-- The opposite of the minus-one source scale is the same whole original unit-scaled differential. -/
private theorem unitBasis_target (jet : InfinityCoefficients.Jet curve)
    (coordinates : Data.Vector Canonical (2 * genus)) :
    Differentials.Basis.differential curve jet coordinates (-(-1 : Canonical)) =
      Differentials.Basis.differential curve jet coordinates :=
  congrArg (fun scalar => Differentials.Basis.differential curve jet coordinates scalar)
    (show -(-1 : Canonical) = 1 by decide +kernel)

/-- The actual minus-one source supplies the unit differential's signed normalized zero channel. -/
private def unitBasisNegative {jet : InfinityCoefficients.Jet curve}
    {coordinates : Data.Vector Canonical (2 * genus)}
    {data : Polynomials (Differentials.Basis.differential curve jet coordinates (-1))}
    {principal : jet.Principal data.1.val
      (Differentials.Basis.differential curve jet coordinates (-1)).scale}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
    {primitive : Antiderivative.ReciprocalPrimitive principal.val genus}
    (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = Primitives.parameterPolynomial principal })
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box)
    (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1) :=
  Normalization.Basis.evenNegative_zero (primitive := primitive) (scale := -1)
    origin table parity bounds edges jetBounds anchor setup errorBounds

/-- Retain one actual refined-model overlap and reuse its flip along the same cap power-circle in either parity. -/
private def refinedSheet (index : Nat) (time : Data.Rat.Fraction.Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) :=
  let other := cap.model.refine index
  let interval : Data.Rat.Interval.Bounds := ⟨0, 1, by decide +kernel⟩
  let contains := fun time (_ : interval.Contains time) => point_inside base unitBound collarBound actual time
  let seed := OverlapSample.build cap.model other (Primitives.point curve (actual.val.point 0))
  let moved := sampleAt (unitBound := unitBound) (collarBound := collarBound) actual interval contains
    (first := 0) ⟨le_rfl, by decide +kernel⟩ seed time inside
  (other, seed, moved, PLift.up (sampleAt_flip (unitBound := unitBound) (collarBound := collarBound)
    actual interval contains (first := 0) ⟨le_rfl, by decide +kernel⟩ seed time inside))

/-- The original four retained programme stages supply their cyclic preparation banks and computed coordinate joins.

Each original certified stage is selected once. Its exact stored reading
bank and paid requests supply every left cache; the original geometric
quarter incidences supply all right-endpoint seams without reacquisition.
-/
private def stageEndpointBanks {data : Polynomials reference} {cached : data.Bounds base}
    {nonzero : base ≠ 0}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {entries : Integral.Entries base nonzero} {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Nat) :=
  let first := (stored.get ⟨0, by decide +kernel⟩).2.2.stage index
  let second := (stored.get ⟨1, by decide +kernel⟩).2.2.stage index
  let third := (stored.get ⟨2, by decide +kernel⟩).2.2.stage index
  let fourth := (stored.get ⟨3, by decide +kernel⟩).2.2.stage index
  let attached0 := Stage.attach first.model.2
  let attached1 := Stage.attach second.model.2
  let attached2 := Stage.attach third.model.2
  let attached3 := Stage.attach fourth.model.2
  let banks := Loop.endpointBanks (cap := cap) (differential := reference)
    (factors := fun parameter => parameter ^ HyperellipticReciprocal.originOrder curve)
    (unitBound := unitBound) (collarBound := collarBound)
    entries first.model.2.1 second.model.2.1 third.model.2.1 fourth.model.2.1
    attached0 attached1 attached2 attached3
  Loop.EndpointBanks.junctions banks

/-- The actual signed balanced stage supplies the same computed cyclic endpoint-cache construction.

All four supplied child caches are projected from that one saved aggregate.
Their original negative-sheet stages and paid requests remain unchanged.
The complete coordinate-join result consumes those actual signed caches.
-/
private def signedEndpointBanks {data : Polynomials reference} {cached : data.Bounds base}
    {nonzero : base ≠ 0}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {entries : Integral.Entries base nonzero} {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (retained : Integration.CertifiedProgram.CachedModel (stored.evenNegativeOperations
      (differential := differential))) :=
  let first := retained.model.1.model.1
  let second := retained.model.1.model.2
  let third := retained.model.2.model.1
  let fourth := retained.model.2.model.2
  let stage0 := first.model.2.2.val
  let stage1 := second.model.2.2.val
  let stage2 := third.model.2.2.val
  let stage3 := fourth.model.2.2.val
  let attached0 := Stage.attach stage0
  let attached1 := Stage.attach stage1
  let attached2 := Stage.attach stage2
  let attached3 := Stage.attach stage3
  let banks := Loop.endpointBanks (cap := cap) (unitBound := unitBound) (collarBound := collarBound)
    (factors := fun _ => -1) entries stage0.1 stage1.1 stage2.1 stage3.1
    attached0 attached1 attached2 attached3
  Loop.EndpointBanks.junctions banks

end TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop.EvenNegative
