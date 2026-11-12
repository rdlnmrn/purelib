module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Program
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Transport
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Jet
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Rational.Geometric.Scale
import Purelib.Tactic.Ring

/-! # Signed four-quarter programmes with their retained logarithmic normalization

The negative even sheet is constructed from the four original quarter
programmes on their same supplied curves. Its actual balanced output is
compared before the same saved logarithmic preparation is used once more
for the new numerator. The shrinking stream samples those actual signed
quotients at their own paid comparison stages.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum
open Purelib.Approximation.Rational.Geometric
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential reference : OddPowerDifferential curve.polynomial}
    {base : Canonical} {nonzero : base ≠ 0}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {data : Polynomials reference} {cached : data.Bounds base}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish} {entries : Integral.Entries base nonzero}
    {referencePairs : reference.denominatorPairs = 0}
    {degreeBound : reference.numerator.natDegree ≤ 2 * genus}

/-- The exact signed model type at one original quarter occurrence and its same supplied programme budget.

This definition abbreviates the original signed model with its actual
quarter curve. It introduces no additional owner, field or cache.
-/
@[expose] def EvenNegativeQuarterModel
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :=
  Model.EvenNegative differential reference cap
    (Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
    ((Integral.quarterBase_normSq base _).trans_le unitBound)
    ((Integral.quarterBase_normSq base _).trans_le collarBound)
    (entries.get index).1 start finish (stored.get index).2.1.val

/-- The original signed operations on that exact retained quarter model and its original budget. -/
@[expose] def evenNegativeQuarterOperations
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :
    CertifiedProgram.ModelOperations (EvenNegativeQuarterModel (differential := differential) stored index) :=
  Model.EvenNegative.operations

/-- The original balanced addition operations for all four actual signed quarter models in occurrence order. -/
@[expose] def evenNegativeOperations
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges) :=
  ((evenNegativeQuarterOperations (differential := differential) stored ⟨0, by decide +kernel⟩).add
    (evenNegativeQuarterOperations (differential := differential) stored ⟨1, by decide +kernel⟩)).add
  ((evenNegativeQuarterOperations (differential := differential) stored ⟨2, by decide +kernel⟩).add
    (evenNegativeQuarterOperations (differential := differential) stored ⟨3, by decide +kernel⟩))

/-- Construct one signed programme from the same retained original quarter and its original factory index law. -/
private def negativeQuarter
    (pairs : differential.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      entries cached referencePairs degreeBound bounds edges)
    (index : Fin Integral.quarters.length) :
    (target : CertifiedProgram.Program (evenNegativeQuarterOperations
      (differential := differential) stored.val index)) ×
      NamedEquivalent target.output.name (stored.val.get index).2.2.output.name :=
  let source := stored.val.get index
  Circle.Program.evenNegative (differential := differential) (reference := reference)
    (Integral.quarterBase_ne_zero base nonzero _) pairs referencePairs sameNumerator oppositeScale parity
    start finish source.2.1.val source.2.2 (fun depth => stored.stage_index index depth)

section Sum

attribute [local irreducible] EvenNegativeQuarterModel evenNegativeQuarterOperations

/-- Construct the actual four-quarter negative-sheet programme and compare its output with the saved original sum.

Each signed quarter is built once from its same supplied source programme.
The original heterogeneous addition retains those same four results. The
saved source comparison is composed directly; its source sum and quarter
factories are not rerun.
-/
def evenNegative
    (pairs : differential.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      entries cached referencePairs degreeBound bounds edges)
    (source : { value : stored.val.Result // value = stored.val.concatenate }) :
    (target : CertifiedProgram.Program (evenNegativeOperations (differential := differential) stored.val)) ×
      NamedEquivalent target.output.name source.val.1.output.name := by
  let first := negativeQuarter pairs sameNumerator oppositeScale parity stored ⟨0, by decide +kernel⟩
  let second := negativeQuarter pairs sameNumerator oppositeScale parity stored ⟨1, by decide +kernel⟩
  let third := negativeQuarter pairs sameNumerator oppositeScale parity stored ⟨2, by decide +kernel⟩
  let fourth := negativeQuarter pairs sameNumerator oppositeScale parity stored ⟨3, by decide +kernel⟩
  let produced := first.1.addFour second.1 third.1 fourth.1
  have earlier := Congruence.coherentAdd_respects first.1.output (stored.val.get ⟨0, by decide +kernel⟩).2.2.output
    second.1.output (stored.val.get ⟨1, by decide +kernel⟩).2.2.output first.2 second.2
  have later := Congruence.coherentAdd_respects third.1.output (stored.val.get ⟨2, by decide +kernel⟩).2.2.output
    fourth.1.output (stored.val.get ⟨3, by decide +kernel⟩).2.2.output third.2 fourth.2
  have summed := Congruence.coherentAdd_respects (first.1.output.add second.1.output)
    ((stored.val.get ⟨0, by decide +kernel⟩).2.2.output.add (stored.val.get ⟨1, by decide +kernel⟩).2.2.output)
    (third.1.output.add fourth.1.output)
    ((stored.val.get ⟨2, by decide +kernel⟩).2.2.output.add (stored.val.get ⟨3, by decide +kernel⟩).2.2.output)
    earlier later
  let sourceOutput : Name.Coherent.CoherentNamed := source.val.1.output
  have sourceChannels : NamedEquivalent stored.val.channels.name sourceOutput.name := source.val.2
  have moved := Eq.mp (congrArg
    (fun channel : Name.Coherent.CoherentNamed => NamedEquivalent channel.name sourceOutput.name)
    (channels_eq stored.val)) sourceChannels
  exact ⟨produced.1, produced.2.symm.trans (summed.trans moved)⟩

end Sum

namespace Normalization.Sources

variable {retained : Sources (data := data) nonzero unitBound collarBound referencePairs degreeBound bounds edges}

/-- The signed programme, its whole saved-preparation quotient and the original normalized comparison.

This existing dependent-pair view retains the original programme and
quotient types. Its factory equation binds the new quotient to the exact
preparation already saved by the supplied original normalized source.
-/
abbrev EvenNegative
    (retained : Sources (data := data) nonzero unitBound collarBound referencePairs degreeBound bounds edges) :=
  (target : CertifiedProgram.Program (evenNegativeOperations (differential := differential) retained.programs.val)) ×
  (normalized : { value : Division.Prepared.Quotient target.output retained.circuit.channel //
    QuotientEquation retained.quotient.val.prepared value }) ×
    NamedEquivalent normalized.val.output.name retained.channel.name

/-- Normalize the actual signed four-quarter programme using the identical stored logarithmic preparation.

The original normalized source retains its own complete quotient. Both
whole quotient caches feed the existing two-numerator comparison, so
neither the saved source sum nor its denominator preparation is rebuilt.
-/
def evenNegative
    (retained : Sources (data := data) nonzero unitBound collarBound referencePairs degreeBound bounds edges)
    (pairs : differential.denominatorPairs = 0)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    EvenNegative (differential := differential) retained :=
  let signed := Programs.evenNegative pairs sameNumerator oppositeScale parity retained.programs retained.source
  let normalized := Division.Prepared.Quotient.quotient signed.1.output retained.quotient.val.prepared
  let compared := Division.Prepared.Quotient.respects normalized retained.quotient.val
    (NamedEquivalent.refl _) signed.2
  let transported := Eq.mp (congrArg
    (fun channel : Name.Coherent.CoherentNamed => NamedEquivalent normalized.output.name channel.name)
    retained.channel_output.symm) compared
  ⟨signed.1, ⟨normalized, QuotientEquation.built retained.quotient.val.prepared⟩, transported⟩

end Normalization.Sources

namespace Normalization

variable {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
    {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
    {principal : jet.Principal data.1.val reference.scale}
    {primitive : Antiderivative.ReciprocalPrimitive principal.val genus}

section SignedStream

variable (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (pairs : differential.denominatorPairs = 0) (referencePairs : reference.denominatorPairs = 0)
    (degreeBound : reference.numerator.natDegree ≤ 2 * genus)
    (sameNumerator : reference.numerator = differential.numerator)
    (oppositeScale : reference.scale = -differential.scale)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)

/-- One actual signed normalized-loop sample source with its paid finite comparison to the fixed coefficient channel.

The original request is computed once at one additional geometric stage.
Its retained source supplies all four signed programmes and the exact saved
normalizer. Two actual comparison receipts pay the stated stage tolerance.
-/
def evenNegativeStage (index : Nat) :
    (source : Sequence.ApproximationData) × Equivalence.Comparison source
      (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
      0 0 (Basic.quarterRadius 1 index) := by
  let precision := Basic.quarterRadius 1 (index + 1)
  have positive : 0 < precision := Basic.quarterRadius_pos (by decide) (index + 1)
  let actual := request (primitive := primitive) origin table referencePairs degreeBound bounds edges
    jetBounds anchor setup errorBounds 0 0 precision positive
  let signed := Sources.evenNegative actual.1 pairs sameNumerator oppositeScale parity
  let bridge := signed.2.2.compare 0 0 precision positive
  have scale : 2 * (precision + precision) = Basic.quarterRadius 1 index := by
    have amplified := Scale.quarterRadius_four_mul 1 (index + 1)
    have shifted := Scale.quarterRadius_four_mul_succ 1 index
    exact (show 2 * (precision + precision) = 4 * precision by ring1).trans
      (amplified.symm.trans shifted)
  exact ⟨Name.Sampling.approximation signed.2.1.val.output.name,
    (bridge.trans actual.2).weaken (Basic.quarterRadius 1 index) scale.le⟩

/-- The shrinking stream samples the actual signed four-quarter quotients at their own paid stages. -/
def evenNegativeGeometric : Geometric.GeometricApproximation :=
  Geometric.GeometricApproximation.fromComparisons
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (evenNegativeStage (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds)

/-- The signed shrinking stream retains its operational comparison with the same fixed coefficient channel. -/
def evenNegativeGeometric_equivalent : Equivalence.Equivalent
    (evenNegativeGeometric (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds).toApproximation
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name) :=
  Geometric.GeometricApproximation.fromComparisons_equivalent
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (evenNegativeStage (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds)

/-- The coherent signed cap channel is produced by the actual normalized negative-sheet loop samples. -/
def evenNegativeChannel : Name.Coherent.CoherentNamed :=
  ofApproximation (evenNegativeGeometric (primitive := primitive) origin table pairs referencePairs degreeBound
    sameNumerator oppositeScale parity bounds edges jetBounds anchor setup errorBounds).toApproximation

/-- The actual normalized negative-sheet loop channel agrees with the original opposite-scale coefficient channel. -/
def evenNegativeChannel_equivalent : NamedEquivalent
    (evenNegativeChannel (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds).name
    (coefficientChannel (origin := origin) table).name :=
  (Equivalence.Equivalent.toNamed_sampling
    (evenNegativeGeometric (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds).toApproximation).trans
    (evenNegativeGeometric_equivalent (primitive := primitive) origin table pairs referencePairs degreeBound
      sameNumerator oppositeScale parity bounds edges jetBounds anchor setup errorBounds)

/-- The actual negative-sheet normalized loop reads the oppositely signed infinity functional on the fixed model.

The same stored origin reciprocal, jet and original numerator determine
the scalar. Its sign follows the retained opposite-scale relation before
normalization; no cyclic sheet or independently chosen chart is identified.
-/
def evenNegativeChannel_even : NamedEquivalent
    (evenNegativeChannel (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
      oppositeScale parity bounds edges jetBounds anchor setup errorBounds).name
    ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
      (Coherence.exact (differential.scale * InfinityCoefficients.evenFunctional curve jet
        (Dense.Evaluation.toVector (2 * genus + 1)
          (Dense.Evaluation.fromDense reference.numerator.normalize))))).name := by
  let functional := InfinityCoefficients.evenFunctional curve jet
    (Dense.Evaluation.toVector (2 * genus + 1)
      (Dense.Evaluation.fromDense reference.numerator.normalize))
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  have scalar : -reference.scale * functional = differential.scale * functional := by
    rewrite [oppositeScale]
    ring1
  have compared := (evenNegativeChannel_equivalent (primitive := primitive) origin table pairs referencePairs
    degreeBound sameNumerator oppositeScale parity bounds edges jetBounds anchor setup errorBounds).trans
    (coefficientChannel_even (origin := origin) (degreeBound := degreeBound) table parity)
  exact Eq.mp (congrArg
    (fun value : Canonical => NamedEquivalent
      (evenNegativeChannel (primitive := primitive) origin table pairs referencePairs degreeBound sameNumerator
        oppositeScale parity bounds edges jetBounds anchor setup errorBounds).name
      (reciprocal.mul (Coherence.exact value)).name) scalar) compared

end SignedStream

end Normalization

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs

end
