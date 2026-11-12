module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Jet
public import Purelib.Integration.CertifiedProgram.Observation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # The retained origin reciprocal times the same closed principal programme -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Principal

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Polynomial
open Purelib.Integration
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Rational.Geometric
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical} {nonzero : base ≠ 0}
  {data : Polynomials differential} {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {retained : jet.Principal data.1.val differential.scale} {circuit : Integral.Circuit base nonzero}

variable (logarithmic : { value :
  (program : CertifiedProgram.Program (Integral.Logarithmic.operations circuit)) ×
    NamedEquivalent circuit.channel.name program.output.name // value = Integral.Logarithmic.program circuit })
  (parameterCached : ParameterPrimitives retained circuit)
  (polar : { value : (program : RefinementProgram) ×
    NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.polarEdges.val.concatenate parameterCached.polar_count,
      parameterCached.polarEdges.val.concatenate_zero parameterCached.polar_count⟩ })
  (regular : { value : (program : RefinementProgram) ×
    NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.regularEdges.val.concatenate parameterCached.regular_count,
      parameterCached.regularEdges.val.concatenate_zero parameterCached.regular_count⟩ })
  (source : ParameterPrimitives.Program.View logarithmic parameterCached polar regular)

/-- The supplied whole principal source cache retains the exact original logarithmic cache at that same index. -/
theorem source_logarithmic (index : Nat)
    (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    actual.val.model.2.1.val = logarithmic.val.1.stage index := by
  have actualSource := congrArg
    (fun value : CertifiedProgram.CachedModel (ParameterPrimitives.Program.operations logarithmic parameterCached) =>
      value.model.2.1.val) actual.property
  have originalSource := (congrArg (fun value => (value.1.stage index).model.2.1.val) source.property).trans
    (ParameterPrimitives.Program.build_source logarithmic parameterCached polar regular index)
  exact actualSource.trans originalSource

/-- The same supplied principal source cache retains its actual logarithmic depth above the requested stage. -/
theorem source_depth_ge (index : Nat) (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    index ≤ actual.val.model.2.1.val.model.1 := by
  have same := congrArg (fun value : CertifiedProgram.CachedModel (Integral.Logarithmic.operations circuit) =>
    value.model.1) (source_logarithmic logarithmic parameterCached polar regular source index actual)
  exact (ParameterPrimitives.Program.depth_ge logarithmic index).trans_eq
    ((ParameterPrimitives.Program.depth_stage logarithmic index).symm.trans same.symm)

/-- The actual supplied principal source sample is the retained circuit's dyadic sample at its own saved log depth. -/
theorem source_sample (index : Nat) (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    actual.val.sample = (circuit.1.dyadicModel (ParameterPrimitives.Program.coefficient parameterCached)
      actual.val.model.2.1.val.model.1).integralSample := by
  have actualSample := congrArg (fun value : CertifiedProgram.CachedModel
    (ParameterPrimitives.Program.operations logarithmic parameterCached) => value.sample) actual.property
  have originalSample := (congrArg (fun value => (value.1.stage index).sample) source.property).trans
    (ParameterPrimitives.Program.build_sample logarithmic parameterCached polar regular index)
  have depth := (congrArg (fun value : CertifiedProgram.CachedModel (Integral.Logarithmic.operations circuit) =>
    value.model.1) (source_logarithmic logarithmic parameterCached polar regular source index actual)).trans
      (ParameterPrimitives.Program.depth_stage logarithmic index)
  exact (actualSample.trans originalSample).trans (congrArg (fun value =>
    (circuit.1.dyadicModel (ParameterPrimitives.Program.coefficient parameterCached) value).integralSample) depth.symm)

/-- The reciprocal target reads the actual logarithmic depth from its same supplied whole principal cache. -/
def targets (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box) :
    CertifiedProgram.Observation.Targets source.val.1 :=
  fun _ actual => Readings.Jets.principalTarget cached jetBounds
    (Basic.quarterRadius 1 actual.val.model.2.1.val.model.1)

/-- Every target computed from the same retained logarithmic cache is strictly positive. -/
theorem targets_positive (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box)
    (index : Nat) (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    0 < targets logarithmic parameterCached polar regular source cached jetBounds index actual :=
  Readings.Jets.principalTarget_positive cached jetBounds nonzero (Basic.quarterRadius_pos (by decide) _)

/-- The actual retained logarithmic depth makes its reciprocal target pay the original requested geometric stage. -/
theorem targets_bounded (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box)
    (index : Nat) (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    targets logarithmic parameterCached polar regular source cached jetBounds index actual ≤
      Basic.quarterRadius 1 index :=
  (Readings.Jets.principalTarget_le cached jetBounds nonzero
    (Basic.quarterRadius_pos (by decide) _)).trans
      (Basic.quarterRadius_antitone (by decide)
        (source_depth_ge logarithmic parameterCached polar regular source index actual))

/-- The computed reciprocal target reads the same displayed whole cache's actual retained logarithmic depth. -/
theorem targets_value (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box)
    (index : Nat) (actual : CertifiedProgram.Observation.SourceCache source.val.1 index) :
    targets logarithmic parameterCached polar regular source cached jetBounds index actual =
      Readings.Jets.principalTarget cached jetBounds (Basic.quarterRadius 1 actual.val.model.2.1.val.model.1) :=
  (rfl)

/-- Build the actual origin-weighted principal programme and its retained logarithmic output comparison.

The same whole principal source retains its actual polar, regular and
logarithmic programmes. Each weighted stage keeps one original source
cache and one reciprocal Request whose target reads that cache's own
logarithmic depth. The guarded original reciprocal is built once before
the programme and its comparison. Original paid-reading and multiplication
bridges derive the operational agreement, before the total-form tail bound.
-/
def build (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box) :
    (produced : CertifiedProgram.Program (CertifiedProgram.Observation.operations
      (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart) source.val.1
      (targets logarithmic parameterCached polar regular source cached jetBounds))) ×
    NamedEquivalent ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
      ((Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
        (parameterOrder curve))).mul circuit.channel)).name produced.output.name := by
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  let paid := targets_positive logarithmic parameterCached polar regular source cached jetBounds
  let bounded := targets_bounded logarithmic parameterCached polar regular source cached jetBounds
  let produced := CertifiedProgram.Observation.program reciprocal source.val.1
    (targets logarithmic parameterCached polar regular source cached jetBounds) paid bounded
  let compared := CertifiedProgram.Observation.output_equivalent reciprocal source.val.1
    (targets logarithmic parameterCached polar regular source cached jetBounds) paid bounded ⟨produced, rfl⟩
  let pivot := Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
    (parameterOrder curve))
  let original := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    reciprocal reciprocal (pivot.mul circuit.channel) source.val.1.output (NamedEquivalent.refl _) source.val.2
  exact ⟨produced, original.trans compared⟩

/-- The whole weighted programme is the same original paid-observation producer over the supplied principal source. -/
theorem build_program (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box) :
    (build logarithmic parameterCached polar regular source (origin := origin) cached jetBounds).1 =
      CertifiedProgram.Observation.program
        (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart) source.val.1
        (targets logarithmic parameterCached polar regular source cached jetBounds)
        (targets_positive logarithmic parameterCached polar regular source cached jetBounds)
        (targets_bounded logarithmic parameterCached polar regular source cached jetBounds) :=
  (rfl)

/-- Each built weighted stage retains its whole supplied principal cache and actual once-built reciprocal Request. -/
theorem build_stage (cached : data.Bounds base) (jetBounds : jet.Bounds collar.box) (index : Nat) :
    ((build logarithmic parameterCached polar regular source (origin := origin) cached jetBounds).1.stage index) =
      CertifiedProgram.CachedModel.canonical
        (operations := CertifiedProgram.Observation.operations
          (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart) source.val.1
          (targets logarithmic parameterCached polar regular source cached jetBounds))
        ⟨index, ⟨source.val.1.stage index, rfl⟩,
          Equivalence.Observation.Request.build
            (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart)
            (targets logarithmic parameterCached polar regular source cached jetBounds index
              ⟨source.val.1.stage index, rfl⟩)
            (targets_positive logarithmic parameterCached polar regular source cached jetBounds index
              ⟨source.val.1.stage index, rfl⟩)⟩ := by
  rewrite [build_program]
  exact CertifiedProgram.Observation.program_stage _ _ _ _ _ index

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Principal

end
