module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent.Integral
import Purelib.Integration.CertifiedProgram.Comparison
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Tactic.Ring

/-! # The actual principal cap programme on the retained logarithmic mesh -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.ParameterPrimitives.Program

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.RationalFunctions.Curve.Canonical
open Purelib.Integration
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Geometric.Coherent
open Purelib.Riemann.Periods
open Purelib.Approximation.Rational.Geometric

variable {genus : Nat} {curve : HyperellipticCurve genus} {jet : InfinityCoefficients.Jet curve}
  {polynomial : Dense.Basic.DensePolynomial Canonical} {scale base : Canonical} {nonzero : base ≠ 0}
  {retained : jet.Principal polynomial scale} {circuit : Circle.Integral.Circuit base nonzero}

/-- Evaluate the same actual retained substituted table with its original nonzero-parameter denominator power. -/
def coefficient (cached : ParameterPrimitives retained circuit) (parameter : Canonical) : Canonical :=
  Evaluation.eval cached.table.val parameter * (parameter ^ (parameterOrder curve + 1))⁻¹

/-- The retained table coefficient is the original C product with the exact original cap Jacobian. -/
theorem coefficient_eq (cached : ParameterPrimitives retained circuit) (parameter : Canonical) :
    coefficient cached parameter =
      ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
        (parameter ^ (degree curve * (genus + 1)))⁻¹ := by
  unfold coefficient
  rewrite [cached.table.property, parameterPolynomial_eval, parameterOrder_succ]
  rfl

/-- The actual same-curve table sample has the original polar/logarithmic/regular split on its own chosen mesh. -/
theorem sample_split (cached : ParameterPrimitives retained circuit) (depth : Nat) :
    (circuit.1.dyadicModel (coefficient cached) depth).integralSample =
      ((cached.polarEdges.val.concatenate cached.polar_count).model depth).integralSample +
        Coefficient.coefficient cached.table.val (parameterOrder curve) *
          (circuit.1.dyadicModel (fun parameter => parameter⁻¹) depth).integralSample +
        ((cached.regularEdges.val.concatenate cached.regular_count).model depth).integralSample :=
  (circuit.1.dyadicModel_sample_congr (coefficient cached)
    (fun parameter => ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
      (parameter ^ (degree curve * (genus + 1)))⁻¹)
    (fun quarter time => coefficient_eq cached ((circuit.1.get quarter).1.val.point time)) depth).trans
      (cached.model_sample_split depth)

variable (logarithmic : { value :
  (program : CertifiedProgram.Program (Circle.Integral.Logarithmic.operations circuit)) ×
    NamedEquivalent circuit.channel.name program.output.name // value = Circle.Integral.Logarithmic.program circuit })

/-- The actual supplied logarithmic stage's retained dyadic depth. -/
def depth (index : Nat) : Nat := (logarithmic.val.1.stage index).model.1

/-- The displayed logarithmic depth is the same saved source stage's actual retained dyadic index. -/
theorem depth_stage (index : Nat) : (logarithmic.val.1.stage index).model.1 = depth logarithmic index :=
  (rfl)

/-- Every actual selected logarithmic depth is above that same original requested stage. -/
theorem depth_ge (index : Nat) : index ≤ depth logarithmic index := by
  unfold depth
  rewrite [logarithmic.property]
  exact Circle.Integral.Logarithmic.program_depth_ge circuit index

/-- Retain the original stage index, its actual whole logarithmic cache and the principal path built on that exact mesh.

The complete supplied logarithmic programme remains a correctness-bearing
parent. The actual path's producer identity uses the same original cached
parameter table and the depth read from that same retained source cache.
-/
abbrev Model (cached : ParameterPrimitives retained circuit) :=
  (index : Nat) ×
    (source : { value : CertifiedProgram.CachedModel (Circle.Integral.Logarithmic.operations circuit) //
      value = logarithmic.val.1.stage index }) ×
      { value : PathModel // value = circuit.1.dyadicModel (coefficient cached) source.val.model.1 }

/-- The sample and allowance read the same original retained principal path. -/
def operations (cached : ParameterPrimitives retained circuit) :
    CertifiedProgram.ModelOperations (Model logarithmic cached) where
  sample model := model.2.2.val.integralSample
  allowance model := model.2.2.val.aggregateAllowance

/-- The sample operation reads the supplied whole cache's actual retained principal path. -/
theorem operations_sample (cached : ParameterPrimitives retained circuit) (model : Model logarithmic cached) :
    (operations logarithmic cached).sample model = model.2.2.val.integralSample := by
  unfold operations
  rfl

/-- The allowance operation reads that same supplied original principal path. -/
theorem operations_allowance (cached : ParameterPrimitives retained circuit) (model : Model logarithmic cached) :
    (operations logarithmic cached).allowance model = model.2.2.val.aggregateAllowance := by
  unfold operations
  rfl

/-- Construct the actual principal path after selecting the supplied logarithmic cache exactly once. -/
private def stage (cached : ParameterPrimitives retained circuit) (index : Nat) :
    CertifiedProgram.CachedModel (operations logarithmic cached) :=
  let original := logarithmic.val.1.stage index
  let actual := circuit.1.dyadicModel (coefficient cached) original.model.1
  .canonical ⟨index, ⟨original, rfl⟩, ⟨actual, rfl⟩⟩

/-- Select literal polar programme caches at the same actual supplied logarithmic depths. -/
def polarProgram (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ }) :=
  polar.val.1.certifiedView.program.selectStages (depth logarithmic) (depth_ge logarithmic)

/-- Select literal regular programme caches at those same actual supplied logarithmic depths. -/
def regularProgram (cached : ParameterPrimitives retained circuit)
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ }) :=
  regular.val.1.certifiedView.program.selectStages (depth logarithmic) (depth_ge logarithmic)

/-- The geometric sum uses the actual selected primitive samples and same retained logarithmic samples.

The original geometric arithmetic derives its movement and center bounds.
It is a view of the actual retained programme samples, not an assumption
about the principal programme's Cauchy behavior or its integral.
-/
def approximation (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ }) :
    GeometricApproximation :=
  ((polarProgram logarithmic cached polar).geometric.add
    ((GeometricApproximation.exact (Coefficient.coefficient cached.table.val (parameterOrder curve))).mul
      logarithmic.val.1.geometric)).add (regularProgram logarithmic cached regular).geometric

/-- The actual principal cache sample equals that finite sum of the supplied original programme samples. -/
private theorem stage_sample (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ })
    (index : Nat) : (stage logarithmic cached index).sample =
      (approximation logarithmic cached polar regular).sample index := by
  change (circuit.1.dyadicModel (coefficient cached) (depth logarithmic index)).integralSample = _
  rewrite [sample_split]
  unfold approximation
  rewrite [GeometricApproximation.add_sample, GeometricApproximation.add_sample,
    GeometricApproximation.mul_sample, GeometricApproximation.exact_sample,
    CertifiedProgram.Program.geometric_sample, CertifiedProgram.Program.geometric_sample,
    CertifiedProgram.Program.geometric_sample]
  unfold polarProgram regularProgram
  rewrite [CertifiedProgram.Program.selectStages_stage, CertifiedProgram.Program.selectStages_stage,
    RefinementProgram.certifiedView_sample, RefinementProgram.certifiedView_sample, polar.property, regular.property]
  have logSample := (logarithmic.val.1.stage index).sample_eq.trans
    (Circle.Integral.Logarithmic.operations_sample circuit (logarithmic.val.1.stage index).model)
  rewrite [logSample, (logarithmic.val.1.stage index).model.2.property]
  rfl

/-- The actual closed principal programme realizes its retained pivot times the original logarithmic circuit channel.

The supplied whole primitive pairs retain both original zero comparisons.
Actual stage-selection comparisons transport those original programmes to the
retained logarithmic depths, and original geometric arithmetic combines
the three actual channels. Neither endpoint cancellation nor coefficient
splitting is used as an assumed integral comparison.
-/
private def logarithmicComparison (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ })
    (produced : CertifiedProgram.Program (operations logarithmic cached))
    (comparison : NamedEquivalent (PeriodMatrix.geometricNamed
      (approximation logarithmic cached polar regular)).name produced.output.name) :
    NamedEquivalent ((Coherence.exact (Coefficient.coefficient cached.table.val (parameterOrder curve))).mul
      circuit.channel).name produced.output.name := by
  let selectedPolar := polarProgram logarithmic cached polar
  let selectedRegular := regularProgram logarithmic cached regular
  let pivot := Coefficient.coefficient cached.table.val (parameterOrder curve)
  let weighted := (Coherence.exact pivot).mul circuit.channel
  have polarZero : NamedEquivalent polar.val.1.output.name (Coherence.exact 0).name := polar.val.2
  have regularZero : NamedEquivalent regular.val.1.output.name (Coherence.exact 0).name := regular.val.2
  have selectedPolarZero : NamedEquivalent selectedPolar.output.name (Coherence.exact 0).name :=
    (polar.val.1.certifiedView.program.selectedStages_output_equivalent
      (depth logarithmic) (depth_ge logarithmic) ⟨selectedPolar, rfl⟩).symm.trans polarZero
  have selectedRegularZero : NamedEquivalent selectedRegular.output.name (Coherence.exact 0).name :=
    (regular.val.1.certifiedView.program.selectedStages_output_equivalent
      (depth logarithmic) (depth_ge logarithmic) ⟨selectedRegular, rfl⟩).symm.trans regularZero
  have polarGeometric : NamedEquivalent (Coherence.exact 0).name
      (PeriodMatrix.geometricNamed selectedPolar.geometric).name :=
    selectedPolarZero.symm.trans selectedPolar.output_equivalent_geometric
  have regularGeometric : NamedEquivalent (Coherence.exact 0).name
      (PeriodMatrix.geometricNamed selectedRegular.geometric).name :=
    selectedRegularZero.symm.trans selectedRegular.output_equivalent_geometric
  have logOriginal : NamedEquivalent circuit.channel.name logarithmic.val.1.output.name := logarithmic.val.2
  have logGeometric : NamedEquivalent circuit.channel.name
      (PeriodMatrix.geometricNamed logarithmic.val.1.geometric).name :=
    logOriginal.trans logarithmic.val.1.output_equivalent_geometric
  let weightedSource := (GeometricApproximation.exact pivot).mul logarithmic.val.1.geometric
  have weightedGeometric : NamedEquivalent weighted.name (PeriodMatrix.geometricNamed weightedSource).name :=
    PeriodMatrix.ScaledInverseCertificate.coherentMul_equivalent_geometricMul (Coherence.exact pivot) circuit.channel
      (GeometricApproximation.exact pivot) logarithmic.val.1.geometric
      (Comparison.geometricExact_equivalent_exact pivot).symm logGeometric
  have earlier := Comparison.coherentAdd_equivalent_geometricAdd (Coherence.exact 0) weighted
    selectedPolar.geometric weightedSource polarGeometric weightedGeometric
  have whole := Comparison.coherentAdd_equivalent_geometricAdd ((Coherence.exact 0).add weighted)
    (Coherence.exact 0) (selectedPolar.geometric.add weightedSource) selectedRegular.geometric
      earlier regularGeometric
  have zeros : NamedEquivalent weighted.name (((Coherence.exact 0).add weighted).add (Coherence.exact 0)).name :=
    (Arithmetic.Add.coherentAdd_zero_left weighted).symm.trans
      (Arithmetic.Add.coherentAdd_zero_right ((Coherence.exact 0).add weighted)).symm
  exact zeros.trans (whole.trans comparison)

/-- Certify the actual principal path programme and compare it to the retained pivot times the original log channel.

The supplied original polar, logarithmic and regular pairs retain their
complete programmes, actual comparison procedures and exact whole producer
equalities. Neither primitive zero comparison is rebuilt. Each new stage reads
the actual logarithmic cache once and builds one principal path on its
retained adaptive mesh. The finite sample identity derives Cauchy bounds
and an executable output comparison without assuming integral agreement.
-/
def build (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ }) :
    (produced : CertifiedProgram.Program (operations logarithmic cached)) ×
      NamedEquivalent ((Coherence.exact (Coefficient.coefficient cached.table.val (parameterOrder curve))).mul
        circuit.channel).name produced.output.name := by
  let reference := Integration.Program.Comparison.geometricRefinementProgram
    (approximation logarithmic cached polar regular)
  let original := reference.certifiedView.program
  let stages := stage logarithmic cached
  have distance (index : Nat) : Norm.Basic.normSq ((stages index).sample - (original.stage index).sample) ≤
      Basic.quarterRadius 0 index := by
    rewrite [stage_sample logarithmic cached polar regular, RefinementProgram.certifiedView_sample,
      Integration.Program.Comparison.geometricRefinementProgram_integralSample,
      Data.Gaussian.Basic.sub_self, Norm.Basic.normSq_zero]
    exact Basic.quarterRadius_nonneg (Fraction.Order.Basic.le_refl _) index
  have allowances : CertifiedProgram.Allowances stages (original.perturbationScale 0) := by
    intro index
    change (circuit.1.dyadicModel (coefficient cached) (depth logarithmic index)).aggregateAllowance ≤ _
    rewrite [Circle.Integral.Entries.dyadicModel_allowance]
    exact Basic.quarterRadius_nonneg (original.perturbationScale_nonnegative 0
      (Fraction.Order.Basic.le_refl _)) index
  let produced := original.perturb stages 0 (Fraction.Order.Basic.le_refl _) distance allowances
  have close (index : Nat) : Norm.Basic.normSq ((original.stage index).sample - (produced.stage index).sample) ≤
      Basic.quarterRadius 0 index := by
    rewrite [CertifiedProgram.Program.perturb_stage, Norm.Bounds.normSq_sub_symm]
    exact distance index
  let compared := original.output_equivalent_of_samples_close produced 0
    (Fraction.Order.Basic.le_refl _) close
  let source := Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
    (approximation logarithmic cached polar regular)
  exact ⟨produced, logarithmicComparison logarithmic cached polar regular produced (source.trans compared)⟩

/-- The same supplied complete principal programme pair retains its actual original producer and primitive caches. -/
@[expose] def View (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ }) :=
  { value : _ // value = build logarithmic cached polar regular }

/-- Each produced principal cache keeps the original requested stage as its actual retained source index. -/
theorem build_index (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ })
    (index : Nat) : ((build logarithmic cached polar regular).1.stage index).model.1 = index := by
  unfold build
  rewrite [CertifiedProgram.Program.perturb_stage]
  rfl

/-- Each produced principal cache retains the complete literal supplied logarithmic stage cache. -/
theorem build_source (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ })
    (index : Nat) : ((build logarithmic cached polar regular).1.stage index).model.2.1.val =
      logarithmic.val.1.stage index := by
  unfold build
  rewrite [CertifiedProgram.Program.perturb_stage]
  rfl

/-- The produced principal sample reads its actual retained same-circuit path at the supplied logarithmic mesh depth. -/
theorem build_sample (cached : ParameterPrimitives retained circuit)
    (polar : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ })
    (regular : { value : (program : RefinementProgram) ×
      NamedEquivalent program.output.name (Coherence.exact 0).name //
      value = ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ })
    (index : Nat) : ((build logarithmic cached polar regular).1.stage index).sample =
      (circuit.1.dyadicModel (coefficient cached) (depth logarithmic index)).integralSample := by
  unfold build
  rewrite [CertifiedProgram.Program.perturb_stage]
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.ParameterPrimitives.Program

end
