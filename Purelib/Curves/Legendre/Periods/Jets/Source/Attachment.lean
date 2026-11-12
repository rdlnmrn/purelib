module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Stage
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Legendre.Periods.Jets.Specification
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
public import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original six-program Legendre source attachment

Every original period-program stage retains the exact regular-chart source
chain on its original lifted-cycle representative. The six literal ordered
cell lists are tied to that same chain. Each source stage retains its original finite endpoint bank, prepared
primitive requests and common-owner branch admissions. Their count-paid
relation bounds are derived from those same original sources.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Curves.Legendre.PicardFuchs

set_option genInjectivity false in
/-- The actual shared regular-chart sources of the six original certified period programs.

The original frame, lifted cycle and six programs remain indexed. Each
retained stage preserves its exact original cell order, chart owners,
selected inverse-model caches and sheet transports. Cell-list equalities
bind those source caches to the original numerical integration programs;
the actual prepared endpoint and branch admissions derive local and
whole-row sample payments without a final theorem certificate as input. -/
structure Attachment {parameter : Canonical} (frame : Paths.Frame parameter) (cycle : LiftedCycleRefinement 2)
    (value : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter coordinate) cycle)
    (first : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter coordinate) cycle)
    (second : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter coordinate) cycle) where
  /-- The exact original source chain retained at every original cycle refinement. -/
  stages : ∀ index, Stage parameter (cycle.liftedPath index) index
  /-- The first original value program consumes the literal first value-cell list of that source chain. -/
  valueZero_eq : ∀ index, ((value 0).integral.model index).cells = (stages index).sources.valueZero
  /-- The second original value program consumes the literal second value-cell list of that source chain. -/
  valueOne_eq : ∀ index, ((value 1).integral.model index).cells = (stages index).sources.valueOne
  /-- The first original first-derivative program consumes that same chain's first derivative-cell list. -/
  firstZero_eq : ∀ index, ((first 0).integral.model index).cells = (stages index).sources.firstZero
  /-- The second original first-derivative program consumes that same chain's weighted derivative-cell list. -/
  firstOne_eq : ∀ index, ((first 1).integral.model index).cells = (stages index).sources.firstOne
  /-- The first original second-derivative program consumes that same chain's first second-derivative-cell list. -/
  secondZero_eq : ∀ index, ((second 0).integral.model index).cells = (stages index).sources.secondZero
  /-- The second original second-derivative program consumes that same chain's weighted second-derivative-cell list. -/
  secondOne_eq : ∀ index, ((second 1).integral.model index).cells = (stages index).sources.secondOne

constructive_injectivity Attachment

namespace Attachment

variable {parameter : Canonical} {frame : Paths.Frame parameter} {cycle : LiftedCycleRefinement 2}
    {value : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.valueSpecification parameter coordinate) cycle}
    {first : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.firstDerivativeSpecification parameter coordinate) cycle}
    {second : ∀ coordinate, CertifiedPeriodProgram (Fibre.frameCurve frame)
      (Specification.secondDerivativeSpecification parameter coordinate) cycle}

/-- Equal original ordered cell lists retain the same original finite integration sample. -/
private theorem sample_eq (model : PathModel) (cells : List CellModel) (equal : model.cells = cells) :
    model.integralSample = (PathModel.mk cells).integralSample :=
  congrArg (fun original => (PathModel.mk original).integralSample) equal

/-- The first source relation sample is the actual original first-and-value program sample combination. -/
theorem zero_integralSample (attached : Attachment frame cycle value first second) (index : Nat) :
    (PathModel.mk (attached.stages index).sources.zero).integralSample =
      Clearance.connectionDenominator parameter * ((first 0).integral.model index).integralSample -
        (parameter * ((value 0).integral.model index).integralSample -
          ((value 1).integral.model index).integralSample) := by
  have result := (attached.stages index).sources.zero_integralSample
  rw [← sample_eq _ _ (attached.firstZero_eq index), ← sample_eq _ _ (attached.valueZero_eq index),
    ← sample_eq _ _ (attached.valueOne_eq index)] at result
  exact result

/-- The second source relation sample is the actual original weighted-first-and-value program sample combination. -/
theorem one_integralSample (attached : Attachment frame cycle value first second) (index : Nat) :
    (PathModel.mk (attached.stages index).sources.one).integralSample =
      Clearance.connectionDenominator parameter * ((first 1).integral.model index).integralSample -
        (parameter * ((value 0).integral.model index).integralSample -
          parameter * ((value 1).integral.model index).integralSample) := by
  have result := (attached.stages index).sources.one_integralSample
  rw [← sample_eq _ _ (attached.firstOne_eq index), ← sample_eq _ _ (attached.valueZero_eq index),
    ← sample_eq _ _ (attached.valueOne_eq index)] at result
  exact result

/-- The scalar source relation sample is the actual original second, first and value program sample combination. -/
theorem scalar_integralSample (attached : Attachment frame cycle value first second) (index : Nat) :
    (PathModel.mk (attached.stages index).sources.scalar).integralSample =
      4 * parameter * (1 - parameter) * ((second 0).integral.model index).integralSample +
        4 * (1 - 2 * parameter) * ((first 0).integral.model index).integralSample -
          ((value 0).integral.model index).integralSample := by
  have result := (attached.stages index).sources.scalar_integralSample
  rw [← sample_eq _ _ (attached.secondZero_eq index), ← sample_eq _ _ (attached.firstZero_eq index),
    ← sample_eq _ _ (attached.valueZero_eq index)] at result
  exact result

/-- The original first connection sample combination meets its internally constructed geometric row request. -/
theorem zero_error_le (attached : Attachment frame cycle value first second) (index : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (Clearance.connectionDenominator parameter * ((first 0).integral.model index).integralSample -
        (parameter * ((value 0).integral.model index).integralSample -
          ((value 1).integral.model index).integralSample)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 1 index := by
  have bound := (attached.stages index).zero_error_le
  rewrite [attached.zero_integralSample index] at bound
  exact bound

/-- The original second connection sample combination meets that same internally constructed row request. -/
theorem one_error_le (attached : Attachment frame cycle value first second) (index : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (Clearance.connectionDenominator parameter * ((first 1).integral.model index).integralSample -
        (parameter * ((value 0).integral.model index).integralSample -
          parameter * ((value 1).integral.model index).integralSample)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 1 index := by
  have bound := (attached.stages index).one_error_le
  rewrite [attached.one_integralSample index] at bound
  exact bound

/-- The original scalar Picard–Fuchs sample combination meets its internally constructed row request. -/
theorem scalar_error_le (attached : Attachment frame cycle value first second) (index : Nat) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (4 * parameter * (1 - parameter) * ((second 0).integral.model index).integralSample +
        4 * (1 - 2 * parameter) * ((first 0).integral.model index).integralSample -
          ((value 0).integral.model index).integralSample) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 1 index := by
  have bound := (attached.stages index).scalar_error_le
  rewrite [attached.scalar_integralSample index] at bound
  exact bound

end Attachment

end Purelib.Curves.Legendre.Periods.Jets.Source

end
