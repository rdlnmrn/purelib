module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Schedule.Common
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Subdivision
public import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Path.Primitive
import Purelib.Integration.Path.Primitive.Polynomial
public import Purelib.Integration.Program.Comparison.Budget
public import Purelib.Integration.Program.Comparison.Scheduled
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Approximation

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational

open Purelib.Approximation.Schedule

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Curves.Legendre.Periods.Jets

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Integration

open Purelib.Integration.Path

open Purelib.Integration.Path.Primitive

open Purelib.Integration.Program.Comparison

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.PicardFuchs

open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Geometric.Coherent
open Purelib.Riemann.Periods
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

/-! ## Fraction-free Picard--Fuchs residual -/

/-- The retained second-derivative value channel scaled by four times the original parameter times one minus that
parameter. -/
def picardFuchsSecondTerm {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  Mul.scaleName (4 * parameter * (1 - parameter)) (jet.secondName 0)

/-- The retained first-derivative value channel scaled by four times one minus twice the original parameter. -/
def picardFuchsFirstTerm {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  Mul.scaleName (4 * (1 - 2 * parameter)) (jet.firstName 0)

/-- The actual coherent arithmetic expression `4 lambda (1-lambda) u'' + 4(1-2 lambda) u' - u`. -/
def picardFuchsResidual {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Coherent.CoherentNamed :=
  CoherentNamed.add
    (CoherentNamed.add
      (picardFuchsSecondTerm jet)
        (picardFuchsFirstTerm jet))
    (CoherentNamed.neg (jet.valueName 0))

/-- The second-derivative term at the original synchronized period-program stage. -/
def picardFuchsSecondGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : GeometricApproximation :=
  (GeometricApproximation.exact (4 * parameter * (1 - parameter))).mul (jet.second 0).integral.geometric

/-- The first-derivative term at that same original period-program stage. -/
def picardFuchsFirstGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : GeometricApproximation :=
  (GeometricApproximation.exact (4 * (1 - 2 * parameter))).mul (jet.first 0).integral.geometric

/-- The scalar relation computed from the original second, first and value samples at one index. -/
def picardFuchsResidualGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : GeometricApproximation :=
  ((picardFuchsSecondGeometric jet).add (picardFuchsFirstGeometric jet)).sub (jet.value 0).integral.geometric

/-- The original second-derivative arithmetic name realizes its same-index scaled program samples. -/
def picardFuchsSecond_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    Gaussian.Equivalence.NamedEquivalent (picardFuchsSecondTerm jet).name
      (PeriodMatrix.geometricNamed (picardFuchsSecondGeometric jet)).name :=
  Program.Comparison.scale_output_equivalent_geometric _ _

/-- The original first-derivative arithmetic name realizes its same-index scaled program samples. -/
def picardFuchsFirst_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    Gaussian.Equivalence.NamedEquivalent (picardFuchsFirstTerm jet).name
      (PeriodMatrix.geometricNamed (picardFuchsFirstGeometric jet)).name :=
  Program.Comparison.scale_output_equivalent_geometric _ _

/-- The original Picard–Fuchs arithmetic residual realizes the original synchronized relation samples. -/
def picardFuchsResidual_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    Gaussian.Equivalence.NamedEquivalent (picardFuchsResidual jet).name
      (PeriodMatrix.geometricNamed (picardFuchsResidualGeometric jet)).name :=
  Comparison.coherentSub_equivalent_geometricSub _ _ _ _
    (Comparison.coherentAdd_equivalent_geometricAdd _ _ _ _
      (picardFuchsSecond_equivalent_geometric jet) (picardFuchsFirst_equivalent_geometric jet))
    (Program.Comparison.output_equivalent_geometric _)

/-- The actual original scalar source relation pays its geometric stage request internally. -/
theorem picardFuchsResidual_error_le {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((picardFuchsResidualGeometric jet).sample index) ≤
      Geometric.Basic.quarterRadius 1 index := by
  dsimp only [picardFuchsResidualGeometric, picardFuchsSecondGeometric, picardFuchsFirstGeometric]
  simp only [GeometricApproximation.sub_sample, GeometricApproximation.add_sample,
    GeometricApproximation.mul_sample, GeometricApproximation.exact_sample, RefinementProgram.geometric_sample]
  exact jet.source.scalar_error_le index

/-- The original scalar-relation cells from the same admitted six-program stages. -/
def picardFuchsResidualModels {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (index : Nat) : PathModel :=
  PathModel.mk (jet.source.stages index).sources.scalar

/-- The retained original scalar cells read the actual synchronized residual sample. -/
theorem picardFuchsResidualModels_integralSample {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) (index : Nat) :
    (picardFuchsResidualModels jet index).integralSample = (picardFuchsResidualGeometric jet).sample index := by
  dsimp only [picardFuchsResidualModels]
  rw [jet.source.scalar_integralSample index]
  dsimp only [picardFuchsResidualGeometric, picardFuchsSecondGeometric, picardFuchsFirstGeometric]
  rw [GeometricApproximation.sub_sample, GeometricApproximation.add_sample,
    GeometricApproximation.mul_sample, GeometricApproximation.mul_sample,
    GeometricApproximation.exact_sample, GeometricApproximation.exact_sample,
    RefinementProgram.geometric_sample, RefinementProgram.geometric_sample, RefinementProgram.geometric_sample]

/-- The scalar-relation polynomial cells are exact; the six original differential allowances remain retained. -/
theorem picardFuchsResidualModels_aggregateAllowance {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) (index : Nat) :
    (picardFuchsResidualModels jet index).aggregateAllowance = 0 :=
  (jet.source.stages index).sources.scalar_aggregateAllowance

/-- Preserve the actual original scalar cells with the original synchronized arithmetic bounds. -/
def picardFuchsResidualProgram {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : Program.Gaussian.Basic.RefinementProgram :=
  let original := Program.Comparison.geometricRefinementProgram (picardFuchsResidualGeometric jet)
  original.withModels (picardFuchsResidualModels jet) (by
    intro index
    rw [Program.Comparison.geometricRefinementProgram_integralSample]
    exact picardFuchsResidualModels_integralSample jet index) (by
    intro index
    rw [picardFuchsResidualModels_aggregateAllowance]
    exact Geometric.Basic.quarterRadius_nonneg (picardFuchsResidualGeometric jet).errorScale_nonneg index)

/-- Read the retained actual whole-cycle scalar program sample. -/
theorem picardFuchsResidualProgram_integralSample {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) (index : Nat) :
    ((picardFuchsResidualProgram jet).model index).integralSample =
      (picardFuchsResidualGeometric jet).sample index := picardFuchsResidualModels_integralSample jet index

/-- The original Picard–Fuchs residual realizes its retained original cell program. -/
def picardFuchsResidual_equivalent_program {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    NamedEquivalent (picardFuchsResidual jet).name (picardFuchsResidualProgram jet).output.name :=
  (picardFuchsResidual_equivalent_geometric jet).trans
    ((Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram _).trans
      (Program.Comparison.refinementProgram_output_equivalent_of_samples_eq _ _ (by
        intro index
        rw [Program.Comparison.geometricRefinementProgram_integralSample,
          picardFuchsResidualProgram_integralSample])))

/-- The actual initial basepoint primitive closes a nonempty boundary retaining the original scalar cells.

Every later stage closes its own original lifted representative. No
cross-stage equality of its basepoint primitive values is required. -/
def picardFuchsPrimitive {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : ClosedPrimitiveBoundary :=
  ClosedPrimitiveBoundary.ofClosedSampleComparison (jet.source.stages 0).base.original.scalar.channel
    (picardFuchsResidualProgram jet) 1 (by decide) (by
      intro index
      rw [picardFuchsResidualProgram_integralSample]
      exact picardFuchsResidual_error_le jet index)

/-- The retained original scalar boundary has its actual row output and empty-tail zero. -/
theorem picardFuchsPrimitive_integralSum {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame) :
    (picardFuchsPrimitive jet).integralSum =
      CoherentNamed.add (picardFuchsResidualProgram jet).output (Coherence.exact 0) := by
  unfold picardFuchsPrimitive
  rw [ClosedPrimitiveBoundary.ofClosedSampleComparison_integralSum]

/-- Derive the actual arithmetic residual's comparison with this retained scalar row boundary. -/
def picardFuchsResidual_equivalent_primitive {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Jets.Basic.SynchronizedPeriodJet frame)
    (primitive : ClosedPrimitiveBoundary)
    (retained : primitive.integralSum =
      CoherentNamed.add (picardFuchsResidualProgram jet).output (Coherence.exact 0)) :
    NamedEquivalent (picardFuchsResidual jet).name primitive.integralSum.name := by
  rw [retained]
  exact (picardFuchsResidual_equivalent_program jet).trans
    (Add.coherentAdd_zero_right (picardFuchsResidualProgram jet).output).symm

/-- The cached original-name comparison attempts for the actual scalar primitive boundary. -/
def PicardFuchsComparison {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) (primitive : ClosedPrimitiveBoundary) :=
  Scheduled.ScheduledComparison (picardFuchsResidual jet) primitive.integralSum 1

/-- Retain the assembled scalar scale and the actual already prepared carriers' synchronization payment. -/
def picardFuchsBudget {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) {primitive : ClosedPrimitiveBoundary}
    (comparison : PicardFuchsComparison jet primitive) : Budget.JetErrorBudget :=
  Budget.JetErrorBudget.ofPrimitiveComparison (picardFuchsResidualGeometric jet).errorScale
    (Budget.JetErrorBudget.synchronizationScale comparison.leftCarrier.errorScale comparison.rightCarrier.errorScale)
    (picardFuchsResidualGeometric jet).errorScale_nonneg
    (Budget.JetErrorBudget.synchronizationScale_nonnegative comparison.leftCarrier.errorScale_nonneg
      comparison.rightCarrier.errorScale_nonneg)

set_option genInjectivity false in
/-- Finite analytic evidence which realizes the fixed symbolic `picardFuchsReduction` on the synchronized period jet. -/
structure PicardFuchsCertificate {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) where
  /-- The original closed primitive boundary realizing the retained differential reduction. -/ primitive :
    ClosedPrimitiveBoundary
  /-- The retained common schedule for the original residual and primitive comparison programs. -/ schedule :
    Common.CommonSchedule
  /-- The retained complete finite error allocation for the residual comparison. -/ budget : Budget.JetErrorBudget
  /-- The actual comparison payloads retained at their requested original starts. -/
  comparison : PicardFuchsComparison jet primitive
  /-- The public schedule reads those same retained comparison payloads. -/
  schedule_eq : schedule = comparison.schedule
  /-- The original residual and primitive-boundary samples satisfy the retained scheduled geometric error bound. -/
    residual_samples_close : forall request,
    Data.Gaussian.Norm.Basic.normSq
        (((RefinementProgram.ofCoherentNamed
          (picardFuchsResidual jet)).model
            (schedule.targetIndex request)).integralSample -
          ((RefinementProgram.ofCoherentNamed primitive.integralSum).model
            (schedule.comparisonIndex request)).integralSample) <=
      Geometric.Basic.quarterRadius budget.total request

constructive_injectivity PicardFuchsCertificate

namespace PicardFuchsCertificate

/-- Compute parameter clearance from this certificate's original jet frame. -/
def clearance
    {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (_certificate : Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Clearance.ParameterClearance parameter :=
  Clearance.ParameterClearance.ofFrame frame

/-- Construct the ordered common subdivision from this certificate's original jet programs. -/
def subdivision
    {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (_certificate : Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Subdivision.JetCommonSubdivision jet :=
  Subdivision.JetCommonSubdivision.ofJet jet

/-- Construct the operational scalar relation from its admitted original six-program jet alone.

The actual source cells, endpoint admissions and exact primitive reduction
derive the numerical row comparison. Its original-name comparison attempts
and schedule remain cached in the resulting certificate. -/
def ofJet {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Jets.Basic.SynchronizedPeriodJet frame) : PicardFuchsCertificate jet := by
  let primitive := picardFuchsPrimitive jet
  let comparison : PicardFuchsComparison jet primitive :=
    Scheduled.fromEquivalent _ _
      (picardFuchsResidual_equivalent_primitive jet primitive (picardFuchsPrimitive_integralSum jet)) 1 (by decide)
  let budget := picardFuchsBudget jet comparison
  exact
    { primitive := primitive
      schedule := comparison.schedule
      budget := budget
      comparison := comparison
      schedule_eq := rfl
      residual_samples_close := fun request => (comparison.samples_close request).trans
        (Geometric.Basic.quarterRadius_scale_mono
          (Budget.JetErrorBudget.one_le_total budget (by exact le_refl 1)) request) }

/-- The finite comparison identifies the actual residual with the exact primitive dictated by the polynomial reduction.
-/
def residual_equivalent_primitive
  {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Gaussian.Equivalence.NamedEquivalent (Jets.PicardFuchs.picardFuchsResidual jet).name
      certificate.primitive.integralSum.name :=
  Scheduled.namedEquivalent_of_selections _ _ 1 (by decide) certificate.comparison.attempts

/-- Finite operational Legendre Picard--Fuchs equation. Its six channels use one displayed lifted cycle, and the
certificate exposes the common schedule and complete finite error allocation used to make the residual vanish. -/
def operational_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Jets.Basic.SynchronizedPeriodJet frame}
    (certificate : Jets.PicardFuchs.PicardFuchsCertificate jet) :
    Gaussian.Equivalence.NamedEquivalent (Jets.PicardFuchs.picardFuchsResidual jet).name
      (Coherence.exact 0).name :=
  NamedEquivalent.trans
    certificate.residual_equivalent_primitive
    (Primitive.exactDifferential_closed_operational_zero
      certificate.primitive)

end PicardFuchsCertificate

end Purelib.Curves.Legendre.Periods.Jets.PicardFuchs

end
