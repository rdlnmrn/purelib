module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Fin.Two
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Schedule.Common
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Basic
public import Purelib.Curves.Legendre.Periods.Jets.Subdivision
import Purelib.Curves.Legendre.PicardFuchs.Clearance
public import Purelib.Curves.Legendre.PicardFuchs.Connection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Path.Primitive
import Purelib.Integration.Path.Primitive.Polynomial
public import Purelib.Integration.Program.Comparison.Budget
public import Purelib.Integration.Program.Comparison.Scheduled
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Approximation

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Coherent

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Rational

open Purelib.Approximation.Schedule

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Periods

open Purelib.Curves.Legendre.Periods.Jets

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Curves.Legendre.PicardFuchs.Clearance

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

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Geometric.Coherent
open Purelib.Integration.Program
open Purelib.Riemann.Periods
open Purelib.Data.Fin
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

/-- The canonical symbolic reduction selected by a row of the genus-one period vector. -/
def connectionReduction (parameter :
  Data.Gaussian.Basic.Canonical) (coordinate : Fin 2) :
    Connection.ConnectionReduction parameter :=
  if coordinate = 0 then Connection.firstConnectionReduction parameter
  else Connection.secondConnectionReduction parameter

/-- The zero coordinate uses the first original symbolic connection reduction. -/
@[simp] theorem connectionReduction_zero (parameter :
  Data.Gaussian.Basic.Canonical) :
    connectionReduction parameter 0 = Connection.firstConnectionReduction
      parameter :=
  rfl

/-- The one coordinate uses the second original symbolic connection reduction. -/
@[simp] theorem connectionReduction_one (parameter :
  Data.Gaussian.Basic.Canonical) :
    connectionReduction parameter 1 =
      Connection.secondConnectionReduction parameter := by
  unfold connectionReduction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The left side `2 lambda (1-lambda) u'` of one connection row. -/
def connectionScaledFirst {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  Mul.scaleName (ParameterClearance.connectionDenominator parameter)
    (jet.firstName coordinate)

/-- The fraction-free connection matrix numerator `[[lambda,-1],[lambda,-lambda]]` acting on the two value channels. -/
def connectionAction {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  if coordinate = 0 then
    Additive.subtractName (Mul.scaleName parameter (jet.valueName 0)) (jet.valueName 1)
  else
    Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
      (Mul.scaleName parameter (jet.valueName 1))

/-- The original scaled first-derivative samples at their same retained period-program indices. -/
def connectionScaledFirstGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : GeometricApproximation :=
  (GeometricApproximation.exact (ParameterClearance.connectionDenominator parameter)).mul
    (jet.first coordinate).integral.geometric

/-- The connection action computed from the original synchronized value samples. -/
def connectionActionGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : GeometricApproximation :=
  let left := (GeometricApproximation.exact parameter).mul (jet.value 0).integral.geometric
  if coordinate = 0 then left.sub (jet.value 1).integral.geometric
  else left.sub ((GeometricApproximation.exact parameter).mul (jet.value 1).integral.geometric)

/-- The actual original row residual at one synchronized period-program stage. -/
def connectionResidualGeometric {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : GeometricApproximation :=
  (connectionScaledFirstGeometric jet coordinate).sub (connectionActionGeometric jet coordinate)

/-- The original scaled derivative name realizes the original same-stage samples. -/
def connectionScaledFirst_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet coordinate).name
      (PeriodMatrix.geometricNamed (connectionScaledFirstGeometric jet coordinate)).name :=
  Program.Comparison.scale_output_equivalent_geometric _ _

/-- The original arithmetic action name realizes the same original value-program samples. -/
def connectionAction_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    NamedEquivalent (connectionAction jet coordinate).name
      (PeriodMatrix.geometricNamed (connectionActionGeometric jet coordinate)).name := by
  unfold connectionAction connectionActionGeometric
  by_cases zero : coordinate = 0
  · rw [if_pos zero, if_pos zero]
    exact Comparison.coherentSub_equivalent_geometricSub _ _ _ _
      (Program.Comparison.scale_output_equivalent_geometric _ _) (Program.Comparison.output_equivalent_geometric _)
  · rw [if_neg zero, if_neg zero]
    exact Comparison.coherentSub_equivalent_geometricSub _ _ _ _
      (Program.Comparison.scale_output_equivalent_geometric _ _)
      (Program.Comparison.scale_output_equivalent_geometric _ _)

/-- The original row difference realizes the actual synchronized residual stream. -/
def connectionResidual_equivalent_geometric {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    NamedEquivalent (Additive.subtractName (connectionScaledFirst jet coordinate)
      (connectionAction jet coordinate)).name
      (PeriodMatrix.geometricNamed (connectionResidualGeometric jet coordinate)).name :=
  Comparison.coherentSub_equivalent_geometricSub _ _ _ _
    (connectionScaledFirst_equivalent_geometric jet coordinate) (connectionAction_equivalent_geometric jet coordinate)

/-- The original admitted source bounds the actual synchronized first-row or second-row residual internally. -/
theorem connectionResidual_error_le {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq ((connectionResidualGeometric jet coordinate).sample index) ≤
      Geometric.Basic.quarterRadius 1 index := by
  rcases Two.finTwo_cases coordinate with zero | one
  · cases zero
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rw [if_pos (rfl : (0 : Fin 2) = 0)]
    simp only [GeometricApproximation.sub_sample, GeometricApproximation.mul_sample,
      GeometricApproximation.exact_sample, RefinementProgram.geometric_sample]
    exact jet.source.zero_error_le index
  · cases one
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    simp only [GeometricApproximation.sub_sample,
      GeometricApproximation.mul_sample, GeometricApproximation.exact_sample,
      RefinementProgram.geometric_sample]
    exact jet.source.one_error_le index

/-- The literal original relation-cell models selected from the same admitted source stages. -/
def connectionResidualModels {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) (index : Nat) : PathModel :=
  let stage := jet.source.stages index
  PathModel.mk (if coordinate = 0 then stage.sources.zero else stage.sources.one)

/-- The retained original relation cells read the original synchronized residual sample. -/
theorem connectionResidualModels_integralSample {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) (index : Nat) :
    (connectionResidualModels jet coordinate index).integralSample =
      (connectionResidualGeometric jet coordinate).sample index := by
  rcases Two.finTwo_cases coordinate with zero | one
  · cases zero
    dsimp only [connectionResidualModels]
    rw [if_pos (rfl : (0 : Fin 2) = 0)]
    rw [jet.source.zero_integralSample index]
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rw [if_pos (rfl : (0 : Fin 2) = 0)]
    simp only [GeometricApproximation.sub_sample, GeometricApproximation.mul_sample,
      GeometricApproximation.exact_sample, RefinementProgram.geometric_sample]
    rfl
  · cases one
    dsimp only [connectionResidualModels]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    rw [jet.source.one_integralSample index]
    dsimp only [connectionResidualGeometric, connectionScaledFirstGeometric, connectionActionGeometric]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    simp only [GeometricApproximation.sub_sample,
      GeometricApproximation.mul_sample, GeometricApproximation.exact_sample,
      RefinementProgram.geometric_sample]
    rfl

/-- The actual original relation-cell model has zero exact-polynomial allowance. -/
theorem connectionResidualModels_aggregateAllowance {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) (index : Nat) :
    (connectionResidualModels jet coordinate index).aggregateAllowance = 0 := by
  dsimp only [connectionResidualModels]
  by_cases zero : coordinate = 0
  · rw [if_pos zero]
    exact (jet.source.stages index).sources.zero_aggregateAllowance
  · rw [if_neg zero]
    exact (jet.source.stages index).sources.one_aggregateAllowance

/-- The original row program retains its actual source-cell lists and the synchronized programs' quantitative bounds.

The model sequence comes from the admitted original stage. Its scalar
readbacks transport the existing geometric arithmetic bounds without
discarding those cells or resetting the numerical source residuals. -/
def connectionResidualProgram {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : Program.Gaussian.Basic.RefinementProgram :=
  let original := Program.Comparison.geometricRefinementProgram (connectionResidualGeometric jet coordinate)
  original.withModels (connectionResidualModels jet coordinate) (by
    intro index
    rw [Program.Comparison.geometricRefinementProgram_integralSample]
    exact connectionResidualModels_integralSample jet coordinate index) (by
    intro index
    rw [connectionResidualModels_aggregateAllowance]
    exact Geometric.Basic.quarterRadius_nonneg (connectionResidualGeometric jet coordinate).errorScale_nonneg index)

/-- The whole-row program reads the actual original synchronized relation sample. -/
theorem connectionResidualProgram_integralSample {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) (index : Nat) :
    ((connectionResidualProgram jet coordinate).model index).integralSample =
      (connectionResidualGeometric jet coordinate).sample index :=
  connectionResidualModels_integralSample jet coordinate index

/-- The original arithmetic residual realizes the retained original row-cell program. -/
def connectionResidual_equivalent_program {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    NamedEquivalent (Additive.subtractName (connectionScaledFirst jet coordinate)
      (connectionAction jet coordinate)).name (connectionResidualProgram jet coordinate).output.name :=
  (connectionResidual_equivalent_geometric jet coordinate).trans
    ((Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram _).trans
      (Program.Comparison.refinementProgram_output_equivalent_of_samples_eq _ _ (by
        intro index
        rw [Program.Comparison.geometricRefinementProgram_integralSample,
          connectionResidualProgram_integralSample])))

/-- The initial representative's actual original primitive channel names the closed boundary's basepoint.

Later stages retain their own actual bank basepoints in `jet.source` and
close their own repeated endpoint differences. This definition does not
identify primitive values at different basepoints. -/
def connectionPrimitiveSource {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  let base := (jet.source.stages 0).base.original
  if coordinate = 0 then base.zero.channel else base.one.channel

/-- A retained original primitive channel with its scalar owner readback. -/
def ConnectionPrimitiveReading {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2) :=
  {source : CoherentNamed // source = connectionPrimitiveSource jet coordinate}

/-- Construct the closed original row boundary from its actual source-stage estimates. -/
def connectionPrimitive {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (source : ConnectionPrimitiveReading jet coordinate := ⟨connectionPrimitiveSource jet coordinate, rfl⟩) :
    ClosedPrimitiveBoundary :=
  ClosedPrimitiveBoundary.ofClosedSampleComparison source.val
    (connectionResidualProgram jet coordinate) 1 (by decide) (by
      intro index
      rw [connectionResidualProgram_integralSample]
      exact connectionResidual_error_le jet coordinate index)

/-- The actual retained row boundary has the original row output and empty-tail zero. -/
theorem connectionPrimitive_integralSum {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (source : ConnectionPrimitiveReading jet coordinate := ⟨connectionPrimitiveSource jet coordinate, rfl⟩) :
    (connectionPrimitive jet coordinate source).integralSum =
      add (connectionResidualProgram jet coordinate).output (Coherence.exact 0) := by
  unfold connectionPrimitive
  rw [ClosedPrimitiveBoundary.ofClosedSampleComparison_integralSum]

/-- The original arithmetic residual realizes a retained boundary with this actual original row output. -/
def connectionResidual_equivalent_primitive {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (primitive : ClosedPrimitiveBoundary)
    (retained : primitive.integralSum = add (connectionResidualProgram jet coordinate).output (Coherence.exact 0)) :
    NamedEquivalent (Additive.subtractName (connectionScaledFirst jet coordinate)
      (connectionAction jet coordinate)).name primitive.integralSum.name := by
  rw [retained]
  exact (connectionResidual_equivalent_program jet coordinate).trans
    (Add.coherentAdd_zero_right (connectionResidualProgram jet coordinate).output).symm

/-- The first connection row is the original parameter-scaled first value minus the second value. -/
@[simp] theorem connectionAction_zero {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) :
    connectionAction jet 0 =
      Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
        (jet.valueName 1) := rfl

/-- The second connection row subtracts the parameter-scaled second value from the parameter-scaled first value. -/
@[simp] theorem connectionAction_one {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) :
    connectionAction jet 1 =
      Additive.subtractName (Mul.scaleName parameter (jet.valueName 0))
        (Mul.scaleName parameter (jet.valueName 1)) := by
  unfold connectionAction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- Add the retained coordinate primitive-boundary integral to the original connection action. -/
def connectionWithPrimitive {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame)
    (primitive : Fin 2 -> ClosedPrimitiveBoundary)
    (coordinate : Fin 2) : CoherentNamed :=
  add (connectionAction jet coordinate)
    (primitive coordinate).integralSum

/-- Adding an original closed primitive boundary preserves the actual connection action. -/
def connectionWithPrimitive_equivalent_action {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame)
    (primitive : Fin 2 → ClosedPrimitiveBoundary) (coordinate : Fin 2) :
    NamedEquivalent (connectionWithPrimitive jet primitive coordinate).name (connectionAction jet coordinate).name :=
  (Congruence.coherentAdd_respects _ _ _ _ (NamedEquivalent.refl _)
    (exactDifferential_closed_operational_zero (primitive coordinate))).trans
    (Add.coherentAdd_zero_right (connectionAction jet coordinate))

/-- The actual original source stages prove a row with its retained original primitive boundary. -/
def connectionScaledFirst_equivalent_primitive {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (jet : Basic.SynchronizedPeriodJet frame)
    (primitive : Fin 2 → ClosedPrimitiveBoundary)
    (retained : ∀ coordinate, (primitive coordinate).integralSum =
      add (connectionResidualProgram jet coordinate).output (Coherence.exact 0)) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet coordinate).name
      (connectionWithPrimitive jet primitive coordinate).name :=
  (Additive.equivalent_of_sub_zero _ _
    ((connectionResidual_equivalent_primitive jet coordinate (primitive coordinate) (retained coordinate)).trans
      (exactDifferential_closed_operational_zero (primitive coordinate)))).trans
    (connectionWithPrimitive_equivalent_action jet primitive coordinate).symm

/-- One cached original-name comparison family for a retained row boundary. -/
def ConnectionComparisons {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) (primitive : Fin 2 → ClosedPrimitiveBoundary) :=
  (coordinate : Fin 2) → Scheduled.ScheduledComparison (connectionScaledFirst jet coordinate)
    (connectionWithPrimitive jet primitive coordinate) 1

/-- Retain both assembled row scales and the actual already prepared carriers' tail payments. -/
def connectionBudget {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) {primitive : Fin 2 → ClosedPrimitiveBoundary}
    (comparisons : ConnectionComparisons jet primitive) : Budget.JetErrorBudget :=
  let zero := comparisons 0
  let one := comparisons 1
  Budget.JetErrorBudget.ofPrimitiveComparison
    ((connectionResidualGeometric jet 0).errorScale + (connectionResidualGeometric jet 1).errorScale)
    (Budget.JetErrorBudget.synchronizationScale zero.leftCarrier.errorScale zero.rightCarrier.errorScale +
      Budget.JetErrorBudget.synchronizationScale one.leftCarrier.errorScale one.rightCarrier.errorScale)
    (add_nonneg (connectionResidualGeometric jet 0).errorScale_nonneg
      (connectionResidualGeometric jet 1).errorScale_nonneg)
    (add_nonneg
      (Budget.JetErrorBudget.synchronizationScale_nonnegative zero.leftCarrier.errorScale_nonneg
        zero.rightCarrier.errorScale_nonneg)
      (Budget.JetErrorBudget.synchronizationScale_nonnegative one.leftCarrier.errorScale_nonneg
        one.rightCarrier.errorScale_nonneg))

set_option genInjectivity false in
/-- Complete finite evidence for both rows of the fraction-free connection. The canonical polynomial reductions are
fixed by `connectionReduction`; this certificate supplies their closed primitive realizations and one common finite
schedule/error allocation for comparing the actual period programs. -/
structure ConnectionCertificate {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) where
  /-- The retained closed primitive boundary for each original connection coordinate. -/ primitive : Fin 2 ->
    ClosedPrimitiveBoundary
  /-- The retained common finite schedule for the original target and comparison programs. -/ schedule :
    Common.CommonSchedule
  /-- The retained complete finite error allocation for the original connection comparison. -/ budget :
    Budget.JetErrorBudget
  /-- The actual original-name comparison attempts, cached before their schedules are joined. -/
  comparisons : ConnectionComparisons jet primitive
  /-- The common schedule advances both cached original target selections. -/
  target_ge : ∀ coordinate request, (comparisons coordinate).schedule.targetIndex request ≤ schedule.targetIndex request
  /-- The common schedule advances both cached original comparison selections. -/
  comparison_ge : ∀ coordinate request,
    (comparisons coordinate).schedule.comparisonIndex request ≤ schedule.comparisonIndex request
  /-- The original scaled-derivative and action-plus-primitive samples satisfy the retained scheduled geometric error
    bound. -/ connection_samples_close : forall coordinate request,
    Data.Gaussian.Norm.Basic.normSq
        (((RefinementProgram.ofCoherentNamed
          (connectionScaledFirst jet
          coordinate)).model
            (schedule.targetIndex request)).integralSample -
          ((RefinementProgram.ofCoherentNamed
            (connectionWithPrimitive jet primitive coordinate)).model
              (schedule.comparisonIndex request)).integralSample) <=
      Geometric.Basic.quarterRadius budget.total request

constructive_injectivity ConnectionCertificate

namespace ConnectionCertificate

/-- Compute parameter clearance from this certificate's original jet frame. -/
def clearance {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (_certificate : ConnectionCertificate jet) : Clearance.ParameterClearance parameter :=
  ParameterClearance.ofFrame frame

/-- Construct the ordered common subdivision from this certificate's original jet programs. -/
def subdivision {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} {jet : Basic.SynchronizedPeriodJet frame}
    (_certificate : ConnectionCertificate jet) : Subdivision.JetCommonSubdivision jet :=
  Subdivision.JetCommonSubdivision.ofJet jet

/-- Construct both operational connection rows from the admitted original jet alone.

The original source stages derive the row bounds and primitive closure.
Actual name comparisons are retained once per row; a coordinatewise maximum
joins their schedules and reuses their certified tail observations. -/
def ofJet {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (jet : Basic.SynchronizedPeriodJet frame) : ConnectionCertificate jet := by
  let base := (jet.source.stages 0).base.original
  let zeroSource : ConnectionPrimitiveReading jet 0 := ⟨base.zero.channel, rfl⟩
  let oneSource : ConnectionPrimitiveReading jet 1 := ⟨base.one.channel, by
    dsimp only [connectionPrimitiveSource]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]⟩
  let zeroPrimitive := connectionPrimitive jet 0 zeroSource
  let onePrimitive := connectionPrimitive jet 1 oneSource
  let primitive : Fin 2 → ClosedPrimitiveBoundary := fun coordinate =>
    if coordinate = 0 then zeroPrimitive else onePrimitive
  have retained : ∀ coordinate, (primitive coordinate).integralSum =
      add (connectionResidualProgram jet coordinate).output (Coherence.exact 0) := by
    intro coordinate
    rcases Two.finTwo_cases coordinate with zero | one
    · cases zero
      dsimp only [primitive]
      rw [if_pos (rfl : (0 : Fin 2) = 0)]
      exact connectionPrimitive_integralSum jet 0 zeroSource
    · cases one
      dsimp only [primitive]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      exact connectionPrimitive_integralSum jet 1 oneSource
  let zeroComparison := Scheduled.fromEquivalent _ _
    (connectionScaledFirst_equivalent_primitive jet primitive retained 0) 1 (by decide)
  let oneComparison := Scheduled.fromEquivalent _ _
    (connectionScaledFirst_equivalent_primitive jet primitive retained 1) 1 (by decide)
  let comparisons : ConnectionComparisons jet primitive := fun coordinate =>
    if zero : coordinate = 0 then zero.symm ▸ zeroComparison
    else ((Two.finTwo_cases coordinate).resolve_left zero).symm ▸ oneComparison
  let budget := connectionBudget jet comparisons
  let schedule := (comparisons 0).schedule.join (comparisons 1).schedule
  have targetGe : ∀ coordinate request,
      (comparisons coordinate).schedule.targetIndex request ≤ schedule.targetIndex request := by
    intro coordinate request
    rcases Two.finTwo_cases coordinate with zero | one
    · cases zero
      exact Common.CommonSchedule.target_le_join_left _ _ request
    · cases one
      exact Common.CommonSchedule.target_le_join_right _ _ request
  have comparisonGe : ∀ coordinate request,
      (comparisons coordinate).schedule.comparisonIndex request ≤ schedule.comparisonIndex request := by
    intro coordinate request
    rcases Two.finTwo_cases coordinate with zero | one
    · cases zero
      exact Common.CommonSchedule.comparison_le_join_left _ _ request
    · cases one
      exact Common.CommonSchedule.comparison_le_join_right _ _ request
  exact
    { primitive := primitive
      schedule := schedule
      budget := budget
      comparisons := comparisons
      target_ge := targetGe
      comparison_ge := comparisonGe
      connection_samples_close := fun coordinate request =>
        ((comparisons coordinate).samples_close_later request _ _
          (targetGe coordinate request) (comparisonGe coordinate request)).trans
          (Geometric.Basic.quarterRadius_scale_mono
            (Budget.JetErrorBudget.one_le_total budget (by exact le_refl 1)) request) }

/-- Query both retained original comparison owners once for one shared request.

The returned bundle retains both actual selections and both joined indices.
Consumers needing both rows can retain this value and read its two views.
Independent calls remain independent finite queries. -/
def select {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {jet : Basic.SynchronizedPeriodJet frame} (certificate : ConnectionCertificate jet) (request : Nat) :
    Scheduled.ScheduledComparison.JoinedSelection (certificate.comparisons 0) (certificate.comparisons 1) request :=
  Scheduled.ScheduledComparison.JoinedSelection.build _ _ request

/-- The scheduled finite comparison realizes the canonical algebraic connection row together with its exact
differential. -/
def coordinate_with_primitive {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Basic.SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet
      coordinate).name
      (connectionWithPrimitive jet certificate.primitive coordinate).name :=
  Scheduled.namedEquivalent_of_selections _ _ 1 (by decide) (fun request =>
    let retained := certificate.select request
    if zero : coordinate = 0 then zero.symm ▸ retained.firstSelection
    else ((Two.finTwo_cases coordinate).resolve_left zero).symm ▸ retained.secondSelection)

/-- The original closed primitive-boundary contribution is operationally zero and can be removed from the retained
connection action. -/
public def action_primitive_to_action
  {parameter : Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Basic.SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent
      (connectionWithPrimitive jet certificate.primitive coordinate).name
      (connectionAction jet coordinate).name :=
  connectionWithPrimitive_equivalent_action jet certificate.primitive coordinate

/-- One row of the finite fraction-free Gauss--Manin connection, `2 lambda (1-lambda) U' =
[[lambda,-1],[lambda,-lambda]] U`. -/
def coordinate_connection {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Basic.SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet
      coordinate).name
      (connectionAction jet coordinate).name :=
  NamedEquivalent.trans
    (certificate.coordinate_with_primitive coordinate)
    (certificate.action_primitive_to_action coordinate)

/-- Vector form of the finite fraction-free Gauss--Manin connection. -/
def connection {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    {jet : Basic.SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) :
    Operational.Basic.VectorEquivalent
      (fun coordinate => connectionScaledFirst jet coordinate)
      (fun coordinate => connectionAction jet coordinate) :=
  certificate.coordinate_connection

end ConnectionCertificate

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
