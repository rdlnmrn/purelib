module

public import Purelib.Integration.Path.Primitive
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive edges from retained finite polynomial models

Original lifted paths supply endpoint telescoping. Each retained cell
comparison supplies an actual derivative residual bound, from which finite
summation derives the original integration program's endpoint comparison.
-/

public section

namespace Purelib.Integration.Path.Primitive.PrimitiveEdge

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Periods
open Purelib.Integration.Program
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Original lifted endpoint continuity telescopes any retained scalar primitive evaluation. -/
private theorem primitive_increments_telescope (primitive : Basic.Canonical → Basic.Canonical)
    {sheets : Nat} {cells : List Cell.Basic.CellModel}
    {start finish : LiftedPoint sheets} {path : LiftedPath sheets start finish}
    (follows : LiftedPath.FollowedBy cells path) :
    Integration.Polynomial.Gaussian.Path.Primitive.incrementSum primitive cells =
      primitive finish.coordinate - primitive start.coordinate := by
  induction follows with
  | nil point =>
      change (0 : Basic.Canonical) = primitive point.coordinate - primitive point.coordinate
      exact (Basic.sub_self _).symm
  | cons start_eq finish_eq tail inductionHypothesis =>
      change primitive _ - primitive _ + Integration.Polynomial.Gaussian.Path.Primitive.incrementSum primitive _ = _
      rw [start_eq, finish_eq, inductionHypothesis]
      ring1

/-- Derive the original primitive edge from actual finite program-versus-endpoint sample comparisons.

Both original endpoint streams and the original integration program remain
retained. The resulting edge transports the finite sample comparison
through the same original stateful endpoint arithmetic. -/
def ofSampleComparison (startSource finishSource : GeometricApproximation)
    (program : Comparison.RefinementProgram)
    (scale : Fraction.Rational) (scale_nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq
      ((program.model index).integralSample - (finishSource.sample index - startSource.sample index)) ≤
        quarterRadius scale index) :
    PrimitiveEdge (PeriodMatrix.geometricNamed startSource) (PeriodMatrix.geometricNamed finishSource) := by
  let difference := GeometricApproximation.add (GeometricApproximation.neg startSource) finishSource
  let carrier := Comparison.geometricRefinementProgram difference
  have sampleComparison : Equivalence.NamedEquivalent program.output.name carrier.output.name :=
    Comparison.refinementProgram_output_equivalent_of_samples_close
      program carrier scale scale_nonnegative (by
        intro index
        rw [Comparison.geometricRefinementProgram_integralSample]
        change Norm.Basic.normSq ((program.model index).integralSample -
          (-startSource.sample index + finishSource.sample index)) ≤ quarterRadius scale index
        rw [show -startSource.sample index + finishSource.sample index =
          finishSource.sample index - startSource.sample index by ring1]
        exact samples index)
  have differenceComparison : Equivalence.NamedEquivalent
      (primitiveDifference (PeriodMatrix.geometricNamed startSource) (PeriodMatrix.geometricNamed finishSource)).name
      (PeriodMatrix.geometricNamed difference).name :=
    Geometric.Coherent.Comparison.coherentAdd_equivalent_geometricAdd
      (Name.Coherent.CoherentNamed.neg (PeriodMatrix.geometricNamed startSource))
      (PeriodMatrix.geometricNamed finishSource)
      (GeometricApproximation.neg startSource) finishSource
      (Geometric.Coherent.Comparison.coherentNeg_equivalent_geometricNeg _ _ (Equivalence.NamedEquivalent.refl _))
      (Equivalence.NamedEquivalent.refl _)
  exact ⟨program, Equivalence.NamedEquivalent.trans sampleComparison
    (Equivalence.NamedEquivalent.trans
      (Comparison.geometricNamed_equivalent_geometricRefinementProgram difference).symm
      differenceComparison.symm)⟩

/-- The sample-comparison edge retains the exact original integration program. -/
theorem ofSampleComparison_program (startSource finishSource : GeometricApproximation)
    (program : Comparison.RefinementProgram)
    (scale : Fraction.Rational) (scale_nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq
      ((program.model index).integralSample - (finishSource.sample index - startSource.sample index)) ≤
        quarterRadius scale index) :
    (ofSampleComparison startSource finishSource program scale scale_nonnegative samples).program = program := by
  unfold ofSampleComparison
  rfl

set_option genInjectivity false in
/-- Polynomial primitive models attached to one original integration program and its original lifted endpoints.

The retained endpoint streams are quantitatively compared with the same
stage primitives at the original endpoints. Local
comparison caches refer to each actual program cell, and their derivative
ceilings fit a finite count-paid geometric budget. No integral-equivalence
or global sample-closeness conclusion is an input. -/
structure PolynomialModels {sheets : Nat} (start finish : LiftedPoint sheets)
    (startSource finishSource : GeometricApproximation)
    (program : Comparison.RefinementProgram) where
  /-- The retained spatial primitive polynomial at each original program stage. -/
  value : Nat → CoefficientPolynomial
  /-- The actual lifted geometric path followed by each retained program model. -/
  lifted : Nat → LiftedPath sheets start finish
  /-- The original cell list follows that exact lifted path with its original endpoint labels. -/
  follows : ∀ index, LiftedPath.FollowedBy (program.model index).cells (lifted index)
  /-- The retained local primitive and derivative residual cache for every original cell occurrence. -/
  cellComparison : ∀ index (cell : Cell.Basic.CellModel),
    cell ∈ (program.model index).cells → Cell.Primitive.Comparison cell
  /-- The local primitive starts at the original stage primitive's value on the original cell start. -/
  localStart : ∀ index cell member, (cellComparison index cell member).value.eval 0 = (value index).eval cell.start
  /-- The local primitive finishes at the original stage primitive's value on the original cell finish. -/
  localFinish : ∀ index cell member, (cellComparison index cell member).value.eval 1 = (value index).eval cell.finish
  /-- The retained common ceiling for the original endpoint readings at each stage. -/
  endpointBound : Nat → Fraction.Rational
  /-- The original starting stream is compared with the retained primitive at its original lifted start. -/
  startError : ∀ index,
    Norm.Basic.normSq ((value index).eval start.coordinate - startSource.sample index) ≤ endpointBound index
  /-- The original finishing stream is compared with the retained primitive at its original lifted finish. -/
  finishError : ∀ index,
    Norm.Basic.normSq ((value index).eval finish.coordinate - finishSource.sample index) ≤ endpointBound index
  /-- The retained common derivative residual ceiling at each original stage. -/
  localBound : Nat → Fraction.Rational
  /-- Every actual local comparison cache obeys that same retained ceiling. -/
  localBound_le : ∀ index cell member, (cellComparison index cell member).bound ≤ localBound index
  /-- The retained geometric scale paying for the original path's cell count and local residual ceilings. -/
  scale : Fraction.Rational
  /-- The retained geometric comparison scale is nonnegative. -/
  scale_nonnegative : 0 ≤ scale
  /-- The original stage's exact cell count pays both finite sum factors and the local primitive estimate. -/
  budget_le : ∀ index,
    2 * (((program.model index).cells.length : Fraction.Rational) *
        (((program.model index).cells.length : Fraction.Rational) * (2 * localBound index))) +
      8 * endpointBound index ≤ quarterRadius scale index

constructive_injectivity PolynomialModels

namespace PolynomialModels

/-- The original integration sample is geometrically close to the two retained primitive endpoint readings.

The bound is derived from the actual local derivative residual caches and
the original lifted-path endpoint continuity. -/
theorem sample_error_le {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Comparison.RefinementProgram}
    (models : PolynomialModels start finish startSource finishSource program) (index : Nat) :
    Norm.Basic.normSq
        ((program.model index).integralSample - (finishSource.sample index - startSource.sample index)) ≤
      quarterRadius models.scale index := by
  have bounded (cell : Cell.Basic.CellModel) (member : cell ∈ (program.model index).cells) :
      Basic.Canonical.normSq
          ((models.value index).eval cell.finish - (models.value index).eval cell.start - cell.integralSample) ≤
        2 * models.localBound index := by
    have localEstimate := (models.cellComparison index cell member).integral_error_le
    rw [models.localStart index cell member, models.localFinish index cell member,
      Norm.Basic.normSq_eq_canonical] at localEstimate
    exact localEstimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (models.localBound_le index cell member) (by decide))
  have estimate := Integration.Polynomial.Gaussian.Path.Primitive.integral_error_le_uniform
    (models.value index).eval (program.model index)
    (primitive_increments_telescope _ (models.follows index)) (2 * models.localBound index) bounded
  rw [← Norm.Basic.normSq_eq_canonical] at estimate
  have endpointError : Norm.Basic.normSq
      (((models.value index).eval finish.coordinate - (models.value index).eval start.coordinate) -
        (finishSource.sample index - startSource.sample index)) ≤ 4 * models.endpointBound index := by
    rw [show ((models.value index).eval finish.coordinate - (models.value index).eval start.coordinate) -
        (finishSource.sample index - startSource.sample index) =
      ((models.value index).eval finish.coordinate - finishSource.sample index) -
        ((models.value index).eval start.coordinate - startSource.sample index) by ring1]
    exact (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (models.finishError index) (models.startError index)) (by decide)).trans
          (le_of_eq (by ring1)))
  rw [show (program.model index).integralSample -
        (finishSource.sample index - startSource.sample index) =
      ((program.model index).integralSample -
        ((models.value index).eval finish.coordinate - (models.value index).eval start.coordinate)) +
        (((models.value index).eval finish.coordinate - (models.value index).eval start.coordinate) -
          (finishSource.sample index - startSource.sample index)) by ring1]
  have reversedEstimate := estimate
  rw [Norm.Bounds.normSq_sub_symm] at reversedEstimate
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add reversedEstimate endpointError) (by decide)).trans
        ((le_of_eq (by ring1)).trans (models.budget_le index)))

/-- Construct the original primitive edge from its retained finite polynomial models.

The program is reused exactly. Its comparison with the two retained
endpoint names is derived internally from finite cell integration estimates
and the endpoint streams' original arithmetic soundness. -/
def edge {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Comparison.RefinementProgram}
    (models : PolynomialModels start finish startSource finishSource program) :
    PrimitiveEdge (PeriodMatrix.geometricNamed startSource) (PeriodMatrix.geometricNamed finishSource) := by
  exact ofSampleComparison startSource finishSource program models.scale models.scale_nonnegative
    models.sample_error_le

/-- The derived primitive edge retains the exact original integration program. -/
theorem edge_program {sheets : Nat} {start finish : LiftedPoint sheets}
    {startSource finishSource : GeometricApproximation}
    {program : Comparison.RefinementProgram}
    (models : PolynomialModels start finish startSource finishSource program) :
    models.edge.program = program := by
  unfold edge
  rfl

end PolynomialModels
end Purelib.Integration.Path.Primitive.PrimitiveEdge

namespace Purelib.Integration.Path.Primitive.ClosedPrimitiveBoundary

open Purelib
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Periods
open Purelib.Integration.Program

/-- Retain an original whole-cycle program as one closed primitive edge.

The endpoint stream is the original primitive at a retained lifted
basepoint. Each actual program stage supplies its own closed-path bound;
only the repeated endpoint difference is cancelled. No equality between
primitive values at different stage basepoints is asserted. -/
@[expose] def ofClosedSampleComparison (source : CoherentNamed) (program : RefinementProgram)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq (program.model index).integralSample ≤ quarterRadius scale index) :
    ClosedPrimitiveBoundary :=
  let carrier := RefinementProgram.ofCoherentNamed source
  let geometric := carrier.geometric
  let edge := PrimitiveEdge.ofSampleComparison geometric geometric program scale nonnegative (by
    intro index
    rw [Basic.sub_self, Basic.sub_zero]
    exact samples index)
  let original := (Comparison.output_equivalent_geometric carrier).symm.trans
    (Comparison.ofCoherentNamed_output_equivalent source).symm
  ofLoop (.cons (edge.changeEndpoints source source original original) (.nil source))

/-- The original primitive channel is retained literally as the boundary's starting owner. -/
theorem ofClosedSampleComparison_start (source : CoherentNamed) (program : RefinementProgram)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq (program.model index).integralSample ≤ quarterRadius scale index) :
    (ofClosedSampleComparison source program scale nonnegative samples).start = source := rfl

/-- The same original channel is retained literally as the closed boundary's finishing owner. -/
theorem ofClosedSampleComparison_finish (source : CoherentNamed) (program : RefinementProgram)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq (program.model index).integralSample ≤ quarterRadius scale index) :
    (ofClosedSampleComparison source program scale nonnegative samples).finish = source := rfl

/-- The actual whole-cycle program closes a nonempty boundary with one literally retained program. -/
theorem ofClosedSampleComparison_nonempty (source : CoherentNamed) (program : RefinementProgram)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq (program.model index).integralSample ≤ quarterRadius scale index) :
    ∃ edge : PrimitiveEdge source source,
      edge.program = program ∧
        (ofClosedSampleComparison source program scale nonnegative samples).path = .cons edge (.nil source) := by
  let carrier := RefinementProgram.ofCoherentNamed source
  let edge := PrimitiveEdge.ofSampleComparison carrier.geometric carrier.geometric
    program scale nonnegative (by
      intro index
      rw [Basic.sub_self, Basic.sub_zero]
      exact samples index)
  let original := (Comparison.output_equivalent_geometric carrier).symm.trans
    (Comparison.ofCoherentNamed_output_equivalent source).symm
  refine ⟨edge.changeEndpoints source source original original, ?_, rfl⟩
  exact PrimitiveEdge.ofSampleComparison_program carrier.geometric carrier.geometric
    program scale nonnegative (by
      intro index
      rw [Basic.sub_self, Basic.sub_zero]
      exact samples index)

/-- The retained closed edge sum is the original program output with its empty-tail zero. -/
theorem ofClosedSampleComparison_integralSum (source : CoherentNamed) (program : RefinementProgram)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (samples : ∀ index, Norm.Basic.normSq (program.model index).integralSample ≤ quarterRadius scale index) :
    (ofClosedSampleComparison source program scale nonnegative samples).integralSum =
      Approximation.Gaussian.Name.Coherent.CoherentNamed.add program.output
        (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0) := by
  unfold ofClosedSampleComparison
  let carrier := RefinementProgram.ofCoherentNamed source
  have retained := PrimitiveEdge.ofSampleComparison_program carrier.geometric carrier.geometric
    program scale nonnegative (by
      intro index
      rw [Basic.sub_self, Basic.sub_zero]
      exact samples index)
  exact congrArg (fun original : RefinementProgram => CoherentNamed.add original.output
    (Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0)) retained

end Purelib.Integration.Path.Primitive.ClosedPrimitiveBoundary
end
