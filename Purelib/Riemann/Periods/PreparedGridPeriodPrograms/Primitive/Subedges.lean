module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Primitive.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Primitive.Subedges
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # Original ordered periods compared with actual rooted child source models

The original parent primitive request and canonical period tail are
retained. A separate child-mass selection pays the actual independent
child model allowance. The primitive tolerance is scaled from the fixed
child geometry before either request is acquired. No source, center,
rooted refinement or canonical bank is rebuilt by this comparison.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

open Purelib.Data.Rat.Fraction
open Purelib.Data.Nat
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
open Purelib.Riemann.Integration.PreparedRefinementProgramCore
  (standardDifferentials standardDifferential_mem_standardDifferentials)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}

/-- The positive fixed-geometry factor used before acquiring the original primitive bank. -/
@[expose] def refinementFactor (children : List (CenteredEdge (Fibre.frameCurve frame) source)) : Rational :=
  32 * movementMass children + 3

/-- The literal child count and movement give a strictly positive allocation factor, including the empty list. -/
theorem refinementFactor_positive (children : List (CenteredEdge (Fibre.frameCurve frame) source)) :
    0 < refinementFactor children :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children)) (by decide +kernel)

/-- The actual original primitive selection and additional child-model search, with both whole factories.

The first cache retains the original controlled parent requests, original
source-floor search and canonical tail unchanged. The second search pays
the actual child movement mass rather than reusing the parent payment.
-/
@[expose] def SubedgeSelection (walk : PeriodWalk grid base owner source)
    (children : List (CenteredEdge (Fibre.frameCurve frame) source)) (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) : Type _ :=
  (original : { value : PrimitiveSelection walk sourceStart periodStart
      (tolerance / refinementFactor children)
      (Order.Field.div_pos_direct positive (refinementFactor_positive children)) //
    value = walk.primitiveSelection sourceStart periodStart (tolerance / refinementFactor children)
      (Order.Field.div_pos_direct positive (refinementFactor_positive children)) }) ×
  { child : Geometric.Search.Selection (32 * movementMass children) sourceStart (tolerance / 4) //
    child = Geometric.Search.Selection.build (32 * movementMass children)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children))
      sourceStart (tolerance / 4) (Order.Field.div_pos_direct positive (by decide +kernel)) }

/-- Acquire the original scaled parent selection and actual child-mass selection once, before any model reading. -/
def subedgeSelection (walk : PeriodWalk grid base owner source)
    (children : List (CenteredEdge (Fibre.frameCurve frame) source)) (sourceStart periodStart : Nat)
    (tolerance : Rational) (positive : 0 < tolerance) :
    SubedgeSelection walk children sourceStart periodStart tolerance positive :=
  let original := walk.primitiveSelection sourceStart periodStart (tolerance / refinementFactor children)
    (Order.Field.div_pos_direct positive (refinementFactor_positive children))
  let child := Geometric.Search.Selection.build (32 * movementMass children)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children))
    sourceStart (tolerance / 4) (Order.Field.div_pos_direct positive (by decide +kernel))
  ⟨⟨original, rfl⟩, ⟨child, rfl⟩⟩

/-- A parent mass-plus-one coefficient allocation is no larger than its actual half-target. -/
private theorem coefficientTarget_le_half {mass target coefficient : Rational}
    (nonnegative : 0 ≤ mass) (positive : 0 < target)
    (factory : coefficient = (target / 2) / (mass + 1)) : coefficient ≤ target / 2 := by
  have denominator := Arithmetic.add_le_add_direct nonnegative
    (Data.Rat.Fraction.Order.Basic.le_refl (1 : Rational))
  have atLeastOne : (1 : Rational) ≤ mass + 1 := (Data.Rat.Fraction.zero_add 1).symm.trans_le denominator
  have bounded := Order.Field.div_le_div_of_nonneg_left_direct
    (Order.Field.div_pos_direct positive (by decide +kernel : (0 : Rational) < 2)).le
    (by decide +kernel : (0 : Rational) < 1) atLeastOne
  rewrite [factory]
  have one : (target / 2) / 1 = target / 2 :=
    (Data.Rat.Fraction.Field.mul_one_direct ((target / 2) / 1)).symm.trans
      (Data.Rat.Fraction.Field.div_mul_cancel_of_ne (target / 2) 1 (by decide +kernel))
  exact bounded.trans_eq one

/-- The geometry-scaled primitive and canonical-tail charges consume less than the remaining target share. -/
private theorem scaled_payment {mass tolerance : Rational} (nonnegative : 0 ≤ mass)
    (positive : 0 < tolerance) :
    tolerance / 4 + (16 * mass + 2) * ((tolerance / (32 * mass + 3)) / 64) < tolerance := by
  have factorPositive : 0 < 32 * mass + 3 := Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative) (by decide +kernel)
  have targetPositive := Order.Field.div_pos_direct
    (Order.Field.div_pos_direct positive factorPositive) (by decide +kernel : (0 : Rational) < 64)
  have factorLe : 16 * mass + 2 ≤ 32 * mass + 3 := by
    have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (16 : Rational) ≤ 32) nonnegative
    exact Arithmetic.add_le_add_direct scaled (by decide +kernel)
  have bounded := Arithmetic.mul_le_mul_of_nonneg_right_direct factorLe targetPositive.le
  have cancelled : (32 * mass + 3) * ((tolerance / (32 * mass + 3)) / 64) = tolerance / 64 := by
    apply Data.Rat.Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (64 : Rational) ≠ 0)
    calc
      _ = (32 * mass + 3) * (((tolerance / (32 * mass + 3)) / 64) * 64) := by ring1
      _ = (32 * mass + 3) * (tolerance / (32 * mass + 3)) := by
        rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ 64 (by decide +kernel)]
        rfl
      _ = tolerance := by
        rewrite [Data.Rat.Fraction.mul_comm,
          Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ _ factorPositive.ne']
        rfl
      _ = _ := (Data.Rat.Fraction.Field.div_mul_cancel_of_ne tolerance 64 (by decide +kernel)).symm
  have quarter : tolerance / 4 + tolerance / 64 = (17 / 64) * tolerance := by
    apply Data.Rat.Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (64 : Rational) ≠ 0)
    calc
      _ = ((tolerance / 4) * 4) * 16 + (tolerance / 64) * 64 := by ring1
      _ = tolerance * 16 + tolerance := by
        rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide +kernel),
          Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ 64 (by decide +kernel)]
        rfl
      _ = ((17 / 64) * 64) * tolerance := by
        rewrite [Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ 64 (by decide +kernel)]
        ring1
      _ = _ := by ring1
  have strict := Arithmetic.mul_lt_mul_of_pos_right_direct
    (by decide +kernel : (17 / 64 : Rational) < 1) positive
  exact (Arithmetic.add_le_add_direct (Data.Rat.Fraction.Order.Basic.le_refl _) bounded).trans_lt
    ((congrArg (tolerance / 4 + ·) cancelled).trans_lt
      (quarter.trans_lt (strict.trans_eq (by ring1))))

/-- Every later pair of actual child-source and original ordered-period model samples is paid internally.

The source and period indices are independent. Each source model remains
at its actual selected precision, which only needs to be at least its
programme index. The original parent and additional child searches are
both retained before either model sample is read.
-/
theorem subedgeSelection_close (walk : PeriodWalk grid base owner source)
    {children : List (CenteredEdge (Fibre.frameCurve frame) source)} {sourceStart periodStart : Nat}
    {tolerance : Rational} {positive : 0 < tolerance}
    (retained : SubedgeSelection walk children sourceStart periodStart tolerance positive)
    (refinement : RootSubedgeRefinement walk.initial.state.parents children)
    {childCount floor : Nat} (covered : CoveredParents childCount children) {point : LiftedPoint 2}
    (chain : CenteredPathChain children (start := point) (finish := point))
    (precision : Nat → Nat) (precisionFloor : ∀ index, index ≤ precision index)
    (requested : (index : Nat) → { targets : CellEndpoints.Targets chain.path (precision index) //
      targets = CellEndpoints.Targets.build chain.path (precision index) })
    (prepared : (index : Nat) → PreparedParents covered floor (requested index).val)
    (sourceStage periodStage : Nat)
    (sourceLater : Nat.max retained.1.val.2.1.val.stage retained.2.val.stage ≤ sourceStage)
    (periodLater : retained.1.val.2.2.val.stage ≤ periodStage) :
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources covered (prepared sourceStage) chain).cells 0)).integralSample -
        ((walk.program 0).integral.model periodStage).integralSample) < tolerance := by
  let request := retained.1.val.1.val
  let mass := movementMass children
  let target := (tolerance / refinementFactor children) / 64
  have sourceBound := PreparedParents.rooted_primitive_error_le
    (parameter := parameter) (frame := frame) (basis := source)
    (primitiveBasis := PeriodMatrix.standardDifferential (0 : Fin 1))
    request.requests (by rfl) refinement covered (prepared sourceStage) request.coefficient_accurate chain
  have increments : request.primitiveSum = Norm.Sum.Basic.gaussianSum request.requests.increments :=
    request.primitiveSum_eq.trans (congrArg Norm.Sum.Basic.gaussianSum request.increments_eq)
  rewrite [← increments] at sourceBound
  have canonical := retained.1.val.2.2.val.accurate
    (standardDifferential_mem_standardDifferentials (0 : Fin 1)) periodStage periodLater
  rewrite [← Norm.Basic.normSq_eq_canonical] at canonical
  rewrite [← RootClosedState.sample_eq_flat walk.initial (standardDifferentials 1)
    (PeriodMatrix.standardDifferential (0 : Fin 1)) periodStage] at canonical
  rewrite [← walk.state_eq periodStage, ← walk.program_model 0 periodStage] at canonical
  have triangle := Norm.Bounds.normSq_sub_le_via
    (PathModel.mk ((PreparedParents.sources covered (prepared sourceStage) chain).cells 0)).integralSample
    request.primitiveSum ((walk.program 0).integral.model periodStage).integralSample
  have reverse := sourceBound
  rewrite [Norm.Bounds.normSq_sub_symm] at reverse
  have joined := triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct reverse canonical.le) (by decide +kernel))
  have coefficient := coefficientTarget_le_half
    ((movementMass_nonnegative _).trans_eq request.mass_eq.symm)
    (Order.Field.div_pos_direct
      (Order.Field.div_pos_direct positive (refinementFactor_positive children))
      (by decide +kernel : (0 : Rational) < 64)) request.coefficientTarget_eq
  have coefficientPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (movementMass_nonnegative children))
  have modelPayment := (requested sourceStage).val.mul_localBound_le_quarterRadius (32 * mass)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children))
  have indexPayment := Geometric.Basic.quarterRadius_antitone
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (movementMass_nonnegative children)) (precisionFloor sourceStage)
  have selectedPayment := retained.2.val.later_accurate ((Order.le_max_right _ _).trans sourceLater)
  have geometryPayment := modelPayment.trans_lt (indexPayment.trans_lt selectedPayment)
  calc
    _ ≤ 2 * (16 * ((requested sourceStage).val.localBound + request.coefficientTarget) * mass + target) := joined
    _ = 32 * mass * (requested sourceStage).val.localBound +
        (32 * mass * request.coefficientTarget + 2 * target) := by ring1
    _ ≤ 32 * mass * (requested sourceStage).val.localBound +
        (32 * mass * (target / 2) + 2 * target) :=
      Arithmetic.add_le_add_direct (Data.Rat.Fraction.Order.Basic.le_refl _)
        (Arithmetic.add_le_add_direct coefficientPayment (Data.Rat.Fraction.Order.Basic.le_refl _))
    _ < tolerance / 4 + (32 * mass * (target / 2) + 2 * target) :=
      Arithmetic.add_lt_add_right_direct geometryPayment _
    _ = tolerance / 4 + (16 * mass + 2) * target := by
      have halves := Data.Rat.Fraction.Field.div_mul_cancel_of_ne target 2 (by decide +kernel)
      calc
        _ = tolerance / 4 + (16 * mass * ((target / 2) * 2) + 2 * target) := by ring1
        _ = _ := by rewrite [halves]; ring1
    _ < tolerance := scaled_payment (movementMass_nonnegative children) positive

/-- Compare the SAME actual adaptive child model stream with the original ordered dx/y period stream.

The given rooted refinement supplies genuine signed incidence at every
child query. Each comparison constructs the original parent primitive
selection and the additional child-mass payment before returning two
independent all-later model floors. No output-name sampling or replacement
source programme occurs.
-/
def subedgeSourcePeriodEquivalent (walk : PeriodWalk grid base owner source)
    {children : List (CenteredEdge (Fibre.frameCurve frame) source)}
    (refinement : RootSubedgeRefinement walk.initial.state.parents children)
    {childCount floor : Nat} (covered : CoveredParents childCount children) {point : LiftedPoint 2}
    (chain : CenteredPathChain children (start := point) (finish := point))
    (precision : Nat → Nat) (precisionFloor : ∀ index, index ≤ precision index)
    (requested : (index : Nat) → { targets : CellEndpoints.Targets chain.path (precision index) //
      targets = CellEndpoints.Targets.build chain.path (precision index) })
    (prepared : (index : Nat) → PreparedParents covered floor (requested index).val) :
    Equivalence.Equivalent
      (PreparedParents.certifiedAtPrecision
        covered chain precision requested prepared precisionFloor 0).integral.geometric.toApproximation
      (walk.program 0).integral.geometric.toApproximation where
  compare := fun sourceStart periodStart tolerance positive =>
    let retained := walk.subedgeSelection children sourceStart periodStart tolerance positive
    { leftIndex := Nat.max retained.1.val.2.1.val.stage retained.2.val.stage
      rightIndex := retained.1.val.2.2.val.stage
      left_ge := retained.1.val.2.1.val.lower.trans (Order.le_max_left _ _)
      right_ge := retained.1.val.2.2.val.stage_ge
      close := by
        intro sourceStage periodStage sourceLater periodLater
        have bounded := walk.subedgeSelection_close retained refinement covered chain precision precisionFloor
          requested prepared sourceStage periodStage sourceLater periodLater
        change Norm.Basic.normSq
          (((PreparedParents.certifiedAtPrecision
            covered chain precision requested prepared precisionFloor 0).integral.model sourceStage).integralSample -
            ((walk.program 0).integral.model periodStage).integralSample) < tolerance
        rewrite [PreparedParents.certifiedAtPrecision_model]
        exact bounded }

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk

end
