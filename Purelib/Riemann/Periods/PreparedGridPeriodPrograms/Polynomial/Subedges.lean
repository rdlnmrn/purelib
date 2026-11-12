module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Polynomial.Subedges
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Given coordinate-numerator programmes compared across rooted refinement

The target is the original retained PolynomialValue with numerator x and
one sheet factor. Its actual parent-stage models provide their cached
primitives. Two independent executable finite searches pay source and
parent MODEL stages before readings, with the source's own precision floor.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass movementMass_nonnegative)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source}

/-- The two independent paid MODEL-floor searches on the fixed actual child geometry, with whole factories. -/
@[expose] def PolynomialSelection (children : List (CenteredEdge (Fibre.frameCurve frame) source))
    (sourceStart polynomialStart : Nat) (tolerance : Rational) (positive : 0 < tolerance) : Type _ :=
  { selected : Geometric.Search.Selection (16 * movementMass children) sourceStart (tolerance / 2) //
    selected = Geometric.Search.Selection.build (16 * movementMass children)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children)) sourceStart
      (tolerance / 2) (Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) } ×
  { selected : Geometric.Search.Selection (16 * movementMass children) polynomialStart (tolerance / 2) //
    selected = Geometric.Search.Selection.build (16 * movementMass children)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children)) polynomialStart
      (tolerance / 2) (Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) }

/-- Select both independent source/parent stages before any actual model is read. -/
def polynomialSelection (children : List (CenteredEdge (Fibre.frameCurve frame) source))
    (sourceStart polynomialStart : Nat) (tolerance : Rational) (positive : 0 < tolerance) :
    PolynomialSelection children sourceStart polynomialStart tolerance positive :=
  let left := Geometric.Search.Selection.build (16 * movementMass children)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children)) sourceStart
    (tolerance / 2) (Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  let right := Geometric.Search.Selection.build (16 * movementMass children)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (movementMass_nonnegative children)) polynomialStart
    (tolerance / 2) (Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  ⟨⟨left, rfl⟩, ⟨right, rfl⟩⟩

/-- Free parent indices transport the entire supplied work/model cache together to the original recast parent word. -/
private theorem original_polynomial_error_le
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    (same : parents = walk.initial.state.parents.map
      (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1))))
    {polynomialFloor polynomialStage : Nat} (parentCover : CoveredParents 1 parents)
    (work : PolynomialWork parentCover polynomialFloor (Jets.Specification.valueSpecification parameter 1))
    (models : work.Models polynomialStage) {children : List (CenteredEdge (Fibre.frameCurve frame) source)}
    (refinement : RootSubedgeRefinement walk.initial.state.parents children)
    {count floor : Nat} (covered : CoveredParents count children)
    {first last : LiftedPoint 2} {original : LiftedPath 2 first last} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain children (start := start) (finish := finish)) :
    Norm.Basic.normSq ((PathModel.mk (PolynomialWork.Models.cells parentCover work models)).integralSample -
      (PathModel.mk ((PreparedParents.sources covered prepared chain).cells 1)).integralSample) ≤
      16 * (targets.localBound + Geometric.Basic.quarterRadius 1 polynomialStage) * movementMass children := by
  cases same
  exact PreparedParents.rooted_polynomial_error_le
    (parameter := parameter) (frame := frame) (basis := source)
    (parentBasis := PeriodMatrix.standardDifferential (0 : Fin 1))
    parentCover work models refinement covered prepared chain

/-- Every later actual source/parent MODEL pair is paid by the SAME two retained searches.

The parent model's original request chooses its own inverse-polynomial
index; that index is not substituted for its programme stage. The source
keeps its actual selected precision and original Targets factory. Both
whole models remain independently owned at every later pair of indices.
-/
theorem polynomialSelection_close (spine : PolynomialSpine walk) {polynomialFloor : Nat}
    (value : PolynomialValue walk spine polynomialFloor 1)
    {children : List (CenteredEdge (Fibre.frameCurve frame) source)} {sourceStart polynomialStart : Nat}
    {tolerance : Rational} {positive : 0 < tolerance}
    (selected : PolynomialSelection children sourceStart polynomialStart tolerance positive)
    (refinement : RootSubedgeRefinement walk.initial.state.parents children)
    {count floor : Nat} (covered : CoveredParents count children) {point : LiftedPoint 2}
    (chain : CenteredPathChain children (start := point) (finish := point))
    (precision : Nat → Nat) (precisionFloor : ∀ index, index ≤ precision index)
    (requested : (index : Nat) → { targets : CellEndpoints.Targets chain.path (precision index) //
      targets = CellEndpoints.Targets.build chain.path (precision index) })
    (prepared : (index : Nat) → PreparedParents covered floor (requested index).val)
    (sourceStage polynomialStage : Nat) (sourceLater : selected.1.val.stage ≤ sourceStage)
    (polynomialLater : selected.2.val.stage ≤ polynomialStage) :
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources covered (prepared sourceStage) chain).cells 1)).integralSample -
        (value.2.val.integral.model polynomialStage).integralSample) < tolerance := by
  let models := value.1.models polynomialStage
  have bounded := original_polynomial_error_le (parameter := parameter) (frame := frame) (walk := walk)
    spine.parents_eq spine.covered value.1 models refinement covered (prepared sourceStage) chain
  have actualModel := walk.polynomialValue_model value polynomialStage
  have displayed : PolynomialWork.model value.1 value.1.models polynomialStage =
      PathModel.mk (PolynomialWork.Models.cells spine.covered value.1 models) :=
    congrArg PathModel.mk (PolynomialWork.model_cells value.1 value.1.models polynomialStage)
  rewrite [← actualModel.trans displayed, Norm.Bounds.normSq_sub_symm] at bounded
  have nonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Rational) ≤ 16) (movementMass_nonnegative children)
  have modelPaid := (requested sourceStage).val.mul_localBound_le_quarterRadius
    (16 * movementMass children) nonnegative
  have indexPaid := Geometric.Basic.quarterRadius_antitone nonnegative (precisionFloor sourceStage)
  have sourcePaid := modelPaid.trans_lt
    (indexPaid.trans_lt (selected.1.val.later_accurate sourceLater))
  have polynomialPaid := selected.2.val.later_accurate polynomialLater
  have coefficient : 16 * movementMass children * Geometric.Basic.quarterRadius 1 polynomialStage =
      Geometric.Basic.quarterRadius (16 * movementMass children) polynomialStage := by
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  have sourceAndPolynomial := Arithmetic.add_lt_add_direct sourcePaid polynomialPaid
  have halves : tolerance / 2 + tolerance / 2 = tolerance := by
    calc
      _ = (tolerance / 2) * 2 := by ring1
      _ = tolerance := Data.Rat.Fraction.Field.div_mul_cancel_of_ne tolerance 2 (by decide +kernel)
  exact bounded.trans_lt ((show
    16 * ((requested sourceStage).val.localBound + Geometric.Basic.quarterRadius 1 polynomialStage) *
        movementMass children =
      16 * movementMass children * (requested sourceStage).val.localBound +
        Geometric.Basic.quarterRadius (16 * movementMass children) polynomialStage by
          rewrite [← coefficient]
          ring1).trans_lt (sourceAndPolynomial.trans_eq halves))

/-- Compare the SAME actual adaptive child value-one stream with the GIVEN original polynomial x dx/y programme.

The original ordered walk, retained spine/work/model factories and rooted
refinement are fixed before tolerance. The comparison selects independent
MODEL floors and pays every later pair internally. It does not construct
another source, jet, polynomial programme, primitive, recast or cover.
-/
def subedgeSourceEquivalent (spine : PolynomialSpine walk) {polynomialFloor : Nat}
    (value : PolynomialValue walk spine polynomialFloor 1)
    {children : List (CenteredEdge (Fibre.frameCurve frame) source)}
    (refinement : RootSubedgeRefinement walk.initial.state.parents children)
    {count floor : Nat} (covered : CoveredParents count children) {point : LiftedPoint 2}
    (chain : CenteredPathChain children (start := point) (finish := point))
    (precision : Nat → Nat) (precisionFloor : ∀ index, index ≤ precision index)
    (requested : (index : Nat) → { targets : CellEndpoints.Targets chain.path (precision index) //
      targets = CellEndpoints.Targets.build chain.path (precision index) })
    (prepared : (index : Nat) → PreparedParents covered floor (requested index).val) :
    Equivalence.Equivalent
      (PreparedParents.certifiedAtPrecision covered chain precision requested prepared precisionFloor
        1).integral.geometric.toApproximation
      value.2.val.integral.geometric.toApproximation where
  compare := fun sourceStart polynomialStart tolerance positive =>
    let selected := polynomialSelection children sourceStart polynomialStart tolerance positive
    { leftIndex := selected.1.val.stage
      rightIndex := selected.2.val.stage
      left_ge := selected.1.val.lower
      right_ge := selected.2.val.lower
      close := by
        intro sourceStage polynomialStage sourceLater polynomialLater
        have bounded := spine.polynomialSelection_close value selected refinement covered chain precision
          precisionFloor requested prepared sourceStage polynomialStage sourceLater polynomialLater
        change Norm.Basic.normSq
          (((PreparedParents.certifiedAtPrecision covered chain precision requested prepared
            precisionFloor 1).integral.model sourceStage).integralSample -
            (value.2.val.integral.model polynomialStage).integralSample) < tolerance
        rewrite [PreparedParents.certifiedAtPrecision_model]
        exact bounded }

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
