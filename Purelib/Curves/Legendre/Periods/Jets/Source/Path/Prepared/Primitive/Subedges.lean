module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Primitive
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.State.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Specification.Ordinary
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Cast
import Purelib.Tactic.Ring

/-! # An original parent primitive on actual rooted child sources

The primitive remains the polynomial selected on its original parent.
Every child retains its independent source model, patch, Point and query
states. The all-query rooted subedge comparison, rather than a square
residual, fixes the sign in the coefficient comparison. No spatial Taylor
remainder is introduced by this polynomial derivative comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.State (CoefficientState)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.Value (differentialValue)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
  (basedRoot basedApart coefficient coefficient_possible_bound)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator differentialNumerator_eval)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge)
open Purelib.Riemann.Paths.PreparedPrimitivePaths (point_inside_of_endpoints)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements
  (recastPreparedEdge_rootName)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis primitiveBasis : Differential 1}
    {parent child : CenteredEdge (Fibre.frameCurve frame) basis} {count childCount floor : Nat}
    {patch : PreparedPatch child} {covered : (patch.neighborhood childCount).box.Contains (child.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {target coefficientTarget : Rational} {minimum : Nat}

/-- The actual child coordinate lies in the original primitive request's unchanged patch.

The rooted subedge supplies its retained parent fraction. Original endpoint
containment and convexity establish whole-child containment, including
stationary and repeated occurrences, without recasting the child model.
-/
theorem subedge_inside
    (request : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
      target coefficientTarget minimum)
    (relation : RootSubedge parent child) (prepared : PreparedParent patch childCount floor covered targets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    (request.localRequest.patch.neighborhood count).box.Contains
      (prepared.preparation.cell.models.coordinate.point input) := by
  let location := relation.location input inside
  have first := request.localRequest.patch.start_inside count
  have last := request.localRequest.finishInside
  rewrite [request.localRequest.neighborhood_eq] at last
  have admitted := point_inside_of_endpoints (recastCenteredEdge primitiveBasis parent)
    (request.localRequest.patch.neighborhood count).box first last location.inside
  have pointEq : (recastCenteredEdge primitiveBasis parent).edge.point location.fraction =
      prepared.preparation.cell.models.coordinate.point input :=
    location.point_eq.trans (prepared.queryPoint_eq input).symm
  exact Eq.mp (congrArg (fun point =>
    (request.localRequest.patch.neighborhood count).box.Contains point) pointEq) admitted

/-- The same actual child observation and ancestor primitive coefficient obey their two retained allowances.

The source's actual Point is related through the original child query and
all-query parent comparison to a genuine ancestor-patch Point. Each side
keeps its own reading state and primitive index. Only the retained named
root comparisons transfer the reciprocal coefficient between them.
-/
theorem subedge_coefficient_difference_le
    (request : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
      target coefficientTarget minimum)
    (zero : primitiveBasis.exponent = 0) (relation : RootSubedge parent child)
    (prepared : PreparedParent patch childCount floor covered targets)
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (observed : CellModels.Observations frame (liftedCell child) prepared.preparation.cell.models
      prepared.preparation.query.requests input)
    (factory : observed = prepared.preparation.query.observe frame input lower upper) :
    Norm.Basic.normSq
      (Evaluation.eval prepared.preparation.cell.models.valueZero.model.polynomial ⟨input, 0⟩ -
        (controlledPrimitive request).coefficient.eval
          (prepared.preparation.cell.models.coordinate.point input)) ≤
      8 * (prepared.preparation.cell.models.valueZero.model.localAllowance +
        quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
          request.localRequest.request.index) := by
  let model := controlledPrimitive request
  let location := relation.location input ⟨lower, upper⟩
  have inside := subedge_inside request relation prepared input ⟨lower, upper⟩
  let sample := ContinuedNeighborhood.Point.acquire (request.localRequest.patch.neighborhood count)
    (prepared.preparation.cell.models.coordinate.point input) inside
  let direct := PreparedEdge.Query.build child.edge input ⟨lower, upper⟩
  have childRoot := prepared.querySampleEquivalent input ⟨lower, upper⟩ observed.retained.sample direct
  have pointEq : (recastCenteredEdge primitiveBasis parent).edge.point location.fraction =
      prepared.preparation.cell.models.coordinate.point input :=
    location.point_eq.trans (prepared.queryPoint_eq input).symm
  have parentRoot := request.localRequest.patch.point_equivalent_at count location.fraction location.inside
    pointEq inside sample
  have parentName := recastPreparedEdge_rootName primitiveBasis parent.edge location.fraction location.inside
  have parentRootRaw : NamedEquivalent (parent.edge.rootName location.fraction location.inside)
      sample.certificate.value.name := NamedEquivalent.transport parentName rfl parentRoot
  have sourceRoot : observed.valueZero.algebraic.sheetValue.value.name =
      observed.retained.sample.certificate.value.name :=
    prepared.preparation.query.channel_root_name frame input lower upper observed factory 0
  have rootEquivalent : NamedEquivalent observed.valueZero.algebraic.sheetValue.value.name
      (basedRoot (curve := Fibre.frameCurve frame) sample request.localRequest.request.index).name := by
    rewrite [sourceRoot]
    exact childRoot.symm.trans ((relation.equivalent input ⟨lower, upper⟩).symm.trans
      (parentRootRaw.trans (sample.certificate.value.basedEquivalent
        (sample.readingState request.localRequest.request.index))))
  let first := observed.valueZero.algebraic.interpretation.channel
  let last := coefficient (curve := Fibre.frameCurve frame) sample request.localRequest.request.index primitiveBasis
  have normalized := Specification.valueZero_denotation_reciprocal parameter observed.valueZero.algebraic.point
    observed.valueZero.algebraic.sheetValue.value observed.valueZero.algebraic.sheetValue.squareIdentity
    observed.valueZero.algebraic.sheetValue.apart observed.valueZero.algebraic.interpretation
  have quotient := Division.Equivalence.coherentDiv_respects (Coherence.exact 1) (Coherence.exact 1)
    observed.valueZero.algebraic.sheetValue.value
    (basedRoot (curve := Fibre.frameCurve frame) sample request.localRequest.request.index)
    observed.valueZero.algebraic.sheetValue.apart
    (basedApart (curve := Fibre.frameCurve frame) sample request.localRequest.request.index)
    (NamedEquivalent.refl _) rootEquivalent
  have lastEq : last = CoherentNamed.div (Coherence.exact 1)
      (basedRoot (curve := Fibre.frameCurve frame) sample request.localRequest.request.index)
      (basedApart (curve := Fibre.frameCurve frame) sample request.localRequest.request.index) := by
    dsimp only [last, coefficient, differentialValue]
    rewrite [zero]
    rfl
  have equivalent : NamedEquivalent first.name last.name := by
    rewrite [lastEq]
    exact normalized.trans quotient
  have lastBound : ∀ candidate, last.name.process.Possible last.name.state candidate →
      Norm.Basic.normSq (candidate - model.coefficient.eval
        (prepared.preparation.cell.models.coordinate.point input)) ≤
      quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
        request.localRequest.request.index := by
    intro candidate possible
    have bounded := coefficient_possible_bound (curve := Fibre.frameCurve frame) sample inside
      request.localRequest.request.index primitiveBasis _ possible
    rewrite [differentialNumerator_eval, zero, pow_zero, Data.Gaussian.Basic.one_mul] at bounded
    rewrite [Data.Gaussian.Basic.Canonical.normSq_one, Data.Rat.Fraction.one_mul] at bounded
    rewrite [model.coefficient_eq, differentialNumerator_eval, zero, pow_zero, Data.Gaussian.Basic.one_mul,
      Norm.Bounds.normSq_sub_symm, Norm.Basic.normSq_eq_canonical]
    exact bounded
  have positive : 0 < prepared.preparation.cell.models.valueZero.model.localAllowance +
      quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
        request.localRequest.request.index := by
    rewrite [prepared.preparation.cell.models.valueZero.allowance_eq]
    exact Arithmetic.add_pos_of_pos_of_nonneg_direct prepared.preparation.query.positive
      (quarterRadius_nonneg (request.localRequest.patch.neighborhood count).inverseErrorScale_positive.le _)
  exact CoefficientState.reference_difference_le
    ⟨first, observed.valueZero.algebraic.readingState⟩ ⟨last, last.name.state⟩
    (Evaluation.eval prepared.preparation.cell.models.valueZero.model.polynomial ⟨input, 0⟩)
    (model.coefficient.eval (prepared.preparation.cell.models.coordinate.point input))
    prepared.preparation.cell.models.valueZero.model.localAllowance
    (quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
      request.localRequest.request.index)
    (fun _ possible => observed.valueZero.candidate_error_le possible) lastBound equivalent positive

/-- Compile the original ancestor primitive in the actual child source coordinate.

The finite derivative and residual caches are constructed once. Their
uniform bound follows from the same child's actual observation factory
and retained rooted subedge; no final integral estimate is an input.
-/
def subedgePrimitiveComparison
    (request : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
      target coefficientTarget minimum)
    (zero : primitiveBasis.exponent = 0) (relation : RootSubedge parent child)
    (prepared : PreparedParent patch childCount floor covered targets) :
    Primitive.Comparison prepared.preparation.cell.models.valueZero.model :=
  let model := controlledPrimitive request
  Primitive.Comparison.ofSpatialBound prepared.preparation.cell.models.valueZero.model model.primitive.value
    (Norm.Basic.normSq prepared.preparation.cell.models.valueZero.model.displacement *
      (8 * (prepared.preparation.cell.models.valueZero.model.localAllowance +
        quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
          request.localRequest.request.index))) (by
      intro input inside
      let observed := prepared.preparation.query.observe frame input inside.1 inside.2
      have bounded := subedge_coefficient_difference_le request zero relation prepared
        input inside.1 inside.2 observed rfl
      have pointEq : Geometry.Rational.Affine.line prepared.preparation.cell.models.valueZero.model.start
          prepared.preparation.cell.models.valueZero.model.displacement input =
          prepared.preparation.cell.models.coordinate.point input := by
        change prepared.preparation.cell.models.valueZero.model.start + (⟨input, 0⟩ : Canonical) *
          (prepared.preparation.cell.models.valueZero.model.finish -
            prepared.preparation.cell.models.valueZero.model.start) = _
        rewrite [prepared.preparation.cell.models.valueZero.start_eq,
          prepared.preparation.cell.models.valueZero.finish_eq, prepared.preparation.cell.models.coordinate.point_eq]
        rfl
      have reverse := Norm.Bounds.normSq_sub_symm
        (model.coefficient.eval (prepared.preparation.cell.models.coordinate.point input))
        (Evaluation.eval prepared.preparation.cell.models.valueZero.model.polynomial ⟨input, 0⟩)
      rewrite [model.primitive.derivative_eq, pointEq, Norm.Basic.normSq_mul, Cast.Path.ofCoordinate, reverse]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Norm.Basic.normSq_nonneg _))

/-- The actual child integral retains the ancestor's exact polynomial and receives its own displacement charge. -/
theorem subedge_primitive_error_le
    (request : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
      target coefficientTarget minimum)
    (zero : primitiveBasis.exponent = 0) (relation : RootSubedge parent child)
    (prepared : PreparedParent patch childCount floor covered targets) :
    Norm.Basic.normSq (request.localRequest.request.model.primitive.value.eval (child.edge.point 1) -
      request.localRequest.request.model.primitive.value.eval (child.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + quarterRadius request.localRequest.neighborhood.inverseErrorScale
        request.localRequest.request.index) * cost child := by
  have original := (subedgePrimitiveComparison request zero relation prepared).integral_error_le
  change Norm.Basic.normSq
    ((Primitive.spatialPrimitive prepared.preparation.cell.models.valueZero.model
          (controlledPrimitive request).primitive.value).eval 1 -
      (Primitive.spatialPrimitive prepared.preparation.cell.models.valueZero.model
          (controlledPrimitive request).primitive.value).eval 0 -
      prepared.preparation.cell.models.valueZero.model.integralSample) ≤
    2 * (Norm.Basic.normSq prepared.preparation.cell.models.valueZero.model.displacement *
      (8 * (prepared.preparation.cell.models.valueZero.model.localAllowance +
        quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
          request.localRequest.request.index))) at original
  have allowanceEq := prepared.preparation.cell.models.valueZero.allowance_eq.trans prepared.allowance_eq
  rewrite [Primitive.spatialPrimitive_start, Primitive.spatialPrimitive_finish,
    prepared.preparation.cell.models.valueZero.start_eq, prepared.preparation.cell.models.valueZero.finish_eq,
    controlledPrimitive_value request, allowanceEq] at original
  have scaleEq := congrArg (fun neighborhood => neighborhood.inverseErrorScale)
    request.localRequest.neighborhood_eq
  have displacement : prepared.preparation.cell.models.valueZero.model.displacement =
      (finishPoint child).coordinate - (startPoint child).coordinate := by
    change prepared.preparation.cell.models.valueZero.model.finish -
      prepared.preparation.cell.models.valueZero.model.start = _
    rewrite [prepared.preparation.cell.models.valueZero.start_eq,
      prepared.preparation.cell.models.valueZero.finish_eq]
    rfl
  change _ ≤ 2 * (Norm.Basic.normSq prepared.preparation.cell.models.valueZero.model.displacement *
    (8 * (targets.localBound + quarterRadius (request.localRequest.patch.neighborhood count).inverseErrorScale
      request.localRequest.request.index))) at original
  rewrite [← scaleEq, displacement] at original
  rewrite [child.edge.point_one, child.edge.point_zero]
  exact original.trans_eq (by
    unfold cost
    ring1)

/-- The original request's paid numerator bound pays its inverse error for every rooted child source. -/
theorem subedge_primitive_paid_le
    (request : ControlledLocalRequest (recastCenteredEdge primitiveBasis parent) count
      target coefficientTarget minimum)
    (zero : primitiveBasis.exponent = 0) (relation : RootSubedge parent child)
    (prepared : PreparedParent patch childCount floor covered targets) :
    Norm.Basic.normSq (request.localRequest.request.model.primitive.value.eval (child.edge.point 1) -
      request.localRequest.request.model.primitive.value.eval (child.edge.point 0) -
        prepared.preparation.cell.models.valueZero.model.integralSample) ≤
      16 * (targets.localBound + coefficientTarget) * cost child := by
  have inside : request.localRequest.neighborhood.box.Contains
      ((recastCenteredEdge primitiveBasis parent).edge.point 0) := by
    rewrite [request.localRequest.neighborhood_eq]
    exact request.localRequest.patch.start_inside count
  have numerator := request.localRequest.request.numerator_le
    ((recastCenteredEdge primitiveBasis parent).edge.point 0) inside
  rewrite [differentialNumerator_eval, zero, pow_zero] at numerator
  change (1 : Rational) ≤ request.localRequest.request.numeratorBound at numerator
  have enlarged := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide +kernel : (1 : Rational) ≤ 4) request.localRequest.request.numerator_nonnegative
  have oneLe : (1 : Rational) ≤ 4 * request.localRequest.request.numeratorBound :=
    numerator.trans ((show request.localRequest.request.numeratorBound =
      1 * request.localRequest.request.numeratorBound by ring1).trans_le enlarged)
  have inverseLe : quarterRadius request.localRequest.neighborhood.inverseErrorScale
      request.localRequest.request.index ≤
      Riemann.Readings.PreparedPrimitiveChargeBounds.localCoefficient request.localRequest := by
    change _ ≤ 4 * request.localRequest.request.numeratorBound * _
    exact (show quarterRadius request.localRequest.neighborhood.inverseErrorScale
      request.localRequest.request.index = 1 * quarterRadius request.localRequest.neighborhood.inverseErrorScale
        request.localRequest.request.index by ring1).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe
        (quarterRadius_nonneg request.localRequest.neighborhood.inverseErrorScale_positive.le _))
  have paid := inverseLe.trans request.coefficient_accurate.le
  exact (subedge_primitive_error_le request zero relation prepared).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (Data.Rat.Fraction.Order.Basic.le_refl targets.localBound) paid)
        (by decide +kernel))
      (cost_nonnegative child))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
