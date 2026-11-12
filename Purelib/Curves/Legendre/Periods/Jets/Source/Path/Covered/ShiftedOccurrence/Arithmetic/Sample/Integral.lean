module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Sample
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor.Integral
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Transport
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Actual child integral Taylor construction on original query Samples

The original prepared source, retained shifted block and globally allocated
Request remain abstract indices. One stored six-table restriction bank and
one retained Sample family supply the actual arithmetic comparisons. Original
occurrence evidence derives sheet and endpoint incidence; paid original model
allowances derive the integral remainder without a closed-stage owner.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath LiftedCell)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
  (startPoint finishPoint liftedCell ShiftedAcquisition)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}

variable (located : Occurrence blocks request sourceIndex)
    (aligned : Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)

namespace Sample

variable (restriction : ShiftedAcquisition.Restrictions
  (child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
  (prepared.entry located.block))

variable (order coordinate : Fin 2)

/-- The original shifted child occurrence retains the same source starting sheet. -/
private theorem sameSheet :
    (startPoint ((firstParent :: remaining)[located.block.val]'located.block.isLt)).sheet =
      (startPoint ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)).sheet :=
  ((DependentProduct.get (firstParent :: remaining) blocks located.block).shifted.child_sheet
    located.child located.parent_eq).symm

/-- The exact mapped original source time is the same retained child's restriction parameter. -/
private theorem mappedTime (time : { input : Rational // Primitive.unitInterval.Contains input }) :
    located.sourceInput time.val = Restriction.parameter
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.left.parameter
      ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt).edge.request.endpoint.parameter
      time.val :=
  Riemann.Branches.PreparedSheetContinuation.parameterAt_eq_affine _ _ _

section RestrictedQueries

variable {aligned nonzero spatial}

variable {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample located aligned nonzero spatial time)

/-- Reindex the same actual selected source base query through the supplied original cached restriction. -/
private def restrictedBase := UniformObservation.restrictAt
  (liftedCell ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt))
  (restriction.cache (Specification.Table.baseIndex order coordinate)) (sameSheet (located := located))
  (answer.old.1.channel (Specification.Table.baseIndex order coordinate))
  (mappedTime (located := located) time)

/-- Reindex the same actual selected independent source slope query through its supplied original restriction. -/
private def restrictedSlope := UniformObservation.restrictAt
  (liftedCell ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt))
  (restriction.cache (Specification.Table.slopeIndex order coordinate)) (sameSheet (located := located))
  (answer.old.1.channel (Specification.Table.slopeIndex order coordinate))
  (mappedTime (located := located) time)

/-- Restriction preserves the whole already paid selected source base comparison on its original numeric Reading. -/
private def baseComparison :
    ArithmeticComparison (restrictedBase (located := located) (restriction := restriction)
      (order := order) (coordinate := coordinate) answer) (answer.numerics order coordinate).1 answer.sourceIdentity :=
  ArithmeticComparison.restrictAt
    (liftedCell ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt))
    (restriction.cache (Specification.Table.baseIndex order coordinate)) (sameSheet (located := located))
    (answer.commonComparisons order coordinate).1
    (mappedTime (located := located) time)

/-- Restriction preserves the whole independent selected source slope comparison on its same numeric Reading. -/
private def slopeComparison :
    ArithmeticComparison (restrictedSlope (located := located) (restriction := restriction)
      (order := order) (coordinate := coordinate) answer) (answer.numerics order coordinate).2.2
      answer.sourceIdentity :=
  ArithmeticComparison.restrictAt
    (liftedCell ((request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt))
    (restriction.cache (Specification.Table.slopeIndex order coordinate)) (sameSheet (located := located))
    (answer.commonComparisons order coordinate).2.2
    (mappedTime (located := located) time)

end RestrictedQueries

/-- Construct an actual selected-row same-child integral Taylor certificate from the retained original query Samples.

The supplied six-table restriction bank and answer family are consumed directly. Their
original scalar certificates, numeric Readings and operational comparisons
are transported, never rebuilt. The three actual original model allowance
payments and the unit increment bound suffice; original occurrence laws
derive endpoint and sheet incidence internally.
-/
def integralCertificate
    (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance) :
    Quadratic.Basic.Certificate increment := by
  let child := (request.shape.val.1 :: request.shape.val.2)[
        sourceIndex.val]'sourceIndex.isLt
  let old := prepared.entry located.block
  let fresh := request.attempt.2.1.entry sourceIndex
  let block := DependentProduct.get (firstParent :: remaining) blocks located.block
  let common := spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)
  let curves : Data.Vector (HyperellipticCurve 1) 3 :=
    .cons (Fibre.frameCurve frame) (.cons (Fibre.frameCurve target) (.cons (Fibre.frameCurve frame) .nil))
  let forms : (entry : Fin 3) → OddPowerDifferential (curves entry).polynomial :=
    Data.Fin.casesDependent (Specification.Table.forms parameter (Specification.Table.baseIndex order coordinate))
      (Data.Fin.casesDependent (Specification.Table.forms (parameter + increment) (Specification.Table.baseIndex
          order coordinate))
        (Data.Fin.casesDependent (Specification.Table.forms parameter (Specification.Table.slopeIndex order coordinate))
          (fun entry => Fin.elim0 entry)))
  let starts : Data.Vector (LiftedPoint 2) 3 :=
    .cons (startPoint child) (.cons (startPoint child) (.cons (startPoint child) .nil))
  let finishes : Data.Vector (LiftedPoint 2) 3 :=
    .cons (finishPoint child) (.cons (finishPoint child) (.cons (finishPoint child) .nil))
  let lifted : (entry : Fin 3) → LiftedCell (starts entry) (finishes entry) :=
    Data.Fin.casesDependent (liftedCell child)
      (Data.Fin.casesDependent (liftedCell child)
        (Data.Fin.casesDependent (liftedCell child) (fun entry => Fin.elim0 entry)))
  let cells : Data.Vector CellModel 3 :=
    .cons (restriction.model (Specification.Table.baseIndex order coordinate)) (.cons
        (fresh.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (restriction.model (Specification.Table.slopeIndex order coordinate)) .nil))
  let points := fun time : { input : Rational // Primitive.unitInterval.Contains input } =>
    let point := old.preparation.cell.models.coordinate.point (located.sourceInput time.val)
    (Data.Vector.cons point (.cons point (.cons point .nil)) : Data.Vector Canonical 3)
  let sheets := fun time : { input : Rational // Primitive.unitInterval.Contains input } =>
    let answer := answers time
    (Data.Vector.cons answer.sourceRoot.value (.cons answer.targetRoot.value (.cons answer.sourceRoot.value .nil)) :
      Data.Vector CoherentNamed 3)
  let apart : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      (entry : Fin 3) → Named.Apart (sheets time entry).name := fun time =>
    Data.Fin.casesDependent (answers time).sourceRoot.apart
      (Data.Fin.casesDependent (answers time).targetRoot.apart
        (Data.Fin.casesDependent (answers time).sourceRoot.apart (fun entry => Fin.elim0 entry)))
  let states : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      (entry : Fin 3) → (sheets time entry).name.process.State := fun time =>
    Data.Fin.casesDependent (answers time).joint.core.sourceSample.state
      (Data.Fin.casesDependent (answers time).joint.core.targetSample.state
        (Data.Fin.casesDependent (answers time).joint.core.sourceSample.state (fun entry => Fin.elim0 entry)))
  let rootObservations := fun time : { input : Rational // Primitive.unitInterval.Contains input } =>
    (Data.Vector.cons (answers time).joint.core.sourceSample.observation
      (.cons (answers time).joint.core.targetSample.observation
        (.cons (answers time).joint.core.sourceSample.observation .nil)) : Data.Vector RootObservation 3)
  let numerics : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      (entry : Fin 3) → Reading (forms entry) (points time entry) (sheets time entry) (apart time entry)
        (states time entry) (rootObservations time entry) common := fun time =>
    Data.Fin.casesDependent ((answers time).numerics order coordinate).1
      (Data.Fin.casesDependent ((answers time).numerics order coordinate).2.1
        (Data.Fin.casesDependent ((answers time).numerics order coordinate).2.2 (fun entry => Fin.elim0 entry)))
  let identities : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      (entry : Fin 3) → PowerIdentity (sheets time entry) 2
        ((curves entry).polynomial.eval (points time entry)) := fun time =>
    Data.Fin.casesDependent (answers time).sourceIdentity
      (Data.Fin.casesDependent (answers time).targetIdentity
        (Data.Fin.casesDependent (answers time).sourceIdentity (fun entry => Fin.elim0 entry)))
  let uniforms : (entry : Fin 3) → UniformCellCertificate (curves entry) (forms entry)
      (lifted entry) (cells entry) :=
    Data.Fin.casesDependent ⟨fun input lower upper =>
      restrictedBase (located := located) (restriction := restriction)
        (order := order) (coordinate := coordinate) (answers ⟨input, lower, upper⟩)⟩
      (Data.Fin.casesDependent ⟨fun input lower upper => (answers ⟨input, lower, upper⟩).fresh.channel
          (Specification.Table.baseIndex order coordinate)⟩
        (Data.Fin.casesDependent ⟨fun input lower upper =>
          restrictedSlope (located := located) (restriction := restriction)
            (order := order) (coordinate := coordinate) (answers ⟨input, lower, upper⟩)⟩
          (fun entry => Fin.elim0 entry)))
  let comparisons : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      ArithmeticComparison.TaylorComparisons (cells := cells) (lifted := lifted)
        (times := Data.Vector.Basic.vectorOfFn (fun _ : Fin 3 => time.val))
        (uniforms := fun entry => Eq.mpr
          (congrArg (UniformObservation (curves entry) (forms entry) (lifted entry) (cells entry))
            (Data.Vector.Basic.vectorOfFn_apply (fun _ : Fin 3 => time.val) entry))
          ((uniforms entry).query time.val time.property.1 time.property.2))
        (numerics := numerics time) (identities := identities time) := by
    intro time
    refine ArithmeticComparison.TaylorComparisons.atTime
      (curves := curves) (differentials := forms) (starts := starts) (finishes := finishes)
      (lifted := lifted) (cells := cells) (points := points time) (sheets := sheets time)
      (apart := apart time) (states := states time) (rootObservations := rootObservations time)
      (accuracy := common) (numerics := numerics time) (identities := identities time)
      time.val (fun entry => (uniforms entry).query time.val time.property.1 time.property.2) ?_ ?_ ?_
    · dsimp only [uniforms, numerics, identities, Data.Fin.casesDependent]
      exact baseComparison (located := located) (restriction := restriction)
        (order := order) (coordinate := coordinate) (answers time)
    · dsimp only [uniforms, numerics, identities, Data.Fin.casesDependent]
      exact ((answers time).targetComparison order coordinate)
    · dsimp only [uniforms, numerics, identities, Data.Fin.casesDependent]
      exact slopeComparison (located := located) (restriction := restriction)
        (order := order) (coordinate := coordinate) (answers time)
  have allowances : ∀ entry, (cells entry).localAllowance ≤ common.tolerance := by
    intro entry
    refine Data.Fin.casesDependent
      (motive := fun entry : Fin 3 => (cells entry).localAllowance ≤ common.tolerance) ?_
      (Data.Fin.casesDependent ?_ (Data.Fin.casesDependent ?_ (fun entry => Fin.elim0 entry))) entry
    · dsimp only [cells, Data.Vector.get]
      unfold ShiftedAcquisition.Restrictions.model
      exact Eq.mpr
        (congrArg (fun amount : Rational => amount ≤ common.tolerance)
          (Restriction.model_allowance (old.preparation.cell.models.cell (Specification.Table.baseIndex order
              coordinate))
            (first := child.edge.left.parameter) (last := child.edge.request.endpoint.parameter)
            (restriction.cache (Specification.Table.baseIndex order coordinate))))
        valuePaid
    · dsimp only [cells, Data.Vector.get]
      exact outputPaid
    · dsimp only [cells, Data.Vector.get]
      unfold ShiftedAcquisition.Restrictions.model
      exact Eq.mpr
        (congrArg (fun amount : Rational => amount ≤ common.tolerance)
          (Restriction.model_allowance (old.preparation.cell.models.cell (Specification.Table.slopeIndex order
              coordinate))
            (first := child.edge.left.parameter) (last := child.edge.request.endpoint.parameter)
            (restriction.cache (Specification.Table.slopeIndex order coordinate))))
        firstPaid
  have parameterPaid : common.tolerance ≤ Norm.Basic.normSq increment ^ 2 :=
    spatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero)
  have base_start : (cells 0).start = (cells 1).start :=
    (restriction.model_start (source := old) (child := child) block.shifted located.child located.parent_eq
        (Specification.Table.baseIndex order coordinate)).trans
      (fresh.preparation.cell.models.cell_start (Specification.Table.baseIndex order coordinate)).symm
  have base_finish : (cells 0).finish = (cells 1).finish :=
    (restriction.model_finish (source := old) (child := child) block.shifted located.child located.parent_eq
        (Specification.Table.baseIndex order coordinate)).trans
      (fresh.preparation.cell.models.cell_finish (Specification.Table.baseIndex order coordinate)).symm
  have slope_start : (cells 2).start = (cells 1).start :=
    (restriction.model_start (source := old) (child := child) block.shifted located.child located.parent_eq
        (Specification.Table.slopeIndex order coordinate)).trans
      (fresh.preparation.cell.models.cell_start (Specification.Table.baseIndex order coordinate)).symm
  have slope_finish : (cells 2).finish = (cells 1).finish :=
    (restriction.model_finish (source := old) (child := child) block.shifted located.child located.parent_eq
        (Specification.Table.slopeIndex order coordinate)).trans
      (fresh.preparation.cell.models.cell_finish (Specification.Table.baseIndex order coordinate)).symm
  let ceiling := Variation.Point.Step.Joint.rowCeiling old.preparation.cell.patch increment order coordinate
  have ceiling_nonnegative : 0 ≤ ceiling :=
    Variation.Point.Step.Joint.rowCeiling_nonnegative old.preparation.cell.patch increment order coordinate
  let actual := ArithmeticComparison.integralCertificate uniforms numerics identities comparisons
    (fun time => (answers time).certificate order coordinate)
    (fun time => (answers time).certificate_base order coordinate)
    (fun time => (answers time).certificate_output order coordinate)
    (fun time => (answers time).certificate_slope order coordinate) unit allowances parameterPaid
    base_start base_finish slope_start slope_finish ceiling ceiling_nonnegative
    (fun time => (answers time).certificate_factor_le order coordinate)
  exact actual

variable (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)

open Acquisition.Segment

/-- The selected base is the same original cached source base-channel integral sample. -/
private theorem integralCertificate_base_proof :
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).base =
      (restriction.model (Specification.Table.baseIndex order coordinate)).integralSample := by
  unfold integralCertificate
  apply ArithmeticComparison.integralCertificate_base
    (curves := Data.Vector.cons (Fibre.frameCurve frame)
      (.cons (Fibre.frameCurve target) (.cons (Fibre.frameCurve frame) .nil)))
    (cells := Data.Vector.cons (restriction.model (Specification.Table.baseIndex order coordinate))
      (.cons ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate))
        (.cons (restriction.model (Specification.Table.slopeIndex order coordinate)) .nil)))

/-- Every selected child certificate retains its original source base integral.

The original occurrence, restriction and answer family retain their indices;
the unit increment bound and three supplied allowance payments remain quantified. -/
@[expose] def IntegralBaseLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)
    (aligned : RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)
    (restriction : ShiftedAcquisition.Restrictions
  (child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
  (prepared.entry located.block))
    (order coordinate : Fin 2)
    (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance),
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).base =
      (restriction.model (Specification.Table.baseIndex order coordinate)).integralSample

/-- The selected base is the same original cached source base-channel integral sample. -/
theorem integralCertificate_base : IntegralBaseLaw := @integralCertificate_base_proof

/-- The output remains the same independently allocated global target cell's actual integral sample. -/
private theorem integralCertificate_output_proof :
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).output =
      ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
          coordinate)).integralSample := by
  unfold integralCertificate
  apply ArithmeticComparison.integralCertificate_output
    (curves := Data.Vector.cons (Fibre.frameCurve frame)
      (.cons (Fibre.frameCurve target) (.cons (Fibre.frameCurve frame) .nil)))
    (cells := Data.Vector.cons (restriction.model (Specification.Table.baseIndex order coordinate))
      (.cons ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate))
        (.cons (restriction.model (Specification.Table.slopeIndex order coordinate)) .nil)))

/-- Every selected child certificate retains its independently allocated target integral.

The original occurrence, restriction and answer family retain their indices;
the unit increment bound and three supplied allowance payments remain quantified. -/
@[expose] def IntegralOutputLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)
    (aligned : RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)
    (restriction : ShiftedAcquisition.Restrictions
  (child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
  (prepared.entry located.block))
    (order coordinate : Fin 2)
    (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance),
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).output =
      ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
          coordinate)).integralSample

/-- The output remains the same independently allocated global target cell's actual integral sample. -/
theorem integralCertificate_output : IntegralOutputLaw := @integralCertificate_output_proof

/-- The selected slope is the same original independent derivative-channel integral sample. -/
private theorem integralCertificate_slope_proof :
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).slope =
      (restriction.model (Specification.Table.slopeIndex order coordinate)).integralSample := by
  unfold integralCertificate
  apply ArithmeticComparison.integralCertificate_slope
    (curves := Data.Vector.cons (Fibre.frameCurve frame)
      (.cons (Fibre.frameCurve target) (.cons (Fibre.frameCurve frame) .nil)))
    (cells := Data.Vector.cons (restriction.model (Specification.Table.baseIndex order coordinate))
      (.cons ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate))
        (.cons (restriction.model (Specification.Table.slopeIndex order coordinate)) .nil)))

/-- Every selected child certificate retains its independent source slope integral.

The original occurrence, restriction and answer family retain their indices;
the unit increment bound and three supplied allowance payments remain quantified. -/
@[expose] def IntegralSlopeLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)
    (aligned : RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)
    (restriction : ShiftedAcquisition.Restrictions
  (child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
  (prepared.entry located.block))
    (order coordinate : Fin 2)
    (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance),
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).slope =
      (restriction.model (Specification.Table.slopeIndex order coordinate)).integralSample

/-- The selected slope is the same original independent derivative-channel integral sample. -/
theorem integralCertificate_slope : IntegralSlopeLaw := @integralCertificate_slope_proof

/-- The factor retains the actual fixed source-box ceiling and unchanged target physical displacement. -/
private theorem integralCertificate_factor_proof :
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).factor =
      2 * (4 * (Variation.Point.Step.Joint.rowCeiling
        (prepared.entry located.block).preparation.cell.patch increment order coordinate + 7 / 2 + 7 / 2 + 7 / 2)) *
        Norm.Basic.normSq
          ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
              coordinate)).displacement := by
  unfold integralCertificate
  apply ArithmeticComparison.integralCertificate_factor
    (curves := Data.Vector.cons (Fibre.frameCurve frame)
      (.cons (Fibre.frameCurve target) (.cons (Fibre.frameCurve frame) .nil)))
    (cells := Data.Vector.cons (restriction.model (Specification.Table.baseIndex order coordinate))
      (.cons ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate))
        (.cons (restriction.model (Specification.Table.slopeIndex order coordinate)) .nil)))

/-- Every selected child certificate retains its original ceiling and displacement factor.

The original occurrence, restriction and answer family retain their indices;
the unit increment bound and three supplied allowance payments remain quantified. -/
@[expose] def IntegralFactorLaw : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {firstParent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (firstParent :: remaining)}
    {floor : Nat} {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (firstParent :: remaining).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (firstParent :: remaining) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint firstParent) (startPoint firstParent) first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor rootStage : Nat}
    {request : Request whole requestIndex globalFloor rootStage}
    {sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length}
    (located : Occurrence blocks request sourceIndex)
    (aligned : RootComparisons.Alignment
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.paths
      (DependentProduct.get (firstParent :: remaining) blocks located.block).comparison.firstReference)
    (nonzero : increment ≠ 0) (spatial : AccuracyRequest)
    (restriction : ShiftedAcquisition.Restrictions
  (child := (request.shape.val.1 :: request.shape.val.2)[sourceIndex.val]'sourceIndex.isLt)
  (prepared.entry located.block))
    (order coordinate : Fin 2)
    (answers : (time : { input : Rational // Primitive.unitInterval.Contains input }) →
      Sample located aligned nonzero spatial time)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (valuePaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.baseIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (outputPaid : ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance)
    (firstPaid : ((prepared.entry located.block).preparation.cell.models.cell (Specification.Table.slopeIndex order
        coordinate)).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance),
    (integralCertificate (located := located) (aligned := aligned) (nonzero := nonzero)
      (spatial := spatial) (restriction := restriction) (order := order) (coordinate := coordinate)
      answers unit valuePaid outputPaid firstPaid).factor =
      2 * (4 * (Variation.Point.Step.Joint.rowCeiling
        (prepared.entry located.block).preparation.cell.patch increment order coordinate + 7 / 2 + 7 / 2 + 7 / 2)) *
        Norm.Basic.normSq
          ((request.attempt.2.1.entry sourceIndex).preparation.cell.models.cell (Specification.Table.baseIndex order
              coordinate)).displacement

/-- The factor retains the actual fixed source-box ceiling and unchanged target physical displacement. -/
theorem integralCertificate_factor : IntegralFactorLaw := @integralCertificate_factor_proof

end Sample

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
