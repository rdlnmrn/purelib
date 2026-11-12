module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Between.Arithmetic
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Fin

/-! # Actual polynomial Taylor rows between two absolute-time targets

The ten existing comparisons are read as four adjacent derivative rows.
Each row keeps its two actual target observation bundles and the three
literal query times. The original arithmetic polynomial constructor adds
only the three independently paid model discrepancies to that same scalar
Taylor certificate. No root, observation or comparison is reconstructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

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
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath LiftedCell)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (sourcePrepared : PreparedParent patch count floor covered targets) {time : Rational}
    {sample : ContinuedNeighborhood.Point sourcePrepared.preparation.cell.patch
      (sourcePrepared.preparation.cell.models.coordinate.point time)}
    (firstStep : Variation.Point.Step sample firstOffset) (lastStep : Variation.Point.Step sample lastOffset)
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstChild : CenteredEdge (Fibre.frameCurve firstFrame) basis}
    {lastChild : CenteredEdge (Fibre.frameCurve lastFrame) basis}
    {firstPatch : PreparedPatch firstChild} {lastPatch : PreparedPatch lastChild}
    {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (firstChild.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (lastChild.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (firstPrepared : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (lastPrepared : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    {firstInput lastInput : Rational}
    (firstObserved : CellModels.Observations firstFrame (liftedCell firstChild)
      firstPrepared.preparation.cell.models firstPrepared.preparation.query.requests firstInput)
    (lastObserved : CellModels.Observations lastFrame (liftedCell lastChild)
      lastPrepared.preparation.cell.models lastPrepared.preparation.query.requests lastInput)
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {core : Variation.Point.Step.BetweenCore firstStep lastStep unit}
    {arithmetic : Variation.Arithmetic.Observations core} {spatial : AccuracyRequest}
    (paid : Variation.Arithmetic.Reobservations arithmetic spatial)

/-- Three exact original comparisons for one of the four two-target polynomial rows.

The base and slope retain the first target's actual curve, query time and
root. The output retains the second target's own curve, query time, root
and observation. This is the existing three-pair container, with no new
comparison, root-equivalence or context owner.
-/
@[expose] def BetweenRow (order coordinate : Fin 2) :=
  let point := sourcePrepared.preparation.cell.models.coordinate.point time
  let firstRoot := firstStep.root.castParameter (Variation.Point.radicand_eq (parameter + firstOffset) point)
  let lastRoot := lastStep.root.castParameter
    (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial (parameter + firstOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + firstOffset) point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + lastOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset))
        (PowerIdentity.ofSquare lastRoot.square)
  ArithmeticComparison (firstObserved.channel (Specification.Table.baseIndex order coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).1 firstIdentity ×
    ArithmeticComparison (lastObserved.channel (Specification.Table.baseIndex order coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).2.1 lastIdentity ×
    ArithmeticComparison (firstObserved.channel (Specification.Table.slopeIndex order coordinate))
      (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).2.2 firstIdentity

namespace BetweenComparisons

variable {sourcePrepared firstStep lastStep firstPrepared lastPrepared firstObserved lastObserved paid}

/-- Read the same ten retained comparisons as one selected three-entry row without executing another comparison.

The first-order source entries are read from the same bank for a value
slope and a first-row base. Finite selection preserves both independently
paid observations and every original selected comparison tail.
-/
def row (retained : BetweenComparisons
    (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (time := time) (firstInput := firstInput) (lastInput := lastInput) (sample := sample)
    (firstStep := firstStep) (lastStep := lastStep) (firstObserved := firstObserved)
    (lastObserved := lastObserved) (paid := paid)) (order coordinate : Fin 2) :
    BetweenRow sourcePrepared firstStep lastStep firstPrepared lastPrepared firstObserved lastObserved
      paid order coordinate :=
  let entry := fun order coordinate : Fin 2 =>
    BetweenRow sourcePrepared firstStep lastStep firstPrepared lastPrepared firstObserved lastObserved
      paid order coordinate
  Data.Fin.casesDependent (motive := fun order : Fin 2 => entry order coordinate)
    (Data.Fin.casesDependent (motive := fun coordinate : Fin 2 => entry 0 coordinate)
      ⟨retained.1.get 0, retained.2.1.get 0, retained.2.2.1.get 0⟩
      (Data.Fin.casesDependent
        (motive := fun coordinate : Fin 1 => entry 0 coordinate.succ)
        ⟨retained.1.get 1, retained.2.1.get 1, retained.2.2.1.get 1⟩
        (fun coordinate => Fin.elim0 coordinate)) coordinate)
    (Data.Fin.casesDependent (motive := fun order : Fin 1 => entry order.succ coordinate)
      (Data.Fin.casesDependent (motive := fun coordinate : Fin 2 => entry 1 coordinate)
        ⟨retained.2.2.1.get 0, retained.2.2.2.1.get 0, retained.2.2.2.2.get 0⟩
        (Data.Fin.casesDependent
          (motive := fun coordinate : Fin 1 => entry 1 coordinate.succ)
          ⟨retained.2.2.1.get 1, retained.2.2.2.1.get 1, retained.2.2.2.2.get 1⟩
          (fun coordinate => Fin.elim0 coordinate)) coordinate)
      (fun order => Fin.elim0 order)) order

end BetweenComparisons

variable (retained : BetweenComparisons
    (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (time := time) (firstInput := firstInput) (lastInput := lastInput) (sample := sample)
    (firstStep := firstStep) (lastStep := lastStep) (firstObserved := firstObserved)
    (lastObserved := lastObserved) (paid := paid))
    (order coordinate : Fin 2)
    (basePaid : (firstPrepared.preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate)).localAllowance ≤ (spatial.minimum core.accuracy).tolerance)
    (outputPaid : (lastPrepared.preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate)).localAllowance ≤ (spatial.minimum core.accuracy).tolerance)
    (slopePaid : (firstPrepared.preparation.cell.models.cell
      (Specification.Table.slopeIndex order coordinate)).localAllowance ≤ (spatial.minimum core.accuracy).tolerance)

/-- Construct the local difference-offset Taylor certificate on the three actual independently queried polynomials.

The original arithmetic constructor receives literal firstInput, lastInput,
firstInput times. All ten comparison caches and both actual target bundles
stay inputs; only the selected row is packed. The same numerical certificate
and its own exact accuracy equation pay the parameter-fourth remainder.
-/
def betweenPolynomialCertificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) := by
  let point := sourcePrepared.preparation.cell.models.coordinate.point time
  let firstRoot := firstStep.root.castParameter (Variation.Point.radicand_eq (parameter + firstOffset) point)
  let lastRoot := lastStep.root.castParameter
    (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset)
  let firstIdentity : PowerIdentity firstRoot.value 2 ((Paths.polynomial (parameter + firstOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity firstRoot.value 2 value)
      (Variation.Point.radicand_eq (parameter + firstOffset) point)) (PowerIdentity.ofSquare firstRoot.square)
  let lastIdentity : PowerIdentity lastRoot.value 2 ((Paths.polynomial (parameter + lastOffset)).eval point) :=
    Eq.mpr (congrArg (fun value => PowerIdentity lastRoot.value 2 value)
      (Variation.Point.Step.betweenRadicand_eq parameter point firstOffset lastOffset))
        (PowerIdentity.ofSquare lastRoot.square)
  let curves : Data.Vector (HyperellipticCurve 1) 3 :=
    .cons (Fibre.frameCurve firstFrame) (.cons (Fibre.frameCurve lastFrame) (.cons (Fibre.frameCurve firstFrame) .nil))
  let forms : (entry : Fin 3) → OddPowerDifferential (curves entry).polynomial :=
    Data.Fin.casesDependent
      (Specification.Table.forms (parameter + firstOffset) (Specification.Table.baseIndex order coordinate))
      (Data.Fin.casesDependent
        (Specification.Table.forms (parameter + lastOffset) (Specification.Table.baseIndex order coordinate))
        (Data.Fin.casesDependent
          (Specification.Table.forms (parameter + firstOffset) (Specification.Table.slopeIndex order coordinate))
          (fun entry => Fin.elim0 entry)))
  let starts : Data.Vector (LiftedPoint 2) 3 :=
    .cons (startPoint firstChild) (.cons (startPoint lastChild) (.cons (startPoint firstChild) .nil))
  let finishes : Data.Vector (LiftedPoint 2) 3 :=
    .cons (finishPoint firstChild) (.cons (finishPoint lastChild) (.cons (finishPoint firstChild) .nil))
  let lifted : (entry : Fin 3) → LiftedCell (starts entry) (finishes entry) :=
    Data.Fin.casesDependent (liftedCell firstChild)
      (Data.Fin.casesDependent (liftedCell lastChild)
        (Data.Fin.casesDependent (liftedCell firstChild) (fun entry => Fin.elim0 entry)))
  let cells : Data.Vector CellModel 3 :=
    .cons (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (.cons (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate)) .nil))
  let times : Data.Vector Rational 3 := .cons firstInput (.cons lastInput (.cons firstInput .nil))
  let uniforms : (entry : Fin 3) → UniformObservation (curves entry) (forms entry)
      (lifted entry) (cells entry) (times entry) :=
    Data.Fin.casesDependent (firstObserved.channel (Specification.Table.baseIndex order coordinate))
      (Data.Fin.casesDependent (lastObserved.channel (Specification.Table.baseIndex order coordinate))
        (Data.Fin.casesDependent (firstObserved.channel (Specification.Table.slopeIndex order coordinate))
          (fun entry => Fin.elim0 entry)))
  let points : Data.Vector Canonical 3 := .cons point (.cons point (.cons point .nil))
  let sheets : Data.Vector CoherentNamed 3 :=
    .cons firstRoot.value (.cons lastRoot.value (.cons firstRoot.value .nil))
  let apart : (entry : Fin 3) → Named.Apart (sheets entry).name :=
    Data.Fin.casesDependent firstRoot.apart
      (Data.Fin.casesDependent lastRoot.apart
        (Data.Fin.casesDependent firstRoot.apart (fun entry => Fin.elim0 entry)))
  let states : (entry : Fin 3) → (sheets entry).name.process.State :=
    Data.Fin.casesDependent core.sourceSample.state
      (Data.Fin.casesDependent core.targetSample.state
        (Data.Fin.casesDependent core.sourceSample.state (fun entry => Fin.elim0 entry)))
  let rootObservations : Data.Vector RootObservation 3 :=
    .cons core.sourceSample.observation (.cons core.targetSample.observation (.cons core.sourceSample.observation .nil))
  let numerics : (entry : Fin 3) → Reading (forms entry) (points entry) (sheets entry) (apart entry)
      (states entry) (rootObservations entry) (spatial.minimum core.accuracy) :=
    Data.Fin.casesDependent (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).1
      (Data.Fin.casesDependent (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).2.1
        (Data.Fin.casesDependent (Variation.Point.Step.betweenNumerics firstStep lastStep paid order coordinate).2.2
          (fun entry => Fin.elim0 entry)))
  let identities : (entry : Fin 3) → PowerIdentity (sheets entry) 2
      ((curves entry).polynomial.eval (points entry)) :=
    Data.Fin.casesDependent firstIdentity
      (Data.Fin.casesDependent lastIdentity
        (Data.Fin.casesDependent firstIdentity (fun entry => Fin.elim0 entry)))
  let selected := retained.row order coordinate
  let comparisons : ArithmeticComparison.TaylorComparisons
      (curves := curves) (differentials := forms) (starts := starts) (finishes := finishes)
      (lifted := lifted) (cells := cells) (times := times) (uniforms := uniforms)
      (points := points) (sheets := sheets) (apart := apart) (states := states)
      (rootObservations := rootObservations) (accuracy := spatial.minimum core.accuracy)
      (numerics := numerics) (identities := identities) :=
    Data.Vector.DependentVector.ofFn
      (Data.Fin.casesDependent selected.1
        (Data.Fin.casesDependent selected.2.1
          (Data.Fin.casesDependent selected.2.2 (fun entry => Fin.elim0 entry))))
  have allowances : ∀ entry, (cells entry).localAllowance ≤ (spatial.minimum core.accuracy).tolerance := by
    intro entry
    exact Data.Fin.casesDependent
      (motive := fun entry : Fin 3 => (cells entry).localAllowance ≤ (spatial.minimum core.accuracy).tolerance)
      basePaid (Data.Fin.casesDependent outputPaid
        (Data.Fin.casesDependent slopePaid (fun entry => Fin.elim0 entry))) entry
  exact ArithmeticComparison.polynomialCertificate comparisons (paid.rowCertificate order coordinate)
    (Variation.Point.Step.betweenNumerics_base firstStep lastStep paid order coordinate)
    (Variation.Point.Step.betweenNumerics_output firstStep lastStep paid order coordinate)
    (Variation.Point.Step.betweenNumerics_slope firstStep lastStep paid order coordinate)
    unit allowances ((spatial.minimum_le_right core.accuracy).trans_eq core.accuracy_eq)

/-- The base is the SAME first target polynomial at its exact original firstInput query time. -/
theorem betweenPolynomialCertificate_base :
    (betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
      firstObserved lastObserved paid retained order coordinate basePaid outputPaid slopePaid).base =
      Evaluation.eval (firstPrepared.preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).polynomial (Cast.Path.ofCoordinate firstInput) := by
  unfold betweenPolynomialCertificate
  apply ArithmeticComparison.polynomialCertificate_base
    (curves := Data.Vector.cons (Fibre.frameCurve firstFrame)
      (.cons (Fibre.frameCurve lastFrame) (.cons (Fibre.frameCurve firstFrame) .nil)))
    (cells := Data.Vector.cons
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (.cons (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate)) .nil)))
    (times := Data.Vector.cons firstInput (.cons lastInput (.cons firstInput .nil)))

/-- The output is the SAME independently retained second target polynomial at its own lastInput query time. -/
theorem betweenPolynomialCertificate_output :
    (betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
      firstObserved lastObserved paid retained order coordinate basePaid outputPaid slopePaid).output =
      Evaluation.eval (lastPrepared.preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).polynomial (Cast.Path.ofCoordinate lastInput) := by
  unfold betweenPolynomialCertificate
  apply ArithmeticComparison.polynomialCertificate_output
    (curves := Data.Vector.cons (Fibre.frameCurve firstFrame)
      (.cons (Fibre.frameCurve lastFrame) (.cons (Fibre.frameCurve firstFrame) .nil)))
    (cells := Data.Vector.cons
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (.cons (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate)) .nil)))
    (times := Data.Vector.cons firstInput (.cons lastInput (.cons firstInput .nil)))

/-- The slope is the first target's SAME independent derivative polynomial at its original firstInput time. -/
theorem betweenPolynomialCertificate_slope :
    (betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
      firstObserved lastObserved paid retained order coordinate basePaid outputPaid slopePaid).slope =
      Evaluation.eval (firstPrepared.preparation.cell.models.cell
        (Specification.Table.slopeIndex order coordinate)).polynomial (Cast.Path.ofCoordinate firstInput) := by
  unfold betweenPolynomialCertificate
  apply ArithmeticComparison.polynomialCertificate_slope
    (curves := Data.Vector.cons (Fibre.frameCurve firstFrame)
      (.cons (Fibre.frameCurve lastFrame) (.cons (Fibre.frameCurve firstFrame) .nil)))
    (cells := Data.Vector.cons
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (.cons (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate)) .nil)))
    (times := Data.Vector.cons firstInput (.cons lastInput (.cons firstInput .nil)))

/-- The original polynomial certificate factor retains the SAME actual numerical certificate and three payments. -/
theorem betweenPolynomialCertificate_factor :
    (betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
      firstObserved lastObserved paid retained order coordinate basePaid outputPaid slopePaid).factor =
      4 * ((paid.rowCertificate order coordinate).factor + 7 / 2 + 7 / 2 + 7 / 2) := by
  unfold betweenPolynomialCertificate
  apply ArithmeticComparison.polynomialCertificate_factor
    (curves := Data.Vector.cons (Fibre.frameCurve firstFrame)
      (.cons (Fibre.frameCurve lastFrame) (.cons (Fibre.frameCurve firstFrame) .nil)))
    (cells := Data.Vector.cons
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (.cons (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (.cons (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate)) .nil)))
    (times := Data.Vector.cons firstInput (.cons lastInput (.cons firstInput .nil)))

omit order coordinate basePaid outputPaid slopePaid in
/-- Materialize all four original polynomial Taylor rows once from the SAME two bundles and ten comparisons.

The two actual globally allocated preparations pay their own model
allowances. The first-order comparison entries remain shared by value
slopes and first-row bases. This operation does not query, reobserve,
continue a root, rebuild a model or construct another comparison.
-/
def betweenPolynomialRows
    (firstAllowances : ∀ channel : Fin 6,
      (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
        (spatial.minimum core.accuracy).tolerance)
    (lastAllowances : ∀ channel : Fin 6,
      (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
        (spatial.minimum core.accuracy).tolerance) :
    Data.Vector (Data.Vector (Quadratic.Basic.Certificate (lastOffset - firstOffset)) 2) 2 :=
  Data.Vector.Basic.vectorOfFn (fun degree : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun component : Fin 2 =>
      betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
        firstObserved lastObserved paid retained degree component
        (firstAllowances (Specification.Table.baseIndex degree component))
        (lastAllowances (Specification.Table.baseIndex degree component))
        (firstAllowances (Specification.Table.slopeIndex degree component))))

omit basePaid outputPaid slopePaid in
/-- The retained four-row table reads exactly the selected original polynomial certificate. -/
theorem betweenPolynomialRows_apply
    (firstAllowances : ∀ channel : Fin 6,
      (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
        (spatial.minimum core.accuracy).tolerance)
    (lastAllowances : ∀ channel : Fin 6,
      (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
        (spatial.minimum core.accuracy).tolerance) :
    betweenPolynomialRows sourcePrepared firstStep lastStep firstPrepared lastPrepared
        firstObserved lastObserved paid retained firstAllowances lastAllowances order coordinate =
      betweenPolynomialCertificate sourcePrepared firstStep lastStep firstPrepared lastPrepared
        firstObserved lastObserved paid retained order coordinate
        (firstAllowances (Specification.Table.baseIndex order coordinate))
        (lastAllowances (Specification.Table.baseIndex order coordinate))
        (firstAllowances (Specification.Table.slopeIndex order coordinate)) := by
  unfold betweenPolynomialRows
  rewrite [Data.Vector.Basic.vectorOfFn_apply]
  rewrite [Data.Vector.Basic.vectorOfFn_apply]
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
