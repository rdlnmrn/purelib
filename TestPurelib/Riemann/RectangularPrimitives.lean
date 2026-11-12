module

import Purelib.Riemann.Comparison.PrimitiveEdgeComparison

import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Tactic.QuotientFreeOmega

/-! # Retained rectangular primitives for the value and first odd derivative -/

namespace TestPurelib.Riemann.RectangularPrimitives

open Purelib
open Purelib.Riemann
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives PrimitiveCell)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy GluedPrimitives)
open Purelib.Riemann.Integration.RectangularRefinementSigns (SheetCache)
open Purelib.Riemann.Branches
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow quarterRadius_antitone)

variable {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegularFaceInverseModels.Clearance polynomial ambient}
    {columns rows : Nat} {geometry : Geometry columns rows}

/-- Construct both coefficient banks from one actual retained patch and one cached gauge-oriented model bank. -/
def primitivePowers {bounds : RegularFaceInverseModels.Bounds clearance}
    {source : Owner (polynomial.eval ambient.anchor)} (patch : RectangularPatch bounds source geometry)
    (numerator : Polynomial) :
    Σ models : {actual : Bank polynomial geometry //
      actual = RectangularSheetGauge.Transitions.oriented patch.sheets.transitions patch.sheets.gauge},
      Primitives models.val numerator × Primitives models.val numerator 1 :=
  let models := RectangularSheetGauge.Transitions.oriented patch.sheets.transitions patch.sheets.gauge
  let value := Primitives.build models numerator
  let derivative := Primitives.build models numerator 1
  ⟨⟨models, rfl⟩, value, derivative⟩

/-- Reading the actual higher coefficient retains the same common model and its cube. -/
example {bounds : RegularFaceInverseModels.Bounds clearance}
    {source : Owner (polynomial.eval ambient.anchor)} (patch : RectangularPatch bounds source geometry)
    (numerator : Polynomial) (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : Gaussian) :
    ((primitivePowers patch numerator).2.2.cells column row).coefficient.eval point =
      numerator.eval point *
        ((primitivePowers patch numerator).1.val.ready column row).model.value.eval point ^ 3 :=
  (primitivePowers patch numerator).2.2.coefficient_eq column row point

/-- The omitted pair index preserves the complete former coefficient, primitive and remainder caches. -/
example (models : Bank polynomial geometry) (numerator : Polynomial) :
    Primitives.build models numerator =
      (show Primitives models numerator from
        let cells := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
          let coefficient := numerator * (models.ready column row).model.value
          let primitive := Primitive.Certificate.DensePrimitive.ofPolynomial coefficient (geometry.box column row)
          (⟨coefficient, primitive.value, primitive.derivative_eq, primitive.remainderBound,
            primitive.remainderBound_nonnegative⟩ : PrimitiveCell)
        { cells := cells
          coefficient_eq := fun column row point => by
            dsimp only [cells]
            rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
            exact Dense.Basic.DensePolynomial.eval_mul _ _ _
          increment_bound := fun column row _ _ startInside finishInside => by
            dsimp only [cells]
            rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
            simpa only [Norm.Basic.normSq_eq_canonical] using (Primitive.Certificate.DensePrimitive.ofPolynomial _
              _).increment_bound startInside finishInside }) := rfl

/-- The omitted pair index preserves the complete former grid payment and selected stage. -/
example (bounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator)
    (target : Coordinate) (positive : 0 < target) :
    GridPrimitiveAccuracy.build bounds columns target positive =
      (show GridPrimitiveAccuracy bounds columns target from
        let edgeScale := 24 * (1 / 256) * (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq
        let factor := 8 * Budget.Aggregate.countCoordinate columns ^ 2 + 2
        have factorEq : factor = 8 * (columns : Coordinate) ^ 2 + 2 := by
          dsimp only [factor]
          rw [Budget.Aggregate.countCoordinate_eq]
        let scale := factor * edgeScale
        have scaleNonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct
          ((show (0 : Coordinate) ≤ 1 by decide).trans
            ((GridPrimitiveAccuracy.factor_one_le columns).trans_eq factorEq.symm))
            (GridPrimitiveAccuracy.edgeScale_nonneg bounds)
        let index := Geometric.Search.firstQuarterBelow scale 0 target
        let edgeBound := quarterRadius edgeScale index
        let globalBound := factor * edgeBound
        have equal : globalBound = quarterRadius scale index := by
          simp only [globalBound, edgeBound, scale, quarterRadius_eq_mul_pow]
          ring1
        { edgeScale := edgeScale
          edgeScale_eq := rfl
          scale := scale
          scale_eq := by dsimp only [scale]; rw [factorEq]
          index := index
          edgeBound := edgeBound
          edgeBound_eq := rfl
          globalBound := globalBound
          globalBound_eq := by dsimp only [globalBound]; rw [factorEq]
          accurate := equal.trans_lt
            (Geometric.Search.firstQuarterBelow_accurate scale scaleNonnegative 0 target positive) }) := rfl

/-- The omitted pair index preserves the complete original glued bank and every retained cache. -/
example {bank : Bank polynomial geometry} (sheets : SheetCache bank) (numerator : Polynomial) :
    GluedPrimitives.ofSheets sheets numerator =
      (show GluedPrimitives bank numerator from
        let transitions := sheets.transitions
        let gauge := sheets.gauge
        let oriented := RectangularSheetGauge.Transitions.oriented transitions gauge
        let primitives := Primitives.build oriented numerator
        let anchors := PrimitiveAnchors.build primitives
        ⟨transitions, gauge, primitives, anchors, anchors.offsets⟩) := rfl

/-- The first odd derivative uses the actual paid request stage and its retained coefficient bank. -/
example {geometricBounds : RegularFaceInverseModels.Bounds clearance}
    {source : Owner (polynomial.eval ambient.anchor)} (patch : RectangularPatch geometricBounds source geometry)
    (numerator : Polynomial) (target : Coordinate) (positive : 0 < target) :
    let bounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build clearance numerator
    let request := GridPrimitiveAccuracy.build bounds columns target positive 1
    let actual := request.prepare patch.sheets
    request.globalBound < target ∧
      ∀ column row point, (actual.primitives.cells column row).coefficient.eval point =
        numerator.eval point *
          (((RectangularSheetGauge.Transitions.oriented actual.transitions actual.gauge).ready
            column row).model.value.eval point) ^ 3 := by
  let bounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build clearance numerator
  let request := GridPrimitiveAccuracy.build bounds columns target positive 1
  let actual := request.prepare patch.sheets
  constructor
  · exact request.accurate
  · intro column row point
    exact actual.primitives.coefficient_eq column row point

section SourceCalibration

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Polynomial.Winding
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets.PreparedPolynomialSheetPropagation (prepared_within)

variable {genus : Nat} {curve : HyperellipticCurve genus} {outer inner actualAmbient : Box}
    {clearance : RegularFaceInverseModels.Clearance curve.polynomial outer}
    {bounds : RegularFaceInverseModels.Bounds clearance} {source : Owner (curve.polynomial.eval outer.anchor)}
    {point : Gaussian} {actualPath : ClearPath curve.polynomial actualAmbient outer.anchor point}

/-- The empty retained prefix preserves the complete former operational comparison of the same old inputs. -/
example (cell : TransportedCell bounds source inner) (degreePositive : 0 < curve.polynomial.natDegree)
    (reference : WindingOneLoop curve.polynomial outer.anchor)
    {localPath : ClearPath curve.polynomial inner inner.anchor point}
    (prepared : CoveredTracedPath localPath cell.traced.finishOwner) (traced : TracedPath actualPath source)
    (inside : InBox outer actualPath) (frame : OwnerFrame (curve.polynomial.eval point)) :
    cell.compareContinuedTrace
      (entered := TracedPath.build (ClearPath.nil (polynomial := curve.polynomial) (ambient := outer) outer.anchor)
        (.nil outer.anchor) source) outer.contains_anchor degreePositive reference prepared traced inside frame =
      (show NamedEquivalent (OwnerTraceReadings.ownerName prepared.traced.finishOwner)
          (OwnerTraceReadings.ownerName traced.finishOwner) from by
        let joined := cell.traced.trace.get.append prepared.traced.trace.get
        have localInside : localPath.InBox outer :=
          (InBox.ofWithin localPath (prepared_within prepared.traced.prepared)
            inner.contains_anchor).mono cell.geometry.refines
        have winding : PreparedPathWinding.ClearPath.rawWinding actualPath =
            Polygon.Basic.chainRaw curve.polynomial outer.anchor joined.vertices := by
          rw [RootPathTransport.OwnerPath.append_winding,
            PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original cell.traced,
            PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original prepared.traced,
            ClearBoxPathWinding.Route.winding clearance degreePositive cell.route outer.contains_anchor,
            ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance degreePositive localPath localInside,
            ClearBoxPathWinding.ClearPath.rawWinding_eq_potential clearance degreePositive actualPath inside]
          omega
        exact (ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections reference
          (prepared_within traced.prepared) traced joined frame (frame.select traced.finishOwner)
          (frame.select prepared.traced.finishOwner) winding).symm) := rfl

/-- The empty retained prefix preserves every original transition field and both cached polynomial readings. -/
example (cell : TransportedCell bounds source inner) (differential : Differential genus)
    (degreePositive : 0 < curve.polynomial.natDegree) (reference : WindingOneLoop curve.polynomial outer.anchor)
    (traced : TracedPath actualPath source) (inside : InBox outer actualPath)
    (frame : OwnerFrame (curve.polynomial.eval point)) (pointInside : inner.Contains point)
    {count : Nat} (neighborhood : TracedPrimitiveNeighborhood.Neighborhood traced count) (leftIndex rightIndex : Nat)
    (left : Model curve.polynomial inner) (right : Model curve.polynomial neighborhood.patch.base.box)
    (leftEq : left.value.eval point = (cell.model.refine (leftIndex + 2)).value.eval point)
    (rightEq : right.value.eval point = (neighborhood.patch.base.refine (rightIndex + 2)).value.eval point)
    (finish : Gaussian) (leftFinish : inner.Contains finish) (rightFinish : neighborhood.patch.box.Contains finish) :
    cell.traceTransition
      (entered := TracedPath.build (ClearPath.nil (polynomial := curve.polynomial) (ambient := outer) outer.anchor)
        (.nil outer.anchor) source) outer.contains_anchor differential degreePositive reference traced inside frame
      pointInside neighborhood leftIndex rightIndex left right leftEq rightEq finish leftFinish rightFinish =
      (show InverseModelEdgeTransition.EdgeTransition left right point finish from
        { leftStart := pointInside
          leftFinish := leftFinish
          rightStart := neighborhood.patch.box_refines.contains neighborhood.center_inside
          rightFinish := neighborhood.patch.box_refines.contains rightFinish
          sample :=
            let first := left.value.eval point
            let second := right.value.eval point
            ⟨first, rfl, second, rfl, ⟨false, second, rfl, by
              dsimp only [first, second]
              rewrite [leftEq, rightEq]
              have scalar := cell.trace_nearest
                (entered := TracedPath.build (ClearPath.nil (polynomial := curve.polynomial)
                  (ambient := outer) outer.anchor) (.nil outer.anchor) source) outer.contains_anchor
                differential degreePositive reference traced inside frame pointInside neighborhood leftIndex rightIndex
              simpa only [Norm.Basic.normSq_eq_canonical] using scalar⟩⟩ }) := rfl

end SourceCalibration

section LocalOddAccuracy

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
  (PrimitiveOverlapBounds PrimitiveEdgeAccuracy PrimitiveEdgeAnchor)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Geometry
open Purelib.Riemann.Integration

/-- The omitted pair parameter keeps the complete former local request and its selected stage. -/
example {leftBox rightBox : Box} {localClearance : RegularFaceInverseModels.Clearance polynomial leftBox}
    (bounds : PrimitiveOverlapBounds localClearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) (positive : 0 < target) :
    PrimitiveEdgeAccuracy.build bounds left right start finish target positive =
      (show PrimitiveEdgeAccuracy bounds left right start finish target from
        let scale := 12 * (left.bound + right.bound) * (bounds.numeratorUpper * bounds.inverseUpper) *
          Basic.Canonical.normSq (finish - start)
        have nonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct
            (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg left.bound_nonnegative right.bound_nonnegative))
            (Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
          (Basic.Canonical.normSq_nonneg _)
        ⟨scale, rfl, Geometric.Search.firstQuarterBelow scale 0 target,
          Geometric.Search.firstQuarterBelow_accurate scale nonnegative 0 target positive⟩) := rfl

/-- An actual adjacent-cell pair pays its retained cubic primitive discrepancy at the computed request stage.

The request, refined bank, primitives, transition sample and anchor are
computed from the same original patch. Grid corner laws derive every
endpoint containment. No final comparison or successful-domain premise is
provided by the caller.
-/
example {geometricBounds : RegularFaceInverseModels.Bounds clearance}
    {source : Owner (polynomial.eval ambient.anchor)} (patch : RectangularPatch geometricBounds source geometry)
    (numerator : Polynomial) (column : Fin columns) (row : Fin (rows + 1))
    (target : Coordinate) (positive : 0 < target) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let bounds := PrimitiveOverlapBounds.build (clearance.restrict (patch.cell_refines column.castSucc row)) numerator
    let left := (patch.models.ready column.castSucc row).model
    let right := (patch.models.ready column.succ row).model
    let request := PrimitiveEdgeAccuracy.build bounds left right start finish target positive 1
    let models := patch.models.refine request.index
    let primitives := Primitives.build models numerator 1
    let edge : EdgeTransition (left.refine request.index) (right.refine request.index) start finish :=
      (RectangularRefinementSigns.Bank.refine_model patch.models request.index column.castSucc row) ▸
      (RectangularRefinementSigns.Bank.refine_model patch.models request.index column.succ row) ▸
      EdgeTransition.build (models.ready column.castSucc row).model (models.ready column.succ row).model start finish
        (geometry.lowerRight_mem column.castSucc row) (geometry.upperRight_mem column.castSucc row)
        (geometry.lowerLeft_mem column.succ row) (geometry.upperLeft_mem column.succ row)
    let anchor := PrimitiveEdgeAnchor.build edge
      (primitives.dense column.castSucc row).value (primitives.dense column.succ row).value
    ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 →
      Basic.Canonical.normSq ((primitives.dense column.castSucc row).value.eval
          (Rational.Affine.line start (finish - start) parameter) -
        anchor.alignedValue (Rational.Affine.line start (finish - start) parameter)) < target := by
  let start := geometry.vertex column.castSucc.succ row.castSucc
  let finish := geometry.vertex column.castSucc.succ row.succ
  let bounds := PrimitiveOverlapBounds.build (clearance.restrict (patch.cell_refines column.castSucc row)) numerator
  let left := (patch.models.ready column.castSucc row).model
  let right := (patch.models.ready column.succ row).model
  let request := PrimitiveEdgeAccuracy.build bounds left right start finish target positive 1
  let models := patch.models.refine request.index
  let primitives := Primitives.build models numerator 1
  let edge : EdgeTransition (left.refine request.index) (right.refine request.index) start finish :=
    (RectangularRefinementSigns.Bank.refine_model patch.models request.index column.castSucc row) ▸
    (RectangularRefinementSigns.Bank.refine_model patch.models request.index column.succ row) ▸
    EdgeTransition.build (models.ready column.castSucc row).model (models.ready column.succ row).model start finish
      (geometry.lowerRight_mem column.castSucc row) (geometry.upperRight_mem column.castSucc row)
      (geometry.lowerLeft_mem column.succ row) (geometry.upperLeft_mem column.succ row)
  let anchor := PrimitiveEdgeAnchor.build edge
    (primitives.dense column.castSucc row).value (primitives.dense column.succ row).value
  refine fun parameter inside => ?_
  apply request.drift_lt edge (primitives.dense column.castSucc row) (primitives.dense column.succ row) anchor
    (parameter := parameter) _ _ inside
  · intro query
    have value := primitives.coefficient_eq column.castSucc row query
    rewrite [RectangularRefinementSigns.Bank.refine_model] at value
    exact value
  · intro query
    have value := primitives.coefficient_eq column.succ row query
    rewrite [RectangularRefinementSigns.Bank.refine_model] at value
    exact value

end LocalOddAccuracy

/-- Raising the zero-pair request preserves the complete original atLeast result for every input. -/
example {bounds : Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator}
    {target : Coordinate} (request : GridPrimitiveAccuracy bounds columns target) (minimum : Nat) :
    request.atLeast minimum =
      (let index := max minimum request.index
       { edgeScale := request.edgeScale, edgeScale_eq := request.edgeScale_eq
         scale := request.scale, scale_eq := request.scale_eq
         index := index
         edgeBound := Geometric.Basic.quarterRadius request.edgeScale index, edgeBound_eq := rfl
         globalBound := Geometric.Basic.quarterRadius request.scale index
         globalBound_eq := by rw [request.scale_eq]; simp only [quarterRadius_eq_mul_pow]; ring1
         accurate := (quarterRadius_antitone
           (GridPrimitiveAccuracy.scale_nonnegative request)
           (Purelib.Data.Nat.Order.le_max_right _ _)).trans_lt
           ((GridPrimitiveAccuracy.globalBound_eq_quarter request).symm.trans_lt request.accurate) } :
        GridPrimitiveAccuracy bounds columns target) := rfl

/-- Retain one original paid request, raise its existing stage, then acquire its actual cubic primitive bank.

The complete initial and raised records remain in the returned tuple. The
same raised request supplies both the retained floor proof and the model
index used by the original glued-bank constructor.
-/
private def laterPrimitives {bounds : RegularFaceInverseModels.Bounds clearance}
    {source : Owner (polynomial.eval ambient.anchor)} (patch : RectangularPatch bounds source geometry)
    (numerator : Polynomial) (target : Coordinate) (positive : 0 < target) (minimum : Nat) :
    let bounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build clearance numerator
    Σ initial : {value : GridPrimitiveAccuracy bounds columns target 1 //
      value = GridPrimitiveAccuracy.build bounds columns target positive 1},
    Σ request : {value : GridPrimitiveAccuracy bounds columns target 1 //
      value = initial.val.atLeast minimum ∧ minimum ≤ value.index},
      {value : GluedPrimitives (patch.models.refine request.val.index) numerator 1 //
        value = request.val.prepare patch.sheets} :=
  let bounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build clearance numerator
  let initial := GridPrimitiveAccuracy.build bounds columns target positive 1
  let request := initial.atLeast minimum
  let actual := request.prepare patch.sheets
  ⟨⟨initial, rfl⟩, ⟨request, rfl, initial.atLeast_index_ge minimum⟩, actual, rfl⟩

end TestPurelib.Riemann.RectangularPrimitives
