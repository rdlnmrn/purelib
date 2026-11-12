module

import Purelib.Tactic.Ring

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Jets
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Primitive
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Polynomial.Dense.Power
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Circuit
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Source
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathParentContainment
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Data.List.GetD
import Purelib.Data.Nat.List.Maximum
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial

import all TestPurelib.Curves.Legendre.ParallelDifferential

/-! # Primitive requests on the retained regular parallel circuits

The original circuit fixtures supply the same spatial legs, scalar layers
and owner budgets. The import-all fixture owner retains the bodies needed
by dependent layer and primitive readback regressions.
-/

namespace TestPurelib.Curves.Legendre.ParallelPrimitiveRequests

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Bounds.Quarter (quarter_pos four_quarters)

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Dyadic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerMoves
open Purelib.RootIsolation
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveReading)
open Purelib.Riemann.Normalization
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.List (DependentProduct)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells (Model)


open TestPurelib.Curves.Legendre.ParallelDifferential

attribute [local irreducible] circuit valueData channelData valuePiece spatial ownerBudget ownerTrace primitiveBounds

section PrimitiveMove

open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Parallel.OwnerMove (PrimitiveTarget)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairGeometry)

variable (site : Fin 2) (quarter : UnitCircuitQuarter)
variable {budget : Parallel.OwnerBudget (spatial site quarter).leg (ownerBudget site quarter)
  (some (primitiveBounds site quarter).timeRequest)}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {firstReading : Radial.Transport.Reading (spatial site quarter).leg.actual first firstInside}
variable {lastReading : Radial.Transport.Reading (spatial site quarter).leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometry : Parallel.Geometry firstReading lastReading (spatial site quarter).leg.regular payment}
variable {oldFirst oldLast : Canonical}
variable {data : SquareRootTrace.EdgeData (Paths.polynomial (parameter site)) oldFirst oldLast
  (coordinate site (parameter site) 2 quarter (by decide +kernel) first)
  (coordinate site (parameter site) 2 quarter (by decide +kernel) last)}
variable {paid : (first - last) ^ 2 < ((spatial site quarter).leg.source.residualTimeRequest
  (Parallel.OwnerBudget.accuracy (spatial site quarter).leg budget.floor
    (some (primitiveBounds site quarter).timeRequest)).val
  ((spatial site quarter).leg.traceMovement (ownerBudget site quarter).bounds)
  ((spatial site quarter).leg.traceMovement_nonnegative
    (ownerBudget site quarter).bounds (ownerBudget site quarter).bounds_eq)).tolerance}
variable {dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site (parameter site) ^ 2 / 1024}
variable {source : Owner ((Paths.polynomial (parameter site)).eval
  (coordinate site (parameter site) 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent
  (source.certificate source.parameterNonzero).value.name firstReading.lift.value.name}

/-- Materialize the original common primitive Point for any actual paid move of the two retained circuit fixtures.

The supplied move already contains its actual fixed preparation and target.
The primitive domain and signed link are constructed from its cap and stored
payments; neither coverage nor a successful target comparison is supplied.
-/
private def primitiveMovePoint
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    Parallel.OwnerMove.PrimitiveTarget (primitiveBounds site quarter) move count :=
  Parallel.OwnerMove.primitiveTarget (primitiveBounds site quarter) move count

attribute [local irreducible] primitiveMovePoint

/-- The primitive client retains the whole actual original move, including both nominal endpoint owners and caches. -/
theorem primitive_move_original
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    (primitiveMovePoint site quarter move count).move = move :=
  (primitiveMovePoint site quarter move count).move_eq

/-- The actual original scalar endpoint channel lies on the same signed sheet as the retained primitive Point.

This all-input fixture consumes the actual paid move and the newly retained
Point at both labelled parameters and every oriented quarter. It checks the
original scalar-to-primitive contract without executing the full fine mesh
or asserting supplied-trace integral equivalence.
-/
def primitive_move_reading
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    NamedEquivalent lastReading.lift.value.name
      (primitiveMovePoint site quarter move count).sample.certificate.value.name :=
  (primitiveMovePoint site quarter move count).readingEquivalent

/-- The exact original endpoint cache type with both actual same-patch Points and retained scalar links. -/
private def PrimitiveMoveEndpoints
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) : Type :=
    Σ retained : {actual : Parallel.OwnerMove.PrimitiveTarget (primitiveBounds site quarter) move count //
        actual = primitiveMovePoint site quarter move count},
    Σ sample : ContinuedNeighborhood.Point retained.val.patch
        (coordinate site (parameter site) 2 quarter (by decide +kernel) first),
      NamedEquivalent firstReading.lift.value.name sample.certificate.value.name

/-- Retain both original endpoint Points on the same cached primitive patch and their genuine scalar links.

The complete primitive target cache is stored once. Its source Point uses
the existing seed owner and original paid join; its target Point and original
move are the same prior caches. No independent source owner is acquired.
-/
private def primitiveMoveEndpoints
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    PrimitiveMoveEndpoints site quarter move count :=
  let retained := primitiveMovePoint site quarter move count
  let sample := retained.sourcePoint
  ⟨⟨retained, rfl⟩, sample⟩

attribute [local irreducible] primitiveMoveEndpoints

/-- Both signed endpoints retain the entire same supplied primitive cache, including its literal original move. -/
theorem primitive_endpoints_original
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    (primitiveMoveEndpoints site quarter move count).1.val = primitiveMovePoint site quarter move count :=
  (primitiveMoveEndpoints site quarter move count).1.property

/-- The original scalar source is linked to the actual stored source Point of the same primitive patch. -/
def primitive_source_reading
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    NamedEquivalent firstReading.lift.value.name
      (primitiveMoveEndpoints site quarter move count).2.1.certificate.value.name :=
  (primitiveMoveEndpoints site quarter move count).2.2

/-- The original scalar target keeps its retained signed link on that very same patch and endpoint cache. -/
def primitive_endpoints_target
    (move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    NamedEquivalent lastReading.lift.value.name
      (primitiveMoveEndpoints site quarter move count).1.val.sample.certificate.value.name :=
  (primitiveMoveEndpoints site quarter move count).1.val.readingEquivalent

/-- Build the original inverse-root primitive from the supplied actual endpoint cache and original value numerator. -/
private def primitiveMoveModel
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (index : Nat) (coordinateIndex : Fin 2) :
    PrimitiveModel endpoints.1.val.patch index (Specification.valueNumerator coordinateIndex) :=
  PrimitiveModel.ofIndex endpoints.1.val.patch index (Specification.valueNumerator coordinateIndex)

/-- The whole cached primitive is exactly the original same-patch factory result. -/
private theorem primitiveMoveModel_eq
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (index : Nat) (coordinateIndex : Fin 2) :
    primitiveMoveModel site quarter endpoints index coordinateIndex =
      PrimitiveModel.ofIndex endpoints.1.val.patch index (Specification.valueNumerator coordinateIndex) := rfl

attribute [local irreducible] primitiveMoveModel

/-- The original value numerator and common inverse-root model give the actual finite primitive increment estimate.

The model is constructed from the same stored patch. Both endpoint domains
are derived by the production cache, and its source Point is linked to the
original scalar Reading. The geometric inverse-error scale is retained; no
supplied-trace integral equality or unproved refinement decay is asserted.
-/
theorem primitive_common_increment
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (index : Nat) (coordinateIndex : Fin 2) {root : Canonical}
    (possible : endpoints.2.1.certificate.value.name.process.Possible
      (endpoints.2.1.readingState index) root) :
    let numerator := Specification.valueNumerator coordinateIndex
    let model := primitiveMoveModel site quarter endpoints index coordinateIndex
    Norm.Basic.normSq (model.primitive.value.eval
        (coordinate site (parameter site) 2 quarter (by decide +kernel) last) -
      model.primitive.value.eval (coordinate site (parameter site) 2 quarter (by decide +kernel) first) -
      (numerator.eval (coordinate site (parameter site) 2 quarter (by decide +kernel) first) / root) *
        (coordinate site (parameter site) 2 quarter (by decide +kernel) last -
          coordinate site (parameter site) 2 quarter (by decide +kernel) first)) ≤
      2 * (model.primitive.remainderBound * Norm.Basic.normSq
          (coordinate site (parameter site) 2 quarter (by decide +kernel) last -
            coordinate site (parameter site) 2 quarter (by decide +kernel) first) ^ 2 +
        Norm.Basic.normSq (numerator.eval
            (coordinate site (parameter site) 2 quarter (by decide +kernel) first)) *
          Geometric.Basic.quarterRadius endpoints.1.val.patch.inverseErrorScale index * Norm.Basic.normSq
            (coordinate site (parameter site) 2 quarter (by decide +kernel) last -
              coordinate site (parameter site) 2 quarter (by decide +kernel) first)) := by
  dsimp only
  simp only [Norm.Basic.normSq_eq_canonical]
  exact PrimitiveModel.operational_increment_bound
    (model := primitiveMoveModel site quarter endpoints index coordinateIndex)
    (start := coordinate site (parameter site) 2 quarter (by decide +kernel) first)
    (finish := coordinate site (parameter site) 2 quarter (by decide +kernel) last)
    (root := root) endpoints.1.val.source_inside endpoints.1.val.target_inside endpoints.2.1 possible

/-- Materialize actual interior links for both retained circuit fixtures and their original Reading bank.

The production builder derives domains, continuation payments and signed
comparisons from each genuine time occurrence. One exact original prepared
source view is captured outside its finite entry producer.
-/
private def primitiveMoveInteriors
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (times : List Fraction.Rational)
    (inside : Parallel.Inside times) (readings : Parallel.Readings (spatial site quarter).leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) :
    PrimitiveTarget.CurvePoints (primitiveBounds site quarter) endpoints.1.val times inside readings interior :=
  PrimitiveTarget.curvePoints (primitiveBounds site quarter) endpoints.1.val times inside readings interior

attribute [local irreducible] primitiveMoveInteriors

/-- Every actual interior entry retains the complete original endpoint cache and its unchanged move. -/
theorem primitive_interiors_parent
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (times : List Fraction.Rational)
    (inside : Parallel.Inside times) (readings : Parallel.Readings (spatial site quarter).leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) (index : Fin times.length) :
    (PrimitiveTarget.CurvePoints.get (primitiveBounds site quarter)
      (primitiveMoveInteriors site quarter endpoints times inside readings interior) index).parent = endpoints.1.val :=
  (PrimitiveTarget.CurvePoints.get (primitiveBounds site quarter)
    (primitiveMoveInteriors site quarter endpoints times inside readings interior) index).parent_eq

/-- Each original scalar Reading is linked to its same retained primitive Point. -/
def primitive_interiors_reading
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (times : List Fraction.Rational)
    (inside : Parallel.Inside times) (readings : Parallel.Readings (spatial site quarter).leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) (index : Fin times.length) :
    NamedEquivalent (Parallel.Readings.get readings index).lift.value.name
      (PrimitiveTarget.CurvePoints.get (primitiveBounds site quarter)
        (primitiveMoveInteriors site quarter endpoints times inside readings interior)
        index).sample.certificate.value.name :=
  (PrimitiveTarget.CurvePoints.get (primitiveBounds site quarter)
    (primitiveMoveInteriors site quarter endpoints times inside readings interior) index).readingEquivalent

/-- The actual scalar coefficient and shared common primitive are compared through their retained original root states.

This client consumes the supplied interior Point, actual scalar cell and
complete original inverse-model/power caches. The production comparison
constructs its finite payment, signed relation, domain and denominator
floors internally, without acquiring another Point, root or scalar cell.
-/
private def primitiveScalarCoefficient
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    {span : Interval.Bounds} {timeInside : FixedRootBoxPath.Inside span.lower}
    {pointReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower timeInside}
    {interior : first < span.lower ∧ span.lower < last}
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      span.lower pointReading interior) {cellAccuracy : AccuracyRequest}
    (cell : Cells.Model (valueData site) pointReading cellAccuracy)
    {stage : Nat}
    {inverse : InverseRootPolynomial.Model (Paths.polynomial (parameter site))
      endpoints.1.val.patch.base.box} {powers : OddPowers inverse.value}
    (shared : PrimitiveReading
      point.sample stage inverse powers)
    (common : PrimitiveModel endpoints.1.val.patch stage (Specification.valueNumerator 0))
    (target : Fraction.Rational) (positive : 0 < target) :
    {actual : Approximation.Gaussian.Equivalence.Observation.Comparison cell.rootReading shared.rootReading target //
      cell.primitiveResidual common.coefficient ≤
        Norm.Basic.normSq (((Specification.valueSpecification (parameter site) 0).scale *
          (Specification.valueSpecification (parameter site) 0).numerator.eval
            (Radial.point site (parameter site) 2 (Waist.direction quarter span.lower) (by decide +kernel)).base) *
              Radial.Tangent.baseVelocity site (parameter site) 2 quarter span.lower) *
          (2 * (Geometric.Basic.quarterRadius endpoints.1.val.patch.inverseErrorScale stage +
            ((Model.comparisonFloor pointReading endpoints.1.val.patch)⁻¹ *
              (Model.comparisonFloor pointReading endpoints.1.val.patch)⁻¹) * actual.bound))} :=
  PrimitiveTarget.CurvePoint.coefficientComparison (primitiveBounds site quarter) point cell
    (Specification.valueSpecification_denominatorPairs (parameter site) 0) rfl shared common target positive

/-- The actual scalar-cell consumer requests its root accuracy and derives the finite coefficient payment internally.

The same completed scalar cell, retained CurvePoint, original common model
and power caches are supplied. The production constructor selects one
actual root observation and retains its shared reading/comparison, with no
successful radius or sampled-coefficient inequality supplied by this client.
-/
private def primitiveScalarRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    {span : Interval.Bounds} {timeInside : FixedRootBoxPath.Inside span.lower}
    {pointReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower timeInside}
    {interior : first < span.lower ∧ span.lower < last}
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      span.lower pointReading interior) {cellAccuracy : AccuracyRequest}
    (cell : Cells.Model (valueData site) pointReading cellAccuracy)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial (parameter site))
      endpoints.1.val.patch.base.box} {powers : OddPowers inverse.value}
    (sameModel : inverse = endpoints.1.val.patch.base.refine stage)
    (common : PrimitiveModel endpoints.1.val.patch stage (Specification.valueNumerator 0)) :=
  PrimitiveTarget.CurvePoint.coefficientRequest (powers := powers) (primitiveBounds site quarter) point cell
    (Specification.valueSpecification_denominatorPairs (parameter site) 0)
    (fun _ => (Basic.one_mul _).symm) sameModel common

/-- The actual scalar source cell consumes the same retained source Point and shared coefficient-request procedure.

The source-time equation records the original occurrence, rather than a
successful sheet or coefficient comparison. Same-quarter query equations
and original source containment derive those conditions internally. Both
original source/readings, inverse/power caches and complete request remain
unchanged, with no source preparation, Point acquisition or replacement cell.
-/
private def primitiveScalarSourceRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    {span : Interval.Bounds} {timeInside : FixedRootBoxPath.Inside span.lower}
    {pointReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower timeInside}
    {cellAccuracy : AccuracyRequest} (sameTime : span.lower = first)
    (cell : Cells.Model (valueData site) pointReading cellAccuracy)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial (parameter site))
      endpoints.1.val.patch.base.box}
    (powers : OddPowers inverse.value)
    (sameModel : inverse = endpoints.1.val.patch.base.refine stage)
    (common : PrimitiveModel endpoints.1.val.patch stage (Specification.valueNumerator 0)) :=
  let retained := PrimitiveTarget.SourcePoint.atTime (primitiveBounds site quarter)
    endpoints.1.val endpoints.2 span.lower sameTime
  let linked : PrimitiveTarget.ScalarPoint (primitiveBounds site quarter) endpoints.1.val endpoints.2
      pointReading := .inl ⟨sameTime, retained⟩
  PrimitiveTarget.ScalarPoint.coefficientRequest (primitiveBounds site quarter) linked cell
    (Specification.valueSpecification_denominatorPairs (parameter site) 0)
    (fun _ => (Basic.one_mul _).symm) powers sameModel common

/-- The computed model and scalar stages pay a real original scalar-layer occurrence on its retained primitive parent.

The two original selections are supplied as completed caches. The actual
original layer uses their scalar stage, and its bounded ordinal retains the
same original piece through the whole stored-leg equality. One coefficient
request consumes the same Point, inverse model, powers and common primitive;
its requested residual bound is derived from the actual layer accuracy.
-/
private def primitiveScalarSelected
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (selected : {actual :
      Geometric.Search.Selection
        (PrimitiveTarget.modelErrorScale (primitiveBounds site quarter) endpoints.1.val (valueData site))
        modelFloor (target / 2) ×
      Geometric.Search.Selection
        (PrimitiveTarget.samplingErrorScale (primitiveBounds site quarter) endpoints.1.val
          (valueData site) accuracy) scalarFloor (target / 2) //
      actual = PrimitiveTarget.coefficientSelections (primitiveBounds site quarter) endpoints.1.val
        (valueData site) accuracy modelFloor scalarFloor target positive})
    (layer : Refinement.Layer (valuePiece site quarter) selected.val.2.stage)
    (index : Fin layer.pieces.length)
    {interior : first < (valueLayerPiece site quarter layer index).span.lower ∧
      (valueLayerPiece site quarter layer index).span.lower < last}
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      (valueLayerPiece site quarter layer index).span.lower (valueLayerPiece site quarter layer index).source interior)
    {inverse : InverseRootPolynomial.Model (Paths.polynomial (parameter site)) endpoints.1.val.patch.base.box}
    (powers : OddPowers inverse.value)
    (sameModel : inverse = endpoints.1.val.patch.base.refine selected.val.1.stage)
    (common : PrimitiveModel endpoints.1.val.patch selected.val.1.stage (Specification.valueNumerator 0)) := by
  let piece := valueLayerPiece site quarter layer index
  let linked : PrimitiveTarget.ScalarPoint (primitiveBounds site quarter) endpoints.1.val endpoints.2
      piece.source := .inr ⟨interior, point⟩
  let request := PrimitiveTarget.ScalarPoint.coefficientRequest (primitiveBounds site quarter) linked piece.cell
    (Specification.valueSpecification_denominatorPairs (parameter site) 0)
    (fun _ => (Basic.one_mul _).symm) powers sameModel common
  have selectionEqual := selected.property
  have modelEqual := congrArg (fun pair => pair.1.stage) selectionEqual
  have scalarEqual := congrArg (fun pair => pair.2.stage) selectionEqual
  have attained : piece.cell.primitiveResidual common.coefficient < target :=
    PrimitiveTarget.coefficient_error_lt (primitiveBounds site quarter) endpoints.1.val piece.cell
      sameModel common request
      accuracy selected.val.2.stage modelFloor scalarFloor target positive
      (valueLayerOnCoverage site quarter layer).accuracy_eq modelEqual.symm.le scalarEqual.symm.le
  exact @Subtype.mk _ (fun _ => piece.cell.primitiveResidual common.coefficient < target) request attained

/-- The retained primitive bounds its increment from a linked interior Point to the original endpoint.

The supplied model is consumed as a complete value on the existing endpoint
patch. No primitive factory, scalar query or Point acquisition is invoked by
the comparison. Both domains are derived from the actual original paid move.
The independent geometric inverse-error and Taylor terms keep their units.
-/
theorem primitive_interior_increment
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    {time : Fraction.Rational} {timeInside : FixedRootBoxPath.Inside time}
    {pointReading : Radial.Transport.Reading (spatial site quarter).leg.actual time timeInside}
    {interior : first < time ∧ time < last}
    (value : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val time pointReading interior)
    (index : Nat) (coordinateIndex : Fin 2)
    (model : PrimitiveModel endpoints.1.val.patch index (Specification.valueNumerator coordinateIndex))
    {root : Canonical}
    (possible : value.sample.certificate.value.name.process.Possible (value.sample.readingState index) root) :
    let start := (Radial.point site (parameter site) 2 (Waist.direction quarter time) (by decide +kernel)).base
    let finish := coordinate site (parameter site) 2 quarter (by decide +kernel) last
    let numerator := Specification.valueNumerator coordinateIndex
    Norm.Basic.normSq (model.primitive.value.eval finish - model.primitive.value.eval start -
      (numerator.eval start / root) * (finish - start)) ≤
      2 * (model.primitive.remainderBound * Norm.Basic.normSq (finish - start) ^ 2 +
        Norm.Basic.normSq (numerator.eval start) * Geometric.Basic.quarterRadius
          endpoints.1.val.patch.inverseErrorScale index * Norm.Basic.normSq (finish - start)) := by
  dsimp only
  simp only [Norm.Basic.normSq_eq_canonical]
  exact PrimitiveModel.operational_increment_bound (model := model)
    (start := (Radial.point site (parameter site) 2 (Waist.direction quarter time) (by decide +kernel)).base)
    (finish := coordinate site (parameter site) 2 quarter (by decide +kernel) last) (root := root)
    (PrimitiveTarget.curve_inside (primitiveBounds site quarter) endpoints.1.val time ⟨interior.1.le, interior.2.le⟩)
    endpoints.1.val.target_inside value.sample possible

/-- Each actual cached spatial parent lies in the same retained primitive domain as the original capped move.

The supplied frame, complete spatial cover and numerical parent cache remain
the original inputs. The actual route hull and cap derive containment; no
successful common-patch or signed-overlap hypothesis is supplied.
-/
theorem primitive_spatial_parent_inside
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (parent : CenteredEdge (Periods.Fibre.frameCurve frame) ⟨0⟩) (member : parent ∈ cache.parents) :
    endpoints.1.val.patch.box.Contains (parent.edge.point 0) ∧
      endpoints.1.val.patch.box.Contains (parent.edge.point 1) :=
  PrimitiveTarget.parent_endpoints_inside (primitiveBounds site quarter) endpoints.1.val
    frame covered cache parent member

/-- Cache actual original parent prefixes from the supplied spatial cover and its same retained parent bank.

The original production equation comes from the retained Covered itself;
neither trace provenance nor a successful owner comparison is a caller input.
-/
private def primitiveSpatialPrefixes (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0) :
    ParentCache.OwnerPrefixes cache :=
  cache.ownerPrefixes geometry.route.within covered.block_eq

/-- Every actual cached parent-prefix vertex satisfies the intrinsic movement bound of the same original spatial leg.

The complete original frame, cover and parent cache are retained inputs.
The bank reads their once-forced trace, and its exact prefix membership
transports the original internally proved route-Horner bound.
-/
theorem primitive_spatial_prefix_movement (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (index : Fin cache.parents.length) (point : Canonical)
    (member : point ∈ OwnerPath.vertices
      (DependentProduct.get cache.parents (primitiveSpatialPrefixes site quarter frame covered cache) index)) :
    Norm.Basic.normSq ((Paths.polynomial (parameter site)).eval point -
      (Paths.polynomial (parameter site)).eval
        (coordinate site (parameter site) 2 quarter (by decide +kernel) first)) ≤
      (spatial site quarter).leg.traceMovement (ownerBudget site quarter).bounds * (first - last) ^ 2 := by
  have entry := cache.ownerPrefixes_get geometry.route.within covered.block_eq index
  have retained : point ∈ OwnerPath.vertices
      (cache.ownerPrefixFromTrace geometry.route.within covered.block_eq covered.block.traced.trace.get rfl index) :=
    Eq.mp (congrArg (fun path : ParentCache.OwnerPrefix cache index => point ∈ OwnerPath.vertices path) entry) member
  exact PrimitiveTarget.parent_prefix_movement (leg := (spatial site quarter).leg)
    (coarse := ownerBudget site quarter) frame covered cache index point retained

/-- The original production signed Point bank on these actual retained fixture inputs. -/
private def PrimitiveSpatialPoints
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0) : Type :=
  PrimitiveTarget.ParentPoints (primitiveBounds site quarter) endpoints.1.val endpoints.2 frame covered cache

/-- Consume the original library producer on the retained fixture patch, parent cache and complete source Point. -/
private def primitiveSpatialPoints
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0) :
    PrimitiveSpatialPoints site quarter endpoints frame covered cache :=
  PrimitiveTarget.parentPoints (primitiveBounds site quarter) endpoints.1.val endpoints.2 frame covered cache

/-- The original local request and common primitive share their actual spatial-parent domains and signed root.

The supplied cached Point bank supplies the actual parent link. Both common
endpoint containments follow from the same retained cover and original
parent index; the request supplies its own local endpoint domains.
-/
private def primitiveSpatialRequestGeometry
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (index : Fin cache.parents.length)
    (localRequest : LocalRequest (cache.parents[index.val]'index.isLt) localCount target) :=
  let parent := cache.parents[index.val]'index.isLt
  have retained := primitive_spatial_parent_inside site quarter endpoints frame covered cache parent
    (_root_.List.getElem_mem index.isLt)
  have firstInside : endpoints.1.val.patch.box.Contains
      (parent.edge.segment.pointAt parent.edge.left.parameter) := by
    have first := retained.1
    rewrite [parent.edge.point_zero] at first
    exact first
  localRequest.pairGeometry endpoints.1.val.patch firstInside retained.2

/-- Every retained local/common primitive pair on an actual spatial parent has its internally derived signed budget.

The actual cached bank provides the same Point and original parent link.
Neither a successful sheet comparison nor domain/decay evidence is a caller
premise. The estimate uses the two actual supplied cached polynomials at the
minimum of their independent original refinement indices.
-/
private theorem primitive_spatial_model_mismatch
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (index : Fin cache.parents.length)
    (localRequest : LocalRequest (cache.parents[index.val]'index.isLt) localCount target)
    {commonIndex : Nat}
    (model : PrimitiveModel endpoints.1.val.patch commonIndex
      (differentialNumerator (⟨0⟩ : Differential 1))) :
    let parent := cache.parents[index.val]'index.isLt
    let pair := primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index localRequest
    Norm.Basic.normSq (localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
      localRequest.request.model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) +
      (model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        model.primitive.value.eval (parent.edge.point 1))) ≤
      Geometric.Basic.quarterRadius pair.budget.scale (min localRequest.request.index commonIndex) := by
  let pair := primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index localRequest
  let retained := DependentProduct.get cache.parents
    (PrimitiveTarget.ParentPoints.points (primitiveBounds site quarter) points) index
  have bounded := localRequest.increment_mismatch_le pair retained.1 retained.2.2 model
    (min localRequest.request.index commonIndex) (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  exact (Norm.Basic.normSq_eq_canonical _).trans_le bounded

/-- Exact original per-parent pair, finite selection, refined request and common model with its attained mismatch.

Every computed value retains its whole factory equation. The finite request
and the actual later models share the same original parent and primitive
domains; no new root or primitive-certificate family is introduced.
-/
private def PrimitiveSpatialRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (index : Fin cache.parents.length)
    (localRequest : LocalRequest (cache.parents[index.val]'index.isLt) localCount target)
    (positive : 0 < target) (tolerance : Fraction.Rational) : Type 2 :=
  let parent := cache.parents[index.val]'index.isLt
  Σ pair : {actual : PrimitivePairGeometry localRequest.neighborhood endpoints.1.val.patch
      (differentialNumerator (⟨0⟩ : Differential 1))
      (parent.edge.segment.pointAt parent.edge.left.parameter) (parent.edge.point 1) //
    actual = primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index localRequest},
  Σ selection : Geometric.Search.Selection pair.val.budget.scale 0 tolerance,
  Σ refined : {actual : LocalRequest parent localCount target //
    actual = localRequest.refine positive (Riemann.Integration.PreparedDyadicRefinements.AllParentsProper.get
      cache.proper index) selection.stage},
  {model : PrimitiveModel endpoints.1.val.patch selection.stage
      (differentialNumerator (⟨0⟩ : Differential 1)) //
    Norm.Basic.normSq (refined.val.request.model.primitive.value.eval (parent.edge.point 1) -
      refined.val.request.model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) +
      (model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        model.primitive.value.eval (parent.edge.point 1))) < tolerance}

/-- Construct actual cached models attaining a finite mismatch request on any retained spatial parent.

The intrinsic cover and signed Point bank derive all domains and sheet
relations. Original properness is read at the same bounded occurrence.
Adequate requests return literally; only necessary local model refinement
and the one common primitive model are constructed at the selected stage.
-/
private def primitiveSpatialRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (index : Fin cache.parents.length)
    (localRequest : LocalRequest (cache.parents[index.val]'index.isLt) localCount target)
    (positive : 0 < target) (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance) :
    PrimitiveSpatialRequested site quarter endpoints frame covered cache index localRequest positive tolerance := by
  let pair := primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index localRequest
  let selection := pair.budget.choose 0 tolerance tolerancePositive
  have proper := Riemann.Integration.PreparedDyadicRefinements.AllParentsProper.get cache.proper index
  let refined := localRequest.refine positive proper selection.stage
  let model := PrimitiveModel.ofIndex endpoints.1.val.patch selection.stage
    (differentialNumerator (⟨0⟩ : Differential 1))
  let retained := DependentProduct.get cache.parents
    (PrimitiveTarget.ParentPoints.points (primitiveBounds site quarter) points) index
  have attained := localRequest.refine_increment_mismatch_lt positive proper pair retained.1 retained.2.2
    selection model (Nat.le_refl _)
  exact ⟨⟨pair, rfl⟩, selection, ⟨refined, rfl⟩,
    ⟨model, (Norm.Basic.normSq_eq_canonical _).trans_lt attained⟩⟩

/-- The actual ordered refined request bank, one common model and its paid aggregate on the retained parent list.

The selected original parent fixes a computed finite stage. Every retained
bank entry attains that floor, while its same selected occurrence satisfies
the signed local/common estimate. The actual aggregate keeps the whole bank
and compares its cached sum with its actual flattened child-block integral.
-/
private def PrimitiveSpatialSumRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length) cache.parents)
    (index : Fin cache.parents.length) (positive : 0 < target) (tolerance : Fraction.Rational) : Type 2 :=
  let parent := cache.parents[index.val]'index.isLt
  let pair := primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index (requests.get index)
  Σ selection : Geometric.Search.Selection pair.budget.scale 0 tolerance,
  Σ refined : {actual : RequestedParents localCount
      (Budget.Aggregate.perTerm target cache.parents.length) cache.parents //
    actual = requests.refine (Budget.Aggregate.perTerm_positive positive cache.parents.length)
      cache.proper selection.stage},
  Σ model : PrimitiveModel endpoints.1.val.patch selection.stage
      (differentialNumerator (⟨0⟩ : Differential 1)),
  {result : PrimitiveSumRequest cache.parents localCount target //
    result = PrimitiveSumRequest.ofRequests cache.parents target positive refined.val ∧
    Norm.Basic.normSq (result.primitiveSum - result.integralSample) < target ∧
    (∀ occurrence : Fin cache.parents.length, selection.stage ≤ (refined.val.get occurrence).request.index) ∧
    Norm.Basic.normSq ((refined.val.get index).request.model.primitive.value.eval (parent.edge.point 1) -
      (refined.val.get index).request.model.primitive.value.eval
        (parent.edge.segment.pointAt parent.edge.left.parameter) +
      (model.primitive.value.eval (parent.edge.segment.pointAt parent.edge.left.parameter) -
        model.primitive.value.eval (parent.edge.point 1))) < tolerance}

/-- Refine the supplied actual bank at a computed signed-mismatch stage and assemble its actual integral caches once.

Original properness is derived from the same parent cache. The one common
model lies outside all bank entry producers, and the selected Point/link is
read at the same original bounded occurrence. No successful precision or
sheet comparison is supplied by the caller.
-/
private def primitiveSpatialSumRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count localCount : Nat}
    {target : Fraction.Rational} (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length) cache.parents)
    (index : Fin cache.parents.length) (positive : 0 < target)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance) :
    PrimitiveSpatialSumRequested site quarter endpoints frame covered cache requests index positive tolerance := by
  let original := requests.get index
  let pair := primitiveSpatialRequestGeometry site quarter endpoints frame covered cache index original
  let selection := pair.budget.choose 0 tolerance tolerancePositive
  have localPositive := Budget.Aggregate.perTerm_positive positive cache.parents.length
  let refined := requests.refine localPositive cache.proper selection.stage
  let model := PrimitiveModel.ofIndex endpoints.1.val.patch selection.stage
    (differentialNumerator (⟨0⟩ : Differential 1))
  let result := PrimitiveSumRequest.ofRequests cache.parents target positive refined
  let retained := DependentProduct.get cache.parents
    (PrimitiveTarget.ParentPoints.points (primitiveBounds site quarter) points) index
  have attained := original.refine_increment_mismatch_lt localPositive
    (Riemann.Integration.PreparedDyadicRefinements.AllParentsProper.get cache.proper index)
    pair retained.1 retained.2.2 selection model (Nat.le_refl _)
  have requested := requests.get_refine localPositive cache.proper selection.stage index
  refine ⟨selection, ⟨refined, rfl⟩, model, ⟨result, rfl, ?_, ?_, ?_⟩⟩
  · exact (Norm.Basic.normSq_eq_canonical _).trans_lt result.accurate
  · intro occurrence
    exact requests.refine_index_ge localPositive cache.proper selection.stage occurrence
  · change Norm.Basic.normSq ((refined.get index).request.model.primitive.value.eval _ -
      (refined.get index).request.model.primitive.value.eval _ + _) < tolerance
    rewrite [requested]
    exact (Norm.Basic.normSq_eq_canonical _).trans_lt attained

/-- An actual finite-accuracy common-boundary comparison on the same retained spatial parent cache.

The initial original request bank is acquired once from its retained patch
coverage. Both quarter allowances are computed internally, and the public
production route pays every parent selection and one common primitive.
This is a finite spatial-sample comparison, not whole-program equivalence.
-/
private def primitiveSpatialIntegralRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Σ initial : {actual : RequestedParents 1
        (Budget.Aggregate.perTerm (accuracy / 4) cache.parents.length) cache.parents //
      actual = RequestedParents.acquire cache.covered
        (Budget.Aggregate.perTerm (accuracy / 4) cache.parents.length)
        (Budget.Aggregate.perTerm_positive
          (quarter_pos positive) cache.parents.length) cache.proper},
    {value : PrimitiveTarget.ParentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
        frame covered cache initial.val
        (quarter_pos positive) (accuracy / 4)
        (quarter_pos positive) //
      Norm.Basic.normSq (value.boundary - value.request.integralSample) < accuracy} := by
  have quarterPositive : 0 < accuracy / 4 := quarter_pos positive
  let allowance := Budget.Aggregate.perTerm (accuracy / 4) cache.parents.length
  have allowancePositive := Budget.Aggregate.perTerm_positive quarterPositive cache.parents.length
  let initial := RequestedParents.acquire cache.covered allowance allowancePositive cache.proper
  let value := PrimitiveTarget.parentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
    frame covered cache points initial quarterPositive (accuracy / 4) quarterPositive
  have attained := value.accurate
  have paid := four_quarters accuracy
  exact ⟨⟨initial, rfl⟩, ⟨value, (Norm.Basic.normSq_eq_canonical _).trans_lt (attained.trans_eq paid)⟩⟩

/-- An actual existing spatial aggregate can pay a new target without changing any retained source neighborhood.

Strict parent order comes from the same actual cache. The returned request
attains both the new integral target and floor at every original occurrence;
all original local root/source neighborhoods are equal as COMPLETE values.
-/
private def primitiveSpatialRetargeted {localCount : Nat} {target : Fraction.Rational}
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (original : PrimitiveSumRequest cache.parents localCount target) (next : Fraction.Rational)
    (positive : 0 < next) (minimum : Nat) :
    {actual : PrimitiveSumRequest cache.parents localCount next //
      actual = original.retarget next positive cache.proper minimum ∧
      Norm.Basic.normSq (actual.primitiveSum - actual.integralSample) < next ∧
      (∀ index : Fin cache.parents.length, minimum ≤ (actual.requests.get index).request.index) ∧
      (∀ index : Fin cache.parents.length, (actual.requests.get index).neighborhood =
        (original.requests.get index).neighborhood)} := by
  let actual := original.retarget next positive cache.proper minimum
  exact ⟨actual, rfl, (Norm.Basic.normSq_eq_canonical _).trans_lt actual.accurate,
    original.retarget_index_ge next positive cache.proper minimum,
    original.retarget_neighborhood next positive cache.proper minimum⟩

/-- A computed weaker target preserves a retained actual parent's complete primitive model and child block.

Both new payments follow internally from the original request's validity.
The same actual proper parent and stored model index pay the new request;
no successful model/spatial reuse condition is a caller assumption.
-/
private theorem primitive_spatial_weaker_target_reuses
    {localCount : Nat} {target : Fraction.Rational}
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (index : Fin cache.parents.length)
    (original : LocalRequest (cache.parents[index.val]'index.isLt) localCount target) (positive : 0 < target) :
    let localTarget := target / 8
    let next := localTarget + localTarget
    let localPositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 8)
    let nextPositive := Arithmetic.add_pos_of_pos_of_nonneg_direct localPositive localPositive.le
    let proper := Riemann.Integration.PreparedDyadicRefinements.AllParentsProper.get cache.proper index
    HEq (original.request.retarget next nextPositive proper original.request.index).model original.request.model ∧
      (original.request.retarget next nextPositive proper original.request.index).block = original.request.block := by
  dsimp only
  have localPositive : 0 < target / 8 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have nextPositive := Arithmetic.add_pos_of_pos_of_nonneg_direct localPositive localPositive.le
  have weaker := Arithmetic.add_le_add_right_direct localPositive.le (target / 8)
  rewrite [Fraction.Field.zero_add] at weaker
  have proper := Riemann.Integration.PreparedDyadicRefinements.AllParentsProper.get cache.proper index
  exact ⟨original.request.retarget_model_heq_of_le _ nextPositive proper original.request.index weaker (Nat.le_refl _),
    original.request.retarget_block_of_le _ nextPositive proper original.request.index weaker (Nat.le_refl _)⟩

/-- A computed weaker target reuses the actual original aggregate's complete data and scalar caches.

The same retained parent cache supplies properness. Positivity and all
sufficient payments follow from the original request and its stored target,
without a successful acquisition or cache-reuse premise.
-/
private def primitiveSpatialWeakerRetargeted {localCount : Nat} {target : Fraction.Rational}
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (original : PrimitiveSumRequest cache.parents localCount target) :
    let next := target + target
    let nextPositive := Arithmetic.add_pos_of_pos_of_nonneg_direct
      original.target_positive original.target_positive.le
    {actual : PrimitiveSumRequest cache.parents localCount next //
      actual = original.retarget next nextPositive cache.proper ∧
      actual.blocks = original.blocks ∧ actual.increments = original.increments ∧
      actual.primitiveSum = original.primitiveSum ∧ actual.integralSample = original.integralSample ∧
      Norm.Basic.normSq (actual.primitiveSum - actual.integralSample) < next} := by
  dsimp only
  have positive := Arithmetic.add_pos_of_pos_of_nonneg_direct
    original.target_positive original.target_positive.le
  have weaker := Arithmetic.add_le_add_right_direct original.target_positive.le target
  rewrite [Fraction.Field.zero_add] at weaker
  let actual := original.retarget (target + target) positive cache.proper
  have reused := original.retarget_caches_of_le (target + target) positive cache.proper 0 weaker
    (fun _ => Nat.zero_le _)
  exact ⟨actual, rfl, reused.1, reused.2.1, reused.2.2.1, reused.2.2.2,
    (Norm.Basic.normSq_eq_canonical _).trans_lt actual.accurate⟩

/-- Tightening a genuinely relaxed actual aggregate reuses those same complete caches when their actual payments hold.

The relaxed target is strictly larger. Its original cached model, Taylor
and preparation payments still pay the original smaller target internally;
the second retarget therefore retains the SAME blocks, increments, sum and
integral sample without new observations or a caller-supplied success test.
-/
private def primitiveSpatialTighterRetargeted {localCount : Nat} {target : Fraction.Rational}
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (original : PrimitiveSumRequest cache.parents localCount target) :
    let next := target + target
    let nextPositive := Arithmetic.add_pos_of_pos_of_nonneg_direct
      original.target_positive original.target_positive.le
    let relaxed := original.retarget next nextPositive cache.proper
    {actual : PrimitiveSumRequest cache.parents localCount target //
      target < next ∧ actual = relaxed.retarget target original.target_positive cache.proper ∧
      actual.blocks = original.blocks ∧ actual.increments = original.increments ∧
      actual.primitiveSum = original.primitiveSum ∧ actual.integralSample = original.integralSample ∧
      Norm.Basic.normSq (actual.primitiveSum - actual.integralSample) < target} := by
  dsimp only
  have positive := Arithmetic.add_pos_of_pos_of_nonneg_direct
    original.target_positive original.target_positive.le
  have strict := Arithmetic.add_lt_add_right_direct original.target_positive target
  rewrite [Fraction.Field.zero_add] at strict
  let next := target + target
  have paid := original.requests.cachePays_of_le (Budget.Aggregate.perTerm next cache.parents.length) 0
    (original.localTarget_eq.trans_le (Budget.Aggregate.perTerm_mono strict.le cache.parents.length))
    (fun _ => Nat.zero_le _)
  have originalPaid := original.requests.cachePays_of_le (Budget.Aggregate.perTerm target cache.parents.length) 0
    original.localTarget_eq.le (fun _ => Nat.zero_le _)
  let relaxed := original.retarget next positive cache.proper
  have retainedPaid := original.cachePays_retarget next positive cache.proper 0 paid _ 0 originalPaid
  let actual := relaxed.retarget target original.target_positive cache.proper
  have first := original.retarget_caches_of_cachePays next positive cache.proper 0 paid
  have second := relaxed.retarget_caches_of_cachePays target original.target_positive cache.proper 0 retainedPaid
  exact ⟨actual, strict, rfl, second.1.trans first.1, second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1, second.2.2.2.trans first.2.2.2,
    (Norm.Basic.normSq_eq_canonical _).trans_lt actual.accurate⟩

/-- The actual parent-integral producer consumes a supplied aggregate retargeted to a computed accuracy share.

The exact retargeted request and its ordered original bank are passed to the
public producer. No new initial request bank is acquired. Its real paid
quarter target and separate mismatch quarter give the requested finite
spatial-sample bound; whole scalar-program agreement is still separate.
-/
private def primitiveSpatialSuppliedIntegralRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    let sharePositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
    Σ paid : {actual : PrimitiveSumRequest cache.parents localCount (accuracy / 4) //
      actual = original.retarget (accuracy / 4) sharePositive cache.proper},
    {value : PrimitiveTarget.ParentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
        frame covered cache paid.val.requestsAtTarget sharePositive (accuracy / 4) sharePositive //
      value = PrimitiveTarget.parentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
        frame covered cache points paid.val.requestsAtTarget sharePositive (accuracy / 4) sharePositive
          (some ⟨paid.val, rfl⟩) ∧
      Norm.Basic.normSq (value.boundary - value.request.integralSample) < accuracy} := by
  dsimp only
  have sharePositive : 0 < accuracy / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let paid := original.retarget (accuracy / 4) sharePositive cache.proper
  let value := PrimitiveTarget.parentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
    frame covered cache points paid.requestsAtTarget sharePositive (accuracy / 4) sharePositive (some ⟨paid, rfl⟩)
  have attained := value.accurate
  have combined : 2 * (accuracy / 4 + accuracy / 4) = accuracy := by
    rewrite [show 2 * (accuracy / 4 + accuracy / 4) = (accuracy / 4) * 4 by ring0]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  exact ⟨⟨paid, rfl⟩, ⟨value, rfl, (Norm.Basic.normSq_eq_canonical _).trans_lt (attained.trans_eq combined)⟩⟩

section CoefficientPayments

open Purelib.Data.Vector (DependentVector)

/-- The exact original coefficient request and strict payment over supplied actual primitive caches.

Naming the same dependent subtype at its actual model, powers and scalar
cell prevents backward inference through an entire selected source Request.
The alias adds no record, transport or numerical construction.
-/
private def PaidSourceCoefficientAt {count : Nat}
    (patch : ContinuedNeighborhood (Paths.polynomial (parameter site)) count)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point patch
      (coordinate site (parameter site) 2 quarter (by decide +kernel) span.lower))
    (channel : Fin 6) (scalarAccuracy : AccuracyRequest)
    (cell : Cells.Model (channelData site channel)
      (span := span) scalarReading scalarAccuracy)
    (stage : Nat) (inverse : InverseRootPolynomial.Model (Paths.polynomial (parameter site)) patch.base.box)
    (powers : OddPowers inverse.value) (sameModel : inverse = patch.base.refine stage)
    (common : PrimitiveModel patch stage
      ((Specification.Table.forms (parameter site) channel).numerator.scale
        (Specification.Table.forms (parameter site) channel).scale)
      (Specification.Table.forms (parameter site) channel).denominatorPairs)
    (target : Fraction.Rational) : Type 1 :=
  {actual : Model.CoefficientRequest
    (site := site) (parameter := parameter site) (quarter := quarter) (positive := by decide +kernel)
    (actual := (spatial site quarter).leg.actual) (span := span) (inside := scalarInside)
    (radicand := Paths.polynomial (parameter site))
    (differential := Specification.Table.forms (parameter site) channel)
    (polynomial := Paths.polynomial (parameter site)) (count := count) (patch := patch) (sample := sample)
    (stage := stage) (inverse := inverse) (powers := powers)
    (numerator := (Specification.Table.forms (parameter site) channel).numerator.scale
      (Specification.Table.forms (parameter site) channel).scale)
    (pairCount := (Specification.Table.forms (parameter site) channel).denominatorPairs)
    (data := channelData site channel) (source := scalarReading) (accuracy := scalarAccuracy)
    cell sameModel common // cell.primitiveResidual common.coefficient < target}

/-- The exact original selected scales, source Request, scalar cell, primitive and paid coefficient request.

The Sigma view retains the complete factory results, actual stage/floor
indices and unchanged nominal parents for one selected form. It introduces
no numerical request family or six-form container.
-/
private def PaidSourceCoefficient
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point endpoints.1.val.patch
      (coordinate site (parameter site) 2 quarter (by decide +kernel) span.lower))
    (channel : Fin 6) (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :=
  Σ selected : {actual :
      Geometric.Search.Selection
        (PrimitiveTarget.modelErrorScale (primitiveBounds site quarter) endpoints.1.val (channelData site channel)
          (Specification.Table.forms (parameter site) channel).denominatorPairs) modelFloor (target / 2) ×
      Geometric.Search.Selection
        (PrimitiveTarget.samplingErrorScale (primitiveBounds site quarter) endpoints.1.val
          (channelData site channel) accuracy (Specification.Table.forms (parameter site) channel).denominatorPairs)
        scalarFloor (target / 2) //
      actual = PrimitiveTarget.coefficientSelections (primitiveBounds site quarter) endpoints.1.val
        (channelData site channel) accuracy modelFloor scalarFloor target positive
        (Specification.Table.forms (parameter site) channel).denominatorPairs},
  Σ requested : {actual : Source.Request cache selected.val.1.stage sourceAccuracy.tolerance //
      actual = cache.request selected.val.1.stage sourceAccuracy.tolerance sourceAccuracy.positive},
  let scalarAccuracy : AccuracyRequest :=
    ⟨Geometric.Basic.quarterRadius accuracy.tolerance selected.val.2.stage,
      Geometric.Basic.quarterRadius_pos accuracy.positive selected.val.2.stage⟩
  Σ cell : {actual : Cells.Model (channelData site channel)
      (span := span) scalarReading scalarAccuracy //
      actual = Model.build (span := span) (inside := scalarInside)
        (actual := (spatial site quarter).leg.actual)
        (channelData site channel) scalarReading (spatial site quarter).leg.regular scalarAccuracy},
  Σ common : {actual : PrimitiveModel endpoints.1.val.patch requested.val.selection.stage
      ((Specification.Table.forms (parameter site) channel).numerator.scale
        (Specification.Table.forms (parameter site) channel).scale)
      (Specification.Table.forms (parameter site) channel).denominatorPairs //
      actual = requested.val.primitive channel},
    PaidSourceCoefficientAt site quarter endpoints.1.val.patch scalarReading sample channel scalarAccuracy cell.val
      requested.val.selection.stage requested.val.model requested.val.models.powers requested.val.model_eq common.val
      target

/-- Compute one actual finite-paid coefficient request from supplied original Reading and Point caches.

Both geometric specializations derive the signed link and model domain from
their retained original owners. This shared pipeline selects both accuracies,
consumes one original Source Request and its actual primitive, and proves the
strict coefficient payment from those actual observations and floors.
-/
private def paidCoefficient
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point endpoints.1.val.patch
      (coordinate site (parameter site) 2 quarter (by decide +kernel) span.lower))
    (related : NamedEquivalent scalarReading.lift.value.name sample.certificate.value.name)
    (contained : endpoints.1.val.patch.box.Contains
      (coordinate site (parameter site) 2 quarter (by decide +kernel) span.lower))
    (channel : Fin 6) (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    PaidSourceCoefficient site quarter endpoints cache scalarReading sample channel modelFloor scalarFloor target
      positive sourceAccuracy := by
  let selected := PrimitiveTarget.coefficientSelections (primitiveBounds site quarter) endpoints.1.val
    (channelData site channel) accuracy modelFloor scalarFloor target positive
    (Specification.Table.forms (parameter site) channel).denominatorPairs
  let requested := cache.request selected.1.stage sourceAccuracy.tolerance sourceAccuracy.positive
  let scalarAccuracy : AccuracyRequest :=
    ⟨Geometric.Basic.quarterRadius accuracy.tolerance selected.2.stage,
      Geometric.Basic.quarterRadius_pos accuracy.positive selected.2.stage⟩
  let cell : Cells.Model (channelData site channel)
      (span := span) scalarReading scalarAccuracy :=
    Model.build (span := span) (inside := scalarInside)
        (actual := (spatial site quarter).leg.actual)
        (channelData site channel) scalarReading (spatial site quarter).leg.regular scalarAccuracy
  let common := requested.primitive channel
  let coefficient := Model.coefficientRequest
    (site := site) (parameter := parameter site) (quarter := quarter) (positive := by decide +kernel)
    (actual := (spatial site quarter).leg.actual) (span := span) (inside := scalarInside)
    (radicand := Paths.polynomial (parameter site))
    (differential := Specification.Table.forms (parameter site) channel)
    (polynomial := Paths.polynomial (parameter site)) (count := count) (patch := endpoints.1.val.patch)
    (sample := sample) (stage := requested.selection.stage)
    (inverse := requested.model) (powers := requested.models.powers)
    (numerator := (Specification.Table.forms (parameter site) channel).numerator.scale
      (Specification.Table.forms (parameter site) channel).scale)
    (pairCount := (Specification.Table.forms (parameter site) channel).denominatorPairs)
    (data := channelData site channel) (source := scalarReading) (accuracy := scalarAccuracy)
    cell related rfl (fun location => by rewrite [Dense.Basic.DensePolynomial.eval_scale]; rfl)
    requested.model_eq common contained
  have attained : cell.primitiveResidual common.coefficient < target :=
    PrimitiveTarget.coefficient_error_lt (primitiveBounds site quarter) endpoints.1.val cell requested.model_eq
      common coefficient accuracy selected.2.stage modelFloor scalarFloor target positive rfl
      requested.selection.lower (Nat.le_refl _)
  exact ⟨⟨selected, rfl⟩, ⟨requested, rfl⟩, ⟨cell, rfl⟩, ⟨common, rfl⟩, ⟨coefficient, attained⟩⟩

/-- The genuine source specialization consumes its identical retained original Point and actual move domain. -/
private def paidSourceCoefficient
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch) (ordered : first ≤ last) (channel : Fin 6)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    PaidSourceCoefficient site quarter endpoints cache (span := ⟨first, last, ordered⟩) firstReading endpoints.2.1
      channel modelFloor scalarFloor target positive sourceAccuracy :=
  paidCoefficient site quarter endpoints cache (span := ⟨first, last, ordered⟩) firstReading endpoints.2.1
    endpoints.2.2 (PrimitiveTarget.source_inside (primitiveBounds site quarter) endpoints.1.val)
    channel modelFloor scalarFloor target positive sourceAccuracy

/-- The actual retained strict-interior Point pays any original selected form at its computed finite model/root stages.

The actual CurvePoint supplies the signed channel relation and the original
move derives the common-model domain. The same Point, Reading, Source
Request, model, Shared powers and primitive remain the original inputs and
caches; no final inequality or successful comparison is a caller premise.
-/
private def paidInteriorCoefficient
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (interior : first < span.lower ∧ span.lower < last)
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      span.lower scalarReading interior)
    (channel : Fin 6) (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    PaidSourceCoefficient site quarter endpoints cache scalarReading point.sample channel modelFloor scalarFloor
      target positive sourceAccuracy :=
  paidCoefficient site quarter endpoints cache scalarReading point.sample point.readingEquivalent
    (PrimitiveTarget.curve_inside (primitiveBounds site quarter) endpoints.1.val span.lower
      ⟨interior.1.le, interior.2.le⟩) channel modelFloor scalarFloor target positive sourceAccuracy

/-- Construct all six original source coefficients from the same endpoint Point and complete retained source cache.

The production procedure computes its finite selection bank before one
common source/model/root acquisition. The original channelData family
retains the exact six indexed specification forms and actual numerical
owners; the result stores paid requests, not an entry-producing function.
-/
private def paidSourceCoefficients
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch) (ordered : first ≤ last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    let forms := DependentVector.ofFn (channelData site)
    PrimitiveTarget.CoefficientRequests (span := ⟨first, last, ordered⟩)
      (primitiveBounds site quarter) endpoints.1.val firstReading endpoints.2.1 cache forms
      accuracy modelFloor scalarFloor target positive sourceAccuracy :=
  let forms := DependentVector.ofFn (channelData site)
  PrimitiveTarget.sourceCoefficientRequests (primitiveBounds site quarter) endpoints.1.val endpoints.2
    last ordered cache forms accuracy modelFloor scalarFloor target positive sourceAccuracy

/-- Construct all six original interior coefficients from one supplied actual CurvePoint and its original Reading.

The production method forwards that same Point and retained signed link.
Its actual move derives the model domain; all six selected bounds are paid
by the same final Source Request, scalar accuracy and stored root triple.
-/
private def paidInteriorCoefficients
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (interior : first < span.lower ∧ span.lower < last)
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      span.lower scalarReading interior)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    let forms := DependentVector.ofFn (channelData site)
    PrimitiveTarget.CoefficientRequests (primitiveBounds site quarter) endpoints.1.val scalarReading point.sample
      cache forms accuracy modelFloor scalarFloor target positive sourceAccuracy :=
  let forms := DependentVector.ofFn (channelData site)
  PrimitiveTarget.CurvePoint.coefficientRequests (primitiveBounds site quarter) endpoints.1.val point
    cache forms accuracy modelFloor scalarFloor target positive sourceAccuracy

/-- Every actual stored source-channel request pays its requested coefficient target at the retained common stage. -/
example {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch) (ordered : first ≤ last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (channel : Fin 6) :
    let retained := paidSourceCoefficients site quarter endpoints cache ordered modelFloor scalarFloor
      target positive sourceAccuracy
    let entry := retained.2.2.2.2.2.get channel
    entry.1.val.primitiveResidual (retained.2.2.2.1.val.get channel).coefficient < target := by
  dsimp only
  exact ((paidSourceCoefficients site quarter endpoints cache ordered modelFloor scalarFloor
    target positive sourceAccuracy).2.2.2.2.2.get channel).2.property

/-- Every actual stored interior-channel request pays the same target on its supplied original Point and Reading. -/
example {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Radial.Transport.Reading (spatial site quarter).leg.actual span.lower scalarInside)
    (interior : first < span.lower ∧ span.lower < last)
    (point : PrimitiveTarget.CurvePoint (primitiveBounds site quarter) endpoints.1.val
      span.lower scalarReading interior)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (channel : Fin 6) :
    let retained := paidInteriorCoefficients site quarter endpoints cache scalarReading interior point
      modelFloor scalarFloor target positive sourceAccuracy
    let entry := retained.2.2.2.2.2.get channel
    entry.1.val.primitiveResidual (retained.2.2.2.1.val.get channel).coefficient < target := by
  dsimp only
  exact ((paidInteriorCoefficients site quarter endpoints cache scalarReading interior point
    modelFloor scalarFloor target positive sourceAccuracy).2.2.2.2.2.get channel).2.property

/-- The complete genuine-source operation is the same retained pipeline with its actual original source inputs. -/
example {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch) (ordered : first ≤ last) (channel : Fin 6)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    paidSourceCoefficient site quarter endpoints cache ordered channel modelFloor scalarFloor target positive
      sourceAccuracy =
    paidCoefficient site quarter endpoints cache (span := ⟨first, last, ordered⟩) firstReading endpoints.2.1
      endpoints.2.2 (PrimitiveTarget.source_inside (primitiveBounds site quarter) endpoints.1.val)
      channel modelFloor scalarFloor target positive sourceAccuracy := rfl

/-- The whole source result retains the former complete five-cache factory construction after shared factoring. -/
example {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count)
    (cache : Source.Cache endpoints.1.val.patch) (ordered : first ≤ last) (channel : Fin 6)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    paidSourceCoefficient site quarter endpoints cache ordered channel modelFloor scalarFloor target positive
      sourceAccuracy =
    (show PaidSourceCoefficient site quarter endpoints cache (span := ⟨first, last, ordered⟩) firstReading endpoints.2.1
      channel modelFloor scalarFloor target positive sourceAccuracy from by
      let selected := PrimitiveTarget.coefficientSelections (primitiveBounds site quarter) endpoints.1.val
        (channelData site channel) accuracy modelFloor scalarFloor target positive
        (Specification.Table.forms (parameter site) channel).denominatorPairs
      let requested := cache.request selected.1.stage sourceAccuracy.tolerance sourceAccuracy.positive
      let scalarAccuracy : AccuracyRequest :=
        ⟨Geometric.Basic.quarterRadius accuracy.tolerance selected.2.stage,
          Geometric.Basic.quarterRadius_pos accuracy.positive selected.2.stage⟩
      let cell : Cells.Model (channelData site channel)
          (span := ⟨first, last, ordered⟩) firstReading scalarAccuracy :=
        Model.build (span := ⟨first, last, ordered⟩) (inside := firstInside)
            (actual := (spatial site quarter).leg.actual)
            (channelData site channel) firstReading (spatial site quarter).leg.regular scalarAccuracy
      let common := requested.primitive channel
      let coefficient := Model.coefficientRequest
        (site := site) (parameter := parameter site) (quarter := quarter) (positive := by decide +kernel)
        (actual := (spatial site quarter).leg.actual) (span := ⟨first, last, ordered⟩) (inside := firstInside)
        (radicand := Paths.polynomial (parameter site))
        (differential := Specification.Table.forms (parameter site) channel)
        (polynomial := Paths.polynomial (parameter site)) (count := count) (patch := endpoints.1.val.patch)
        (sample := endpoints.2.1) (stage := requested.selection.stage)
        (inverse := requested.model) (powers := requested.models.powers)
        (numerator := (Specification.Table.forms (parameter site) channel).numerator.scale
          (Specification.Table.forms (parameter site) channel).scale)
        (pairCount := (Specification.Table.forms (parameter site) channel).denominatorPairs)
        (data := channelData site channel) (source := firstReading) (accuracy := scalarAccuracy)
        cell endpoints.2.2 rfl (fun location => by rewrite [Dense.Basic.DensePolynomial.eval_scale]; rfl)
        requested.model_eq common (PrimitiveTarget.source_inside (primitiveBounds site quarter) endpoints.1.val)
      have attained : cell.primitiveResidual common.coefficient < target :=
        PrimitiveTarget.coefficient_error_lt (primitiveBounds site quarter) endpoints.1.val cell requested.model_eq
          common coefficient accuracy selected.2.stage modelFloor scalarFloor target positive rfl
          requested.selection.lower (Nat.le_refl _)
      exact ⟨⟨selected, rfl⟩, ⟨requested, rfl⟩, ⟨cell, rfl⟩, ⟨common, rfl⟩, ⟨coefficient, attained⟩⟩) := rfl

/-- The omitted pair index still has the complete original ordered two-search result on every retained parent cache. -/
example {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    let selected := PrimitiveTarget.coefficientSelections (primitiveBounds site quarter) endpoints.1.val
      (valueData site) accuracy modelFloor scalarFloor target positive
    selected =
      (let weight := Radial.Differential.Bounds.tangentNumeratorBound (valueData site)
       let inverseFloor := (Model.comparisonFloor firstReading endpoints.1.val.patch)⁻¹
       let modelScale := 2 * weight * endpoints.1.val.patch.inverseErrorScale
       let sampleScale := 2 * weight * (inverseFloor * inverseFloor) *
         (16 * (((25 / 4) * (valueData site).gapNorm) + 1) + 4) * accuracy.tolerance
       let halfTarget := target / 2
       have halfPositive : 0 < halfTarget := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       (Geometric.Search.Selection.build modelScale selected.1.scaleNonnegative modelFloor halfTarget halfPositive,
         Geometric.Search.Selection.build sampleScale selected.2.scaleNonnegative scalarFloor halfTarget
           halfPositive)) :=
  PrimitiveTarget.coefficientSelections_zero_eq (primitiveBounds site quarter) endpoints.1.val (valueData site)
    accuracy modelFloor scalarFloor target positive _ _

end CoefficientPayments

section ScalarModelRequest

open Parallel.OwnerMove.PrimitiveTarget (ScalarModels ParentIntegralRequest)

/-- The actual retained aggregate, finite selections, scalar precision and original parent-integral result.

This exact Sigma keeps the supplied original caches and whole factory
identities. Its final subtype relates the same stored scalar model to the
actual spatial aggregate; no parallel request or primitive record is added.
-/
private def PrimitiveSpatialScalarModelRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (requested : Fraction.Rational) (positive : 0 < requested) : Type 2 :=
  let sharePositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
  Σ paid : {actual : PrimitiveSumRequest cache.parents localCount (requested / 4) //
      actual = original.retarget (requested / 4) sharePositive cache.proper},
  Σ selections : ParentIntegralRequest.Selections (primitiveBounds site quarter) endpoints.1.val
      frame covered cache paid.val.requestsAtTarget (requested / 4) sharePositive,
  Σ scalar : ScalarModels.Precision (primitiveBounds site quarter) endpoints.1.val initial
      selections.val.stage 0 (requested / 4) sharePositive,
  Σ model : ParentIntegralRequest.Model (primitiveBounds site quarter) endpoints.1.val
      frame covered cache paid.val.requestsAtTarget (requested / 4) sharePositive,
    {value : ParentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
        frame covered cache paid.val.requestsAtTarget sharePositive (requested / 4) sharePositive (some model) //
      value = PrimitiveTarget.parentIntegralRequest (primitiveBounds site quarter) endpoints.1.val frame covered cache
        points paid.val.requestsAtTarget sharePositive (requested / 4) sharePositive
        (some ⟨paid.val, rfl⟩) selections (some model) ∧
      HEq value.model (ScalarModels.Precision.models (primitiveBounds site quarter) scalar).common ∧
      Norm.Basic.normSq
        ((ScalarModels.Precision.models (primitiveBounds site quarter) scalar).common.primitive.value.eval
            (coordinate site (parameter site) 2 quarter (by decide +kernel) last) -
          (ScalarModels.Precision.models (primitiveBounds site quarter) scalar).common.primitive.value.eval
            (coordinate site (parameter site) 2 quarter (by decide +kernel) first) - value.request.integralSample) <
        requested}

/-- The same actual scalar precision model pays every supplied spatial parent at a computed later stage.

One retained aggregate is retargeted to the requested quarter allowance.
Its actual pair-selection bank supplies the scalar model floor, and the
original scalar Precision constructs that model once. The original parent
producer consumes the same bank and whole model, with both finite errors
paid internally. This value-form comparison is not whole-Blocks or six-form
programme equivalence.
-/
private def primitiveSpatialScalarModelRequested
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (endpoints : PrimitiveMoveEndpoints site quarter move count) (frame : Paths.Frame (parameter site))
    (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveSpatialPoints site quarter endpoints frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (requested : Fraction.Rational) (positive : 0 < requested) :
    PrimitiveSpatialScalarModelRequested site quarter endpoints frame covered cache points original initial
      requested positive := by
  dsimp only [PrimitiveSpatialScalarModelRequested]
  have sharePositive : 0 < requested / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let paid := original.retarget (requested / 4) sharePositive cache.proper
  let selections : ParentIntegralRequest.Selections (primitiveBounds site quarter) endpoints.1.val
      frame covered cache paid.requestsAtTarget (requested / 4) sharePositive :=
    ⟨PrimitiveTarget.parentPairSelections (primitiveBounds site quarter) endpoints.1.val frame covered cache
      paid.requestsAtTarget (Budget.Aggregate.perTerm (requested / 4) cache.parents.length)
      (Budget.Aggregate.perTerm_positive sharePositive cache.parents.length), rfl⟩
  let scalar := ScalarModels.precision (primitiveBounds site quarter) endpoints.1.val
    initial selections.val.stage 0 (requested / 4) sharePositive
  let models := ScalarModels.Precision.models (primitiveBounds site quarter) scalar
  have commonEq : models.common = PrimitiveModel.ofIndex endpoints.1.val.patch scalar.modelStage
      (differentialNumerator (⟨0⟩ : Differential 1)) := by
    obtain ⟨⟨inverse, inverseEq⟩, powers, common⟩ := models
    cases inverseEq
    exact ScalarModels.common_eq (primitiveBounds site quarter)
      (numerator := (Specification.valueSpecification (parameter site) 0).numerator)
      (pairCount := 0) (supplied := none)
      ⟨⟨_, rfl⟩, powers, common⟩
  let retainedModel : ParentIntegralRequest.Model (primitiveBounds site quarter) endpoints.1.val
      frame covered cache paid.requestsAtTarget (requested / 4) sharePositive :=
    ⟨scalar.modelStage, ⟨models.common, commonEq,
      scalar.coefficients.1.lower.trans
        (ScalarModels.Precision.modelStage_ge (primitiveBounds site quarter) scalar)⟩⟩
  let parent := PrimitiveTarget.parentIntegralRequest (primitiveBounds site quarter) endpoints.1.val frame covered cache
    points paid.requestsAtTarget sharePositive (requested / 4) sharePositive (some ⟨paid, rfl⟩)
    selections (some retainedModel)
  have sameModel := PrimitiveTarget.parentIntegralRequest_model_retained (primitiveBounds site quarter)
    endpoints.1.val frame covered cache points paid.requestsAtTarget sharePositive (requested / 4) sharePositive
    (some ⟨paid, rfl⟩) selections retainedModel
  have boundary := PrimitiveTarget.parentIntegralRequest_boundary_retained (primitiveBounds site quarter)
    endpoints.1.val frame covered cache points paid.requestsAtTarget sharePositive (requested / 4) sharePositive
    (some ⟨paid, rfl⟩) selections retainedModel
  have attained := ParentIntegralRequest.accurate (primitiveBounds site quarter) parent
  rewrite [boundary] at attained
  have combined : 2 * (requested / 4 + requested / 4) = requested := by
    rewrite [show 2 * (requested / 4 + requested / 4) = (requested / 4) * 4 by ring0]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  let result : {value : ParentIntegralRequest (primitiveBounds site quarter) endpoints.1.val
      frame covered cache paid.requestsAtTarget sharePositive (requested / 4) sharePositive (some retainedModel) //
    value = parent ∧ HEq value.model models.common ∧
    Norm.Basic.normSq (models.common.primitive.value.eval
        (coordinate site (parameter site) 2 quarter (by decide +kernel) last) -
      models.common.primitive.value.eval
        (coordinate site (parameter site) 2 quarter (by decide +kernel) first) - value.request.integralSample) <
      requested} :=
    ⟨parent, rfl, sameModel, (Norm.Basic.normSq_eq_canonical _).trans_lt (attained.trans_eq combined)⟩
  exact ⟨⟨paid, rfl⟩, selections, scalar, retainedModel, result⟩

/-- Read the exact existing endpoint view from the original retained target and source Point. -/
private def anchoredEndpoints
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    (retained : PrimitiveTarget.Anchored (primitiveBounds site quarter) move count) :
    PrimitiveMoveEndpoints site quarter move count :=
  ⟨⟨retained.target, by unfold primitiveMovePoint; exact retained.target_eq⟩, retained.sourcePoint⟩

/-- The original scalar cell requests and their paid discrepancy from the supplied spatial sample.

Both samples use the same retained common primitive. The actual layer is
computed at the stored Taylor stage; all model and spatial request caches
come from the original comparison value.
-/
private def ScalarSpatialLayerRequests
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (retained : PrimitiveTarget.Anchored (primitiveBounds site quarter) move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveTarget.ParentPoints (primitiveBounds site quarter) retained.target retained.sourcePoint
      frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (requested : Fraction.Rational) (positive : 0 < requested)
    (compared : PrimitiveSpatialScalarModelRequested site quarter (anchoredEndpoints site quarter retained)
      frame covered cache points original initial (requested / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))) : Type 1 :=
  let scalar := compared.2.2.1
  let models := ScalarModels.Precision.models (primitiveBounds site quarter) scalar
  Σ layer : {actual : Refinement.Layer initial scalar.taylor.stage //
      actual = initial.layerAt scalar.taylor.stage},
    {_requests : ScalarModels.LayerRequests (primitiveBounds site quarter) retained
        (PrimitiveTarget.curveSource (primitiveBounds site quarter) retained.target) models layer.val
        (ScalarModels.coefficientTarget initial ((requested / 4) / 4)) //
      Norm.Basic.normSq (layer.val.model.integralSample - compared.2.2.2.2.val.request.integralSample) < requested}

/-- Pay the actual scalar layer against the independently retained spatial aggregate through their same primitive.

The original finite scalar requests are constructed here at the stored
Taylor stage. Quarter allowances and the two cached boundary estimates
supply the final squared-error bound without a comparison hypothesis.
-/
private def scalarSpatialLayerRequests
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (retained : PrimitiveTarget.Anchored (primitiveBounds site quarter) move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveTarget.ParentPoints (primitiveBounds site quarter) retained.target retained.sourcePoint
      frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (requested : Fraction.Rational) (positive : 0 < requested)
    (compared : PrimitiveSpatialScalarModelRequested site quarter (anchoredEndpoints site quarter retained)
      frame covered cache points original initial (requested / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)))
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last) :
    ScalarSpatialLayerRequests site quarter retained frame covered cache points original initial
      requested positive compared := by
  dsimp only [ScalarSpatialLayerRequests]
  let scalar := compared.2.2.1
  let models := ScalarModels.Precision.models (primitiveBounds site quarter) scalar
  let layer := initial.layerAt scalar.taylor.stage
  let prepared := PrimitiveTarget.curveSource (primitiveBounds site quarter) retained.target
  let requests := ScalarModels.Precision.requests (primitiveBounds site quarter) retained scalar prepared
    ⟨scalar.taylor.stage, Nat.le_refl _⟩ span_eq proper layer (initial.layerAt_spans scalar.taylor.stage)
    rfl (fun _ => (Basic.one_mul _).symm)
  let boundary := models.common.primitive.value.eval
      (coordinate site (parameter site) 2 quarter (by decide +kernel) last) -
    models.common.primitive.value.eval
      (coordinate site (parameter site) 2 quarter (by decide +kernel) first)
  have scalarBound := ScalarModels.Precision.accurate (primitiveBounds site quarter) retained scalar
    ⟨scalar.taylor.stage, Nat.le_refl _⟩ span_eq layer (initial.layerAt_spans scalar.taylor.stage) requests
  have spatialBound := compared.2.2.2.2.property.2.2
  have sharePositive : 0 < requested / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have firstBound : Norm.Basic.normSq (layer.model.integralSample - boundary) < requested / 4 :=
    (Norm.Bounds.normSq_sub_symm _ _).trans_lt (scalarBound.trans_le
      (Fraction.Order.Field.divide_le_self sharePositive.le
        (by decide +kernel : (1 : Fraction.Rational) ≤ 4)))
  exact ⟨⟨layer, rfl⟩, ⟨requests, Norm.Bounds.normSq_sub_lt_of_quarter_bounds firstBound spatialBound⟩⟩

/-- The same retained spatial comparison, actual scalar layer and requests produced from one common primitive.

The first subtype records the whole original comparison factory. The
second component stores the actual layer, its whole refinement identity
and the independently paid discrepancy between both retained samples.
-/
private def ScalarSpatialRequest
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (retained : PrimitiveTarget.Anchored (primitiveBounds site quarter) move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveTarget.ParentPoints (primitiveBounds site quarter) retained.target retained.sourcePoint
      frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (requested : Fraction.Rational) (positive : 0 < requested) : Type 2 :=
  let sharePositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
  Σ compared : {actual : PrimitiveSpatialScalarModelRequested site quarter
      (anchoredEndpoints site quarter retained) frame covered cache points original initial
      (requested / 4) sharePositive //
    actual = primitiveSpatialScalarModelRequested site quarter (anchoredEndpoints site quarter retained)
      frame covered cache points original initial (requested / 4) sharePositive},
    ScalarSpatialLayerRequests site quarter retained frame covered cache points original initial
      requested positive compared.val

/-- Construct both actual samples and their common-primitive comparison from the original supplied spatial request.

One retained scalar precision pays both constructions. The spatial
aggregate, actual scalar layer and scalar requests remain cached in the
returned original views, with the final squared-error request proved here.
-/
private def scalarSpatialRequest
    {move : Parallel.OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}
    {localCount : Nat} {target : Fraction.Rational}
    (retained : PrimitiveTarget.Anchored (primitiveBounds site quarter) move count)
    (frame : Paths.Frame (parameter site)) (covered : Parallel.Covered geometry source)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0)
    (points : PrimitiveTarget.ParentPoints (primitiveBounds site quarter) retained.target retained.sourcePoint
      frame covered cache)
    (original : PrimitiveSumRequest cache.parents localCount target)
    (initial : Refinement.Piece (valueData site) (spatial site quarter).leg.actual accuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (requested : Fraction.Rational) (positive : 0 < requested) :
    ScalarSpatialRequest site quarter retained frame covered cache points original initial requested positive := by
  let sharePositive := Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 4)
  let compared := primitiveSpatialScalarModelRequested site quarter (anchoredEndpoints site quarter retained)
    frame covered cache points original initial (requested / 4) sharePositive
  let scalar := scalarSpatialLayerRequests site quarter retained frame covered cache points original initial
    requested positive compared span_eq proper
  exact ⟨⟨compared, rfl⟩, scalar⟩

end ScalarModelRequest

end PrimitiveMove

end TestPurelib.Curves.Legendre.ParallelPrimitiveRequests
