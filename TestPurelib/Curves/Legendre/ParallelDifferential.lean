module

import Purelib.Tactic.Ring

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Jets
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
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial

/-! # Original regular circuit endpoints and their six cached differential channels

The fixture constructs both labelled regular circuits from intrinsic parameter
bounds. All endpoint channels consume the retained actual lifts and denominator
preparations. The two symbolic derivative levels use the identical geometric
endpoint and its original oriented tangent, including real-axis seams where
the scale-one waist ordinate vanishes.
-/

namespace TestPurelib.Curves.Legendre.ParallelDifferential

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

/-- The original regular parameter one eighth from each labelled collision. -/
@[expose] public def parameter (site : Fin 2) : Canonical := Degeneration.criticalValue site + (1 / 8 : Canonical)

/-- Both original fixture parameters are regular. -/
public theorem regular (site : Fin 2) : parameter site ≠ Degeneration.criticalValue site := by
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Both fixture parameters pay the intrinsic regular parallel radius. -/
private theorem radius (site : Fin 2) :
    Norm.Basic.normSq (parameter site - Degeneration.criticalValue site) ≤ (1 / 64 : Fraction.Rational) := by
  rcases Data.Fin.Two.finTwo_cases site with equal | equal
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- Construct the actual original regular parallel circuit and retain its four continuous seams. -/
public def circuit (site : Fin 2) : Radial.Transport.Circuit site (parameter site) :=
  Radial.Transport.Circuit.build site (parameter site) (regular site) (radius site)

attribute [local irreducible] circuit

/-- Materialize the six original differential channels on the identical retained source of each geometric leg. -/
private def source (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Jets.Bank ((circuit site).leg quarter).source.lift :=
  Jets.build ((circuit site).leg quarter).source.lift

/-- Materialize the same six forms on the independently retained actual finish of that geometric leg. -/
private def target (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Jets.Bank ((circuit site).leg quarter).target.lift :=
  Jets.build ((circuit site).leg quarter).target.lift

attribute [local irreducible] source target

/-- Every original source bank retains precisely the reciprocal of its same cached geometric cofactor channel. -/
theorem source_reciprocal (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (source site quarter).reciprocal = (Coherence.exact 1).div
      ((circuit site).leg quarter).source.lift.unitRoot.value
      ((circuit site).leg quarter).source.lift.unitRoot.apart :=
  (source site quarter).reciprocal_eq

/-- The ordinary value differential uses the retained source preparation and agrees with its cached channel. -/
def source_value (site : Fin 2) (quarter : UnitCircuitQuarter) (coordinate : Fin 2) :
    NamedEquivalent (((Specification.valueSpecification (parameter site) coordinate).value
      (Radial.point site (parameter site) 2 (Waist.direction quarter 0) (by decide +kernel)).base
      ((circuit site).leg quarter).sourcePrepared.denominator
      ((circuit site).leg quarter).sourcePrepared.apart).mul
        (Coherence.exact (Radial.Tangent.baseVelocity site (parameter site) 2 quarter 0))).name
      (Jets.value (source site quarter) coordinate).name :=
  Jets.value_agrees (source site quarter) coordinate
    (regular site) ((circuit site).leg quarter).sourcePrepared

/-- The original cubic-denominator first derivative uses the identical source point, sheet, preparation and tangent. -/
def source_first (site : Fin 2) (quarter : UnitCircuitQuarter) (coordinate : Fin 2) :
    NamedEquivalent (((Specification.firstDerivativeSpecification (parameter site) coordinate).value
      (Radial.point site (parameter site) 2 (Waist.direction quarter 0) (by decide +kernel)).base
      ((circuit site).leg quarter).sourcePrepared.denominator
      ((circuit site).leg quarter).sourcePrepared.apart).mul
        (Coherence.exact (Radial.Tangent.baseVelocity site (parameter site) 2 quarter 0))).name
      (Jets.first (source site quarter) coordinate).name :=
  Jets.first_agrees (source site quarter) coordinate
    (regular site) ((circuit site).leg quarter).sourcePrepared

/-- The original fifth-power second derivative uses the actual retained finish and its original cached preparation. -/
def target_second (site : Fin 2) (quarter : UnitCircuitQuarter) (coordinate : Fin 2) :
    NamedEquivalent (((Specification.secondDerivativeSpecification (parameter site) coordinate).value
      (Radial.point site (parameter site) 2 (Waist.direction quarter 1) (by decide +kernel)).base
      ((circuit site).leg quarter).targetPrepared.denominator
      ((circuit site).leg quarter).targetPrepared.apart).mul
        (Coherence.exact (Radial.Tangent.baseVelocity site (parameter site) 2 quarter 1))).name
      (Jets.second (target site quarter) coordinate).name :=
  Jets.second_agrees (target site quarter) coordinate
    (regular site) ((circuit site).leg quarter).targetPrepared

/-- The highest original derivative form has a strictly positive uniform parallel ordinate floor. -/
theorem second_floor_positive (site : Fin 2) (coordinate : Fin 2) :
    0 < Radial.Differential.Bounds.ordinateFloor
      (Waist.Differential.Bounds.Data.build site (parameter site)
        (Specification.secondDerivativeSpecification (parameter site) coordinate)) :=
  Radial.Differential.Bounds.ordinateFloor_positive _ (regular site)

/-- The retained initial scalar cells request this original positive cofactor-square tolerance. -/
public def accuracy : AccuracyRequest := ⟨1 / 4096, by decide +kernel⟩

/-- The original value budget keeps the exact first differential specification. -/
public def valueData (site : Fin 2) :=
  Waist.Differential.Bounds.Data.build site (parameter site) (Specification.valueSpecification (parameter site) 0)

/-- The original six-form budget keeps the identical materialized specification table entry. -/
public def channelData (site : Fin 2) (index : Fin 6) :=
  Waist.Differential.Bounds.Data.build site (parameter site) (Specification.Table.forms (parameter site) index)

attribute [local irreducible] valueData channelData

/-- Construct one paid original scalar quarter piece from the identical cached geometric leg source. -/
public def valuePiece (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Refinement.Piece (valueData site) ((circuit site).leg quarter).actual accuracy :=
  Refinement.Piece.ofSource (valueData site)
    ((circuit site).leg quarter).source (regular site) accuracy

/-- The retained original starting scalar piece is its complete original source factory result. -/
private theorem valuePiece_eq (site : Fin 2) (quarter : UnitCircuitQuarter) :
    valuePiece site quarter = Refinement.Piece.ofSource (valueData site)
      ((circuit site).leg quarter).source (regular site) accuracy := rfl

attribute [local irreducible] valuePiece

/-- The identical original source scalar piece retains the complete closed unit chart span. -/
private theorem valuePiece_span (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (valuePiece site quarter).span = ⟨0, 1, by decide +kernel⟩ :=
  (congrArg (fun piece : Refinement.Piece (valueData site)
    ((circuit site).leg quarter).actual accuracy => piece.span) (valuePiece_eq site quarter)).trans
      (Refinement.Piece.ofSource_span (valueData site)
        ((circuit site).leg quarter).source (regular site) accuracy)

/-- Read the identical root observation at an actual original scalar-layer occurrence with internally paid radius decay.

The layer is supplied as completed work. The bounded original ordinal reads
its same piece and source, and the actual cofactor observation supplies the
full-cubic product reading without rebuilding the layer or sampling a root.
-/
private def valueLayerRootReading (site : Fin 2) (quarter : UnitCircuitQuarter) (depth : Nat)
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (index : Fin layer.pieces.length) :
    let piece := layer.pieces[index.val]'index.isLt
    {actual : Approximation.Gaussian.Equivalence.Observation.Reading piece.source.lift.value //
      actual = piece.cell.rootReading ∧
      actual.value = piece.cell.sample.reading *
        (Radial.point site (parameter site) 2 (Waist.direction quarter piece.span.lower) (by decide +kernel)).ordinate ∧
      actual.radius ≤ Geometric.Basic.quarterRadius
        (((25 / 4) * Norm.Basic.normSq (Degeneration.halfGap site (parameter site))) * accuracy.tolerance) depth} := by
  dsimp only
  let piece := layer.pieces[index.val]'index.isLt
  exact ⟨piece.cell.rootReading, rfl, piece.cell.rootReading_value, layer.rootReading_radius_le piece⟩

/-- All six original scalar forms consume the same complete paid starting cofactor observation. -/
private def channelPiece (site : Fin 2) (quarter : UnitCircuitQuarter) (index : Fin 6) :
    Refinement.Piece (channelData site index) ((circuit site).leg quarter).actual accuracy :=
  (valuePiece site quarter).reweight (channelData site index)

/-- Every reweighted scalar channel retains the full original geometric source query of its actual leg. -/
theorem channel_source (site : Fin 2) (quarter : UnitCircuitQuarter) (index : Fin 6) :
    (channelPiece site quarter index).source = (valuePiece site quarter).source :=
  (valuePiece site quarter).reweight_source (channelData site index)

/-- All six starting scalar cells reuse the identical original paid cofactor observation without resampling. -/
theorem channel_sample (site : Fin 2) (quarter : UnitCircuitQuarter) (index : Fin 6) :
    (channelPiece site quarter index).cell.sample = (valuePiece site quarter).cell.sample :=
  (valuePiece site quarter).cell.reweight_sample (channelData site index)

/-- The original value piece prepares one actual retained midpoint split of that same geometric quarter. -/
private def split (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Refinement.Split (valuePiece site quarter).cell (valuePiece site quarter).within :=
  Refinement.Split.build (valuePiece site quarter).cell (valuePiece site quarter).within

attribute [local irreducible] split

/-- Both actual midpoint children pay exactly one quarter of the original starting scalar allowance. -/
theorem split_allowances (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (split site quarter).left.allowance = (valuePiece site quarter).cell.allowance / 4 ∧
      (split site quarter).right.allowance = (valuePiece site quarter).cell.allowance / 4 :=
  ⟨(split site quarter).left_allowance_eq, (split site quarter).right_allowance_eq⟩

/-- The regular scalar quarter integrals include all original derivative denominators with exact finite cell counts. -/
theorem channel_count (site : Fin 2) (quarter : UnitCircuitQuarter) (index : Fin 6) (depth : Nat) :
    ((channelPiece site quarter index).program.model depth).cells.length = 2 ^ depth :=
  ((channelPiece site quarter index).layerAt depth).model_count

/-- Every original scalar channel integral has a quantified finite later-sample bound on that same prepared quarter. -/
theorem channel_later_close (site : Fin 2) (quarter : UnitCircuitQuarter) (index : Fin 6)
    {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq (((channelPiece site quarter index).layerAt later).model.integralSample -
      ((channelPiece site quarter index).layerAt earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius
        (16 * (channelPiece site quarter index).span.width ^ 2 * (channelPiece site quarter index).cell.allowance)
        earlier :=
  (channelPiece site quarter index).later_close order

/-- Assemble all four original scalar quarter integrals on the identical retained geometric circuit. -/
private def scalarCircuit (site : Fin 2) :
    Radial.Differential.Circuit.Integral (valueData site) (circuit site) accuracy :=
  Radial.Differential.Circuit.Integral.build (valueData site) (circuit site) accuracy

attribute [local irreducible] scalarCircuit

/-- Reweight all four original scalar source cells to any of the six retained differential forms. -/
private def scalarCells (site : Fin 2) (index : Fin 6) :
    Radial.Differential.Circuit.Cells (channelData site index) (circuit site) accuracy :=
  (scalarCircuit site).cells.reweight (channelData site index)

/-- Every original circuit channel preserves its complete paid first-quarter source observation. -/
theorem scalar_first_sample (site : Fin 2) (index : Fin 6) :
    (scalarCells site index).first.sample = (scalarCircuit site).cells.first.sample :=
  (scalarCircuit site).cells.first.reweight_sample (channelData site index)

/-- Each derivative circuit programme retains exactly four original dyadic quarter cell lists. -/
theorem scalar_count (site : Fin 2) (index : Fin 6) (depth : Nat) :
    ((scalarCells site index).program.model depth).cells.length = 4 * 2 ^ depth :=
  (scalarCells site index).program_count depth

/-- The original whole-circuit cache internally meets every supplied positive finite integral allowance request. -/
theorem scalar_requested_allowance (site : Fin 2) (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    ((scalarCircuit site).cached.stage
      ((scalarCircuit site).cached.approximation.refineIndex current target positive)).allowance < target :=
  (scalarCircuit site).requested_allowance current target positive

/-- Construct one whole covered quarter on the identical original circuit used by all retained scalar integral rows.

The actual spatial finish Owner is not identified with the independent
original target Reading. The whole original Leg and all its scalar-program
source indices remain unchanged while spatial coverage is constructed.
-/
public def spatial (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Parallel.Coverage ((circuit site).leg quarter) := Parallel.Coverage.build ((circuit site).leg quarter)

attribute [local irreducible] spatial

/-- The stored spatial leg retains the identical complete prepared scalar quarter. -/
public theorem scalarQuarter_eq (site : Fin 2) (quarter : UnitCircuitQuarter)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    ((circuit site).leg quarter).actual = coverage.leg.actual :=
  (congrArg (fun leg : Radial.Transport.Leg site (parameter site) quarter => leg.actual) coverage.leg_eq).symm

/-- Reindex the supplied actual scalar layer by the stored whole-leg equality, preserving all its caches. -/
public def valueLayerOnCoverage (site : Fin 2) (quarter : UnitCircuitQuarter) {depth : Nat}
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :=
  layer.transport (scalarQuarter_eq site quarter coverage)

/-- The same complete fine scalar programme model and its actual coarse-indexed Piece/cell cache partition. -/
private def ValueLayerRefinement (site : Fin 2) (quarter : UnitCircuitQuarter)
    (coverage : Parallel.Coverage ((circuit site).leg quarter)) {coarse : Nat}
    (parents : Refinement.Layer (valuePiece site quarter) coarse) (extra : Nat) : Type 1 :=
  let initial := (valuePiece site quarter).transport (scalarQuarter_eq site quarter coverage)
  Σ fine : {actual : Refinement.Layer initial (coarse + extra) //
      actual = initial.layerAt (coarse + extra) ∧
        actual.model = (valuePiece site quarter).program.model (coarse + extra)},
    Refinement.Layer.Partition (valueLayerOnCoverage site quarter parents coverage) fine.val

/-- Continue the supplied original scalar layer and partition its same actual fine caches on the supplied Coverage.

The whole quarter is transported by its original complete Leg equality.
One original cached advance and one partition retain the actual Piece and
CellModel banks; erased equations identify the whole original scalar
programme model at the summed depth. No scalar source, original Piece,
model programme or observation is constructed again by this consumer.
-/
private def valueLayerRefinement (site : Fin 2) (quarter : UnitCircuitQuarter)
    (coverage : Parallel.Coverage ((circuit site).leg quarter)) {coarse : Nat}
    (parents : Refinement.Layer (valuePiece site quarter) coarse)
    (original : parents = (valuePiece site quarter).layerAt coarse) (extra : Nat) :
    ValueLayerRefinement site quarter coverage parents extra := by
  let quarterEq := scalarQuarter_eq site quarter coverage
  let initial := (valuePiece site quarter).transport quarterEq
  let retained := valueLayerOnCoverage site quarter parents coverage
  have parentEq : retained = initial.layerAt coarse :=
    (congrArg (fun layer : Refinement.Layer (valuePiece site quarter) coarse =>
      layer.transport quarterEq) original).trans ((valuePiece site quarter).layerAt_transport coarse quarterEq).symm
  let fine := retained.advance extra
  have fineEq : fine = initial.layerAt (coarse + extra) :=
    (congrArg (fun layer : Refinement.Layer initial coarse => layer.advance extra)
      parentEq).trans (initial.layerAt_advance coarse extra)
  have modelEq : fine.model = (valuePiece site quarter).program.model (coarse + extra) := by
    calc
      fine.model = (initial.layerAt (coarse + extra)).model :=
        congrArg (fun layer : Refinement.Layer initial (coarse + extra) => layer.model) fineEq
      _ = (((valuePiece site quarter).layerAt (coarse + extra)).transport quarterEq).model :=
        congrArg (fun layer : Refinement.Layer initial (coarse + extra) => layer.model)
          ((valuePiece site quarter).layerAt_transport (coarse + extra) quarterEq)
      _ = ((valuePiece site quarter).layerAt (coarse + extra)).model :=
        ((valuePiece site quarter).layerAt (coarse + extra)).transport_model quarterEq
      _ = _ := ((valuePiece site quarter).model_eq (coarse + extra)).symm
  let partition := Refinement.Layer.partition retained parentEq fine fineEq
  exact ⟨⟨fine, fineEq, modelEq⟩, partition⟩

/-- Read the same original bounded scalar occurrence after complete-quarter transport. -/
public def valueLayerPiece (site : Fin 2) (quarter : UnitCircuitQuarter) {depth : Nat}
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :=
  (valueLayerOnCoverage site quarter layer coverage).pieces[index.val]'(by
    change index.val < (layer.transport (scalarQuarter_eq site quarter coverage)).pieces.length
    rewrite [layer.transport_count]
    exact index.isLt)

/-- The spatially indexed readback preserves the identical original scalar piece at its actual ordinal. -/
private theorem valueLayerPiece_original (site : Fin 2) (quarter : UnitCircuitQuarter) {depth : Nat}
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    HEq (valueLayerPiece site quarter layer index coverage) (layer.pieces[index.val]'index.isLt) :=
  layer.transport_get (scalarQuarter_eq site quarter coverage) index

/-- The same actual scalar factory layer retains its canonical ordered dyadic spans on the stored spatial quarter.

The supplied complete layer is retained rather than rebuilt. Its exact
factory equation and original whole-quarter equality preserve every scalar
occurrence and source cache; the canonical interval row is used only in
this erased proof, without a successful assignment or coverage premise.
-/
private theorem value_layer_spans (site : Fin 2) (quarter : UnitCircuitQuarter) (depth : Nat)
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (original : layer = (valuePiece site quarter).layerAt depth)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    (valueLayerOnCoverage site quarter layer coverage).pieces.map (fun piece => piece.span) =
      Interval.Bisection.parts depth ⟨0, 1, by decide +kernel⟩ := by
  have retained := (valuePiece site quarter).layerAt_spans depth
  rewrite [← original] at retained
  exact (layer.transport_spans (scalarQuarter_eq site quarter coverage)).trans
    (retained.trans (congrArg (Interval.Bisection.parts depth) (valuePiece_span site quarter)))

/-- The same actual original bounded scalar occurrence belongs to the original midpoint partition. -/
private theorem value_layer_span_member (site : Fin 2) (quarter : UnitCircuitQuarter) (depth : Nat)
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (original : layer = (valuePiece site quarter).layerAt depth) (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    (valueLayerPiece site quarter layer index coverage).span ∈
      Interval.Bisection.parts depth ⟨0, 1, by decide +kernel⟩ := by
  have bounded : index.val < (valueLayerOnCoverage site quarter layer coverage).pieces.length := by
    change index.val < (layer.transport (scalarQuarter_eq site quarter coverage)).pieces.length
    rewrite [layer.transport_count]
    exact index.isLt
  have member : valueLayerPiece site quarter layer index coverage ∈
      (valueLayerOnCoverage site quarter layer coverage).pieces := List.getElem_mem bounded
  have mapped : (valueLayerPiece site quarter layer index coverage).span ∈
      ((valueLayerOnCoverage site quarter layer coverage).pieces.map (fun piece => piece.span)) :=
    Data.List.Map.mem_map_of_mem member
  rewrite [value_layer_spans site quarter depth layer original coverage] at mapped
  exact mapped

/-- Every same retained original scalar occurrence has internally proved positive chart width. -/
private theorem value_layer_proper (site : Fin 2) (quarter : UnitCircuitQuarter) (depth : Nat)
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (original : layer = (valuePiece site quarter).layerAt depth) (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    (valueLayerPiece site quarter layer index coverage).span.lower <
      (valueLayerPiece site quarter layer index coverage).span.upper := by
  exact Interval.Bisection.parts_proper depth ⟨0, 1, by decide +kernel⟩ (by decide +kernel)
    (value_layer_span_member site quarter depth layer original index coverage)

/-- The same actual scalar layer's original upper-time row is its canonical retained unit dyadic trace. -/
private theorem value_layer_uppers (site : Fin 2) (quarter : UnitCircuitQuarter) (depth : Nat)
    (layer : Refinement.Layer (valuePiece site quarter) depth)
    (original : layer = (valuePiece site quarter).layerAt depth)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    (valueLayerOnCoverage site quarter layer coverage).pieces.map (fun piece => piece.span.upper) =
      DyadicTrace.tail depth 0 1 := by
  have retained := congrArg (fun spans : List Interval.Bounds => spans.map (fun span => span.upper))
    (value_layer_spans site quarter depth layer original coverage)
  rewrite [Data.List.Map.map_map] at retained
  exact retained.trans (DyadicTrace.tail_eq_parts_upper depth ⟨0, 1, by decide +kernel⟩).symm

/-- The original locator assigns a whole actual scalar cell to its retained coarse trace edge.

The supplied ordered time row is completed work, with its original dyadic
factory equation used only in erased proofs. The same actual scalar layer
and bounded cell ordinal derive endpoint coverage internally. One original
locator call reads that retained row at the actual cell's upper endpoint;
no layer, time row, Reading, Point or model is rebuilt.
-/
private def valueLayerEdge (site : Fin 2) (quarter : UnitCircuitQuarter) (coarse extra : Nat)
    (times : List Fraction.Rational) (trace : times = DyadicTrace.tail coarse 0 1)
    (layer : Refinement.Layer (valuePiece site quarter) (coarse + extra))
    (original : layer = (valuePiece site quarter).layerAt (coarse + extra))
    (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    {edge : Fin times.length //
      (DyadicTrace.indexed 0 times edge.castSucc ≤ (valueLayerPiece site quarter layer index coverage).span.lower ∧
        (valueLayerPiece site quarter layer index coverage).span.upper ≤ DyadicTrace.indexed 0 times edge.succ) ∧
      (extra = 0 →
        DyadicTrace.indexed 0 times edge.castSucc = (valueLayerPiece site quarter layer index coverage).span.lower ∧
          DyadicTrace.indexed 0 times edge.succ = (valueLayerPiece site quarter layer index coverage).span.upper)} := by
  let part := (valueLayerPiece site quarter layer index coverage).span
  have member : part ∈ Interval.Bisection.parts (coarse + extra) ⟨0, 1, by decide +kernel⟩ :=
    value_layer_span_member site quarter (coarse + extra) layer original index coverage
  have bounded := Interval.Bisection.parts_subset (coarse + extra) ⟨0, 1, by decide +kernel⟩ member
    (show part.Contains part.upper from ⟨part.valid, le_rfl⟩)
  have nonempty : times ≠ [] := by
    intro empty
    have size := congrArg List.length trace
    rewrite [empty, DyadicSteps.tail_length] at size
    exact (Nat.ne_of_gt (Nat.pow_pos (by decide +kernel : 0 < 2))).symm size
  have upper : part.upper ≤ DyadicTrace.terminal 0 times := by
    rewrite [trace, DyadicTrace.tail_terminal]
    exact bounded.2
  let selected := DyadicTrace.locate 0 times nonempty part.upper bounded.1 upper
  refine ⟨selected.val, ?_⟩
  dsimp only [selected]
  cases trace
  exact DyadicSteps.tail_locate_contains coarse extra ⟨0, 1, by decide +kernel⟩
    (by decide +kernel) member nonempty bounded.1 upper

/-- The assigned actual cell begins either at its original edge source or strictly inside that same edge.

Positive scalar width and the computed whole-cell containment exclude the
target endpoint. The two existing source/interior coefficient procedures
therefore cover every bounded scalar occurrence without a target replacement.
-/
private theorem valueLayerEdge_source_or_interior (site : Fin 2) (quarter : UnitCircuitQuarter)
    (coarse extra : Nat) (times : List Fraction.Rational) (trace : times = DyadicTrace.tail coarse 0 1)
    (layer : Refinement.Layer (valuePiece site quarter) (coarse + extra))
    (original : layer = (valuePiece site quarter).layerAt (coarse + extra)) (index : Fin layer.pieces.length)
    (coverage : Parallel.Coverage ((circuit site).leg quarter) := spatial site quarter) :
    let edge := valueLayerEdge site quarter coarse extra times trace layer original index coverage
    (valueLayerPiece site quarter layer index coverage).span.lower = DyadicTrace.indexed 0 times edge.val.castSucc ∨
      (DyadicTrace.indexed 0 times edge.val.castSucc < (valueLayerPiece site quarter layer index coverage).span.lower ∧
        (valueLayerPiece site quarter layer index coverage).span.lower <
          DyadicTrace.indexed 0 times edge.val.succ) := by
  let edge := valueLayerEdge site quarter coarse extra times trace layer original index coverage
  by_cases same : (valueLayerPiece site quarter layer index coverage).span.lower =
      DyadicTrace.indexed 0 times edge.val.castSucc
  · exact Or.inl same
  · have past : DyadicTrace.indexed 0 times edge.val.castSucc <
        (valueLayerPiece site quarter layer index coverage).span.lower :=
      ⟨edge.property.1.1, fun reverse => same (Fraction.Order.Basic.le_antisymm _ _ reverse edge.property.1.1)⟩
    exact Or.inr ⟨past,
      (value_layer_proper site quarter (coarse + extra) layer original index coverage).trans_le edge.property.1.2⟩

/-- The actual covered-mesh source and original scalar integral piece retain the same complete original Reading. -/
theorem spatial_scalar_source (site : Fin 2) (quarter : UnitCircuitQuarter) :
    HEq ((spatial site quarter).readings.get 0) ((scalarCircuit site).cells.piece quarter).source := by
  have original : HEq (spatial site quarter).leg.source ((circuit site).leg quarter).source := by
    have project (left right : Radial.Transport.Leg site (parameter site) quarter) (equal : left = right) :
        HEq left.source right.source := by
      cases equal
      rfl
    exact project _ _ (spatial site quarter).leg_eq
  exact (heq_of_eq (spatial site quarter).readings_source).trans
    (original.trans ((scalarCircuit site).cells.piece_source quarter).symm)

/-- The covered mesh retains the original target query separately from its actual continued geometric finish Owner. -/
theorem spatial_target (site : Fin 2) (quarter : UnitCircuitQuarter) :
    HEq ((spatial site quarter).readings.get (Fin.last Parallel.times.length))
      ((circuit site).leg quarter).target := by
  have original : HEq (spatial site quarter).leg.target ((circuit site).leg quarter).target := by
    have project (left right : Radial.Transport.Leg site (parameter site) quarter) (equal : left = right) :
        HEq left.target right.target := by
      cases equal
      rfl
    exact project _ _ (spatial site quarter).leg_eq
  exact (spatial site quarter).readings_target.trans original

/-- Continue the actual second quarter from the actual first spatial finish, preserving the original circuit source.

The original second Reading/Geometry banks persist. Its former independent
attachment is not used as the handoff, and its original target Reading is not
silently substituted for the new continued finish owner.
-/
private def spatialFirstSecond (site : Fin 2) :=
  (spatial site .second).appendFrom (spatial site .first).blocks
    (Parallel.quarter_seams site (parameter site)).1

attribute [local irreducible] spatialFirstSecond

/-- The actual two-quarter seam construction retains both paid whole-quarter block counts. -/
theorem spatial_first_second_count (site : Fin 2) : (spatialFirstSecond site).2.val.length = 256 := by
  exact (spatialFirstSecond site).2.property.trans
    ((congrArg (fun count => count + 128) (spatial site .first).count).trans (by decide +kernel))

/-- The appended quarter consumes the very same complete original first spatial chain before its actual new tail. -/
theorem spatial_first_second_moving (site : Fin 2) :
    ((spatial site .second).appendFrom (spatial site .first).blocks
      (Parallel.quarter_seams site (parameter site)).1).2.val.movingVertices =
    (spatial site .first).blocks.movingVertices ++
      ((spatial site .second).continueFrom
        (SquareRoot.Owner.Transport.castOwnerParameter
          (congrArg (Paths.polynomial (parameter site)).eval
            (Parallel.quarter_seams site (parameter site)).1)
          (spatial site .first).finishOwner)).2.val.movingVertices :=
  (spatial site .second).appendFrom_movingVertices (spatial site .first).blocks
    (Parallel.quarter_seams site (parameter site)).1

/-- The paid actual owner-trace budget on the same retained leg of the existing spatial fixture. -/
public def ownerBudget (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Radial.Transport.Leg.TraceBudget (spatial site quarter).leg :=
  Radial.Transport.Leg.TraceBudget.build (spatial site quarter).leg

attribute [local irreducible] ownerBudget

/-- Continue the actual existing full-cubic source owner using its same original attachment and leg caches. -/
public def ownerTrace (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Parallel.OwnerTrace (spatial site quarter).leg (ownerBudget site quarter) (spatial site quarter).source :=
  Parallel.OwnerTrace.build (spatial site quarter).leg (ownerBudget site quarter) (spatial site quarter).source

attribute [local irreducible] ownerTrace

/-- Materialize compared spatial blocks from the same complete original owner trace and its literal affine targets.

The computed fine table is used without claiming execution of its full mesh.
The pre-existing coarse spatial fixture and its source attachment remain
retained; no assumed comparison or replacement source owner is supplied.
-/
private def comparedSpatial (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Parallel.OwnerTrace.Covered (ownerTrace site quarter) := (ownerTrace site quarter).cover

attribute [local irreducible] comparedSpatial

/-- Both labelled fixtures keep the entire original owner trace beside their compared spatial block caches. -/
theorem compared_spatial_original (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (comparedSpatial site quarter).trace = ownerTrace site quarter := (comparedSpatial site quarter).trace_eq

/-- The compared fine cover starts on the identical complete original coarse-cover Source attachment. -/
theorem compared_spatial_source (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (comparedSpatial site quarter).trace.source = (spatial site quarter).source :=
  (comparedSpatial site quarter).trace.source_eq

/-- Every actual quarter's compared spatial finish names the same original signed circuit target channel.

The original block trace ends at that exact retained affine owner by its
index. Only the existing leg identity transports the target name; the
comparison preserves both original numerical owners and its actual requests.
-/
def compared_spatial_target (site : Fin 2) (quarter : UnitCircuitQuarter) :
    NamedEquivalent
      (((comparedSpatial site quarter).trace.finishAtTarget).certificate
        ((comparedSpatial site quarter).trace.finishAtTarget).parameterNonzero).value.name
      ((circuit site).leg quarter).target.lift.value.name :=
  Gaussian.Equivalence.NamedEquivalent.transport rfl
    (congrArg (fun leg : Radial.Transport.Leg site (parameter site) quarter => leg.target.lift.value.name)
      (spatial site quarter).leg_eq)
    (comparedSpatial site quarter).trace.targetAgreement

/-- The fine cover's actual target reindexing keeps one spatial block per paid chart edge and retains every handoff. -/
theorem compared_spatial_count (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (comparedSpatial site quarter).blocksAtTarget.length =
      2 ^ (comparedSpatial site quarter).trace.budget.fine.selection.stage :=
  (comparedSpatial site quarter).blocksAtTarget_length

/-- An original full-cubic local primitive gives a finite boundary estimate for the same retained scalar quarter.

The actual inverse-root model, numerator and indexed coefficient stay intact.
Only its box ceiling changes; the complete primitive polynomial is the supplied
original cache. The layer residual remains explicit, so the claim neither
assumes sheet agreement nor asserts arbitrary-accuracy integral equivalence.
-/
theorem scalar_original_primitive_boundary (site : Fin 2) (quarter : UnitCircuitQuarter)
    {count index : Nat} {patch : ContinuedNeighborhood (Paths.polynomial (parameter site)) count}
    {numerator : CoefficientPolynomial} (original : PrimitiveModel patch index numerator) (depth : Nat) :
    let primitive := original.primitive.onBox (Degeneration.spatialBox site)
    let layer := ((scalarCircuit site).cells.piece quarter).layerAt depth
    let bounds := Dense.Gaussian.Bounds.Box.denseHornerNormBounds original.coefficient (Degeneration.spatialBox site)
    Norm.Basic.normSq (original.primitive.value.eval
        (Radial.point site (parameter site) 2
          (Waist.direction quarter ((scalarCircuit site).cells.piece quarter).span.upper) (by decide +kernel)).base -
      original.primitive.value.eval (Radial.point site (parameter site) 2
        (Waist.direction quarter ((scalarCircuit site).cells.piece quarter).span.lower) (by decide +kernel)).base -
      layer.model.integralSample) ≤
        4 * (primitive.remainderBound *
          ((25 / 4) * Norm.Basic.normSq (Degeneration.halfGap site (parameter site))) ^ 2 +
          bounds.value * ((25 / 4) * Norm.Basic.normSq (Degeneration.halfGap site (parameter site)))) *
            ((scalarCircuit site).cells.piece quarter).span.width ^ 2 *
              Geometric.Basic.quarterRadius (((scalarCircuit site).cells.piece quarter).span.width ^ 2) depth +
                2 * layer.primitiveResidual original.coefficient *
                  ((scalarCircuit site).cells.piece quarter).span.width ^ 2 := by
  exact (((scalarCircuit site).cells.piece quarter).layerAt depth).spatialPrimitive_error_le
    (((scalarCircuit site).cells.piece quarter).layerAt_spans depth)
    (original.primitive.onBox (Degeneration.spatialBox site))
    (Dense.Gaussian.Bounds.Box.denseHornerNormBounds original.coefficient (Degeneration.spatialBox site)) rfl
    (fun time _ => Radial.point_inside site (parameter site) 2 (Waist.direction quarter time)
      (by decide +kernel) ((circuit site).leg quarter).actual.data.lower
      ((circuit site).leg quarter).actual.data.upper ((circuit site).leg quarter).actual.data.bound)

/-- Request the actual spatial primitive bank on the supplied original frame's curve and retained fine covered trace.

The original frame is an input owner; no isolation or replacement curve is
constructed for this request. The first holomorphic differential uses the
same displayed full cubic as the retained parallel circuit.
-/
private def spatialRequest (site : Fin 2) (quarter : UnitCircuitQuarter)
    (frame : Paths.Frame (parameter site)) (target : Fraction.Rational) (positive : 0 < target) :
    Parallel.OwnerTrace.Covered.PrimitiveRequest (comparedSpatial site quarter) (Periods.Fibre.frameCurve frame) rfl
      ⟨0⟩ 0 target :=
  (comparedSpatial site quarter).primitiveRequest (Periods.Fibre.frameCurve frame) rfl ⟨0⟩ 0 target positive

attribute [local irreducible] spatialRequest

/-- Actual spatial primitive acquisition retains the entire identical supplied OwnerTrace, Reading and Blocks cache. -/
theorem spatial_request_original (site : Fin 2) (quarter : UnitCircuitQuarter)
    (frame : Paths.Frame (parameter site)) (target : Fraction.Rational) (positive : 0 < target) :
    (spatialRequest site quarter frame target positive).1.val = comparedSpatial site quarter :=
  (spatialRequest site quarter frame target positive).1.property

/-- The primitive bank retains the identical original fine Blocks with their actual moving targets and paid joins. -/
theorem spatial_request_blocks (site : Fin 2) (quarter : UnitCircuitQuarter)
    (frame : Paths.Frame (parameter site)) (target : Fraction.Rational) (positive : 0 < target) :
    HEq (spatialRequest site quarter frame target positive).2.1.val
      (spatialRequest site quarter frame target positive).1.val.blocksAtTarget :=
  Parallel.OwnerTrace.Covered.PrimitiveRequest.blocks_heq (spatialRequest site quarter frame target positive)

/-- The original computed spatial child integral approximates its actual cached primitive-boundary sum at any target.

Coverage, properness, local sheet links and all refinement budgets are derived
from the same retained fine Blocks. This does not yet compare their boundary
sum with the separate original curved scalar integral program.
-/
theorem spatial_request_accurate (site : Fin 2) (quarter : UnitCircuitQuarter)
    (frame : Paths.Frame (parameter site)) (target : Fraction.Rational) (positive : 0 < target) :
    Norm.Basic.normSq ((spatialRequest site quarter frame target positive).2.2.2.primitiveSum -
      (spatialRequest site quarter frame target positive).2.2.2.integralSample) < target := by
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact (spatialRequest site quarter frame target positive).2.2.2.accurate

/-- Cache one original whole-ambient primitive bound on the existing retained spatial Leg. -/
public def primitiveBounds (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Parallel.OwnerBudget.PrimitiveBounds (spatial site quarter).leg (ownerBudget site quarter)
      (ownerTrace site quarter).budget.clearance :=
  Parallel.OwnerBudget.primitiveBounds (spatial site quarter).leg (ownerBudget site quarter)
    (ownerTrace site quarter).budget.clearance

attribute [local irreducible] primitiveBounds

/-- Every original fine-bank chord consumes the identical cached primitive radius at its actual bounded occurrence.

The geometric entries are the OwnerTrace's own retained neighboring Reading
pairs, clearances and routes. No alternative endpoint or root owner is built,
and the common bound is retained outside this edge-indexed readback.
-/
theorem primitive_chord_radius (site : Fin 2) (quarter : UnitCircuitQuarter)
    (edge : Fin (DyadicTrace.tail
      (ownerTrace site quarter).budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    ((primitiveBounds site quarter).chord ((ownerTrace site quarter).geometries.get edge)).radius =
      (primitiveBounds site quarter).radius :=
  Parallel.OwnerBudget.PrimitiveBounds.chord_radius _ _

/-- The actual retained Leg obtains a finite common-domain selection from its identical cached numerical bounds. -/
private def primitiveBudget (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Radial.Transport.Leg.TraceBudget (spatial site quarter).leg (primitiveBounds site quarter).accuracy :=
  (primitiveBounds site quarter).traceBudget

attribute [local irreducible] primitiveBudget

/-- Every original curved-quarter point in the actual selected fixture edge lies in its common primitive domain.

Both labelled parameters and all original oriented quarters use their retained
Leg and source clearance. The requested finite Selection and radius are
actual caches; no successful coverage or replacement root is supplied.
-/
theorem primitive_curve_domain (site : Fin 2) (quarter : UnitCircuitQuarter)
    (edge : Fin (DyadicTrace.tail
      (primitiveBudget site quarter).selection.stage (0 : Fraction.Rational) 1).length)
    (time : Fraction.Rational)
    (between :
      DyadicTrace.indexed 0
        (DyadicTrace.tail (primitiveBudget site quarter).selection.stage
          (0 : Fraction.Rational) 1) edge.castSucc ≤ time ∧
      time ≤ DyadicTrace.indexed 0
        (DyadicTrace.tail (primitiveBudget site quarter).selection.stage
          (0 : Fraction.Rational) 1) edge.succ) :
    (Box.Square.Centered.BoxTransport.centeredBox
      (coordinate site (parameter site) 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0
          (DyadicTrace.tail (primitiveBudget site quarter).selection.stage
            (0 : Fraction.Rational) 1) edge.castSucc))
      (primitiveBounds site quarter).radius (primitiveBounds site quarter).radius_positive.le).Contains
        (coordinate site (parameter site) 2 quarter (by decide +kernel) time) :=
  (primitiveBounds site quarter).curve_inside (primitiveBudget site quarter) edge time between

/-- Build the original owner trace at the actual cached primitive-domain cap and unchanged supplied source. -/
private def primitiveOwnerTrace (site : Fin 2) (quarter : UnitCircuitQuarter) :
    Parallel.OwnerTrace (spatial site quarter).leg (ownerBudget site quarter) (spatial site quarter).source
      (some (primitiveBounds site quarter).timeRequest) :=
  Parallel.OwnerTrace.build (spatial site quarter).leg (ownerBudget site quarter) (spatial site quarter).source
    (some (primitiveBounds site quarter).timeRequest)

attribute [local irreducible] primitiveOwnerTrace

section EntryBank

attribute [local irreducible] Parallel.OwnerMove.PrimitiveTarget.Anchored

variable (site : Fin 2) (quarter : UnitCircuitQuarter)
variable (coverage : Parallel.Coverage ((circuit site).leg quarter))
variable (coarse : Radial.Transport.Leg.TraceBudget coverage.leg)
variable {clearance : Parallel.OwnerBudget.SourceClearance coverage.leg}
variable (bounds : Parallel.OwnerBudget.PrimitiveBounds coverage.leg coarse clearance)

/-- The original capped trace on the supplied actual Coverage and retained coarse/primitive bounds. -/
private def EntryTrace : Type 1 :=
  Parallel.OwnerTrace coverage.leg coarse coverage.source (some bounds.timeRequest)

/-- Cache original source owners, signed links and moves once on a supplied actual capped quarter trace.

The original Coverage, coarse bounds and trace are completed work. One
forward original entry-bank construction retains its literal ordered moves,
including every target-as-next-source handoff. The initial signed link uses
the supplied actual Coverage fields, without invoking a Coverage factory.
-/
private def primitiveEntryBank (trace : EntryTrace site quarter coverage coarse bounds) :
    {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves} :=
  let bank := Parallel.OwnerMoves.entries trace.moves
  ⟨bank, rfl⟩

/-- Read the same actual retained move selected by an original scalar cell on the supplied capped trace.

One original upper-endpoint locator consumes the supplied completed time row
and scalar layer/index. Exact whole-bank list transport passes that SAME row
to the original dependent-product lookup, without constructing a time row,
source, signed comparison, Reading, geometry, Point, primitive or prefix path.
-/
private def valueLayerMove (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    (extra : Nat) (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage 0 1)
    (layer : Refinement.Layer (valuePiece site quarter)
      (trace.budget.fine.selection.stage + extra))
    (original : layer = (valuePiece site quarter).layerAt (trace.budget.fine.selection.stage + extra))
    (index : Fin layer.pieces.length) :=
  let edge := valueLayerEdge site quarter trace.budget.fine.selection.stage extra times sameTimes layer original index
  let retained := DependentProduct.castItems sameTimes bank.val
  DependentProduct.get times retained edge.val

/-- The complete actual selected source, signed relation and move belong to the same original entry-bank factory.

The retained-bank equation transports all three original values at this
actual bounded locator index. The factory is used only in erased ownership
proofs; executable readback consumes the whole supplied bank and time row.
-/
private theorem valueLayerMove_original (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    (extra : Nat) (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage 0 1)
    (layer : Refinement.Layer (valuePiece site quarter)
      (trace.budget.fine.selection.stage + extra))
    (original : layer = (valuePiece site quarter).layerAt (trace.budget.fine.selection.stage + extra))
    (index : Fin layer.pieces.length) :
    let edge := valueLayerEdge site quarter trace.budget.fine.selection.stage extra times sameTimes layer original index
    let selected : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length :=
      ⟨edge.val.val, by rewrite [← sameTimes]; exact edge.val.isLt⟩
    valueLayerMove site quarter coverage coarse bounds trace bank extra times sameTimes layer original index =
      Entries.get (Parallel.OwnerMoves.entries trace.moves) selected := by
  dsimp only [valueLayerMove]
  rewrite [DependentProduct.get_castItems]
  exact congrArg (fun retained => Entries.get retained _) bank.property

/-- Build actual primitive/source/reference entries once on the supplied completed quarter's original move bank.

The production constructor consumes the same retained geometry and move
entries in one paired traversal. Each original target, source Point and
fixed source reference is retained as a whole factory result; no original
Coverage, trace, Reading, observation or source preparation is repeated.
-/
private def primitiveTargetBank (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    (count : Nat) :
    {actual : Entries.Primitives bounds bank.val count //
      actual = Entries.primitives bounds bank.val count} :=
  let retained := Entries.primitives bounds bank.val count
  ⟨retained, rfl⟩

/-- Read an original scalar cell's whole retained primitive/source/reference cache through its actual containing edge.

The completed primitive bank and original time row are supplied once. One
unchanged locator selects the original bounded occurrence, and direct
readback returns its same target, signed source Point and fixed reference.
No per-cell primitive factory, geometry lookup or trace construction runs.
-/
private def valueLayerPrimitive (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (extra : Nat) (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage 0 1)
    (layer : Refinement.Layer (valuePiece site quarter)
      (trace.budget.fine.selection.stage + extra))
    (original : layer = (valuePiece site quarter).layerAt (trace.budget.fine.selection.stage + extra))
    (index : Fin layer.pieces.length) :=
  let edge := valueLayerEdge site quarter trace.budget.fine.selection.stage extra times sameTimes layer original index
  let actual := DependentProduct.castItems sameTimes retained
  DependentProduct.get times actual edge.val

/-- The selected original scalar cell consumes the complete factory cache belonging to the same retained move.

The equation uses the original source/Point/reference factory only in an
erased proof. Both the actual scalar occurrence and the primitive bank's
original bounded move remain unchanged.
-/
private theorem valueLayerPrimitive_original (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat}
    (retained : {actual : Entries.Primitives bounds bank.val count //
      actual = Entries.primitives bounds bank.val count})
    (extra : Nat) (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage 0 1)
    (layer : Refinement.Layer (valuePiece site quarter)
      (trace.budget.fine.selection.stage + extra))
    (original : layer = (valuePiece site quarter).layerAt (trace.budget.fine.selection.stage + extra))
    (index : Fin layer.pieces.length) :
    let edge := valueLayerEdge site quarter trace.budget.fine.selection.stage extra times sameTimes layer original index
    let selected : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length :=
      ⟨edge.val.val, by rewrite [← sameTimes]; exact edge.val.isLt⟩
    valueLayerPrimitive site quarter coverage coarse bounds trace bank retained.val extra times sameTimes
      layer original index =
      Parallel.OwnerMove.PrimitiveTarget.anchor bounds
        (Entries.get bank.val selected).2.2 count := by
  dsimp only [valueLayerPrimitive]
  exact (DependentProduct.get_castItems sameTimes retained.val _).trans
    ((congrArg (fun actual : Entries.Primitives bounds bank.val count =>
      Entries.Primitives.get bounds actual _) retained.property).trans
        (Entries.primitives_get bounds bank.val count _))

/-- Build the actual spatial-parent Point bank using the same retained original target, source Point and Reference.

The supplied trace, entry bank and bounded occurrence retain both original
owners and actual geometry. The original parent cache and its ordered
indices are supplied completed work. Direct cache projections feed the
original Point factory, with no repeated Reference or source preparation.
-/
private def primitiveBankParentPoints (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage 0 1) (edge : Fin times.length)
    (frame : Paths.Frame (parameter site))
    (covered :
      let selected : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length :=
        ⟨edge.val, by rewrite [← sameTimes]; exact edge.isLt⟩
      Parallel.Covered (trace.geometries.get selected) (Entries.get bank.val selected).1)
    (cache : ParentCache (curve := Periods.Fibre.frameCurve frame) covered.block ⟨0⟩ 0) :
    let selected := DependentProduct.get times (DependentProduct.castItems sameTimes retained) edge
    Parallel.OwnerMove.PrimitiveTarget.ParentPoints bounds selected.target selected.sourcePoint frame covered cache :=
  let selected := DependentProduct.get times (DependentProduct.castItems sameTimes retained) edge
  Parallel.OwnerMove.PrimitiveTarget.parentPoints bounds selected.target selected.sourcePoint frame covered cache
    ⟨selected.reference, selected.reference_eq⟩

section ScalarLayer

open Parallel.OwnerMove.PrimitiveTarget
open Purelib.Approximation.Rational.Geometric

section ParentPrecisions

open Purelib.Data.Nat.List
open Purelib.Algebra
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

/-- The same actual coarse occurrence retains its computed edge, original root cache, initial piece and paid model.

The existing Sigma/subtype view keeps whole actual inputs as runtime
caches beside the original Precision and prepared source. Future child
requests consume those entries without another root-bank or coarse-piece
lookup. All factory equations and index/domain evidence remain erased.
-/
private def ParentPrecision (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (index : Fin parents.pieces.length)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) : Type 1 :=
  let selected := valueLayerEdge site quarter trace.budget.fine.selection.stage 0 times sameTimes
    parents original index coverage
  let roots := DependentProduct.castItems sameTimes retained
  Σ edge : {actual : Fin times.length // actual = selected.val},
  Σ anchored : {actual // actual = DependentProduct.get times roots edge.val},
  Σ initial : {actual // actual = valueLayerPiece site quarter parents index coverage},
    ScalarModels.Precision bounds anchored.val.target initial.val modelFloor scalarFloor target positive ×
      CurveSource bounds anchored.val.target

/-- The ordered original coarse-piece bank of whole retained parent inputs and actual paid Precisions. -/
private def ParentPrecisions (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) : Type 1 :=
  DependentProduct parents.pieces (fun index =>
    ParentPrecision site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original index modelFloor scalarFloor target positive)

/-- Read the computed Taylor stages in one structural traversal of the supplied actual parent cache bank. -/
private def parentPrecisionStages (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive) : List Nat :=
  DependentProduct.mapToList parents.pieces values (fun _ value =>
    (ScalarModels.Precision.taylor bounds (positive := positive) value.2.2.2.1).stage)

/-- Compute the original finite-list maximum of actual retained parent Taylor stages, with zero for an empty bank. -/
private def parentPrecisionStage (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive) : Nat :=
  Maximum.listMaximum
    (parentPrecisionStages site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive values)

/-- Construct the actual ordered parent-model bank and retain its once-computed common later scalar depth.

Every coarse occurrence selects its original model and finite Taylor
payment once. A structural stage readback and the original finite maximum
consume those same stored Selections outside any later child producer.
The resulting existing Sigma/subtype retains both the bank and its actual
computed depth, without adding a nominal request or programme family.
-/
private def parentPrecisions (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Σ values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive,
      {stage : Nat // stage = parentPrecisionStage site quarter coverage coarse bounds
        trace bank retained times sameTimes
      parents original
        modelFloor scalarFloor target positive values} :=
  let parameterValue := parameter site
  let differential := Specification.valueSpecification parameterValue 0
  let data := valueData site
  let values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive :=
    DependentProduct.ofFn parents.pieces (fun index => by
      let selected := valueLayerEdge site quarter trace.budget.fine.selection.stage 0 times sameTimes
        parents original index coverage
      let anchored := DependentProduct.get times (DependentProduct.castItems sameTimes retained) selected.val
      let initial := valueLayerPiece site quarter parents index coverage
      let choice := ScalarModels.precision (parameter := parameterValue)
        (cellDifferential := differential) (cellData := data)
        bounds anchored.target initial modelFloor scalarFloor target positive
      let prepared := curveSource bounds anchored.target
      exact ⟨⟨selected.val, rfl⟩, ⟨anchored, rfl⟩, ⟨initial, rfl⟩, choice, prepared⟩)
  let stage := parentPrecisionStage site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive values
  ⟨values, ⟨stage, rfl⟩⟩

/-- The single finite maximum covers every actual retained original parent Taylor Selection.

The proof uses original dependent-product lookup/map readback and the
existing natural-list maximum theorem. It consumes the stored selected
stage at the same original bounded coarse occurrence, without another
selection or model construction.
-/
private theorem parentPrecisionStage_covers (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive)
    (index : Fin parents.pieces.length) :
    (ScalarModels.Precision.taylor bounds (positive := positive)
      (DependentProduct.get parents.pieces values index).2.2.2.1).stage ≤
        parentPrecisionStage site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive values := by
  let mapped : (index : Fin parents.pieces.length) →
      ParentPrecision site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original index modelFloor scalarFloor target positive → Nat :=
    fun _ value => (ScalarModels.Precision.taylor bounds (positive := positive) value.2.2.2.1).stage
  have readback := DependentProduct.get_mapToList parents.pieces values mapped index
  have bound := Maximum.member_le_listMaximum
    (DependentProduct.mapToList parents.pieces values mapped) _
    (List.getElem_mem (Nat.lt_of_lt_of_le index.isLt
      (DependentProduct.length_mapToList parents.pieces values mapped).symm.le))
  exact readback.symm.le.trans bound

/-- Materialize one original common fine scalar mesh after retaining the same complete parent model/Selection bank.

The actual finite maximum is read from its stored subtype once. Original
valueLayerRefinement advances the supplied completed scalar parent cache
and retains both the actual fine numerical cells and their coarse-order
partition, with its whole original scalar-programme model equation.
-/
private def primitiveBankRefinement (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Σ selected : (Σ values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive,
      {stage : Nat // stage = parentPrecisionStage site quarter coverage coarse bounds
        trace bank retained times sameTimes
      parents original
        modelFloor scalarFloor target positive values}),
      ValueLayerRefinement site quarter coverage parents selected.2.val :=
  let selected := parentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive
  let fine := valueLayerRefinement site quarter coverage parents original selected.2.val
  ⟨selected, fine⟩

/-- The actual retained local Layer and original coefficient requests at one coarse occurrence.

The existing Sigma/subtype keeps the same partition cell slice and the
attained same-model boundary estimate. Its root, prepared source, model,
selections and initial Piece remain the supplied parent-row caches.
-/
private def ParentScalarRequest (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive)
    (stage : {actual : Nat // actual = parentPrecisionStage site quarter coverage coarse bounds
      trace bank retained times sameTimes parents original modelFloor scalarFloor target positive values})
    (fine : ValueLayerRefinement site quarter coverage parents stage.val)
    (index : Fin parents.pieces.length) : Type 1 :=
  let row := DependentProduct.get parents.pieces values index
  let actualParents := valueLayerOnCoverage site quarter parents coverage
  let actualIndex : Fin actualParents.pieces.length := ⟨index.val, by
    change index.val < (parents.transport (scalarQuarter_eq site quarter coverage)).pieces.length
    rewrite [parents.transport_count]
    exact index.isLt⟩
  Σ layer : Refinement.Layer row.2.2.1.val stage.val,
    {_requests : ScalarModels.LayerRequests bounds row.2.1.val row.2.2.2.2
        (ScalarModels.Precision.models bounds (positive := positive) row.2.2.2.1) layer
        (ScalarModels.coefficientTarget row.2.2.1.val target) //
      Norm.Basic.normSq ((ScalarModels.Precision.models bounds (positive := positive)
          row.2.2.2.1).common.primitive.value.eval
          (coordinate site (parameter site) 2 quarter (by decide +kernel) row.2.2.1.val.span.upper) -
        (ScalarModels.Precision.models bounds (positive := positive)
          row.2.2.2.1).common.primitive.value.eval
          (coordinate site (parameter site) 2 quarter (by decide +kernel) row.2.2.1.val.span.lower) -
        layer.model.integralSample) < target ∧
          layer.model.cells = (fine.2.get actualIndex).2.val}

/-- Request the actual partition cells from their same retained parent model and computed common stage.

The original dyadic locator's zero-extra readback proves exact parent
endpoints. Its actual source/interior procedure constructs every cell
request. The common stage covers the stored Taylor Selection, and original
Precision.accurate proves the requested bound on this same numerical slice.
No model, selection, Reading, Reference, scalar mesh or source is rebuilt.
-/
private def primitiveBankScalarRequests (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive)
    (stage : {actual : Nat // actual = parentPrecisionStage site quarter coverage coarse bounds
      trace bank retained times sameTimes parents original modelFloor scalarFloor target positive values})
    (fine : ValueLayerRefinement site quarter coverage parents stage.val)
    (index : Fin parents.pieces.length) :
    ParentScalarRequest site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive values stage fine index := by
  let row := DependentProduct.get parents.pieces values index
  let anchored := row.2.1.val
  let initial := row.2.2.1.val
  let value := row.2.2.2.1
  let prepared := row.2.2.2.2
  let actualParents := valueLayerOnCoverage site quarter parents coverage
  let actualIndex : Fin actualParents.pieces.length := ⟨index.val, by
    change index.val < (parents.transport (scalarQuarter_eq site quarter coverage)).pieces.length
    rewrite [parents.transport_count]
    exact index.isLt⟩
  let parent : {kept : Refinement.Piece (valueData site) coverage.leg.actual actualParents.accuracy //
      kept = actualParents.pieces[actualIndex.val]'actualIndex.isLt} :=
    ⟨initial, row.2.2.1.property⟩
  let layer := fine.2.layer actualIndex parent
  have spans := fine.2.layer_spans actualIndex parent
  have floor := parentPrecisionStage_covers site quarter coverage coarse bounds trace bank retained
    times sameTimes parents original modelFloor scalarFloor target positive values index
  have paid : (ScalarModels.Precision.taylor bounds (positive := positive) value).stage ≤ stage.val :=
    floor.trans_eq stage.property.symm
  let edge : Fin times.length := row.1.val
  let canonical : Fin (DyadicTrace.tail trace.budget.fine.selection.stage
      (0 : Fraction.Rational) 1).length :=
    ⟨edge.val, Nat.lt_of_lt_of_le edge.isLt (congrArg List.length sameTimes).le⟩
  let selected := valueLayerEdge site quarter trace.budget.fine.selection.stage 0 times sameTimes
    parents original index coverage
  have raw := selected.property.2 rfl
  have spanTimes : initial.span.lower = DyadicTrace.indexed 0 times edge.castSucc ∧
      initial.span.upper = DyadicTrace.indexed 0 times edge.succ := by
    constructor
    · exact (congrArg (fun piece : Refinement.Piece (valueData site) coverage.leg.actual actualParents.accuracy =>
          piece.span.lower) row.2.2.1.property).trans
        (raw.1.symm.trans (congrArg (fun edge : Fin times.length =>
          DyadicTrace.indexed 0 times edge.castSucc) row.1.property).symm)
    · exact (congrArg (fun piece : Refinement.Piece (valueData site) coverage.leg.actual actualParents.accuracy =>
          piece.span.upper) row.2.2.1.property).trans
        (raw.2.symm.trans (congrArg (fun edge : Fin times.length =>
          DyadicTrace.indexed 0 times edge.succ) row.1.property).symm)
  have leftReadback : DyadicTrace.indexed 0 times edge.castSucc = DyadicTrace.indexed 0
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.castSucc :=
    (Data.List.at_cast (congrArg (List.cons (0 : Fraction.Rational)) sameTimes) edge.castSucc).symm
  have rightReadback : DyadicTrace.indexed 0 times edge.succ = DyadicTrace.indexed 0
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.succ :=
    (Data.List.at_cast (congrArg (List.cons (0 : Fraction.Rational)) sameTimes) edge.succ).symm
  have spanCanonical : initial.span.lower = DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.castSucc ∧
      initial.span.upper = DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.succ :=
    ⟨spanTimes.1.trans leftReadback, spanTimes.2.trans rightReadback⟩
  have stepPositive : 0 < trace.budget.step := Arithmetic.mul_pos_direct
    (by decide +kernel : (0 : Fraction.Rational) < 1 - 0)
    (Arithmetic.pow_pos_direct (by decide +kernel) trace.budget.fine.selection.stage)
  have properCanonical : DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.castSucc <
      DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.succ :=
    Arithmetic.lt_of_sub_pos_direct
      (stepPositive.trans_eq (trace.budget.steps.indexed canonical).symm)
  let requests := ScalarModels.Precision.requests bounds (positive := positive) (initial := initial)
    (modelFloor := modelFloor) (scalarFloor := scalarFloor) (target := target) anchored value prepared
    (stage := ⟨stage.val, paid⟩) spanCanonical properCanonical layer spans
    (Specification.valueSpecification_denominatorPairs (parameter site) 0)
    (fun _ => (Basic.one_mul _).symm)
  have attained := ScalarModels.Precision.accurate bounds (positive := positive)
    (initial := initial) (prepared := prepared)
    (modelFloor := modelFloor) (scalarFloor := scalarFloor) (target := target) anchored value
    (stage := ⟨stage.val, paid⟩) spanCanonical layer spans requests
  let polynomial : CoefficientPolynomial :=
    (ScalarModels.Precision.models bounds (positive := positive) value).common.primitive.value
  let evaluate : Fraction.Rational → Canonical := fun time =>
    polynomial.eval (coordinate site (parameter site) 2 quarter (by decide +kernel) time)
  let sample : Canonical := layer.model.integralSample
  have scalarBound : Norm.Basic.normSq
      (evaluate (DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.succ) -
      evaluate (DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.castSucc) -
      sample) < target := attained
  have sameEndpoints : (initial.span.lower, initial.span.upper) =
      (DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.castSucc,
      DyadicTrace.indexed 0
        (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) canonical.succ) :=
    Prod.ext spanCanonical.1 spanCanonical.2
  have transported := congrArg (fun endpoints : Fraction.Rational × Fraction.Rational =>
    Norm.Basic.normSq (evaluate endpoints.2 - evaluate endpoints.1 - sample)) sameEndpoints
  have endpointBound := Eq.mpr (congrArg (fun amount : Fraction.Rational => amount < target) transported) scalarBound
  exact ⟨layer, ⟨requests, endpointBound, fine.2.layer_cells actualIndex parent⟩⟩

/-- Request all actual fine partition slices from the same retained original coarse-model bank.

The original product visits each bounded coarse occurrence once. Each
entry reads its stored anchor, initial Piece, model, selections and source,
then consumes the actual ordered partition cells at the same common stage.
Original product lookup prefix scans remain; no model or mesh is rebuilt.
-/
private def primitiveBankRequests (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive)
    (stage : {actual : Nat // actual = parentPrecisionStage site quarter coverage coarse bounds
      trace bank retained times sameTimes parents original modelFloor scalarFloor target positive values})
    (fine : ValueLayerRefinement site quarter coverage parents stage.val) :
    DependentProduct parents.pieces (fun index =>
      ParentScalarRequest site quarter coverage coarse bounds trace bank retained times sameTimes
        parents original modelFloor scalarFloor target positive values stage fine index) :=
  DependentProduct.ofFn parents.pieces (fun index =>
    primitiveBankScalarRequests site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive values stage fine index)

/-- The same complete parent plan, original fine scalar programme and its actual ordered coefficient-request bank. -/
private def RequestedScalarRefinement (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) : Type 1 :=
  Σ selected : (Σ values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive,
      {stage : Nat // stage = parentPrecisionStage site quarter coverage coarse bounds
        trace bank retained times sameTimes parents original modelFloor scalarFloor target positive values}),
  Σ fine : ValueLayerRefinement site quarter coverage parents selected.2.val,
    DependentProduct parents.pieces (fun index =>
      ParentScalarRequest site quarter coverage coarse bounds trace bank retained times sameTimes
        parents original modelFloor scalarFloor target positive selected.1 selected.2 fine index)

/-- Construct the retained common-stage scalar refinement and every actual per-parent coefficient request once.

One original parent plan and fine refinement are retained before producing
requests. Every request's same-model boundary bound and whole numerical
slice readback concern that supplied fine programme. This does not yet sum
the parent boundaries or compare an unrelated spatial integral programme.
-/
private def primitiveBankRequestedRefinement (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    RequestedScalarRefinement site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive :=
  let completed := primitiveBankRefinement site quarter coverage coarse bounds trace bank retained times sameTimes
    parents original modelFloor scalarFloor target positive
  let requests := primitiveBankRequests site quarter coverage coarse bounds trace bank retained times sameTimes
    parents original modelFloor scalarFloor target positive completed.1.1 completed.1.2 completed.2
  ⟨completed.1, completed.2, requests⟩

/-- Evaluate the same retained common primitive at its actual original parent endpoints.

The whole model and initial Piece are supplied caches at the same bounded
coarse occurrence. This operation reads those values; it constructs no new
primitive, model, root, Reading, reference or numerical observation.
-/
private def parentBoundary (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (index : Fin parents.pieces.length)
    (row : ParentPrecision site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original index modelFloor scalarFloor target positive) : Canonical :=
  let model := ScalarModels.Precision.models bounds (positive := positive) row.2.2.2.1
  model.common.primitive.value.eval
      (coordinate site (parameter site) 2 quarter (by decide +kernel) row.2.2.1.val.span.upper) -
    model.common.primitive.value.eval
      (coordinate site (parameter site) 2 quarter (by decide +kernel) row.2.2.1.val.span.lower)

/-- Actual retained parent requests bound the original whole fine scalar programme at their genuine count-squared cost.

The actual ordered numerical cell slices sum to the supplied fine model.
An exact original dimension cast preserves each coarse ordinal after whole
quarter transport. Original finite Gaussian Cauchy and the stored per-parent
requests then bound the sum of the same common-primitive boundaries.
-/
private theorem primitiveBank_scalar_error_le (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (values : ParentPrecisions site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive)
    (stage : {actual : Nat // actual = parentPrecisionStage site quarter coverage coarse bounds
      trace bank retained times sameTimes parents original modelFloor scalarFloor target positive values})
    (fine : ValueLayerRefinement site quarter coverage parents stage.val)
    (requests : DependentProduct parents.pieces (fun index =>
      ParentScalarRequest site quarter coverage coarse bounds trace bank retained times sameTimes
        parents original modelFloor scalarFloor target positive values stage fine index)) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index : Fin parents.pieces.length =>
        parentBoundary site quarter coverage coarse bounds trace bank retained times sameTimes
          parents original modelFloor scalarFloor target positive index
            (DependentProduct.get parents.pieces values index)) -
      ((valuePiece site quarter).program.model
        (trace.budget.fine.selection.stage + stage.val)).integralSample) ≤
      (parents.pieces.length : Fraction.Rational) ^ 2 * target := by
  let boundary := fun index : Fin parents.pieces.length =>
    parentBoundary site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive index
        (DependentProduct.get parents.pieces values index)
  let samples := fun index : Fin parents.pieces.length =>
    (DependentProduct.get parents.pieces requests index).1.model.integralSample
  have per : ∀ index : Fin parents.pieces.length,
      Norm.Basic.normSq (boundary index - samples index) ≤ target := by
    intro index
    have attained := (DependentProduct.get parents.pieces requests index).2.property.1.le
    simpa only [boundary, samples, parentBoundary] using attained
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le
    (fun index : Fin parents.pieces.length => boundary index - samples index) target per
  rewrite [FiniteSum.Fin.sumFin_sub] at estimate
  let actualParents := valueLayerOnCoverage site quarter parents coverage
  have countEqual : actualParents.pieces.length = parents.pieces.length :=
    parents.transport_count (scalarQuarter_eq site quarter coverage)
  let blocks := fun index : Fin actualParents.pieces.length =>
    (PathModel.mk (fine.2.get index).2.val).integralSample
  have readback : ∀ index : Fin parents.pieces.length,
      samples index = blocks (Fin.cast countEqual.symm index) := by
    intro index
    exact congrArg (fun cells : List CellModel => (PathModel.mk cells).integralSample)
      (DependentProduct.get parents.pieces requests index).2.property.2
  have grouped : FiniteSum.Fin.sumFin samples = fine.1.val.model.integralSample :=
    (FiniteSum.Fin.sumFin_congr readback).trans
      ((FiniteSum.Fin.sumFin_cast countEqual.symm blocks).trans fine.2.integralSample_eq_sum.symm)
  have programme := congrArg (fun model : PathModel => model.integralSample) fine.1.property.2
  rewrite [grouped, programme] at estimate
  exact estimate

/-- The original requested common-stage scalar refinement with its internally paid whole-quarter boundary bound. -/
private def QuarterScalarRefinement (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) : Type 1 :=
  let perTarget := Budget.Weighted.allowance (target / 2) ((parents.pieces.length : Fraction.Rational) ^ 2)
  let perPositive := Budget.Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
    (Arithmetic.sq_nonneg_direct (parents.pieces.length : Fraction.Rational))
  {completed : RequestedScalarRefinement site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor perTarget perPositive //
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index : Fin parents.pieces.length =>
        parentBoundary site quarter coverage coarse bounds trace bank retained times sameTimes
          parents original modelFloor scalarFloor perTarget perPositive index
            (DependentProduct.get parents.pieces completed.1.1 index)) -
      ((valuePiece site quarter).program.model
        (trace.budget.fine.selection.stage + completed.1.2.val)).integralSample) < target}

/-- Compute every actual coefficient/scalar stage needed to meet an arbitrary whole-quarter squared-error request.

The real original coarse count determines one weighted positive per-parent
allowance. One original retained-model/fine-mesh/request producer pays that
allowance. Its actual finite sum is below the supplied global target; the
original scalar programme remains the numerical comparison channel.
-/
private def primitiveBankQuarterRequest (trace : EntryTrace site quarter coverage coarse bounds)
    (bank : {actual : Entries trace.moves // actual = Parallel.OwnerMoves.entries trace.moves})
    {count : Nat} (retained : Entries.Primitives bounds bank.val count)
    (times : List Fraction.Rational)
    (sameTimes : times = DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (parents : Refinement.Layer (valuePiece site quarter) trace.budget.fine.selection.stage)
    (original : parents = (valuePiece site quarter).layerAt trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    QuarterScalarRefinement site quarter coverage coarse bounds trace bank retained times sameTimes
      parents original modelFloor scalarFloor target positive := by
  let weight : Fraction.Rational := (parents.pieces.length : Fraction.Rational) ^ 2
  have nonnegative : 0 ≤ weight := Arithmetic.sq_nonneg_direct _
  have halfPositive : 0 < target / 2 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let perTarget := Budget.Weighted.allowance (target / 2) weight
  have perPositive : 0 < perTarget := Budget.Weighted.allowance_positive halfPositive nonnegative
  let completed := primitiveBankRequestedRefinement site quarter coverage coarse bounds trace bank retained
    times sameTimes parents original modelFloor scalarFloor perTarget perPositive
  have summed := primitiveBank_scalar_error_le site quarter coverage coarse bounds trace bank retained
    times sameTimes parents original modelFloor scalarFloor perTarget perPositive
      completed.1.1 completed.1.2 completed.2.1 completed.2.2
  have paid : weight * perTarget ≤ target / 2 :=
    Budget.Weighted.mul_allowance_le halfPositive.le nonnegative
  exact ⟨completed, (summed.trans paid).trans_lt (Fraction.Order.Field.half_lt_self positive)⟩

end ParentPrecisions

end ScalarLayer

end EntryBank

/-- The actual capped construction retains the entire supplied source attachment. -/
theorem primitive_owner_source (site : Fin 2) (quarter : UnitCircuitQuarter) :
    (primitiveOwnerTrace site quarter).source = (spatial site quarter).source :=
  (primitiveOwnerTrace site quarter).source_eq

/-- The actual capped owner trace still names the same original signed scalar-quarter target.

The original target comparison is constructed by the same retained move and
residual machinery at the stronger request. This checks the nondefault cap
against the original circuit owner and numerical name without executing the
full selected mesh or identifying a different path integral.
-/
def primitive_owner_target (site : Fin 2) (quarter : UnitCircuitQuarter) :
    NamedEquivalent
      (((primitiveOwnerTrace site quarter).finishAtTarget).certificate
        ((primitiveOwnerTrace site quarter).finishAtTarget).parameterNonzero).value.name
      ((circuit site).leg quarter).target.lift.value.name :=
  Gaussian.Equivalence.NamedEquivalent.transport rfl
    (congrArg (fun leg : Radial.Transport.Leg site (parameter site) quarter => leg.target.lift.value.name)
      (spatial site quarter).leg_eq)
    (primitiveOwnerTrace site quarter).targetAgreement

end TestPurelib.Curves.Legendre.ParallelDifferential
