module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
import Purelib.Riemann.RootContinuation.RootRadialEnergy
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Energy

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.RadialTriangles

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.RootRadialEnergy

open Purelib.Riemann.RootContinuation.RootRadialRefinement

public section

/-!
# Requested odd cap energy on the retained chart path

Every genuine root edge of the existing chart evaluation is filled in cap
orientation. A single polynomial-bound cache and parameter mesh are shared
by all its fans. Their complete computed error sum meets the request, and
internal radial boundaries cancel using the original root-coordinate chain.
Cell, parent, and closing joins remain separate signed contributions.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (domain arcArea radialArea)
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)
open Purelib.Riemann.RootContinuation.RootRadialEnergy (PolynomialSample)
open Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation (coordinate_norm_upper)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

namespace AreaRequest.Evaluation

variable {evaluated : Evaluation charts
  original stage} {energyDepth : Nat}
  {parameters : Parameters energyDepth} {radius :
    Coordinate}

set_option genInjectivity false in
/-- A finite radial refinement and polynomial energy sample on one actual retained cap-path segment.

The segment keeps its original path membership; the radial refinement follows its retained endpoint coordinates in the
cap orientation. -/
structure ArcEnergy (evaluated : AreaRequest.Evaluation charts original stage)
    (parameters : RadialTriangles.Parameters energyDepth) (radius : InverseRootPolynomial.Coordinate) where
  /-- The actual retained chart-path segment whose radial contribution is sampled. -/ segment : VertexPaths.Segment
    regular owners.model original.sample request.tolerance floor stage
  /-- This exact segment occurs in the original retained chart path. -/ member : segment ∈
    evaluated.vertices.path.segments
  /-- The cached radial refinement on the segment's actual last and first root coordinates. -/ refinement :
    RootRadialRefinement.Refinement segment.last.root.coordinate segment.first.root.coordinate parameters
  /-- The polynomial energy sample on this exact retained radial refinement and cap sample. -/ polynomial :
    RootRadialEnergy.PolynomialSample refinement capSample radius

constructive_injectivity ArcEnergy

namespace ArcEnergy

/-- Construct the radial refinement from the actual retained segment coordinates and certify its polynomial energy
sample using their original bounds. -/
@[expose] def build (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) (radius : InverseRootPolynomial.Coordinate) (positive : 0 <
      radius)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy evaluated parameters
      radius := by
  have bounded {parameter : InverseRootPolynomial.Coordinate}
      (reading : VertexRequests.Reading regular owners.model original.sample parameter request.tolerance floor stage) :
        Data.Gaussian.Norm.Basic.normSq reading.root.coordinate ≤ 2 := by
    have square := reading.square
    rw [branch, pow_one, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at square
    have unit := Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve
      (data.boundary.point ⟨edge.left.inside.1.trans reading.prepared.inside.1,
        reading.prepared.inside.2.trans edge.right.inside.2⟩))
    rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at unit
    have scalar := ReciprocalDiskCoordinateOrientation.coordinate_norm_upper unit request.small square
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  let refinement := Refinement.build (bounded segment.last) (bounded segment.first)
    (evaluated.coordinate_area_positive branch oriented segment member).le parameters
  exact ⟨segment, member, refinement, PolynomialSample.build refinement capSample radius positive⟩

/-- Build one retained radial energy sample for every supplied original segment occurrence. -/
@[expose] def buildMany (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) (radius : InverseRootPolynomial.Coordinate) (positive : 0 <
      radius) :
    (segments : List (VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)) →
    (∀ segment ∈ segments, segment ∈ evaluated.vertices.path.segments) → List
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy evaluated parameters
      radius)
  | [], _ => []
  | segment :: segments, within =>
      build evaluated branch
        oriented parameters radius positive segment (within segment List.mem_cons_self) ::
        buildMany
          evaluated branch oriented parameters radius positive segments
          (fun other member => within other (List.mem_cons_of_mem segment member))

/-- The constructed energy entries project to exactly the supplied ordered list of actual segments. -/
theorem buildMany_segments (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) (radius : InverseRootPolynomial.Coordinate) (positive : 0 <
      radius) :
    (segments : List (VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)) →
    (within : ∀ segment ∈ segments, segment ∈ evaluated.vertices.path.segments) →
    (buildMany evaluated branch
      oriented parameters radius positive segments within).map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.segment = segments
  | [], _ => rfl
  | segment :: segments, within => congrArg (List.cons segment)

        (buildMany_segments
        evaluated branch oriented parameters radius positive segments
        (fun other member => within other (List.mem_cons_of_mem segment member)))

/-- The negative sum of retained local error budgets bounds one quarter of the imaginary total boundary area. -/
theorem sum_lower (entries : List
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy evaluated parameters
  radius)) :
    -Squares.coordinateSum (entries.map (fun entry => entry.polynomial.surface.errorBudget)) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
        entry.polynomial.surface.boundaryArea))).im / 4 := by
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Coordinate) ≤ 0 / 4; decide
  | cons head tail ih =>
      have bound := Fraction.Order.Arithmetic.add_le_add_direct head.polynomial.lower ih
      simp only [List.map_cons, Squares.coordinateSum, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Data.Gaussian.Basic.add_im]
      exact (by ring1 : -(head.polynomial.surface.errorBudget + Squares.coordinateSum (tail.map (fun entry =>
        entry.polynomial.surface.errorBudget))) =
        -head.polynomial.surface.errorBudget + -Squares.coordinateSum (tail.map (fun entry =>
          entry.polynomial.surface.errorBudget))).trans_le
          (bound.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))

/-- The summed actual local errors satisfy the common coefficient and epsilon ceiling multiplied by the retained entry
count. -/
theorem errors_le (bounds : Cap.EnergyBounds capSample RootRadialGeometry.domain)
    {number : Nat} {energyTarget : InverseRootPolynomial.Coordinate} {energyFloor : Nat}
    (energyRequest : Cap.EnergyRequest bounds number energyTarget energyFloor)
    {parameters : RadialTriangles.Parameters energyRequest.depth}
    (entries : List (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy evaluated
      parameters energyRequest.radius)) :
    Squares.coordinateSum (entries.map (fun entry => entry.polynomial.surface.errorBudget)) ≤
      (entries.length : InverseRootPolynomial.Coordinate) * (128 * (2 * bounds.coefficient + 4) * energyRequest.epsilon)
        := by
  induction entries with
  | nil => change 0 ≤ 0 * _; rw [Fraction.Field.zero_mul_direct]
  | cons head tail ih =>
      have bound := Fraction.Order.Arithmetic.add_le_add_direct (head.polynomial.error_le bounds energyRequest) ih
      simp only [List.map_cons, Squares.coordinateSum, List.length_cons, Nat.cast_succ]
      exact bound.trans_eq (by ring1)

/-- The original coordinate chain cancels every internal radial side, even when a root's two appearances came from
different recursive branches. -/
theorem boundary_sum (entries : List
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy evaluated parameters
  radius)) {first last : InverseRootPolynomial.Gaussian}
    (chain : Segment.From first (entries.map
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.segment) last) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.polynomial.surface.boundaryArea)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => RootRadialGeometry.arcArea
        capSample.primitive.value.eval energyDepth
        entry.segment.last.root.coordinate entry.segment.first.root.coordinate)) +
      RootRadialGeometry.radialArea capSample.primitive.value.eval energyDepth last -
      RootRadialGeometry.radialArea capSample.primitive.value.eval energyDepth first := by
  induction entries generalizing first with
  | nil => change first = last at chain; rw [chain]; change 0 = 0 + _ - _; ring1
  | cons head tail ih =>
      change first = head.segment.first.root.coordinate ∧ Segment.From head.segment.last.root.coordinate (tail.map
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.segment) last at chain
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      rw [head.polynomial.boundary_eq_arcs, ih chain.2, chain.1]
      ring1

end ArcEnergy

set_option genInjectivity false in
/-- A paid finite radial-energy evaluation on every actual segment of the original chart path.

The request retains its coefficient bounds, refinement parameters and complete entry list; exact count, area and error
caches include the endpoint radial correction. -/
structure RequestedEnergy (evaluated : AreaRequest.Evaluation charts original stage) (energyTarget :
  InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The cached coefficient and model bounds on the original cap radial domain. -/ bounds : Cap.EnergyBounds
    capSample RootRadialGeometry.domain
  /-- The retained accuracy request using the actual segment count, target and stage floor. -/ request :
    Cap.EnergyRequest bounds evaluated.vertices.path.segments.length energyTarget energyFloor
  /-- The cached radial-triangle parameters at the retained request depth. -/ parameters : RadialTriangles.Parameters
    request.depth
  /-- The ordered cached energy samples on the actual original path segments. -/ entries : List
    (ArcEnergy evaluated parameters
    request.radius)
  /-- The retained entries project exactly to the original ordered segment list. -/ segments_eq : entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.segment =
    evaluated.vertices.path.segments
  /-- The cached total number of retained radial triangles. -/ count : Nat
  /-- The cached count equals the actual entry count times the retained refinement leaf count. -/ count_eq : count =
    entries.length * (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length
  /-- The cached count is the original segment count times the explicit doubled fourth-power subdivision count. -/
    count_refined : count = evaluated.vertices.path.segments.length * (2 * 4 ^ request.depth)
  /-- The cached sum of actual retained radial boundary areas. -/ area : InverseRootPolynomial.Gaussian
  /-- The area cache equals the Gaussian sum of these exact entries' boundary areas. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.polynomial.surface.boundaryArea))
  /-- The cached sum of actual retained local energy errors. -/ error : InverseRootPolynomial.Coordinate
  /-- The error cache equals the coordinate sum of these exact local error budgets. -/ error_eq : error =
    Squares.coordinateSum (entries.map (fun entry => entry.polynomial.surface.errorBudget))
  /-- The actual cached error is at most the retained request's total error budget. -/ error_le : error ≤ request.total
  /-- The cached total error is strictly below the original requested energy target. -/ error_lt : error < energyTarget
  /-- The negative original energy target strictly bounds one quarter of the cached area's imaginary part. -/ lower :
    -energyTarget < area.im / 4
  /-- The cached radial boundary sum equals the actual path arc sum plus its retained last-minus-first radial
    correction. -/ boundary : area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
    RootRadialGeometry.arcArea capSample.primitive.value.eval request.depth
      entry.segment.last.root.coordinate entry.segment.first.root.coordinate)) +
    RootRadialGeometry.radialArea capSample.primitive.value.eval request.depth evaluated.vertices.last.root.coordinate -
    RootRadialGeometry.radialArea capSample.primitive.value.eval request.depth evaluated.vertices.first.root.coordinate

constructive_injectivity RequestedEnergy

namespace RequestedEnergy

/-- Reuse the supplied energy bounds, paid request and refinement parameters to cache all actual segment samples and
their exact finite sums. -/
@[expose] def buildWithRequest (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    {energyTarget : InverseRootPolynomial.Coordinate} {energyFloor : Nat}
    (bounds : Cap.EnergyBounds capSample RootRadialGeometry.domain)
    (request : Cap.EnergyRequest bounds evaluated.vertices.path.segments.length energyTarget energyFloor)
    (parameters : RadialTriangles.Parameters request.depth) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated
      energyTarget energyFloor := by
  let entries := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.buildMany
    evaluated branch oriented parameters request.radius request.radius_positive
    evaluated.vertices.path.segments (fun _ member => member)
  have segments :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.buildMany_segments
    evaluated branch oriented parameters request.radius request.radius_positive
    evaluated.vertices.path.segments (fun _ member => member)
  have length : entries.length = evaluated.vertices.path.segments.length := by
    have same := congrArg List.length segments
    rw [Data.List.Map.length_map] at same
    exact same
  let area := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
    entry.polynomial.surface.boundaryArea))
  let error := Squares.coordinateSum (entries.map (fun entry => entry.polynomial.surface.errorBudget))
  have bounded : error ≤ request.total := by
    have estimate := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.errors_le
      bounds request entries
    rw [length] at estimate
    exact estimate.trans_eq (by rw [request.total_eq, request.scale_eq]; ring1)
  have accurate : error < energyTarget := bounded.trans_lt request.accurate
  have chain : Segment.From evaluated.vertices.first.root.coordinate (entries.map
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.segment)
      evaluated.vertices.last.root.coordinate := segments.symm ▸ evaluated.vertices.path.chain
  have countEq : entries.length * (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length =
      evaluated.vertices.path.segments.length * (2 * 4 ^ request.depth) := by
    rw [length, parameters.mesh.faceCount_eq]
  exact ⟨bounds, request, parameters, entries, segments,
    entries.length * (PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length, rfl, countEq,
      area, rfl, error, rfl,
    bounded, accurate, (Fraction.Order.Arithmetic.neg_lt_neg_direct accurate).trans_le
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.sum_lower entries),
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.ArcEnergy.boundary_sum entries chain⟩

/-- Construct the radial refinement from the actual retained segment coordinates and certify its polynomial energy
sample using their original bounds. -/
@[expose] def build (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated
      energyTarget energyFloor :=
  let bounds := EnergyBounds.build capSample RootRadialGeometry.domain
  let request := EnergyRequest.build bounds evaluated.vertices.path.segments.length energyTarget positive energyFloor
  buildWithRequest
    evaluated branch oriented bounds request (Parameters.build request.depth)

end RequestedEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
