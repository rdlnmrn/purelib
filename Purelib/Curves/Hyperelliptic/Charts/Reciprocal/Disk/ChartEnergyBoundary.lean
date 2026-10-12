module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

public section

/-!
# Odd fan energy compared with the original primitive path

The refined cap boundary is compared with the full retained chart area,
then with the original source-comparison polygon. Both primitive endpoint
and radial endpoint terms remain explicit until physical boundary gluing.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation (RequestedEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)

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
  original stage}

/-- The reversed actual cap-edge area sum is the negative complete primitive trace area along the retained
root-coordinate chain. -/
private theorem reverse_trace (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segments : List (VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage))
    {first last : InverseRootPolynomial.Gaussian} (chain : Segment.From first segments last) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (segments.map (fun segment =>
      Purelib.Integration.Path.BoundaryRibbon.area segment.last.chartValue segment.first.chartValue)) =
      -IncrementArea.traceArea (capSample.primitive.value.eval first) (segments.map Segment.chartIncrement) := by
  induction segments generalizing first with
  | nil => change 0 = -0; ring1
  | cons head tail ih =>
      change first = head.first.root.coordinate ∧ Segment.From head.last.root.coordinate tail last at chain
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, IncrementArea.traceArea]
      rw [ih chain.2, chain.1, head.chart_eq]
      have firstValue : head.first.chartValue = capSample.primitive.value.eval head.first.root.coordinate := by
        have value := head.first.chart_eq
        rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
        exact value
      have lastValue : head.last.chartValue = capSample.primitive.value.eval head.last.root.coordinate := by
        have value := head.last.chart_eq
        rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
        exact value
      rw [← firstValue, ← lastValue, show head.first.chartValue + (head.last.chartValue - head.first.chartValue) =
        head.last.chartValue by ring1]
      have reverse : BoundaryRibbon.area head.last.chartValue head.first.chartValue = -BoundaryRibbon.area
        head.first.chartValue head.last.chartValue := by
        unfold BoundaryRibbon.area; ring1
      rw [reverse]
      ring1

/-- The reversed retained chart-edge area sum equals the negative full chart polygon area minus its actual endpoint
chord. -/
theorem reversed_chart_area (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.vertices.path.segments.map (fun segment =>
      BoundaryRibbon.area segment.last.chartValue segment.first.chartValue)) =
      -evaluated.vertices.path.chart.area - BoundaryRibbon.area evaluated.vertices.first.chartValue
        evaluated.vertices.last.chartValue := by
  have trace := reverse_trace
    branch evaluated.vertices.path.segments evaluated.vertices.path.chain
  rw [← evaluated.vertices.path.chartPath_eq] at trace
  have firstValue : evaluated.vertices.first.chartValue = capSample.primitive.value.eval
    evaluated.vertices.first.root.coordinate := by
    have value := evaluated.vertices.first.chart_eq
    rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
    exact value
  rw [← firstValue, IncrementArea.traceArea_eq, ← evaluated.vertices.path.chart.area_eq,
    ← evaluated.vertices.path.chart.total_eq, evaluated.vertices.path.chart_total, BoundaryRibbon.area_sub_self_right]
      at trace
  exact trace.trans (by ring1)

namespace RequestedEnergy

variable {energyTarget : Coordinate} {energyFloor : Nat}

/-- The actual energy surface is compared with the existing chart polygon, including its primitive offset and the two
uncancelled radial sides. -/
theorem chart_boundary_close (energy : Evaluation.RequestedEnergy evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (energy.area - (-evaluated.vertices.path.chart.area -
      BoundaryRibbon.area evaluated.vertices.first.chartValue evaluated.vertices.last.chartValue +
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.last.root.coordinate -
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.first.root.coordinate)) < target := by
  have mapped := congrArg (List.map (fun segment => RootRadialGeometry.arcArea capSample.primitive.value.eval
    energy.request.depth
    segment.last.root.coordinate segment.first.root.coordinate)) energy.segments_eq
  simp only [Data.List.Map.map_map, Function.comp_def] at mapped
  have bound := Evaluation.refined_arc_error evaluated branch energy.request.depth
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary.AreaRequest.Evaluation.reversed_chart_area
    evaluated branch] at bound
  rw [energy.boundary, mapped]
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt bound
  ring1

/-- The same finite energy surface now has a paid comparison with the original cap-comparison path, retaining all
endpoint terms. -/
theorem source_boundary_close (energy : Evaluation.RequestedEnergy evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (energy.area - (-original.capSummary.area -
      BoundaryRibbon.area evaluated.vertices.first.chartValue evaluated.vertices.last.chartValue +
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.last.root.coordinate -
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.first.root.coordinate)) < 4 * target := by
  let endpoints := -BoundaryRibbon.area evaluated.vertices.first.chartValue evaluated.vertices.last.chartValue +
    RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
      evaluated.vertices.last.root.coordinate -
    RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
      evaluated.vertices.first.root.coordinate
  have chart : Data.Gaussian.Norm.Basic.normSq (energy.area - (-evaluated.vertices.path.chart.area +
    endpoints)) < target := by
    refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt
      (chart_boundary_close
      energy branch)
    dsimp only [endpoints]
    ring1
  have difference : Data.Gaussian.Norm.Basic.normSq ((-evaluated.vertices.path.chart.area + endpoints) -
    (-original.capSummary.area + endpoints)) < target := by
    exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1 : (-evaluated.vertices.path.chart.area +
      endpoints) - (-original.capSummary.area + endpoints) =
      original.capSummary.area - evaluated.vertices.path.chart.area)).trans_lt evaluated.area_error
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via energy.area (-evaluated.vertices.path.chart.area +
    endpoints) (-original.capSummary.area + endpoints)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct chart difference))
  have normalized : Data.Gaussian.Norm.Basic.normSq (energy.area - (-original.capSummary.area + endpoints)) < 4
    * target := estimate.trans_eq (by ring1)
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt normalized
  dsimp only [endpoints]
  ring1

/-- Transfer the signed energy bound to the original cap-comparison polygon once its squared area allowance is paid by a
linear energy budget. -/
theorem source_lower (energy : Evaluation.RequestedEnergy evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (budget : InverseRootPolynomial.Coordinate) (nonnegative :
      0 ≤ budget)
    (paid : 4 * target ≤ (4 * budget) ^ 2) :
    -energyTarget - budget < (-original.capSummary.area -
      BoundaryRibbon.area evaluated.vertices.first.chartValue evaluated.vertices.last.chartValue +
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.last.root.coordinate -
      RootRadialGeometry.radialArea capSample.primitive.value.eval energy.request.depth
        evaluated.vertices.first.root.coordinate).im / 4 := by
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le energy.area _ budget nonnegative

      ((source_boundary_close
      energy branch).le.trans paid)
  have lower := Fraction.Order.Arithmetic.add_lt_add_right_direct energy.lower (-budget)
  exact (show -energyTarget - budget = -energyTarget + -budget by ring1).trans_lt (lower.trans_le comparison)

end RequestedEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary
