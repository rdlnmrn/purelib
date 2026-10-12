module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
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
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Gluing the energies of actual neighbouring odd cap charts

Both fans use one cached polynomial bound and one radial mesh, while retaining
their independently selected root-reading stages. The existing
join request controls their retained endpoint readings, so the internal
radial terms cancel with a paid error. The reference is the complete chart
path with its actual connecting edge, including both cells' excursions.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count otherCount : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent otherParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {otherPatch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
  {cell : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {otherCell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge}
  {owners : Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {otherOwners : Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular otherCell}
  {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {otherComparison :
    Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular otherCell}
  {target otherTarget : Normalization.InverseRootPolynomial.Coordinate} {floor otherFloor joinFloor : Nat}
  {index depth otherDepth stage otherStage minimum otherMinimum : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index} {otherSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive otherData index}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target floor}
    {otherRequest : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest otherComparison otherOwners
    otherTarget otherFloor}
  {charts : Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh request.mesh capSample minimum} {otherCharts :
    Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh otherRequest.mesh capSample otherMinimum}
  {original : Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample depth}
  {otherOriginal : Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell otherComparison otherSource capSample
    otherDepth}
  {joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join owners.last otherOwners.first}

namespace AreaRequest.Evaluation

/-- Owner transport changes only the dependent view of each cached reading.
Containment comes from its actual chart-square certificate. -/
theorem join_radial_close (first : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts
  original stage) (last : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation otherCharts
  otherOriginal otherStage)
    {joinTarget : Normalization.InverseRootPolynomial.Coordinate}
    (joinRequest : Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request owners.bounds.last joined joinTarget
      joinFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : joinRequest.index
      ≤ stage) (otherLater : joinRequest.index ≤ otherStage) (energyDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval
      energyDepth last.vertices.first.root.coordinate -
      RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energyDepth
        first.vertices.last.root.coordinate -
      Path.BoundaryRibbon.area first.vertices.last.chartValue last.vertices.first.chartValue) < joinTarget := by
  let left := Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual first.last_owner
    first.vertices.last.root
  let right := Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual last.first_owner
    last.vertices.first.root
  have leftEq : left.reading.coordinate = first.vertices.last.root.coordinate :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
  have rightEq : right.reading.coordinate = last.vertices.first.root.coordinate :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq _ _
  have leftInside := Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest.Evaluation.square_inside
    request branch first.vertices.last
  have rightInside := Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest.Evaluation.square_inside
    otherRequest branch last.vertices.first
  rw [← leftEq] at leftInside
  rw [← rightEq] at rightInside
  have close := joinRequest.radial_accurate left.reading right.reading branch leftInside rightInside later otherLater
    energyDepth
  rw [leftEq, rightEq] at close
  have leftValue : first.vertices.last.chartValue = capSample.primitive.value.eval first.vertices.last.root.coordinate
    := by
    have value := first.vertices.last.chart_eq
    rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
    exact value
  have rightValue : last.vertices.first.chartValue = capSample.primitive.value.eval last.vertices.first.root.coordinate
    := by
    have value := last.vertices.first.chart_eq
    rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
    exact value
  rw [leftValue, rightValue]
  exact close

set_option genInjectivity false in
/-- Two retained neighbouring chart energies computed at one shared radial depth.

Keep the full original chart paths, their actual connecting edge, the finite area summary and the combined strict lower
bound. -/
structure JoinedEnergy (first : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts
  original stage) (last : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation otherCharts
  otherOriginal otherStage)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The actual retained fan energy of the first chart. -/ firstEnergy :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy first energyTarget
    energyFloor
  /-- The actual retained fan energy of the second chart. -/ lastEnergy :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy last energyTarget
    energyFloor
  /-- The common radial subdivision depth of both retained fan computations. -/ depth : Nat
  /-- The first original fan uses the retained shared depth. -/ first_depth : firstEnergy.request.depth = depth
  /-- The second original fan uses the retained shared depth. -/ last_depth : lastEnergy.request.depth = depth
  /-- The complete joined increment path including the original chart connector. -/ paths : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained path is exactly the first chart, actual endpoint connector and second chart in order. -/ paths_eq :
    paths = first.vertices.path.chartPath ++
    (last.vertices.first.chartValue - first.vertices.last.chartValue) :: last.vertices.path.chartPath
  /-- The finite area summary of that exact retained joined path. -/ polygon : Path.IncrementArea.Summary paths
  /-- The retained sum of both actual fan energies. -/ energy : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained energy is exactly the first fan energy plus the second. -/ energy_eq : energy = firstEnergy.area +
    lastEnergy.area
  /-- The imaginary part of the retained combined energy divided by four exceeds minus twice the energy target. -/ lower
    : -(2 * energyTarget) < energy.im / 4

constructive_injectivity JoinedEnergy

namespace JoinedEnergy

/-- Both depth searches are cheap and precede all fan generation. The bound
cache and final parameter mesh are shared by the two actual cells. -/
@[expose] def build (first : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts
  original stage) (last : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation otherCharts
  otherOriginal otherStage)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (firstOriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (lastOriented : 0 < Energy.AffineTriangle.crossEnergy (otherParent.edge.point 0) (otherParent.edge.point 1))
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.JoinedEnergy first last energyTarget
      energyFloor := by
  let bounds := Cap.EnergyBounds.build capSample
    RootContinuation.RootRadialGeometry.domain
  let firstRequest := Cap.EnergyRequest.build bounds
    first.vertices.path.segments.length energyTarget positive energyFloor
  let lastRequest := Cap.EnergyRequest.build bounds
    last.vertices.path.segments.length energyTarget positive energyFloor
  let depth := max firstRequest.depth lastRequest.depth
  let parameters := Path.Dyadic.RadialTriangles.Parameters.build depth
  let firstEnergy :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy.buildWithRequest first
    branch firstOriented bounds
    (firstRequest.atDepth depth (Data.Nat.Order.le_max_left _ _)) parameters
  let lastEnergy :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy.buildWithRequest last branch
    lastOriented bounds
    (lastRequest.atDepth depth (Data.Nat.Order.le_max_right _ _)) parameters
  let paths := first.vertices.path.chartPath ++
    (last.vertices.first.chartValue - first.vertices.last.chartValue) :: last.vertices.path.chartPath
  have lower := Fraction.Order.Arithmetic.add_lt_add_direct firstEnergy.lower lastEnergy.lower
  refine ⟨firstEnergy, lastEnergy, depth, rfl, rfl, paths, rfl, Path.IncrementArea.Summary.build paths,
    firstEnergy.area + lastEnergy.area, rfl, ?_⟩
  exact (by ring1 : -(2 * energyTarget) = -energyTarget + -energyTarget).trans_lt
    (lower.trans_eq (by rw [Gaussian.Basic.add_im]; simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))

variable {first : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts original stage}
  {last : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation otherCharts otherOriginal
  otherStage}
  {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}

/-- The joined trace area equals both original chart areas, endpoint terms and the actual connecting edge area. -/
theorem trace_eq (energy : Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.JoinedEnergy
  first last energyTarget energyFloor) :
    Path.IncrementArea.traceArea first.vertices.first.chartValue energy.paths =
      first.vertices.path.chart.area + Path.BoundaryRibbon.area first.vertices.first.chartValue
        first.vertices.last.chartValue +
      Path.BoundaryRibbon.area first.vertices.last.chartValue last.vertices.first.chartValue +
      last.vertices.path.chart.area + Path.BoundaryRibbon.area last.vertices.first.chartValue
        last.vertices.last.chartValue := by
  rw [energy.paths_eq, Path.IncrementArea.traceArea_append,
    ← first.vertices.path.chart.total_eq, first.vertices.path.chart_total,
    show first.vertices.first.chartValue + (first.vertices.last.chartValue - first.vertices.first.chartValue) =
      first.vertices.last.chartValue by ring1, Path.IncrementArea.traceArea,
    show first.vertices.last.chartValue + (last.vertices.first.chartValue - first.vertices.last.chartValue) =
      last.vertices.first.chartValue by ring1,
    Path.IncrementArea.traceArea_eq, Path.IncrementArea.traceArea_eq,
    ← first.vertices.path.chart.area_eq, ← last.vertices.path.chart.area_eq,
    ← first.vertices.path.chart.total_eq, ← last.vertices.path.chart.total_eq,
    first.vertices.path.chart_total, last.vertices.path.chart_total,
    Path.BoundaryRibbon.area_sub_self_right, Path.BoundaryRibbon.area_sub_self_right]
  ring1

/-- The connector closes precisely the gap between the two cached paths. -/
theorem polygon_total (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.JoinedEnergy first last energyTarget
  energyFloor) :
    energy.polygon.total = last.vertices.last.chartValue - first.vertices.first.chartValue := by
  rw [energy.polygon.total_eq, energy.paths_eq, Path.IncrementArea.sum_append]
  change _ + ((_ - _) + _) = _
  rw [← first.vertices.path.chart.total_eq, ← last.vertices.path.chart.total_eq,
    first.vertices.path.chart_total, last.vertices.path.chart_total]
  ring1

/-- Only the two exterior radial sides survive. The reference retains the
actual joining edge and every increment of both original chart paths. -/
theorem boundary_close (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.JoinedEnergy first last energyTarget
  energyFloor)
    (joinRequest : Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request owners.bounds.last joined target
      joinFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : joinRequest.index
      ≤ stage) (otherLater : joinRequest.index ≤ otherStage) :
    Data.Gaussian.Norm.Basic.normSq (energy.energy - (-Path.IncrementArea.traceArea first.vertices.first.chartValue
      energy.paths +
      RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
        last.vertices.last.root.coordinate -
      RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
        first.vertices.first.root.coordinate)) < 2 * (2 * (target + otherTarget) + target) := by
  have firstClose :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary.AreaRequest.Evaluation.RequestedEnergy.chart_boundary_close
    energy.firstEnergy branch
  have lastClose :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary.AreaRequest.Evaluation.RequestedEnergy.chart_boundary_close
    energy.lastEnergy branch
  rw [energy.first_depth] at firstClose
  rw [energy.last_depth] at lastClose
  have joinClose := Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.join_radial_close first
    last joinRequest branch later otherLater energy.depth
  let firstReference := -first.vertices.path.chart.area - Path.BoundaryRibbon.area first.vertices.first.chartValue
    first.vertices.last.chartValue +
    RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
      first.vertices.last.root.coordinate -
    RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
      first.vertices.first.root.coordinate
  let lastReference := -last.vertices.path.chart.area - Path.BoundaryRibbon.area last.vertices.first.chartValue
    last.vertices.last.chartValue +
    RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
      last.vertices.last.root.coordinate -
    RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
      last.vertices.first.root.coordinate
  let connector := RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
    last.vertices.first.root.coordinate -
    RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
      first.vertices.last.root.coordinate -
    Path.BoundaryRibbon.area first.vertices.last.chartValue last.vertices.first.chartValue
  have pairClose : Data.Gaussian.Norm.Basic.normSq ((energy.firstEnergy.area - firstReference) +
    (energy.lastEnergy.area - lastReference)) < 2 * (target + otherTarget) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct firstClose lastClose)).trans_eq (by ring1))
  have estimate : Data.Gaussian.Norm.Basic.normSq (((energy.firstEnergy.area - firstReference) +
    (energy.lastEnergy.area - lastReference)) - connector) < 2 * (2 * (target + otherTarget) + target) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct pairClose joinClose)).trans_eq (by ring1))
  rw [energy.energy_eq, energy.trace_eq]
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt estimate
  dsimp only [firstReference, lastReference, connector]
  ring1

/-- Transfer the two actual fan lower bounds to the complete joined path;
its two outer radial sides remain explicit for the next gluing step. -/
theorem boundary_lower (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins.AreaRequest.Evaluation.JoinedEnergy first last energyTarget
  energyFloor)
    (joinRequest : Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests.Request owners.bounds.last joined target
      joinFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (later : joinRequest.index
      ≤ stage) (otherLater : joinRequest.index ≤ otherStage)
    (budget : Normalization.InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ budget) (paid : 2 * (2 * (target +
      otherTarget) + target) ≤ (4 * budget) ^ 2) :
    -(2 * energyTarget) - budget < (-Path.IncrementArea.traceArea first.vertices.first.chartValue energy.paths +
      RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
        last.vertices.last.root.coordinate -
      RootContinuation.RootRadialGeometry.radialArea capSample.primitive.value.eval energy.depth
        first.vertices.first.root.coordinate).im / 4 := by
  have transfer := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le energy.energy _ budget nonnegative
    ((energy.boundary_close joinRequest branch later otherLater).le.trans paid)
  exact (show -(2 * energyTarget) - budget = -(2 * energyTarget) + -budget by ring1).trans_lt
    ((Fraction.Order.Arithmetic.add_lt_add_right_direct energy.lower (-budget)).trans_le transfer)

end JoinedEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins
