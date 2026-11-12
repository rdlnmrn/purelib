module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentClosure
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses

open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

public section

/-!
# Exact segment endpoint accounting on each regular exterior component

The complete cap area is the sum of its original segment areas and the
polygon of shared primitive endpoint values. Closure identifies that polygon
with its oriented edge sum; no intermediate excursion is removed.
-/

namespace Purelib.Integration.Path.IncrementArea

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Data.Gaussian.Basic.Canonical

/-- The original edge increments telescope along a certified path to its endpoint difference. -/
private theorem edge_sum {count : Nat} (values : Fin count → Gaussian)
    {edges : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Stokes.OrientedEdge.start
      Stokes.OrientedEdge.finish edges first last) :
    Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => values edge.finish - values edge.start)) = values
      last - values first := by
  induction path with
  | nil => exact (Gaussian.Basic.sub_self _).symm
  | cons path ih => change (_ - _) + _ = _; rw [ih]; ring1

/-- The trace area of the actual edge increments equals the sum of the original oriented endpoint wedges. -/
private theorem edge_trace {count : Nat} (values : Fin count → Gaussian)
    {edges : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Stokes.OrientedEdge.start
      Stokes.OrientedEdge.finish edges first last) :
    IncrementArea.traceArea (values first) (edges.map (fun edge => values edge.finish - values edge.start)) =
      Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => BoundaryRibbon.area (values edge.start)
        (values edge.finish))) := by
  induction path with
  | nil => rfl
  | @cons edge tail last path ih =>
      change BoundaryRibbon.area (values edge.start) (values edge.start + (values edge.finish - values edge.start))
        +
        IncrementArea.traceArea (values edge.start + (values edge.finish - values edge.start)) _ = _
      rw [show values edge.start + (values edge.finish - values edge.start) = values edge.finish by ring1, ih]
      rfl

/-- For a closed retained edge path, the increment-polygon area equals the sum of its original endpoint wedges. -/
theorem closed_edge_polygon {count : Nat} (values : Fin count → Gaussian)
    {edges : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Stokes.OrientedEdge.start
      Stokes.OrientedEdge.finish edges anchor anchor) :
    IncrementArea.pathArea (edges.map (fun edge => values edge.finish - values edge.start)) =
      Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => BoundaryRibbon.area (values edge.start)
        (values edge.finish))) := by
  have trace := IncrementArea.edge_trace values path
  rw [IncrementArea.traceArea_eq, IncrementArea.edge_sum values path, Gaussian.Basic.sub_self,
    IncrementArea.area_zero_right, Gaussian.Basic.add_zero] at trace
  exact trace

end Purelib.Integration.Path.IncrementArea

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}

/-- The actual regular primitive paths on appended original parent banks concatenate in the same order. -/
theorem regularPrimitivePaths_append {first last : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    {firstCovers : UniformReciprocalCover.ParentCovers first} {lastCovers :
      UniformReciprocalCover.ParentCovers last}
    (left : SideBank regular firstCovers) (right :
      SideBank regular lastCovers) (value :
      InverseRootPolynomial.Polynomial) (depth : Nat) :
    RegularSidePrimitive.SideBank.regularPrimitivePaths value depth (left.append
      right) =
      RegularSidePrimitive.SideBank.regularPrimitivePaths value depth left ++
      RegularSidePrimitive.SideBank.regularPrimitivePaths value depth right := by
  induction left with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons _) ih

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Rational.Box} {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment
    curve.polynomial ambient start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece : CoveredSegment segment
    owner} {sheet : Fin 2}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap}

/-- The original retained regular segment's primitive paths telescope to its final-minus-initial reciprocal polynomial
value. -/
theorem regular_segment_total (cache : ParentCache piece.path differential sheet)
    {covers : UniformReciprocalCover.ParentCovers cache.parents} (bank :
      Disk.ParentJoins.SideBank regular covers) (value : Polynomial) (depth : Nat) :
    Gaussian.Norm.Sum.Basic.gaussianSum
      (Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
      bank).flatten = value.eval finish⁻¹ - value.eval start⁻¹ := by
  obtain ⟨chain⟩ := cache.chain
  have direct : DirectPathChain cache.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩) :=
    chain.toDirectPathChain
  exact Disk.ParentJoins.SideBank.regularPrimitivePaths_sum
    (parents := cache.parents) (covers := covers) (first := ⟨start, sheet⟩) (last := ⟨finish, sheet⟩) bank value depth
      direct

end Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfaceComponent)

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap}
  {domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box} {shared :
    Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea : Coordinate} {floor : Nat}

namespace SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence

/-- The unsigned path is a specification of the original retained parents. -/
@[expose] def
  unsignedPath
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (value : InverseRootPolynomial.Polynomial) (depth : Nat) : List
      Gaussian :=
  (Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
    occurrence.cap.path.bank).flatten

/-- The original occurrence's unsigned primitive path totals its actual endpoint polynomial difference. -/
theorem
  unsigned_total
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (value : InverseRootPolynomial.Polynomial) (depth : Nat) :
    Gaussian.Norm.Sum.Basic.gaussianSum (occurrence.unsignedPath value depth) = value.eval occurrence.finish⁻¹ -
      value.eval occurrence.start⁻¹ := by
  exact occurrence.compared.entered.cache.regular_segment_total occurrence.cap.path.bank value depth

/-- The original complete cap-spine path is exactly the concatenation of its retained occurrence paths. -/
theorem
  capSpine_paths
    (occurrences : List
      (SurfaceOccurrence
      regular domains differential)) (value : InverseRootPolynomial.Polynomial) (depth : Nat) :
    (Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
      (SurfaceOccurrence.capSpine
      occurrences).bank).flatten =
      (occurrences.map (fun occurrence => occurrence.unsignedPath value depth)).flatten := by
  induction occurrences with
  | nil => rfl
  | cons head tail ih =>
      change (Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
        (head.cap.path.bank.append
          (SurfaceOccurrence.capSpine
          tail).bank)).flatten = _
      rw [Disk.ParentJoins.SideBank.regularPrimitivePaths_append,
        List.Flatten.flatten_append, ih]
      rfl

end SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence

namespace SurfaceRequests.AllSurfacePreparation.SampledEntry

/-- Endpoint correction attached to one actual shared-surface segment. -/
@[expose] def
  endpointArea
    (value : SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor) : Gaussian :=
  Path.BoundaryRibbon.area (sample.primitive.value.eval value.entry.occurrence.start⁻¹) (sample.primitive.value.eval
    value.entry.occurrence.finish⁻¹)

end SurfaceRequests.AllSurfacePreparation.SampledEntry

namespace ComponentSamples.SampledComponent

/-- In even degree, the actual component cap area is the sum of its original segment areas and explicit endpoint
corrections. -/
theorem
  area_segments
    (group : SampledComponent (regular := regular) sample
      shared depth readingIndex localTarget localArea floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    group.cap.area = Gaussian.Norm.Sum.Basic.gaussianSum (group.values.map (fun value => value.evaluated.right.area
      + value.endpointArea)) := by
  let value := sample.primitive.value
  have formula := group.regular_area degree
  rw
    [SurfaceOccurrence.capSpine_paths,
    ← group.occurrences_eq, List.Map.map_map, Path.IncrementArea.pathArea_flatten] at formula
  have areas : (group.values.map (fun item => item.entry.occurrence.unsignedPath value depth)).map
    Path.IncrementArea.pathArea =
      group.values.map (fun item => item.evaluated.right.area) := by
    rw [List.Map.map_map]
    apply List.Map.map_congr_left
    intro item _
    exact (item.evaluated.regular_area_unsigned degree).symm
  have totals : (group.values.map (fun item => item.entry.occurrence.unsignedPath value depth)).map
    Gaussian.Norm.Sum.Basic.gaussianSum =
      group.values.map (fun item => value.eval item.entry.occurrence.finish⁻¹ - value.eval
        item.entry.occurrence.start⁻¹) := by
    rw [List.Map.map_map]
    apply List.Map.map_congr_left
    intro item _
    exact item.entry.occurrence.unsigned_total value depth
  have indexed : group.values.map (fun item => item.entry.occurrence.placement.indexed) =
    group.component.program.indexed := by
    have same := congrArg (List.map (fun occurrence => occurrence.placement.indexed)) group.occurrences_eq
    rw [List.Map.map_map] at same
    exact same.trans group.component.prepared.occurrences_eq
  let vertices (vertex : Fin lifted.vertices.count) := value.eval (lifted.vertices.coordinate vertex)⁻¹
  have deltas : group.values.map (fun item => value.eval item.entry.occurrence.finish⁻¹ - value.eval
    item.entry.occurrence.start⁻¹) =
      group.component.program.indexed.map (fun edge => vertices edge.finish - vertices edge.start) := by
    rw [← indexed, List.Map.map_map]
    apply List.Map.map_congr_left
    intro item _
    dsimp only [Function.comp_def, vertices]
    rw [item.entry.occurrence.placement.start_eq, item.entry.occurrence.placement.finish_eq]
  have endpoints : group.component.program.indexed.map (fun edge => Path.BoundaryRibbon.area (vertices edge.start)
    (vertices edge.finish)) =
      group.values.map
        SurfaceRequests.AllSurfacePreparation.SampledEntry.endpointArea :=
        by
    rw [← indexed, List.Map.map_map]
    apply List.Map.map_congr_left
    intro item _
    dsimp only [Function.comp_def, vertices,
      SurfaceRequests.AllSurfacePreparation.SampledEntry.endpointArea,
        value]
    rw [item.entry.occurrence.placement.start_eq, item.entry.occurrence.placement.finish_eq]
  obtain ⟨anchor, closed⟩ := Caps.indexed_closed group.component.program
  have polygon := Path.IncrementArea.closed_edge_polygon vertices closed
  rw [endpoints] at polygon
  change group.cap.area = Gaussian.Norm.Sum.Basic.gaussianSum ((group.values.map (fun item =>
    item.entry.occurrence.unsignedPath value depth)).map Path.IncrementArea.pathArea) +
    Path.IncrementArea.pathArea ((group.values.map (fun item => item.entry.occurrence.unsignedPath value depth)).map
      Gaussian.Norm.Sum.Basic.gaussianSum) at formula
  rw [areas, totals, deltas, polygon] at formula
  exact formula.trans (Gaussian.Norm.Sum.Basic.gaussianSum_map_add group.values (fun item =>
    item.evaluated.right.area)
    SurfaceRequests.AllSurfacePreparation.SampledEntry.endpointArea)

end ComponentSamples.SampledComponent

namespace ComponentArea.ExteriorProgram

/-- Summing retained component readings equals summing the same readings on the exact flattened occurrence list. -/
private theorem sum_component_values
    (groups : List (ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (value : SurfaceRequests.AllSurfacePreparation.SampledEntry (regular :=
      regular) sample shared depth readingIndex localTarget localArea floor → Gaussian) :
    Gaussian.Norm.Sum.Basic.gaussianSum (groups.map (fun group => Gaussian.Norm.Sum.Basic.gaussianSum
      (group.values.map value))) =
      Gaussian.Norm.Sum.Basic.gaussianSum (((groups.map
        ComponentSamples.SampledComponent.values).flatten).map value) := by
  induction groups with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, Gaussian.Norm.Sum.Basic.gaussianSum, List.flatten_cons, List.Map.map_append]
      rw [Path.IncrementArea.sum_append, ih]

end ComponentArea.ExteriorProgram

namespace ComponentSamples

/-- The original grouped cap areas equal the sum of the same ordered segment areas and endpoint corrections. -/
theorem
  area_segments
    {components : List
      (SurfaceComponent
      regular domains differential)}
    {values : List (SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)}
    (grouped : ComponentSamples sample shared depth
      readingIndex localTarget localArea floor components values)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Gaussian.Norm.Sum.Basic.gaussianSum (grouped.groups.map (fun group => group.cap.area)) =
      Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.right.area +
        value.endpointArea)) := by
  have same := congrArg (fun values : List
    (SurfaceRequests.AllSurfacePreparation.SampledEntry (regular := regular)
    sample shared depth readingIndex localTarget localArea floor) =>
    Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.right.area +
      value.endpointArea))) grouped.values_eq
  calc
    _ = Gaussian.Norm.Sum.Basic.gaussianSum (grouped.groups.map (fun group =>
      Gaussian.Norm.Sum.Basic.gaussianSum
        (group.values.map (fun value => value.evaluated.right.area + value.endpointArea)))) := by
      apply congrArg Gaussian.Norm.Sum.Basic.gaussianSum
      apply List.Map.map_congr_left
      intro group _
      exact group.area_segments degree
    _ = Gaussian.Norm.Sum.Basic.gaussianSum (((grouped.groups.map
      SampledComponent.values).flatten).map
        (fun value => value.evaluated.right.area + value.endpointArea)) :=
          ComponentArea.ExteriorProgram.sum_component_values _ _
    _ = _ := same

end ComponentSamples

variable {prepared :
  AllSurfacePreparation
    regular domains differential} {target areaTarget : Coordinate}
  {request : SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}

namespace SurfaceRequests.AllSurfacePreparation.Request.Evaluation

/-- The original full cap cache is an exact sum of its original segment
areas plus explicit endpoint corrections. This is the consuming identity
for summing the requested inverse-arc errors. -/
theorem
  cap_area_segments
    (evaluated : Evaluation
      request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    evaluated.cap.area = Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.samples.values.map (fun value =>
      value.evaluated.right.area + value.endpointArea)) :=
  (evaluated.cap_area_components degree).trans (evaluated.components.area_segments degree)

end SurfaceRequests.AllSurfacePreparation.Request.Evaluation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
