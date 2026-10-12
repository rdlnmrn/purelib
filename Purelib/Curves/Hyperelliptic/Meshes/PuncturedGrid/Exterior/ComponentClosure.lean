module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

public section

/-!
# Exact closure of the sampled regular exterior components

One signed polynomial holds along each original root thread. Its endpoint
increments telescope on that same closed parent chain, so every component
has exact zero total. Only then do cross-component area terms disappear.
-/

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.List

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {first last : Path.Gaussian.Lifted.Basic.LiftedPoint 2}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

/-- The actual regular primitive paths telescope along the original direct parent chain to its final-minus-initial
polynomial value. -/
theorem regularPrimitivePaths_sum (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers)
  (value : Normalization.InverseRootPolynomial.Polynomial) (depth : Nat)
    (chain : Integration.PreparedDirectDyadicRefinements.DirectPathChain parents (start := first) (finish := last)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
      bank).flatten = value.eval last.coordinate⁻¹ - value.eval first.coordinate⁻¹ := by
  induction chain with
  | nil => cases bank; exact (Gaussian.Basic.sub_self _).symm
  | cons parent chain ih =>
      cases bank with
      | cons head tail =>
          rw [Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths.eq_def,
            List.flatten_cons, Path.IncrementArea.sum_append,
            Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath,
            Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements_sum, ih tail,
            parent.edge.point_zero, parent.edge.point_one]
          ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank in
/-- The retained regular primitive increments have zero total on the same closed original parent chain. -/
theorem total_closed {index depth : Nat} {box : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
    {paths : List (List Normalization.InverseRootPolynomial.Gaussian)} (witnesses :
      RegularWitnesses sample depth bank paths) (links :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links bank)
    (chain : Integration.PreparedDirectDyadicRefinements.DirectPathChain parents (start := first) (finish := last))
      (closed : first.coordinate = last.coordinate) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum paths.flatten = 0 := by
  rw [witnesses.paths_eq witnesses.primitive (witnesses.shared links), bank.regularPrimitivePaths_sum _ _ chain, closed]
  exact Gaussian.Basic.sub_self _

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceOccurrence SurfacePreparation)

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

namespace ComponentSamples.SampledComponent

/-- In even degree, the actual cached cap total of each original exterior component is zero. -/
theorem total_zero
    (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample
      shared depth readingIndex localTarget localArea floor)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) : group.cap.total = 0 := by
  obtain ⟨paths, pathsEq, witnesses⟩ :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_witnesses
    group.values degree
  rw [group.occurrences_eq] at witnesses
  obtain ⟨witnesses⟩ := witnesses
  let joined :=
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.JoinedCap.build
    group.component.prepared
  have links : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
    group.component.prepared.occurrences).bank := by
    rw [← joined.spine_eq]
    exact joined.links
  have chain := group.component.program.cache.chain
  rw [← group.component.prepared.parents_eq] at chain
  obtain ⟨chain⟩ := chain
  rw [group.cap.total_eq, pathsEq]
  exact witnesses.total_closed links chain.toDirectPathChain rfl

/-- This cancellation uses certified zero component totals; the complete
internal areas are retained as the sum on the right. -/
theorem groups_area
    (groups : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Path.IncrementArea.pathArea (((groups.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.values).flatten).map
      (fun value => value.evaluated.capPath)).flatten = Data.Gaussian.Norm.Sum.Basic.gaussianSum (groups.map (fun group
        => group.cap.area)) := by
  induction groups with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, Map.map_append, Flatten.flatten_append, -eq_self, -iff_self]
      rw [Path.IncrementArea.pathArea_append, ← head.cap.area_eq, ih, ← head.cap.total_eq, head.total_zero degree,
        Path.IncrementArea.area_zero_left]
      change _ + _ + 0 = _ + _
      ring1

end ComponentSamples.SampledComponent

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
    areaTarget floor}

namespace SurfaceRequests.AllSurfacePreparation.Request.Evaluation

/-- The full original cap-area cache equals the sum of the component caches
assembled from its exact sample partition. -/
theorem
  cap_area_components
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation
      request sample shared depth readingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    evaluated.cap.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.components.groups.map (fun group =>
      group.cap.area)) := by
  rw [evaluated.cap.area_eq, evaluated.pairs_eq, Map.map_map]
  change Path.IncrementArea.pathArea (evaluated.samples.values.map (fun value => value.evaluated.capPath)).flatten = _
  have same := congrArg (fun values : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry (regular := regular)
    sample shared depth readingIndex request.localTarget request.budget.areaTarget floor) =>
    Path.IncrementArea.pathArea (values.map (fun value => value.evaluated.capPath)).flatten)
      evaluated.components.values_eq
  exact same.symm.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.groups_area
    evaluated.components.groups degree)

end SurfaceRequests.AllSurfacePreparation.Request.Evaluation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
