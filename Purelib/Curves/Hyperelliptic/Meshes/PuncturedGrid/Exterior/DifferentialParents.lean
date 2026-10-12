module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Riemann.Paths.PreparedPathDifferentialRecasting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateWitnessTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Differential-independent parent geometry of the actual exterior programs. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

/-- A common retained trace gives exactly the recast parents, including their
order and root owners, even when each differential constructs its own cache. -/
theorem DifferentialParents.ofCovered_parents_recast (source target : Differentials.Basic.Differential genus) (sheet :
  Fin 2)
    (covered : Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorWalk base).path
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner lifted sheet)) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.ofCovered lifted source sheet
      covered).cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target) =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.ofCovered lifted target sheet
        covered).cache.parents :=
  Paths.PreparedPathDifferentialRecasting.ofPreparedPath_recast curve source target 0 covered.traced.prepared

/-- Automatic preparation selects its covered trace independently of the
differential. This identifies actual built caches rather than replacement ones. -/
theorem
  PeriodPrograms.ExteriorProgram.build_parents_recast
  (source target : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source
      sheet).cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target) =
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted target
        sheet).cache.parents :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.DifferentialParents.ofCovered_parents_recast source target sheet _

variable {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- Independent surface preparations preserve the same ordered parent list
across all occurrence boundaries. Their local subdivisions need not be equal. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.build_parents_recast
    {source target : Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2}
    (first :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source
      sheet))
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted target
      sheet)) :
    (first.occurrences.map (fun occurrence => occurrence.compared.entered.cache.parents)).flatten.map
        (Integration.PreparedEdgeRecasting.recastCenteredEdge target) =
      (last.occurrences.map (fun occurrence => occurrence.compared.entered.cache.parents)).flatten :=
  (congrArg (List.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target)) first.parents_eq).trans
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build_parents_recast source target
      sheet).trans last.parents_eq.symm)

/-- The paired polygon of actual retained parent totals equals the unsigned primitive polygon when the parent lists
agree by differential recasting. -/
private theorem DifferentialParents.polygon_of_parent_eq
    {source target : Hyperelliptic.Differentials.Basic.Differential genus} {index depth otherDepth : Nat} {box otherBox
      : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
    {otherParents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve target)}
    (same : parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target) = otherParents)
    {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} {bank :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
    {otherCovers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers otherParents}
      {otherBank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular otherCovers}
    {paths otherPaths : List (List Normalization.InverseRootPolynomial.Gaussian)}
    (first : Charts.Reciprocal.Disk.RegularWitnesses sample depth bank paths)
    (last : Charts.Reciprocal.Disk.RegularWitnesses otherSample otherDepth
      otherBank otherPaths)
    (links : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links bank) (otherLinks :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links otherBank) :
    Path.PairedIncrementArea.area (List.zipWith (fun left right => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      left), Data.Gaussian.Norm.Sum.Basic.gaussianSum right⟩ : Topology.Polygon.Stokes.PrimitivePoint)) paths
      otherPaths) =
      Path.PairedIncrementArea.area (parents.map (fun parent =>
        (⟨conj (sample.primitive.value.eval (parent.edge.point 1)⁻¹ - sample.primitive.value.eval (parent.edge.point
          0)⁻¹),
          otherSample.primitive.value.eval (parent.edge.point 1)⁻¹ - otherSample.primitive.value.eval (parent.edge.point
            0)⁻¹⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))) := by
  cases same
  exact Hyperelliptic.Charts.Reciprocal.Disk.ConjugateWitnessTotals.RegularWitnesses.conjugate_total_polygon first last
    links otherLinks

/-- The actual independently built surface banks have a common root sign
along the whole exterior component. Their retained parent-total polygon is
the unsigned primitive polygon on the original period cache. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.conjugate_built_parent_polygon
    {source target : Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2}
    (first :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source
      sheet))
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted target
      sheet))
    {index depth otherDepth : Nat} {box otherBox : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}
    {paths otherPaths : List (List Normalization.InverseRootPolynomial.Gaussian)}
    (firstWitnesses : Charts.Reciprocal.Disk.RegularWitnesses sample depth
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
      first.occurrences).bank paths)
    (lastWitnesses : Charts.Reciprocal.Disk.RegularWitnesses otherSample
      otherDepth
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
      last.occurrences).bank otherPaths) :
    Path.PairedIncrementArea.area (List.zipWith (fun left right => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      left), Data.Gaussian.Norm.Sum.Basic.gaussianSum right⟩ : Topology.Polygon.Stokes.PrimitivePoint)) paths
      otherPaths) =
      Path.PairedIncrementArea.area ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build
        lifted source sheet).cache.parents.map (fun parent =>
        (⟨conj (sample.primitive.value.eval (parent.edge.point 1)⁻¹ - sample.primitive.value.eval (parent.edge.point
          0)⁻¹),
          otherSample.primitive.value.eval (parent.edge.point 1)⁻¹ - otherSample.primitive.value.eval (parent.edge.point
            0)⁻¹⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))) := by
  have result := Hyperelliptic.Meshes.PuncturedGrid.Exterior.DifferentialParents.polygon_of_parent_eq
    (first.build_parents_recast last) firstWitnesses lastWitnesses

      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.JoinedCap.build
      first).links
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.JoinedCap.build
      last).links
  exact result.trans (congrArg (fun parents => Path.PairedIncrementArea.area (parents.map (fun parent =>
    (⟨conj (sample.primitive.value.eval (parent.edge.point 1)⁻¹ - sample.primitive.value.eval (parent.edge.point 0)⁻¹),
      otherSample.primitive.value.eval (parent.edge.point 1)⁻¹ - otherSample.primitive.value.eval (parent.edge.point
        0)⁻¹⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))) first.parents_eq)

/-- Extract the parent paths from the two already evaluated component sample
lists. The polygon identity therefore concerns the retained numerical paths,
with independent request budgets and depths. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.conjugate_sampled_parent_polygon
    {source target : Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2}
    (first :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted source
      sheet))
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted target
      sheet))
    {index depth otherDepth readingIndex otherReadingIndex floor otherFloor : Nat} {box otherBox :
      Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank source index domains}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank target index domains}
    {localTarget localArea otherTarget otherArea : Normalization.InverseRootPolynomial.Coordinate}
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (otherValues : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular)
      otherSample otherShared otherDepth otherReadingIndex otherTarget otherArea otherFloor))
    (occurrences : values.map (fun value => value.entry.occurrence) = first.occurrences)
    (otherOccurrences : otherValues.map (fun value => value.entry.occurrence) = last.occurrences)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ paths otherPaths,
      (values.map (fun value => value.evaluated.capPath)).flatten = paths.flatten ∧
      (otherValues.map (fun value => value.evaluated.capPath)).flatten = otherPaths.flatten ∧
      Path.PairedIncrementArea.area (List.zipWith (fun left right => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum
        left), Data.Gaussian.Norm.Sum.Basic.gaussianSum right⟩ : Topology.Polygon.Stokes.PrimitivePoint)) paths
        otherPaths) =
        Path.PairedIncrementArea.area ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build
          lifted source sheet).cache.parents.map (fun parent =>
          (⟨conj (sample.primitive.value.eval (parent.edge.point 1)⁻¹ - sample.primitive.value.eval (parent.edge.point
            0)⁻¹),
            otherSample.primitive.value.eval (parent.edge.point 1)⁻¹ - otherSample.primitive.value.eval
              (parent.edge.point 0)⁻¹⟩ :
              Topology.Polygon.Stokes.PrimitivePoint))) := by
  obtain ⟨paths, pathsEq, witnesses⟩ :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_witnesses
    values degree
  obtain ⟨otherPaths, otherPathsEq, otherWitnesses⟩ :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_witnesses
    otherValues degree
  rw [occurrences] at witnesses
  rw [otherOccurrences] at otherWitnesses
  obtain ⟨firstWitnesses⟩ := witnesses
  obtain ⟨lastWitnesses⟩ := otherWitnesses
  exact ⟨paths, otherPaths, pathsEq, otherPathsEq, first.conjugate_built_parent_polygon last firstWitnesses
    lastWitnesses⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
