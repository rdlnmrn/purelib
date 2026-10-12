module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergyData
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Orientation

open Purelib.Curves

@[expose] public section

/-!
# Every actual exterior occurrence retains a nonempty parent bank

Its oriented original grid edge has distinct endpoints. The cached parent
chain therefore cannot be empty, independently of its finite refinement.
-/

section
section

open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfacePreparation SurfaceOccurrence)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Riemann

open Purelib.Integration.Energy in
/-- The coordinate triangle with repeated nonzero endpoint has zero oriented area. -/
private theorem self_area (value : Gaussian) :
    Integration.Energy.AffineTriangle.coordinateTriangleArea 0 value
  value = 0 := open Purelib.Data.Rat in by
  simp only [AffineTriangle.coordinateTriangleArea, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- An empty retained centered parent chain has equal endpoint coordinates. -/
private theorem empty_chain
    {first last : Purelib.Geometry.Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain (curve := curve)
      (differential := differential) [] (start := first) (finish := last)) :
    first.coordinate = last.coordinate := by
  cases chain
  rfl

end Purelib.Riemann

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation

/-- Each actual exterior occurrence retains a nonempty parent bank because its original oriented edge has distinct
endpoints. -/
theorem

    occurrence_nonempty
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential}
    (prepared :

        SurfacePreparation
      regular domains program) (occurrence :

        SurfaceOccurrence
      regular domains differential)
    (member : occurrence ∈ prepared.occurrences) : occurrence.compared.entered.cache.parents ≠ [] := open Purelib in
      open Purelib.Integration in by
  have indexed : occurrence.placement.indexed ∈ program.indexed :=
    prepared.occurrences_eq ▸ Data.List.Map.mem_map.mpr ⟨occurrence, member, rfl⟩
  have positive : 0 < Energy.AffineTriangle.coordinateTriangleArea 0 occurrence.start occurrence.finish := by
    simpa only [occurrence.placement.start_eq, occurrence.placement.finish_eq] using program.indexed_oriented _ indexed
  intro empty
  have chain := occurrence.compared.entered.cache.chain
  rw [empty] at chain
  have same : occurrence.start = occurrence.finish := by
    obtain ⟨chain⟩ := chain
    exact Purelib.Riemann.empty_chain chain
  rw [same, Purelib.Riemann.self_area] at positive
  exact (lt_irrefl (0 : Coordinate)) positive

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation

/-- Every occurrence in the complete original exterior preparation retains a nonempty parent bank. -/
theorem

    occurrence_nonempty
  (prepared :

    AllSurfacePreparation
  regular domains differential)
    (occurrence :

        SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences) :
    occurrence.compared.entered.cache.parents ≠ [] := open Purelib in by
  rw [prepared.occurrences_eq] at member
  obtain ⟨component, _, belongs⟩ := Data.List.Flatten.mem_flatMap.mp member
  exact component.prepared.occurrence_nonempty occurrence belongs

end LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

end
end
