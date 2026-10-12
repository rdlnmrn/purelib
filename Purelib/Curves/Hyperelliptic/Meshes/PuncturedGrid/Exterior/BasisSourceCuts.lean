module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Init.Data.List.Basic
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.List

public section

/-! One cut bank contains the original exterior source partitions of every
standard differential, before any physical-owner requests are selected. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest (BasisArcPreparations)
open Purelib.Riemann.Normalization
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- One common cut bank containing every original exterior basis source partition.

The previous cut bank and all source points are retained in their original order, with exact readback equalities. -/
structure BasisSourceCuts (preparations : BasisArcRequest.BasisArcPreparations regular domains) (previous :
  RegularMeshes.CommonCuts domains) where
  /-- The cached concatenation of all original exterior source partition points in basis and occurrence order. -/
    sourcePoints : List Data.Gaussian.Basic.Canonical
  /-- The source point cache equals the actual original basis-occurrence point concatenation. -/ sourcePoints_eq :
    sourcePoints = (List.ofFn (fun first : Fin genus => first)).flatMap
    (fun first => (preparations.get first).occurrences.flatMap (fun occurrence =>
      occurrence.compared.entered.mesh.points))
  /-- The shared original domain cut bank extended by every retained basis source point. -/ cuts :
    RegularMeshes.CommonCuts domains
  /-- The extended cut bank is exactly the previous point list followed by the cached original source points. -/
    points_eq : cuts.points = previous.points ++ sourcePoints

constructive_injectivity BasisSourceCuts

namespace BasisSourceCuts
variable {preparations : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations
  regular domains} {previous :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}

/-- Cache every original basis source partition point once and append the complete list to the retained previous cut
bank.

Basis and occurrence order determine the same cached source-point concatenation, which extends the retained previous
bank without repeating acquisition. -/
@[expose] def build (preparations : BasisArcRequest.BasisArcPreparations regular domains) (previous :
  RegularMeshes.CommonCuts domains) :
    BasisSourceCuts preparations previous :=
  let sourcePoints := (List.ofFn (fun first : Fin genus => first)).flatMap
    (fun first => (preparations.get first).occurrences.flatMap (fun occurrence =>
      occurrence.compared.entered.mesh.points))
  let cuts : RegularMeshes.CommonCuts domains := ⟨previous.points ++ sourcePoints,
    fun position sheet point member => List.mem_append_left _ (previous.includes position sheet point member)⟩
  ⟨sourcePoints, rfl, cuts, rfl⟩

/-- Each differential gets a certificate for the very same common bank. No row-specific mesh, source splitting or
numerical acquisition is repeated.

Membership in the original finite basis table identifies the selected differential while preserving the same complete
cut bank and source occurrences. -/
@[expose] def select (selected : BasisSourceCuts
  preparations previous) (first : Fin genus) :
    SourceCuts (preparations.get first) previous := by
  refine ⟨(preparations.get first).occurrences.flatMap (fun occurrence => occurrence.compared.entered.mesh.points),
    rfl, selected.cuts, ?_, ?_⟩
  · intro point member
    rw [selected.points_eq]
    exact List.mem_append_left _ member
  · intro point member
    rw [selected.points_eq]
    apply List.mem_append_right
    rw [selected.sourcePoints_eq]
    exact Flatten.mem_flatMap.mpr ⟨first, OfFn.Basic.mem_ofFn.mpr ⟨first, rfl⟩, member⟩

end BasisSourceCuts
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
