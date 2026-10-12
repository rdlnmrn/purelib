module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves

open Purelib

@[expose] public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}

/-- The exact original domain bank over this selected owner's retained faces. -/
@[reducible] def Domains (owner : OwnedPuncturedMesh curve) : Type :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank
    owner.frames owner.base.faces.regulars

/-- The original cache with entries, validity index, bound and their equalities. -/
@[reducible] def MagnitudeBank (owner : OwnedPuncturedMesh curve)
    (domains : Domains owner) (differential : Hyperelliptic.Differentials.Basic.Differential genus) : Type 2 :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential

/-- The original executable recursive product; no domains or samples are rebuilt. -/
@[reducible] def PrimitiveBank (owner : OwnedPuncturedMesh curve)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (stage : Nat) (domains : Domains owner) : Type
      :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains

/-- The original vector cache and values_eq witness over the same mesh and bank. -/
@[reducible] def TriangleCache (owner : OwnedPuncturedMesh curve)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (stage : Nat) (domains : Domains owner)
    (data : PrimitiveBank owner differential stage domains) : Type :=
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings data owner.mesh

/-- The original finite source carrier, retaining its triangle and corner indices. -/
@[reducible] def Source (owner : OwnedPuncturedMesh curve) : Type :=
  Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge owner.mesh.triangles.length

/-- The actual ordered source list, with multiplicity and sheet labels unchanged. -/
@[reducible] def Sources (owner : OwnedPuncturedMesh curve) : Type := List (Source owner)

/-- The exact source-by-source obligation of the existing chart builder. -/
@[reducible] def Nonloop (owner : OwnedPuncturedMesh curve) (sources : Sources owner) : Prop :=
  ∀ source ∈ sources, source.first ≠ source.last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
