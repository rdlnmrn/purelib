module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

@[expose] public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {genus : Nat}

/-- The exact selected base family; this alias keeps the owner field telescope small. -/
@[reducible] def OwnedBase (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) :=
  FramedPuncturedGrid curve branches higher

/-- The original nominal lifted carrier, with its executable caches unchanged. -/
@[reducible] def OwnedLifted {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree}
    (base : OwnedBase curve branches higher) := LiftedPuncturedGrid base

set_option genInjectivity false in
/-- Ownership of the actually selected punctured grid and its retained lift. -/
structure OwnedPuncturedMesh (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original retained finite branch family for this curve. -/ branches : BranchIsolation.Data curve
  /-- The retained curve polynomial has degree greater than one. -/ higher : 1 < curve.polynomial.natDegree
  /-- The actually selected framed punctured base grid indexed by the retained branch family. -/ base : OwnedBase curve
    branches higher
  /-- The original nominal lift of this exact selected base grid. -/ lifted : OwnedLifted base

constructive_injectivity OwnedPuncturedMesh

namespace OwnedPuncturedMesh

variable {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Read the cached vertices of the retained lifted grid. -/
@[reducible] def vertices (owner : OwnedPuncturedMesh curve) := owner.lifted.vertices
/-- Read the cached root frames of the retained lifted grid. -/
@[reducible] def frames (owner : OwnedPuncturedMesh curve) := owner.lifted.frames
/-- Read the cached edges of the retained lifted grid. -/
@[reducible] def edges (owner : OwnedPuncturedMesh curve) := owner.lifted.edges
/-- Read the original finite mesh carried by the retained lift. -/
@[reducible] def mesh (owner : OwnedPuncturedMesh curve) := owner.lifted.mesh

/-- Package an existing selection without rebuilding any executable data. -/
def ofExisting (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree)
    (base : OwnedBase curve branches higher) (lifted : OwnedLifted base) :
    OwnedPuncturedMesh curve :=
  { branches := branches, higher := higher, base := base, lifted := lifted }

variable (branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve)
  (higher : 1 < curve.polynomial.natDegree)
  (base : OwnedBase curve branches higher) (lifted : OwnedLifted base)

/-- Packaging an existing selection retains its original branch family exactly. -/
theorem ofExisting_branches : (ofExisting branches higher base lifted).branches = branches := rfl
/-- Packaging an existing selection retains its original base grid exactly. -/
theorem ofExisting_base : (ofExisting branches higher base lifted).base = base := rfl
/-- Packaging an existing selection retains its original nominal lift exactly. -/
theorem ofExisting_lifted : (ofExisting branches higher base lifted).lifted = lifted := rfl
/-- Packaging an existing selection reuses its exact cached vertices. -/
theorem ofExisting_vertices : (ofExisting branches higher base lifted).vertices = lifted.vertices := rfl
/-- Packaging an existing selection reuses its exact cached frames. -/
theorem ofExisting_frames : (ofExisting branches higher base lifted).frames = lifted.frames := rfl
/-- Packaging an existing selection reuses its exact cached edges. -/
theorem ofExisting_edges : (ofExisting branches higher base lifted).edges = lifted.edges := rfl
/-- Packaging an existing selection reuses its exact cached mesh. -/
theorem ofExisting_mesh : (ofExisting branches higher base lifted).mesh = lifted.mesh := rfl

end OwnedPuncturedMesh
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
