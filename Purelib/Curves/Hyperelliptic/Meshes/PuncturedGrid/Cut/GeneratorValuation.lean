module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.VertexGluing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Cut.GeneratorExtension
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PotentialReadings
import Purelib.Topology.Surface.Sewing.SewingTree
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Automatic closed test valuations on the actual lifted-grid cut. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest
open Purelib.Topology.Surface.Cut.GeneratorExtension
open _root_.Purelib.Topology.Surface.Cut renaming GeneratorExtension -> GeneratorExtension
open Purelib.Topology.Surface.Cut.VertexGluing
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewingConnected
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  (lifted : LiftedPuncturedGrid base)
  (values : Data.Vector Canonical
    lifted.cutBoundaryWord.alphabet.count)

-- Preserve this original nominal owner and its existing public API names.
set_option genInjectivity false in
/-- Generator values, their physical support certificate, and all acquired readings have one cut owner.

The supplied values are indexed by the original boundary alphabet. Their cached
extension retains the exact cut and pairing, together with physical vanishing. -/
structure GeneratorValuation where
  /-- Every original one-sided physical generator has zero supplied value. -/ physical : ∀ index,
    lifted.cutBoundaryWord.alphabet.oneSided index = true → vget values index = 0
  /-- The cached generator extension indexed by the exact original cut, pairing and value vector. -/ extension :
    Topology.Surface.Cut.GeneratorExtension lifted.cutPolygon.patch.cut lifted.cutBoundaryPairs values

-- Original constructor API retains the same nominal parent.

constructive_injectivity GeneratorValuation

namespace GeneratorValuation

-- Preserve this original nominal owner and its existing public API names.
/-- The projected directed edge occurrences of the original cut triangles have no duplicates.

The retained single-polygon assembly covers the original triangles, and its
projected incidence keeps the original oriented-edge uniqueness certificate. -/
theorem occurrences_unique :
    ((lifted.cutPolygon.patch.cut.triangles.flatMap OrientedTriangle.boundary).map
      (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)).Nodup := by
  rw [CutPatch.projected_edges lifted.cutPolygon.patch.cut]
  exact SinglePolygon.originalEdges_unique
    lifted.cutPolygon lifted.mesh.orientedEdges_unique

/-- Every original lifted triangle is covered by the retained single cut polygon. -/
private theorem face_covered (index : Fin lifted.mesh.triangles.length) : index ∈ lifted.cutPolygon.patch.faceIndices :=
  by
  have member := SewingForest.face_mem lifted.cutForest index
  rw [lifted.cutPolygon.equation, Data.List.Flatten.flatMap_cons] at member
  change index ∈ lifted.cutPolygon.patch.faceIndices ++ [] at member
  rewrite [Data.List.Append.append_nil] at member
  exact member

-- Preserve this original nominal owner and its existing public API names.
/-- Extend the supplied original cut-generator values using their actual physical-boundary vanishing certificate. -/
@[expose] def build (physical : ∀ index, lifted.cutBoundaryWord.alphabet.oneSided index = true → vget values index = 0)
  :
    GeneratorValuation lifted values :=
  ⟨physical, GeneratorExtension.build lifted.cutPolygon.patch.cut lifted.cutBoundaryPairs values
    (occurrences_unique lifted)
      physical⟩

variable {lifted values} (data :
  GeneratorValuation lifted values)

-- Preserve this original nominal owner and its existing public API names.
/-- Read the cached original generator extension on an actual lifted oriented edge. -/
@[expose] def value (edge : Stokes.OrientedEdge lifted.vertices.count) : Data.Gaussian.Basic.Canonical :=
  data.extension.readings.value edge

-- Preserve this original nominal owner and its existing public API names.
/-- Reversing an original lifted oriented edge negates its retained valuation. -/
theorem value_reverse (edge : Stokes.OrientedEdge lifted.vertices.count) : data.value edge.reverse = -data.value edge :=
  data.extension.value_reverse
    (occurrences_unique lifted) edge

-- Preserve this original nominal owner and its existing public API names.
/-- The retained valuation reads back the exact supplied value of every original cut generator. -/
theorem generator_readback (index : Fin lifted.cutBoundaryWord.alphabet.count) :
    data.value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators index)) = vget values index :=
  data.extension.generator_readback
    (occurrences_unique lifted)
    index

-- Preserve this original nominal owner and its existing public API names.
/-- The retained original valuation sums to zero around every actual lifted triangle. -/
theorem face_zero (index : Fin lifted.mesh.triangles.length) :
    SewingRetraction.wordValue data.value (lifted.mesh.triangulation.faces index).boundary = 0 :=
  GeneratorExtension.face_zero data.extension
    (occurrences_unique lifted)
      index (face_covered lifted
      index)

-- Preserve this original nominal owner and its existing public API names.
/-- The retained original valuation sums to zero around each actual physical boundary component. -/
theorem boundary_zero (word : List (Stokes.OrientedEdge lifted.vertices.count)) (member : word ∈ lifted.boundaryLoops) :
    SewingRetraction.wordValue data.value word = 0 := by
  apply GeneratorExtension.physical_word_zero
    data.extension
      (occurrences_unique lifted)
      data.physical word
  intro edge onWord
  apply (lifted.cut_boundary_iff_boundaryComponents edge).mpr
  exact SimpleBoundaryCycles.mem_flatten.mpr ⟨word, member, onWord⟩

end GeneratorValuation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

end
