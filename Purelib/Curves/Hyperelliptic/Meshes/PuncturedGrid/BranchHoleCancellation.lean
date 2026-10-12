module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Data.List.Map

open Purelib.Curves

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-!
# Requested cancellation on the actual two-lap branch-hole boundary

The retained source list projects to the original eight lifted edges, using
the proved one-lap sheet swap. Its increment sum is small at every later
shared primitive index. This controls a period correction; it makes no claim
that the full discrete primitive area of the boundary vanishes.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}

/-- The constructor selects and caches both actual face occurrences on
each of the four original sides, then pays their complete two-sheet sum. -/
def cancellationRequest (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (target :
      Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh) domains differential
      hole.inwardBoundary target :=
  Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest.build mesh domains differential
    hole.inwardBoundary target positive

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {target :
  Normalization.InverseRootPolynomial.Coordinate}

/-- Literal projection to the retained root-closed two-lap tour. Equality
of the planar coordinates alone would not establish this source identity. -/
theorem cancellation_sources_project (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh) domains
      differential hole.inwardBoundary target) :
    request.sources.map (fun source => source.project mesh.triangulation.faces) = hole.liftedBoundary vertices edges :=
  request.sources_project.trans (hole.liftedBoundary_eq vertices edges).symm

/-- The retained original two-lap branch-hole cancellation has exactly eight source occurrences. -/
theorem cancellation_sources_length (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh) domains
      differential hole.inwardBoundary target) :
    request.sources.length = 8 := by
  have count := congrArg List.length
    (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole request)
  rw [Data.List.Map.length_map, hole.liftedBoundary_length] at count
  exact count

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
