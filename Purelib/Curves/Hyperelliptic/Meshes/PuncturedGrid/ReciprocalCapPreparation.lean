module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Curves

open Purelib.Data

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Retained source geometry shared by the reciprocal chart constructions

Preparation retains the entered face occurrence and its original parent
cache. A request selects the face-comparison floor before evaluating one cap
sample. The shared triangle edge is compared with the total of that same
connected cap path. Full source/cap area and primitive-origin terms remain
explicit; the path's internal area is not replaced by its endpoint chord.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
    differential parentSheet}

set_option genInjectivity false in
/-- The geometric cap bank is retained across all later accuracy requests. -/
structure CapPreparation (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
      differential parentSheet) where
  /-- The reciprocal-cap path preparation on the exact original entered parent cache. -/ path :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular compared.entered.cache.parents
  /-- The retained count-paid source increment magnitude bound. -/ sourceBound :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The bound equals the original parent count squared times twice the sum of the retained source slope maximum and
    one. -/ sourceBound_eq : sourceBound = (compared.entered.cache.parents.length :
    Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (2 *
    (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum path.covers + 1))
  /-- The original retained source bound is nonnegative. -/ sourceBound_nonnegative : 0 ≤ sourceBound

constructive_injectivity CapPreparation

/-- Prepare the reciprocal cover of the original entered parent cache and retain its exact nonnegative source-slope
bound. -/
@[expose] def CapPreparation.build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
      differential parentSheet)
    (side : Paths.PreparedBoundarySegments.SameSide (Hyperelliptic.Branches.Cuts.Ambient curve) start finish) :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared
      :=
  open Purelib.Data.Rat in
  let path := Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Segment.prepare regular
    compared.entered.cache side
  let sourceBound := (compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (2 *
    (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum path.covers + 1))
  ⟨path, sourceBound, rfl, Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (by
        have bound := Fraction.Order.Arithmetic.add_le_add_direct
          (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative path.covers)
          (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)
        rewrite [Fraction.Field.zero_add] at bound
        exact bound))⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
