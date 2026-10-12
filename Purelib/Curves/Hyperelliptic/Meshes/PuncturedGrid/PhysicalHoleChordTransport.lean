module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceWords
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

@[expose] public section

/-! The physical cut-hole area is transported to the same source chords
used by the fine physical remainder. All eight origin terms are retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalHoleChordTransport

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.LiftedPuncturedGrid (holeSourceChords)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {hole : Fin base.faces.holes.length}
  {adjacent : HoleAdjacentFaces
    base (base.faces.holes[hole.val]'hole.isLt)}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars} {stage : Nat}
  {cache : RegularMeshes.Numerics domains stage}
    {i j : Fin genus}
  {prepared : BilinearPreparation
    lifted.cutPolygon domains i j}
  {target : Purelib.Data.Rat.Fraction.Rational} {floor : Nat}

/-- The physical cut-hole area, with all original source-origin terms removed, approximates the same retained hole
source chords.

The estimate pays both factors of the eight edge occurrences using the original sewing request and shared triangle
readings. -/
theorem physical_chord_accurate (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted ((base.faces.holes[hole.val]'hole.isLt).liftedBoundary
      lifted.vertices lifted.edges))
    (request : BilinearPreparation.Request prepared target floor) (later : request.index ≤ stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea sample.values physical.edges -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (physical.sources.entries.map (fun route =>
        Stokes.edgeArea (sample.values lifted.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
          ((sample.values route.cutEdge.finish).sub (sample.values route.cutEdge.start)))) -
      LiftedPuncturedGrid.holeSourceChords left right sides) ≤
      8 * (8 * (request.budget.weight * request.budget.error)) := by
  have estimate := BilinearPreparation.Request.path_source_chord_accurate
    request later left right sample physical.sources
  rw [HoleSourceWords.physical_sources_chords sides physical left right] at estimate
  have count : physical.edges.length = 8 :=
    physical.length_eq.trans ((base.faces.holes[hole.val]'hole.isLt).liftedBoundary_length lifted.vertices lifted.edges)
  rw [count] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalHoleChordTransport
