module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceWords
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Locate the retained annular hole in the actual physical hole list and
cache its adjacent lifted sides. Selection uses the finite branch index. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerReadback
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
    (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance (InnerOccurrences)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

namespace HoleSides

/-- Find the retained position of a supplied list member using decidable unique keys.

The returned finite index is certified to contain that exact original item; the construction searches the existing list
without rebuilding entries. -/
@[expose] def positionByKey {Item Key : Type} [DecidableEq Key] (key : Item → Key) (target : Item) :
    (items : List Item) → items.Pairwise (fun first second => key first ≠ key second) → target ∈ items →
      {position : Fin items.length // items[position.val] = target}
  | [], _, member => (List.not_mem_nil member).elim
  | head :: tail, unique, member =>
      if equal : key head = key target then
        ⟨⟨0, Nat.zero_lt_succ _⟩, by
          rcases Data.List.Membership.mem_cons.mp member with same | inTail
          · exact same.symm
          · exact ((List.pairwise_cons.mp unique).1 target inTail equal).elim⟩
      else
        let found := Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides.positionByKey key target tail
          (List.pairwise_cons.mp unique).2
          ((Data.List.Membership.mem_cons.mp member).resolve_left (fun same => equal (congrArg key same.symm)))
        ⟨found.val.succ, found.property⟩

end HoleSides

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index}

section AnnularFaces.Lifted

set_option genInjectivity false in
/-- The original annular hole's retained physical-list position and actual adjacent side lifts.

The equality binds the listed physical hole to the annular owner, and all root-sheet side selections depend on that same
position. -/
structure HoleSides (region : LiftedBoundary.Lifted annulus lifted) where
  /-- The retained physical-list position of the original annular hole. -/ position : Fin grid.faces.holes.length
  /-- The selected list entry is exactly the retained annular hole. -/ hole_eq : grid.faces.holes[position.val] =
    region.hole
  /-- The four actual regular faces adjacent to that selected physical hole. -/ adjacent :
    PuncturedGrid.HoleAdjacentFaces grid.punctured grid.faces.holes[position.val]
  /-- The actual root-sheet lifts of those retained adjacent sides. -/ sides : HoleRootedCorrection.HoleSideLifts lifted
    adjacent

constructive_injectivity HoleSides

namespace HoleSides
variable {region : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- Locate the original annular hole by its unique branch key and retain its actual adjacent side lifts. -/
@[expose] def build (region : LiftedBoundary.Lifted annulus lifted) :
  HoleSides region :=
  let found := Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides.positionByKey (fun hole => hole.index) region.hole
    grid.faces.holes grid.faces.holes_pairwise region.hole_mem
  let adjacent := PuncturedGrid.HoleAdjacentFaces.build grid.punctured grid.faces.holes[found.val.val]
  ⟨found.val, found.property, adjacent, HoleSideLifts.build lifted adjacent⟩

/-- Reindex the existing annular occurrences to the physical hole position. The edges and source-owner cache are reused
without a new cut lookup. -/
@[expose] def innerPhysical (cached : HoleSides
  region) (inner : CutBalance.InnerOccurrences region) :
    BranchHoleCutWords.PhysicalCutWord lifted (grid.faces.holes[cached.position.val].liftedBoundary lifted.vertices
      lifted.edges) where
  edges := inner.word.edges
  physical := (InnerOccurrences.toPhysical inner).physical
  project := (inner.project.trans region.inner_eq).trans
    (congrArg (fun hole => hole.liftedBoundary lifted.vertices lifted.edges) cached.hole_eq).symm
  sources := inner.word.sources

variable {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  grid.faces.regulars} {stage : Nat}
  {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    {i j : Fin genus}

/-- The actual retained annular inner source list has the same chord sum as its indexed physical-hole side bank. -/
theorem inner_source_chords (cached : HoleSides
  region) (inner : CutBalance.InnerOccurrences region)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (inner.word.sources.sources.map (TriangleReadings.sourceChord left
      right)) =
      LiftedPuncturedGrid.holeSourceChords left right cached.sides :=
  HoleSourceWords.physical_sources_chords cached.sides
    (innerPhysical cached inner) left
    right

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
open Purelib.Algebra.FiniteSum.Fin (sumFin)
variable {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {physicalTarget : Purelib.Data.Rat.Fraction.Rational}
  {physicalRequest : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun
    sheet => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts
    sheet coarseDepth) fixed physicalTarget}

/-- Read the eight fine side areas from the already retained perimeter bank. -/
@[expose] def finePerimeter (cached : HoleSides
  region)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest) cache.normalize i j) :
      Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun sheet =>
    ((perimeters.perimeters.get cached.adjacent.left.position).get (cached.sides.left.get sheet).selected.sheet).right -
    ((perimeters.perimeters.get cached.adjacent.right.position).get (cached.sides.right.get sheet).selected.sheet).left
      -
    (((perimeters.perimeters.get cached.adjacent.bottom.position).get (cached.sides.bottom.get
      sheet).selected.sheet).top -
      ((perimeters.perimeters.get cached.adjacent.top.position).get (cached.sides.top.get
        sheet).selected.sheet).bottom))

/-- The centered source chords cancel exactly between the annular inner word and the indexed physical hole remainder. -/
theorem remainder_add_inner_chords (cached :
  HoleSides region) (inner :
  CutBalance.InnerOccurrences region)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    HoleAreaRemainder.holeAreaRemainder perimeters cached.sides +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (inner.word.sources.sources.map (TriangleReadings.sourceChord left
        right)) =
      cached.finePerimeter perimeters :=
  HoleSourceWords.remainder_add_physical_source_chords cached.sides
    (innerPhysical cached inner)
    perimeters left right

end HoleSides
end AnnularFaces.Lifted
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
