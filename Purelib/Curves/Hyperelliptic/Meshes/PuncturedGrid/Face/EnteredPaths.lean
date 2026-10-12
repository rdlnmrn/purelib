module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.CoordinateTriangulation

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Readings

@[expose] public section

/-!
# Requested primitive comparisons for paths with inherited entry owners

An arbitrary contained path keeps its original preparation and source owner.
The face-sheet assignment, axes, centered parents, primitive cover, split
mesh and endpoint indices are materialized once. Later accuracy requests use
these retained data and construct their own checked numerical witnesses.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.PreparedParentSplitting (PreparedSplitMesh)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry.Axis (Located locate)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch RectangularLayout)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {base finish : Purelib.Data.Gaussian.Basic.Canonical} {owner :
    Owner (curve.polynomial.eval base)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish}

/-- The final point of an original path contained in a box remains in that box. -/
public theorem finish_inside {polynomial : ClearPath.GaussianPolynomial} {ambient box : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start
      finish),
      path.InBox box → box.Contains finish
  | _, _, .nil _, inside => inside
  | _, _, .cons _ tail, inside => finish_inside tail
    inside.2

namespace PeriodDomain

/-- Locate on the retained axes, including independently generated axes. -/
def locate {sheet : Fin 2} (domain : Periods.PeriodDomain models sheet) (point : Data.Gaussian.Basic.Canonical)
    (inside : face.cell.box.Contains point) : Geometry.Rectangle.Partition.RectangularUniformGeometry.Located
        domain.geometry point :=
  let covered := domain.covers inside
  let horizontal := Axis.locate domain.geometry.x point.re covered.1 covered.2.1
  let vertical := Axis.locate domain.geometry.y point.im covered.2.2.1 covered.2.2.2
  ⟨horizontal.index, vertical.index, horizontal.inside.1, horizontal.inside.2, vertical.inside.1, vertical.inside.2⟩

end PeriodDomain

set_option genInjectivity false in
/-- All expensive finite data are explicit caches. The source owner is the one in the supplied preparation, not an
independently prepared substitute. -/
structure EnteredPath (models : BranchCellBank.FaceModels frames face) (prepared :
  PreparedClearPathModels.CoveredTracedPath path owner)
    (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) where
  /-- The original inherited source owner's retained face-sheet assignment. -/ entry : FaceModels.Entry models base
    owner
  /-- The cached complete face domain on this exact original selected sheet. -/ domain : Periods.PeriodDomain models
    entry.sheet
  /-- The original preparation's retained differential parent and coverage cache. -/ cache :
    PreparedClearPathModels.ParentCache prepared differential parentSheet
  /-- Every original cached parent is reached from the retained face owner on its actual sheet. -/ reached : ∀ parent ∈
    cache.parents, PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners entry.sheet) parent
  /-- The cached original parent splitting retaining both actual path endpoint coordinates. -/ mesh :
    PreparedParentSplitting.PreparedSplitMesh domain.cuts cache.parents [base, finish]
  /-- The retained fragment bounds for the original face patch and differential. -/ bounds :
    FragmentReadings.FragmentBounds domain.patch differential
  /-- The retained original clear-face primitive overlap bounds. -/ globalBounds :
    PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance (PreparedPrimitiveSamples.differentialNumerator
    differential)
  /-- The cached index of the original starting point in the retained split mesh. -/ first : Fin
    mesh.mesh.surface.mesh.vertices.length
  /-- The cached index of the original finishing point in the retained split mesh. -/ last : Fin
    mesh.mesh.surface.mesh.vertices.length
  /-- The cached first mesh vertex is exactly the original path start. -/ first_eq : mesh.mesh.surface.mesh.coordinate
    first = base
  /-- The cached last mesh vertex is exactly the original path finish. -/ last_eq : mesh.mesh.surface.mesh.coordinate
    last = finish

constructive_injectivity EnteredPath

namespace EnteredPath

variable {prepared : CoveredTracedPath path
  owner} {differential : Differential genus} {parentSheet : Fin 2}

/-- Reuse the assigned occurrence, shared face domain, and original centered parent/cover cache. The endpoint chain is
needed only in erased proofs. -/
def ofEntry (entry : FaceModels.Entry models base owner) (domain : Periods.PeriodDomain models entry.sheet)
    (prepared : PreparedClearPathModels.CoveredTracedPath path owner) (inside : ClearPath.InBox face.cell.box path)
    (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) (cache :
      PreparedClearPathModels.ParentCache prepared differential parentSheet) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models prepared differential parentSheet :=
  have reached : ∀ parent ∈ cache.parents,
      PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners entry.sheet) parent := by
    intro parent member
    exact entry.parent_reached differential parentSheet prepared.traced inside parent (by
        rw [← cache.parents_eq];
        exact member)
  let mesh := PreparedSplitMesh.build domain.cuts cache.parents (fun parent member =>
    ⟨domain.covers (reached parent member).first_inside, domain.covers (reached parent member).last_inside⟩) [base,
      finish]
  have firstMember : base ∈ mesh.points := by
    rw [mesh.points_eq]
    exact List.mem_append_right _ List.mem_cons_self
  have lastMember : finish ∈ mesh.points := by
    rw [mesh.points_eq]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  let firstCell := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.PeriodDomain.locate domain base
    inside.start
  let lastCell := Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.PeriodDomain.locate domain finish
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.finish_inside path inside)
  let first := mesh.mesh.lookup base firstMember firstCell.column firstCell.row
    (Geometry.allCells_mem domain.geometry _ _) firstCell.inside
  let last := mesh.mesh.lookup finish lastMember lastCell.column lastCell.row
    (Geometry.allCells_mem domain.geometry _ _) lastCell.inside
  ⟨entry, domain, cache, reached, mesh, FragmentBounds.build domain.patch differential,
    PrimitiveOverlapBounds.build face.clearance (PreparedPrimitiveSamples.differentialNumerator differential),
      first.index, last.index,
    first.coordinate_eq, last.coordinate_eq⟩

/-- Automatic sheet assignment and comparison geometry for an actual contained preparation starting at any grid vertex.
No analytic premise is required, and the original preparation is never run again. -/
def acquire (models : BranchCellBank.FaceModels frames face) (member :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid base)
    (prepared : PreparedClearPathModels.CoveredTracedPath path owner) (inside : ClearPath.InBox face.cell.box path)
    (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models prepared differential parentSheet
      :=
  let entry := Entry.acquire models member inside.start owner
  ofEntry entry (PeriodDomain.build models
    entry.sheet) prepared inside differential parentSheet
    (ParentCache.build prepared differential parentSheet)

/-- Pay a new numerical target on the original cached entered-path geometry, parents and face bounds. -/
def request (entered : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models prepared
  differential parentSheet) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    RequestedFragments entered.mesh entered.bounds entered.globalBounds genus target :=
  RequestedFragments.acquire entered.mesh entered.bounds entered.globalBounds entered.cache.covered entered.cache.proper
    target positive entered.reached

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath
/-- Exact telescoping uses the retained original endpoints even when the base is not the anchor, the owner is inherited,
or the chart label differs from the selected face occurrence. -/
theorem value_eq_increment (entered : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models
  prepared differential parentSheet)
    {target : InverseRootPolynomial.Coordinate} (request : RequestedFragments entered.mesh
      entered.bounds entered.globalBounds genus target) :
    request.summary.value = request.readings.values entered.last - request.readings.values entered.first := by
  obtain ⟨chain⟩ := entered.cache.chain
  exact request.value_eq_increment chain entered.first entered.last entered.first_eq entered.last_eq

/-- The actual retained endpoint primitive increment differs from the original controlled request sum by less than one
quarter target. -/
theorem accurate (entered : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models prepared
  differential parentSheet)
    {target : InverseRootPolynomial.Coordinate} (request : RequestedFragments entered.mesh
      entered.bounds entered.globalBounds genus target) :
    Data.Gaussian.Norm.Basic.normSq
      ((request.readings.values entered.last - request.readings.values entered.first) - request.request.primitiveSum) <
        target / 4 := by
  rw [← entered.value_eq_increment request]
  exact request.accurate

end EnteredPath

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
