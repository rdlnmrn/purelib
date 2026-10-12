module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Polygon

public section

/-! Cache each actual annular selection and its conjugate area alongside the
positive polygons of the same excision hole. No scalar sewn sample is rebuilt. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
  (PairedAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceMask)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {comparison :
    PairedComparison
    prepared first second domains}
  {stage : Nat} {cache : Numerics
    domains stage}
  (left : TriangleReadings (cache.get first)
    lifted.mesh) (right : TriangleReadings
    (cache.get second) lifted.mesh)
  (leftSurface : CachedSample lifted.cutPolygon.patch left.values)
  (rightSurface : CachedSample lifted.cutPolygon.patch
    right.values)
  (pair : ConjugatePair leftSurface rightSurface)

set_option genInjectivity false in
/-- One original annular selection with cached conjugate area and its actual physical-hole area.

Both caches have specification equalities tied to the same retained entry and supplied sewn conjugate pair. -/
structure ConjugateTerm where
  /-- The retained original paired annulus. -/ entry : FamilyAreaRequest.PairedAnnulus request lifted first second
    domains
  /-- The actual source-mask selection on the supplied original left sewn surface. -/ selected :
    CachedSample.FaceSelection leftSurface
    (AllHoleExcision.sourceMask entry.source.entry)
  /-- The cached conjugate area of the actual selected triangle boundaries. -/ area : Data.Gaussian.Basic.Canonical
  /-- The area cache equals the original selected triangle boundary evaluation on this conjugate pair. -/ area_eq : area
    = Stokes.edgeListArea pair.values (selected.triangles.flatMap OrientedTriangle.boundary)
  /-- The cached conjugate physical-hole area of that exact entry. -/ hole : Data.Gaussian.Basic.Canonical
  /-- The hole cache equals the original entry's conjugate physical-hole readback. -/ hole_eq : hole =
    entry.source.entry.conjugatePhysicalHoleArea left right

constructive_injectivity ConjugateTerm

/-- Select the original annulus source mask once and retain its exact conjugate area and physical-hole readback. -/
@[expose] def ConjugateTerm.build (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains) :
    ConjugateTerm left right leftSurface rightSurface pair
      :=
  let selected := FaceSelection.build leftSurface (AllHoleExcision.sourceMask entry.source.entry)
  ⟨entry, selected, Stokes.edgeListArea pair.values (selected.triangles.flatMap OrientedTriangle.boundary), rfl,
    entry.source.entry.conjugatePhysicalHoleArea left right, rfl⟩

set_option genInjectivity false in
/-- The complete ordered conjugate annular term list and its retained aggregate area and hole caches.

The entry-list equality preserves the original comparison's order and multiplicity, and both aggregate equalities refer
to the actual term caches. -/
structure ConjugateSample (comparison : PairedComparison prepared first second domains) where
  /-- The actual ordered cached conjugate annular terms. -/ terms : List
    (ConjugateTerm left right leftSurface rightSurface
    pair)
  /-- The retained term entries are exactly the original comparison entry list. -/ terms_eq : terms.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.entry = comparison.entries
  /-- The cached sum of the actual selected annular conjugate areas. -/ area : Data.Gaussian.Basic.Canonical
  /-- The aggregate area equals the sum of the retained term area caches. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.area)
  /-- The cached sum of the actual conjugate physical-hole areas. -/ holes : Data.Gaussian.Basic.Canonical
  /-- The hole cache equals the sum of the retained term hole caches. -/ holes_eq : holes =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.hole)

constructive_injectivity ConjugateSample

/-- Build the original comparison's complete conjugate term list once and cache both exact aggregate sums. -/
@[expose] def ConjugateSample.build (comparison : PairedComparison prepared first second domains) :
    ConjugateSample left right leftSurface rightSurface
      pair comparison :=
  let terms := comparison.entries.map (Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.build
    left right leftSurface rightSurface pair)
  ⟨terms, by
    dsimp only [terms]
    induction comparison.entries with
    | nil => rfl
    | cons entry rest ih => exact congrArg (List.cons entry) ih,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.area), rfl,
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.hole), rfl⟩

variable {left right leftSurface rightSurface pair}

namespace ConjugateSample

/-- The actual retained conjugate term count is bounded by the original family request count. -/
theorem terms_count (sample : Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) :
    sample.terms.length ≤ request.count := by
  have count := congrArg List.length sample.terms_eq
  rw [Data.List.Map.length_map] at count
  exact count.le.trans comparison.entries_count

/-- The retained conjugate terms have exactly the original excision entry list. -/
theorem entries_eq (sample : Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) :
    sample.terms.map (fun term => term.entry.source.entry) = excision.entries := by
  have first := congrArg (List.map (fun entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains =>
    entry.source.entry)) sample.terms_eq
  have second := congrArg (List.map (fun entry : AnnularEntry.Prepared request.single.grid lifted => entry.entry))
    comparison.entries_eq
  rw [Data.List.Map.map_map] at first second
  exact first.trans (second.trans prepared.entries_eq)

/-- The retained aggregate hole cache is exactly the conjugate physical-hole sum on the original excision entries. -/
theorem holes_readback (sample : Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) :
    sample.holes = CellBoundary.sumValues (fun entry => entry.conjugatePhysicalHoleArea left right) excision.entries :=
      by
  rw [sample.holes_eq]
  have read : Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.hole) =
      CellBoundary.sumValues (fun entry => entry.conjugatePhysicalHoleArea left right)
        (sample.terms.map (fun term => term.entry.source.entry)) := by
    induction sample.terms with
    | nil => rfl
    | cons term rest ih => exact congrArg₂ (· + ·) term.hole_eq ih
  exact read.trans (congrArg (CellBoundary.sumValues (fun entry => entry.conjugatePhysicalHoleArea left right))
    sample.entries_eq)

/-- The sum of the actual term area-plus-hole residuals equals the retained aggregate area plus its hole cache. -/
theorem residuals_sum (sample : Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map (fun term => term.area + term.hole)) = sample.area +
      sample.holes := by
  rw [sample.area_eq, sample.holes_eq]
  induction sample.terms with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0; ring1
  | cons term rest ih =>
    change (term.area + term.hole) + Data.Gaussian.Norm.Sum.Basic.gaussianSum _ = (term.area +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum _) + (term.hole + Data.Gaussian.Norm.Sum.Basic.gaussianSum _)
    rw [ih]
    ring1

end ConjugateSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples
