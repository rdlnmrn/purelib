module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate
import Purelib.Riemann.Topology.NewtonPairedSewnExcision
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
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

public section

/-! Exact excision for the retained conjugate annular sample. The remaining
surface and physical-hole replacement use the very same cut triangles. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {request : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation
    target radius}
  {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}
  {prepared : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision} {comparison :
    PairedComparison prepared
    first second domains}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh)
    (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second)
    lifted.mesh)
  (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
  (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
  (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)

variable {left right leftSurface rightSurface pair}

/-- The exact sewn annulus selected by the original conjugate term. -/
@[expose] def ConjugateTerm.annulus (term : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm left
  right leftSurface rightSurface pair) :
    Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus leftSurface := ⟨term.entry.source.entry, term.selected⟩

namespace ConjugateSample

set_option genInjectivity false in
/-- The retained annular excision and complementary area on the original conjugate surface pair.

Its annulus list is exactly the sampled original terms, and the cached remaining area reads their literal complementary
cut triangles. -/
structure Excision (sample : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) where
  /-- The original sewn excision on the same cut surface. -/ retained : Topology.NewtonSewnExcision.AllHoleExcision.Sewn
    excision leftSurface
  /-- The retained annuli are exactly those selected by the original conjugate sample terms. -/ annuli_eq :
    retained.annuli = sample.terms.map Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateTerm.annulus
  /-- The cached conjugate area of the retained complementary triangles. -/ remainingArea : Gaussian.Basic.Canonical
  /-- The remaining area is evaluated on the original conjugate pair and actual complementary triangle boundaries. -/
    remainingArea_eq : remainingArea = Topology.Polygon.Stokes.edgeListArea pair.values
    (retained.remaining.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)

constructive_injectivity Excision

namespace Excision

variable {sample : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right leftSurface
  rightSurface pair comparison}

/-- Retain the original sampled annuli and cache their exact complementary conjugate area. -/
@[expose] def build (sample : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right
  leftSurface rightSurface pair comparison) :
  Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateSample.Excision sample := by
  let annuli := sample.terms.map Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateTerm.annulus
  have sources_eq : annuli.map Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus.source = excision.entries := by
    dsimp only [annuli]
    rw [Data.List.Map.map_map]
    exact Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample.entries_eq sample
  let retained : Topology.NewtonSewnExcision.AllHoleExcision.Sewn excision leftSurface :=
    { annuli := annuli
      sources_eq := sources_eq
      remaining := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build leftSurface
        (fun index => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
          index)))
      annularArea := Geometry.Grid.CellBoundary.sumValues (fun annulus => annulus.selected.area) annuli
      annularArea_eq := rfl }
  exact ⟨retained, rfl, Topology.Polygon.Stokes.edgeListArea pair.values (retained.remaining.triangles.flatMap
    Topology.Polygon.Stokes.OrientedTriangle.boundary), rfl⟩

/-- Every original cut triangle is accounted for once by the cached annuli
or the retained complement, evaluated on the actual conjugate pair. -/
theorem partition (cached : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateSample.Excision sample) :
  sample.area + cached.remainingArea = pair.boundaryArea := by
  have equal := Topology.NewtonPairedSewnExcision.AllHoleExcision.Sewn.paired_partition cached.retained pair.values
  rw [cached.annuli_eq] at equal
  have areas : Geometry.Grid.CellBoundary.sumValues (fun annulus => Topology.Polygon.Stokes.edgeListArea pair.values
      (annulus.selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)) (sample.terms.map
        Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateTerm.annulus) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map
        Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateTerm.area) := by
    induction sample.terms with
    | nil => rfl
    | cons term rest ih => exact congrArg₂ (· + ·) term.area_eq.symm ih
  rw [areas, ← sample.area_eq] at equal
  rw [cached.remainingArea_eq, pair.boundaryArea_eq]
  exact equal

/-- Replacing the complete surface plus positive hole polygons by the retained complement leaves the negative
annular-plus-hole total. -/
theorem remaining_difference (cached : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateSample.Excision
  sample) :
    cached.remainingArea - (pair.boundaryArea + sample.holes) = -(sample.area + sample.holes) := by
  rw [← cached.partition]
  ring1

end Excision
end ConjugateSample

/-- The remaining surface replaces the whole surface plus its positive hole
polygons on every later common sample. No annular area is dropped. -/
@[expose] def conjugateRemainingRequest (comparison :
  PairedComparison prepared
  first second domains)
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first
      second) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
        (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first)
          lifted.mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get
          second) lifted.mesh)
        (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
        (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
        (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
        (sample : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right leftSurface
          rightSurface pair comparison)
        (cached : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining.ConjugateSample.Excision sample), threshold ≤
          stage →
        Data.Gaussian.Norm.Basic.normSq
          (cached.remainingArea - (pair.boundaryArea + sample.holes)) < (82 / 4 : Fraction.Rational) * target} := by
  let acquired := Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate.conjugatePhysicalRequest comparison
    sewing floor
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right leftSurface rightSurface pair sample cached later
  rw [cached.remaining_difference, Gaussian.Norm.Basic.normSq_neg]
  exact acquired.property.2 stage cache left right leftSurface rightSurface pair sample later

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining
