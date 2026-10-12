module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PhysicalRemainder
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Cache all indexed physical hole sides in retained annular order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Data.List
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Topology.Surface.Sewing
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
    (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
  (PairedAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Term Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (AnnularTerm SewnSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

section NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

section PairedComparison

variable {stage : Nat}
  {firstBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential first) stage domains}
  {secondBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential second) stage domains}
  {left : TriangleReadings firstBank
    lifted.mesh} {right : TriangleReadings
    secondBank lifted.mesh}
  {firstSurface : CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : CachedSample lifted.cutPolygon.patch
    right.values}

namespace PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison

set_option genInjectivity false in
/-- One original sewn annular term together with its actual indexed physical-hole side lifts. -/
structure PhysicalTerm (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh)
    (firstSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (secondSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values) where
  /-- The retained original sewn annular term. -/ term : PairedComparison.AnnularTerm left right firstSurface
    secondSurface
  /-- The four adjacent-side root lifts of that exact term's physical hole. -/ sides : Annulus.HoleSides
    term.source.source.source.entry.region

constructive_injectivity PhysicalTerm

end PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison

namespace PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm

/-- Acquire the actual adjacent-side root lifts for the supplied original sewn annular term. -/
@[expose] def build (term : PairedComparison.AnnularTerm left right firstSurface secondSurface) :

      PairedComparison.PhysicalTerm
      left right firstSurface secondSurface :=
  ⟨term, Annulus.HoleSides.build term.source.source.source.entry.region⟩

end PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision} {comparison :
  PairedComparison
  prepared first second domains}
  {source :
    PairedComparison.Sample
    comparison left right}

section SewnSample

namespace PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample

/-- The retained annular list is the original physical hole list, in order. -/
theorem holes_eq (sample : PairedComparison.SewnSample source firstSurface secondSurface) :
    sample.terms.map (fun term => term.source.source.source.entry.hole) = request.single.grid.faces.holes := by
  have firstEq := congrArg (List.map (fun term : PairedComparison.Term left right => term.source.source.entry.hole))
    sample.terms_eq
  have secondEq := congrArg (List.map (fun entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains
    => entry.source.entry.hole)) source.terms_eq
  have thirdEq := congrArg (List.map (fun entry : AnnularEntry.Prepared request.single.grid lifted => entry.entry.hole))
    comparison.entries_eq
  have fourthEq := congrArg (List.map (fun entry : Excision.AnnularEntry request.single.grid lifted => entry.hole))
    prepared.entries_eq
  simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at firstEq secondEq thirdEq fourthEq
  exact firstEq.trans (secondEq.trans (thirdEq.trans (fourthEq.trans excision.holes_eq)))

end PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample

set_option genInjectivity false in
/-- The complete retained physical-side acquisition in the original sewn term order.

The entry equality preserves every original annular term, including its source owner and sheet data. -/
structure PhysicalSides (sample :
    PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
      source firstSurface secondSurface) where
  /-- The actual ordered physical-side entries. -/ entries : List
    (PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm
    left right firstSurface secondSurface)
  /-- The retained physical-side entries project to the exact original sewn term list. -/ terms_eq : entries.map
    PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm.term
    = sample.terms

constructive_injectivity PhysicalSides

namespace PhysicalSides
variable {sample :
  PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}

/-- Retain one physical-side entry per original sewn annular term, preserving the exact term list. -/
@[expose] def build (sample :
    PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
      source firstSurface secondSurface) :
  PhysicalSides
  sample :=
  ⟨sample.terms.map
    NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm.build,
    by
    simp only [Data.List.Map.map_map, -eq_self, -iff_self]
    exact Map.map_id _⟩

/-- The acquired side positions read back the exact original physical-hole list in order. -/
theorem holes_eq (cached :
  PhysicalSides
  sample) :
    cached.entries.map (fun entry => request.single.grid.faces.holes[entry.sides.position.val]) =
      request.single.grid.faces.holes := by
  have mapped : cached.entries.map (fun entry => request.single.grid.faces.holes[entry.sides.position.val]) =
      cached.entries.map (fun entry => entry.term.source.source.source.entry.hole) := by
    apply Map.map_congr_left
    intro entry _
    exact entry.sides.hole_eq.trans entry.term.source.source.source.entry.hole_eq
  have terms := congrArg (List.map (fun term : PairedComparison.AnnularTerm left right firstSurface secondSurface =>
    term.source.source.source.entry.hole)) cached.terms_eq
  simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at terms
  exact mapped.trans (terms.trans
    (AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.holes_eq
      sample))

/-- No physical hole is omitted, repeated, or reordered by side acquisition. -/
theorem positions_eq (cached :
  PhysicalSides
  sample) :
    cached.entries.map (fun entry => entry.sides.position) =
      List.ofFn (fun position : Fin request.single.grid.faces.holes.length => position) := by
  apply (Data.List.Map.map_inj_right (f := fun position : Fin request.single.grid.faces.holes.length =>
    request.single.grid.faces.holes[position.val]) (fun first last equal =>
      HoleSideSelection.hole_position_eq_of_cell request.single.grid.faces first last (congrArg BranchHole.cell
        equal))).mp
  rw [Data.List.Map.map_map, OfFn.Basic.map_ofFn]
  exact
    (holes_eq
    cached).trans (OfFn.Basic.ofFn_getElem _).symm

/-- Summing over the retained physical-side positions equals the finite sum over all original hole indices. -/
theorem sum_positions (cached :
  PhysicalSides
  sample)
    (value : Fin request.single.grid.faces.holes.length → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry => value entry.sides.position)) =
      FiniteSum.Fin.sumFin value := by
  have positions := congrArg (List.map value)
    (positions_eq
    cached)
  simp only [Data.List.Map.map_map, Function.comp_def, OfFn.Basic.map_ofFn, -eq_self, -iff_self] at positions
  exact (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum positions).trans
    ((Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum value).symm)

/-- The retained side-entry count equals the exact original physical-hole count. -/
theorem entries_count (cached :
  PhysicalSides
  sample) :
    cached.entries.length = request.single.grid.faces.holes.length := by
  have count := congrArg List.length
    (positions_eq
    cached)
  simpa only [Data.List.Map.length_map, OfFn.Basic.length_ofFn, -eq_self, -iff_self] using count

end PhysicalSides
end SewnSample
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
