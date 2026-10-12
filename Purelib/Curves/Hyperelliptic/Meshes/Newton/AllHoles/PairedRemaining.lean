module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.WordArea
public import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Riemann.Topology.NewtonPairedSewnExcision
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-! The corrected paired aggregate consumes its exact retained excision
triangles and caches the paired remaining and boundary areas. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
  preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

variable {stage : Nat}
  {firstBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential first) stage domains}
  {secondBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential second) stage domains}
  {left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh} {right :
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh}
  {firstSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values}

variable {prepared :
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision}
  {comparison :
  PairedComparison prepared
  first second domains}
  {source :
    PairedComparison.Sample
    comparison left right}

namespace AnnularTerm

/-- Read the original annular source and selected triangles as the retained sewn annulus. -/
@[expose] def annulus (term :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.AnnularTerm
  left right firstSurface secondSurface) : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus firstSurface :=
  ⟨term.source.source.source.entry, term.selected⟩

end AnnularTerm

namespace SewnSample

set_option genInjectivity false in
/-- The actual retained excision with cached paired remaining and physical-boundary areas.

Its annuli are exactly the original paired terms, and both areas use the same original sewn values. -/
structure Excision (sample :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface) where
  /-- The original sewn excision and actual complementary triangle selection. -/ retained :
    Topology.NewtonSewnExcision.AllHoleExcision.Sewn excision firstSurface
  /-- The retained annuli are exactly the original paired sample terms. -/ annuli_eq : retained.annuli =
    sample.terms.map
    AnnularTerm.annulus
  /-- The cached paired area of the actual remaining triangles. -/ remainingArea : Gaussian.Basic.Canonical
  /-- The cached remaining area uses the exact original two sewn value banks. -/ remainingArea_eq : remainingArea =
    Topology.Polygon.Stokes.edgeListArea (fun vertex =>
    (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    (retained.remaining.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)
  /-- The cached paired physical-boundary area. -/ boundaryArea : Gaussian.Basic.Canonical
  /-- The boundary cache uses the original cut boundary and both retained sewn value banks. -/ boundaryArea_eq :
    boundaryArea = Topology.Polygon.Stokes.edgeListArea (fun vertex =>
    (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ : Topology.Polygon.Stokes.PrimitivePoint))
    lifted.cutPolygon.patch.cut.boundary

constructive_injectivity Excision

namespace Excision

variable {sample :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}

/-- Retain the original selected annuli, select the actual complementary triangles and cache their paired area and
boundary area once. -/
@[expose] def build (sample :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface) :
  SewnSample.Excision
  sample := by
  let annuli := sample.terms.map
    AnnularTerm.annulus
  have sources_eq : annuli.map Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus.source = excision.entries := by
    dsimp only [annuli, -eq_self, -iff_self]
    rw [Data.List.Map.map_map]
    have firstEq :=  congrArg (List.map (fun term :
      PairedComparison.Term
      left right => term.source.source.entry)) sample.terms_eq
    have secondEq :=  congrArg (List.map (fun entry :
      Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus request
      lifted first second domains => entry.source.entry)) source.terms_eq
    have thirdEq :=  congrArg (List.map (fun entry :
      Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AnnularEntry.Prepared request.single.grid
      lifted => entry.entry)) comparison.entries_eq
    simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at firstEq secondEq thirdEq
    exact firstEq.trans (secondEq.trans (thirdEq.trans prepared.entries_eq))
  let retained : Topology.NewtonSewnExcision.AllHoleExcision.Sewn excision firstSurface :=
    { annuli := annuli
      sources_eq := sources_eq
      remaining := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build firstSurface
        (fun index => !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
          index)))
      annularArea := Geometry.Grid.CellBoundary.sumValues (fun annulus => annulus.selected.area) annuli
      annularArea_eq := rfl }
  let primitive := fun vertex => (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint)
  exact ⟨retained, rfl, Topology.Polygon.Stokes.edgeListArea primitive (retained.remaining.triangles.flatMap
    Topology.Polygon.Stokes.OrientedTriangle.boundary), rfl,
    Topology.Polygon.Stokes.edgeListArea primitive lifted.cutPolygon.patch.cut.boundary, rfl⟩

/-- The original selected and retained remaining paired areas sum to the cached physical-boundary area. -/
theorem partition (cached :
  SewnSample.Excision
  sample) : sample.selectedArea + cached.remainingArea = cached.boundaryArea := by
  let primitive := fun vertex => (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint)
  have equal := Topology.NewtonPairedSewnExcision.AllHoleExcision.Sewn.paired_partition cached.retained primitive
  rw [cached.annuli_eq] at equal
  have areas : Geometry.Grid.CellBoundary.sumValues (fun annulus => Topology.Polygon.Stokes.edgeListArea primitive
      (annulus.selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)) (sample.terms.map
        AnnularTerm.annulus)
        =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map (fun term => term.data.selectedArea)) := by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih =>
      exact congrArg₂ (· + ·) term.data.selectedArea_eq.symm ih
  rw [areas, ← sample.selectedArea_eq] at equal
  rw [cached.remainingArea_eq, cached.boundaryArea_eq]
  exact equal

/-- The remaining area minus the corrected physical-boundary area is the negative original aggregate difference. -/
theorem remaining_eq (cached :
  SewnSample.Excision
  sample) :
    cached.remainingArea - (cached.boundaryArea - sample.correction) = -sample.difference := by
  rw [← cached.partition, ← sample.corrected_eq]
  ring1

/-- The actual remaining area is within the target of the physical-boundary area with the original annular correction
retained. -/
theorem remaining_accurate (cached :
  SewnSample.Excision
  sample) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remainingArea - (cached.boundaryArea - sample.correction)) < target :=
      by
  rw [cached.remaining_eq, Gaussian.Norm.Basic.normSq_neg]
  exact sample.accurate later

/-- The cached physical-boundary area equals the actual common bilinear bank's boundary area. -/
theorem boundary_eq_bilinear (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface) :
    cached.boundaryArea = bilinear.boundaryArea :=
  cached.boundaryArea_eq.trans (Periods.BilinearBoundaryReadback.boundary_eq_raw bilinear).symm

/-- The remaining area is within the original target of the corrected bilinear boundary area. -/
theorem remaining_bilinear_accurate (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface) (later : comparison.index
      ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remainingArea - (bilinear.boundaryArea - sample.correction)) < target :=
      by
  rw [← cached.boundary_eq_bilinear bilinear]
  exact cached.remaining_accurate later

/-- The exact cut-word contraction retains both its closed correction and
all annular corrections. Identification with standard periods is separate. -/
theorem remaining_word_accurate (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    {word : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (area : Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample word bilinear.values
      (bilinear.values lifted.cutPolygon.patch.cut.anchor)) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (cached.remainingArea -
      (Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) area.values +
        area.closedCorrection - sample.correction)) < target := by
  rw [← Topology.Surface.Sewing.Bilinear.Samples.boundary_eq_word bilinear area]
  exact cached.remaining_bilinear_accurate bilinear later

/-- The retained remaining triangles use exactly the common bilinear bank's centered values. -/
theorem remaining_eq_bilinear (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface) :
    cached.remainingArea = Topology.Polygon.Stokes.edgeListArea bilinear.values
      (cached.retained.remaining.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) :=
  cached.remainingArea_eq.trans (Periods.BilinearBoundaryReadback.triangles_eq_raw bilinear _).symm

/-- Both remaining triangles and the boundary formula use the same centered
bilinear bank; all cut-word and annular corrections remain visible. -/
theorem centered_remaining_word_accurate (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    {word : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (area : Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample word bilinear.values
      (bilinear.values lifted.cutPolygon.patch.cut.anchor)) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea bilinear.values
      (cached.retained.remaining.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) -
      (Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) area.values +
        area.closedCorrection - sample.correction)) < target := by
  rw [← cached.remaining_eq_bilinear bilinear]
  exact cached.remaining_word_accurate bilinear area later

/-- Transfer a fine local boundary comparison through the actual excision.
The physical perimeter/chord term and annular correction are both retained. -/
theorem local_boundary_transfer (cached :
  SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    (localTotal physicalCorrection : Gaussian.Basic.Canonical) {localError : Fraction.Rational}
    (localBound : Data.Gaussian.Norm.Basic.normSq (localTotal - bilinear.boundaryArea - physicalCorrection) ≤
      localError)
    (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (localTotal - cached.remainingArea - (physicalCorrection + sample.correction)) <
      2 * (localError + target) := by
  have remaining := cached.remaining_bilinear_accurate bilinear later
  have equal : localTotal - cached.remainingArea - (physicalCorrection + sample.correction) =
      (localTotal - bilinear.boundaryArea - physicalCorrection) -
        (cached.remainingArea - (bilinear.boundaryArea - sample.correction)) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_right_direct localBound _).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct remaining _)))

end Excision
end SewnSample
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
