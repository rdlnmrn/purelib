module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Integration.Surface.Sewn.Selection.BilinearReadback
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
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib

public section

/-! Local paired triangle values on the actual surviving region are
compared with the actual cut-word formula and all displayed corrections. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalBilinear

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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
  AllHoles.PairedComparison prepared
  first second domains}
  {source :
    AllHoles.PairedComparison.Sample
    comparison left right}

namespace SewnSample.Excision

variable {sample :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}

/-- The paired triangle area on the actual surviving region after excluding the retained hole masks. -/
@[expose] def localArea (_cached :
  AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position : Fin lifted.cutPolygon.patch.cut.triangles.length =>
    if !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry
      (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source)) then
        Topology.Polygon.Stokes.triangleWedgeArea
      ⟨left.values (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 0, right.values
        (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 0⟩
      ⟨left.values (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 1, right.values
        (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 1⟩
      ⟨left.values (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 2, right.values
        (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 2⟩
    else 0)

set_option genInjectivity false in
/-- The cached local paired area of the original surviving excision region. -/
structure LocalReading (cached :
  AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample) where
  /-- The cached paired area on the original surviving region. -/ value : Gaussian.Basic.Canonical
  /-- The cached value is exactly the original local triangle-area sum. -/ value_eq : value =
    localArea
    cached

constructive_injectivity LocalReading

/-- Cache the actual surviving-region triangle-area sum with its exact readback. -/
@[expose] def LocalReading.build (cached :
  AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample) :
  LocalReading
  cached := ⟨localArea cached, rfl⟩

/-- The cached local paired area approximates the original cut-word contraction and retained corrections within twice
the sum of the excision and local targets. -/
theorem local_word_accurate (cached :
  AllHoles.PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample) (localReading :
  LocalReading
  cached)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    {magnitude localTarget : Fraction.Rational}
    (budget : Topology.Surface.Sewing.Bilinear.Requests.AreaRequest lifted.cutPolygon.patch magnitude localTarget)
    (leftAccurate : Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy budget.tolerance
      firstSurface.sewn.readings)
    (rightAccurate : Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy budget.tolerance
      secondSurface.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (⟨left.values (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source index - left.values
          (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 0,
        right.values (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source index - right.values
          (Topology.Surface.Sewing.Bilinear.Errors.traceAt firstSurface position).source 0⟩ :
          Topology.Polygon.Stokes.PrimitivePoint) magnitude)
    {word : Topology.Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (area : Topology.Surface.Cut.WordArea.CutBoundaryWord.AreaSample word bilinear.values
      (bilinear.values lifted.cutPolygon.patch.cut.anchor)) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (localReading.value -
      (Topology.Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) area.values +
        area.closedCorrection - sample.correction)) < 2 * (target + localTarget) := open Purelib.Integration in by
  have localBound := Surface.Sewn.Selection.BilinearReadback.paired_request_accurate
    cached.retained.remaining bilinear budget leftAccurate rightAccurate bounded
  change Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea bilinear.values
    (cached.retained.remaining.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) -
      localArea
      cached) < localTarget at localBound
  rw [← localReading.value_eq] at localBound
  have wordBound := cached.centered_remaining_word_accurate bilinear area later
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct wordBound localBound))
  have equal : ∀ a b c : Gaussian.Basic.Canonical, (a - b) - (a - c) = c - b := by intros; ring1
  rwa [equal] at estimate

end SewnSample.Excision
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.LocalBilinear
