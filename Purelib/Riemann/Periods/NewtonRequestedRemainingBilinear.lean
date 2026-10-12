module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Topology.NewtonSewnExcision

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedRemaining
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest
import Purelib.Tactic.Ring

@[expose] public section

/-! One automatic global request pays the surviving local paired triangle
sum against the actual cut word, retaining every correction term. -/

namespace Purelib.Riemann.Periods.NewtonRequestedRemainingBilinear

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open
  PairedComparison
  (Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (SewnSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open
  PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  (Excision)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)

variable {stage : Nat}
  {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {left : TriangleReadings (cache.get first)
    lifted.mesh} {right : TriangleReadings
    (cache.get second) lifted.mesh}
  {firstSurface : CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : CachedSample lifted.cutPolygon.patch
    right.values}

open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision} {comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
  prepared first second domains}
  {source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.Sample
    comparison left right}

namespace SewnSample.Excision

open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear

variable {sample :
  PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Bound the surviving paired triangle sum by the actual corrected cut-word area.

Beyond the global request stage, the squared error is less than twice the sum of the excision and local targets; the
retained closing and sewn correction terms remain in the reading. -/
theorem requested_local_word_accurate (cached :
  PairedRemaining.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample.Excision
  sample)
    (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface secondSurface)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first
      second} {localTarget : Rat.Fraction.Rational}
    (globalRequest : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global
      localTarget comparison.index)
    (later : globalRequest.index ≤ stage)
    {word : Surface.Cut.BoundaryWord.CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary}
    (area : Surface.Cut.WordArea.CutBoundaryWord.AreaSample word bilinear.values
      (bilinear.values lifted.cutPolygon.patch.cut.anchor)) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun source =>
      if !(excision.entries.any (fun entry => Topology.NewtonSewnExcision.AllHoleExcision.sourceMask entry source)) then
        Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right source else 0) -
      (Surface.Word.Pairing.contract (fun row column => word.signature.matrix row column) area.values +
        area.closedCorrection - sample.correction)) < 2 * (target + localTarget) := by
  have localBound :=
    Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest.BilinearPreparation.Request.selected_accurate
    globalRequest later left right bilinear cached.retained.remaining
  have wordBound := cached.centered_remaining_word_accurate bilinear area (globalRequest.floor_le.trans later)
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct wordBound localBound))
  have equal : ∀ a b c : Gaussian.Basic.Canonical, (a - b) - (a - c) = c - b := by intros; ring1
  rwa [equal] at estimate

end SewnSample.Excision
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Riemann.Periods.NewtonRequestedRemainingBilinear
