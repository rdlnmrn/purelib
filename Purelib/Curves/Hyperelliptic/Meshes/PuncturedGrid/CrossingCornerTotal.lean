module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Riemann.Periods

@[expose] public section

/-! The complete crossing sum compares to the shared fixed corner bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared
  VerticalPrepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests (CornerGrids)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal (triple_bound)

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin)

namespace CrossingBank

/-- The complete signed fixed-corner jump on the retained crossing bank and shared numerical cache. -/
def cornerJump
    (retained : CrossingBank request mesh) (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus)
      : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    ((((retained.vertical.get a).get b).get c).cornerJump cache i j)))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    ((((retained.horizontal.get a).get b).get c).cornerJump cache i j))))

end CrossingBank

namespace CrossingSamples.CrossingRequests.Samples
variable {retained : CrossingBank request mesh}
  {allocated : CrossingRequests
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained}
  {cache : Numerics domains stage}

/-- The actual crossing endpoint jump approximates the fixed corner-bank jump at the paid magnitude and grid stages.

The bound retains the fourth-power face count and both differential magnitude ceilings. -/
theorem
  corner_jump_bound
    (samples : CrossingRequests.Samples allocated cache.normalize)
    (firstMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (secondMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {cornerTolerance : Fraction.Rational} (grids : CrossingCornerRequests.CornerGrids fixed cornerTolerance) (gridLater
      : grids.index ≤ stage)
    (positive : 0 < cornerTolerance) (small : 16 * cornerTolerance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (samples.endpointJump - retained.cornerJump cache.normalize i j) ≤
      8192 * (faces.regulars.length : Fraction.Rational)^4 *
        (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * cornerTolerance := by
  let perEntry := 512 * (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * cornerTolerance
  let horizontal := fun a b c =>
    HorizontalPrepared.Sample.endpointJump (prepared := (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c) -
    (((retained.horizontal.get a).get b).get c).cornerJump cache.normalize i j
  let vertical := fun a b c =>
    VerticalPrepared.Sample.endpointJump (prepared := (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c) -
    (((retained.vertical.get a).get b).get c).cornerJump cache.normalize i j
  have horizontalBound := CrossingTotal.triple_bound horizontal perEntry (fun a b c =>
    HorizontalPrepared.Sample.corner_jump_bound (((samples.horizontal.get a).get b).get c)
      firstMagnitude secondMagnitude firstLater secondLater grids gridLater positive small)
  have verticalBound := CrossingTotal.triple_bound vertical perEntry (fun a b c =>
    VerticalPrepared.Sample.corner_jump_bound (((samples.vertical.get a).get b).get c)
      firstMagnitude secondMagnitude firstLater secondLater grids gridLater positive small)
  have equal : samples.endpointJump - retained.cornerJump cache.normalize i j =
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (vertical a b))) -
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (horizontal a b))) := by
    simp only [Samples.endpointJump,
      CrossingBank.cornerJump, horizontal, vertical,
      FiniteSum.Fin.sumFin_sub]
    ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add verticalBound horizontalBound)
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by dsimp only [perEntry]; ring1))

end CrossingSamples.CrossingRequests.Samples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
