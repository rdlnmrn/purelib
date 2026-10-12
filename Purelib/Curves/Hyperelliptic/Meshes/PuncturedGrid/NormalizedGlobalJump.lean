module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

public section

/-! The complete normalized crossing bank approximates its primitive-jump sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

namespace CrossingRequests
variable {retained : Matched.CrossingBank request mesh}
  {allocated : Matched.CrossingRequests
    (Periods.PeriodMatrix.standardDifferential i) (Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- The complete normalized crossing area differs from its retained endpoint jump by at most the fourth-power face-count
bound.

Both horizontal and vertical original crossing banks are included with their actual local targets. -/
theorem Samples.normalized_jump_bound (samples :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples allocated cache.normalize)
  (positive : 0 < tolerance)
    (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areaDifference - samples.endpointJump) ≤
      64 * (faces.regulars.length : Fraction.Rational)^4 * tolerance := by
  let horizontal := fun a b c =>
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.areaDifference
      (prepared := (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c) -
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.endpointJump
      (prepared := (((allocated.horizontal.get a).get b).get c))
      (cache := cache.normalize) (((samples.horizontal.get a).get b).get c)
  have horizontalBound : Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b
    => FiniteSum.Fin.sumFin (horizontal a b)))) ≤
      4 * (faces.regulars.length : Fraction.Rational)^4 * (4 * tolerance) :=
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound horizontal (4 * tolerance) (fun a b c =>
      Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared.Sample.normalized_jump_bound
        (((samples.horizontal.get a).get b).get c) positive
        ((allocated.horizontal_le a b c).trans later))
  let vertical := fun a b c =>
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.areaDifference
      (prepared := (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c) -
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.endpointJump
      (prepared := (((allocated.vertical.get a).get b).get c))
      (cache := cache.normalize) (((samples.vertical.get a).get b).get c)
  have verticalBound : Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b
    => FiniteSum.Fin.sumFin (vertical a b)))) ≤
      4 * (faces.regulars.length : Fraction.Rational)^4 * (4 * tolerance) :=
    Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound vertical (4 * tolerance) (fun a b c =>
      Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared.Sample.normalized_jump_bound
        (((samples.vertical.get a).get b).get c) positive
        ((allocated.vertical_le a b c).trans later))
  have equal : samples.areaDifference - samples.endpointJump =
      FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (vertical a b))) -
        FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (horizontal a b))) := by
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.areaDifference,
      Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointJump, horizontal,
        vertical,
      FiniteSum.Fin.sumFin_sub, -eq_self, -iff_self]
    ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add verticalBound horizontalBound)
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

/-- A quarter-target crossing request pays the complete normalized endpoint-jump comparison. -/
theorem TotalRequest.normalized_jump_bound {target : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest
      retained i j firstParent secondParent (target / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize) (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areaDifference - samples.endpointJump) ≤ target := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump.CrossingRequests.Samples.normalized_jump_bound
    samples total.positive later
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct total.paid
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have leftEq : 4 * (16 * (faces.regulars.length : Fraction.Rational)^4 * total.perEntry) =
      64 * (faces.regulars.length : Fraction.Rational)^4 * total.perEntry := by ring1
  have rightEq : 4 * (target / 4) = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [leftEq, rightEq] at paid
  exact estimate.trans paid

/-- The normalized original exterior total minus its physical sides and retained endpoint jump meets the paid whole
target. -/
theorem TotalRequest.normalized_exterior_jump_bound {target : Fraction.Rational}
    (total : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest
      retained i j firstParent secondParent (target / 4) floor)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples total.allocated
      cache.normalize)
    (perimeters : Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank faces)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors -
      samples.endpointJump) ≤ target := by
  have equal : Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.exteriorTotal perimeters -
      Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors =
      samples.areaDifference := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.CrossingBank.exterior_eq_paired_add_physical retained
      perimeters neighbors,
      ← samples.areaDifference_eq_pairedPerimeter perimeters]
    ring1
  rw [equal]
  exact Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump.CrossingRequests.TotalRequest.normalized_jump_bound
    total samples later

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedGlobalJump
