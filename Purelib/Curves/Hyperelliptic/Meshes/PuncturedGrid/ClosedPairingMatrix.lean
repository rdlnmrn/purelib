module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea
import Purelib.Topology.Surface.Cut.ValuationMatrix
import Purelib.Topology.Surface.Word.PhysicalMatrixContraction
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! The actual corrected A/B area pairing reads the retained integral cut matrix. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix

open Purelib.Topology.Polygon.Stokes

local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

namespace GeneratorValuation

/-- The actual original cut-boundary area is the contraction of its retained signature matrix with the original
generator values. -/
theorem cut_area_eq_matrix : Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary =
    Topology.Surface.Word.Pairing.contract (fun row column => lifted.cutBoundaryWord.signature.matrix row column)
      (fun index => Energy.Polygon.energyPrimitivePoint (vget values index)) := open Purelib.Algebra in by
  have area := Topology.Surface.Cut.ValuationMatrix.CutBoundaryWord.wordArea_eq_contract
    lifted.cutBoundaryWord data.value data.value_reverse
  have projected := lifted.cutPolygon.patch.cut.boundary_eq
  have readback := congrArg (Topology.Mesh.RetracingWords.wordArea data.value) projected
  apply readback.symm.trans (area.trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  dsimp only
  rw [data.generator_readback row, data.generator_readback column]

/-- A physical-zero original generator valuation reads the cut area as twice the retained integral pairing contraction.
-/
theorem cut_area_eq_twice_integral (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  lifted.cutBoundaryWord) :
    Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary =
      2 * Topology.Surface.Word.Pairing.contract (fun row column => integral.paired row column)
        (fun index => Energy.Polygon.energyPrimitivePoint (vget values index)) := by
  apply (Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix.GeneratorValuation.cut_area_eq_matrix data).trans
  apply Topology.Surface.Word.PhysicalMatrixContraction.contract_eq_twice_paired integral
  intro index physical
  rw [data.physical index physical]
  rfl

end GeneratorValuation

namespace PairedPrepared

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet
  : Fin 2} {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
  bank sheet}
  {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

/-- This holds for every physical-zero generator vector on the actual program owner. -/
theorem pairing_eq_integral (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  lifted.cutBoundaryWord) :
    prepared.pairing data.value =
      Topology.Surface.Word.Pairing.contract (fun row column => integral.paired row column)
        (fun index => Energy.Polygon.energyPrimitivePoint (vget values index)) := by
  have doubled := (Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea.Paired.Prepared.twice_pairing_eq_cut_area
    data paired prepared).trans
      (Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix.GeneratorValuation.cut_area_eq_twice_integral data
      integral)
  have cancel (first last : Gaussian.Basic.Canonical) (equal : 2 * first = 2 * last) : first = last := by
    have half := congrArg (fun value : Gaussian.Basic.Canonical => (1 / 2) * value) equal
    have identity (value : Gaussian.Basic.Canonical) : (1 / 2) * (2 * value) = value := by
      rw [← mul_assoc]
      have scalar : (1 / 2 : Gaussian.Basic.Canonical) * 2 = 1 := by decide
      rw [scalar, one_mul]
    exact (identity first).symm.trans (half.trans (identity last))
  exact cancel _ _ doubled

end PairedPrepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairingMatrix
