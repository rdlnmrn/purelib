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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCoordinatePairing
public import Purelib.Riemann.Readings.EnergyMatrixEntries
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation

open Purelib.Integration.Energy

open Purelib.Riemann.Readings

open Purelib.Topology.Surface.Word

@[expose] public section

/-! The actual ordered A/B row wedges recover every paired entry of the cut matrix. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_neg)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  (cut : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)

/-- The integer alternating sum of the actual ordered A/B coordinate rows at two original cut-alphabet positions. -/
def wedgeEntry (first last : Fin lifted.cutBoundaryWord.alphabet.count) : Int :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    (cut.rows.get index).a.coordinates.totals first * (cut.rows.get index).b.coordinates.totals last -
    (cut.rows.get index).b.coordinates.totals first * (cut.rows.get index).a.coordinates.totals last)

/-- Interchanging the two cut-alphabet positions negates the complete retained A/B wedge entry. -/
theorem wedgeEntry_skew (first last : Fin lifted.cutBoundaryWord.alphabet.count) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry cut first last =
      -Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry cut last first := by
  exact (FiniteSum.Fin.sumFin_congr (fun index => by ring1)).trans (FiniteSum.Fin.sumFin_neg _)

/-- The actual ordered A/B wedge matrix and original cut pairing have equal contraction against every retained closed
generator valuation. -/
theorem wedgeEntry_contract
    {values : Data.Vector Data.Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
    (data : Cut.GeneratorValuation lifted values) :
    Pairing.contract (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry cut) (fun index =>
      Polygon.energyPrimitivePoint (vget values index)) =
      Pairing.contract (fun first last => cut.integral.paired first last)
        (fun index => Polygon.energyPrimitivePoint (vget values index)) := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry
  rw [EnergyMatrixEntries.contract_sum]
  exact cut.closed_wedge_contraction data

/-- A physical slot cannot be either of the selected paired coordinates. -/
theorem entryProbe_physical (first last : Fin lifted.cutBoundaryWord.alphabet.count)
    (firstPaired : lifted.cutBoundaryWord.alphabet.oneSided first = false)
    (lastPaired : lifted.cutBoundaryWord.alphabet.oneSided last = false)
    (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (physical : lifted.cutBoundaryWord.alphabet.oneSided index = true) :
    EnergyMatrixEntries.entryProbe first last index = 0 := by
  apply EnergyMatrixEntries.entryProbe_zero
  · intro same
    have equal := (congrArg (fun position => lifted.cutBoundaryWord.alphabet.oneSided position) same).symm.trans
      physical
    exact Bool.noConfusion (firstPaired.symm.trans equal)
  · intro same
    have equal := (congrArg (fun position => lifted.cutBoundaryWord.alphabet.oneSided position) same).symm.trans
      physical
    exact Bool.noConfusion (lastPaired.symm.trans equal)

/-- Entry equality is extracted from closed test valuations, not from construction tags. -/
theorem wedgeEntry_eq_paired (first last : Fin lifted.cutBoundaryWord.alphabet.count)
    (firstPaired : lifted.cutBoundaryWord.alphabet.oneSided first = false)
    (lastPaired : lifted.cutBoundaryWord.alphabet.oneSided last = false) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry cut first last = cut.integral.paired first
      last := by
  let values := Data.Vector.Basic.vectorOfFn (EnergyMatrixEntries.entryProbe first last)
  have physical (index : Fin lifted.cutBoundaryWord.alphabet.count)
      (side : lifted.cutBoundaryWord.alphabet.oneSided index = true) : vget values index = 0 :=
    (Data.Vector.Basic.vectorOfFn_apply _ index).trans
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.entryProbe_physical first last firstPaired
      lastPaired index side)
  let data := GeneratorValuation.build lifted values physical
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry_contract cut data
  have readback (matrix : Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int) :
      Pairing.contract matrix (fun index => Polygon.energyPrimitivePoint (vget values index)) =
        Pairing.contract matrix (fun index => Polygon.energyPrimitivePoint (EnergyMatrixEntries.entryProbe first last
          index)) := by
    apply FiniteSum.Fin.sumFin_congr
    intro row
    apply FiniteSum.Fin.sumFin_congr
    intro column
    dsimp only
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  exact EnergyMatrixEntries.entry_eq_of_probe (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry
    cut) (fun row column => cut.integral.paired row column)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry_skew cut) cut.integral.paired_skew first
      last
    ((readback (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix.wedgeEntry cut)).symm.trans (equal.trans
      (readback _)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix
