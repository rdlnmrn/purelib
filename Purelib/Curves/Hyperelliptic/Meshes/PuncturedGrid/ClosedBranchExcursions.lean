module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemCancellation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Integration.Path

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Opposite-sheet cancellation of the actual branch excursions, including their areas. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append wordValue_reverse)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut (GeneratorValuation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {values : Data.Vector Canonical
    lifted.cutBoundaryWord.alphabet.count}
  (data : GeneratorValuation lifted values)
    (bank : BasedBranchBank
    lifted)

/-- Each hole lap is zero; the original forward stems on the two sheets remain. -/
theorem
  loop_value_stems
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    SewingRetraction.wordValue data.value (bank.liftedLoop index sheet).indexed =
      SewingRetraction.wordValue data.value (bank.stemWord index sheet) -
        SewingRetraction.wordValue data.value (bank.stemWord index (BranchCutLifts.otherSheet sheet)) := by
  rw [bank.loop_words, SewingRetraction.wordValue_append, SewingRetraction.wordValue_append,
    ClosedBranchHoles.holeWord_value_zero data bank index sheet,
    bank.returnWord_reverse, SewingRetraction.wordValue_reverse data.value data.value_reverse]
  ring1

/-- The original branch excursion on the opposite sheet has the negative closed generator value. -/
theorem
  loop_value_other
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    SewingRetraction.wordValue data.value (bank.liftedLoop index (BranchCutLifts.otherSheet sheet)).indexed =
      -SewingRetraction.wordValue data.value (bank.liftedLoop index sheet).indexed := by
  rw [data.loop_value_stems, data.loop_value_stems, BranchCutLifts.otherSheet_other]
  ring1

/-- The whole excursion area retains the stem polygon difference and its cross term. -/
theorem
  loop_area_stems
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    RetracingWords.wordArea data.value (bank.liftedLoop index sheet).indexed =
      RetracingWords.wordArea data.value (bank.stemWord index sheet) -
        RetracingWords.wordArea data.value (bank.stemWord index (BranchCutLifts.otherSheet sheet)) +
      BoundaryRibbon.area (SewingRetraction.wordValue data.value (bank.stemWord index sheet))
        (-(SewingRetraction.wordValue data.value (bank.stemWord index sheet) +
          SewingRetraction.wordValue data.value (bank.stemWord index (BranchCutLifts.otherSheet sheet)))) := by
  rw [bank.loop_area, ClosedBranchHoles.holeArea_zero data bank index sheet,
    Data.Gaussian.Basic.zero_add, bank.stemError_opposite data.value data.value_reverse,
    ClosedBranchHoles.holeWord_value_zero data bank index sheet, Data.Gaussian.Basic.add_zero]

/-- Opposite-sheet excursions cancel as full polygons, not merely as endpoint increments. -/
theorem
  loop_area_other
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    RetracingWords.wordArea data.value (bank.liftedLoop index (BranchCutLifts.otherSheet sheet)).indexed =
      -RetracingWords.wordArea data.value (bank.liftedLoop index sheet).indexed := by
  rw [data.loop_area_stems, data.loop_area_stems, BranchCutLifts.otherSheet_other]
  apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
    Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
    ring1

/-- The original closed branch pair has value equal to the first excursion value minus the second excursion value. -/
theorem pair_value
    {first last : BranchIsolation.Data.Index branches} {sheet : Fin 2}
    (pair : BasedBranchBank.Pair bank first last sheet) :
    SewingRetraction.wordValue data.value pair.closed.indexed =
      SewingRetraction.wordValue data.value (bank.liftedLoop first sheet).indexed -
        SewingRetraction.wordValue data.value (bank.liftedLoop last sheet).indexed := by
  rw [pair.closed_eq]
  change SewingRetraction.wordValue data.value (pair.outward.indexed ++ pair.returning.indexed) = _
  rw [SewingRetraction.wordValue_append, pair.outward_eq, pair.returning_indexed, data.loop_value_other]
  rfl

/-- The original branch-pair value changes sign on the opposite retained sheet. -/
theorem
  pair_value_other
    {first last : BranchIsolation.Data.Index branches} {sheet : Fin 2}
    (pair : BasedBranchBank.Pair bank first last sheet)
    (other : BasedBranchBank.Pair bank first last (BranchCutLifts.otherSheet sheet)) :
    SewingRetraction.wordValue data.value other.closed.indexed = -SewingRetraction.wordValue data.value
      pair.closed.indexed := by
  rw [data.pair_value bank other, data.pair_value bank pair, data.loop_value_other, data.loop_value_other]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
