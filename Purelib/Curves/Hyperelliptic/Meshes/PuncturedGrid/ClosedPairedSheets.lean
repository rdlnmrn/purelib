module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchExcursions
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Opposite-sheet readbacks for the complete corrected paired family and its excursions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)
  {reference : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

namespace PairedRow
variable {labels : Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {prior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} {otherPrior :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)}

/-- The B prefix changes sign together with its original reference pair. -/
theorem corrected_value_other (row : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference sheet
  labels prior)
    (other : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRow bank reference
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) labels otherPrior)
    (priorOpp : Topology.Surface.Sewing.SewingRetraction.wordValue data.value otherPrior.indexed =
      -Topology.Surface.Sewing.SewingRetraction.wordValue data.value prior.indexed) :
    Topology.Surface.Sewing.SewingRetraction.wordValue data.value other.corrected.indexed =
      -Topology.Surface.Sewing.SewingRetraction.wordValue data.value row.corrected.indexed := by
  rw [other.corrected_eq, row.corrected_eq]
  change Topology.Surface.Sewing.SewingRetraction.wordValue data.value (other.b.closed.indexed ++ otherPrior.indexed) =
    -Topology.Surface.Sewing.SewingRetraction.wordValue data.value (row.b.closed.indexed ++ prior.indexed)
  rw [Topology.Surface.Sewing.SewingRetraction.wordValue_append,
    Topology.Surface.Sewing.SewingRetraction.wordValue_append, data.pair_value_other bank row.b other.b, priorOpp]
  ring1

end PairedRow
namespace PairedRows

/-- Negating both original Gaussian increments preserves their bilinear ribbon area. -/
private theorem area_neg_neg (first last : Gaussian.Basic.Canonical) : Purelib.Integration.Path.BoundaryRibbon.area
  (-first) (-last) = Purelib.Integration.Path.BoundaryRibbon.area first last := by
  apply Gaussian.Basic.ext <;>
    simp only [Integration.Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj, Gaussian.Basic.neg_re,
      Gaussian.Basic.neg_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;> ring1

/-- The complete corrected paired area agrees on opposite sheets when the retained initial prefix changes sign. -/
theorem correctedArea_other
    {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    {prior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} (rows :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior)
    {otherPrior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)}
    (other : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) labels otherPrior)
    (priorOpp : Topology.Surface.Sewing.SewingRetraction.wordValue data.value otherPrior.indexed =
      -Topology.Surface.Sewing.SewingRetraction.wordValue data.value prior.indexed) :
    other.correctedArea data.value = rows.correctedArea data.value := open Purelib.Integration in by
  induction rows generalizing otherPrior with
  | nil => cases other; rfl
  | @cons labels rest prior row tail ih =>
      cases other with
      | cons otherRow otherTail =>
          have first := data.pair_value_other bank row.a otherRow.a
          have last := row.corrected_value_other data otherRow priorOpp
          have continued : Topology.Surface.Sewing.SewingRetraction.wordValue data.value (otherPrior.append
            otherRow.a.closed).indexed =
              -Topology.Surface.Sewing.SewingRetraction.wordValue data.value (prior.append row.a.closed).indexed := by
            change Topology.Surface.Sewing.SewingRetraction.wordValue data.value (otherPrior.indexed ++
              otherRow.a.closed.indexed) =
              -Topology.Surface.Sewing.SewingRetraction.wordValue data.value (prior.indexed ++ row.a.closed.indexed)
            rw [Topology.Surface.Sewing.SewingRetraction.wordValue_append,
              Topology.Surface.Sewing.SewingRetraction.wordValue_append, priorOpp, first]
            ring1
          change Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue data.value
            otherRow.a.closed.indexed) (Topology.Surface.Sewing.SewingRetraction.wordValue data.value
            otherRow.corrected.indexed) +
            otherTail.correctedArea data.value = _
          rw [first, last, Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows.area_neg_neg, ih otherTail
            continued]
          rfl

/-- The actual internal excursion area changes sign on the opposite sheet. -/
theorem internalArea_other
    {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    {prior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} (rows :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior)
    {otherPrior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)}
    (other : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference
      (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) labels otherPrior) :
    other.internalArea data.value = -rows.internalArea data.value := by
  induction rows generalizing otherPrior with
  | nil => cases other; exact neg_zero.symm
  | @cons labels rest prior row tail ih =>
      cases other with
      | cons otherRow otherTail =>
          change Topology.Mesh.RetracingWords.wordArea data.value otherRow.a.outward.indexed +
            Topology.Mesh.RetracingWords.wordArea data.value otherRow.a.returning.indexed +
            otherTail.internalArea data.value =
              -(Topology.Mesh.RetracingWords.wordArea data.value row.a.outward.indexed +
                Topology.Mesh.RetracingWords.wordArea data.value row.a.returning.indexed + tail.internalArea data.value)
          rw [otherRow.a.outward_eq, otherRow.a.returning_indexed, row.a.outward_eq, row.a.returning_indexed,
            data.loop_area_other bank labels.1 sheet,
            data.loop_area_other bank labels.2 (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet), ih otherTail]
          ring1

end PairedRows
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
