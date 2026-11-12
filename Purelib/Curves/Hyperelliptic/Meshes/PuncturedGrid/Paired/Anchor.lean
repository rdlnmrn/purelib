module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.Anchor
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Fin
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

/-! # The literal earlier-A prefix of the original corrected paired walks

The recursion follows the GIVEN PairedRows cache. Every earlier A pair is
read from that original cache; no bank, pair, source or period is prepared.
Whole RootClosedWalk transport keeps the original trace, primitive cover,
root names and operational return rather than constructing a new period.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex (VertexWalk)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}

namespace Paired.BranchArea.PairedRows

/-- The actual retained earlier-A prefix projects to the original pair labels strictly before the bounded row.

The initial prior remains an explicit first factor. Repeated labels and
stationary original walks remain literal ordered occurrences of the cache.
-/
theorem prior_atAnchor {reference : Data.Index branches}
    {labels : List (Data.Index branches × Data.Index branches)} {prior : BranchArea.CommonLoop lifted sheet}
    (rows : BranchArea.PairedRows bank reference sheet labels prior) (index : Fin labels.length) :
    atAnchor (lifted := lifted) sheet sheet (rows.get index).prior =
      (atAnchor (lifted := lifted) sheet sheet prior).append
        (bank.loopProduct ((labels.take index.val).flatMap (fun pair => [pair.1, pair.2]))) := by
  induction rows with
  | nil => exact Fin.elim0 index
  | @cons label rest prior row tail ih =>
      rcases index with ⟨position, bounded⟩
      cases position with
      | zero =>
          change atAnchor (lifted := lifted) sheet sheet prior =
            (atAnchor (lifted := lifted) sheet sheet prior).append (Walk.nil _)
          exact (atAnchor (lifted := lifted) sheet sheet prior).append_nil.symm
      | succ position =>
          let next : Fin rest.length := ⟨position, Nat.lt_of_succ_lt_succ bounded⟩
          change atAnchor (lifted := lifted) sheet sheet (tail.get next).prior =
            (atAnchor (lifted := lifted) sheet sheet prior).append
              (bank.loopProduct ([label.1, label.2] ++
                (rest.take next.val).flatMap (fun pair => [pair.1, pair.2])))
          have earlier := ih next
          have head := (atAnchor_append sheet sheet sheet prior row.a.closed).trans
            (congrArg (fun walk => (atAnchor (lifted := lifted) sheet sheet prior).append walk) row.a.atAnchor_closed)
          have expanded := earlier.trans (congrArg (fun walk => walk.append
            (bank.loopProduct ((rest.take next.val).flatMap (fun pair => [pair.1, pair.2])))) head)
          exact expanded.trans ((Walk.append_assoc _ _ _).trans
            (congrArg (fun walk => (atAnchor (lifted := lifted) sheet sheet prior).append walk)
              (bank.loopProduct_append [label.1, label.2]
                ((rest.take next.val).flatMap (fun pair => [pair.1, pair.2]))).symm))

end Paired.BranchArea.PairedRows

namespace OrderedBranchPairs.Ordered.Paired

variable {ordered : BasedBranchBank.Ordered bank sheet} (paired : OrderedBranchPairs.Ordered.Paired ordered)

/-- The two actual branch labels of the retained ordered A pair. -/
@[expose] def aLabels (index : Fin genus) : List (Data.Index branches) :=
  let pair := paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'
    (Fin.cast paired.split.count_eq.symm index).isLt
  [pair.1, pair.2]

/-- The actual B-reference labels followed by every earlier A pair in its retained order. -/
@[expose] def bLabels (index : Fin genus) : List (Data.Index branches) :=
  let pair := paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'
    (Fin.cast paired.split.count_eq.symm index).isLt
  [pair.1, paired.split.ending.reference] ++
    (paired.split.pairs.take index.val).flatMap (fun earlier => [earlier.1, earlier.2])

/-- The actual retained genus row's prior is exactly its literal earlier-A branch product at the common coordinate. -/
theorem prior_atAnchor (index : Fin genus) :
    atAnchor (lifted := lifted) sheet sheet (paired.row index).prior =
      bank.loopProduct ((paired.split.pairs.take index.val).flatMap (fun pair => [pair.1, pair.2])) := by
  have earlier := paired.rows.prior_atAnchor (Fin.cast paired.split.count_eq.symm index)
  have stationary := atAnchor_nil (lifted := lifted) sheet
  exact earlier.trans (congrArg (fun walk => walk.append
    (bank.loopProduct ((paired.split.pairs.take index.val).flatMap (fun pair => [pair.1, pair.2])))) stationary)

/-- The actual corrected B is its original B pair followed by the complete original earlier-A product. -/
theorem corrected_atAnchor (index : Fin genus) :
    atAnchor (lifted := lifted) sheet sheet (paired.row index).row.corrected =
      bank.loopProduct (paired.bLabels index) := by
  have divided := (congrArg (atAnchor (lifted := lifted) sheet sheet) (paired.row index).row.corrected_eq).trans
    (atAnchor_append sheet sheet sheet (paired.row index).row.b.closed (paired.row index).prior)
  have parts := congrArg₂ Walk.append (paired.row index).row.b.atAnchor_closed (paired.prior_atAnchor index)
  exact divided.trans (parts.trans (bank.loopProduct_append _ _).symm)

end OrderedBranchPairs.Ordered.Paired

namespace Paired.PeriodPrograms.Prepared

variable {ordered : BasedBranchBank.Ordered bank sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (prepared : PeriodPrograms.Prepared paired)

/-- Transport the GIVEN A closed preparation jointly through its actual anchor coordinate and Owner readbacks. -/
def aAtAnchor (index : Fin genus) : RootClosedWalk base.bank.grid (Ambient curve).anchor
    ((lifted.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners sheet) :=
  (prepared.row index).prepared.a.atAnchor

/-- Transport the GIVEN full corrected-B preparation and its earlier-A prefix to the actual common coordinate. -/
def bAtAnchor (index : Fin genus) : RootClosedWalk base.bank.grid (Ambient curve).anchor
    ((lifted.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners sheet) :=
  (prepared.bWalk index).closed.castBase (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)

/-- The A transport preserves the SAME complete preparation, trace, cover, names and operational return. -/
theorem aAtAnchor_heq (index : Fin genus) : HEq (prepared.aAtAnchor index) (prepared.aWalk index).closed :=
  (prepared.row index).prepared.a.atAnchor_heq

/-- The corrected-B transport preserves the SAME complete preparation and its full retained return evidence. -/
theorem bAtAnchor_heq (index : Fin genus) : HEq (prepared.bAtAnchor index) (prepared.bWalk index).closed :=
  (prepared.bWalk index).closed.castBase_heq (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)

/-- The transported A preparation reads exactly its two original ordered labels. -/
theorem aAtAnchor_walk (index : Fin genus) :
    (prepared.aAtAnchor index).walk = bank.loopProduct (paired.aLabels index) :=
  (prepared.row index).prepared.a.atAnchor_walk

/-- The transported B preparation reads its original B pair and complete earlier-A label prefix. -/
theorem bAtAnchor_walk (index : Fin genus) :
    (prepared.bAtAnchor index).walk = bank.loopProduct (paired.bLabels index) :=
  ((prepared.bWalk index).closed.castBase_walk (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)).trans
    ((congrArg (fun walk => walk.castEndpoints (anchor_coordinate (lifted := lifted) sheet)
      (anchor_coordinate (lifted := lifted) sheet)) (prepared.b_walk_eq index)).trans
      (paired.corrected_atAnchor index))

end Paired.PeriodPrograms.Prepared

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

end
