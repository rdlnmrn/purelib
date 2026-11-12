module
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

namespace Purelib.Curves.Legendre.Periods.Fibre

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces BranchHole)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
  {branches : BranchIsolation.Data (frameCurve frame)}
  {higher : 1 < (frameCurve frame).polynomial.natDegree}

public section

namespace BranchLabels

/-- The actual real Legendre order determines the retained genus-one pair and terminal reference.

The original pair split is read without rebuilding it. Its full window
order is unit, moving and zero, so its sole pair and odd terminal label
have those same original branch indices.
-/
theorem split_labels {bank : BranchCellBank (frameCurve frame) branches higher}
    (labels : BranchLabels frame bank) (real : parameter.im = 0)
    (positive : 0 < parameter.re) (unit : parameter.re < 1)
    {faces : PuncturedFaces bank}
    {window : Window bank.grid (Cuts.Ambient (frameCurve frame))}
    {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
    {sheet : Fin 2} (prepared : OrderedBranchCircuits.Window.OrderedBranches faces window edges vertices sheet)
    (split : OrderedBranchPairs.LabelPairs 1 prepared.labels) :
    split.pairs = [(labels.val.backward 2, labels.val.backward 1)] ∧
      split.ending.reference = labels.val.backward 0 := by
  have encoded : ([2, 1, 0] : List (Fin 3)) =
      (split.pairs.flatMap (fun pair => [pair.1, pair.2]) ++ split.ending.labels).map labels.val.forward :=
    (labels.window_labels real positive unit prepared).symm.trans
      (congrArg (List.map labels.val.forward) split.labels_eq)
  have count := split.count_eq
  cases pairsEq : split.pairs with
  | nil =>
      rewrite [pairsEq] at count
      nomatch count
  | cons pair rest =>
      rewrite [pairsEq] at count
      cases pair with
      | mk first second =>
          have empty : rest.length = 0 := Nat.succ.inj count
          cases rest with
          | cons next rest => nomatch empty
          | nil =>
              cases endingEq : split.ending with
              | odd reference =>
                  rewrite [pairsEq, endingEq] at encoded
                  change [2, 1, 0] =
                    [labels.val.forward first, labels.val.forward second, labels.val.forward reference] at encoded
                  have firstReading := (List.cons.inj encoded).1
                  have next := (List.cons.inj encoded).2
                  have secondReading := (List.cons.inj next).1
                  have referenceReading := (List.cons.inj (List.cons.inj next).2).1
                  have firstEq : first = labels.val.backward 2 :=
                    (labels.val.backward_forward first).symm.trans
                      (congrArg labels.val.backward firstReading.symm)
                  have secondEq : second = labels.val.backward 1 :=
                    (labels.val.backward_forward second).symm.trans
                      (congrArg labels.val.backward secondReading.symm)
                  have referenceEq : reference = labels.val.backward 0 :=
                    (labels.val.backward_forward reference).symm.trans
                      (congrArg labels.val.backward referenceReading.symm)
                  refine ⟨congrArg₂ (fun first second => [(first, second)]) firstEq secondEq, ?_⟩
                  exact referenceEq
              | even reference last =>
                  rewrite [pairsEq, endingEq] at encoded
                  change [2, 1, 0] = [labels.val.forward first, labels.val.forward second,
                    labels.val.forward reference, labels.val.forward last] at encoded
                  have impossible := (List.cons.inj (List.cons.inj (List.cons.inj encoded).2).2).2
                  nomatch impossible

variable {base : FramedPuncturedGrid (frameCurve frame) branches higher}
  {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchBank.Ordered bank sheet}

/-- The sole actual canonical row and retained terminal reference have their exact logical branch labels.

Only the original count-index transport is used to read the row. No
branch walk, sheet, reference owner or ordered split is replaced.
-/
theorem paired_labels (labels : BranchLabels frame base.bank.toBranchCellBank)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1)
    (paired : OrderedBranchPairs.Ordered.Paired ordered) :
    paired.split.pairs[(Fin.cast paired.split.count_eq.symm (0 : Fin 1)).val]'
        (Fin.cast paired.split.count_eq.symm (0 : Fin 1)).isLt =
        (labels.val.backward 2, labels.val.backward 1) ∧
      paired.split.ending.reference = labels.val.backward 0 := by
  have actual := labels.split_labels real positive unit ordered.prepared paired.split
  refine ⟨?_, actual.2⟩
  exact getElem_congr actual.1 (show (Fin.cast paired.split.count_eq.symm (0 : Fin 1)).val = 0 from rfl)
    (Fin.cast paired.split.count_eq.symm (0 : Fin 1)).isLt

end BranchLabels

end

/-- The original reference-pair identity transports only its branch indices and retains every supplied pair. -/
private theorem retained_reference {base : FramedPuncturedGrid (frameCurve frame) branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {first last reference moving zero : BranchIsolation.Data.Index branches}
    {prior : BranchArea.CommonLoop lifted sheet}
    (row : BranchArea.PairedRow bank reference sheet (first, last) prior)
    (lastEq : last = moving) (referenceEq : reference = zero)
    (waist : BasedBranchBank.Pair bank moving zero sheet)
    (repeated : BasedBranchBank.Pair bank moving moving sheet)
    (value : OrientedEdge lifted.vertices.count → Canonical) :
    wordValue value row.a.closed.indexed = wordValue value row.b.closed.indexed -
      wordValue value waist.closed.indexed + wordValue value repeated.closed.indexed := by
  cases lastEq
  cases referenceEq
  exact BasedBranchRelations.Pair.reference_value row.a row.b waist repeated value

/-- The original repeated-pair identity transports only the actual moving-branch index to its retained hole. -/
private theorem repeated_physical {base : FramedPuncturedGrid (frameCurve frame) branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {moving : BranchIsolation.Data.Index branches}
    (hole : BranchHole base.bank.toBranchCellBank) (same : hole.index = moving)
    (repeated : BasedBranchBank.Pair bank moving moving sheet)
    (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    wordValue value repeated.closed.indexed =
      -wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  cases same
  exact BasedBranchRelations.Pair.repeated_hole_value hole repeated value anti

public section

namespace BranchLabels

variable {base : FramedPuncturedGrid (frameCurve frame) branches higher}
  {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchBank.Ordered bank sheet}
  {paired : OrderedBranchPairs.Ordered.Paired ordered}

/-- The actual moving-zero pair reads as canonical B minus canonical A with its complete repeated-branch correction.

The A and corrected B words come from the same retained prepared genus-one
row. Its earlier-A prefix is empty. The repeated moving-branch word stays
explicit; no physical hole or face contribution is assumed to vanish.
-/
theorem waist_value (labels : BranchLabels frame base.bank.toBranchCellBank)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1)
    (prepared : PeriodPrograms.Prepared paired)
    (waist : BasedBranchBank.Pair bank (labels.val.backward 1) (labels.val.backward 0) sheet)
    (repeated : BasedBranchBank.Pair bank (labels.val.backward 1) (labels.val.backward 1) sheet)
    (value : OrientedEdge lifted.vertices.count → Canonical) :
    wordValue value waist.closed.indexed = wordValue value (prepared.bWord 0) -
      wordValue value (prepared.aWord 0) + wordValue value repeated.closed.indexed := by
  have indices := labels.paired_labels real positive unit paired
  have relation := retained_reference (paired.row 0).row (congrArg Prod.snd indices.1) indices.2
    waist repeated value
  have a := congrArg (wordValue value) (prepared.aWord_eq 0)
  have prefixValue := PrefixValues.Prepared.bWord_prefix_value paired prepared value 0
  have empty : sumFin (fun earlier : Fin 1 => if earlier.val < 0 then
      wordValue value (prepared.aWord earlier) else 0) = 0 :=
    (Purelib.Algebra.FiniteSum.Fin.sumFin_congr (fun earlier => if_neg (Nat.not_lt_zero earlier.val))).trans
      Purelib.Algebra.FiniteSum.Fin.sumFin_zero
  have b : wordValue value (prepared.bWord 0) = wordValue value (paired.row 0).row.b.closed.indexed :=
    prefixValue.trans ((congrArg (wordValue value (paired.row 0).row.b.closed.indexed + ·) empty).trans
      (Data.Gaussian.Basic.add_zero _))
  calc
    _ = wordValue value (paired.row 0).row.b.closed.indexed -
        wordValue value (paired.row 0).row.a.closed.indexed + wordValue value repeated.closed.indexed := by
      rewrite [relation]
      ring1
    _ = _ := by rewrite [← a, ← b]; rfl

/-- The actual moving-zero pair retains the clockwise physical boundary of its original moving-branch hole.

The hole is obtained from the same cached face list and its existing
coverage law. The canonical B-minus-A expression includes that actual
boundary; antisymmetry alone does not remove it.
-/
theorem waist_physical_value (labels : BranchLabels frame base.bank.toBranchCellBank)
    (real : parameter.im = 0) (positive : 0 < parameter.re) (unit : parameter.re < 1)
    (prepared : PeriodPrograms.Prepared paired)
    (waist : BasedBranchBank.Pair bank (labels.val.backward 1) (labels.val.backward 0) sheet)
    (repeated : BasedBranchBank.Pair bank (labels.val.backward 1) (labels.val.backward 1) sheet)
    (value : OrientedEdge lifted.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    ∃ hole ∈ base.faces.holes,
      wordValue value waist.closed.indexed = wordValue value (prepared.bWord 0) -
        wordValue value (prepared.aWord 0) -
          wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  rcases base.faces.hole_complete (labels.val.backward 1) with ⟨hole, member, same⟩
  refine ⟨hole, member, ?_⟩
  have actual := waist_value (base := base) (lifted := lifted) (bank := bank)
    (sheet := sheet) (ordered := ordered) labels real positive unit prepared waist repeated value
  have physical := repeated_physical (base := base) (lifted := lifted) (bank := bank)
    (sheet := sheet) hole same repeated value anti
  exact (actual.trans (congrArg
    (wordValue value (prepared.bWord 0) - wordValue value (prepared.aWord 0) + ·) physical)).trans
      (Data.Gaussian.Basic.sub_eq_add_neg _ _).symm

end BranchLabels

end

end Purelib.Curves.Legendre.Periods.Fibre
