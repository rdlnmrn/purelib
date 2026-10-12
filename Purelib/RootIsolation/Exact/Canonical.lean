module
import Purelib.Data.Int.Order
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.Build
import Purelib.RootIsolation.Exact.Extraction
public import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.Run
import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Exact.Step

import Purelib.Data.Rat.Fraction.Order
public import Purelib.RootIsolation.Track.Newton.Canonical
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Tactic.Ring

open Purelib.RootIsolation.Exact.State (IsolationState)
open Purelib.RootIsolation.Track.Newton (Canonical)
open Purelib.RootIsolation.Track.Newton.Canonical (All)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-! Every track produced by canonical isolation retains the original Newton
refinement operation, for every supplied current state. This identifies the
operation needed when restoring branch-cell refinements from checkpoints. -/
namespace Purelib.RootIsolation.Exact.Canonical

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)

/-- The track extracted from the original selected positive region uses canonical Newton refinement. -/
theorem extraction (selected : Clearance.Box.Region.ClearRegion p ambient)
  (positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p selected.box) :
    Canonical degreeAtLeastTwo squarefree elimination
      (Exact.Extraction.extractRegion degreeAtLeastTwo squarefree elimination selected positive).track := by
  intro current epsilon epsilonPositive
  rfl

/-- One original isolation step preserves canonical Newton refinement of every retained track. -/
theorem step_preserves (state : IsolationState p ambient)
    (nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions) (known : All degreeAtLeastTwo
      squarefree elimination state.tracks) :
    All degreeAtLeastTwo squarefree elimination
      (Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive).next.tracks := by
  let selection := Winding.Box.Region.Selection.selectPositive state.regions nonnegative positive
  change All degreeAtLeastTwo squarefree elimination
    ((Exact.Extraction.extractRegion degreeAtLeastTwo squarefree elimination selection.selected
      selection.positive).track :: state.tracks)
  exact Canonical.cons degreeAtLeastTwo squarefree elimination
    (extraction degreeAtLeastTwo squarefree elimination selection.selected selection.positive) known

/-- The complete finite isolation run preserves canonical refinement of the retained track list. -/
theorem run_preserves (steps : Nat) (state : IsolationState p
  ambient)
    (total : Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * steps)
    (known : All degreeAtLeastTwo squarefree elimination state.tracks) :
    All degreeAtLeastTwo squarefree elimination
      (Exact.Run.run degreeAtLeastTwo squarefree elimination steps state total).final.tracks := by
  induction steps generalizing state with
  | zero => exact known
  | succ steps ih =>
      have positive : 0 < Winding.Box.Region.Sum.totalRaw state.regions := by
        rw [total]
        exact Purelib.Data.Int.Order.mul_pos (by decide)
          (Purelib.Data.Int.Order.natCast_pos (Nat.zero_lt_succ steps))
      have nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
        intro region _
        exact Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative degreeAtLeastTwo squarefree
          elimination
          region.refinesAmbient region.proper region.clearance
      let first := Exact.Step.step degreeAtLeastTwo squarefree elimination state nonnegative positive
      have nextTotal : Winding.Box.Region.Sum.totalRaw first.next.regions = (4 : Int) * steps := by
        rw [first.totalRaw_next, total, Nat.cast_succ]
        ring1
      change All degreeAtLeastTwo squarefree elimination
        (Exact.Run.run degreeAtLeastTwo squarefree elimination steps first.next nextTotal).final.tracks
      exact ih first.next nextTotal (step_preserves degreeAtLeastTwo squarefree elimination state
        nonnegative positive known)

/-- Every track isolated from the original clear region has canonical Newton refinement. -/
theorem fromRegion (region : Clearance.Box.Region.ClearRegion p ambient)
  (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p region.box = (4 : Int) * count) :
    All degreeAtLeastTwo squarefree elimination
      (Exact.Build.isolateFromRegion degreeAtLeastTwo squarefree elimination region count raw).tracks := by
  let state := IsolationState.initial region
  have total : Winding.Box.Region.Sum.totalRaw state.regions = (4 : Int) * count := by
    change Winding.Box.Basic.quadrupledBoxWinding p region.box + 0 = _
    rw [raw, add_zero]
  exact run_preserves degreeAtLeastTwo squarefree elimination count state total
    (Canonical.nil degreeAtLeastTwo squarefree elimination)

/-- Every track in the original coefficient-computed large-square output has canonical Newton refinement. -/
theorem largeSquare : All degreeAtLeastTwo
  squarefree elimination
    (Exact.LargeSquare.isolateLargeSquare degreeAtLeastTwo squarefree elimination).tracks := by
  unfold Exact.LargeSquare.isolateLargeSquare
  apply fromRegion

/-- The track at a retained output index inherits canonical refinement from the original track list. -/
theorem trackAt {count : Nat} (output : Exact.Basic.Output p ambient count)
    (known : All degreeAtLeastTwo squarefree elimination output.tracks) (index : Fin count) :
    Canonical degreeAtLeastTwo squarefree elimination (output.trackAt index) :=
  known _ (List.getElem_mem (output.trackIndex index).isLt)

end Purelib.RootIsolation.Exact.Canonical

end
