module
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
import Purelib.RootIsolation.Progressive.Braid.Projected.Path
public import Purelib.RootIsolation.Progressive.Braid.Projected.Refinement
public import Purelib.Topology.Knot.Braid.Artin
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Word.Writhe

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Braid.Projected.Path (ProjectedPath)
open Purelib.Topology.Knot.Braid.Artin (Equivalent)

open Purelib.RootIsolation

open Purelib

section
@[expose] public section

/-!
# Subdivision and Artin invariance of projected braid extraction

This file gives an operational notion of further subdivision.  A stationary
cell may be replaced by an all-stationary finite chain.  A crossing cell may
be replaced by a finite chain containing exactly the same signed crossing,
with any number of stationary cells before and after it.  Applying this rule
cell by cell is a refinement of a projected path.

The resulting extracted word is proved equal, rather than merely assumed
equal.  A second relation permits the finite cancellation, far-commutation,
and three-strand Artin moves from `ArtinRelations`.  Both relations preserve
the endpoint owner transport, and concatenation respects the Artin relation.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected.Artin

/-! ## Artin-equivalent projected paths -/

/-- Two certified projected paths represent the same braid class when their
extracted words are joined by a finite proof made from the Artin rewrites. -/
def BraidClassSame {strands : Nat}
    {start finish : ProjectedFrame strands}
    (left right : ProjectedPath start finish) : Prop :=
  Equivalent left.word right.word

namespace BraidClassSame

/-- Every retained projected path represents its own extracted braid class. -/
theorem refl {strands : Nat} {start finish
  : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
      Progressive.Braid.Projected.Artin.BraidClassSame path path :=
  Equivalent.refl path.word

/-- Reverse the finite Artin equivalence between two retained path words. -/
theorem symm {strands : Nat} {start finish
  : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : Progressive.Braid.Projected.Artin.BraidClassSame left right) :
      Progressive.Braid.Projected.Artin.BraidClassSame right left :=
  Equivalent.symm same

/-- Compose finite Artin equivalences of three retained path words. -/
theorem trans {strands : Nat} {start
  finish : ProjectedFrame strands}
    {first second third : ProjectedPath start finish}
    (firstSecond : Progressive.Braid.Projected.Artin.BraidClassSame first second)
    (secondThird : Progressive.Braid.Projected.Artin.BraidClassSame second third) :
    Progressive.Braid.Projected.Artin.BraidClassSame first third :=
  Equivalent.trans firstSecond secondThird

/-- An event-preserving refinement retains the original projected path's braid class. -/
theorem of_refinement {strands : Nat}
    {start finish : ProjectedFrame strands}
    {coarse fine : ProjectedPath start finish}
    (refinement : RootIsolation.Progressive.Braid.Projected.Refinement coarse fine) :
      Progressive.Braid.Projected.Artin.BraidClassSame coarse fine := by
  unfold Progressive.Braid.Projected.Artin.BraidClassSame
  rw [refinement.word_eq]
  exact Equivalent.refl _

/-- Concatenating pairs of Artin-equivalent retained paths preserves their braid class. -/
theorem append {strands : Nat}
    {start middle finish : ProjectedFrame strands}
    {firstLeft firstRight : ProjectedPath start middle}
    {secondLeft secondRight : ProjectedPath middle finish}
    (first : Progressive.Braid.Projected.Artin.BraidClassSame firstLeft firstRight)
    (second : Progressive.Braid.Projected.Artin.BraidClassSame secondLeft secondRight) :
    Progressive.Braid.Projected.Artin.BraidClassSame (firstLeft.append secondLeft)
      (firstRight.append secondRight) := by
  unfold Progressive.Braid.Projected.Artin.BraidClassSame
  rw [ProjectedPath.word_append,
    ProjectedPath.word_append]
  exact Equivalent.append first second

/-- Artin-equivalent extractions have the same endpoint owner transport. -/
theorem transport_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : Progressive.Braid.Projected.Artin.BraidClassSame left right) (position : Fin strands) :
    left.chamberPath.transport.forward (start.ownerIndex position) =
      right.chamberPath.transport.forward (start.ownerIndex position) := by
  calc
    left.chamberPath.transport.forward (start.ownerIndex position) =
        finish.ownerIndex (left.word.permutation.forward position) :=
      left.transport_agrees position
    _ = finish.ownerIndex (right.word.permutation.forward position) :=
      congrArg finish.ownerIndex (same.permutationSame position)
    _ = right.chamberPath.transport.forward (start.ownerIndex position) :=
      (right.transport_agrees position).symm

/-- Artin-equivalent retained projected paths have the same extracted writhe. -/
theorem writhe_eq {strands : Nat}
    {start finish : ProjectedFrame strands}
    {left right : ProjectedPath start finish}
    (same : Progressive.Braid.Projected.Artin.BraidClassSame left right) :
    left.word.writhe = right.word.writhe :=
  Equivalent.writhe_eq same

end BraidClassSame

end Purelib.RootIsolation.Progressive.Braid.Projected.Artin

end
