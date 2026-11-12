module
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
public import Purelib.RootIsolation.Progressive.Chamber.Path.Basic

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Path.Basic
namespace ChamberPath

/-- Compose the original finite path's owner matchings into a bijection between its endpoint index sets. -/
def transport : {start finish :
  ChamberFrame} →
    ChamberPath start finish → Data.Fin.Bijection start.degree
      finish.degree
  | _, _, .nil frame => Data.Fin.Bijection.identity frame.degree
  | _, _, .cons step remaining =>
      Data.Fin.Bijection.comp remaining.transport step.matching

/-- Transport an original starting owner index to its retained finishing-frame index. -/
def finalIndex {start finish :
  ChamberFrame}
    (path : ChamberPath start finish) (index : start.Index) : finish.Index :=
  path.transport.forward index

/-- The empty chamber path preserves the original owner index. -/
@[simp] theorem finalIndex_nil (frame :
  ChamberFrame) (index : frame.Index) :
    (nil frame).finalIndex index = index := rfl

/-- A path step first applies its original overlap matching before the remaining transport. -/
@[simp] theorem finalIndex_cons
    {start middle finish : ChamberFrame}
    (step : Overlap.ChamberOverlap start middle)
    (remaining : ChamberPath middle finish) (index : start.Index) :
    (cons step remaining).finalIndex index =
      remaining.finalIndex (step.matching.forward index) := rfl

/-- Transport along joined chamber paths composes their original forward owner maps. -/
theorem transport_append
    {start middle finish : ChamberFrame}
    (first : ChamberPath start middle)
    (second : ChamberPath middle finish) (index : start.Index) :
    (first.append second).transport.forward index =
      second.transport.forward (first.transport.forward index) := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      exact inductionHypothesis second (step.matching.forward index)

/-- The final index of a joined path is obtained by transporting through its original shared middle frame. -/
theorem finalIndex_append
    {start middle finish : ChamberFrame}
    (first : ChamberPath start middle) (second :
      ChamberPath middle finish)
    (index : start.Index) :
    (first.append second).finalIndex index =
      second.finalIndex (first.finalIndex index) :=
  transport_append first second index

/-- The reversed path's forward owner map is the original path's backward map. -/
theorem transport_reverse_forward
    {start finish : ChamberFrame} (path : ChamberPath start
      finish)
    (index : finish.Index) :
    path.reverse.transport.forward index = path.transport.backward index := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      change
        (remaining.reverse.append
          (.cons step.reverse (.nil _))).transport.forward index = _
      rw [transport_append]
      change step.matching.backward
          (remaining.reverse.transport.forward index) = _
      rw [inductionHypothesis]
      rfl

/-- Reversing a chamber path gives the inverse of its original retained owner bijection. -/
theorem transport_reverse
    {start finish : ChamberFrame} (path : ChamberPath start
      finish) :
    Data.Fin.Bijection.Same path.reverse.transport path.transport.reverse :=
  path.transport_reverse_forward

/-- The reversed original path returns every selected endpoint to its original bounded occurrence. -/
theorem finalIndex_reverse {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : start.Index) : path.reverse.finalIndex (path.finalIndex index) = index := by
  rewrite [finalIndex, path.transport_reverse_forward]
  exact path.transport.backward_forward index

/-- Joining paths concatenates their actual ordered selected bridge-box lists. -/
theorem bridgeBoxes_append {start middle finish : ChamberFrame}
    (first : ChamberPath start middle) (second : ChamberPath middle finish) (index : start.Index) :
    (first.append second).bridgeBoxes index =
      first.bridgeBoxes index ++ second.bridgeBoxes (first.finalIndex index) := by
  induction first with
  | nil => rfl
  | cons step remaining previous =>
    change (step.bridge index).box :: (remaining.append second).bridgeBoxes (step.matching.forward index) = _
    rewrite [previous second (step.matching.forward index)]
    rfl

/-- Reversing the original selected path reverses exactly the same finite bridge boxes. -/
theorem bridgeBoxes_reverse {start finish : ChamberFrame}
    (path : ChamberPath start finish) (index : start.Index) :
    path.reverse.bridgeBoxes (path.finalIndex index) = (path.bridgeBoxes index).reverse := by
  induction path with
  | nil => rfl
  | cons step remaining previous =>
    change (remaining.reverse.append (.cons step.reverse (.nil _))).bridgeBoxes
      (remaining.finalIndex (step.matching.forward index)) = _
    rewrite [bridgeBoxes_append, previous (step.matching.forward index)]
    change (remaining.bridgeBoxes (step.matching.forward index)).reverse ++
      [(step.bridge (step.matching.backward
        (remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index))))).reverse.box] = _
    rewrite [remaining.finalIndex_reverse, step.matching.backward_forward]
    change (remaining.bridgeBoxes (step.matching.forward index)).reverse ++ [(step.bridge index).box] =
      ((step.bridge index).box :: remaining.bridgeBoxes (step.matching.forward index)).reverse
    exact (Data.List.Reverse.reverse_cons _ _).symm

/-- Reverse an exact retained selected-box list without rerunning the original path selectors. -/
def reverseBridgeBoxes {start finish : ChamberFrame} (path : ChamberPath start finish) (index : start.Index)
    (boxes : { value : List Geometry.Rational.Box // value = path.bridgeBoxes index }) :
    { value : List Geometry.Rational.Box // value = path.reverse.bridgeBoxes (path.finalIndex index) } :=
  ⟨boxes.val.reverse, (congrArg List.reverse boxes.property).trans (path.bridgeBoxes_reverse index).symm⟩

/-- The monodromy of a displayed closed finite chamber path. -/
def monodromy {frame :
  ChamberFrame} (loop : ChamberPath frame frame) :
    Data.Fin.Bijection frame.degree frame.degree :=
  loop.transport

/-- The monodromy of joined loops composes their original forward owner permutations. -/
theorem monodromy_append {frame :
  ChamberFrame}
    (first second : ChamberPath frame frame) (index : frame.Index) :
    (first.append second).monodromy.forward index =
      second.monodromy.forward (first.monodromy.forward index) :=
  first.transport_append second index

/-- The reversed loop has the inverse of its original owner monodromy. -/
theorem monodromy_reverse {frame :
  ChamberFrame}
    (loop : ChamberPath frame frame) :
    Data.Fin.Bijection.Same loop.reverse.monodromy loop.monodromy.reverse :=
  loop.transport_reverse

end ChamberPath

end Purelib.RootIsolation.Progressive.Chamber.Path.Basic

end
