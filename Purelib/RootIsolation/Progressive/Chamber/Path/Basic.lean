module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
public import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic

open Purelib.Geometry.Rational

open Purelib.RootIsolation

section
public section

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

/-! ## Finite chamber paths and their monodromy -/

set_option genInjectivity false in
/-- A finite coefficient path is a finite inductive chain of certified
chamber overlaps.  The endpoint indices remain dependent on their displayed
frames, so unequal degrees cannot be joined accidentally. -/
inductive ChamberPath : (start finish : Progressive.Chamber.Frame.ChamberFrame) → Type 2
  /-- The empty retained chamber path at one original frame. -/ | nil (frame : Progressive.Chamber.Frame.ChamberFrame) :
    Purelib.RootIsolation.Progressive.Chamber.Path.Basic.ChamberPath frame frame
  /-- Prepend an original chamber overlap to a path beginning at its exact finishing frame. -/ | cons {start middle
    finish : Progressive.Chamber.Frame.ChamberFrame}
      (step : Progressive.Chamber.Overlap.ChamberOverlap start middle)
      (remaining : Purelib.RootIsolation.Progressive.Chamber.Path.Basic.ChamberPath middle finish) :
        Purelib.RootIsolation.Progressive.Chamber.Path.Basic.ChamberPath start finish

constructive_injectivity ChamberPath

namespace ChamberPath

/-- Count the actual retained chamber overlaps in a finite path. -/
@[expose] def stepCount : {start finish : Progressive.Chamber.Frame.ChamberFrame} →
    Progressive.Chamber.Path.Basic.ChamberPath start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.stepCount + 1

/-- The finite list of rational Rouché bridge boxes traversed by one initial
owner.  Its index is updated by the certified matching at every step. -/
@[expose] def bridgeBoxes : {start finish : Progressive.Chamber.Frame.ChamberFrame} →
    (path : Progressive.Chamber.Path.Basic.ChamberPath start finish) → start.Index → List Box
  | _, _, .nil _, _ => []
  | _, _, .cons step remaining, index =>
      (step.bridge index).box ::
        remaining.bridgeBoxes (step.matching.forward index)

/-- Every original owner traverses exactly one retained bridge box per path step. -/
@[simp] theorem bridgeBoxes_length
    {start finish : Progressive.Chamber.Frame.ChamberFrame} (path : Progressive.Chamber.Path.Basic.ChamberPath start
      finish)
    (index : start.Index) :
    (path.bridgeBoxes index).length = path.stepCount := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, Progressive.Chamber.Path.Basic.ChamberPath.bridgeBoxes, List.length_cons,
        Progressive.Chamber.Path.Basic.ChamberPath.stepCount,
        inductionHypothesis]
      rfl

/-- Join compatible finite chamber paths at their exact shared middle frame. -/
@[expose] def append {start middle finish : Progressive.Chamber.Frame.ChamberFrame}
    (first : Progressive.Chamber.Path.Basic.ChamberPath start middle)
    (second : Progressive.Chamber.Path.Basic.ChamberPath middle finish) : Progressive.Chamber.Path.Basic.ChamberPath
      start finish :=
  match first with
  | .nil _ => second
  | .cons step remaining => .cons step (remaining.append second)

/-- Joining finite chamber paths is associative. -/
theorem append_assoc
    {first second third fourth : Progressive.Chamber.Frame.ChamberFrame}
    (left : Progressive.Chamber.Path.Basic.ChamberPath first second) (middle :
      Progressive.Chamber.Path.Basic.ChamberPath second third)
    (right : Progressive.Chamber.Path.Basic.ChamberPath third fourth) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | cons step remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, Progressive.Chamber.Path.Basic.ChamberPath.append, inductionHypothesis]
      rfl

/-- Reverse a finite chamber path and each of its original certified overlaps. -/
@[expose] def reverse : {start finish : Progressive.Chamber.Frame.ChamberFrame} →
    Progressive.Chamber.Path.Basic.ChamberPath start finish → Progressive.Chamber.Path.Basic.ChamberPath finish start
  | _, _, .nil frame => .nil frame
  | _, _, .cons step remaining =>
      remaining.reverse.append (.cons step.reverse (.nil _))
end ChamberPath

end Purelib.RootIsolation.Progressive.Chamber.Path.Basic

end
