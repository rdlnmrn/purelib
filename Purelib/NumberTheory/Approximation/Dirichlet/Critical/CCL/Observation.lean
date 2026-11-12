module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.History
public import Purelib.Approximation.Gaussian.Observation.Prefix.Family

/-!
# Rational observation families of retained RFAP histories

The original joint history supplies the proper prefix enclosure, exact
parser and inverse chart. Every later recorded request refines that box.
Each separated rational leaf consequently preserves the original raw word
and all retained consecutive-best and threshold-violation certificates.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.History

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical
open Purelib.Approximation.Gaussian.Observation
open Purelib.Geometry.Rational.Box

variable {threshold : Fraction.Rational} {certificate : Sharpness.IsSharperWindowThreshold threshold}

/-- Record numerical requests from the original joint history's exact cached prefix enclosure. -/
@[expose] def record (history : History threshold certificate) (requests : List Cursor.Request) :
    Prefix.Source.Recording (Prefix.Source.Snapshot.ofEnclosure history.enclosure) :=
  (Prefix.Source.Recording.start (Prefix.Source.Snapshot.ofEnclosure history.enclosure)).execute requests

/-- Construct separated rational continuations of the actual numerical recording inside the retained RFAP box. -/
def observationFamily (history : History threshold certificate) (requests : List Cursor.Request) (depth : Nat) :
    Prefix.Source.Recording.Family (history.record requests) depth :=
  Prefix.Source.Recording.Family.build (history.record requests) depth

/-- Every retained observation leaf lies in the same original RFAP history's proper box. -/
theorem leaf_inside (history : History threshold certificate)
    (recording : Prefix.Source.Recording (Prefix.Source.Snapshot.ofEnclosure history.enclosure)) {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Prefix.Source.Recording.Leaf recording tree) :
    history.box.Contains leaf.admitted.realization.point := by
  have currentInside := leaf.pointEq.symm ▸ tree.point_inside leaf.address
  exact recording.originRefines.contains currentInside

/-- Each observation leaf realizes the exact original raw word with its same cached parser and inverse chart. -/
theorem leaf_wordRepresented (history : History threshold certificate)
    (recording : Prefix.Source.Recording (Prefix.Source.Snapshot.ofEnclosure history.enclosure)) {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Prefix.Source.Recording.Leaf recording tree) :
    CCL.Encoding.Parser.Semantics.Prefix.Represented history.word leaf.admitted.realization.point :=
  history.enclosure.represented (history.leaf_inside recording leaf)

/-- Every original retained RFAP window is consecutive best at each rational observation leaf. -/
theorem leaf_consecutive (history : History threshold certificate)
    (recording : Prefix.Source.Recording (Prefix.Source.Snapshot.ofEnclosure history.enclosure)) {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Prefix.Source.Recording.Leaf recording tree)
    (entry : Robust.WindowHistory.Entry threshold) (member : entry ∈ history.robust.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest leaf.admitted.realization.point entry.2.lower entry.2.upper :=
  history.robust.uniformConsecutive _ (history.boxEq ▸ history.leaf_inside recording leaf) entry member

/-- Every original retained RFAP window violates its threshold at each rational observation leaf. -/
theorem leaf_violation (history : History threshold certificate)
    (recording : Prefix.Source.Recording (Prefix.Source.Snapshot.ofEnclosure history.enclosure)) {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Prefix.Source.Recording.Leaf recording tree)
    (entry : Robust.WindowHistory.Entry threshold) (member : entry ∈ history.robust.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      leaf.admitted.realization.point entry.2.lower entry.2.upper :=
  history.robust.uniformViolation _ (history.boxEq ▸ history.leaf_inside recording leaf) entry member

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.History

end
