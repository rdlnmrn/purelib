module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)

open Purelib

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

namespace Purelib.RootIsolation.Progressive.Chamber.Path.Local

/-! ## Paths retained inside one chamber -/

set_option genInjectivity false in
/-- A path explicitly retained inside one certified chamber.  Each step may
carry a different finite Rouché calculation, but both endpoint owner families
are the same chamber family. -/
inductive LocalPath (frame :
  ChamberFrame) : Type 2
  /-- The empty path inside the original chamber frame. -/ | nil :
    LocalPath frame
  /-- An original self-overlap followed by a retained path in that same chamber. -/ | cons (step :
    Progressive.Chamber.Overlap.ChamberOverlap frame frame)
      (remaining : LocalPath frame) :
        LocalPath frame

constructive_injectivity LocalPath

namespace LocalPath

/-- Read the original finite chamber path underlying the retained sequence of self-overlaps. -/
@[expose] def toPath {frame :
  ChamberFrame} : Progressive.Chamber.Path.Local.LocalPath frame →
  Progressive.Chamber.Path.Basic.ChamberPath frame frame
  | .nil => .nil frame
  | .cons step remaining => .cons step remaining.toPath

/-- Read owner transport along the original chamber-contained path. -/
@[expose] def monodromy {frame :
  ChamberFrame} (path : Progressive.Chamber.Path.Local.LocalPath frame) :
    Data.Fin.Bijection frame.degree frame.degree :=
  path.toPath.monodromy

/-- A chamber-contained path has identity monodromy, regardless of how many
finite refinements or redundant self-overlap certificates it contains. -/
theorem monodromy_identity {frame :
  ChamberFrame}
    (path : Progressive.Chamber.Path.Local.LocalPath frame) :
    Data.Fin.Bijection.Same path.monodromy
      (Data.Fin.Bijection.identity frame.degree) := by
  intro index
  induction path generalizing index with
  | nil => rfl
  | cons step remaining inductionHypothesis =>
      change remaining.monodromy.forward (step.matching.forward index) = index
      rw [inductionHypothesis]
      exact step.forward_eq_self index

end LocalPath

end Purelib.RootIsolation.Progressive.Chamber.Path.Local

end
