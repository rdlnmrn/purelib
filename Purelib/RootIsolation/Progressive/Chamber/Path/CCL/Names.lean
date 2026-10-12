module
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.RootIsolation.Progressive.Chamber.Names
import Purelib.RootIsolation.Progressive.Chamber.CCL.Names
public import Purelib.RootIsolation.Progressive.Chamber.Path.Names
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.RootIsolation.Progressive.Closure.Basic
import Purelib.RootIsolation.Progressive.Continuation.Approximation
import Purelib.RootIsolation.Progressive.Continuation.Basic

open Purelib.Data.CCL.Transducer (Machine)

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

/-- Every finite prefix of the root name at the path's actual final index is productive. -/
theorem finalRootName_productive
    {start finish : Progressive.Chamber.Frame.ChamberFrame} (path : Progressive.Chamber.Path.Basic.ChamberPath start
      finish)
    (index : start.Index) (count : Nat) :
    (path.finalRootName index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (path.finalRootName index).machine count).emitted ∧
      (Machine.Advance.advance
          (path.finalRootName index).machine count).emitted.length = count :=
  finish.rootName_productive (path.finalIndex index) count

/-- Parsing the final root name recovers the output at the path's retained final index exactly. -/
theorem finalRootName_exact
    {start finish : Progressive.Chamber.Frame.ChamberFrame} (path : Progressive.Chamber.Path.Basic.ChamberPath start
      finish)
    (index : start.Index) (count : Nat) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (finish.closure.continuation.toProcess (path.finalIndex index))
      finish.closure.continuation.initial
      (Machine.Advance.advance
        (path.finalRootName index).machine count) :=
  finish.rootName_exact (path.finalIndex index) count
end ChamberPath

end Purelib.RootIsolation.Progressive.Chamber.Path.Basic

end
