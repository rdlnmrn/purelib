module
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.RootIsolation.Progressive.Chamber.Names
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Closure.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
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

namespace Purelib.RootIsolation.Progressive.Chamber.Frame
namespace ChamberFrame

/-- Every requested finite prefix of the retained chamber root name is productive. -/
theorem rootName_productive (frame :
  Progressive.Chamber.Frame.ChamberFrame)
    (index : frame.Index) (count : Nat) :
    (frame.rootName index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (frame.rootName index).machine count).emitted ∧
      (Machine.Advance.advance
          (frame.rootName index).machine count).emitted.length = count :=
  frame.closure.roots_productive index count

/-- Parsing the retained root name recovers the original chamber frame's root output exactly. -/
theorem rootName_exact (frame :
  Progressive.Chamber.Frame.ChamberFrame)
    (index : frame.Index) (count : Nat) :
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      (frame.closure.continuation.toProcess index)
      frame.closure.continuation.initial
      (Machine.Advance.advance
        (frame.rootName index).machine count) :=
  frame.closure.roots_exact index count
end ChamberFrame

end Purelib.RootIsolation.Progressive.Chamber.Frame

end
