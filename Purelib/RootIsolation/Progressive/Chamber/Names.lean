module
public import Purelib.RootIsolation.Progressive.Closure.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Frame

open Purelib.Approximation.Gaussian

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

/-- The executable degree-many persistent root family belonging to this
chamber frame. -/
def closure (frame :
  Progressive.Chamber.Frame.ChamberFrame) :
    Progressive.Closure.Basic.EffectiveAlgebraicClosure frame.chamber :=
  frame.chamber.effectiveAlgebraicClosure

/-- Read the productive arithmetic root name at the original finite chamber index. -/
def rootName (frame :
  Progressive.Chamber.Frame.ChamberFrame) (index : frame.Index) :
    Name.Basic.Named :=
  frame.closure.roots index
end ChamberFrame

end Purelib.RootIsolation.Progressive.Chamber.Frame

end
