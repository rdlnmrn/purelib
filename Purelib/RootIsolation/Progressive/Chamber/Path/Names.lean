module
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Names
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport

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

namespace Purelib.RootIsolation.Progressive.Chamber.Path.Basic
namespace ChamberPath

/-- The arithmetic-ready persistent CCL name at the endpoint selected by
finite owner transport from one starting owner. -/
def finalRootName {start finish :
  Progressive.Chamber.Frame.ChamberFrame}
    (path : Progressive.Chamber.Path.Basic.ChamberPath start finish) (index : start.Index) :
    Name.Basic.Named :=
  finish.rootName (path.finalIndex index)
end ChamberPath

end Purelib.RootIsolation.Progressive.Chamber.Path.Basic

end
