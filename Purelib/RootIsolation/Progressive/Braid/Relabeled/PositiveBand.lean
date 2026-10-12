module
import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.OrbitLabeling
public import Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.Topology.Knot.Braid.PositiveBand.Basic
public import Purelib.Topology.Knot.Braid.PositiveBand.Labeling
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`Bijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic

namespace RelabeledLoopBraid

/-- Canonical positive-band representative of a one-cycle loop, using the
inverse orbit of one displayed base owner as its strand labelling. -/
def positiveBandOfSingleCycle
    {frame : Progressive.Chamber.Frame.ChamberFrame}
    {loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame}
    (positive : 0 < frame.degree)
    (cycle : Data.Fin.Bijection.IsSingleCycle
      loop.monodromy)
    (base : frame.Index) : Progressive.Braid.Relabeled.Basic.RelabeledLoopBraid frame loop where
  word := Topology.Knot.Braid.PositiveBand.Basic.positiveBand frame.degree
  labeling := Data.Fin.Bijection.OrbitLabeling.inverseOrbitLabeling
    loop.monodromy cycle base
  agrees := Topology.Knot.Braid.PositiveBand.Labeling.positiveBand_agrees positive
    loop.monodromy cycle base
end RelabeledLoopBraid

end Purelib.RootIsolation.Progressive.Braid.Relabeled.Basic

end
