module
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.CellularHomology
public import Purelib.Topology.Surface.CellularHomology.GenusOne.Basic

open Purelib

open Purelib.Topology.Surface

open Purelib.Topology.Surface.CellularHomology

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.Topology.Surface.CellularHomology.GenusOne.Transvection

/-- The plus-sign transvection fixed by `a · b = +1`. -/
def transvection (delta gamma :
  GenusOne.Basic.Homology) : GenusOne.Basic.Homology :=
  Data.Vector.Basic.vectorOfFn fun coordinate =>
    gamma coordinate +
      CellularHomology.intersection gamma delta * delta coordinate
end Purelib.Topology.Surface.CellularHomology.GenusOne.Transvection

end
