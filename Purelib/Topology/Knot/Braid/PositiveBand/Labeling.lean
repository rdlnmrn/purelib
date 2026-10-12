module
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Cycle
public import Purelib.Data.Fin.Bijection.OrbitLabeling
public import Purelib.Topology.Knot.Braid.PositiveBand.Basic
import Purelib.Topology.Knot.Braid.PositiveBand.Permutation
import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Topology.Knot.Braid

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

namespace Purelib.Topology.Knot.Braid.PositiveBand.Labeling

section

/-- The positive Artin band has exactly the relabelled endpoint action of any displayed one-cycle permutation. -/
theorem positiveBand_agrees {count : Nat} (positive : 0 <
  count)
    (bijection : Data.Fin.Bijection count count)
    (cycle : Data.Fin.Bijection.IsSingleCycle bijection)
    (base position : Fin count) :
    bijection.forward
        ((OrbitLabeling.inverseOrbitLabeling bijection cycle base).forward position) =
      (OrbitLabeling.inverseOrbitLabeling bijection cycle base).forward
        ((PositiveBand.Basic.positiveBand count).permutation.forward
          position) := by
  rw [PositiveBand.Permutation.positiveBand_permutation_forward positive]
  exact OrbitLabeling.forward_inverseOrbitLabeling positive bijection cycle base position

end

end Purelib.Topology.Knot.Braid.PositiveBand.Labeling

end
