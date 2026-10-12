module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.Data.Fin.Bijection.Cycle
import Purelib.Data.Fin.Bijection.Iteration
public import Purelib.Data.Fin.Bijection.Search
public import Purelib.Data.Fin.Cyclic.Predecessor

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Fin.Bijection

open Purelib.Data.Fin.Cyclic

open Purelib.Data

section
public section

/-!
# Constructive orbit labelling of cyclic monodromy

A finite one-cycle permutation can be labelled without any choice principle:
select one displayed base index and enumerate the orbit of the explicit
inverse map.  Bounded preimage search turns that injective enumeration into a
`Bijection`.  With this labelling, the original permutation is exactly
the cyclic predecessor, hence exactly the endpoint action of the positive
Artin band `sigma_1 ... sigma_(d-1)`.
-/

namespace Purelib.Data.Fin

namespace Bijection.OrbitLabeling

/-- Label a finite single cycle by successive backward iterates from a displayed base.

Use bounded preimage search to invert the injective enumeration of inverse-orbit
positions. The supplied base and cycle certificate determine the retained forward
map. -/
@[expose] def inverseOrbitLabeling {count : Nat}
    (bijection : Bijection count count)
    (cycle : IsSingleCycle bijection)
    (base : Fin count) : Bijection count count :=
  Bijection.ofInjectiveEndomap
    (fun steps : Fin count =>
      Bijection.iterateForward
        bijection.reverse steps.val base)
    (Cycle.orbit_injective (Cycle.IsSingleCycle.reverse cycle) base)

/-- The forward orbit-labeling map executes backward iteration from the retained base. -/
@[simp] theorem inverseOrbitLabeling_forward {count : Nat}
    (bijection : Bijection count count)
    (cycle : IsSingleCycle bijection)
    (base position : Fin count) :
    (OrbitLabeling.inverseOrbitLabeling bijection cycle base).forward position =
      Bijection.iterateForward
        bijection.reverse position.val base := rfl

/-- Inverse-orbit coordinates identify a positive-size cycle's forward map with cyclic
predecessor.

Positive count supplies the wraparound index. At position zero use the full-period
return; at each positive position cancel one backward step. -/
theorem forward_inverseOrbitLabeling {count : Nat} (positive : 0 < count)
    (bijection : Bijection count count)
    (cycle : IsSingleCycle bijection)
    (base position : Fin count) :
    bijection.forward
        ((OrbitLabeling.inverseOrbitLabeling bijection cycle base).forward position) =
      (OrbitLabeling.inverseOrbitLabeling bijection cycle base).forward
        (Predecessor.cyclicPredecessor positive position) := by
  by_cases zero : position.val = 0
  · have positionZero : position = ⟨0, positive⟩ := Fin.ext zero
    subst position
    rw [Predecessor.cyclicPredecessor_zero,
      OrbitLabeling.inverseOrbitLabeling_forward, OrbitLabeling.inverseOrbitLabeling_forward]
    have reverseReturns :=
      (Cycle.IsSingleCycle.reverse cycle).return_at_count base
    have successor : count - 1 + 1 = count := Nat.Subtraction.sub_add_cancel positive
    have stepReturns :
        Bijection.iterateForward
            bijection.reverse (count - 1 + 1) base = base :=
      (congrArg
        (fun steps : Nat =>
          Bijection.iterateForward
            bijection.reverse steps base) successor).trans reverseReturns
    rw [Bijection.iterateForward_succ]
      at stepReturns
    change bijection.forward base =
      Bijection.iterateForward
        bijection.reverse (count - 1) base
    apply bijection.reverse.forward_injective
    change bijection.backward (bijection.forward base) =
      bijection.backward
        (Bijection.iterateForward
          bijection.reverse (count - 1) base)
    rw [bijection.backward_forward]
    exact stepReturns.symm
  · rw [Predecessor.cyclicPredecessor_of_ne_zero
      positive position zero,
      OrbitLabeling.inverseOrbitLabeling_forward, OrbitLabeling.inverseOrbitLabeling_forward]
    change bijection.forward
        (Bijection.iterateForward
          bijection.reverse position.val base) =
      Bijection.iterateForward
        bijection.reverse (position.val - 1) base
    have predecessor : position.val - 1 + 1 = position.val :=
      Nat.Subtraction.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)
    have expanded :
        Bijection.iterateForward
            bijection.reverse position.val base =
          bijection.backward
            (Bijection.iterateForward
              bijection.reverse (position.val - 1) base) := by
      calc
        _ = Bijection.iterateForward
              bijection.reverse (position.val - 1 + 1) base :=
          congrArg
            (fun steps : Nat =>
              Bijection.iterateForward
                bijection.reverse steps base) predecessor.symm
        _ = _ := rfl
    rw [expanded]
    rw [bijection.forward_backward]
end Bijection.OrbitLabeling

end Purelib.Data.Fin

end
