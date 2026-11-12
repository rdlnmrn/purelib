module
public import Purelib.Topology.BranchedCover
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
public import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Replicate

open Purelib

open Purelib.Topology

public section

/-!
# Finite topology of hyperelliptic covers

For `y^2 = f(x)`, a squarefree polynomial of degree `2g+1` has one ramified
point over infinity, while degree `2g+2` has two unramified points there.  The
profiles below display those two cases as finite cycle-count lists and compute
their genus from the finite Riemann--Hurwitz theorem.
-/

namespace Purelib.Curves.Hyperelliptic.Topology.BranchProfile

open Purelib.Topology.BranchedCover
open Purelib.Data.List

/-- Odd degree `2g+1`: all finite roots and infinity have one monodromy cycle. There are therefore `2g+2` displayed
ramified base vertices. -/
@[expose] def oddDegreeProfile (genus : Nat) : BranchProfile where
  sheets := 2
  sheetsAtLeastTwo := le_rfl
  cycles := List.replicate (2 * genus + 2) 1
  cyclesPositive := by
    intro cyclesAtVertex membership
    rw [Membership.eq_of_mem_replicate membership]
    exact Nat.zero_lt_succ 0
  cyclesAtMostSheets := by
    intro cyclesAtVertex membership
    rw [Membership.eq_of_mem_replicate membership]
    exact Nat.le_succ 1

/-- Even degree `2g+2`: the finite roots have one monodromy cycle, and the displayed infinity vertex has two cycles
because it is unramified. -/
@[expose] def evenDegreeProfile (genus : Nat) : BranchProfile where
  sheets := 2
  sheetsAtLeastTwo := le_rfl
  cycles := List.replicate (2 * genus + 2) 1 ++ [2]
  cyclesPositive := by
    intro cyclesAtVertex membership
    have branches := Membership.mem_append.mp membership
    have membership : cyclesAtVertex ∈ List.replicate (2 * genus + 2) 1 ∨ cyclesAtVertex = 2 :=
      branches.elim Or.inl (fun member => Or.inr (Membership.mem_singleton.mp member))
    cases membership with
    | inl finiteMembership =>
        rw [Membership.eq_of_mem_replicate finiteMembership]
        exact Nat.zero_lt_succ 0
    | inr infinityEqual =>
        rw [infinityEqual]
        exact Nat.zero_lt_succ 1
  cyclesAtMostSheets := by
    intro cyclesAtVertex membership
    have branches := Membership.mem_append.mp membership
    have membership : cyclesAtVertex ∈ List.replicate (2 * genus + 2) 1 ∨ cyclesAtVertex = 2 :=
      branches.elim Or.inl (fun member => Or.inr (Membership.mem_singleton.mp member))
    cases membership with
    | inl finiteMembership =>
        rw [Membership.eq_of_mem_replicate finiteMembership]
        exact Nat.le_succ 1
    | inr infinityEqual =>
        rw [infinityEqual]

/-- The odd-degree profile has twice the genus plus two displayed branch vertices. -/
@[simp] theorem oddDegreeProfile_cycleCount (genus : Nat) :
    (oddDegreeProfile genus).cycles.length = 2 * genus + 2 := by
  simp only [oddDegreeProfile, Replicate.length_replicate, -eq_self,
    -iff_self]
  rfl

/-- The even-degree profile includes its unramified infinity vertex, giving twice the genus plus three vertices. -/
@[simp] theorem evenDegreeProfile_cycleCount (genus : Nat) :
    (evenDegreeProfile genus).cycles.length = 2 * genus + 3 := by
  simp only [evenDegreeProfile, Append.length_append,
    Replicate.length_replicate,
    List.length_cons, List.length_nil, -eq_self, -iff_self]
  rfl

/-- The total defect of the odd-degree double-cover profile is twice the genus plus two. -/
@[simp] theorem oddDegreeProfile_totalDefect (genus : Nat) :
    (oddDegreeProfile genus).totalDefect = 2 * genus + 2 := by
  unfold BranchProfile.totalDefect oddDegreeProfile
  simp only [Replicate.map_replicate, Nat.reduceSub, total_replicate, Nat.mul_one, -eq_self, -iff_self]
  rfl

/-- The unramified infinity vertex leaves the even-degree total defect at twice the genus plus two. -/
@[simp] theorem evenDegreeProfile_totalDefect (genus : Nat) :
    (evenDegreeProfile genus).totalDefect = 2 * genus + 2 := by
  unfold BranchProfile.totalDefect evenDegreeProfile
  simp only [Map.map_append, Replicate.map_replicate, List.map_cons, List.map_nil,
    Nat.reduceSub, total_append, total_replicate, total_cons,
      total_nil,
    Nat.mul_one, Nat.add_zero, -eq_self, -iff_self]
  rfl

/-- The arithmetic genus certificate for odd-degree hyperelliptic data. -/
@[expose] def oddDegreeGenusCertificate (genus : Nat) :
    GenusCertificate (oddDegreeProfile genus) where
  enoughDefect := by
    rw [oddDegreeProfile_totalDefect]
    change 2 * 2 <= 2 * genus + 2 + 2
    omega0
  evenNumerator := by
    rw [oddDegreeProfile_totalDefect]
    change (2 * genus + 2 + 2 - 2 * 2) % 2 = 0
    omega0

/-- The arithmetic genus certificate for even-degree hyperelliptic data. -/
@[expose] def evenDegreeGenusCertificate (genus : Nat) :
    GenusCertificate (evenDegreeProfile genus) where
  enoughDefect := by
    rw [evenDegreeProfile_totalDefect]
    change 2 * 2 <= 2 * genus + 2 + 2
    omega0
  evenNumerator := by
    rw [evenDegreeProfile_totalDefect]
    change (2 * genus + 2 + 2 - 2 * 2) % 2 = 0
    omega0

/-- The finite odd-degree branch profile computes the specified genus. -/
theorem oddDegree_computedGenus (genus : Nat) :
    (oddDegreeGenusCertificate genus).genus = genus := by
  unfold GenusCertificate.genus GenusCertificate.numerator
  rw [oddDegreeProfile_totalDefect]
  change (2 * genus + 2 + 2 - 2 * 2) / 2 = genus
  omega0

/-- The finite even-degree branch profile computes the specified genus. -/
theorem evenDegree_computedGenus (genus : Nat) :
    (evenDegreeGenusCertificate genus).genus = genus := by
  unfold GenusCertificate.genus GenusCertificate.numerator
  rw [evenDegreeProfile_totalDefect]
  change (2 * genus + 2 + 2 - 2 * 2) / 2 = genus
  omega0

/-- Concrete finite cell model for a squarefree odd-degree hyperelliptic curve. -/
@[expose] def oddDegreeModel (genus : Nat) : BranchedCellModel :=
  branchedCover (oddDegreeProfile genus)

/-- Concrete finite cell model for a squarefree even-degree hyperelliptic curve. -/
@[expose] def evenDegreeModel (genus : Nat) : BranchedCellModel :=
  branchedCover (evenDegreeProfile genus)

/-- The explicit odd-degree branched cell model has Euler characteristic two minus twice the genus. -/
theorem oddDegree_eulerCharacteristic (genus : Nat) :
    (oddDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus := by
  have genusIdentity :=
    GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      (oddDegreeGenusCertificate genus)
      (spherePolygonCellulation (oddDegreeProfile
        genus).cycles.length)
  rw [oddDegree_computedGenus] at genusIdentity
  simpa only [oddDegreeModel, branchedCover, -eq_self,
    -iff_self] using genusIdentity

/-- The explicit even-degree branched cell model has Euler characteristic two minus twice the genus. -/
theorem evenDegree_eulerCharacteristic (genus : Nat) :
    (evenDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus :=
      by
  have genusIdentity :=
    GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      (evenDegreeGenusCertificate genus)
      (spherePolygonCellulation (evenDegreeProfile
        genus).cycles.length)
  rw [evenDegree_computedGenus] at genusIdentity
  simpa only [evenDegreeModel, branchedCover, -eq_self,
    -iff_self] using genusIdentity

open Purelib.Curves.Hyperelliptic.Topology.BranchProfile in
/-- Both parity cases produce the requested genus from their explicit finite branch-at-infinity data. -/
theorem hyperelliptic_riemannHurwitz (genus : Nat) :
    (oddDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus /\
      (evenDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus :=
  And.intro (oddDegree_eulerCharacteristic genus)
    (evenDegree_eulerCharacteristic genus)

end Purelib.Curves.Hyperelliptic.Topology.BranchProfile

end
