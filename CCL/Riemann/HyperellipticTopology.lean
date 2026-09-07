import CCL.Riemann.BranchedCover

/-!
# Finite topology of hyperelliptic covers

For `y^2 = f(x)`, a squarefree polynomial of degree `2g+1` has one ramified
point over infinity, while degree `2g+2` has two unramified points there.  The
profiles below display those two cases as finite cycle-count lists and compute
their genus from the finite Riemann--Hurwitz theorem.
-/

namespace CCL.Riemann.Hyperelliptic

/-- Odd degree `2g+1`: all finite roots and infinity have one monodromy cycle.
There are therefore `2g+2` displayed ramified base vertices. -/
def oddDegreeProfile (genus : Nat) : BranchProfile where
  sheets := 2
  sheetsAtLeastTwo := le_rfl
  cycles := List.replicate (2 * genus + 2) 1
  cyclesPositive := by
    intro cyclesAtVertex membership
    rw [List.eq_of_mem_replicate membership]
    exact Nat.zero_lt_succ 0
  cyclesAtMostSheets := by
    intro cyclesAtVertex membership
    rw [List.eq_of_mem_replicate membership]
    exact Nat.le_succ 1

/-- Even degree `2g+2`: the finite roots have one monodromy cycle, and the
displayed infinity vertex has two cycles because it is unramified. -/
def evenDegreeProfile (genus : Nat) : BranchProfile where
  sheets := 2
  sheetsAtLeastTwo := le_rfl
  cycles := List.replicate (2 * genus + 2) 1 ++ [2]
  cyclesPositive := by
    intro cyclesAtVertex membership
    rw [List.mem_append, List.mem_singleton] at membership
    cases membership with
    | inl finiteMembership =>
        rw [List.eq_of_mem_replicate finiteMembership]
        exact Nat.zero_lt_succ 0
    | inr infinityEqual =>
        rw [infinityEqual]
        exact Nat.zero_lt_succ 1
  cyclesAtMostSheets := by
    intro cyclesAtVertex membership
    rw [List.mem_append, List.mem_singleton] at membership
    cases membership with
    | inl finiteMembership =>
        rw [List.eq_of_mem_replicate finiteMembership]
        exact Nat.le_succ 1
    | inr infinityEqual =>
        rw [infinityEqual]

@[simp] theorem oddDegreeProfile_cycleCount (genus : Nat) :
    (oddDegreeProfile genus).cycles.length = 2 * genus + 2 := by
  simp only [oddDegreeProfile, List.length_replicate]

@[simp] theorem evenDegreeProfile_cycleCount (genus : Nat) :
    (evenDegreeProfile genus).cycles.length = 2 * genus + 3 := by
  simp only [evenDegreeProfile, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]

@[simp] theorem oddDegreeProfile_totalDefect (genus : Nat) :
    (oddDegreeProfile genus).totalDefect = 2 * genus + 2 := by
  unfold BranchProfile.totalDefect oddDegreeProfile
  simp only [List.map_replicate, Nat.reduceSub, total_replicate, Nat.mul_one]

@[simp] theorem evenDegreeProfile_totalDefect (genus : Nat) :
    (evenDegreeProfile genus).totalDefect = 2 * genus + 2 := by
  unfold BranchProfile.totalDefect evenDegreeProfile
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    Nat.reduceSub, total_append, total_replicate, total_cons, total_nil,
    Nat.mul_one, Nat.add_zero]

/-- The arithmetic genus certificate for odd-degree hyperelliptic data. -/
def oddDegreeGenusCertificate (genus : Nat) :
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
def evenDegreeGenusCertificate (genus : Nat) :
    GenusCertificate (evenDegreeProfile genus) where
  enoughDefect := by
    rw [evenDegreeProfile_totalDefect]
    change 2 * 2 <= 2 * genus + 2 + 2
    omega0
  evenNumerator := by
    rw [evenDegreeProfile_totalDefect]
    change (2 * genus + 2 + 2 - 2 * 2) % 2 = 0
    omega0

theorem oddDegree_computedGenus (genus : Nat) :
    (oddDegreeGenusCertificate genus).genus = genus := by
  unfold GenusCertificate.genus GenusCertificate.numerator
  rw [oddDegreeProfile_totalDefect]
  change (2 * genus + 2 + 2 - 2 * 2) / 2 = genus
  omega0

theorem evenDegree_computedGenus (genus : Nat) :
    (evenDegreeGenusCertificate genus).genus = genus := by
  unfold GenusCertificate.genus GenusCertificate.numerator
  rw [evenDegreeProfile_totalDefect]
  change (2 * genus + 2 + 2 - 2 * 2) / 2 = genus
  omega0

/-- Concrete finite cell model for a squarefree odd-degree hyperelliptic
curve. -/
def oddDegreeModel (genus : Nat) : BranchedCellModel :=
  finiteBranchedCover (oddDegreeProfile genus)

/-- Concrete finite cell model for a squarefree even-degree hyperelliptic
curve. -/
def evenDegreeModel (genus : Nat) : BranchedCellModel :=
  finiteBranchedCover (evenDegreeProfile genus)

theorem oddDegree_eulerCharacteristic (genus : Nat) :
    (oddDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus := by
  have genusIdentity :=
    GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      (oddDegreeGenusCertificate genus)
      (spherePolygonCellulation (oddDegreeProfile genus).cycles.length)
  rw [oddDegree_computedGenus] at genusIdentity
  simpa only [oddDegreeModel, finiteBranchedCover] using genusIdentity

theorem evenDegree_eulerCharacteristic (genus : Nat) :
    (evenDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus := by
  have genusIdentity :=
    GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      (evenDegreeGenusCertificate genus)
      (spherePolygonCellulation (evenDegreeProfile genus).cycles.length)
  rw [evenDegree_computedGenus] at genusIdentity
  simpa only [evenDegreeModel, finiteBranchedCover] using genusIdentity

/-- Both parity cases produce the requested genus from their explicit finite
branch-at-infinity data. -/
theorem finite_hyperelliptic_riemannHurwitz (genus : Nat) :
    (oddDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus /\
      (evenDegreeModel genus).eulerCharacteristic = (2 : Int) - 2 * genus :=
  And.intro (oddDegree_eulerCharacteristic genus)
    (evenDegree_eulerCharacteristic genus)

end CCL.Riemann.Hyperelliptic
