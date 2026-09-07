import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.CumulativeStability

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace FiniteMeasure

namespace Distribution

/-- Greatest member of a displayed rational list which is at most the
supplied cut, when such a member exists. -/
private def greatestAtMost : List Coordinate → Coordinate → Option Coordinate
  | [], _ => none
  | value :: remaining, cut =>
      match greatestAtMost remaining cut with
      | none => if value ≤ cut then some value else none
      | some current =>
          if value ≤ cut then some (max value current) else some current

private theorem greatestAtMost_none_no_member_le :
    ∀ (values : List Coordinate) (cut : Coordinate),
      greatestAtMost values cut = none →
        ∀ value, value ∈ values → ¬value ≤ cut
  | [], cut, empty, value, member => (List.not_mem_nil member).elim
  | head :: remaining, cut, empty, value, member => by
      unfold greatestAtMost at empty
      cases tailResult : greatestAtMost remaining cut with
      | none =>
          by_cases headLe : head ≤ cut
          · simp only [tailResult, headLe, if_pos] at empty
            cases empty
          · simp only [tailResult, headLe] at empty
            rcases List.mem_cons.mp member with equal | tailMember
            · subst value
              exact headLe
            · exact greatestAtMost_none_no_member_le remaining cut
                tailResult value tailMember
      | some current =>
          by_cases headLe : head ≤ cut
          · simp only [tailResult, headLe, if_pos] at empty
            cases empty
          · simp only [tailResult, headLe] at empty
            cases empty

private theorem greatestAtMost_some_spec :
    ∀ (values : List Coordinate) (cut result : Coordinate),
      greatestAtMost values cut = some result →
        result ∈ values ∧ result ≤ cut ∧
          ∀ value, value ∈ values → value ≤ cut → value ≤ result
  | [], cut, result, selected => by cases selected
  | head :: remaining, cut, result, selected => by
      unfold greatestAtMost at selected
      cases tailResult : greatestAtMost remaining cut with
      | none =>
          by_cases headLe : head ≤ cut
          · simp only [tailResult, headLe, if_pos] at selected
            have resultEqual : result = head := Option.some.inj selected.symm
            subst result
            refine ⟨List.mem_cons_self, headLe, ?_⟩
            intro value member valueLe
            rcases List.mem_cons.mp member with equal | tailMember
            · exact equal.le
            · exact (greatestAtMost_none_no_member_le remaining cut
                tailResult value tailMember valueLe).elim
          · simp only [tailResult, headLe] at selected
            cases selected
      | some current =>
          have tailSpec := greatestAtMost_some_spec remaining cut current
            tailResult
          by_cases headLe : head ≤ cut
          · simp only [tailResult, headLe, if_pos] at selected
            have resultEqual : result = max head current :=
              Option.some.inj selected.symm
            subst result
            refine ⟨?_, max_le headLe tailSpec.2.1, ?_⟩
            · rcases le_total head current with headLeCurrent | currentLeHead
              · rw [max_eq_right headLeCurrent]
                exact List.mem_cons_of_mem head tailSpec.1
              · rw [max_eq_left currentLeHead]
                exact List.mem_cons_self
            · intro value member valueLe
              rcases List.mem_cons.mp member with equal | tailMember
              · subst value
                exact le_max_left _ _
              · exact (tailSpec.2.2 value tailMember valueLe).trans
                  (le_max_right _ _)
          · simp only [tailResult, headLe] at selected
            have resultEqual : result = current := Option.some.inj selected.symm
            subst result
            refine ⟨List.mem_cons_of_mem head tailSpec.1, tailSpec.2.1, ?_⟩
            intro value member valueLe
            rcases List.mem_cons.mp member with equal | tailMember
            · subst value
              exact (headLe valueLe).elim
            · exact tailSpec.2.2 value tailMember valueLe

/-- Displayed rational payload grid of one finite law.  Repeated payloads are
retained because they do not affect a maximum over the grid. -/
def atomPayloadGrid (distribution : Distribution Coordinate) :
    List Coordinate :=
  distribution.atoms.map fun atom => atom.item

theorem atom_item_mem_atomPayloadGrid
    (distribution : Distribution Coordinate)
    (atom : Weighted Coordinate) (member : atom ∈ distribution.atoms) :
    atom.item ∈ distribution.atomPayloadGrid :=
  QuotientFreeList.mem_map.mpr ⟨atom, member, rfl⟩

/-- Finite union of the two displayed rational payload tables.  Duplicates
are harmless because the grid distance uses maximum. -/
def cumulativeSupportGrid (left right : Distribution Coordinate) :
    List Coordinate :=
  left.atomPayloadGrid ++ right.atomPayloadGrid

private theorem left_item_mem_cumulativeSupportGrid
    (left right : Distribution Coordinate)
    (atom : Weighted Coordinate) (member : atom ∈ left.atoms) :
    atom.item ∈ cumulativeSupportGrid left right :=
  List.mem_append.mpr (Or.inl
    (left.atom_item_mem_atomPayloadGrid atom member))

private theorem right_item_mem_cumulativeSupportGrid
    (left right : Distribution Coordinate)
    (atom : Weighted Coordinate) (member : atom ∈ right.atoms) :
    atom.item ∈ cumulativeSupportGrid left right :=
  List.mem_append.mpr (Or.inr
    (right.atom_item_mem_atomPayloadGrid atom member))

/-- Displayed values strictly below one rational cut. -/
private def valuesStrictlyBelow
    (values : List Coordinate) (cut : Coordinate) : List Coordinate :=
  values.filter fun value => decide (value < cut)

private theorem mem_valuesStrictlyBelow_iff
    (values : List Coordinate) (cut value : Coordinate) :
    value ∈ valuesStrictlyBelow values cut ↔
      value ∈ values ∧ value < cut := by
  unfold valuesStrictlyBelow
  simp only [List.mem_filter, decide_eq_true_eq]

/-- Executable rational lower cut isolating one queried payload from all
strictly smaller displayed atoms. -/
structure CumulativeJumpCertificate
    (distribution : Distribution Coordinate) (item : Coordinate) where
  lower : Coordinate
  lower_lt : lower < item
  isolates : ∀ atom, atom ∈ distribution.atoms →
    atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item

/-- Compute a singleton-jump certificate by searching the finite displayed
support for its greatest member strictly below the queried payload.  If none
exists, `item - 1` is a certified lower cut. -/
def cumulativeJumpCertificate
    (distribution : Distribution Coordinate) (item : Coordinate) :
    CumulativeJumpCertificate distribution item := by
  let values := distribution.atomPayloadGrid
  let below := valuesStrictlyBelow values item
  cases selected : greatestAtMost below item with
  | none =>
      refine
        { lower := item - 1
          lower_lt := ?_
          isolates := ?_ }
      · simpa only [sub_zero] using
          (RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (a := 0) (b := 1) (by decide) item)
      · intro atom member
        have atomInValues : atom.item ∈ values :=
          distribution.atom_item_mem_atomPayloadGrid atom member
        have notBelow : ¬atom.item < item := by
          intro atomBelow
          have belowMember : atom.item ∈ below :=
            (mem_valuesStrictlyBelow_iff values item atom.item).2
              ⟨atomInValues, atomBelow⟩
          exact greatestAtMost_none_no_member_le below item selected atom.item
            belowMember atomBelow.le
        rcases lt_trichotomy item atom.item with above | equal | belowItem
        · exact Or.inr (Or.inr above)
        · exact Or.inr (Or.inl equal.symm)
        · exact (notBelow belowItem).elim
  | some result =>
      have spec := greatestAtMost_some_spec below item result selected
      have resultBelow : result < item :=
        (mem_valuesStrictlyBelow_iff values item result).1 spec.1 |>.2
      refine
        { lower := result
          lower_lt := resultBelow
          isolates := ?_ }
      intro atom member
      rcases lt_trichotomy atom.item item with atomBelow | equal | above
      · apply Or.inl
        apply spec.2.2 atom.item
        · exact (mem_valuesStrictlyBelow_iff values item atom.item).2
            ⟨distribution.atom_item_mem_atomPayloadGrid atom member,
              atomBelow⟩
        · exact atomBelow.le
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr above)

/-- Every singleton mass is the exact jump of the finite CDF across its
computed isolating lower cut.  Repeated rows at the queried payload are all
included. -/
theorem atomMass_eq_cumulative_sub_jumpCertificate
    (distribution : Distribution Coordinate) (item : Coordinate) :
    distribution.atomMass item =
      distribution.cumulative item -
        distribution.cumulative
          (distribution.cumulativeJumpCertificate item).lower := by
  unfold atomMass
  exact distribution.probability_eqValue_eq_cumulative_sub_of_atom_gap
    (distribution.cumulativeJumpCertificate item).lower_lt
    (distribution.cumulativeJumpCertificate item).isolates

private theorem cumulative_eq_at_greatestAtMost
    (distribution : Distribution Coordinate)
    (values : List Coordinate) (cut result : Coordinate)
    (selected : greatestAtMost values cut = some result)
    (covers : ∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) :
    distribution.cumulative cut = distribution.cumulative result := by
  let spec := greatestAtMost_some_spec values cut result selected
  unfold cumulative
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold atMostEvent
  by_cases atomLeCut : atom.item ≤ cut
  · have atomLeResult := spec.2.2 atom.item (covers atom member) atomLeCut
    simp only [atomLeCut, atomLeResult, decide_true]
  · have notLeResult : ¬atom.item ≤ result := by
      intro atomLeResult
      exact atomLeCut (atomLeResult.trans spec.2.1)
    simp only [atomLeCut, notLeResult, decide_false]

private theorem cumulative_eq_zero_of_greatestAtMost_none
    (distribution : Distribution Coordinate)
    (values : List Coordinate) (cut : Coordinate)
    (empty : greatestAtMost values cut = none)
    (covers : ∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) :
    distribution.cumulative cut = 0 := by
  unfold cumulative
  calc
    distribution.probability (atMostEvent cut) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      have notLe := greatestAtMost_none_no_member_le values cut empty atom.item
        (covers atom member)
      unfold atMostEvent
      simp only [notLe, decide_false]
    _ = 0 := distribution.probability_false

/-- If one displayed threshold grid covers both finite atom tables, its
computed maximum controls the CDF discrepancy at every rational cut. -/
theorem cumulative_separation_le_cumulativeGridDistance_of_support_covered
    (left right : Distribution Coordinate) (thresholds : List Coordinate)
    (leftCovered : ∀ atom, atom ∈ left.atoms → atom.item ∈ thresholds)
    (rightCovered : ∀ atom, atom ∈ right.atoms → atom.item ∈ thresholds)
    (cut : Coordinate) :
    rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.cumulativeGridDistance right thresholds := by
  cases selected : greatestAtMost thresholds cut with
  | none =>
      have leftZero := cumulative_eq_zero_of_greatestAtMost_none left
        thresholds cut selected leftCovered
      have rightZero := cumulative_eq_zero_of_greatestAtMost_none right
        thresholds cut selected rightCovered
      rw [leftZero, rightZero]
      exact (rationalSeparation_eq_zero_iff 0 0).mpr rfl |>.le.trans
        (left.cumulativeGridDistance_nonnegative right thresholds)
  | some result =>
      have spec := greatestAtMost_some_spec thresholds cut result selected
      have leftEqual := cumulative_eq_at_greatestAtMost left thresholds cut
        result selected leftCovered
      have rightEqual := cumulative_eq_at_greatestAtMost right thresholds cut
        result selected rightCovered
      rw [leftEqual, rightEqual]
      exact left.cumulative_separation_le_cumulativeGridDistance right result
        spec.1

/-- Every rational-cut CDF discrepancy is bounded by the exact maximum on
the finite union of the two displayed support tables. -/
theorem cumulative_separation_le_cumulativeSupportGridDistance
    (left right : Distribution Coordinate) (cut : Coordinate) :
    rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.cumulativeGridDistance right
        (cumulativeSupportGrid left right) := by
  exact left.cumulative_separation_le_cumulativeGridDistance_of_support_covered
    right (cumulativeSupportGrid left right)
      (left_item_mem_cumulativeSupportGrid left right)
      (right_item_mem_cumulativeSupportGrid left right) cut

/-- Exact finite Kolmogorov distance: maximum CDF discrepancy over the union
of the two displayed support tables. -/
def finiteKolmogorovDistance (left right : Distribution Coordinate) :
    Coordinate :=
  left.cumulativeGridDistance right (cumulativeSupportGrid left right)

/-- Any displayed threshold grid covering both atom tables computes the same
global upper bound as its pointwise maximum. -/
theorem finiteKolmogorovDistance_le_cumulativeGridDistance_of_support_covered
    (left right : Distribution Coordinate) (thresholds : List Coordinate)
    (leftCovered : ∀ atom, atom ∈ left.atoms → atom.item ∈ thresholds)
    (rightCovered : ∀ atom, atom ∈ right.atoms → atom.item ∈ thresholds) :
    left.finiteKolmogorovDistance right ≤
      left.cumulativeGridDistance right thresholds := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right)
    (left.cumulativeGridDistance right thresholds)
    (left.cumulativeGridDistance_nonnegative right thresholds)
  intro cut member
  exact left.cumulative_separation_le_cumulativeGridDistance_of_support_covered
    right thresholds leftCovered rightCovered cut

theorem finiteKolmogorovDistance_nonnegative
    (left right : Distribution Coordinate) :
    0 ≤ left.finiteKolmogorovDistance right :=
  left.cumulativeGridDistance_nonnegative right
    (cumulativeSupportGrid left right)

@[simp] theorem finiteKolmogorovDistance_refl
    (distribution : Distribution Coordinate) :
    distribution.finiteKolmogorovDistance distribution = 0 :=
  distribution.cumulativeGridDistance_refl
    (cumulativeSupportGrid distribution distribution)

/-- The exact finite Kolmogorov distance controls the CDF discrepancy at
every supplied rational cut. -/
theorem cumulative_separation_le_finiteKolmogorovDistance
    (left right : Distribution Coordinate) (cut : Coordinate) :
    rationalSeparation (left.cumulative cut) (right.cumulative cut) ≤
      left.finiteKolmogorovDistance right :=
  left.cumulative_separation_le_cumulativeSupportGridDistance right cut

/-- Least-upper-bound property over every rational cut.  Although the
statement quantifies over rational cuts, the proof computes only the maximum
on the finite union of the two displayed support tables. -/
theorem finiteKolmogorovDistance_le
    (left right : Distribution Coordinate) (bound : Coordinate)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ cut, rationalSeparation
      (left.cumulative cut) (right.cumulative cut) ≤ bound) :
    left.finiteKolmogorovDistance right ≤ bound := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right) bound boundNonnegative
  intro cut member
  exact pointwise cut

/-- A nonnegative rational is a global upper bound for the exact finite
Kolmogorov distance exactly when it bounds the CDF discrepancy at every
rational cut. -/
theorem finiteKolmogorovDistance_le_iff
    (left right : Distribution Coordinate) (bound : Coordinate)
    (boundNonnegative : 0 ≤ bound) :
    left.finiteKolmogorovDistance right ≤ bound ↔
      ∀ cut, rationalSeparation
        (left.cumulative cut) (right.cumulative cut) ≤ bound := by
  constructor
  · intro distanceLe cut
    exact (left.cumulative_separation_le_finiteKolmogorovDistance right cut)
      |>.trans distanceLe
  · exact fun pointwise => left.finiteKolmogorovDistance_le right bound
      boundNonnegative pointwise

/-- A strict bound on the executable finite maximum is equivalent to the
same strict CDF bound at every rational cut. -/
theorem finiteKolmogorovDistance_lt_iff
    (left right : Distribution Coordinate) (tolerance : Coordinate)
    (tolerancePositive : 0 < tolerance) :
    left.finiteKolmogorovDistance right < tolerance ↔
      ∀ cut, rationalSeparation
        (left.cumulative cut) (right.cumulative cut) < tolerance := by
  constructor
  · intro distanceSmall cut
    exact (left.cumulative_separation_le_finiteKolmogorovDistance right cut)
      |>.trans_lt distanceSmall
  · intro pointwise
    apply (left.cumulativeGridDistance_lt_iff right
      (cumulativeSupportGrid left right) tolerance tolerancePositive).2
    intro cut member
    exact pointwise cut

/-- Exact finite Kolmogorov distance is symmetric even though the two
concatenated support-grid layouts occur in opposite orders. -/
theorem finiteKolmogorovDistance_symm
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right =
      right.finiteKolmogorovDistance left := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply left.cumulativeGridDistance_le right
      (cumulativeSupportGrid left right)
      (right.finiteKolmogorovDistance left)
      (right.finiteKolmogorovDistance_nonnegative left)
    intro cut member
    rw [rationalSeparation_symm]
    exact right.cumulative_separation_le_finiteKolmogorovDistance left cut
  · apply right.cumulativeGridDistance_le left
      (cumulativeSupportGrid right left)
      (left.finiteKolmogorovDistance right)
      (left.finiteKolmogorovDistance_nonnegative right)
    intro cut member
    rw [rationalSeparation_symm]
    exact left.cumulative_separation_le_finiteKolmogorovDistance right cut

/-- Triangle inequality for the global finite support-grid distance. -/
theorem finiteKolmogorovDistance_triangle
    (left middle right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right ≤
      left.finiteKolmogorovDistance middle +
        middle.finiteKolmogorovDistance right := by
  apply left.cumulativeGridDistance_le right
    (cumulativeSupportGrid left right)
  · exact add_nonneg
      (left.finiteKolmogorovDistance_nonnegative middle)
      (middle.finiteKolmogorovDistance_nonnegative right)
  · intro cut member
    exact (rationalSeparation_triangle
      (left.cumulative cut) (middle.cumulative cut)
      (right.cumulative cut)).trans
        (add_le_add
          (left.cumulative_separation_le_finiteKolmogorovDistance middle cut)
          (middle.cumulative_separation_le_finiteKolmogorovDistance right cut))

/-- Adding the same independent finite rational noise on the left cannot
increase exact finite Kolmogorov distance.  The proof is a finite average of
shifted pointwise CDF discrepancies. -/
theorem finiteKolmogorovDistance_convolve_left_le
    (noise left right : Distribution Coordinate) :
    (noise.convolve left).finiteKolmogorovDistance
        (noise.convolve right) ≤
      left.finiteKolmogorovDistance right := by
  apply (noise.convolve left).finiteKolmogorovDistance_le
    (noise.convolve right) (left.finiteKolmogorovDistance right)
      (left.finiteKolmogorovDistance_nonnegative right)
  intro cut
  rw [noise.cumulative_convolve left cut,
    noise.cumulative_convolve right cut]
  calc
    rationalSeparation
        (noise.expectation fun noiseValue =>
          left.cumulative (cut - noiseValue))
        (noise.expectation fun noiseValue =>
          right.cumulative (cut - noiseValue)) ≤
      noise.l1Distance
        (fun noiseValue => left.cumulative (cut - noiseValue))
        (fun noiseValue => right.cumulative (cut - noiseValue)) :=
      noise.expectation_separation_le_l1Distance _ _
    _ ≤ left.finiteKolmogorovDistance right := by
      unfold l1Distance
      calc
        noise.expectation (fun noiseValue => rationalSeparation
            (left.cumulative (cut - noiseValue))
            (right.cumulative (cut - noiseValue))) ≤
          noise.expectation (fun _ => left.finiteKolmogorovDistance right) := by
            apply noise.expectation_mono
            intro atom member
            exact left.cumulative_separation_le_finiteKolmogorovDistance right
              (cut - atom.item)
        _ = left.finiteKolmogorovDistance right :=
          noise.expectation_constant _

/-- Exact finite Kolmogorov distance is convex under a common rational
mixture weight. -/
theorem finiteKolmogorovDistance_mixture_le
    (leftFirst leftSecond rightFirst rightSecond :
      Distribution Coordinate)
    (weight : MixingWeight) :
    (leftFirst.mixture rightFirst weight).finiteKolmogorovDistance
        (leftSecond.mixture rightSecond weight) ≤
      weight.coefficient *
          leftFirst.finiteKolmogorovDistance leftSecond +
        weight.complement *
          rightFirst.finiteKolmogorovDistance rightSecond := by
  apply (leftFirst.mixture rightFirst weight).finiteKolmogorovDistance_le
    (leftSecond.mixture rightSecond weight)
  · exact add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct weight.nonnegative
        (leftFirst.finiteKolmogorovDistance_nonnegative leftSecond))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        weight.complement_nonnegative
        (rightFirst.finiteKolmogorovDistance_nonnegative rightSecond))
  · intro cut
    rw [leftFirst.cumulative_mixture rightFirst weight,
      leftSecond.cumulative_mixture rightSecond weight]
    calc
      rationalSeparation
          (weight.coefficient * leftFirst.cumulative cut +
            weight.complement * rightFirst.cumulative cut)
          (weight.coefficient * leftSecond.cumulative cut +
            weight.complement * rightSecond.cumulative cut) ≤
        rationalSeparation
            (weight.coefficient * leftFirst.cumulative cut)
            (weight.coefficient * leftSecond.cumulative cut) +
          rationalSeparation
            (weight.complement * rightFirst.cumulative cut)
            (weight.complement * rightSecond.cumulative cut) :=
        rationalSeparation_add_le _ _ _ _
      _ = weight.coefficient * rationalSeparation
            (leftFirst.cumulative cut) (leftSecond.cumulative cut) +
          weight.complement * rationalSeparation
            (rightFirst.cumulative cut) (rightSecond.cumulative cut) := by
        rw [rationalSeparation_scale, rationalSeparation_scale,
          rationalSeparation_zero_of_nonneg weight.nonnegative,
          rationalSeparation_zero_of_nonneg weight.complement_nonnegative]
      _ ≤ weight.coefficient *
            leftFirst.finiteKolmogorovDistance leftSecond +
          weight.complement *
            rightFirst.finiteKolmogorovDistance rightSecond :=
        add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (leftFirst.cumulative_separation_le_finiteKolmogorovDistance
              leftSecond cut) weight.nonnegative)
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (rightFirst.cumulative_separation_le_finiteKolmogorovDistance
              rightSecond cut) weight.complement_nonnegative)

/-- Translating both finite rational laws by the same rational shift leaves
their exact finite Kolmogorov distance unchanged. -/
theorem finiteKolmogorovDistance_map_add_eq
    (left right : Distribution Coordinate) (shift : Coordinate) :
    (left.map fun value => value + shift).finiteKolmogorovDistance
        (right.map fun value => value + shift) =
      left.finiteKolmogorovDistance right := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply (left.map fun value => value + shift).finiteKolmogorovDistance_le
      (right.map fun value => value + shift)
      (left.finiteKolmogorovDistance right)
      (left.finiteKolmogorovDistance_nonnegative right)
    intro cut
    rw [left.cumulative_map_add shift cut,
      right.cumulative_map_add shift cut]
    exact left.cumulative_separation_le_finiteKolmogorovDistance right
      (cut - shift)
  · apply left.finiteKolmogorovDistance_le right
      ((left.map fun value => value + shift).finiteKolmogorovDistance
        (right.map fun value => value + shift))
      ((left.map fun value => value + shift)
        |>.finiteKolmogorovDistance_nonnegative
          (right.map fun value => value + shift))
    intro cut
    have shiftedBound :=
      (left.map fun value => value + shift)
        |>.cumulative_separation_le_finiteKolmogorovDistance
          (right.map fun value => value + shift) (cut + shift)
    rw [left.cumulative_map_add shift (cut + shift),
      right.cumulative_map_add shift (cut + shift)] at shiftedBound
    simpa only [add_sub_cancel_right] using shiftedBound

/-- Multiplying both finite rational laws by the same positive rational
factor leaves their exact finite Kolmogorov distance unchanged. -/
theorem finiteKolmogorovDistance_map_mul_pos_eq
    (left right : Distribution Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor) :
    (left.map fun value => factor * value).finiteKolmogorovDistance
        (right.map fun value => factor * value) =
      left.finiteKolmogorovDistance right := by
  have factorNonzero : factor ≠ 0 := factorPositive.ne'
  have cancel : ∀ cut : Coordinate, (cut * factor) / factor = cut := by
    intro cut
    calc
      (cut * factor) / factor =
          (factor * cut) / (factor * 1) := by
        apply congrArg₂ (fun numerator denominator : Coordinate =>
          numerator / denominator)
        · exact RFAP.ConstructiveFraction.mul_comm cut factor
        · exact (RFAP.ConstructiveFraction.mul_one_direct factor).symm
      _ = cut / 1 :=
        RFAP.ConstructiveFraction.mul_div_mul_left_direct
          factor cut 1 factorNonzero
      _ = cut := by
        have cancelled :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne cut 1 (by decide)
        rw [RFAP.ConstructiveFraction.mul_one_direct] at cancelled
        exact cancelled
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply (left.map fun value => factor * value).finiteKolmogorovDistance_le
      (right.map fun value => factor * value)
      (left.finiteKolmogorovDistance right)
      (left.finiteKolmogorovDistance_nonnegative right)
    intro cut
    rw [left.cumulative_map_mul_pos factor cut factorPositive,
      right.cumulative_map_mul_pos factor cut factorPositive]
    exact left.cumulative_separation_le_finiteKolmogorovDistance right
      (cut / factor)
  · apply left.finiteKolmogorovDistance_le right
      ((left.map fun value => factor * value).finiteKolmogorovDistance
        (right.map fun value => factor * value))
      ((left.map fun value => factor * value)
        |>.finiteKolmogorovDistance_nonnegative
          (right.map fun value => factor * value))
    intro cut
    have scaledBound :=
      (left.map fun value => factor * value)
        |>.cumulative_separation_le_finiteKolmogorovDistance
          (right.map fun value => factor * value) (cut * factor)
    rw [left.cumulative_map_mul_pos factor (cut * factor) factorPositive,
      right.cumulative_map_mul_pos factor (cut * factor) factorPositive,
      cancel cut] at scaledBound
    exact scaledBound

/-- Zero exact finite Kolmogorov distance is equivalent to equality of the
two finite CDFs at every rational cut. -/
theorem finiteKolmogorovDistance_eq_zero_iff
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right = 0 ↔
      ∀ cut, left.cumulative cut = right.cumulative cut := by
  constructor
  · intro distanceZero cut
    apply (rationalSeparation_eq_zero_iff _ _).mp
    apply RFAP.ConstructiveFraction.le_antisymm
    · rw [← distanceZero]
      exact left.cumulative_separation_le_finiteKolmogorovDistance right cut
    · exact rationalSeparation_nonneg _ _
  · intro equal
    apply RFAP.ConstructiveFraction.le_antisymm
    · apply left.cumulativeGridDistance_le right
        (cumulativeSupportGrid left right) 0 le_rfl
      intro cut member
      exact ((rationalSeparation_eq_zero_iff _ _).mpr (equal cut)).le
    · exact left.finiteKolmogorovDistance_nonnegative right

private theorem atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
    (left right : Distribution Coordinate)
    (item lower : Coordinate) (lowerLt : lower < item)
    (leftGap : ∀ atom, atom ∈ left.atoms →
      atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item)
    (rightGap : ∀ atom, atom ∈ right.atoms →
      atom.item ≤ lower ∨ atom.item = item ∨ item < atom.item) :
    rationalSeparation (left.atomMass item) (right.atomMass item) ≤
      2 * left.finiteKolmogorovDistance right := by
  unfold atomMass atomEvent
  rw [left.probability_eqValue_eq_cumulative_sub_of_atom_gap lowerLt leftGap,
    right.probability_eqValue_eq_cumulative_sub_of_atom_gap lowerLt rightGap]
  calc
    rationalSeparation
        (left.cumulative item - left.cumulative lower)
        (right.cumulative item - right.cumulative lower) ≤
      rationalSeparation (left.cumulative item) (right.cumulative item) +
        rationalSeparation (left.cumulative lower) (right.cumulative lower) :=
      rationalSeparation_sub_le _ _ _ _
    _ ≤ left.finiteKolmogorovDistance right +
        left.finiteKolmogorovDistance right :=
      add_le_add
        (left.cumulative_separation_le_finiteKolmogorovDistance right item)
        (left.cumulative_separation_le_finiteKolmogorovDistance right lower)
    _ = 2 * left.finiteKolmogorovDistance right := by ring1

/-- At every rational payload, singleton-mass discrepancy is at most twice
the exact finite Kolmogorov distance.  The proof computes a common greatest
displayed predecessor in the finite union support and compares the two CDF
jumps across that shared gap. -/
theorem atomMass_separation_le_two_mul_finiteKolmogorovDistance
    (left right : Distribution Coordinate) (item : Coordinate) :
    rationalSeparation (left.atomMass item) (right.atomMass item) ≤
      2 * left.finiteKolmogorovDistance right := by
  let values := cumulativeSupportGrid left right
  let below := valuesStrictlyBelow values item
  cases selected : greatestAtMost below item with
  | none =>
      have noValueBelow : ∀ value, value ∈ values → ¬value < item := by
        intro value member valueLt
        have belowMember : value ∈ below :=
          (mem_valuesStrictlyBelow_iff values item value).2
            ⟨member, valueLt⟩
        exact greatestAtMost_none_no_member_le below item selected value
          belowMember valueLt.le
      have lowerLt : item - 1 < item := by
        simpa only [sub_zero] using
          (RFAP.ConstructiveFraction.sub_lt_sub_left_direct
            (a := 0) (b := 1) (by decide) item)
      have gap : ∀ (distribution : Distribution Coordinate),
          (∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) →
          ∀ atom, atom ∈ distribution.atoms →
            atom.item ≤ item - 1 ∨ atom.item = item ∨ item < atom.item := by
        intro distribution covers atom member
        have notBelow := noValueBelow atom.item (covers atom member)
        rcases lt_trichotomy item atom.item with above | equal | belowItem
        · exact Or.inr (Or.inr above)
        · exact Or.inr (Or.inl equal.symm)
        · exact (notBelow belowItem).elim
      exact
        atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
          left right item (item - 1) lowerLt
          (gap left (left_item_mem_cumulativeSupportGrid left right))
          (gap right (right_item_mem_cumulativeSupportGrid left right))
  | some result =>
      have spec := greatestAtMost_some_spec below item result selected
      have resultBelow : result < item :=
        (mem_valuesStrictlyBelow_iff values item result).1 spec.1 |>.2
      have greatestBelow : ∀ value, value ∈ values → value < item →
          value ≤ result := by
        intro value member valueLt
        exact spec.2.2 value
          ((mem_valuesStrictlyBelow_iff values item value).2
            ⟨member, valueLt⟩)
          valueLt.le
      have gap : ∀ (distribution : Distribution Coordinate),
          (∀ atom, atom ∈ distribution.atoms → atom.item ∈ values) →
          ∀ atom, atom ∈ distribution.atoms →
            atom.item ≤ result ∨ atom.item = item ∨ item < atom.item := by
        intro distribution covers atom member
        rcases lt_trichotomy atom.item item with belowItem | equal | above
        · exact Or.inl (greatestBelow atom.item (covers atom member)
            belowItem)
        · exact Or.inr (Or.inl equal)
        · exact Or.inr (Or.inr above)
      exact
        atomMass_separation_le_two_mul_finiteKolmogorovDistance_of_gap
          left right item result resultBelow
          (gap left (left_item_mem_cumulativeSupportGrid left right))
          (gap right (right_item_mem_cumulativeSupportGrid left right))

/-- Number of distinct displayed payloads in the consolidated union support
of two finite laws. -/
def comparisonSupportCardinality
    (left right : Distribution Coordinate) : Nat :=
  (left.toFiniteContent.radonNikodymKeys right.toFiniteContent).length

/-- Consolidation never produces more comparison-support entries than the
two displayed atom tables contain altogether. -/
theorem comparisonSupportCardinality_le
    (left right : Distribution Coordinate) :
    left.comparisonSupportCardinality right ≤
      left.atoms.length + right.atoms.length := by
  unfold comparisonSupportCardinality FiniteContent.radonNikodymKeys
    Distribution.toFiniteContent
  simpa only [List.length_append] using
    (consolidateAtoms_length_le (left.atoms ++ right.atoms))

/-- A finite probability law has nonempty consolidated comparison support.
The proof uses preservation of the explicitly displayed total weight. -/
theorem comparisonSupportCardinality_pos
    (left right : Distribution Coordinate) :
    0 < left.comparisonSupportCardinality right := by
  unfold comparisonSupportCardinality FiniteContent.radonNikodymKeys
    Distribution.toFiniteContent
  apply List.length_pos_iff.mpr
  intro empty
  have consolidatedTotalZero :
      totalWeight (consolidateAtoms (left.atoms ++ right.atoms)) = 0 := by
    rw [empty]
    rfl
  have consolidatedTotalTwo :
      totalWeight (consolidateAtoms (left.atoms ++ right.atoms)) = 2 := by
    rw [totalWeight_consolidateAtoms, totalWeight_append,
      left.total_one, right.total_one]
    decide
  have zeroEqualsTwo : (0 : Coordinate) = 2 :=
    consolidatedTotalZero.symm.trans consolidatedTotalTwo
  exact (by decide : (0 : Coordinate) ≠ 2) zeroEqualsTwo

private theorem variationTotalWeight_le_length_mul_of_bounded
    (atoms : List (SignedWeighted Coordinate)) (ceiling : Coordinate)
    (bounded : ∀ atom, atom ∈ atoms →
      rationalSeparation atom.weight 0 ≤ ceiling) :
    totalWeight (atoms.map SignedContent.variationAtom) ≤
      (atoms.length : Coordinate) * ceiling := by
  induction atoms with
  | nil =>
      simp only [List.map_nil, totalWeight_nil, List.length_nil,
        Nat.cast_zero, zero_mul]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          rationalSeparation candidate.weight 0 ≤ ceiling := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem atom member)
      simp only [List.map_cons, totalWeight_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        rationalSeparation atom.weight 0 +
            totalWeight (remaining.map SignedContent.variationAtom) ≤
          ceiling + (remaining.length : Coordinate) * ceiling :=
        add_le_add (bounded atom List.mem_cons_self)
          (inductionHypothesis tailBounded)
        _ = ((remaining.length : Coordinate) + 1) * ceiling := by ring1

/-- Atomic L1 discrepancy is bounded by twice the exact finite Kolmogorov
distance for each distinct payload in the consolidated union support. -/
theorem atomMassL1Distance_le_two_mul_supportCardinality_mul_finiteKolmogorovDistance
    (left right : Distribution Coordinate) :
    left.atomMassL1Distance right ≤
      (left.comparisonSupportCardinality right : Coordinate) *
        (2 * left.finiteKolmogorovDistance right) := by
  have lengthEqual : (left.signedDifference right).atoms.length =
      left.comparisonSupportCardinality right := by
    unfold Distribution.signedDifference FiniteContent.signedDifference
      comparisonSupportCardinality
    simp only [List.length_map]
  unfold atomMassL1Distance SignedContent.variationContent FiniteContent.total
  rw [← lengthEqual]
  change totalWeight ((left.signedDifference right).atoms.map
      SignedContent.variationAtom) ≤
    ((left.signedDifference right).atoms.length : Coordinate) *
      (2 * left.finiteKolmogorovDistance right)
  apply variationTotalWeight_le_length_mul_of_bounded
  intro atom member
  unfold Distribution.signedDifference FiniteContent.signedDifference at member
  rcases QuotientFreeList.mem_map.mp member with ⟨key, keyMember, equal⟩
  subst atom
  change rationalSeparation
      (left.atomMass key.item - right.atomMass key.item) 0 ≤
    2 * left.finiteKolmogorovDistance right
  rw [← rationalSeparation_eq_sub_zero]
  exact left.atomMass_separation_le_two_mul_finiteKolmogorovDistance
    right key.item

/-- On a finite rational support, total variation is bounded by support size
times exact finite Kolmogorov distance.  This quantitative reverse comparison
is obtained by finite summation over the consolidated union support. -/
theorem totalVariationDistance_le_supportCardinality_mul_finiteKolmogorovDistance
    (left right : Distribution Coordinate) :
    left.totalVariationDistance right ≤
      (left.comparisonSupportCardinality right : Coordinate) *
        left.finiteKolmogorovDistance right := by
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      left.totalVariationDistance right * 2 =
          2 * left.totalVariationDistance right := by ring1
      _ = left.atomMassL1Distance right :=
        (left.atomMassL1Distance_eq_two_mul_totalVariationDistance right).symm
      _ ≤ (left.comparisonSupportCardinality right : Coordinate) *
          (2 * left.finiteKolmogorovDistance right) :=
        left.atomMassL1Distance_le_two_mul_supportCardinality_mul_finiteKolmogorovDistance
          right
      _ = ((left.comparisonSupportCardinality right : Coordinate) *
          left.finiteKolmogorovDistance right) * 2 := by ring1
  · decide

private theorem atomMass_eq_of_cumulative_eq
    (left right : Distribution Coordinate)
    (cumulativeEqual : ∀ cut,
      left.cumulative cut = right.cumulative cut)
    (item : Coordinate) :
    left.probability (atomEvent item) =
      right.probability (atomEvent item) := by
  have distanceZero : left.finiteKolmogorovDistance right = 0 :=
    (left.finiteKolmogorovDistance_eq_zero_iff right).2 cumulativeEqual
  apply (rationalSeparation_eq_zero_iff _ _).mp
  apply RFAP.ConstructiveFraction.le_antisymm
  · calc
      rationalSeparation (left.probability (atomEvent item))
          (right.probability (atomEvent item)) =
        rationalSeparation (left.atomMass item) (right.atomMass item) := rfl
      _ ≤ 2 * left.finiteKolmogorovDistance right :=
        left.atomMass_separation_le_two_mul_finiteKolmogorovDistance right item
      _ = 0 := by rw [distanceZero]; ring1
  · exact rationalSeparation_nonneg _ _

/-- Equality of all finite rational CDF evaluations determines every event
probability and rational expectation of the two finite laws. -/
theorem evaluationEquivalent_of_cumulative_eq
    (left right : Distribution Coordinate)
    (cumulativeEqual : ∀ cut,
      left.cumulative cut = right.cumulative cut) :
    EvaluationEquivalent left right := by
  have contentEquivalent : FiniteContent.EvaluationEquivalent
      left.toFiniteContent right.toFiniteContent :=
    FiniteContent.EvaluationEquivalent.of_atom_measure_eq fun item =>
      atomMass_eq_of_cumulative_eq left right cumulativeEqual item
  exact
    { probability_eq := contentEquivalent.measure_eq
      expectation_eq := contentEquivalent.integral_eq }

/-- Finite rational laws are observationally equivalent exactly when their
CDFs agree at every rational cut. -/
theorem evaluationEquivalent_iff_cumulative_eq
    (left right : Distribution Coordinate) :
    EvaluationEquivalent left right ↔
      ∀ cut, left.cumulative cut = right.cumulative cut := by
  constructor
  · intro equivalent cut
    exact equivalent.probability_eq (atMostEvent cut)
  · exact left.evaluationEquivalent_of_cumulative_eq right

/-- The exact finite Kolmogorov distance vanishes precisely on
observationally equivalent finite rational laws. -/
theorem finiteKolmogorovDistance_eq_zero_iff_evaluationEquivalent
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right = 0 ↔
      EvaluationEquivalent left right := by
  rw [left.finiteKolmogorovDistance_eq_zero_iff right,
    ← left.evaluationEquivalent_iff_cumulative_eq right]

/-- On finite rational laws, exact finite Kolmogorov distance and total
variation vanish on precisely the same observational equivalence class. -/
theorem finiteKolmogorovDistance_eq_zero_iff_totalVariationDistance_eq_zero
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right = 0 ↔
      left.totalVariationDistance right = 0 := by
  rw [left.finiteKolmogorovDistance_eq_zero_iff_evaluationEquivalent right,
    left.totalVariationDistance_eq_zero_iff_evaluationEquivalent right]

/-- Exact finite Kolmogorov distance depends only on the observational laws,
not on atom ordering, duplication, or zero-weight bookkeeping rows. -/
theorem EvaluationEquivalent.finiteKolmogorovDistance_eq
    {leftFirst leftSecond rightFirst rightSecond : Distribution Coordinate}
    (leftEquivalent : EvaluationEquivalent leftFirst leftSecond)
    (rightEquivalent : EvaluationEquivalent rightFirst rightSecond) :
    leftFirst.finiteKolmogorovDistance rightFirst =
      leftSecond.finiteKolmogorovDistance rightSecond := by
  have leftCumulative : ∀ cut,
      leftFirst.cumulative cut = leftSecond.cumulative cut := fun cut =>
    leftEquivalent.probability_eq (atMostEvent cut)
  have rightCumulative : ∀ cut,
      rightFirst.cumulative cut = rightSecond.cumulative cut := fun cut =>
    rightEquivalent.probability_eq (atMostEvent cut)
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply leftFirst.finiteKolmogorovDistance_le rightFirst
      (leftSecond.finiteKolmogorovDistance rightSecond)
      (leftSecond.finiteKolmogorovDistance_nonnegative rightSecond)
    intro cut
    rw [leftCumulative cut, rightCumulative cut]
    exact leftSecond.cumulative_separation_le_finiteKolmogorovDistance
      rightSecond cut
  · apply leftSecond.finiteKolmogorovDistance_le rightSecond
      (leftFirst.finiteKolmogorovDistance rightFirst)
      (leftFirst.finiteKolmogorovDistance_nonnegative rightFirst)
    intro cut
    rw [← leftCumulative cut, ← rightCumulative cut]
    exact leftFirst.cumulative_separation_le_finiteKolmogorovDistance
      rightFirst cut

/-- Equivalently, adding the same independent finite rational noise on the
right cannot increase exact finite Kolmogorov distance. -/
theorem finiteKolmogorovDistance_convolve_right_le
    (left right noise : Distribution Coordinate) :
    (left.convolve noise).finiteKolmogorovDistance
        (right.convolve noise) ≤
      left.finiteKolmogorovDistance right := by
  calc
    (left.convolve noise).finiteKolmogorovDistance
          (right.convolve noise) =
        (noise.convolve left).finiteKolmogorovDistance
          (noise.convolve right) :=
      (left.convolve_comm_evaluationEquivalent noise)
        |>.finiteKolmogorovDistance_eq
          (right.convolve_comm_evaluationEquivalent noise)
    _ ≤ left.finiteKolmogorovDistance right :=
      noise.finiteKolmogorovDistance_convolve_left_le left right

/-- Total variation bounds the exact finite Kolmogorov distance. -/
theorem finiteKolmogorovDistance_le_totalVariationDistance
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right ≤
      left.totalVariationDistance right :=
  left.cumulativeGridDistance_le_totalVariationDistance right
    (cumulativeSupportGrid left right)

/-- Exact finite Kolmogorov distance between probability laws lies in the
rational unit interval. -/
theorem finiteKolmogorovDistance_le_one
    (left right : Distribution Coordinate) :
    left.finiteKolmogorovDistance right ≤ 1 :=
  (left.finiteKolmogorovDistance_le_totalVariationDistance right).trans
    (left.totalVariationDistance_le_one right)

end Distribution

end FiniteMeasure
