import CCL.Progressive.PolynomialRoots

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

namespace CCL.FiniteMonodromy

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev OwnerFamily := CCL.ProgressivePolynomialRoots.OwnerFamily
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable
abbrev SimpleRootChamber :=
  CCL.ProgressivePolynomialRoots.SimpleRootChamber

/-- Change only the displayed polynomial index of a local owner along an
exact coefficientwise equality. -/
def castOwner {left right : GaussianPolynomial}
    (same : left = right) (owner : LocalOwner left) : LocalOwner right := by
  rw [← same]
  exact owner

@[simp] theorem castOwner_box {left right : GaussianPolynomial}
    (same : left = right) (owner : LocalOwner left) :
    (castOwner same owner).box = owner.box := by
  subst right
  rfl

@[simp] theorem castOwner_clearance_bound
    {left right : GaussianPolynomial}
    (same : left = right) (owner : LocalOwner left) :
    (castOwner same owner).clearance.bound = owner.clearance.bound := by
  subst right
  rfl

/-- Change only the displayed polynomial index of an owner family. -/
def castOwnerFamily {left right : GaussianPolynomial} {count : Nat}
    (same : left = right) (family : OwnerFamily left count) :
    OwnerFamily right count := by
  rw [← same]
  exact family

@[simp] theorem castOwnerFamily_owner_box
    {left right : GaussianPolynomial} {count : Nat}
    (same : left = right) (family : OwnerFamily left count)
    (index : Fin count) :
    ((castOwnerFamily same family).owner index).box =
      (family.owner index).box := by
  subst right
  rfl

/-- Simultaneously change the polynomial and the displayed finite index
count of an owner family. -/
def castOwnerFamilyFull
    {left right : GaussianPolynomial} {leftCount rightCount : Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) : OwnerFamily right rightCount := by
  subst right
  subst rightCount
  exact family

@[simp] theorem castOwnerFamilyFull_owner_box
    {left right : GaussianPolynomial} {leftCount rightCount : Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin leftCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner
      (Fin.cast countSame index)).box = (family.owner index).box := by
  subst right
  subst rightCount
  rfl

@[simp] theorem castOwnerFamilyFull_owner_box_target
    {left right : GaussianPolynomial} {leftCount rightCount : Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin rightCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner index).box =
      (family.owner (Fin.cast countSame.symm index)).box := by
  subst right
  subst rightCount
  rfl

@[simp] theorem castOwnerFamilyFull_owner_clearance_bound_target
    {left right : GaussianPolynomial} {leftCount rightCount : Nat}
    (polynomialSame : left = right) (countSame : leftCount = rightCount)
    (family : OwnerFamily left leftCount) (index : Fin rightCount) :
    ((castOwnerFamilyFull polynomialSame countSame family).owner
      index).clearance.bound =
      (family.owner
        (Fin.cast countSame.symm index)).clearance.bound := by
  subst right
  subst rightCount
  rfl

/-- Reindex a finite winding-one state along exact polynomial and ambient-box
equalities.  All numerical data, including the four full ambient-line
clearances, are retained. -/
def castWindingOneState
    {leftPolynomial rightPolynomial : GaussianPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (state : RFAP.ShrinkingTrack.WindingOneState
      leftPolynomial leftAmbient) :
    RFAP.ShrinkingTrack.WindingOneState rightPolynomial rightAmbient := by
  subst rightPolynomial
  subst rightAmbient
  exact state

@[simp] theorem castWindingOneState_box
    {leftPolynomial rightPolynomial : GaussianPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (state : RFAP.ShrinkingTrack.WindingOneState
      leftPolynomial leftAmbient) :
    (castWindingOneState polynomialSame ambientSame state).box = state.box := by
  subst rightPolynomial
  subst rightAmbient
  rfl

/-- Reindex an entire executable shrinking track without changing its finite
refinement program. -/
def castWindingOneTrack
    {leftPolynomial rightPolynomial : GaussianPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (track : RFAP.ShrinkingTrack.WindingOneTrack
      leftPolynomial leftAmbient) :
    RFAP.ShrinkingTrack.WindingOneTrack rightPolynomial rightAmbient := by
  subst rightPolynomial
  subst rightAmbient
  exact track

@[simp] theorem castWindingOneTrack_initial_box
    {leftPolynomial rightPolynomial : GaussianPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (track : RFAP.ShrinkingTrack.WindingOneTrack
      leftPolynomial leftAmbient) :
    (castWindingOneTrack polynomialSame ambientSame track).initial.box =
      track.initial.box := by
  subst rightPolynomial
  subst rightAmbient
  rfl

/-! ## Finite bijections without a global choice principle -/

/-- An explicitly executable bijection between two displayed finite index
types.  Both directions and both inverse laws are data. -/
structure FiniteBijection (sourceCount targetCount : Nat) where
  forward : Fin sourceCount → Fin targetCount
  backward : Fin targetCount → Fin sourceCount
  backward_forward : ∀ source, backward (forward source) = source
  forward_backward : ∀ target, forward (backward target) = target

namespace FiniteBijection

def identity (count : Nat) : FiniteBijection count count where
  forward := fun index => index
  backward := fun index => index
  backward_forward := fun _ => rfl
  forward_backward := fun _ => rfl

/-- Transport indices across an explicitly displayed equality of their
finite counts. -/
def cast {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) :
    FiniteBijection sourceCount targetCount := by
  subst targetCount
  exact identity sourceCount

@[simp] theorem cast_forward {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) (index : Fin sourceCount) :
    (cast equal).forward index = Fin.cast equal index := by
  subst targetCount
  rfl

@[simp] theorem cast_backward {sourceCount targetCount : Nat}
    (equal : sourceCount = targetCount) (index : Fin targetCount) :
    (cast equal).backward index = Fin.cast equal.symm index := by
  subst targetCount
  rfl

/-- Composition is written in path order: first `left`, then `right`. -/
def comp {firstCount middleCount lastCount : Nat}
    (right : FiniteBijection middleCount lastCount)
    (left : FiniteBijection firstCount middleCount) :
    FiniteBijection firstCount lastCount where
  forward := fun index => right.forward (left.forward index)
  backward := fun index => left.backward (right.backward index)
  backward_forward := by
    intro index
    rw [right.backward_forward, left.backward_forward]
  forward_backward := by
    intro index
    rw [left.forward_backward, right.forward_backward]

def reverse {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    FiniteBijection targetCount sourceCount where
  forward := bijection.backward
  backward := bijection.forward
  backward_forward := bijection.forward_backward
  forward_backward := bijection.backward_forward

/-- Pointwise equality is the constructive equality notion needed for finite
permutations.  It avoids asking for extensional equality of function values
that are already compared one displayed index at a time. -/
def Same {sourceCount targetCount : Nat}
    (left right : FiniteBijection sourceCount targetCount) : Prop :=
  ∀ index, left.forward index = right.forward index

theorem same_refl {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    Same bijection bijection := fun _ => rfl

theorem same_symm {sourceCount targetCount : Nat}
    {left right : FiniteBijection sourceCount targetCount}
    (same : Same left right) : Same right left := by
  intro index
  exact (same index).symm

theorem same_trans {sourceCount targetCount : Nat}
    {first second third : FiniteBijection sourceCount targetCount}
    (firstSecond : Same first second) (secondThird : Same second third) :
    Same first third := by
  intro index
  exact (firstSecond index).trans (secondThird index)

theorem comp_identity_left {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    Same (comp (identity targetCount) bijection) bijection :=
  fun _ => rfl

theorem comp_identity_right {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    Same (comp bijection (identity sourceCount)) bijection :=
  fun _ => rfl

theorem comp_assoc
    {firstCount secondCount thirdCount fourthCount : Nat}
    (third : FiniteBijection thirdCount fourthCount)
    (second : FiniteBijection secondCount thirdCount)
    (first : FiniteBijection firstCount secondCount) :
    Same (comp third (comp second first))
      (comp (comp third second) first) :=
  fun _ => rfl

theorem reverse_comp
    {firstCount secondCount thirdCount : Nat}
    (right : FiniteBijection secondCount thirdCount)
    (left : FiniteBijection firstCount secondCount) :
    Same (reverse (comp right left))
      (comp (reverse left) (reverse right)) :=
  fun _ => rfl

theorem reverse_forward {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount)
    (index : Fin targetCount) :
    (reverse bijection).forward index = bijection.backward index := rfl

theorem reverse_reverse {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    Same (reverse (reverse bijection)) bijection :=
  fun _ => rfl

/-! ## Finite cycle arithmetic -/

/-- Repeatedly execute the displayed forward map.  The recursion is on the
finite natural count supplied by the caller. -/
def iterateForward {count : Nat} (bijection : FiniteBijection count count) :
    Nat → Fin count → Fin count
  | 0, index => index
  | steps + 1, index => bijection.forward
      (iterateForward bijection steps index)

@[simp] theorem iterateForward_zero {count : Nat}
    (bijection : FiniteBijection count count) (index : Fin count) :
    iterateForward bijection 0 index = index := rfl

@[simp] theorem iterateForward_succ {count : Nat}
    (bijection : FiniteBijection count count) (steps : Nat)
    (index : Fin count) :
    iterateForward bijection (steps + 1) index =
      bijection.forward (iterateForward bijection steps index) := rfl

theorem forward_injective {sourceCount targetCount : Nat}
    (bijection : FiniteBijection sourceCount targetCount) :
    Function.Injective bijection.forward := by
  intro left right equal
  have inverseEqual := congrArg bijection.backward equal
  simpa only [bijection.backward_forward] using inverseEqual

theorem iterateForward_injective {count : Nat}
    (bijection : FiniteBijection count count) :
    ∀ steps : Nat, Function.Injective (iterateForward bijection steps)
  | 0 => fun _ _ equal => equal
  | steps + 1 => by
      intro left right equal
      apply iterateForward_injective bijection steps
      exact bijection.forward_injective equal

theorem iterateForward_add {count : Nat}
    (bijection : FiniteBijection count count) (first second : Nat)
    (index : Fin count) :
    iterateForward bijection (first + second) index =
      iterateForward bijection second
        (iterateForward bijection first index) := by
  induction second with
  | zero => simp only [Nat.add_zero, iterateForward_zero]
  | succ second inductionHypothesis =>
      rw [Nat.add_succ, iterateForward_succ, iterateForward_succ,
        inductionHypothesis]

/-- Bounded search through every displayed source index for a preimage. -/
def findPreimage? {count : Nat} (map : Fin count → Fin count)
    (target : Fin count) : Option (Fin count) :=
  (List.ofFn fun index : Fin count => index).find? fun source =>
    decide (map source = target)

/-- Every injective endomap of a displayed `Fin count` is constructively
surjective.  The successful branch returns the result of an explicit list
search.  A failed search would inject `count+1` displayed indices into
`count`. -/
theorem fin_surjective_of_injective {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) (target : Fin count) :
    ∃ source : Fin count, map source = target := by
  match found : findPreimage? map target with
  | some source =>
      have checked := List.find?_some found
      change decide (map source = target) = true at checked
      exact ⟨source, of_decide_eq_true checked⟩
  | none =>
    have rejected : ∀ source ∈ List.ofFn (fun index : Fin count => index),
        decide (map source = target) = false := by
      apply QuotientFreeList.find?_eq_none.mp
      simpa only [findPreimage?] using found
    have targetDifferent (source : Fin count) : target ≠ map source := by
      intro equal
      have sourceMember : source ∈
          List.ofFn (fun index : Fin count => index) :=
        List.mem_ofFn.mpr ⟨source, rfl⟩
      have rejectedSource := rejected source sourceMember
      have accepted : decide (map source = target) = true :=
        decide_eq_true equal.symm
      rw [accepted] at rejectedSource
      exact Bool.noConfusion rejectedSource
    let extended : Fin (count + 1) → Fin count :=
      fun index => Fin.cases target (fun source => map source) index
    have extendedInjective : Function.Injective extended := by
      intro left right equal
      cases left using Fin.cases with
      | zero =>
          cases right using Fin.cases with
          | zero => rfl
          | succ rightTail =>
              have impossible : target = map rightTail := by
                simpa only [extended, Fin.cases_zero, Fin.cases_succ]
                  using equal
              exact (targetDifferent rightTail impossible).elim
      | succ leftTail =>
          cases right using Fin.cases with
          | zero =>
              have impossible : map leftTail = target := by
                simpa only [extended, Fin.cases_zero, Fin.cases_succ]
                  using equal
              exact (targetDifferent leftTail impossible.symm).elim
          | succ rightTail =>
              apply congrArg Fin.succ
              apply injective
              simpa only [extended, Fin.cases_succ] using equal
    have impossible :=
      RFAP.FinitePacking.fin_card_le_of_injective_direct
        extended extendedInjective
    exact (Nat.not_succ_le_self count (by simpa only [Nat.add_comm] using
      impossible)).elim

theorem findPreimage?_isSome_of_surjective
    {count : Nat} (map : Fin count → Fin count)
    (surjective : ∀ target, ∃ source, map source = target)
    (target : Fin count) : (findPreimage? map target).isSome := by
  rw [findPreimage?, QuotientFreeList.find?_isSome]
  obtain ⟨source, equal⟩ := surjective target
  exact ⟨source, by simp, decide_eq_true equal⟩

/-- The executable result of finite preimage search, together with the
kernel-checked equation certifying the selected entry. -/
structure SelectedPreimage {count : Nat} (map : Fin count → Fin count)
    (target : Fin count) where
  source : Fin count
  equal : map source = target

def selectPreimage {count : Nat} (map : Fin count → Fin count)
    (surjective : ∀ target, ∃ source, map source = target)
    (target : Fin count) : SelectedPreimage map target := by
  match found : findPreimage? map target with
  | none =>
      have present := findPreimage?_isSome_of_surjective map surjective target
      rw [found] at present
      exact Bool.noConfusion present
  | some source =>
      have checked := List.find?_some found
      change decide (map source = target) = true at checked
      exact ⟨source, of_decide_eq_true checked⟩

/-- An injective endomap of a displayed finite index type becomes a fully
executable bijection.  Its inverse is a bounded list search, not a selected
preimage hidden behind a choice principle. -/
def ofInjectiveEndomap {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) : FiniteBijection count count := by
  let surjective : ∀ target, ∃ source, map source = target :=
    fin_surjective_of_injective map injective
  let selected (target : Fin count) : SelectedPreimage map target :=
    selectPreimage map surjective target
  exact
    { forward := map
      backward := fun target => (selected target).source
      backward_forward := by
        intro source
        apply injective
        exact (selected (map source)).equal
      forward_backward := fun target => (selected target).equal }

@[simp] theorem ofInjectiveEndomap_forward
    {count : Nat} (map : Fin count → Fin count)
    (injective : Function.Injective map) (index : Fin count) :
    (ofInjectiveEndomap map injective).forward index = map index := rfl

/-- Every target index occurs among the first `count` iterates exactly when
those iterates do not repeat. -/
theorem iterateForward_surjective_of_noEarlyReturn
    {count : Nat} (bijection : FiniteBijection count count)
    (noEarlyReturn : ∀ (index : Fin count) (steps : Nat),
      0 < steps → steps < count →
        iterateForward bijection steps index ≠ index)
    (start target : Fin count) :
    ∃ steps : Fin count,
      iterateForward bijection steps.val start = target := by
  let orbit : Fin count → Fin count := fun steps =>
    iterateForward bijection steps.val start
  have orbitInjective : Function.Injective orbit := by
    intro left right equal
    change iterateForward bijection left.val start =
      iterateForward bijection right.val start at equal
    by_cases valuesEqual : left.val = right.val
    · exact Fin.ext valuesEqual
    · by_cases leftBefore : left.val < right.val
      · let difference := right.val - left.val
        have differencePositive : 0 < difference :=
          Nat.sub_pos_of_lt leftBefore
        have differenceSmall : difference < count :=
          (Nat.sub_le right.val left.val).trans_lt right.isLt
        have split : left.val + difference = right.val :=
          Nat.add_sub_of_le leftBefore.le
        have returned :
            iterateForward bijection difference
                (iterateForward bijection left.val start) =
              iterateForward bijection left.val start := by
          calc
            iterateForward bijection difference
                (iterateForward bijection left.val start) =
              iterateForward bijection (left.val + difference) start :=
                (iterateForward_add bijection left.val difference start).symm
            _ = iterateForward bijection right.val start := by rw [split]
            _ = iterateForward bijection left.val start := equal.symm
        exact (noEarlyReturn (orbit left) difference differencePositive
          differenceSmall (by simpa only [orbit] using returned)).elim
      · have rightBefore : right.val < left.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt leftBefore)
            (Ne.symm valuesEqual)
        let difference := left.val - right.val
        have differencePositive : 0 < difference :=
          Nat.sub_pos_of_lt rightBefore
        have differenceSmall : difference < count :=
          (Nat.sub_le left.val right.val).trans_lt left.isLt
        have split : right.val + difference = left.val :=
          Nat.add_sub_of_le rightBefore.le
        have returned :
            iterateForward bijection difference
                (iterateForward bijection right.val start) =
              iterateForward bijection right.val start := by
          calc
            iterateForward bijection difference
                (iterateForward bijection right.val start) =
              iterateForward bijection (right.val + difference) start :=
                (iterateForward_add bijection right.val difference start).symm
            _ = iterateForward bijection left.val start := by rw [split]
            _ = iterateForward bijection right.val start := equal
        exact (noEarlyReturn (orbit right) difference differencePositive
          differenceSmall (by simpa only [orbit] using returned)).elim
  simpa only [orbit] using
    fin_surjective_of_injective orbit orbitInjective target

/-- A displayed finite permutation is one `count`-cycle when every index
returns after exactly `count` steps and no positive smaller count returns. -/
structure IsSingleCycle {count : Nat}
    (bijection : FiniteBijection count count) : Prop where
  return_at_count : ∀ index : Fin count,
    iterateForward bijection count index = index
  no_early_return : ∀ (index : Fin count) (steps : Nat),
    0 < steps → steps < count →
      iterateForward bijection steps index ≠ index

/-- The finite no-early-return calculation already forces the full return
and hence a single cycle; no group order or infinite orbit is used. -/
theorem isSingleCycle_of_noEarlyReturn
    {count : Nat} (bijection : FiniteBijection count count)
    (noEarlyReturn : ∀ (index : Fin count) (steps : Nat),
      0 < steps → steps < count →
        iterateForward bijection steps index ≠ index) :
    IsSingleCycle bijection where
  no_early_return := noEarlyReturn
  return_at_count := by
    intro index
    let predecessor := bijection.backward index
    obtain ⟨steps, reaches⟩ :=
      iterateForward_surjective_of_noEarlyReturn bijection noEarlyReturn
        index predecessor
    have returns : iterateForward bijection (steps.val + 1) index = index := by
      rw [iterateForward_succ, reaches, bijection.forward_backward]
    have notLess : ¬steps.val + 1 < count := by
      intro small
      exact noEarlyReturn index (steps.val + 1) (Nat.zero_lt_succ _)
        small returns
    have equalCount : steps.val + 1 = count :=
      Nat.le_antisymm (Nat.succ_le_of_lt steps.isLt)
        (Nat.le_of_not_gt notLess)
    simpa only [equalCount] using returns

theorem IsSingleCycle.reaches
    {count : Nat} {bijection : FiniteBijection count count}
    (cycle : IsSingleCycle bijection) (start target : Fin count) :
    ∃ steps : Fin count,
      iterateForward bijection steps.val start = target :=
  iterateForward_surjective_of_noEarlyReturn bijection
    cycle.no_early_return start target

end FiniteBijection

/-! ## Rouché-connected rational owner boxes -/

/-- One oriented finite Rouché comparison on one displayed rational box. -/
structure OrientedRouche
    (base target : GaussianPolynomial) (box : Box) where
  perturbation : GaussianPolynomial
  target_eq_add : target = base + perturbation
  dominance : RFAP.WindingHomotopy.BoundaryNormDominance
    base perturbation box

/-- A symmetric record that the two polynomial readings are joined on one
rational box by a finite Rouché calculation.  Equality is the zero-length
piece; the two oriented cases make path reversal data-preserving. -/
inductive RoucheConnection
    (left right : GaussianPolynomial) (box : Box) : Type
  | equal (same : left = right)
  | forward (certificate : OrientedRouche left right box)
  | backward (certificate : OrientedRouche right left box)

namespace RoucheConnection

def reverse {left right : GaussianPolynomial} {box : Box} :
    RoucheConnection left right box → RoucheConnection right left box
  | .equal same => .equal same.symm
  | .forward certificate => .backward certificate
  | .backward certificate => .forward certificate

end RoucheConnection

/-- One rational winding-one owner carried by both endpoint polynomials of a
finite path piece.  The connection field records the finite Rouché reason
that these are two readings of the same local owner. -/
structure OwnerBridge (left right : GaussianPolynomial) where
  box : Box
  proper : box.Proper
  leftClearance : RFAP.BoxClearance.BoundaryClearance left box
  rightClearance : RFAP.BoxClearance.BoundaryClearance right box
  leftWindingFour :
    RFAP.Winding.quadrupledBoxWinding left box = 4
  rightWindingFour :
    RFAP.Winding.quadrupledBoxWinding right box = 4
  connection : RoucheConnection left right box

namespace OwnerBridge

/-- Change only the two displayed polynomial indices of a bridge along
coefficientwise equalities. -/
def cast {left left' right right' : GaussianPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : OwnerBridge left right) : OwnerBridge left' right' := by
  subst left'
  subst right'
  exact bridge

@[simp] theorem cast_box {left left' right right' : GaussianPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : OwnerBridge left right) :
    (bridge.cast leftSame rightSame).box = bridge.box := by
  subst left'
  subst right'
  rfl

@[simp] theorem cast_leftClearance_bound
    {left left' right right' : GaussianPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : OwnerBridge left right) :
    (bridge.cast leftSame rightSame).leftClearance.bound =
      bridge.leftClearance.bound := by
  subst left'
  subst right'
  rfl

@[simp] theorem cast_rightClearance_bound
    {left left' right right' : GaussianPolynomial}
    (leftSame : left = left') (rightSame : right = right')
    (bridge : OwnerBridge left right) :
    (bridge.cast leftSame rightSame).rightClearance.bound =
      bridge.rightClearance.bound := by
  subst left'
  subst right'
  rfl

def reflexive {polynomial : GaussianPolynomial}
    (owner : LocalOwner polynomial) : OwnerBridge polynomial polynomial where
  box := owner.box
  proper := owner.proper
  leftClearance := owner.clearance
  rightClearance := owner.clearance
  leftWindingFour := owner.rawWindingFour
  rightWindingFour := owner.rawWindingFour
  connection := .equal rfl

/-- Construct the target side of a bridge from one dominant endpoint and an
explicit finite boundary comparison. -/
def ofForward {left right : GaussianPolynomial}
    (owner : LocalOwner left)
    (certificate : OrientedRouche left right owner.box) :
    OwnerBridge left right where
  box := owner.box
  proper := owner.proper
  leftClearance := owner.clearance
  rightClearance := by
    rw [certificate.target_eq_add]
    exact
      RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper
          certificate.dominance
  leftWindingFour := owner.rawWindingFour
  rightWindingFour := by
    rw [certificate.target_eq_add]
    exact
      (RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper owner.clearance
          certificate.dominance).trans owner.rawWindingFour
  connection := .forward certificate

/-- The target-side clearance stored by a forward owner bridge is exactly
the finite boundary-dominance clearance used to construct it. -/
@[simp] theorem ofForward_rightClearance_bound
    {left right : GaussianPolynomial}
    (owner : LocalOwner left)
    (certificate : OrientedRouche left right owner.box) :
    (ofForward owner certificate).rightClearance.bound =
      (RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
        left certificate.perturbation owner.box owner.proper
          certificate.dominance).bound := by
  obtain ⟨perturbation, targetEq, dominance⟩ := certificate
  subst right
  rfl

def reverse {left right : GaussianPolynomial}
    (bridge : OwnerBridge left right) : OwnerBridge right left where
  box := bridge.box
  proper := bridge.proper
  leftClearance := bridge.rightClearance
  rightClearance := bridge.leftClearance
  leftWindingFour := bridge.rightWindingFour
  rightWindingFour := bridge.leftWindingFour
  connection := bridge.connection.reverse

def leftOwner {left right : GaussianPolynomial}
    (bridge : OwnerBridge left right) : LocalOwner left where
  box := bridge.box
  proper := bridge.proper
  clearance := bridge.leftClearance
  rawWindingFour := bridge.leftWindingFour

def rightOwner {left right : GaussianPolynomial}
    (bridge : OwnerBridge left right) : LocalOwner right where
  box := bridge.box
  proper := bridge.proper
  clearance := bridge.rightClearance
  rawWindingFour := bridge.rightWindingFour

end OwnerBridge

/-! ## Certified simple-root chamber frames and overlaps -/

/-- One complete degree-indexed simple-root frame.  Keeping the original
chamber certificate here retains its squarefree data and degree-sharp
maximality, rather than treating an arbitrary list of boxes as a root family. -/
structure ChamberFrame where
  reference : CoefficientTable
  chamber : SimpleRootChamber reference

namespace ChamberFrame

abbrev degree (frame : ChamberFrame) : Nat := frame.reference.degree
abbrev Index (frame : ChamberFrame) := Fin frame.degree

def polynomial (frame : ChamberFrame) : GaussianPolynomial :=
  frame.reference.polynomial

def owner (frame : ChamberFrame) (index : frame.Index) :
    LocalOwner frame.polynomial :=
  frame.chamber.owners.owner index

/-- The executable degree-many persistent root family belonging to this
chamber frame. -/
def closure (frame : ChamberFrame) :
    CCL.ProgressivePolynomialRoots.EffectiveAlgebraicClosure frame.chamber :=
  frame.chamber.effectiveAlgebraicClosure

def rootName (frame : ChamberFrame) (index : frame.Index) :
    CCL.ProgressiveTransducer.Named :=
  frame.closure.roots index

theorem rootName_productive (frame : ChamberFrame)
    (index : frame.Index) (count : Nat) :
    (frame.rootName index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (frame.rootName index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (frame.rootName index).machine count).emitted.length = count :=
  frame.closure.roots_productive index count

theorem rootName_exact (frame : ChamberFrame)
    (index : frame.Index) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (frame.closure.continuation.toProcess index)
      frame.closure.continuation.initial
      (CCL.ProgressiveTransducer.advance
        (frame.rootName index).machine count) :=
  frame.closure.roots_exact index count

theorem pairwiseSeparated (frame : ChamberFrame)
    (left right : frame.Index) (different : left ≠ right) :
    (frame.owner left).box.Separated (frame.owner right).box :=
  frame.chamber.owners.pairwiseSeparated left right different

end ChamberFrame

/-- A complete finite overlap between two certified chamber frames.  Every
source owner is represented on a common rational bridge box and matched to
one target owner; the stored inverse proves that no owner is lost or
duplicated.  The bridge itself carries winding four for both endpoint
polynomials and an explicit finite Rouché connection. -/
structure ChamberOverlap (left right : ChamberFrame) where
  matching : FiniteBijection left.degree right.degree
  bridge : left.Index → OwnerBridge left.polynomial right.polynomial
  bridge_refines_left : ∀ index : left.Index,
    (bridge index).box.Refines (left.owner index).box
  bridge_refines_right : ∀ index : left.Index,
    (bridge index).box.Refines
      (right.owner (matching.forward index)).box

namespace ChamberOverlap

def identity (frame : ChamberFrame) : ChamberOverlap frame frame where
  matching := FiniteBijection.identity frame.degree
  bridge := fun index => OwnerBridge.reflexive (frame.owner index)
  bridge_refines_left := fun index =>
    RFAP.Boxes.Box.refines_refl (frame.owner index).box
  bridge_refines_right := fun index =>
    RFAP.Boxes.Box.refines_refl (frame.owner index).box

def reverse {left right : ChamberFrame}
    (overlap : ChamberOverlap left right) : ChamberOverlap right left where
  matching := overlap.matching.reverse
  bridge := fun index =>
    (overlap.bridge (overlap.matching.backward index)).reverse
  bridge_refines_left := by
    intro index
    have refines :=
      overlap.bridge_refines_right (overlap.matching.backward index)
    rw [overlap.matching.forward_backward] at refines
    exact refines
  bridge_refines_right := by
    intro index
    exact overlap.bridge_refines_left (overlap.matching.backward index)

/-- On a self-overlap the geometric owner matching is forced to be the
identity.  A bridge box cannot refine two distinct separated owners because
its displayed anchor belongs to both. -/
theorem forward_eq_self {frame : ChamberFrame}
    (overlap : ChamberOverlap frame frame) (index : frame.Index) :
    overlap.matching.forward index = index := by
  by_cases same : overlap.matching.forward index = index
  · exact same
  · have separated := frame.pairwiseSeparated index
      (overlap.matching.forward index) (fun reverse => same reverse.symm)
    have distinct := separated.points_ne
      ((overlap.bridge_refines_left index).contains
        (overlap.bridge index).box.contains_anchor)
      ((overlap.bridge_refines_right index).contains
        (overlap.bridge index).box.contains_anchor)
    exact (distinct rfl).elim

theorem self_matching_identity {frame : ChamberFrame}
    (overlap : ChamberOverlap frame frame) :
    FiniteBijection.Same overlap.matching
      (FiniteBijection.identity frame.degree) :=
  overlap.forward_eq_self

end ChamberOverlap

/-! ## Finite chamber paths and their monodromy -/

/-- A finite coefficient path is a finite inductive chain of certified
chamber overlaps.  The endpoint indices remain dependent on their displayed
frames, so unequal degrees cannot be joined accidentally. -/
inductive ChamberPath : (start finish : ChamberFrame) → Type 2
  | nil (frame : ChamberFrame) : ChamberPath frame frame
  | cons {start middle finish : ChamberFrame}
      (step : ChamberOverlap start middle)
      (remaining : ChamberPath middle finish) : ChamberPath start finish

namespace ChamberPath

def stepCount : {start finish : ChamberFrame} →
    ChamberPath start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ remaining => remaining.stepCount + 1

def transport : {start finish : ChamberFrame} →
    ChamberPath start finish → FiniteBijection start.degree finish.degree
  | _, _, .nil frame => FiniteBijection.identity frame.degree
  | _, _, .cons step remaining =>
      FiniteBijection.comp remaining.transport step.matching

/-- The finite list of rational Rouché bridge boxes traversed by one initial
owner.  Its index is updated by the certified matching at every step. -/
def bridgeBoxes : {start finish : ChamberFrame} →
    (path : ChamberPath start finish) → start.Index → List Box
  | _, _, .nil _, _ => []
  | _, _, .cons step remaining, index =>
      (step.bridge index).box ::
        remaining.bridgeBoxes (step.matching.forward index)

@[simp] theorem bridgeBoxes_length
    {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : start.Index) :
    (path.bridgeBoxes index).length = path.stepCount := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [bridgeBoxes, List.length_cons, stepCount,
        inductionHypothesis]

def finalIndex {start finish : ChamberFrame}
    (path : ChamberPath start finish) (index : start.Index) : finish.Index :=
  path.transport.forward index

@[simp] theorem finalIndex_nil (frame : ChamberFrame) (index : frame.Index) :
    (ChamberPath.nil frame).finalIndex index = index := rfl

@[simp] theorem finalIndex_cons
    {start middle finish : ChamberFrame}
    (step : ChamberOverlap start middle)
    (remaining : ChamberPath middle finish) (index : start.Index) :
    (ChamberPath.cons step remaining).finalIndex index =
      remaining.finalIndex (step.matching.forward index) := rfl

/-- The arithmetic-ready persistent CCL name at the endpoint selected by
finite owner transport from one starting owner. -/
def finalRootName {start finish : ChamberFrame}
    (path : ChamberPath start finish) (index : start.Index) :
    CCL.ProgressiveTransducer.Named :=
  finish.rootName (path.finalIndex index)

theorem finalRootName_productive
    {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : start.Index) (count : Nat) :
    (path.finalRootName index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (path.finalRootName index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (path.finalRootName index).machine count).emitted.length = count :=
  finish.rootName_productive (path.finalIndex index) count

theorem finalRootName_exact
    {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : start.Index) (count : Nat) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (finish.closure.continuation.toProcess (path.finalIndex index))
      finish.closure.continuation.initial
      (CCL.ProgressiveTransducer.advance
        (path.finalRootName index).machine count) :=
  finish.rootName_exact (path.finalIndex index) count

def append {start middle finish : ChamberFrame}
    (first : ChamberPath start middle)
    (second : ChamberPath middle finish) : ChamberPath start finish :=
  match first with
  | .nil _ => second
  | .cons step remaining => .cons step (remaining.append second)

theorem append_assoc
    {first second third fourth : ChamberFrame}
    (left : ChamberPath first second) (middle : ChamberPath second third)
    (right : ChamberPath third fourth) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | cons step remaining inductionHypothesis =>
      simp only [append, inductionHypothesis]

theorem transport_append
    {start middle finish : ChamberFrame}
    (first : ChamberPath start middle)
    (second : ChamberPath middle finish) (index : start.Index) :
    (first.append second).transport.forward index =
      second.transport.forward (first.transport.forward index) := by
  induction first with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      exact inductionHypothesis second (step.matching.forward index)

theorem finalIndex_append
    {start middle finish : ChamberFrame}
    (first : ChamberPath start middle) (second : ChamberPath middle finish)
    (index : start.Index) :
    (first.append second).finalIndex index =
      second.finalIndex (first.finalIndex index) :=
  transport_append first second index

def reverse : {start finish : ChamberFrame} →
    ChamberPath start finish → ChamberPath finish start
  | _, _, .nil frame => .nil frame
  | _, _, .cons step remaining =>
      remaining.reverse.append (.cons step.reverse (.nil _))

theorem transport_reverse_forward
    {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : finish.Index) :
    path.reverse.transport.forward index = path.transport.backward index := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      change
        (remaining.reverse.append
          (.cons step.reverse (.nil _))).transport.forward index = _
      rw [transport_append]
      change step.matching.backward
          (remaining.reverse.transport.forward index) = _
      rw [inductionHypothesis]
      rfl

theorem transport_reverse
    {start finish : ChamberFrame} (path : ChamberPath start finish) :
    FiniteBijection.Same path.reverse.transport path.transport.reverse :=
  path.transport_reverse_forward

/-- The monodromy of a displayed closed finite chamber path. -/
def monodromy {frame : ChamberFrame} (loop : ChamberPath frame frame) :
    FiniteBijection frame.degree frame.degree :=
  loop.transport

theorem monodromy_append {frame : ChamberFrame}
    (first second : ChamberPath frame frame) (index : frame.Index) :
    (first.append second).monodromy.forward index =
      second.monodromy.forward (first.monodromy.forward index) :=
  first.transport_append second index

theorem monodromy_reverse {frame : ChamberFrame}
    (loop : ChamberPath frame frame) :
    FiniteBijection.Same loop.reverse.monodromy loop.monodromy.reverse :=
  loop.transport_reverse

end ChamberPath

/-! ## Paths retained inside one chamber -/

/-- A path explicitly retained inside one certified chamber.  Each step may
carry a different finite Rouché calculation, but both endpoint owner families
are the same chamber family. -/
inductive LocalPath (frame : ChamberFrame) : Type 2
  | nil : LocalPath frame
  | cons (step : ChamberOverlap frame frame)
      (remaining : LocalPath frame) : LocalPath frame

namespace LocalPath

def toPath {frame : ChamberFrame} : LocalPath frame → ChamberPath frame frame
  | .nil => .nil frame
  | .cons step remaining => .cons step remaining.toPath

def monodromy {frame : ChamberFrame} (path : LocalPath frame) :
    FiniteBijection frame.degree frame.degree :=
  path.toPath.monodromy

/-- A chamber-contained path has identity monodromy, regardless of how many
finite refinements or redundant self-overlap certificates it contains. -/
theorem monodromy_identity {frame : ChamberFrame}
    (path : LocalPath frame) :
    FiniteBijection.Same path.monodromy
      (FiniteBijection.identity frame.degree) := by
  intro index
  induction path generalizing index with
  | nil => rfl
  | cons step remaining inductionHypothesis =>
      change remaining.monodromy.forward (step.matching.forward index) = index
      rw [inductionHypothesis]
      exact step.forward_eq_self index

end LocalPath

end CCL.FiniteMonodromy
