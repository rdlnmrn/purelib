import mathlib.Data.ConstructiveList

/-!
# Finite multivalued relations with persistent ownership

The fibre displayed here is finite and local.  Refinement maps one old label
to a finite family of new labels, so clusters may split or merge without being
misrepresented as permutations.  A permutation is recovered only from an
explicit collision-free loop certificate.

No declaration claims that a displayed fibre enumerates an unbounded or
completed mathematical fibre.
-/

namespace CCL.FiniteMultivaluedRelation

universe u v w x y

/-- A finite displayed relation fibre.  `Witness` certifies each local
candidate.  Every distinct pair is either visibly separated or belongs to one
explicit unresolved cluster. -/
structure Fibre
    (Output : Type u)
    (Separated : Output → Output → Type v)
    (Witness : Output → Type w) : Type (max u v w) where
  count : Nat
  candidate : Fin count → Output
  certified : ∀ label, Witness (candidate label)
  clusterCount : Nat
  cluster : Fin clusterCount → List (Fin count)
  pairResolution : ∀ left right, left ≠ right →
    Sum (Separated (candidate left) (candidate right))
      { clusterIndex : Fin clusterCount //
          left ∈ cluster clusterIndex ∧ right ∈ cluster clusterIndex }

namespace Fibre

/-- A completely separated fibre has no unresolved clusters. -/
def ofPairwiseSeparated
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (count : Nat) (candidate : Fin count → Output)
    (certified : ∀ label, Witness (candidate label))
    (pairwise : ∀ left right, left ≠ right →
      Separated (candidate left) (candidate right)) :
    Fibre Output Separated Witness where
  count := count
  candidate := candidate
  certified := certified
  clusterCount := 0
  cluster := Fin.elim0
  pairResolution := fun left right different =>
    Sum.inl (pairwise left right different)

end Fibre

/-- One finite refinement between displayed fibres.  The continuation family
may contain zero, one, or several new labels.  `covers` stores an explicit old
owner for every new label, and `persists` certifies each displayed edge. -/
structure Refinement
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    (old : Fibre Output Separated OldWitness)
    (new : Fibre Output Separated NewWitness)
    (Continues : Output → Output → Prop) : Type (max u v w x) where
  continues : Fin old.count → List (Fin new.count)
  covers : ∀ newLabel,
    { oldLabel : Fin old.count // newLabel ∈ continues oldLabel }
  persists : ∀ oldLabel newLabel, newLabel ∈ continues oldLabel →
    Continues (old.candidate oldLabel) (new.candidate newLabel)

namespace Refinement

/-- Flat-map distributes over append by direct recursion on the displayed
left list. -/
private theorem flatMap_append_direct
    {Alpha : Type u} {Beta : Type v}
    (function : Alpha → List Beta) : ∀ left right : List Alpha,
    (left ++ right).flatMap function =
      left.flatMap function ++ right.flatMap function
  | [], _ => rfl
  | head :: tail, right => by
      change function head ++ (tail ++ right).flatMap function =
        (function head ++ tail.flatMap function) ++ right.flatMap function
      rw [flatMap_append_direct function tail right, List.append_assoc]

/-- Associativity of displayed finite flat-maps without function
extensionality. -/
private theorem flatMap_assoc_direct
    {Alpha : Type u} {Beta : Type v} {Gamma : Type w}
    (first : Alpha → List Beta) (second : Beta → List Gamma) :
    ∀ values : List Alpha,
      (values.flatMap first).flatMap second =
        values.flatMap (fun value => (first value).flatMap second)
  | [] => rfl
  | head :: tail => by
      change (first head ++ tail.flatMap first).flatMap second =
        (first head).flatMap second ++
          tail.flatMap (fun value => (first value).flatMap second)
      rw [flatMap_append_direct second, flatMap_assoc_direct first second tail]

/-- Pointwise equal finite families have equal flat-maps, proved by recursion
on the displayed source list. -/
private theorem flatMap_congr_direct
    {Alpha : Type u} {Beta : Type v}
    (first second : Alpha → List Beta) : ∀ values : List Alpha,
    (∀ value, value ∈ values → first value = second value) →
      values.flatMap first = values.flatMap second
  | [], _ => rfl
  | head :: tail, equal => by
      change first head ++ tail.flatMap first =
        second head ++ tail.flatMap second
      rw [equal head List.mem_cons_self,
        flatMap_congr_direct first second tail (fun value member =>
          equal value (List.mem_cons_of_mem head member))]

/-- A singleton continuation induced by explicit inverse label maps.  Keeping
the casts here prevents concrete adapters from repeatedly unfolding large
fibre definitions merely to establish equal label cardinalities. -/
def ofLabelEquivalence
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (forward : Fin old.count → Fin new.count)
    (backward : Fin new.count → Fin old.count)
    (rightInverse : ∀ label, forward (backward label) = label)
    (persists : ∀ label,
      Continues (old.candidate label) (new.candidate (forward label))) :
    Refinement old new Continues where
  continues label := [forward label]
  covers label :=
    ⟨backward label, by rw [rightInverse]; exact List.mem_cons_self⟩
  persists := by
    intro oldLabel newLabel member
    have equal : newLabel = forward oldLabel := List.mem_singleton.mp member
    subst newLabel
    exact persists oldLabel

@[simp] theorem ofLabelEquivalence_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (forward : Fin old.count → Fin new.count)
    (backward : Fin new.count → Fin old.count)
    (rightInverse : ∀ label, forward (backward label) = label)
    (persists : ∀ label,
      Continues (old.candidate label) (new.candidate (forward label)))
    (label : Fin old.count) :
    (ofLabelEquivalence forward backward rightInverse
      persists).continues label = [forward label] := rfl

/-- Identity continuation displays exactly the same label once. -/
def identity
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {Continues : Output → Output → Prop}
    (fibre : Fibre Output Separated Witness)
    (continuesRefl : ∀ output, Continues output output) :
    Refinement fibre fibre Continues where
  continues label := [label]
  covers label := ⟨label, by simp⟩
  persists := by
    intro oldLabel newLabel member
    have equal : newLabel = oldLabel := List.mem_singleton.mp member
    subst newLabel
    exact continuesRefl (fibre.candidate oldLabel)

@[simp] theorem identity_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {Continues : Output → Output → Prop}
    (fibre : Fibre Output Separated Witness)
    (continuesRefl : ∀ output, Continues output output)
    (label : Fin fibre.count) :
    (identity fibre continuesRefl).continues label = [label] := rfl

/-- Compose owner-to-family maps by finite list flattening. -/
def compose
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {MiddleWitness : Output → Type x}
    {LastWitness : Output → Type y}
    {firstFibre : Fibre Output Separated FirstWitness}
    {middleFibre : Fibre Output Separated MiddleWitness}
    {lastFibre : Fibre Output Separated LastWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre middleFibre Continues)
    (second : Refinement middleFibre lastFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right) :
    Refinement firstFibre lastFibre Continues where
  continues oldLabel :=
    (first.continues oldLabel).flatMap second.continues
  covers newLabel := by
    let middleOwner := second.covers newLabel
    let oldOwner := first.covers middleOwner.val
    exact ⟨oldOwner.val, QuotientFreeList.mem_flatMap.mpr
      ⟨middleOwner.val, oldOwner.property, middleOwner.property⟩⟩
  persists := by
    intro oldLabel newLabel member
    rcases QuotientFreeList.mem_flatMap.mp member with
      ⟨middleLabel, middleMember, newMember⟩
    exact continuesTrans
      (first.persists oldLabel middleLabel middleMember)
      (second.persists middleLabel newLabel newMember)

@[simp] theorem compose_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {MiddleWitness : Output → Type x}
    {LastWitness : Output → Type y}
    {firstFibre : Fibre Output Separated FirstWitness}
    {middleFibre : Fibre Output Separated MiddleWitness}
    {lastFibre : Fibre Output Separated LastWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre middleFibre Continues)
    (second : Refinement middleFibre lastFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose first second continuesTrans).continues label =
      (first.continues label).flatMap second.continues := rfl

/-- Left identity of finite continuation families. -/
theorem identity_compose_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement firstFibre secondFibre Continues)
    (continuesRefl : ∀ output, Continues output output)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose (identity firstFibre continuesRefl) refinement
      continuesTrans).continues label = refinement.continues label := by
  simp only [compose_continues, identity_continues, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- Right identity of finite continuation families. -/
theorem compose_identity_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement firstFibre secondFibre Continues)
    (continuesRefl : ∀ output, Continues output output)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose refinement (identity secondFibre continuesRefl)
      continuesTrans).continues label = refinement.continues label := by
  simp only [compose_continues]
  induction refinement.continues label with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, identity_continues,
        List.singleton_append, inductionHypothesis]

/-- Subdividing a finite path does not change its endpoint owner family:
composition is associative at the executable continuation-list level. -/
theorem compose_assoc_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {ThirdWitness : Output → Type y}
    {FourthWitness : Output → Type}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {thirdFibre : Fibre Output Separated ThirdWitness}
    {fourthFibre : Fibre Output Separated FourthWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre secondFibre Continues)
    (second : Refinement secondFibre thirdFibre Continues)
    (third : Refinement thirdFibre fourthFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose (compose first second continuesTrans) third
        continuesTrans).continues label =
      (compose first (compose second third continuesTrans)
        continuesTrans).continues label := by
  rw [compose_continues, compose_continues,
    flatMap_assoc_direct second.continues third.continues]
  apply flatMap_congr_direct _ _ (first.continues label)
  intro middleLabel _member
  exact compose_continues second third continuesTrans middleLabel

/-- Every displayed new label has concrete finite provenance. -/
def ownerOf
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement old new Continues)
    (newLabel : Fin new.count) : Fin old.count :=
  (refinement.covers newLabel).val

theorem ownerOf_contains
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement old new Continues)
    (newLabel : Fin new.count) :
    newLabel ∈ refinement.continues (refinement.ownerOf newLabel) :=
  (refinement.covers newLabel).property

end Refinement

/-- Selection by a persistent label is allowed only when that candidate is
separated from every other displayed candidate. -/
structure Isolation
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (fibre : Fibre Output Separated Witness)
    (label : Fin fibre.count) : Type (max u v w) where
  separated : ∀ other, other ≠ label →
    Separated (fibre.candidate label) (fibre.candidate other)

structure Selected
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    (fibre : Fibre Output Separated Witness) : Type (max u v w) where
  label : Fin fibre.count
  isolation : Isolation fibre label

namespace Selected

def output
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {fibre : Fibre Output Separated Witness}
    (selected : Selected fibre) : Output :=
  fibre.candidate selected.label

def witness
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {fibre : Fibre Output Separated Witness}
    (selected : Selected fibre) : Witness selected.output :=
  fibre.certified selected.label

end Selected

/-- Local branch selection may instead be justified by explicit alignment to
one already owned reference. -/
structure AlignedSelection
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w} {Reference : Type x}
    (Aligned : Output → Reference → Type y)
    (fibre : Fibre Output Separated Witness) : Type (max u v w x y) where
  label : Fin fibre.count
  reference : Reference
  aligned : Aligned (fibre.candidate label) reference

/-- A collision-free loop is the additional finite data which upgrades a
general owner-to-family refinement to a permutation. -/
structure FinitePermutation (count : Nat) where
  forward : Fin count → Fin count
  backward : Fin count → Fin count
  leftInverse : ∀ label, backward (forward label) = label
  rightInverse : ∀ label, forward (backward label) = label

structure CollisionFreeLoop
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement fibre fibre Continues) : Type (max u v w) where
  forward : Fin fibre.count → Fin fibre.count
  backward : Fin fibre.count → Fin fibre.count
  leftInverse : ∀ label, backward (forward label) = label
  rightInverse : ∀ label, forward (backward label) = label
  continues_eq : ∀ label, refinement.continues label = [forward label]

namespace CollisionFreeLoop

theorem forward_mem
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    {refinement : Refinement fibre fibre Continues}
    (loop : CollisionFreeLoop refinement) (label : Fin fibre.count) :
    loop.forward label ∈ refinement.continues label := by
  rw [loop.continues_eq]
  simp

/-- Endpoint owner transport of a certified loop is a genuine finite
permutation, represented constructively by its two inverse maps. -/
def permutation
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {fibre : Fibre Output Separated Witness}
    {Continues : Output → Output → Prop}
    {refinement : Refinement fibre fibre Continues}
    (loop : CollisionFreeLoop refinement) :
    FinitePermutation fibre.count where
  forward := loop.forward
  backward := loop.backward
  leftInverse := loop.leftInverse
  rightInverse := loop.rightInverse

end CollisionFreeLoop

end CCL.FiniteMultivaluedRelation
