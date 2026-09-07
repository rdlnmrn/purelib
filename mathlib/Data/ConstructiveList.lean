import Init.Data.List.Find
import Init.Data.List.Nat.Range
import Init.Data.List.Attach
import Init.Data.List.Nat.Pairwise
import Init.Data.List.OfFn

/-!
# Constructive finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

namespace QuotientFreeList

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Pointwise equal functions have equal maps over a displayed finite list. -/
theorem map_congr_left {function other : Alpha → Beta} :
    ∀ {values : List Alpha},
      (∀ value ∈ values, function value = other value) →
        values.map function = values.map other
  | [], _ => rfl
  | value :: values, equal => by
      rw [List.map_cons, List.map_cons,
        equal value List.mem_cons_self,
        map_congr_left (fun item member =>
          equal item (List.mem_cons_of_mem value member))]

/-- Membership in a finite map is witnessed by a displayed source member. -/
theorem mem_map {function : Alpha → Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.map function ↔
        ∃ source, source ∈ values ∧ function source = target
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      constructor
      · intro member
        rcases List.mem_cons.mp member with head | tail
        · exact ⟨value, List.mem_cons_self, head.symm⟩
        · rcases (mem_map (values := values)).mp tail with
            ⟨source, sourceMember, equal⟩
          exact ⟨source, List.mem_cons_of_mem value sourceMember, equal⟩
      · rintro ⟨source, sourceMember, equal⟩
        rcases List.mem_cons.mp sourceMember with head | tail
        · subst source
          exact List.mem_cons.mpr (Or.inl equal.symm)
        · exact List.mem_cons.mpr (Or.inr
            ((mem_map (values := values)).mpr
              ⟨source, tail, equal⟩))

theorem mem_map_of_mem {f : Alpha → Beta} {source : Alpha}
    {values : List Alpha} (member : source ∈ values) :
    f source ∈ values.map f :=
  mem_map.mpr ⟨source, member, rfl⟩

/-- Left folds over concatenation recurse through the displayed left list. -/
theorem foldl_append (function : Beta → Alpha → Beta) :
    ∀ (left right : List Alpha) (initial : Beta),
      (left ++ right).foldl function initial =
        right.foldl function (left.foldl function initial)
  | [], _, _ => rfl
  | value :: values, right, initial =>
      foldl_append function values right (function initial value)

/-- Pointwise-equal accumulator steps give the same result on a displayed
finite left fold, without identifying the two step functions. -/
theorem foldl_congr (left right : Beta → Alpha → Beta)
    (pointwise : ∀ accumulator value,
      left accumulator value = right accumulator value) :
    ∀ (values : List Alpha) (initial : Beta),
      values.foldl left initial = values.foldl right initial
  | [], _ => rfl
  | value :: values, initial => by
      change values.foldl left (left initial value) =
        values.foldl right (right initial value)
      rw [pointwise initial value]
      exact foldl_congr left right pointwise values (right initial value)

/-- Right folds over concatenation recurse through the displayed left list. -/
theorem foldr_append (function : Alpha → Beta → Beta) :
    ∀ (left right : List Alpha) (initial : Beta),
      (left ++ right).foldr function initial =
        left.foldr function (right.foldr function initial)
  | [], _, _ => rfl
  | value :: values, right, initial => by
      change function value ((values ++ right).foldr function initial) =
        function value (values.foldr function (right.foldr function initial))
      rw [foldr_append function values right initial]

/-- Membership in a finite flat-map carries both displayed memberships. -/
theorem mem_flatMap {function : Alpha → List Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.flatMap function ↔
        ∃ source, source ∈ values ∧ target ∈ function source
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      change target ∈ function value ++ values.flatMap function ↔ _
      constructor
      · intro member
        rcases List.mem_append.mp member with head | tail
        · exact ⟨value, List.mem_cons_self, head⟩
        · rcases (mem_flatMap (values := values)).mp tail with
            ⟨source, sourceMember, targetMember⟩
          exact ⟨source, List.mem_cons_of_mem value sourceMember,
            targetMember⟩
      · rintro ⟨source, sourceMember, targetMember⟩
        rcases List.mem_cons.mp sourceMember with head | tail
        · subst source
          exact List.mem_append.mpr (Or.inl targetMember)
        · exact List.mem_append.mpr (Or.inr
            ((mem_flatMap (values := values)).mpr
              ⟨source, tail, targetMember⟩))

/-- Membership in a finite filter-map carries the selected `some`
certificate. -/
theorem mem_filterMap {function : Alpha → Option Beta} {target : Beta} :
    ∀ {values : List Alpha},
      target ∈ values.filterMap function ↔
        ∃ source, source ∈ values ∧ function source = some target
  | [] => by
      constructor
      · intro impossible
        nomatch impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      cases selected : function value with
      | none =>
          rw [List.filterMap_cons_none selected]
          constructor
          · intro member
            rcases (mem_filterMap (values := values)).mp member with
              ⟨source, sourceMember, equal⟩
            exact ⟨source, List.mem_cons_of_mem value sourceMember, equal⟩
          · rintro ⟨source, sourceMember, equal⟩
            rcases List.mem_cons.mp sourceMember with head | tail
            · subst source
              rw [selected] at equal
              nomatch equal
            · exact (mem_filterMap (values := values)).mpr
                ⟨source, tail, equal⟩
      | some selectedValue =>
          rw [List.filterMap_cons_some selected]
          constructor
          · intro member
            rcases List.mem_cons.mp member with head | tail
            · exact ⟨value, List.mem_cons_self,
                selected.trans (congrArg some head.symm)⟩
            · rcases (mem_filterMap (values := values)).mp tail with
                ⟨source, sourceMember, equal⟩
              exact ⟨source, List.mem_cons_of_mem value sourceMember, equal⟩
          · rintro ⟨source, sourceMember, equal⟩
            rcases List.mem_cons.mp sourceMember with head | tail
            · subst source
              have valuesEqual : selectedValue = target := by
                injection selected.symm.trans equal
              exact List.mem_cons.mpr (Or.inl valuesEqual.symm)
            · exact List.mem_cons.mpr (Or.inr
                ((mem_filterMap (values := values)).mpr
                  ⟨source, tail, equal⟩))

/-- A successful finite search is exactly a displayed satisfying member. -/
theorem find?_isSome {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      (values.find? predicate).isSome ↔
        ∃ value, value ∈ values ∧ predicate value
  | [] => by
      constructor
      · intro impossible
        exact Bool.noConfusion impossible
      · rintro ⟨_, impossible, _⟩
        nomatch impossible
  | value :: values => by
      cases selected : predicate value with
      | false =>
          rw [List.find?_cons, selected]
          constructor
          · intro found
            rcases (find?_isSome (values := values)).mp found with
              ⟨source, sourceMember, accepted⟩
            exact ⟨source, List.mem_cons_of_mem value sourceMember, accepted⟩
          · rintro ⟨source, sourceMember, accepted⟩
            rcases List.mem_cons.mp sourceMember with head | tail
            · subst source
              rw [selected] at accepted
              exact Bool.noConfusion accepted
            · exact (find?_isSome (values := values)).mpr
                ⟨source, tail, accepted⟩
      | true =>
          rw [List.find?_cons, selected]
          constructor
          · intro _
            exact ⟨value, List.mem_cons_self, selected⟩
          · intro _
            rfl

/-- A failed Boolean search rejects every displayed list member.  The proof
recurses over the actual list and does not invoke a decidable existential. -/
theorem find?_eq_none {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      values.find? predicate = none ↔
        ∀ value ∈ values, predicate value = false
  | [] => by
      constructor
      · intro _ value impossible
        nomatch impossible
      · intro _
        rfl
  | head :: tail => by
      cases accepted : predicate head with
      | false =>
          rw [List.find?_cons, accepted, find?_eq_none]
          constructor
          · intro tailRejected value member
            rcases List.mem_cons.mp member with equal | tailMember
            · exact equal ▸ accepted
            · exact tailRejected value tailMember
          · intro rejected value member
            exact rejected value (List.mem_cons_of_mem head member)
      | true =>
          rw [List.find?_cons, accepted]
          constructor
          · intro impossible
            nomatch impossible
          · intro rejected
            have impossible := rejected head List.mem_cons_self
            rw [accepted] at impossible
            exact Bool.noConfusion impossible

/-- A finite Boolean `all` succeeds exactly when every displayed member
succeeds. -/
theorem all_eq_true {predicate : Alpha → Bool} :
    ∀ {values : List Alpha},
      values.all predicate = true ↔
        ∀ value ∈ values, predicate value = true
  | [] => by
      constructor
      · intro _ value impossible
        nomatch impossible
      · intro _
        rfl
  | head :: tail => by
      change (predicate head && tail.all predicate) = true ↔ _
      rw [Bool.and_eq_true, all_eq_true]
      constructor
      · rintro ⟨headAccepted, tailAccepted⟩ value member
        rcases List.mem_cons.mp member with equal | tailMember
        · exact equal ▸ headAccepted
        · exact tailAccepted value tailMember
      · intro accepted
        exact ⟨accepted head List.mem_cons_self,
          fun value member =>
            accepted value (List.mem_cons_of_mem head member)⟩

/-- Membership in `range bound` is the computed strict bound. -/
theorem mem_range {value bound : Nat} :
    value ∈ List.range bound ↔ value < bound := by
  induction bound with
  | zero =>
      constructor
      · intro impossible
        nomatch impossible
      · intro impossible
        exact False.elim (Nat.not_lt_zero value impossible)
  | succ bound inductionHypothesis =>
      rw [List.range_succ]
      constructor
      · intro member
        rcases List.mem_append.mp member with earlier | last
        · exact Nat.lt_trans (inductionHypothesis.mp earlier)
            (Nat.lt_succ_self bound)
        · have equal : value = bound := List.mem_singleton.mp last
          exact equal.symm ▸ Nat.lt_succ_self bound
      · intro less
        have lessEqual : value ≤ bound := Nat.le_of_lt_succ less
        rcases Nat.lt_or_eq_of_le lessEqual with earlier | equal
        · exact List.mem_append.mpr
            (Or.inl (inductionHypothesis.mpr earlier))
        · exact List.mem_append.mpr
            (Or.inr (List.mem_singleton.mpr equal))

/-- `ofFn` exposes its head and structurally smaller tail directly. -/
theorem ofFn_succ {size : Nat} {function : Fin (size + 1) → Alpha} :
    List.ofFn function =
      function 0 :: List.ofFn (fun index => function index.succ) := by
  unfold List.ofFn
  rw [Fin.foldr_succ]

/-- Pointwise equality gives equality of the materialized finite tables,
without first identifying the indexing functions. -/
theorem ofFn_congr {size : Nat} {left right : Fin size → Alpha}
    (equal : ∀ index, left index = right index) :
    List.ofFn left = List.ofFn right := by
  induction size with
  | zero =>
      rw [List.ofFn_zero, List.ofFn_zero]
  | succ size inductionHypothesis =>
      rw [ofFn_succ, ofFn_succ, equal 0,
        inductionHypothesis (fun index => equal index.succ)]

/-- `ofFn` may equivalently expose its final entry.  The list equality is
proved from structural recursion and pointwise finite-index equalities. -/
theorem ofFn_succ_last {size : Nat}
    {function : Fin (size + 1) → Alpha} :
    List.ofFn function =
      List.ofFn (fun index => function index.castSucc) ++
        [function (Fin.last size)] := by
  induction size with
  | zero =>
      rw [ofFn_succ]
      have empty : List.ofFn
          (fun index : Fin 0 => function index.castSucc) = [] :=
        List.ofFn_zero
      rw [empty, List.nil_append]
      apply congrArg List.singleton
      apply congrArg function
      apply Fin.ext
      rfl
  | succ size inductionHypothesis =>
      calc
        List.ofFn function =
            function 0 :: List.ofFn (fun index => function index.succ) :=
          ofFn_succ
        _ = function 0 ::
            (List.ofFn (fun index : Fin size =>
                function index.castSucc.succ) ++
              [function (Fin.last (size + 1))]) := by
          apply congrArg (List.cons (function 0))
          calc
            List.ofFn (fun index : Fin (size + 1) => function index.succ) =
                List.ofFn (fun index : Fin size =>
                    function index.succ.castSucc) ++
                  [function (Fin.last size).succ] :=
              inductionHypothesis
            _ = List.ofFn (fun index : Fin size =>
                    function index.castSucc.succ) ++
                  [function (Fin.last (size + 1))] := by
              have firstEqual :
                  List.ofFn (fun index : Fin size =>
                      function index.succ.castSucc) =
                    List.ofFn (fun index : Fin size =>
                      function index.castSucc.succ) := by
                apply ofFn_congr
                intro index
                apply congrArg function
                apply Fin.ext
                rfl
              have lastEqual : [function (Fin.last size).succ] =
                  [function (Fin.last (size + 1))] := by
                apply congrArg List.singleton
                apply congrArg function
                apply Fin.ext
                rfl
              rw [firstEqual, lastEqual]
        _ = (function 0 :: List.ofFn (fun index : Fin size =>
                function index.castSucc.succ)) ++
              [function (Fin.last (size + 1))] := rfl
        _ = List.ofFn (fun index : Fin (size + 1) =>
                function index.castSucc) ++
              [function (Fin.last (size + 1))] := by
          apply congrArg (fun values =>
            values ++ [function (Fin.last (size + 1))])
          rw [ofFn_succ]
          apply congrArg (List.cons (function 0))
          apply ofFn_congr
          intro index
          apply congrArg function
          apply Fin.ext
          rfl

/-- Materializing a finite table over an index sum is the concatenation of
its displayed left and right index tables. -/
theorem ofFn_add {leftSize rightSize : Nat}
    {function : Fin (leftSize + rightSize) → Alpha} :
    List.ofFn function =
      List.ofFn (fun index =>
        function (index.castLE (Nat.le_add_right leftSize rightSize))) ++
      List.ofFn (fun index => function (index.natAdd leftSize)) := by
  induction rightSize with
  | zero =>
      have firstEqual : List.ofFn function =
          List.ofFn (fun index : Fin leftSize =>
            function (index.castLE (Nat.le_add_right leftSize 0))) := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      calc
        List.ofFn function =
            List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) :=
          firstEqual
        _ = List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) ++ [] :=
          (List.append_nil _).symm
        _ = List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) ++
            List.ofFn (fun index : Fin 0 =>
              function (index.natAdd leftSize)) := by
          rw [List.ofFn_zero]
  | succ rightSize inductionHypothesis =>
      let prefixFunction : Fin (leftSize + rightSize) → Alpha :=
        fun index => function index.castSucc
      let leftPrevious : Fin leftSize → Alpha := fun index =>
        prefixFunction
          (index.castLE (Nat.le_add_right leftSize rightSize))
      let rightPrevious : Fin rightSize → Alpha := fun index =>
        prefixFunction (index.natAdd leftSize)
      let leftCurrent : Fin leftSize → Alpha := fun index =>
        function
          (index.castLE (Nat.le_add_right leftSize (rightSize + 1)))
      let rightCurrent : Fin (rightSize + 1) → Alpha := fun index =>
        function (index.natAdd leftSize)
      have prefixSplit : List.ofFn prefixFunction =
          List.ofFn leftPrevious ++ List.ofFn rightPrevious :=
        inductionHypothesis
      have leftEqual : List.ofFn leftPrevious =
          List.ofFn leftCurrent := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      have rightEqual : List.ofFn rightPrevious =
          List.ofFn (fun index : Fin rightSize =>
            rightCurrent index.castSucc) := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      have lastEqual : function (Fin.last (leftSize + rightSize)) =
          rightCurrent (Fin.last rightSize) := by
        apply congrArg function
        apply Fin.ext
        rfl
      have rightSplit : List.ofFn rightCurrent =
          List.ofFn (fun index : Fin rightSize =>
            rightCurrent index.castSucc) ++
            [rightCurrent (Fin.last rightSize)] := ofFn_succ_last
      calc
        List.ofFn function =
            List.ofFn prefixFunction ++
              [function (Fin.last (leftSize + rightSize))] :=
          ofFn_succ_last
        _ = (List.ofFn leftPrevious ++ List.ofFn rightPrevious) ++
              [function (Fin.last (leftSize + rightSize))] := by
          rw [prefixSplit]
        _ = List.ofFn leftPrevious ++
              (List.ofFn rightPrevious ++
                [function (Fin.last (leftSize + rightSize))]) :=
          List.append_assoc _ _ _
        _ = List.ofFn leftCurrent ++
              (List.ofFn (fun index : Fin rightSize =>
                  rightCurrent index.castSucc) ++
                [rightCurrent (Fin.last rightSize)]) := by
          rw [leftEqual, rightEqual, lastEqual]
        _ = List.ofFn leftCurrent ++ List.ofFn rightCurrent := by
          rw [rightSplit]

/-- The length of a displayed finite function table is its finite domain
size. -/
theorem length_ofFn {size : Nat} {function : Fin size → Alpha} :
    (List.ofFn function).length = size := by
  induction size with
  | zero =>
      rw [List.ofFn_zero]
      rfl
  | succ size inductionHypothesis =>
      rw [ofFn_succ, List.length_cons, inductionHypothesis]

/-- Mapping a displayed finite function table maps each table entry. -/
theorem map_ofFn {size : Nat} {function : Fin size → Alpha}
    {transform : Alpha → Beta} :
    (List.ofFn function).map transform =
      List.ofFn (transform ∘ function) := by
  induction size with
  | zero =>
      rw [List.ofFn_zero, List.ofFn_zero]
      rfl
  | succ size inductionHypothesis =>
      rw [ofFn_succ, List.map_cons, ofFn_succ,
        inductionHypothesis]
      rfl

/-- Every attached element occurs in the displayed attached list. -/
theorem mem_attach : ∀ (values : List Alpha)
    (attached : {value // value ∈ values}), attached ∈ values.attach
  | [], attached => by
      nomatch attached.property
  | head :: tail, ⟨value, member⟩ => by
      rw [List.attach_cons]
      rcases List.mem_cons.mp member with equal | tailMember
      · apply List.mem_cons.mpr
        left
        apply Subtype.ext
        exact equal
      · apply List.mem_cons.mpr
        right
        apply mem_map.mpr
        refine ⟨⟨value, tailMember⟩,
          mem_attach tail ⟨value, tailMember⟩, ?_⟩
        apply Subtype.ext
        rfl

/-- Pairwise relatedness is preserved and reflected by a finite map. -/
theorem pairwise_map {function : Alpha → Beta}
    {relation : Beta → Beta → Prop} :
    ∀ {values : List Alpha},
      (values.map function).Pairwise relation ↔
        values.Pairwise
          (fun left right => relation (function left) (function right))
  | [] => by
      constructor <;> intro _ <;> exact List.Pairwise.nil
  | head :: tail => by
      rw [List.map_cons, List.pairwise_cons, List.pairwise_cons]
      constructor
      · rintro ⟨headRelated, tailRelated⟩
        exact ⟨fun value member =>
          headRelated (function value) (mem_map_of_mem member),
          pairwise_map.mp tailRelated⟩
      · rintro ⟨headRelated, tailRelated⟩
        refine ⟨?_, pairwise_map.mpr tailRelated⟩
        intro mapped mappedMember
        rcases mem_map.mp mappedMember with
          ⟨source, sourceMember, equal⟩
        exact equal ▸ headRelated source sourceMember

/-- A singleton is pairwise related for any displayed relation. -/
theorem pairwise_singleton (relation : Alpha → Alpha → Prop)
    (value : Alpha) : [value].Pairwise relation := by
  apply List.pairwise_cons.mpr
  constructor
  · intro other impossible
    nomatch impossible
  · exact List.Pairwise.nil

/-- Assemble pairwise relatedness of an appended finite list from the two
internal certificates and the displayed cross-list certificate. -/
theorem pairwise_append {relation : Alpha → Alpha → Prop} :
    ∀ {left right : List Alpha}, left.Pairwise relation →
      right.Pairwise relation →
      (∀ leftValue ∈ left, ∀ rightValue ∈ right,
        relation leftValue rightValue) →
      (left ++ right).Pairwise relation
  | [], _, _, rightPairwise, _ => rightPairwise
  | head :: tail, right, leftPairwise, rightPairwise, cross => by
      apply List.pairwise_cons.mpr
      constructor
      · intro value member
        rcases List.mem_append.mp member with tailMember | rightMember
        · exact (List.pairwise_cons.mp leftPairwise).1 value tailMember
        · exact cross head List.mem_cons_self value rightMember
      · exact pairwise_append (List.pairwise_cons.mp leftPairwise).2
          rightPairwise (fun leftValue leftMember =>
            cross leftValue (List.mem_cons_of_mem head leftMember))

/-- A singleton list has no duplicate entries. -/
theorem nodup_singleton (value : Alpha) : [value].Nodup :=
  pairwise_singleton (fun left right : Alpha => left ≠ right) value

/-- Append two duplicate-free displayed lists when every cross-list pair is
distinct. -/
theorem nodup_append {left right : List Alpha}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (cross : ∀ leftValue ∈ left, ∀ rightValue ∈ right,
      leftValue ≠ rightValue) :
    (left ++ right).Nodup :=
  pairwise_append leftNodup rightNodup cross

/-- An injective map preserves duplicate-freeness by structural recursion
over the displayed source list. -/
theorem nodup_map_of_injective {function : Alpha → Beta}
    (injective : Function.Injective function) :
    ∀ {values : List Alpha}, values.Nodup → (values.map function).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      rcases List.pairwise_cons.mp nodup with ⟨headFresh, tailNodup⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, nodup_map_of_injective injective tailNodup⟩
      intro mapped mappedMember equal
      rcases mem_map.mp mappedMember with
        ⟨source, sourceMember, sourceEqual⟩
      apply headFresh source sourceMember
      apply injective
      exact equal.trans sourceEqual.symm

/-- A displayed membership splits a finite list at the displayed occurrence.
The recursive proof retains the actual prefix and suffix; it does not choose
an occurrence from an abstract nonempty set. -/
theorem split_of_mem {target : Alpha} :
    ∀ {values : List Alpha}, target ∈ values →
      ∃ before after, values = before ++ target :: after
  | [], impossible => by
      nomatch impossible
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | tailMember
      · subst head
        exact ⟨[], tail, rfl⟩
      · rcases split_of_mem tailMember with ⟨before, after, split⟩
        exact ⟨head :: before, after, by rw [split]; rfl⟩

/-- Removing one displayed middle entry preserves pairwise relatedness. -/
theorem pairwise_remove_middle {relation : Alpha → Alpha → Prop}
    {middle : Alpha} :
    ∀ {before after : List Alpha},
      (before ++ middle :: after).Pairwise relation →
        (before ++ after).Pairwise relation
  | [], _, pairwise => (List.pairwise_cons.mp pairwise).2
  | head :: tail, after, pairwise => by
      rcases List.pairwise_cons.mp pairwise with ⟨headAll, restPairwise⟩
      apply List.pairwise_cons.mpr
      refine ⟨?_, pairwise_remove_middle restPairwise⟩
      intro value member
      rcases List.mem_append.mp member with tailMember | afterMember
      · exact headAll value
          (List.mem_append.mpr (Or.inl tailMember))
      · exact headAll value
          (List.mem_append.mpr
            (Or.inr (List.mem_cons_of_mem middle afterMember)))

/-- A duplicate-free displayed subcollection cannot be longer than a
duplicate-free displayed carrier containing all of its entries.  This is the
finite pigeonhole bound proved directly on the two lists. -/
theorem nodup_length_le_of_mem :
    ∀ {selected : List Alpha}, selected.Nodup →
      ∀ {carrier : List Alpha}, carrier.Nodup →
        (∀ value ∈ selected, value ∈ carrier) →
          selected.length ≤ carrier.length
  | [], _, _, _, _ => Nat.zero_le _
  | head :: tail, selectedNodup, carrier, carrierNodup, contained => by
      rcases split_of_mem
          (contained head List.mem_cons_self) with
        ⟨before, after, carrierSplit⟩
      have reducedCarrier : (before ++ after).Nodup := by
        apply pairwise_remove_middle (middle := head)
        rw [← carrierSplit]
        exact carrierNodup
      have tailContained :
          ∀ value ∈ tail, value ∈ before ++ after := by
        intro value valueMember
        have carrierMember := contained value
          (List.mem_cons_of_mem head valueMember)
        rw [carrierSplit] at carrierMember
        rcases List.mem_append.mp carrierMember with beforeMember | restMember
        · exact List.mem_append.mpr (Or.inl beforeMember)
        · rcases List.mem_cons.mp restMember with equal | suffixMember
          · exact False.elim
              ((List.pairwise_cons.mp selectedNodup).1 value valueMember
                equal.symm)
          · exact List.mem_append.mpr (Or.inr suffixMember)
      have tailBound := nodup_length_le_of_mem
        (List.pairwise_cons.mp selectedNodup).2
        reducedCarrier tailContained
      rw [List.length_append] at tailBound
      rw [carrierSplit, List.length_cons, List.length_append,
        List.length_cons]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_right tailBound 1

/-- Search the left list in order for its first entry also displayed in the
right list. -/
def firstIntersection? [DecidableEq Alpha] :
    List Alpha → List Alpha → Option Alpha
  | [], _ => none
  | head :: tail, right =>
      if head ∈ right then some head else firstIntersection? tail right

/-- Every successful intersection search returns a displayed member of both
input lists. -/
theorem firstIntersection?_eq_some [DecidableEq Alpha]
    {target : Alpha} :
    ∀ {left right : List Alpha},
      firstIntersection? left right = some target →
        target ∈ left ∧ target ∈ right
  | [], _, impossible => by
      nomatch impossible
  | head :: tail, right, found => by
      by_cases headMember : head ∈ right
      · rw [firstIntersection?, if_pos headMember] at found
        injection found with equal
        exact ⟨List.mem_cons.mpr (Or.inl equal.symm), equal ▸ headMember⟩
      · rw [firstIntersection?, if_neg headMember] at found
        rcases firstIntersection?_eq_some found with
          ⟨tailMember, rightMember⟩
        exact ⟨List.mem_cons_of_mem head tailMember, rightMember⟩

/-- A failed intersection search certifies that every displayed cross-list
pair is unequal. -/
theorem firstIntersection?_eq_none [DecidableEq Alpha] :
    ∀ {left right : List Alpha},
      firstIntersection? left right = none →
        ∀ leftValue ∈ left, ∀ rightValue ∈ right,
          leftValue ≠ rightValue
  | [], _, _, _, impossible => by
      nomatch impossible
  | head :: tail, right, failed, leftValue, leftMember => by
      by_cases headMember : head ∈ right
      · rw [firstIntersection?, if_pos headMember] at failed
        nomatch failed
      · rw [firstIntersection?, if_neg headMember] at failed
        rcases List.mem_cons.mp leftMember with equal | tailMember
        · subst leftValue
          intro rightValue rightMember equal
          exact headMember (equal ▸ rightMember)
        · exact firstIntersection?_eq_none failed leftValue tailMember

/-- Constructive finite pigeonhole principle for two displayed lists.  If
their combined length exceeds a duplicate-free carrier containing every
entry, the recursive intersection search succeeds. -/
theorem firstIntersection?_ne_none_of_length_gt [DecidableEq Alpha]
    {left right carrier : List Alpha}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (leftContained : ∀ value ∈ left, value ∈ carrier)
    (rightContained : ∀ value ∈ right, value ∈ carrier)
    (carrierNodup : carrier.Nodup)
    (oversized : carrier.length < left.length + right.length) :
    firstIntersection? left right ≠ none := by
  intro failed
  have appendedNodup : (left ++ right).Nodup :=
    nodup_append leftNodup rightNodup
      (firstIntersection?_eq_none failed)
  have appendedContained :
      ∀ value ∈ left ++ right, value ∈ carrier := by
    intro value member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact leftContained value leftMember
    · exact rightContained value rightMember
  have bound := nodup_length_le_of_mem appendedNodup carrierNodup
    appendedContained
  rw [List.length_append] at bound
  exact (Nat.not_le_of_lt oversized) bound

/-- A pairwise certificate relates any two displayed entries in index order.
This is the direction used by RFAP and CCL; no converse is needed. -/
theorem pairwise_getElem {relation : Alpha → Alpha → Prop}
    {values : List Alpha} (pairwise : values.Pairwise relation) :
    ∀ (left right : Nat) (leftBound : left < values.length)
      (rightBound : right < values.length),
      left < right → relation values[left] values[right] := by
  induction values with
  | nil =>
      intro left _ leftBound
      nomatch leftBound
  | cons head tail inductionHypothesis =>
      intro left right leftBound rightBound ordered
      cases left with
      | zero =>
          cases right with
          | zero => exact False.elim (Nat.lt_irrefl 0 ordered)
          | succ right =>
              have tailBound : right < tail.length :=
                Nat.lt_of_succ_lt_succ rightBound
              exact (List.pairwise_cons.mp pairwise).1 tail[right]
                (List.getElem_mem tailBound)
      | succ left =>
          cases right with
          | zero =>
              exact False.elim (Nat.not_lt_zero (Nat.succ left) ordered)
          | succ right =>
              have leftTailBound : left < tail.length :=
                Nat.lt_of_succ_lt_succ leftBound
              have rightTailBound : right < tail.length :=
                Nat.lt_of_succ_lt_succ rightBound
              have tailOrdered : left < right :=
                Nat.lt_of_succ_lt_succ ordered
              exact inductionHypothesis
                (List.pairwise_cons.mp pairwise).2 left right
                leftTailBound rightTailBound tailOrdered

/-- For a symmetric relation, moving one displayed middle entry to the front
preserves and reflects pairwise relatedness. -/
theorem pairwise_middle {R : Alpha → Alpha → Prop}
    (symmetric : ∀ {left right}, R left right → R right left)
    {middle : Alpha} {left right : List Alpha} :
    (left ++ middle :: right).Pairwise R ↔
      (middle :: (left ++ right)).Pairwise R := by
  constructor
  · intro pairwise
    induction left with
    | nil => exact pairwise
    | cons head tail inductionHypothesis =>
        rcases List.pairwise_cons.mp pairwise with
          ⟨headAll, tailPairwise⟩
        have movedTail := inductionHypothesis tailPairwise
        rcases List.pairwise_cons.mp movedTail with
          ⟨middleAll, remainingPairwise⟩
        apply List.pairwise_cons.mpr
        refine ⟨?_, List.pairwise_cons.mpr
          ⟨?_, remainingPairwise⟩⟩
        · intro value member
          rcases List.mem_cons.mp member with equal | remainingMember
          · exact equal ▸ symmetric (headAll middle
              (List.mem_append.mpr (Or.inr List.mem_cons_self)))
          · exact middleAll value remainingMember
        · intro value member
          rcases List.mem_append.mp member with tailMember | rightMember
          · exact headAll value
              (List.mem_append.mpr (Or.inl tailMember))
          · exact headAll value (List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem middle rightMember)))
  · intro pairwise
    induction left with
    | nil => exact pairwise
    | cons head tail inductionHypothesis =>
        rcases List.pairwise_cons.mp pairwise with
          ⟨middleAll, headRemainingPairwise⟩
        rcases List.pairwise_cons.mp headRemainingPairwise with
          ⟨headAll, remainingPairwise⟩
        have movedTail : (middle :: tail ++ right).Pairwise R :=
          List.pairwise_cons.mpr ⟨fun value member =>
            middleAll value (List.mem_cons_of_mem head member),
            remainingPairwise⟩
        have tailPairwise := inductionHypothesis movedTail
        apply List.pairwise_cons.mpr
        refine ⟨?_, tailPairwise⟩
        intro value member
        rcases List.mem_append.mp member with tailMember | middleRightMember
        · exact headAll value
            (List.mem_append.mpr (Or.inl tailMember))
        · rcases List.mem_cons.mp middleRightMember with equal | rightMember
          · exact equal ▸ symmetric (middleAll head List.mem_cons_self)
          · exact headAll value
              (List.mem_append.mpr (Or.inr rightMember))

end QuotientFreeList
