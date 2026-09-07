import mathlib.Data.ConstructiveList

/-!
# Finite Boolean spans with retained word witnesses

This module incrementally spans one supplied finite list of fixed-length
Boolean vectors under XOR.  It never forms a function space or an ambient
infinite vector space.  Every distinct image vector retains a Boolean word
witness; the result also caches closure, completeness, duplicate-freeness,
rank, and the exact power-of-two length formula.
-/

namespace RFAP.FiniteBooleanSpan

/-- Choice-free XOR on two displayed bits. -/
def bitXor : Bool → Bool → Bool
  | false, value => value
  | true, value => !value

private theorem bitXor_comm (left right : Bool) :
    bitXor left right = bitXor right left := by
  cases left <;> cases right <;> rfl

private theorem bitXor_assoc (first second third : Bool) :
    bitXor (bitXor first second) third =
      bitXor first (bitXor second third) := by
  cases first <;> cases second <;> cases third <;> rfl

private theorem bitXor_self (value : Bool) :
    bitXor value value = false := by
  cases value <;> rfl

/-- Coordinatewise XOR.  The span engine calls this only on equal-length
lists; the exhausted-input cases make the function total. -/
def bitsXor : List Bool → List Bool → List Bool
  | left :: leftTail, right :: rightTail =>
      bitXor left right :: bitsXor leftTail rightTail
  | _, _ => []

private theorem bitsXor_length_of_eq {left right : List Bool}
    (lengthEq : left.length = right.length) :
    (bitsXor left right).length = left.length := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => nomatch lengthEq
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => nomatch lengthEq
      | cons rightHead rightTail =>
          simp only [List.length_cons] at lengthEq ⊢
          unfold bitsXor
          simp only [List.length_cons]
          rw [inductionHypothesis (Nat.succ.inj lengthEq)]

private theorem bitsXor_comm_of_length_eq {left right : List Bool}
    (lengthEq : left.length = right.length) :
    bitsXor left right = bitsXor right left := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => nomatch lengthEq
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => nomatch lengthEq
      | cons rightHead rightTail =>
          simp only [List.length_cons] at lengthEq
          simp only [bitsXor, List.cons.injEq]
          exact ⟨bitXor_comm leftHead rightHead,
            inductionHypothesis (Nat.succ.inj lengthEq)⟩

private theorem bitsXor_assoc_of_lengths
    {first second third : List Bool}
    (firstSecond : first.length = second.length)
    (secondThird : second.length = third.length) :
    bitsXor (bitsXor first second) third =
      bitsXor first (bitsXor second third) := by
  induction first generalizing second third with
  | nil =>
      cases second with
      | nil =>
          cases third with
          | nil => rfl
          | cons _ _ => nomatch secondThird
      | cons _ _ => nomatch firstSecond
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | nil => nomatch firstSecond
      | cons secondHead secondTail =>
          cases third with
          | nil => nomatch secondThird
          | cons thirdHead thirdTail =>
              simp only [List.length_cons] at firstSecond secondThird
              simp only [bitsXor, List.cons.injEq]
              exact ⟨bitXor_assoc firstHead secondHead thirdHead,
                inductionHypothesis (Nat.succ.inj firstSecond)
                  (Nat.succ.inj secondThird)⟩

private theorem bitsXor_self_eq_false : ∀ values : List Bool,
    bitsXor values values = List.replicate values.length false
  | [] => rfl
  | head :: tail => by
      simp only [bitsXor, List.length_cons, List.replicate_succ,
        List.cons.injEq, bitXor_self, true_and]
      exact bitsXor_self_eq_false tail

private theorem false_bitsXor : ∀ values : List Bool,
    bitsXor (List.replicate values.length false) values = values
  | [] => rfl
  | head :: tail => by
      simp only [List.length_cons, List.replicate_succ, bitsXor, bitXor]
      rw [false_bitsXor tail]

private theorem bitsXor_false : ∀ values : List Bool,
    bitsXor values (List.replicate values.length false) = values
  | [] => rfl
  | head :: tail => by
      simp only [List.length_cons, List.replicate_succ, bitsXor]
      rw [bitXor_comm head false, bitXor, bitsXor_false tail]

/-- A fixed-length displayed Boolean vector. -/
@[ext]
structure Vector (width : Nat) where
  bits : List Bool
  length_eq : bits.length = width

/-- The all-false vector of one displayed width. -/
def zero (width : Nat) : Vector width where
  bits := List.replicate width false
  length_eq := List.length_replicate

/-- Coordinatewise XOR of fixed-length vectors. -/
def xor {width : Nat} (left right : Vector width) : Vector width where
  bits := bitsXor left.bits right.bits
  length_eq := (bitsXor_length_of_eq
    (left.length_eq.trans right.length_eq.symm)).trans left.length_eq

theorem xor_comm {width : Nat} (left right : Vector width) :
    xor left right = xor right left := by
  apply Vector.ext
  exact bitsXor_comm_of_length_eq
    (left.length_eq.trans right.length_eq.symm)

theorem xor_assoc {width : Nat} (first second third : Vector width) :
    xor (xor first second) third = xor first (xor second third) := by
  apply Vector.ext
  exact bitsXor_assoc_of_lengths
    (first.length_eq.trans second.length_eq.symm)
    (second.length_eq.trans third.length_eq.symm)

theorem xor_self {width : Nat} (value : Vector width) :
    xor value value = zero width := by
  apply Vector.ext
  change bitsXor value.bits value.bits = List.replicate width false
  rw [bitsXor_self_eq_false, value.length_eq]

theorem zero_xor {width : Nat} (value : Vector width) :
    xor (zero width) value = value := by
  apply Vector.ext
  change bitsXor (List.replicate width false) value.bits = value.bits
  have replicatedEqual : List.replicate width false =
      List.replicate value.bits.length false :=
    congrArg (fun length => List.replicate length false)
      value.length_eq.symm
  exact (congrArg (fun bits => bitsXor bits value.bits)
    replicatedEqual).trans (false_bitsXor value.bits)

theorem xor_zero {width : Nat} (value : Vector width) :
    xor value (zero width) = value := by
  apply Vector.ext
  change bitsXor value.bits (List.replicate width false) = value.bits
  have replicatedEqual : List.replicate width false =
      List.replicate value.bits.length false :=
    congrArg (fun length => List.replicate length false)
      value.length_eq.symm
  exact (congrArg (fun bits => bitsXor value.bits bits)
    replicatedEqual).trans (bitsXor_false value.bits)

private def boolListDecEq : (left right : List Bool) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun impossible => by nomatch impossible
  | _ :: _, [] => isFalse fun impossible => by nomatch impossible
  | left :: leftTail, right :: rightTail =>
      match Bool.decEq left right with
      | isFalse different => isFalse fun equal =>
          different (List.cons.inj equal).1
      | isTrue equal =>
          match boolListDecEq leftTail rightTail with
          | isFalse different => isFalse fun listEqual =>
              different (List.cons.inj listEqual).2
          | isTrue tailEqual => isTrue (by rw [equal, tailEqual])

private def vectorDecEq {width : Nat} (left right : Vector width) :
    Decidable (left = right) :=
  match boolListDecEq left.bits right.bits with
  | isTrue equal => isTrue (Vector.ext equal)
  | isFalse different => isFalse fun vectorEqual =>
      different (congrArg Vector.bits vectorEqual)

/-- Evaluate one finite Boolean word against one finite generator list. -/
def evaluate {width : Nat} : List Bool → List (Vector width) → Vector width
  | true :: choices, generator :: generators =>
      xor generator (evaluate choices generators)
  | false :: choices, _generator :: generators =>
      evaluate choices generators
  | _, _ => zero width

theorem evaluate_allFalse {width : Nat} :
    ∀ generators : List (Vector width),
      evaluate (List.replicate generators.length false) generators =
        zero width
  | [] => rfl
  | _generator :: generators => by
      change evaluate (List.replicate generators.length false) generators =
        zero width
      exact evaluate_allFalse generators

theorem generator_evaluation {width : Nat}
    {generator : Vector width} :
    ∀ {generators : List (Vector width)}, generator ∈ generators →
      ∃ choices : List Bool,
        choices.length = generators.length ∧
          evaluate choices generators = generator
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      rw [List.mem_cons] at member
      rcases member with equal | tailMember
      · subst head
        let choices := true :: List.replicate tail.length false
        refine ⟨choices, ?_, ?_⟩
        · simp only [choices, List.length_cons, List.length_replicate]
        · change xor generator
            (evaluate (List.replicate tail.length false) tail) = generator
          rw [evaluate_allFalse, xor_zero]
      · rcases generator_evaluation tailMember with
          ⟨tailChoices, tailLength, tailEvaluation⟩
        exact ⟨false :: tailChoices, congrArg Nat.succ tailLength,
          tailEvaluation⟩

/-- One distinct image vector with a retained Boolean generator word. -/
structure Entry {width : Nat} (generators : List (Vector width)) where
  vector : Vector width
  choices : List Bool
  choices_length : choices.length = generators.length
  evaluates : evaluate choices generators = vector

def prependFalse {width : Nat} (generator : Vector width)
    {generators : List (Vector width)} (entry : Entry generators) :
    Entry (generator :: generators) where
  vector := entry.vector
  choices := false :: entry.choices
  choices_length := congrArg Nat.succ entry.choices_length
  evaluates := entry.evaluates

def prependTrue {width : Nat} (generator : Vector width)
    {generators : List (Vector width)} (entry : Entry generators) :
    Entry (generator :: generators) where
  vector := xor generator entry.vector
  choices := true :: entry.choices
  choices_length := congrArg Nat.succ entry.choices_length
  evaluates := by
    change xor generator (evaluate entry.choices generators) =
      xor generator entry.vector
    rw [entry.evaluates]

private theorem falseVectors {width : Nat} {generator : Vector width}
    {generators : List (Vector width)} :
    ∀ entries : List (Entry generators),
      (entries.map (prependFalse generator)).map Entry.vector =
        entries.map Entry.vector
  | [] => rfl
  | _head :: tail => by
      simp only [List.map_cons, prependFalse]
      rw [falseVectors tail]

private theorem trueVectors {width : Nat} {generator : Vector width}
    {generators : List (Vector width)} :
    ∀ entries : List (Entry generators),
      (entries.map (prependTrue generator)).map Entry.vector =
        (entries.map Entry.vector).map (xor generator)
  | [] => rfl
  | _head :: tail => by
      simp only [List.map_cons, prependTrue]
      rw [trueVectors tail]

inductive Search {width : Nat} {generators : List (Vector width)}
    (target : Vector width) : List (Entry generators) → Type
  | found (entry : Entry generators) (member : entry ∈ entries)
      (vector_eq : entry.vector = target) : Search target entries
  | absent (notFound : ∀ entry ∈ entries, entry.vector ≠ target) :
      Search target entries

def search {width : Nat} {generators : List (Vector width)}
    (target : Vector width) :
    (entries : List (Entry generators)) → Search target entries
  | [] => Search.absent fun _entry impossible => by nomatch impossible
  | head :: tail =>
      match vectorDecEq head.vector target with
      | isTrue equal => Search.found head List.mem_cons_self equal
      | isFalse different =>
          match search target tail with
          | Search.found entry member equal =>
              Search.found entry (List.mem_cons_of_mem head member) equal
          | Search.absent notFound => Search.absent fun entry member => by
              rcases List.mem_cons.mp member with equal | tailMember
              · subst entry
                exact different
              · exact notFound entry tailMember

structure Result {width : Nat} (generators : List (Vector width)) where
  rank : Nat
  entries : List (Entry generators)
  vectors_nodup : (entries.map Entry.vector).Nodup
  length_eq : entries.length = 2 ^ rank
  complete : ∀ choices : List Bool,
    choices.length = generators.length →
      ∃ entry ∈ entries, evaluate choices generators = entry.vector
  closed : ∀ left ∈ entries, ∀ right ∈ entries,
    ∃ output ∈ entries, xor left.vector right.vector = output.vector

theorem Result.zero_mem {width : Nat}
    {generators : List (Vector width)} (result : Result generators) :
    ∃ entry ∈ result.entries, entry.vector = zero width := by
  rcases result.complete (List.replicate generators.length false)
      List.length_replicate with ⟨entry, member, evaluation⟩
  exact ⟨entry, member, evaluation.symm.trans
    (evaluate_allFalse generators)⟩

theorem Result.generator_mem {width : Nat}
    {generators : List (Vector width)} (result : Result generators)
    {generator : Vector width} (member : generator ∈ generators) :
    ∃ entry ∈ result.entries, entry.vector = generator := by
  rcases generator_evaluation member with
    ⟨choices, choicesLength, evaluates⟩
  rcases result.complete choices choicesLength with
    ⟨entry, entryMember, classified⟩
  exact ⟨entry, entryMember, classified.symm.trans evaluates⟩

/-- Classify the XOR fold of any supplied finite word whose displayed vectors
all belong to the generator list. -/
theorem Result.classifyXorWord {width : Nat}
    {generators : List (Vector width)} (result : Result generators) :
    ∀ word : List (Vector width),
      (∀ vector ∈ word, vector ∈ generators) →
        ∃ entry ∈ result.entries,
          word.foldr xor (zero width) = entry.vector
  | [], _allMembers => by
      rcases result.zero_mem with ⟨entry, member, vectorEq⟩
      exact ⟨entry, member, vectorEq.symm⟩
  | head :: tail, allMembers => by
      have headMember : head ∈ generators :=
        allMembers head List.mem_cons_self
      have tailMembers : ∀ vector ∈ tail, vector ∈ generators := by
        intro vector member
        exact allMembers vector (List.mem_cons_of_mem head member)
      rcases result.generator_mem headMember with
        ⟨headEntry, headEntryMember, headVector⟩
      rcases result.classifyXorWord tail tailMembers with
        ⟨tailEntry, tailEntryMember, tailVector⟩
      rcases result.closed headEntry headEntryMember tailEntry tailEntryMember
        with ⟨output, outputMember, outputVector⟩
      refine ⟨output, outputMember, ?_⟩
      change xor head (tail.foldr xor (zero width)) = output.vector
      rw [← headVector, tailVector]
      exact outputVector

private theorem xor_left_injective {width : Nat} (generator : Vector width) :
    Function.Injective (xor generator) := by
  intro left right equal
  have canceled := congrArg (xor generator) equal
  simpa only [← xor_assoc, xor_self, zero_xor] using canceled

private theorem generator_eq_xor_of_eq_xor {width : Nat}
    {generator left right : Vector width}
    (equal : left = xor generator right) :
    generator = xor left right := by
  calc
    generator = xor generator (zero width) := (xor_zero generator).symm
    _ = xor generator (xor right right) := by rw [xor_self]
    _ = xor (xor generator right) right :=
      (xor_assoc generator right right).symm
    _ = xor left right := by rw [equal]

private theorem falseMap_mem {width : Nat} {generator : Vector width}
    {generators : List (Vector width)} {entry : Entry generators}
    {entries : List (Entry generators)} (member : entry ∈ entries) :
    prependFalse generator entry ∈ entries.map (prependFalse generator) :=
  QuotientFreeList.mem_map.mpr ⟨entry, member, rfl⟩

private theorem trueMap_mem {width : Nat} {generator : Vector width}
    {generators : List (Vector width)} {entry : Entry generators}
    {entries : List (Entry generators)} (member : entry ∈ entries) :
    prependTrue generator entry ∈ entries.map (prependTrue generator) :=
  QuotientFreeList.mem_map.mpr ⟨entry, member, rfl⟩

/-- Incrementally compute the distinct XOR image and one Boolean word for
every image.  A dependent generator leaves the rank unchanged; an independent
generator produces a certified disjoint doubling. -/
def compute {width : Nat} :
    (generators : List (Vector width)) → Result generators
  | [] =>
      let identity : Entry ([] : List (Vector width)) :=
        { vector := zero width
          choices := []
          choices_length := rfl
          evaluates := rfl }
      { rank := 0
        entries := [identity]
        vectors_nodup := by
          apply List.pairwise_cons.mpr
          exact ⟨(by intro value member; nomatch member), List.Pairwise.nil⟩
        length_eq := rfl
        complete := by
          intro choices lengthZero
          cases choices with
          | nil => exact ⟨identity, List.mem_cons_self, rfl⟩
          | cons _head _tail => nomatch lengthZero
        closed := by
          intro left leftMember right rightMember
          rw [List.mem_singleton] at leftMember rightMember
          subst left
          subst right
          exact ⟨identity, List.mem_cons_self, xor_self (zero width)⟩ }
  | generator :: generators =>
      let previous := compute generators
      let falseEntries := previous.entries.map (prependFalse generator)
      match found : search generator previous.entries with
      | Search.found generatorEntry generatorMember generatorVector =>
          { rank := previous.rank
            entries := falseEntries
            vectors_nodup := by
              rw [falseVectors]
              exact previous.vectors_nodup
            length_eq := by
              rw [List.length_map]
              exact previous.length_eq
            complete := by
              intro choices choicesLength
              cases choices with
              | nil => nomatch choicesLength
              | cons selected tailChoices =>
                  have tailLength : tailChoices.length = generators.length :=
                    Nat.succ.inj choicesLength
                  rcases previous.complete tailChoices tailLength with
                    ⟨tailEntry, tailMember, tailEvaluation⟩
                  cases selected with
                  | false =>
                      exact ⟨prependFalse generator tailEntry,
                        falseMap_mem tailMember, tailEvaluation⟩
                  | true =>
                      rcases previous.closed tailEntry tailMember
                        generatorEntry generatorMember with
                        ⟨output, outputMember, outputEquation⟩
                      refine ⟨prependFalse generator output,
                        falseMap_mem outputMember, ?_⟩
                      change xor generator (evaluate tailChoices generators) =
                        output.vector
                      rw [tailEvaluation, ← generatorVector]
                      exact (xor_comm generatorEntry.vector
                        tailEntry.vector).trans outputEquation
            closed := by
              intro left leftMember right rightMember
              rcases QuotientFreeList.mem_map.mp leftMember with
                ⟨leftSource, leftSourceMember, leftEqual⟩
              rcases QuotientFreeList.mem_map.mp rightMember with
                ⟨rightSource, rightSourceMember, rightEqual⟩
              subst left
              subst right
              rcases previous.closed leftSource leftSourceMember
                rightSource rightSourceMember with
                ⟨output, outputMember, outputEquation⟩
              exact ⟨prependFalse generator output,
                falseMap_mem outputMember, outputEquation⟩ }
      | Search.absent generatorAbsent =>
          let trueEntries := previous.entries.map (prependTrue generator)
          { rank := previous.rank + 1
            entries := falseEntries ++ trueEntries
            vectors_nodup := by
              rw [List.map_append, falseVectors, trueVectors]
              apply QuotientFreeList.nodup_append previous.vectors_nodup
                (QuotientFreeList.nodup_map_of_injective
                  (xor_left_injective generator) previous.vectors_nodup)
              intro leftVector leftVectorMember rightVector rightVectorMember
                equal
              rcases QuotientFreeList.mem_map.mp leftVectorMember with
                ⟨leftEntry, leftEntryMember, leftEntryEqual⟩
              rcases QuotientFreeList.mem_map.mp rightVectorMember with
                ⟨rightSourceVector, rightSourceVectorMember,
                  rightSourceEqual⟩
              rcases QuotientFreeList.mem_map.mp rightSourceVectorMember with
                ⟨rightEntry, rightEntryMember, rightEntryEqual⟩
              have collision : leftEntry.vector =
                  xor generator rightEntry.vector := by
                calc
                  leftEntry.vector = leftVector := leftEntryEqual
                  _ = rightVector := equal
                  _ = xor generator rightSourceVector := rightSourceEqual.symm
                  _ = xor generator rightEntry.vector := by
                    rw [rightEntryEqual]
              rcases previous.closed leftEntry leftEntryMember
                rightEntry rightEntryMember with
                ⟨output, outputMember, outputEquation⟩
              apply generatorAbsent output outputMember
              exact ((generator_eq_xor_of_eq_xor collision).trans
                outputEquation).symm
            length_eq := by
              rw [List.length_append, List.length_map, List.length_map,
                previous.length_eq, Nat.pow_succ, Nat.mul_two]
            complete := by
              intro choices choicesLength
              cases choices with
              | nil => nomatch choicesLength
              | cons selected tailChoices =>
                  have tailLength : tailChoices.length = generators.length :=
                    Nat.succ.inj choicesLength
                  rcases previous.complete tailChoices tailLength with
                    ⟨tailEntry, tailMember, tailEvaluation⟩
                  cases selected with
                  | false =>
                      exact ⟨prependFalse generator tailEntry,
                        List.mem_append_left _ (falseMap_mem tailMember),
                        tailEvaluation⟩
                  | true =>
                      refine ⟨prependTrue generator tailEntry,
                        List.mem_append_right _ (trueMap_mem tailMember), ?_⟩
                      change xor generator (evaluate tailChoices generators) =
                        xor generator tailEntry.vector
                      rw [tailEvaluation]
            closed := by
              intro left leftMember right rightMember
              rw [List.mem_append] at leftMember rightMember
              rcases leftMember with leftFalse | leftTrue
              · rcases QuotientFreeList.mem_map.mp leftFalse with
                  ⟨leftSource, leftSourceMember, leftEqual⟩
                subst left
                rcases rightMember with rightFalse | rightTrue
                · rcases QuotientFreeList.mem_map.mp rightFalse with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  exact ⟨prependFalse generator output,
                    List.mem_append_left _ (falseMap_mem outputMember),
                    outputEquation⟩
                · rcases QuotientFreeList.mem_map.mp rightTrue with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨prependTrue generator output,
                    List.mem_append_right _ (trueMap_mem outputMember), ?_⟩
                  change xor leftSource.vector
                    (xor generator rightSource.vector) =
                      xor generator output.vector
                  rw [← outputEquation, ← xor_assoc,
                    xor_comm leftSource.vector generator, xor_assoc]
              · rcases QuotientFreeList.mem_map.mp leftTrue with
                  ⟨leftSource, leftSourceMember, leftEqual⟩
                subst left
                rcases rightMember with rightFalse | rightTrue
                · rcases QuotientFreeList.mem_map.mp rightFalse with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨prependTrue generator output,
                    List.mem_append_right _ (trueMap_mem outputMember), ?_⟩
                  change xor (xor generator leftSource.vector)
                    rightSource.vector = xor generator output.vector
                  rw [← outputEquation, xor_assoc]
                · rcases QuotientFreeList.mem_map.mp rightTrue with
                    ⟨rightSource, rightSourceMember, rightEqual⟩
                  subst right
                  rcases previous.closed leftSource leftSourceMember
                    rightSource rightSourceMember with
                    ⟨output, outputMember, outputEquation⟩
                  refine ⟨prependFalse generator output,
                    List.mem_append_left _ (falseMap_mem outputMember), ?_⟩
                  change xor (xor generator leftSource.vector)
                    (xor generator rightSource.vector) = output.vector
                  rw [← outputEquation]
                  calc
                    xor (xor generator leftSource.vector)
                        (xor generator rightSource.vector) =
                      xor (xor (xor generator leftSource.vector) generator)
                        rightSource.vector :=
                          (xor_assoc (xor generator leftSource.vector)
                            generator rightSource.vector).symm
                    _ = xor (xor generator
                        (xor generator leftSource.vector))
                          rightSource.vector := by
                            rw [xor_comm
                              (xor generator leftSource.vector) generator]
                    _ = xor (xor (xor generator generator)
                        leftSource.vector) rightSource.vector :=
                      congrArg (fun vector : Vector width =>
                        xor vector rightSource.vector)
                        (xor_assoc generator generator
                          leftSource.vector).symm
                    _ = xor leftSource.vector rightSource.vector := by
                      rw [xor_self, zero_xor] }

end RFAP.FiniteBooleanSpan
