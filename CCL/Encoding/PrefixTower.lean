import CCL.Encoding.Encoder
import CCL.Encoding.PrefixMinimax

/-!
# Finite approximation towers for exact CCL names

This module packages the elementary prefix clauses of the manuscript's
finite-name tower without introducing a completed stream or a collection of
all points in a cylinder.
-/

namespace CCL.PrefixTower

abbrev Word := List Bool
abbrev Frac := CCL.Integral.Frac
abbrev Gauge := CCL.PrefixMinimax.Gauge

/-- The first `count` bits of one displayed finite word. -/
def prefixAt (word : Word) (count : Nat) : Word := word.take count

/-- Every finite approximation is an ordinary list prefix. -/
theorem prefixAt_isPrefix (word : Word) (count : Nat) :
    (prefixAt word count).IsPrefix word :=
  List.take_prefix count word

/-- Consecutive finite approximations extend monotonically. -/
theorem prefixAt_successive (word : Word) (count : Nat) :
    (prefixAt word count).IsPrefix (prefixAt word (count + 1)) := by
  refine ⟨word[count]?.toList, ?_⟩
  exact List.take_add_one.symm

/-- The pure cylinder predicate is just finite-list prefixhood of the exact
finite encoder output. -/
def Cylinder (stem : Word) (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) : Prop :=
  stem.IsPrefix
    (CCL.Encoder.encode fraction numeratorNonzero)

/-- Every member of the canonical prefix tower satisfies its cylinder
predicate by construction. -/
theorem prefixAt_cylinder (fraction : Frac)
    (numeratorNonzero : fraction.num ≠ 0) (count : Nat) :
    Cylinder
      (prefixAt (CCL.Encoder.encode fraction numeratorNonzero)
        count)
      fraction numeratorNonzero :=
  List.take_prefix count
    (CCL.Encoder.encode fraction numeratorNonzero)

/-- Before the end of a finite word, the cylindrical gauge distance from its
current prefix to the complete tag is exactly the current gauge value. -/
theorem distance_prefixAt (gauge : Gauge) (word : Word) (count : Nat)
    (beforeEnd : count < word.length) :
    CCL.PrefixMinimax.distance gauge (prefixAt word count) word =
      gauge.value (prefixAt word count) := by
  have split :
      word = prefixAt word count ++
        word[count] :: word.drop (count + 1) := by
    calc
      word = word.take count ++ word.drop count :=
        (List.take_append_drop count word).symm
      _ = word.take count ++
          word[count] :: word.drop (count + 1) :=
        congrArg (fun suffix => word.take count ++ suffix)
          (List.drop_eq_getElem_cons beforeEnd)
  calc
    CCL.PrefixMinimax.distance gauge (prefixAt word count) word =
        CCL.PrefixMinimax.distance gauge (prefixAt word count)
          (prefixAt word count ++
            word[count] :: word.drop (count + 1)) :=
      congrArg
        (CCL.PrefixMinimax.distance gauge (prefixAt word count))
        split
    _ = gauge.value (prefixAt word count) :=
      CCL.PrefixMinimax.distance_prefix_child gauge
        (prefixAt word count) (word.drop (count + 1)) word[count]

end CCL.PrefixTower
