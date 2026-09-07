import FTA.CCLCompatibleSearch

/-!
# Explicit finite Gaussian-rational candidate grids

Lemma 10.4 needs a bounded finite list, not an open-ended enumeration.  For a
natural bound `B`, this module lists every rational whose normalized numerator
absolute value and positive denominator are at most `B`, then takes the finite
Cartesian square for Gaussian rationals.  Every Gaussian rational appears at
its coefficient-computed height, so the exact terminating-encoder verifier is
complete for any displayed height bound.
-/

namespace FTA
namespace CCLCompatibleCandidates

open CCL
open FTA.CCLCompatibleSearch

abbrev QI := CCL.GaussianRat

/-- All integers in the symmetric interval `[-B,B]`. -/
def integersUpTo (bound : ℕ) : List ℤ :=
  (List.range (bound + 1)).map Int.ofNat ++
    (List.range bound).map Int.negSucc

/-- All positive natural denominators at most `B`. -/
def denominatorsUpTo (bound : ℕ) : List ℕ :=
  (List.range bound).map Nat.succ

/-- Finite (possibly duplicate) list of all normalized-height-bounded
rationals.  Duplicates are harmless and keep the evaluator transparent. -/
def rationalsUpTo (bound : ℕ) : List ℚ :=
  (integersUpTo bound).flatMap fun numerator : ℤ =>
    (denominatorsUpTo bound).map fun denominator : ℕ =>
      (numerator : ℚ) / (denominator : ℚ)

def rationalHeight (value : ℚ) : ℕ :=
  max value.num.natAbs value.den

theorem integer_mem_integersUpTo {value : ℤ} {bound : ℕ}
    (height : value.natAbs ≤ bound) : value ∈ integersUpTo bound := by
  cases value with
  | ofNat value =>
      rw [integersUpTo, List.mem_append]
      left
      rw [List.mem_map]
      refine ⟨value, List.mem_range.mpr ?_, rfl⟩
      simpa using Nat.lt_succ_of_le height
  | negSucc value =>
      rw [integersUpTo, List.mem_append]
      right
      rw [List.mem_map]
      refine ⟨value, List.mem_range.mpr ?_, rfl⟩
      simpa using height

theorem denominator_mem_denominatorsUpTo {value bound : ℕ}
    (positive : 0 < value) (upper : value ≤ bound) :
    value ∈ denominatorsUpTo bound := by
  rw [denominatorsUpTo, List.mem_map]
  refine ⟨value - 1, List.mem_range.mpr (by omega), by omega⟩

theorem mem_rationalsUpTo_of_height_le (value : ℚ) {bound : ℕ}
    (height : rationalHeight value ≤ bound) :
    value ∈ rationalsUpTo bound := by
  have numeratorHeight : value.num.natAbs ≤ bound :=
    (le_max_left value.num.natAbs value.den).trans height
  have denominatorHeight : value.den ≤ bound :=
    (le_max_right value.num.natAbs value.den).trans height
  have denominatorPositive : 0 < value.den := Nat.pos_of_ne_zero value.den_nz
  unfold rationalsUpTo
  apply List.mem_flatMap.mpr
  refine ⟨value.num, integer_mem_integersUpTo numeratorHeight, ?_⟩
  apply List.mem_map.mpr
  refine ⟨value.den,
    denominator_mem_denominatorsUpTo denominatorPositive denominatorHeight, ?_⟩
  exact value.num_div_den

theorem mem_rationalsUpTo_height (value : ℚ) :
    value ∈ rationalsUpTo (rationalHeight value) :=
  mem_rationalsUpTo_of_height_le value le_rfl

/-- Explicit finite Cartesian square of the one-dimensional rational grid. -/
def gaussianRationalsUpTo (bound : ℕ) : List QI :=
  (rationalsUpTo bound).flatMap fun re =>
    (rationalsUpTo bound).map fun im => ⟨re, im⟩

def gaussianHeight (value : QI) : ℕ :=
  max (rationalHeight value.re) (rationalHeight value.im)

theorem mem_gaussianRationalsUpTo_of_height_le
    (value : QI) {bound : ℕ} (height : gaussianHeight value ≤ bound) :
    value ∈ gaussianRationalsUpTo bound := by
  have realHeight : rationalHeight value.re ≤ bound :=
    (le_max_left _ _).trans height
  have imagHeight : rationalHeight value.im ≤ bound :=
    (le_max_right _ _).trans height
  rw [gaussianRationalsUpTo, List.mem_flatMap]
  refine ⟨value.re, mem_rationalsUpTo_of_height_le value.re realHeight, ?_⟩
  rw [List.mem_map]
  exact ⟨value.im, mem_rationalsUpTo_of_height_le value.im imagHeight,
    GaussianRat.ext rfl rfl⟩

theorem mem_gaussianRationalsUpTo_height (value : QI) :
    value ∈ gaussianRationalsUpTo (gaussianHeight value) :=
  mem_gaussianRationalsUpTo_of_height_le value le_rfl

/-- Fully executable bounded grid followed by the actual terminating encoder
prefix verifier. -/
def firstGeneratedCompatible?
    (word : Prefix.Word) (box : RatBox) (bound : ℕ) : Option QI :=
  firstCompatible? word box (gaussianRationalsUpTo bound)

/-- Bounded generated search whose result is guaranteed to remain in affine
raw-parser semantics rather than completing an unrelated rational word. -/
def firstGeneratedStrictCompatible?
    (word : Prefix.Word) (box : RatBox) (bound : ℕ) : Option QI :=
  firstStrictCompatible? word box (gaussianRationalsUpTo bound)

theorem firstGeneratedCompatible?_some_certifies
    {word : Prefix.Word} {box : RatBox} {bound : ℕ} {q : QI}
    (search : firstGeneratedCompatible? word box bound = some q) :
    box.Contains q ∧
      ∃ nonzero : q ≠ 0, word <+: RationalEncoder.encode q nonzero := by
  exact firstCompatible?_some_certifies search

theorem firstGeneratedStrictCompatible?_some_certifies
    {word : Prefix.Word} {box : RatBox} {bound : ℕ} {q : QI}
    (search : firstGeneratedStrictCompatible? word box bound = some q) :
    box.Contains q ∧ q ≠ 0 ∧
      RawParserSemantics.Represented word q := by
  exact firstStrictCompatible?_some_certifies search

/-- Absolute bounded completeness: any accepted point under the displayed
height bound forces the finite generated search to succeed. -/
theorem firstGeneratedCompatible?_isSome_of_height_le
    {word : Prefix.Word} {box : RatBox} {bound : ℕ} {q : QI}
    (height : gaussianHeight q ≤ bound) (accepted : Accepts word box q) :
    (firstGeneratedCompatible? word box bound).isSome := by
  exact firstCompatible?_isSome_of_mem
    (mem_gaussianRationalsUpTo_of_height_le q height) accepted

/-- In particular, the coefficient-computed height of a supplied geometric
witness is an explicit sufficient finite search bound. -/
theorem firstGeneratedCompatible?_isSome_at_height
    {word : Prefix.Word} {box : RatBox} {q : QI}
    (accepted : Accepts word box q) :
    (firstGeneratedCompatible? word box (gaussianHeight q)).isSome :=
  firstGeneratedCompatible?_isSome_of_height_le le_rfl accepted

/-- The affine parser/encoder bridge turns any nonzero represented point in
the box into an explicit sufficient bound for the generated finite search. -/
theorem firstGeneratedCompatible?_isSome_of_represented
    {word : Prefix.Word} {box : RatBox} {q : QI}
    (inside : box.Contains q) (nonzero : q ≠ 0)
    (represented : RawParserSemantics.Represented word q) :
    (firstGeneratedCompatible? word box (gaussianHeight q)).isSome := by
  apply firstGeneratedCompatible?_isSome_at_height
  refine ⟨inside, ?_⟩
  apply (compatible_iff_exists_encoder_prefix word q).2
  exact ⟨nonzero,
    ((RationalEncoder.represented_iff_strictPrefix_encode
      q nonzero word).1 represented).1⟩

/-- A supplied nonzero affine witness appears at its explicit Gaussian height,
so the strict generated search succeeds without admitting complete-word
false terminals. -/
theorem firstGeneratedStrictCompatible?_isSome_of_represented
    {word : Prefix.Word} {box : RatBox} {q : QI}
    (inside : box.Contains q) (nonzero : q ≠ 0)
    (represented : RawParserSemantics.Represented word q) :
    (firstGeneratedStrictCompatible? word box
      (gaussianHeight q)).isSome := by
  apply firstStrictCompatible?_isSome_of_mem
    (mem_gaussianRationalsUpTo_height q)
  exact ⟨inside,
    (strictCompatible_iff_nonzero_represented word q).2
      ⟨nonzero, represented⟩⟩

/-- Proof-bearing output of the strict bounded search. -/
structure RepresentedOutcome (word : Prefix.Word) (box : RatBox) where
  point : QI
  inside : box.Contains point
  nonzero : point ≠ 0
  semantics : RawParserSemantics.Represented word point

/-- Extract a represented sample from any successful strict generated
search. -/
def representedOutcomeOfIsSome
    (word : Prefix.Word) (box : RatBox) (bound : ℕ)
    (success : (firstGeneratedStrictCompatible? word box bound).isSome) :
    RepresentedOutcome word box := by
  cases search : firstGeneratedStrictCompatible? word box bound with
  | none => simp [search] at success
  | some point =>
      have certified :=
        firstGeneratedStrictCompatible?_some_certifies search
      exact
        { point := point
          inside := certified.1
          nonzero := certified.2.1
          semantics := certified.2.2 }

/-- Lemma 10.4's nonterminal output at the explicit height of a supplied
affine witness. -/
def searchRepresentedAtHeight
    (word : Prefix.Word) (box : RatBox) (q : QI)
    (inside : box.Contains q) (nonzero : q ≠ 0)
    (represented : RawParserSemantics.Represented word q) :
    RepresentedOutcome word box :=
  representedOutcomeOfIsSome word box (gaussianHeight q)
    (firstGeneratedStrictCompatible?_isSome_of_represented
      inside nonzero represented)

/-- Proof-bearing result of the bounded compatible-sample search.  The only
accepted word without affine raw-parser semantics is the complete encoder
word, which is returned as the exact projective terminal case. -/
inductive SearchOutcome (word : Prefix.Word) (box : RatBox) where
  | represented (point : QI) (inside : box.Contains point)
      (nonzero : point ≠ 0)
      (semantics : RawParserSemantics.Represented word point)
  | terminal (point : QI) (inside : box.Contains point)
      (nonzero : point ≠ 0)
      (complete : word = RationalEncoder.encode point nonzero)

/-- Extract the certified semantic/terminal dichotomy from any successful
bounded generated search. -/
def searchOutcomeOfIsSome
    (word : Prefix.Word) (box : RatBox) (bound : ℕ)
    (success : (firstGeneratedCompatible? word box bound).isSome) :
    SearchOutcome word box := by
  cases search : firstGeneratedCompatible? word box bound with
  | none => simp [search] at success
  | some point =>
      have accepted : Accepts word box point :=
        firstCompatible?_some_accepts (by
          simpa [firstGeneratedCompatible?] using search)
      have inside := accepted.1
      have nonzero : point ≠ 0 := accepted.2.nonzero
      have isPrefix : word <+: RationalEncoder.encode point nonzero :=
        (compatible_iff_exists_encoder_prefix word point).mp
          accepted.2 |>.choose_spec
      by_cases complete : word = RationalEncoder.encode point nonzero
      · exact .terminal point inside nonzero complete
      · exact .represented point inside nonzero
          ((RationalEncoder.represented_iff_strictPrefix_encode
            point nonzero word).2 ⟨isPrefix, complete⟩)

/-- Lemma 10.4's final executable verification step at the explicit height
of a supplied semantic witness. -/
def searchOutcomeAtRepresentedHeight
    (word : Prefix.Word) (box : RatBox) (q : QI)
    (inside : box.Contains q) (nonzero : q ≠ 0)
    (represented : RawParserSemantics.Represented word q) :
    SearchOutcome word box :=
  searchOutcomeOfIsSome word box (gaussianHeight q)
    (firstGeneratedCompatible?_isSome_of_represented inside nonzero represented)

theorem firstGeneratedCompatible?_none_iff
    (word : Prefix.Word) (box : RatBox) (bound : ℕ) :
    firstGeneratedCompatible? word box bound = none ↔
      ∀ q ∈ gaussianRationalsUpTo bound, ¬Accepts word box q :=
  firstCompatible?_none_iff word box (gaussianRationalsUpTo bound)

end CCLCompatibleCandidates
end FTA
