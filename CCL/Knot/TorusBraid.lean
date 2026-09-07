import CCL.Knot.ArtinRelations

/-!
# Finite torus braids

This file constructs the positive braid
`(σ₁ · … · σₚ₋₁)^q` as an executable finite word on `p`
strands.  It is the combinatorial braid predicted for the algebraic
singularity `z^p = w^q`.  The construction exposes exact crossing count,
writhe, and endpoint permutation iteration without invoking a completed
curve or a topological quotient.
-/

namespace CCL.Knot.TorusBraid

open CCL.Knot.FiniteBraid

/-! ## Positive bands -/

def positiveGenerator {strands : Nat} (index : Fin (strands - 1)) :
    Generator strands :=
  { index := index
    sign := .positive }

/-- The displayed band `σ₁…σₚ₋₁`, in traversal order. -/
def positiveBand (strands : Nat) : Word strands :=
  List.ofFn fun index : Fin (strands - 1) => positiveGenerator index

@[simp] theorem positiveBand_length (strands : Nat) :
    (positiveBand strands).length = strands - 1 := by
  simp only [positiveBand, List.length_ofFn]

theorem writhe_eq_length_of_positive {strands : Nat} :
    ∀ word : Word strands,
      (∀ generator ∈ word, generator.sign = .positive) →
      word.writhe = (word.length : Int)
  | [], _ => rfl
  | generator :: remaining, positive => by
      have headPositive : generator.sign = .positive :=
        positive generator (by simp only [List.mem_cons, true_or])
      have tailPositive : ∀ entry ∈ remaining, entry.sign = .positive := by
        intro entry member
        exact positive entry (by simp only [List.mem_cons, member, or_true])
      rw [CCL.Knot.FiniteBraid.Word.writhe_cons,
        writhe_eq_length_of_positive remaining tailPositive]
      simp only [Generator.weight, headPositive, CrossingSign.weight,
        List.length_cons, Int.natCast_add, Int.natCast_one]
      ring1

@[simp] theorem positiveBand_writhe (strands : Nat) :
    (positiveBand strands).writhe = (strands - 1 : Nat) := by
  rw [writhe_eq_length_of_positive]
  · simp only [positiveBand_length]
  · intro generator member
    rw [positiveBand, List.mem_ofFn] at member
    obtain ⟨index, equal⟩ := member
    rw [← equal]
    rfl

/-! ## Finite word powers -/

/-- Concatenate `word` with itself exactly `exponent` times. -/
def repeatWord {strands : Nat} (word : Word strands) : Nat → Word strands
  | 0 => []
  | exponent + 1 => repeatWord word exponent ++ word

@[simp] theorem repeatWord_zero {strands : Nat} (word : Word strands) :
    repeatWord word 0 = [] := rfl

@[simp] theorem repeatWord_succ {strands : Nat} (word : Word strands)
    (exponent : Nat) :
    repeatWord word (exponent + 1) = repeatWord word exponent ++ word := rfl

theorem repeatWord_add {strands : Nat} (word : Word strands)
    (first second : Nat) :
    repeatWord word (first + second) =
      repeatWord word first ++ repeatWord word second := by
  induction second with
  | zero => simp only [Nat.add_zero, repeatWord_zero, List.append_nil]
  | succ second inductionHypothesis =>
      rw [Nat.add_succ, repeatWord_succ, repeatWord_succ,
        inductionHypothesis, List.append_assoc]

@[simp] theorem repeatWord_length {strands : Nat} (word : Word strands) :
  ∀ exponent : Nat,
      (repeatWord word exponent).length = exponent * word.length
  | 0 => by simp only [repeatWord_zero, List.length_nil, zero_mul]
  | exponent + 1 => by
      rw [repeatWord_succ, List.length_append, repeatWord_length]
      simp only [Nat.add_mul, Nat.one_mul]

@[simp] theorem repeatWord_writhe {strands : Nat} (word : Word strands) :
    ∀ exponent : Nat,
      (repeatWord word exponent).writhe = (exponent : Int) * word.writhe
  | 0 => by simp only [repeatWord_zero, CCL.Knot.FiniteBraid.Word.writhe_nil,
      Int.ofNat_zero, zero_mul]
  | exponent + 1 => by
      rw [repeatWord_succ, CCL.Knot.FiniteBraid.Word.writhe_append,
        repeatWord_writhe]
      simp only [Int.natCast_add, Int.natCast_one]
      ring1

/-- Repeating a braid word iterates its explicit strand permutation. -/
theorem repeatWord_permutation {strands : Nat} (word : Word strands) :
    ∀ (exponent : Nat) (index : Fin strands),
      (repeatWord word exponent).permutation.forward index =
        CCL.FiniteMonodromy.FiniteBijection.iterateForward
          word.permutation exponent index
  | 0, _ => rfl
  | exponent + 1, index => by
      calc
        (repeatWord word (exponent + 1)).permutation.forward index =
            word.permutation.forward
              ((repeatWord word exponent).permutation.forward index) :=
          CCL.Knot.FiniteBraid.Word.permutation_append
            (repeatWord word exponent) word index
        _ = word.permutation.forward
            (CCL.FiniteMonodromy.FiniteBijection.iterateForward
              word.permutation exponent index) := by
          rw [repeatWord_permutation word exponent index]
        _ = CCL.FiniteMonodromy.FiniteBijection.iterateForward
            word.permutation (exponent + 1) index := rfl

/-! ## The algebraic torus-link model -/

/-- Positive integral exponents for the finite singularity model
`z^p = w^q`. -/
structure PowerSingularity where
  p : Nat
  q : Nat
  pPositive : 0 < p
  qPositive : 0 < q
deriving Repr

namespace PowerSingularity

/-- The braid `(σ₁…σₚ₋₁)^q` predicted by the singularity. -/
def braidWord (singularity : PowerSingularity) : Word singularity.p :=
  repeatWord (positiveBand singularity.p) singularity.q

def closure (singularity : PowerSingularity) : Closure :=
  { strands := singularity.p
    word := singularity.braidWord }

@[simp] theorem braidWord_length (singularity : PowerSingularity) :
    singularity.braidWord.length = singularity.q * (singularity.p - 1) := by
  simp only [braidWord, repeatWord_length, positiveBand_length]

@[simp] theorem braidWord_writhe (singularity : PowerSingularity) :
    singularity.braidWord.writhe =
      (singularity.q : Int) * (singularity.p - 1 : Nat) := by
  simp only [braidWord, repeatWord_writhe, positiveBand_writhe]

theorem closure_permutation (singularity : PowerSingularity)
    (index : Fin singularity.p) :
    singularity.closure.permutation.forward index =
      CCL.FiniteMonodromy.FiniteBijection.iterateForward
        (positiveBand singularity.p).permutation singularity.q index := by
  exact repeatWord_permutation (positiveBand singularity.p)
    singularity.q index

end PowerSingularity

end CCL.Knot.TorusBraid
