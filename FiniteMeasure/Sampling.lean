import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Convolution
import FiniteMeasure.Moments

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace FiniteMeasure

/-- Exact rational sum of a displayed observable over one finite sample
list. -/
def sampleSum {α : Type} (value : α → Coordinate) :
    List α → Coordinate
  | [] => 0
  | item :: remaining => value item + sampleSum value remaining

namespace Distribution

/-- A supplied positive rational sample-count cast is nonzero. -/
theorem positiveSampleCount_ne_zero (count : Nat)
    (positive : 0 < (count : Coordinate)) :
    (count : Coordinate) ≠ 0 :=
  positive.ne'

/-- Explicit field cancellation for a supplied positive sample count. -/
theorem positiveSampleCount_mul_inv (count : Nat)
    (positive : 0 < (count : Coordinate)) :
    (count : Coordinate) * (count : Coordinate)⁻¹ = 1 :=
  RFAP.ConstructiveFraction.mul_inv_cancel _
    (positiveSampleCount_ne_zero count positive)

theorem positiveSampleCount_inv_mul_value (count : Nat)
    (positive : 0 < (count : Coordinate)) (value : Coordinate) :
    (count : Coordinate)⁻¹ * ((count : Coordinate) * value) = value := by
  calc
    (count : Coordinate)⁻¹ * ((count : Coordinate) * value) =
        ((count : Coordinate)⁻¹ * (count : Coordinate)) * value :=
      RFAP.ConstructiveFraction.mul_assoc _ _ _ |>.symm
    _ = ((count : Coordinate) * (count : Coordinate)⁻¹) * value := by
      rw [RFAP.ConstructiveFraction.mul_comm
        (count : Coordinate)⁻¹ (count : Coordinate)]
    _ = 1 * value := by rw [positiveSampleCount_mul_inv count positive]
    _ = value := RFAP.ConstructiveFraction.one_mul value

theorem positiveSampleCount_inv_sq_mul_value (count : Nat)
    (positive : 0 < (count : Coordinate)) (value : Coordinate) :
    (count : Coordinate)⁻¹ ^ 2 * ((count : Coordinate) * value) =
      value / (count : Coordinate) := by
  rw [pow_two, RFAP.ConstructiveFraction.mul_pair_swap]
  have inverseTimesCount :
      (count : Coordinate)⁻¹ * (count : Coordinate) = 1 := by
    rw [RFAP.ConstructiveFraction.mul_comm
      (count : Coordinate)⁻¹ (count : Coordinate),
      positiveSampleCount_mul_inv count positive]
  rw [inverseTimesCount, RFAP.ConstructiveFraction.one_mul,
    RFAP.ConstructiveFraction.mul_comm (count : Coordinate)⁻¹ value,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]

/-- Distribution of exactly the displayed finite number of independent
draws, represented as an explicit finite table of lists. -/
def iidSamples {α : Type} (source : Distribution α) :
    Nat → Distribution (List α)
  | 0 => Distribution.pure []
  | count + 1 =>
      (source.product (iidSamples source count)).map fun pair =>
        pair.1 :: pair.2

theorem iidSamples_zero {α : Type} (source : Distribution α) :
    iidSamples source 0 = Distribution.pure [] := rfl

theorem iidSamples_succ {α : Type} (source : Distribution α)
    (count : Nat) :
    iidSamples source (count + 1) =
      (source.product (iidSamples source count)).map fun pair =>
        pair.1 :: pair.2 := rfl

/-- Exact table-size cost of a displayed finite sample count. -/
theorem iidSamples_atoms_length {α : Type} (source : Distribution α) :
    ∀ count : Nat,
      (iidSamples source count).atoms.length = source.atoms.length ^ count
  | 0 => rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_atoms_length,
        Distribution.product_atoms_length,
        iidSamples_atoms_length source count, pow_succ]
      exact Nat.mul_comm _ _

/-- A displayed sample list is supported row by row by the source atom
table.  This recursive predicate retains explicit witnesses and does not form
an ambient support set. -/
def SampleSupportedBy {α : Type} (source : Distribution α) : List α → Prop
  | [] => True
  | item :: remaining =>
      (∃ atom, atom ∈ source.atoms ∧ atom.item = item) ∧
        SampleSupportedBy source remaining

/-- A payload occurring in a source-supported sample comes from an explicit
source atom. -/
theorem sampleSupportedBy_source_of_mem {α : Type}
    (source : Distribution α) (item : α) :
    ∀ {samples : List α}, SampleSupportedBy source samples →
      item ∈ samples →
        ∃ atom, atom ∈ source.atoms ∧ atom.item = item
  | [], supported, member => (List.not_mem_nil member).elim
  | head :: remaining, supported, member => by
      rcases supported with ⟨headSupported, tailSupported⟩
      rcases List.mem_cons.mp member with equal | tailMember
      · rcases headSupported with ⟨atom, member, atomEqual⟩
        exact ⟨atom, member, atomEqual.trans equal.symm⟩
      · exact source.sampleSupportedBy_source_of_mem item
          tailSupported tailMember

/-- Every payload row of the explicit finite iid table is supported by the
source atom table, with witnesses obtained by finite product recursion. -/
theorem iidSamples_atom_sampleSupportedBy {α : Type}
    (source : Distribution α) : ∀ (count : Nat)
    (candidate : Weighted (List α)),
      candidate ∈ (source.iidSamples count).atoms →
        SampleSupportedBy source candidate.item
  | 0, candidate, member => by
      rw [iidSamples_zero] at member
      simp only [pure, List.mem_cons, List.not_mem_nil, or_false] at member
      have payloadEqual :=
        congrArg (fun atom : Weighted (List α) => atom.item) member
      rw [payloadEqual]
      trivial
  | count + 1, candidate, member => by
      rw [iidSamples_succ] at member
      rcases (source.product (source.iidSamples count)).mem_map_atoms_source
          (fun pair => pair.1 :: pair.2) candidate member with
        ⟨pairAtom, pairMember, mappedEqual⟩
      rcases source.mem_product_atoms_sources (source.iidSamples count)
          pairAtom pairMember with
        ⟨headAtom, headMember, tailAtom, tailMember, pairEqual⟩
      rw [← mappedEqual, ← pairEqual]
      exact ⟨⟨headAtom, headMember, rfl⟩,
        source.iidSamples_atom_sampleSupportedBy count tailAtom tailMember⟩

/-- Every payload produced by the explicit iid table has exactly the
requested finite sample length, expressed as an exact probability-one
invariant. -/
theorem iidSamples_probability_sampleLength_eq {α : Type}
    (source : Distribution α) : ∀ count : Nat,
    (iidSamples source count).probability
      (fun sample => decide (sample.length = count)) = 1
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_probability]
      rfl
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_probability]
      calc
        (source.product (iidSamples source count)).probability
              (fun pair : α × List α =>
                decide ((pair.1 :: pair.2).length = count + 1)) =
            (source.product (iidSamples source count)).probability
              (fun pair => (fun _ : α => true) pair.1 &&
                decide (pair.2.length = count)) :=
          (source.product (iidSamples source count)).probability_congr _ _
            (fun pair => by
              simp only [List.length_cons, Nat.add_right_cancel_iff,
                Bool.true_and])
        (source.product (iidSamples source count)).probability
              (fun pair => (fun _ : α => true) pair.1 &&
                decide (pair.2.length = count)) =
            source.probability (fun _ : α => true) *
              (iidSamples source count).probability
                (fun sample => decide (sample.length = count)) :=
          source.product_probability_rectangle (iidSamples source count)
            (fun _ => true) (fun sample => decide (sample.length = count))
        _ = 1 := by
          rw [source.probability_true,
            iidSamples_probability_sampleLength_eq source count, one_mul]

theorem pure_variance {α : Type} (item : α)
    (value : α → Coordinate) :
    (Distribution.pure item).variance value = 0 := by
  rw [(Distribution.pure item).variance_eq_secondMoment_sub_sq,
    Distribution.pure_expectation, Distribution.pure_expectation]
  ring1

/-- A finite sample sum has sample count times the source expectation. -/
theorem iidSamples_expectation_sampleSum {α : Type}
    (source : Distribution α) (value : α → Coordinate) :
    ∀ count : Nat,
      (iidSamples source count).expectation (sampleSum value) =
        (count : Coordinate) * source.expectation value
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_expectation]
      simp only [sampleSum, Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_expectation]
      change
        (source.product (iidSamples source count)).expectation
            (fun pair => value pair.1 + sampleSum value pair.2) =
          ((count + 1 : Nat) : Coordinate) * source.expectation value
      rw [(source.product (iidSamples source count)).expectation_add,
        source.product_expectation_left,
        source.product_expectation_right,
        iidSamples_expectation_sampleSum source value count,
        Nat.cast_add, Nat.cast_one]
      ring1

/-- A finite independent sample sum has sample count times the source
variance. -/
theorem iidSamples_variance_sampleSum {α : Type}
    (source : Distribution α) (value : α → Coordinate) :
    ∀ count : Nat,
      (iidSamples source count).variance (sampleSum value) =
        (count : Coordinate) * source.variance value
  | 0 => by
      rw [iidSamples_zero, Distribution.pure_variance]
      simp only [Nat.cast_zero, zero_mul]
  | count + 1 => by
      rw [iidSamples_succ, Distribution.map_variance]
      change
        (source.product (iidSamples source count)).variance
            (fun pair => value pair.1 + sampleSum value pair.2) =
          ((count + 1 : Nat) : Coordinate) * source.variance value
      rw [source.product_variance_add_coordinates,
        iidSamples_variance_sampleSum source value count,
        Nat.cast_add, Nat.cast_one]
      ring1

/-- Rational mean of one supplied finite sample list.  At count zero this
total function evaluates to zero; the statistical theorems carry explicit
positive-count hypotheses. -/
def sampleMean {α : Type} (count : Nat) (value : α → Coordinate)
    (sample : List α) : Coordinate :=
  ((count : Coordinate))⁻¹ * sampleSum value sample

/-- A positive-count finite sample mean is unbiased exactly. -/
theorem iidSamples_expectation_sampleMean {α : Type}
    (source : Distribution α) (value : α → Coordinate)
    (count : Nat) (positive : 0 < (count : Coordinate)) :
    (iidSamples source count).expectation (sampleMean count value) =
      source.expectation value := by
  unfold sampleMean
  rw [source.iidSamples count |>.expectation_scale,
    iidSamples_expectation_sampleSum]
  exact positiveSampleCount_inv_mul_value count positive
    (source.expectation value)

/-- Variance of a positive-count finite sample mean is exactly source
variance divided by the displayed count. -/
theorem iidSamples_variance_sampleMean {α : Type}
    (source : Distribution α) (value : α → Coordinate)
    (count : Nat) (positive : 0 < (count : Coordinate)) :
    (iidSamples source count).variance (sampleMean count value) =
      source.variance value / (count : Coordinate) := by
  unfold sampleMean
  rw [(iidSamples source count).variance_scale,
    iidSamples_variance_sampleSum]
  exact positiveSampleCount_inv_sq_mul_value count positive
    (source.variance value)

/-! ## Finite event frequencies -/

/-- Rational frequency of an executable event in one displayed finite sample
list. -/
def eventFrequency {α : Type} (count : Nat) (event : α → Bool) :
    List α → Coordinate :=
  sampleMean count (indicator event)

/-- A positive-count finite event frequency is exactly unbiased for the
source event probability. -/
theorem iidSamples_expectation_eventFrequency {α : Type}
    (source : Distribution α) (event : α → Bool)
    (count : Nat) (positive : 0 < (count : Coordinate)) :
    (iidSamples source count).expectation (eventFrequency count event) =
      source.probability event := by
  unfold eventFrequency
  rw [source.iidSamples_expectation_sampleMean
    (indicator event) count positive, source.expectation_indicator]

/-- Exact Bernoulli variance divided by the displayed positive finite sample
count. -/
theorem iidSamples_variance_eventFrequency {α : Type}
    (source : Distribution α) (event : α → Bool)
    (count : Nat) (positive : 0 < (count : Coordinate)) :
    (iidSamples source count).variance (eventFrequency count event) =
      (source.probability event * (1 - source.probability event)) /
        (count : Coordinate) := by
  unfold eventFrequency
  rw [source.iidSamples_variance_sampleMean
    (indicator event) count positive, source.variance_indicator]

/-- Executable squared-deviation event for a finite sample mean. -/
def sampleMeanDeviation {α : Type} (source : Distribution α)
    (count : Nat) (value : α → Coordinate) (threshold : Coordinate) :
    List α → Bool :=
  fun sample => decide
    (threshold ^ 2 ≤
      (sampleMean count value sample - source.expectation value) ^ 2)

/-- One-shot finite Chebyshev estimate for a displayed positive sample
count.  The reciprocal-count improvement is an exact rational expression. -/
theorem iidSamples_sampleMean_chebyshev {α : Type}
    (source : Distribution α) (value : α → Coordinate)
    (count : Nat) (countPositive : 0 < (count : Coordinate))
    (threshold : Coordinate) (thresholdPositive : 0 < threshold) :
    (iidSamples source count).probability
        (sampleMeanDeviation source count value threshold) ≤
      (source.variance value / (count : Coordinate)) / threshold ^ 2 := by
  have estimate := (iidSamples source count).chebyshev_bound
    (sampleMeanDeviation source count value threshold)
    (sampleMean count value) threshold thresholdPositive (by
      intro atom member selected
      rw [source.iidSamples_expectation_sampleMean value count countPositive]
      exact of_decide_eq_true selected)
  rw [source.iidSamples_variance_sampleMean value count countPositive]
    at estimate
  exact estimate

end Distribution

end FiniteMeasure
