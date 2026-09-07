import CCL.Progressive.Transducer

/-!
# Limit-free progressive rational approximations

A transcendental computation in the constructive CCL layer must not first
manufacture a completed non-rational point.  `Approximation` instead records
only a sequence of displayed Gaussian-rational samples, a rational
squared-error allowance at each finite index, and a terminating refinement
operation which reaches any requested positive rational allowance.

The possibility predicate used below has an explicit natural-number witness:
`value` is one particular later finite sample.  It is a predicate, not a set
of all samples, and it does not assert that the samples have a limit.
-/

namespace CCL.ProgressiveApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Named := CCL.ProgressiveTransducer.Named

open RFAP.ConstructiveGaussian.Gaussian

/-- Entirely finite data sufficient to answer arbitrarily accurate rational
sample requests, without adjoining a completed value. -/
structure Approximation where
  sample : Nat → Gaussian
  radiusSq : Nat → Coordinate
  radiusSq_nonneg : ∀ index, 0 ≤ radiusSq index
  later_close : ∀ {earlier later : Nat}, earlier ≤ later →
    normSq (sample later - sample earlier) ≤ radiusSq earlier
  refineIndex : (current : Nat) → (target : Coordinate) →
    0 < target → Nat
  refineIndex_ge : ∀ (current : Nat) (target : Coordinate)
      (positive : 0 < target),
    current ≤ refineIndex current target positive
  refineIndex_accurate : ∀ (current : Nat) (target : Coordinate)
      (positive : 0 < target),
    radiusSq (refineIndex current target positive) < target
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  sample_bounded : ∀ index, normSq (sample index) ≤ centerBound

namespace Approximation

/-- A value is possible at `index` when a displayed finite later index
witnesses it. -/
def Possible (approximation : Approximation) (index : Nat)
    (value : Gaussian) : Prop :=
  ∃ later : Nat, index ≤ later ∧ value = approximation.sample later

theorem sample_possible (approximation : Approximation) (index : Nat) :
    approximation.Possible index (approximation.sample index) :=
  ⟨index, Nat.le_refl index, rfl⟩

theorem possible_persists (approximation : Approximation)
    {earlier later : Nat} (order : earlier ≤ later) {value : Gaussian}
    (possible : approximation.Possible later value) :
    approximation.Possible earlier value := by
  rcases possible with ⟨witnessIndex, laterLe, identity⟩
  exact ⟨witnessIndex, Nat.le_trans order laterLe, identity⟩

/-- Every explicitly witnessed later sample lies in the current finite ball. -/
theorem possible_inside (approximation : Approximation)
    {index : Nat} {value : Gaussian}
    (possible : approximation.Possible index value) :
    ({ center := approximation.sample index
       radiusSq := approximation.radiusSq index
       radiusSq_nonneg := approximation.radiusSq_nonneg index } : Ball).Contains
      value := by
  rcases possible with ⟨later, order, rfl⟩
  exact approximation.later_close order

/-- Forget only the sequence presentation, retaining its explicit finite-index
predicate as the sidecar semantics consumed by the ordinary CCL controller. -/
def toProcess (approximation : Approximation) : Process where
  State := Nat
  ball index :=
    { center := approximation.sample index
      radiusSq := approximation.radiusSq index
      radiusSq_nonneg := approximation.radiusSq_nonneg index }
  Possible := approximation.Possible
  witness index := ⟨approximation.sample index,
    approximation.sample_possible index⟩
  possible_inside := by
    intro index value possible
    exact approximation.possible_inside possible
  refine := approximation.refineIndex
  refine_persists := by
    intro current target positive value possible
    exact approximation.possible_persists
      (approximation.refineIndex_ge current target positive) possible
  accurate := approximation.refineIndex_accurate
  centerBound := approximation.centerBound
  centerBound_nonneg := approximation.centerBound_nonneg
  center_bounded := approximation.sample_bounded

@[simp] theorem toProcess_ball (approximation : Approximation) (index : Nat) :
    (approximation.toProcess.ball
      (show approximation.toProcess.State from index)).center =
        approximation.sample index ∧
      (approximation.toProcess.ball
        (show approximation.toProcess.State from index)).radiusSq =
        approximation.radiusSq index :=
  ⟨rfl, rfl⟩

@[simp] theorem toProcess_possible (approximation : Approximation)
    (index : Nat) (value : Gaussian) :
    approximation.toProcess.Possible
        (show approximation.toProcess.State from index) value ↔
      approximation.Possible index value := by
  rfl

/-- Start the unchanged productive raw CCL controller from the first finite
sample/error certificate. -/
def toNamed (approximation : Approximation) : Named :=
  { process := approximation.toProcess
    state := by
      change Nat
      exact 0 }

/-- Every limit-free progressive approximation produces exactly the requested
number of raw CCL bits while preserving its old prefix. -/
theorem output_productive (approximation : Approximation) (count : Nat) :
    approximation.toNamed.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          approximation.toNamed.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          approximation.toNamed.machine count).emitted.length = count :=
  approximation.toNamed.productive count

end Approximation

end CCL.ProgressiveApproximation
