import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.EncodedPrefix
import CCL.Measure.ChordalProbe
import FiniteMeasure.DistributionEquivalence

/-!
# Root-free L2 stability for actual finite CCL encoder tables

This module applies squared-probe prefix stability directly to the block lists
and projective realization certificates computed by `encodeBlocks`.  The
comparison target is the original affine Gaussian fraction, connected to the
computed homogeneous witness by the encoder's explicit reconstruction proof.
-/

namespace CCL.FiniteMeasure

/-- Every squared-sensitive projective probe takes exactly the same value on
the encoder's computed homogeneous point and on the reconstructed original
affine Gaussian fraction. -/
theorem encodedSquaredSensitiveProbe_eq_value
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    probe (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point =
      probe (CCL.Proj.affine fraction.value) := by
  let encoding := CCL.Encoder.encodeBlocks fraction numeratorNonzero
  exact squaredSensitive_probe_eq_of_projectiveEquivalent probe factor
    sensitive encoding.realizes.valid
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate fraction.value)
    encoding.reconstruct

/-- Consequently an actual finite encoder table has exactly the same probe
expectation at its computed points as at the original affine inputs. -/
theorem encodedSquaredSensitiveProbe_expectation_eq_values {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.expectation (fun item =>
        probe (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.expectation (fun item =>
        probe (CCL.Proj.affine (fraction item).value)) := by
  exact distribution.expectation_congr _ _ (fun item =>
    encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)

/-- The probe pushforward law of the encoder's own computed points is
observationally identical to the probe pushforward law of the original
affine inputs.  Thus every executable probe event and every rational
observable of probe values agrees exactly. -/
theorem encodedSquaredSensitiveProbeLaw_evaluationEquivalent {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    _root_.FiniteMeasure.Distribution.EvaluationEquivalent
      (distribution.map fun item =>
        probe (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
      (distribution.map fun item =>
        probe (CCL.Proj.affine (fraction item).value)) := by
  have lawsEqual := distribution.map_congr
    (fun item => probe (CCL.Encoder.encodeBlocks
      (fraction item) (numeratorNonzero item)).point)
    (fun item => probe (CCL.Proj.affine (fraction item).value))
    (fun item => encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)
  rw [lawsEqual]
  exact _root_.FiniteMeasure.Distribution.EvaluationEquivalent.refl _

/-- Every executable Boolean event of an encoded squared-sensitive probe has
exactly the same probability as the corresponding event of the reconstructed
affine input. -/
theorem encodedSquaredSensitiveProbe_eventProbability_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor)
    (event : Coordinate → Bool) :
    distribution.probability (fun item => event (probe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.probability (fun item => event
        (probe (CCL.Proj.affine (fraction item).value))) := by
  calc
    distribution.probability (fun item => event (probe
          (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point)) =
        (distribution.map fun item => probe
          (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point).probability event :=
      (distribution.map_probability _ event).symm
    _ = (distribution.map fun item =>
          probe (CCL.Proj.affine (fraction item).value)).probability event :=
      (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
        fraction numeratorNonzero probe factor sensitive).probability_eq event
    _ = distribution.probability (fun item => event
          (probe (CCL.Proj.affine (fraction item).value))) :=
      distribution.map_probability _ event

/-- Every rational post-observable of the encoded probe likewise has exactly
the affine-input expectation.  This includes all displayed finite moments and
rational loss functions. -/
theorem encodedSquaredSensitiveProbe_observableExpectation_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor)
    (observable : Coordinate → Coordinate) :
    distribution.expectation (fun item => observable (probe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.expectation (fun item => observable
        (probe (CCL.Proj.affine (fraction item).value))) := by
  calc
    distribution.expectation (fun item => observable (probe
          (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point)) =
        (distribution.map fun item => probe
          (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point).expectation
              observable :=
      (distribution.map_expectation _ observable).symm
    _ = (distribution.map fun item =>
          probe (CCL.Proj.affine (fraction item).value)).expectation
            observable :=
      (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
        fraction numeratorNonzero probe factor sensitive).expectation_eq
          observable
    _ = distribution.expectation (fun item => observable
          (probe (CCL.Proj.affine (fraction item).value))) :=
      distribution.map_expectation _ observable

/-- For a finite table of nonzero Gaussian fractions, every explicitly
supplied family of points realizing the emitted block lists is close in exact
powered L2 to the original affine inputs. -/
theorem encodedSquaredProbe_poweredL2Distance_values_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.poweredL2Distance
        (fun item => probe (points item))
        (fun item => probe (CCL.Proj.affine (fraction item).value)) ≤
      distribution.expectation fun item =>
        factor * cylinderSpread
          (CCL.Encoder.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) -
        probe (CCL.Proj.affine (fraction item).value)) ^ 2) ≤
    distribution.expectation fun item =>
      factor * cylinderSpread
        (CCL.Encoder.encodeBlocks (fraction item)
          (numeratorNonzero item)).blocks
  apply distribution.expectation_mono
  intro atom member
  let encoding := CCL.Encoder.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (CCL.Proj.affine (fraction atom.item).value) :=
    encodedSquaredSensitiveProbe_eq_value (fraction atom.item)
      (numeratorNonzero atom.item) probe factor sensitive
  rw [← probeEqual, ← _root_.FiniteMeasure.rationalSeparation_sq]
  exact projectiveRealized_probe_separation_sq_le
    (pointsRealize atom member) encoding.realizes probe factor
      factorNonnegative sensitive

/-- Meeting the computed finite block request makes every displayed actual
encoder realization strictly probe-close to its original affine Gaussian
input. -/
theorem encodedSquaredProbe_separation_lt_requested_on_atom {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (atom : _root_.FiniteMeasure.Weighted index)
    (member : atom ∈ distribution.atoms) :
    _root_.FiniteMeasure.rationalSeparation
        (probe (points atom.item))
        (probe (CCL.Proj.affine (fraction atom.item).value)) < epsilon := by
  let encoding := CCL.Encoder.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (CCL.Proj.affine (fraction atom.item).value) :=
    encodedSquaredSensitiveProbe_eq_value (fraction atom.item)
      (numeratorNonzero atom.item) probe factor sensitive
  rw [← probeEqual]
  exact projectiveRealizedSquaredProbe_separation_lt_of_requested
    (pointsRealize atom member) encoding.realizes probe factor factorPositive
    sensitive epsilon epsilonPositive (enough atom member)

/-- The finite request therefore makes the actual encoded-versus-affine
probe error event at the requested tolerance have exactly zero probability.
This is a zero-failure finite convergence-in-probability certificate. -/
theorem encodedSquaredProbe_separationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
      (_root_.FiniteMeasure.separationAtLeast epsilon
        (fun item => probe (points item))
        (fun item =>
          probe (CCL.Proj.affine (fraction item).value))) = 0 := by
  calc
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast epsilon
          (fun item => probe (points item))
          (fun item =>
            probe (CCL.Proj.affine (fraction item).value))) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      unfold _root_.FiniteMeasure.separationAtLeast
      apply decide_eq_false_iff_not.mpr
      exact not_le_of_gt
        (encodedSquaredProbe_separation_lt_requested_on_atom distribution
          fraction numeratorNonzero probe factor factorPositive sensitive
          epsilon epsilonPositive enough points pointsRealize atom member)
    _ = 0 := distribution.probability_false

/-- Consequently, squared separation between the finite expectation of any
compatible realization family and the exact affine-input expectation is
bounded by the expected emitted CCL cylinder budget. -/
theorem encodedSquaredProbe_expectation_separation_sq_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item =>
          probe (CCL.Proj.affine (fraction item).value)) ^ 2 ≤
      distribution.expectation fun item =>
        factor * cylinderSpread
          (CCL.Encoder.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun item => probe (points item))
    (fun item => probe (CCL.Proj.affine (fraction item).value))).trans
      (encodedSquaredProbe_poweredL2Distance_values_le distribution fraction
        numeratorNonzero probe factor factorNonnegative sensitive points
        pointsRealize)

private theorem half_sq_lt_sq {epsilon : Coordinate}
    (positive : 0 < epsilon) : epsilon ^ 2 / 2 < epsilon ^ 2 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  have squarePositive : 0 < epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  calc
    epsilon ^ 2 = epsilon ^ 2 * 1 := by ring1
    _ < epsilon ^ 2 * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        squarePositive (by decide)

/-- A finite block-count check on every concrete encoder output makes the
compatible-family expectation strictly closer than a supplied positive
rational tolerance to the exact affine-input expectation. -/
theorem encodedSquaredProbe_expectation_separation_lt_requested {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item =>
          probe (CCL.Proj.affine (fraction item).value)) < epsilon := by
  have poweredL2Le := encodedSquaredProbe_poweredL2Distance_values_le
    distribution fraction numeratorNonzero probe factor factorPositive.le
    sensitive points pointsRealize
  have budgetLe : distribution.expectation (fun item =>
        factor * cylinderSpread
          (CCL.Encoder.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * cylinderSpread
              (CCL.Encoder.encodeBlocks (fraction item)
                (numeratorNonzero item)).blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have poweredL2Small := poweredL2Le.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact distribution.expectation_separation_lt_of_poweredL2Distance_lt_sq
    (fun item => probe (points item))
    (fun item => probe (CCL.Proj.affine (fraction item).value))
    epsilon epsilonPositive poweredL2Small

/-! ## Concrete nonconstant chordal-observation specializations -/

/-- The encoder's own computed point has exactly the original affine
fraction's distance-to-`omega` probe value. -/
theorem encodedChordalOmegaProbe_eq_value
    (fraction : CCL.Encoder.Frac) (numeratorNonzero : fraction.num ≠ 0) :
    chordalOmegaProbe
        (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point =
      chordalOmegaProbe (CCL.Proj.affine fraction.value) :=
  encodedSquaredSensitiveProbe_eq_value fraction numeratorNonzero
    chordalOmegaProbe 2 chordalOmegaProbe_squaredSensitive

/-- Exact law identity between the encoder's own chordal-`omega` probe values
and the original affine-input probe values. -/
theorem encodedChordalOmegaProbeLaw_evaluationEquivalent {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    _root_.FiniteMeasure.Distribution.EvaluationEquivalent
      (distribution.map fun item => chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
      (distribution.map fun item => chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value)) :=
  encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution fraction
    numeratorNonzero chordalOmegaProbe 2 chordalOmegaProbe_squaredSensitive

/-- Every Boolean event of the actual encoded chordal-`omega` value has its
exact affine-input probability. -/
theorem encodedChordalOmegaProbe_eventProbability_eq_values {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (event : Coordinate → Bool) :
    distribution.probability (fun item => event (chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.probability (fun item => event (chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value))) :=
  encodedSquaredSensitiveProbe_eventProbability_eq_values distribution
    fraction numeratorNonzero chordalOmegaProbe 2
    chordalOmegaProbe_squaredSensitive event

/-- Every rational statistic of the actual encoded chordal-`omega` value has
its exact affine-input expectation. -/
theorem encodedChordalOmegaProbe_observableExpectation_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (observable : Coordinate → Coordinate) :
    distribution.expectation (fun item => observable (chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.expectation (fun item => observable (chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value))) :=
  encodedSquaredSensitiveProbe_observableExpectation_eq_values distribution
    fraction numeratorNonzero chordalOmegaProbe 2
    chordalOmegaProbe_squaredSensitive observable

/-- A sufficient finite encoder prefix makes the distance-to-`omega` probe
error event relative to the original affine inputs have exactly zero
probability at the requested positive rational tolerance. -/
theorem encodedChordalOmegaProbe_separationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
      (_root_.FiniteMeasure.separationAtLeast epsilon
        (fun item => chordalOmegaProbe (points item))
        (fun item => chordalOmegaProbe
          (CCL.Proj.affine (fraction item).value))) = 0 :=
  encodedSquaredProbe_separationProbability_eq_zero_of_requested distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough points
    pointsRealize

/-- Every compatible realization of a finite encoder table has its
distance-to-`omega` expectation squared-error bounded by twice the expected
emitted cylinder spread. -/
theorem encodedChordalOmegaProbe_expectation_separation_sq_le {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => chordalOmegaProbe (points item))
        (distribution.expectation fun item =>
          chordalOmegaProbe (CCL.Proj.affine (fraction item).value)) ^ 2 ≤
      distribution.expectation fun item =>
        2 * cylinderSpread
          (CCL.Encoder.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks :=
  encodedSquaredProbe_expectation_separation_sq_le distribution fraction
    numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive points pointsRealize

/-- The corresponding finite request theorem for the concrete nonconstant
distance-to-`omega` observable. -/
theorem encodedChordalOmegaProbe_expectation_separation_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => chordalOmegaProbe (points item))
        (distribution.expectation fun item =>
          chordalOmegaProbe (CCL.Proj.affine (fraction item).value)) < epsilon :=
  encodedSquaredProbe_expectation_separation_lt_requested distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize

end CCL.FiniteMeasure
