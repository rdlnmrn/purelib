import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.ProjectivePrefixProfile
import CCL.Encoding.Encoder

/-!
# Finite measure certificates emitted by the executable CCL encoder

This module is the concrete bridge from `CCL.Encoder.encodeBlocks` to the
projectively rescaled prefix-measure facade.  It packages each finite encoder
result as an inhabited rational enclosure and lifts a finite input table to a
finite expectation enclosure.

The reconstructed affine input is used only through the encoder's explicit
finite projective-equivalence proof.  No quotient representative is chosen.
-/

namespace CCL.FiniteMeasure

/-- Package one executable finite block encoding as an encoder-facing prefix
certificate. -/
def encodedProjectivePrefixCertificate
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    CompletedProjectivePrefixCertificate where
  blocks := (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
  witness := (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point
  witnessRealizes :=
    CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero

/-- The packaged encoder witness reconstructs the original affine fraction
up to the explicit finite projective equivalence relation. -/
theorem encodedProjectivePrefixCertificate_reconstruct
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0) :
    (encodedProjectivePrefixCertificate fraction numeratorNonzero).witness
        |>.Equivalent (CCL.Proj.affine fraction.value) :=
  CCL.Encoder.encodeBlocks_reconstruct fraction numeratorNonzero

/-- Any chordal-sensitive rational probe takes the same value on two
explicitly equivalent homogeneous representatives. -/
theorem probe_eq_of_projectiveEquivalent
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {left right : Proj} (equivalent : left.Equivalent right) :
    probe left = probe right := by
  have separationNonpositive :
      _root_.FiniteMeasure.rationalSeparation
          (probe left) (probe right) ≤ 0 := by
    calc
      _root_.FiniteMeasure.rationalSeparation
          (probe left) (probe right) ≤
          factor * CCL.Chordal.chordalSq left right :=
        sensitive left right
      _ = 0 := by
        rw [CCL.Chordal.chordalSq_eq_zero_of_equivalent equivalent]
        ring1
  have directed := max_le_iff.mp separationNonpositive
  apply le_antisymm
  · have moved := (sub_le_iff_le_add).1 directed.1
    simpa only [zero_add] using moved
  · have moved := (sub_le_iff_le_add).1 directed.2
    simpa only [zero_add] using moved

/-- Rational probe enclosure attached directly to one finite encoder run. -/
def encodedProjectivePrefixProbeBound
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.Bound :=
  (encodedProjectivePrefixCertificate fraction numeratorNonzero).probeBound
    probe factor factorNonnegative sensitive

/-- The encoder-facing enclosure contains the probe value of the exact
homogeneous representative computed by `encodeBlocks`. -/
theorem encodedProjectivePrefixProbeBound_contains_point
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorNonnegative sensitive).Contains
        (probe (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point) := by
  exact completedProjectivePrefixProbeBound_contains
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point
    (CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero)
    probe factor factorNonnegative sensitive
    (CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero)

/-- The same enclosure contains the probe value of the original affine
fraction reconstructed by the encoder. -/
theorem encodedProjectivePrefixProbeBound_contains_value
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorNonnegative sensitive).Contains
        (probe (CCL.Proj.affine fraction.value)) := by
  have inside := encodedProjectivePrefixProbeBound_contains_point fraction
    numeratorNonzero probe factor factorNonnegative sensitive
  have probeEqual := probe_eq_of_projectiveEquivalent probe factor sensitive
    (CCL.Encoder.encodeBlocks_reconstruct fraction numeratorNonzero)
  rw [probeEqual] at inside
  exact inside

/-- A sufficient emitted block count turns one concrete encoder run into a
strict rational accuracy certificate for every compatible projective value. -/
theorem encodedProjectivePrefixProbeBound_width_lt_requested
    (fraction : CCL.Encoder.Frac)
    (numeratorNonzero : fraction.num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : requiredProbeBlockCount target factor ≤
      (CCL.Encoder.encodeBlocks fraction numeratorNonzero).blocks.length) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorPositive.le sensitive).width < target :=
  completedProjectivePrefixProbeBound_width_lt_requested
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero).point
    (CCL.Encoder.encodeBlocks_realizes fraction numeratorNonzero)
    probe factor factorPositive sensitive target targetPositive enough

/-! ## Finite tables of encoder inputs -/

/-- Push a finite input distribution through the executable certificate
packager.  Repeated encoded rows remain explicit weighted rows. -/
def encodedProjectivePrefixDistribution {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (fraction : ι → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate :=
  distribution.map fun item =>
    encodedProjectivePrefixCertificate (fraction item)
      (numeratorNonzero item)

/-- The projective-prefix family enclosure of an actual finite encoder table
contains the exact finite expectation of the computed homogeneous points. -/
theorem encodedProjectivePrefixExpectationBound_contains_points {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (fraction : ι → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (projectivePrefixFamilyProbeExpectationBound
      (encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun item =>
          probe (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point) := by
  have inside := projectivePrefixFamilyProbeExpectationBound_contains
    (encodedProjectivePrefixDistribution distribution fraction
      numeratorNonzero)
    probe factor factorNonnegative sensitive
    (fun certificate => certificate.witness)
    (by
      intro atom member
      exact atom.item.witnessRealizes)
  rw [encodedProjectivePrefixDistribution, distribution.map_expectation]
    at inside
  exact inside

/-- Using finite reconstruction and probe sensitivity, the same family
enclosure contains the exact finite expectation on the original affine input
fractions. -/
theorem encodedProjectivePrefixExpectationBound_contains_values {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (fraction : ι → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (projectivePrefixFamilyProbeExpectationBound
      (encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun item =>
          probe (CCL.Proj.affine (fraction item).value)) := by
  have inside := encodedProjectivePrefixExpectationBound_contains_points
    distribution fraction numeratorNonzero probe factor factorNonnegative
      sensitive
  have expectationEqual :
      distribution.expectation (fun item =>
          probe (CCL.Encoder.encodeBlocks
            (fraction item) (numeratorNonzero item)).point) =
        distribution.expectation (fun item =>
          probe (CCL.Proj.affine (fraction item).value)) := by
    exact distribution.expectation_congr _ _ (fun item =>
      probe_eq_of_projectiveEquivalent probe factor sensitive
        (CCL.Encoder.encodeBlocks_reconstruct
          (fraction item) (numeratorNonzero item)))
  rw [expectationEqual] at inside
  exact inside

/-- If every row's concrete encoder output meets the computed half-width
budget, the whole finite affine-input expectation enclosure is narrower than
the requested positive rational tolerance. -/
theorem encodedProjectivePrefixExpectationBound_width_lt_requested {ι : Type}
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (fraction : ι → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 2) factor ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length) :
    (projectivePrefixFamilyProbeExpectationBound
      (encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorPositive.le sensitive).width < target := by
  have halfPositive : (0 : Coordinate) < target / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive (by decide)
  have halfSmall : target / 2 < target := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      target = target * 1 := by ring1
      _ < target * 2 :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          targetPositive (by decide)
  rw [projectivePrefixFamilyProbeExpectationBound_width,
    encodedProjectivePrefixDistribution, distribution.map_expectation]
  calc
    distribution.expectation (fun item =>
          2 * (factor * cylinderSpread
            (encodedProjectivePrefixCertificate
              (fraction item) (numeratorNonzero item)).blocks)) ≤
        distribution.expectation (fun _ => target / 2) := by
      apply distribution.expectation_mono
      intro atom member
      have widthSmall := completedProjectivePrefixProbeBound_width_lt_requested
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).point
        (CCL.Encoder.encodeBlocks_realizes (fraction atom.item)
          (numeratorNonzero atom.item))
        probe factor factorPositive sensitive (target / 2) halfPositive
        (enough atom member)
      rw [completedProjectivePrefixProbeBound_width] at widthSmall
      exact widthSmall.le
    _ = target / 2 := distribution.expectation_constant _
    _ < target := halfSmall

end CCL.FiniteMeasure
