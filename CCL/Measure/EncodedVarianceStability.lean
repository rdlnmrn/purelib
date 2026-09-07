import mathlib.Tactic.QuotientFreeOmega
import CCL.Measure.EncodedSquaredStability
import FiniteMeasure.VarianceStability

/-!
# Variance stability for actual finite CCL encoder tables

Uniform squared-sensitive prefix contraction controls not only expectations
but, for unit-interval probes, exact finite variances.  The concrete
distance-to-`omega` probe supplies its own `[0, 1]` range proof.
-/

namespace CCL.FiniteMeasure

/-- On the encoder's own computed homogeneous points, every
squared-sensitive probe has exactly the affine-input variance.  No range,
prefix-length, or approximation hypothesis is needed. -/
theorem encodedSquaredSensitiveProbe_variance_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.variance (fun item =>
        probe (CCL.Proj.affine (fraction item).value)) := by
  exact distribution.variance_congr _ _ (fun item =>
    encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)

/-- Exact variance identity for the actual encoded distance-to-`omega`
observable. -/
theorem encodedChordalOmegaProbe_variance_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    distribution.variance (fun item => chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.variance (fun item => chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value)) :=
  encodedSquaredSensitiveProbe_variance_eq_values distribution fraction
    numeratorNonzero chordalOmegaProbe 2 chordalOmegaProbe_squaredSensitive

/-- A sufficiently long actual encoder table makes the variance of every
compatible realization family close to the exact affine-input variance for
any squared-sensitive unit-interval probe. -/
theorem encodedSquaredProbe_variance_separation_le_requested
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
        (points atom.item))
    (pointsRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ probe (points atom.item) ∧ probe (points atom.item) ≤ 1)
    (valuesRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ probe (CCL.Proj.affine (fraction atom.item).value) ∧
        probe (CCL.Proj.affine (fraction atom.item).value) ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.variance fun item => probe (points item))
        (distribution.variance fun item =>
          probe (CCL.Proj.affine (fraction item).value)) ≤ 4 * epsilon := by
  apply distribution.variance_rationalSeparation_le_of_unitInterval
    (fun item => probe (points item))
    (fun item => probe (CCL.Proj.affine (fraction item).value)) epsilon
    pointsRange valuesRange
  intro atom member
  let encoding := CCL.Encoder.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (CCL.Proj.affine (fraction atom.item).value) :=
    squaredSensitive_probe_eq_of_projectiveEquivalent probe factor sensitive
      encoding.realizes.valid
      (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
        (fraction atom.item).value)
      encoding.reconstruct
  rw [← probeEqual]
  exact (projectiveRealizedSquaredProbe_separation_lt_of_requested
    (pointsRealize atom member) encoding.realizes
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

/-- Concrete distance-to-`omega` variance stability for actual finite encoder
tables. -/
theorem encodedChordalOmegaProbe_variance_separation_le_requested
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
        (distribution.variance fun item => chordalOmegaProbe (points item))
        (distribution.variance fun item => chordalOmegaProbe
          (CCL.Proj.affine (fraction item).value)) ≤ 4 * epsilon := by
  apply encodedSquaredProbe_variance_separation_le_requested distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize
  · intro atom member
    exact ⟨chordalOmegaProbe_nonnegative (points atom.item),
      chordalOmegaProbe_le_one (pointsRealize atom member).valid⟩
  · intro atom member
    exact ⟨chordalOmegaProbe_nonnegative
        (CCL.Proj.affine (fraction atom.item).value),
      chordalOmegaProbe_le_one
        (CCL.Chordal.Proj.affine_hasNonzeroCoordinate
          (fraction atom.item).value)⟩

end CCL.FiniteMeasure
