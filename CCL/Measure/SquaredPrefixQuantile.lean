import mathlib.Tactic.QuotientFreeOmega
import CCL.Measure.EncodedSquaredStability
import FiniteMeasure.QuantileStability

/-!
# Quantile stability from finite squared-sensitive CCL prefixes

Uniform finite CCL cylinder contraction controls executable lower quantiles
of squared-sensitive rational probes.  The result is a direct finite
pushforward theorem at a displayed rational quantile level; no limiting law,
infimum, or completed real value is introduced.
-/

namespace CCL.FiniteMeasure

/-- Any two canonical realization families of a sufficiently long finite
prefix table have lower quantiles within the requested rational tolerance. -/
theorem prefixFamilySquaredProbe_lowerQuantile_separation_le_requested
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item))
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        ((distribution.map fun certificate =>
          probe (leftPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun certificate =>
          probe (rightPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (realizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

/-- The same lower-quantile request theorem holds for projectively rescaled
encoder-facing prefix certificates. -/
theorem projectivePrefixFamilySquaredProbe_lowerQuantile_separation_le_requested
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredSquaredProbeBlockCount epsilon factor ≤
        atom.item.blocks.length)
    (leftPoints rightPoints : CompletedProjectivePrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item))
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        ((distribution.map fun certificate =>
          probe (leftPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun certificate =>
          probe (rightPoints certificate)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (projectiveRealizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

namespace PrefixFamilyProcess

/-- One computed finite process request makes the lower quantiles of every
two admitted realization families uniformly close. -/
theorem request_squaredProbeLowerQuantiles_separation_le {index : Type}
    (process : PrefixFamilyProcess index)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (state : process.State) (epsilon : Coordinate)
    (epsilonPositive : 0 < epsilon)
    (leftPoints rightPoints : index → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          (process.request state
            (requiredSquaredProbeBlockCount epsilon factor)) atom.item)
        (rightPoints atom.item))
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        ((distribution.map fun item => probe (leftPoints item)).lowerQuantile
          level levelPositive levelAtMostOne)
        ((distribution.map fun item => probe (rightPoints item)).lowerQuantile
          level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  exact (realizedSquaredProbe_separation_lt_of_requested
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorPositive sensitive epsilon epsilonPositive
    (process.request_length state
      (requiredSquaredProbeBlockCount epsilon factor) atom.item)).le

end PrefixFamilyProcess

/-! ## Actual executable encoder tables -/

/-- Taking an executable lower quantile of a squared-sensitive probe on the
encoder's computed homogeneous points gives exactly the same rational answer
as taking it on the original affine Gaussian fractions. -/
theorem encodedSquaredSensitiveProbe_lowerQuantile_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    (distribution.map fun item => probe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).lowerQuantile
          level levelPositive levelAtMostOne =
      (distribution.map fun item =>
        probe (CCL.Proj.affine (fraction item).value)).lowerQuantile
          level levelPositive levelAtMostOne :=
  (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
    fraction numeratorNonzero probe factor sensitive).lowerQuantile_eq
      level levelPositive levelAtMostOne

/-- The corresponding executable lower medians agree exactly. -/
theorem encodedSquaredSensitiveProbe_median_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    (distribution.map fun item => probe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).median =
      (distribution.map fun item =>
        probe (CCL.Proj.affine (fraction item).value)).median :=
  (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
    fraction numeratorNonzero probe factor sensitive).median_eq

/-- In particular, the encoder computes the exact finite lower quantiles of
the chordal distance-to-`omega` observable represented by its input table. -/
theorem encodedChordalOmegaProbe_lowerQuantile_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    (distribution.map fun item => chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).lowerQuantile
          level levelPositive levelAtMostOne =
      (distribution.map fun item => chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value)).lowerQuantile
          level levelPositive levelAtMostOne :=
  encodedSquaredSensitiveProbe_lowerQuantile_eq_values distribution fraction
    numeratorNonzero chordalOmegaProbe 2 chordalOmegaProbe_squaredSensitive
      level levelPositive levelAtMostOne

/-- The encoded and affine chordal distance-to-`omega` laws therefore have
the same exact executable lower median. -/
theorem encodedChordalOmegaProbe_median_eq_values
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    (distribution.map fun item => chordalOmegaProbe
        (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).median =
      (distribution.map fun item => chordalOmegaProbe
        (CCL.Proj.affine (fraction item).value)).median :=
  encodedSquaredSensitiveProbe_median_eq_values distribution fraction
    numeratorNonzero chordalOmegaProbe 2 chordalOmegaProbe_squaredSensitive

/-- A sufficiently long actual encoder table has every compatible
realization-family lower quantile within the requested tolerance of the exact
lower quantile of the original affine Gaussian fractions. -/
theorem encodedSquaredProbe_lowerQuantile_separation_le_requested
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
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        ((distribution.map fun item => probe (points item)).lowerQuantile
          level levelPositive levelAtMostOne)
        ((distribution.map fun item =>
          probe (CCL.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
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

/-- The executable lower median of a compatible realization family is within
the same finite request of the exact lower median of the affine inputs. -/
theorem encodedSquaredProbe_median_separation_le_requested
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
    _root_.FiniteMeasure.rationalSeparation
        (distribution.map fun item => probe (points item)).median
        (distribution.map fun item =>
          probe (CCL.Proj.affine (fraction item).value)).median ≤ epsilon := by
  simpa only [_root_.FiniteMeasure.Distribution.median] using
    encodedSquaredProbe_lowerQuantile_separation_le_requested distribution
      fraction numeratorNonzero probe factor factorPositive sensitive
      epsilon epsilonPositive enough points pointsRealize
      (1 / 2) (by decide) (by decide)

/-- Concrete distance-to-`omega` specialization for executable encoder
tables, with the proved squared-sensitivity factor `2`. -/
theorem encodedChordalOmegaProbe_lowerQuantile_separation_le_requested
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
        (points atom.item))
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    _root_.FiniteMeasure.rationalSeparation
        ((distribution.map fun item =>
          chordalOmegaProbe (points item)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun item => chordalOmegaProbe
          (CCL.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon :=
  encodedSquaredProbe_lowerQuantile_separation_le_requested distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize level levelPositive levelAtMostOne

/-- Concrete lower-median stability for the executable distance-to-`omega`
observable. -/
theorem encodedChordalOmegaProbe_median_separation_le_requested
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
        (distribution.map fun item => chordalOmegaProbe (points item)).median
        (distribution.map fun item => chordalOmegaProbe
          (CCL.Proj.affine (fraction item).value)).median ≤ epsilon :=
  encodedSquaredProbe_median_separation_le_requested distribution fraction
    numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize

end CCL.FiniteMeasure
