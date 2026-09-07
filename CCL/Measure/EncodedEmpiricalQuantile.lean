import mathlib.Tactic.QuotientFreeOmega
import CCL.Measure.EncodedSquaredStability
import FiniteMeasure.EmpiricalQuantile

/-!
# Empirical quantiles of actual CCL encoder probes

The encoder's computed homogeneous point and its reconstructed affine input
have exactly the same chordal distance-to-`omega` value.  Consequently their
finite pushforward tables are equal, and the constructive empirical-quantile
request applies directly to samples of the encoded observable.
-/

namespace CCL.FiniteMeasure

/-- Exact finite law of the chordal distance-to-`omega` values computed from
the encoder's homogeneous output points. -/
def encodedChordalOmegaProbeLaw {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    _root_.FiniteMeasure.Distribution Coordinate :=
  distribution.map fun item => chordalOmegaProbe
    (CCL.Encoder.encodeBlocks
      (fraction item) (numeratorNonzero item)).point

/-- Exact finite law of the same probe evaluated on the original affine
Gaussian fractions. -/
def affineChordalOmegaProbeLaw {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac) :
    _root_.FiniteMeasure.Distribution Coordinate :=
  distribution.map fun item =>
    chordalOmegaProbe (CCL.Proj.affine (fraction item).value)

/-- The two executable pushforward tables are equal, row for row. -/
theorem encodedChordalOmegaProbeLaw_eq_affine {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero =
      affineChordalOmegaProbeLaw distribution fraction := by
  unfold encodedChordalOmegaProbeLaw affineChordalOmegaProbeLaw
  exact distribution.map_congr _ _ (fun item =>
    encodedChordalOmegaProbe_eq_value (fraction item)
      (numeratorNonzero item))

/-- The executable encoder-output probe law and its original affine-input
law have exactly zero finite Kolmogorov distance. -/
theorem encodedChordalOmegaProbeLaw_finiteKolmogorovDistance_affine_eq_zero
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    _root_.FiniteMeasure.Distribution.finiteKolmogorovDistance
      (encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      (affineChordalOmegaProbeLaw distribution fraction) = 0 := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact _root_.FiniteMeasure.Distribution.finiteKolmogorovDistance_refl _

/-- A sample from the actual encoder-output probe law has computed
finite-grid CDF distance from the exact affine-input law below the supplied
tolerance, except on an event of explicitly bounded probability. -/
theorem encodedChordalOmegaProbe_iidSamples_empiricalCumulativeGridDistance_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    ((encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (_root_.FiniteMeasure.Distribution.empiricalCumulativeGridDistanceDeviation
        (affineChordalOmegaProbeLaw distribution fraction) thresholds
        (_root_.FiniteMeasure.Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)
        tolerance) < failure := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalCumulativeGridDistanceDeviation_lt_requested
      thresholds tolerance tolerancePositive failure failurePositive

/-- A sample from the actual encoder-output probe law has globally small
finite Kolmogorov distance from the exact affine-input law, except on an
explicitly bounded event.  The required threshold grid is computed internally
from the finite affine law. -/
theorem encodedChordalOmegaProbe_iidSamples_empiricalFiniteKolmogorovDistance_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    ((encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredFiniteKolmogorovSampleCount
          (affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)).probability
      (_root_.FiniteMeasure.Distribution.empiricalFiniteKolmogorovDistanceDeviation
        (affineChordalOmegaProbeLaw distribution fraction)
        (_root_.FiniteMeasure.Distribution.requiredFiniteKolmogorovSampleCount
          (affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)
          tolerance) < failure := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalFiniteKolmogorovDistanceDeviation_lt_requested
      tolerance tolerancePositive failure failurePositive

/-- A finite iid sample of actual encoded chordal probe values has an
executable empirical lower-quantile confidence bracket.  Its two CDF margins
are checked against the exact affine-input probe law, while the sampled law
is the encoder's computed finite table. -/
theorem encodedChordalOmegaProbe_iidSamples_empiricalQuantileBracket_lt_requested
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (thresholds : List Coordinate)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMember : lower ∈ thresholds) (upperMember : upper ∈ thresholds)
    (lowerMargin :
      (affineChordalOmegaProbeLaw distribution fraction).cumulative lower +
        tolerance < level)
    (upperMargin : level + tolerance ≤
      (affineChordalOmegaProbeLaw distribution fraction).cumulative upper) :
    ((encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)).probability
      (_root_.FiniteMeasure.Distribution.empiricalLowerQuantileBracketDeviation
        (_root_.FiniteMeasure.Distribution.requiredCumulativeGridSampleCount
          thresholds tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
      thresholds tolerance tolerancePositive failure failurePositive level
      levelPositive levelAtMostOne lower upper lowerMember upperMember
      lowerMargin upperMargin

/-- Grid-free empirical quantile confidence for actual encoded chordal probe
values.  The finite affine probe law supplies its own support grid, while the
caller supplies only the rational CDF margins defining the desired bracket. -/
theorem encodedChordalOmegaProbe_iidSamples_empiricalQuantileBracket_lt_requested_global
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (failure : Coordinate) (failurePositive : 0 < failure)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate)
    (lowerMargin :
      (affineChordalOmegaProbeLaw distribution fraction).cumulative lower +
        tolerance < level)
    (upperMargin : level + tolerance ≤
      (affineChordalOmegaProbeLaw distribution fraction).cumulative upper) :
    ((encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      |>.iidSamples
        (_root_.FiniteMeasure.Distribution.requiredFiniteKolmogorovSampleCount
          (affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)).probability
      (_root_.FiniteMeasure.Distribution.empiricalLowerQuantileBracketDeviation
        (_root_.FiniteMeasure.Distribution.requiredFiniteKolmogorovSampleCount
          (affineChordalOmegaProbeLaw distribution fraction)
          tolerance failure)
        level levelPositive levelAtMostOne lower upper) < failure := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact (affineChordalOmegaProbeLaw distribution fraction)
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested_global
      tolerance tolerancePositive failure failurePositive level levelPositive
        levelAtMostOne lower upper lowerMargin upperMargin

end CCL.FiniteMeasure
