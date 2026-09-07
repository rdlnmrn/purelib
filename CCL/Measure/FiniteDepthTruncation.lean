import CCL.Measure.FiniteDepth
import CCL.Encoding.RawParser

/-!
# Finite-depth laws of CCL truncation points

The symbolic fair-bit distribution on a displayed raw extension frontier can
be pushed through the parser's explicit projective truncation.  The result is
an ordinary finite distribution of constructive projective points.  No claim
is made about a limiting decoder value or a geometric pushforward measure.
-/

namespace CCL.FiniteMeasure

/-- Projective truncation computed from one finite raw CCL word. -/
def rawTruncation (word : Word) : CCL.GaussianProjective.Proj :=
  (CCL.RawParser.parse word).truncation

/-- Every finite parser truncation is a valid projective point: the parser's
explicit decoder matrix has nonzero determinant. -/
theorem rawTruncation_hasNonzeroCoordinate (word : Word) :
    CCL.Chordal.Proj.HasNonzeroCoordinate (rawTruncation word) := by
  unfold rawTruncation CCL.RawParser.State.truncation
  exact CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    (CCL.RawParser.parse_det_ne word)
    CCL.Chordal.Proj.omega_hasNonzeroCoordinate

/-- Finite pushforward of one displayed raw-extension law through its
explicit parser truncation. -/
def rawTruncationDistribution (stem : Word) (depth : Nat) :
    _root_.FiniteMeasure.Distribution CCL.GaussianProjective.Proj :=
  (rawExtensionDistribution stem depth).map rawTruncation

/-- The pushforward retains exactly one displayed row per finite raw
continuation, including any repeated truncation payloads. -/
theorem rawTruncationDistribution_atoms_length (stem : Word) (depth : Nat) :
    (rawTruncationDistribution stem depth).atoms.length = 2 ^ depth := by
  rw [rawTruncationDistribution,
    _root_.FiniteMeasure.Distribution.map_atoms_length,
    rawExtensionDistribution_atoms_length]

/-- Every executable event of the finite truncation points is an exact
selected-row count times one depth-cell's dyadic mass. -/
theorem rawTruncationDistribution_probability_eq_count_mul
    (stem : Word) (depth : Nat)
    (event : CCL.GaussianProjective.Proj → Bool) :
    (rawTruncationDistribution stem depth).probability event =
      (rawFrontierEventCount (rawExtensions stem depth)
          (fun word => event (rawTruncation word)) : Coordinate) *
        (1 / 2 : Coordinate) ^ depth := by
  rw [rawTruncationDistribution,
    _root_.FiniteMeasure.Distribution.map_probability,
    rawExtensionDistribution_probability_eq_count_mul]

/-- Integrating a rational probe over the finite truncation law is exactly
the corresponding fair-bit frontier average. -/
theorem rawTruncationDistribution_expectation
    (stem : Word) (depth : Nat)
    (probe : CCL.GaussianProjective.Proj → Coordinate) :
    (rawTruncationDistribution stem depth).expectation probe =
      (rawExtensionDistribution stem depth).expectation
        (fun word => probe (rawTruncation word)) := by
  rw [rawTruncationDistribution,
    _root_.FiniteMeasure.Distribution.map_expectation]

/-- A deep finite truncation probe may be folded backward through any
explicitly supplied finite depth gap before taking its expectation. -/
theorem rawTruncationDistribution_expectation_backward
    (stem : Word) (depth extra : Nat)
    (probe : CCL.GaussianProjective.Proj → Coordinate) :
    (rawExtensionDistribution stem depth).expectation
        (rawBackwardMean extra (fun word => probe (rawTruncation word))) =
      (rawTruncationDistribution stem (depth + extra)).expectation probe := by
  rw [rawTruncationDistribution_expectation]
  exact rawExtensionDistribution_expectation_backward stem depth
    (fun word => probe (rawTruncation word)) extra

/-- Exact finite total-variance decomposition for a deep truncation probe:
the displayed residual variance plus the variance of its backward average. -/
theorem rawTruncationDistribution_totalVariance_backward
    (stem : Word) (depth extra : Nat)
    (probe : CCL.GaussianProjective.Proj → Coordinate) :
    (rawTruncationDistribution stem (depth + extra)).variance probe =
      (rawExtensionDistribution stem depth).expectation
          (rawBackwardVariance extra
            (fun word => probe (rawTruncation word))) +
        (rawExtensionDistribution stem depth).variance
          (rawBackwardMean extra
            (fun word => probe (rawTruncation word))) := by
  have mapVariance :
      (rawTruncationDistribution stem (depth + extra)).variance probe =
        (rawExtensionDistribution stem (depth + extra)).variance
          (fun word => probe (rawTruncation word)) := by
    rw [rawTruncationDistribution]
    rw [(_root_.FiniteMeasure.Distribution.map _ _).variance_eq_secondMoment_sub_sq,
      (rawExtensionDistribution stem
        (depth + extra)).variance_eq_secondMoment_sub_sq,
      (rawExtensionDistribution stem (depth + extra)).map_expectation,
      (rawExtensionDistribution stem (depth + extra)).map_expectation]
  rw [mapVariance]
  exact rawExtensionDistribution_totalVariance_backward stem depth
    (fun word => probe (rawTruncation word)) extra

end CCL.FiniteMeasure
