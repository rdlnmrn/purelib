import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixTransport
import CCL.Measure.EncodedSquaredStability

/-!
# Finite transport from actual CCL encoder tables

The same displayed source row canonically couples a compatible realization
with the original affine Gaussian input.  Squared rational separation is the
transport cost, so the exact cost is the source powered-L2 distance and CCL
cylinder contraction bounds it by an executable rational prefix budget.

This is the law-level approximation appropriate to nearby unequal atoms;
total variation need not become small in that situation.  No square root,
infimum over couplings, or completed Wasserstein space is introduced.
-/

namespace CCL.FiniteMeasure

/-- Canonical rowwise law coupling between the probe values of compatible
encoder realizations and the corresponding original affine inputs. -/
def encodedProbeLawCoupling {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (probe : Proj → Coordinate) (points : index → Proj) :
    _root_.FiniteMeasure.LawCoupling
      (distribution.map fun item => probe (points item))
      (distribution.map fun item =>
        probe (CCL.Proj.affine (fraction item).value)) :=
  probeLawCoupling distribution probe points fun item =>
    CCL.Proj.affine (fraction item).value

/-- The coupling's exact squared-separation transport cost is precisely the
powered-L2 distance between the two rowwise probe observables. -/
theorem encodedProbeLawCoupling_squaredTransportCost {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (probe : Proj → Coordinate) (points : index → Proj) :
    (encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) =
      distribution.poweredL2Distance
        (fun item => probe (points item))
        (fun item => probe (CCL.Proj.affine (fraction item).value)) := by
  unfold encodedProbeLawCoupling probeLawCoupling
  unfold _root_.FiniteMeasure.LawCoupling.transportCost
  unfold _root_.FiniteMeasure.LawCoupling.ofMaps
  unfold _root_.FiniteMeasure.Coupling.transportCost
  rw [distribution.map_expectation]
  change distribution.expectation (fun item =>
      _root_.FiniteMeasure.rationalSeparation
        (probe (points item))
        (probe (CCL.Proj.affine (fraction item).value)) ^ 2) =
    distribution.expectation (fun item =>
      (probe (points item) -
        probe (CCL.Proj.affine (fraction item).value)) ^ 2)
  exact distribution.expectation_congr _ _ fun item =>
    _root_.FiniteMeasure.rationalSeparation_sq _ _

/-- Coupling the encoder's own computed probe values to their affine inputs
has exactly zero squared transport cost for every squared-sensitive probe. -/
theorem encodedSquaredSensitiveProbeLawCoupling_squaredTransportCost_eq_zero
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor) :
    (encodedProbeLawCoupling distribution fraction probe
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) = 0 := by
  rw [encodedProbeLawCoupling_squaredTransportCost]
  calc
    distribution.poweredL2Distance
        (fun item => probe (CCL.Encoder.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        (fun item => probe (CCL.Proj.affine (fraction item).value)) =
        distribution.poweredL2Distance
          (fun item => probe (CCL.Proj.affine (fraction item).value))
          (fun item => probe (CCL.Proj.affine (fraction item).value)) := by
      unfold _root_.FiniteMeasure.Distribution.poweredL2Distance
        _root_.FiniteMeasure.FiniteContent.poweredL2Distance
      exact distribution.toFiniteContent.poweredL2_congr _ _ fun item => by
        dsimp only
        rw [encodedSquaredSensitiveProbe_eq_value (fraction item)
          (numeratorNonzero item) probe factor sensitive]
    _ = 0 := distribution.poweredL2Distance_refl _

/-- Exact zero-cost specialization for the encoded chordal
distance-to-`omega` law. -/
theorem encodedChordalOmegaProbeLawCoupling_squaredTransportCost_eq_zero
    {index : Type}
    (distribution : _root_.FiniteMeasure.Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0) :
    (encodedProbeLawCoupling distribution fraction chordalOmegaProbe
      (fun item => (CCL.Encoder.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) = 0 :=
  encodedSquaredSensitiveProbeLawCoupling_squaredTransportCost_eq_zero
    distribution fraction numeratorNonzero chordalOmegaProbe 2
      chordalOmegaProbe_squaredSensitive

/-- Actual encoder contraction bounds the canonical coupling's exact squared
transport cost by the expected emitted cylinder budget. -/
theorem encodedProbeLawCoupling_squaredTransportCost_le {index : Type}
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
    (encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) ≤
      distribution.expectation fun item =>
        factor * cylinderSpread
          (CCL.Encoder.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  rw [encodedProbeLawCoupling_squaredTransportCost]
  exact encodedSquaredProbe_poweredL2Distance_values_le distribution fraction
    numeratorNonzero probe factor factorNonnegative sensitive points
    pointsRealize

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

/-- A finite block-count check on every actual encoder output makes the
canonical squared transport cost strictly smaller than the supplied squared
rational tolerance. -/
theorem encodedProbeLawCoupling_squaredTransportCost_lt_requested
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
    (encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) <
      epsilon ^ 2 := by
  have costLe := encodedProbeLawCoupling_squaredTransportCost_le distribution
    fraction numeratorNonzero probe factor factorPositive.le sensitive points
    pointsRealize
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
  exact costLe.trans_lt (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))

/-- Concrete distance-to-`omega` law coupling with exact squared transport
cost below every requested squared rational tolerance once the emitted block
lists satisfy the computed finite request. -/
theorem encodedChordalOmegaProbeLawCoupling_squaredTransportCost_lt_requested
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
    (encodedProbeLawCoupling distribution fraction chordalOmegaProbe points
      ).transportCost
        (fun left right =>
          _root_.FiniteMeasure.rationalSeparation left right ^ 2) <
      epsilon ^ 2 :=
  encodedProbeLawCoupling_squaredTransportCost_lt_requested distribution
    fraction numeratorNonzero chordalOmegaProbe 2 (by decide)
    chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough points
    pointsRealize

end CCL.FiniteMeasure
