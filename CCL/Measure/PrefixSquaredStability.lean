import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixProcess
import CCL.Measure.ProjectivePrefixProfile
import FiniteMeasure.LpComparison

/-!
# Root-free L2 stability of finite CCL prefix probes

Direct Lipschitz control by `chordalSq` is stronger than is natural for many
nonconstant projective observables.  This module instead accepts the
square-root-free estimate

`rationalSeparation (probe x) (probe y) ^ 2 ≤ factor * chordalSq x y`.

CCL cylinder contraction then controls exact finite powered-L2 distances.
Finite Cauchy--Schwarz transfers that control to squared expectation error,
and a request at the square of a supplied rational tolerance recovers an
ordinary strict expectation-separation theorem.  No square root is selected.
-/

namespace CCL.FiniteMeasure

/-- A rational probe whose squared output separation is controlled by
squared chordal separation. -/
def SquaredProbeSensitive (probe : Proj → Coordinate)
    (factor : Coordinate) : Prop :=
  ∀ left right,
    CCL.Chordal.Proj.HasNonzeroCoordinate left →
    CCL.Chordal.Proj.HasNonzeroCoordinate right →
    _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ^ 2 ≤
      factor * CCL.Chordal.chordalSq left right

private theorem canonicalRealizes_valid
    {blocks : List Block} {point : Proj}
    (realizes : CCL.Cylinder.Realizes blocks point) :
    CCL.Chordal.Proj.HasNonzeroCoordinate point := by
  induction realizes with
  | done point valid => exact valid
  | step block tail rest inductionHypothesis =>
      exact CCL.Chordal.Mat2.act_hasNonzeroCoordinate
        block.matrix_det_ne_zero inductionHypothesis

/-- Canonical CCL realizations inherit the squared probe-separation budget of
their completed prefix. -/
theorem realized_probe_separation_sq_le
    {blocks : List Block} {leftPoint rightPoint : Proj}
    (leftRealizes : CCL.Cylinder.Realizes blocks leftPoint)
    (rightRealizes : CCL.Cylinder.Realizes blocks rightPoint)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    _root_.FiniteMeasure.rationalSeparation
        (probe leftPoint) (probe rightPoint) ^ 2 ≤
      factor * cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint
    (canonicalRealizes_valid leftRealizes)
    (canonicalRealizes_valid rightRealizes)).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.Cylinder.Realizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)

/-- The same squared budget applies to exact projectively rescaled encoder
traces. -/
theorem projectiveRealized_probe_separation_sq_le
    {blocks : List Block} {leftPoint rightPoint : Proj}
    (leftRealizes : CCL.Cylinder.ProjectiveRealizes blocks leftPoint)
    (rightRealizes : CCL.Cylinder.ProjectiveRealizes blocks rightPoint)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor) :
    _root_.FiniteMeasure.rationalSeparation
        (probe leftPoint) (probe rightPoint) ^ 2 ≤
      factor * cylinderSpread blocks := by
  exact (sensitive leftPoint rightPoint leftRealizes.valid
    rightRealizes.valid).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (CCL.Cylinder.ProjectiveRealizes.chordalSq_le_half_pow
        leftRealizes rightRealizes)
      factorNonnegative)

/-- Squared-sensitive probes are invariant under an explicitly supplied
projective equivalence between valid homogeneous representatives. -/
theorem squaredSensitive_probe_eq_of_projectiveEquivalent
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : SquaredProbeSensitive probe factor)
    {left right : Proj}
    (leftValid : CCL.Chordal.Proj.HasNonzeroCoordinate left)
    (rightValid : CCL.Chordal.Proj.HasNonzeroCoordinate right)
    (equivalent : left.Equivalent right) :
    probe left = probe right := by
  have squareNonpositive :
      _root_.FiniteMeasure.rationalSeparation
          (probe left) (probe right) ^ 2 ≤ 0 := by
    calc
      _root_.FiniteMeasure.rationalSeparation
          (probe left) (probe right) ^ 2 ≤
          factor * CCL.Chordal.chordalSq left right :=
        sensitive left right leftValid rightValid
      _ = 0 := by
        rw [CCL.Chordal.chordalSq_eq_zero_of_equivalent equivalent]
        ring1
  have squareZero :
      _root_.FiniteMeasure.rationalSeparation
          (probe left) (probe right) ^ 2 = 0 :=
    le_antisymm squareNonpositive
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have differenceSquareZero : (probe left - probe right) ^ 2 = 0 := by
    rw [← _root_.FiniteMeasure.rationalSeparation_sq]
    exact squareZero
  have differenceZero : probe left - probe right = 0 :=
    (RFAP.ConstructiveFraction.sq_eq_zero_direct _).mp differenceSquareZero
  calc
    probe left = (probe left - probe right) + probe right := by ring1
    _ = 0 + probe right := by rw [differenceZero]
    _ = probe right := by ring1

/-- Powered-L2 distance between two canonical realization families is at
most the exact expected squared-probe cylinder budget. -/
theorem prefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  change distribution.expectation (fun certificate =>
      (probe (leftPoints certificate) - probe (rightPoints certificate)) ^ 2) ≤
    distribution.expectation fun certificate =>
      factor * cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  rw [← _root_.FiniteMeasure.rationalSeparation_sq]
  exact realized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

/-- Powered-L2 distance between two projectively rescaled realization
families obeys the same expected finite cylinder budget. -/
theorem projectivePrefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : CompletedProjectivePrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  change distribution.expectation (fun certificate =>
      (probe (leftPoints certificate) - probe (rightPoints certificate)) ^ 2) ≤
    distribution.expectation fun certificate =>
      factor * cylinderSpread certificate.blocks
  apply distribution.expectation_mono
  intro atom member
  rw [← _root_.FiniteMeasure.rationalSeparation_sq]
  exact projectiveRealized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

/-- Squared separation of two canonical-family expectations is bounded by
the same exact expected CCL budget. -/
theorem prefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : CompletedPrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ^ 2 ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (prefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
        distribution probe factor factorNonnegative sensitive
        leftPoints rightPoints leftRealizes rightRealizes)

/-- Squared separation of two encoder-facing projective-family expectations
is bounded by the same finite expected CCL budget. -/
theorem projectivePrefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
    (distribution : _root_.FiniteMeasure.Distribution
      CompletedProjectivePrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (leftPoints rightPoints : CompletedProjectivePrefixCertificate → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes atom.item.blocks
        (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) ^ 2 ≤
      distribution.expectation fun certificate =>
        factor * cylinderSpread certificate.blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun certificate => probe (leftPoints certificate))
    (fun certificate => probe (rightPoints certificate))).trans
      (projectivePrefixFamilyProbe_poweredL2Distance_le_of_squaredSensitive
        distribution probe factor factorNonnegative sensitive
        leftPoints rightPoints leftRealizes rightRealizes)

/-- Block count used to recover an ordinary rational expectation tolerance
from a squared-probe sensitivity estimate.  The factor `1/2` leaves a strict
finite averaging margin. -/
def requiredSquaredProbeBlockCount
    (epsilon factor : Coordinate) : Nat :=
  requiredBlockCount ((epsilon ^ 2 / 2) / factor)

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

private theorem lt_of_sq_lt_sq_of_nonneg {left right : Coordinate}
    (rightNonnegative : 0 ≤ right) (squares : left ^ 2 < right ^ 2) :
    left < right := by
  rcases lt_trichotomy left right with less | equal | greater
  · exact less
  · subst right
    exact (lt_irrefl _ squares).elim
  · have squareOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      rightNonnegative greater.le 2
    exact ((not_lt_of_ge squareOrder) squares).elim

/-- Meeting the squared-probe request makes one sensitivity-scaled cylinder
budget at most half the square of the supplied rational tolerance. -/
theorem scaledCylinderSpread_le_half_sq_of_requested
    {blocks : List Block} (epsilon factor : Coordinate)
    (epsilonPositive : 0 < epsilon) (factorPositive : 0 < factor)
    (enough : requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    factor * cylinderSpread blocks ≤ epsilon ^ 2 / 2 := by
  have squarePositive : 0 < epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct epsilonPositive 2
  have halfPositive : 0 < epsilon ^ 2 / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct squarePositive (by decide)
  have targetPositive : 0 < (epsilon ^ 2 / 2) / factor :=
    RFAP.ConstructiveFraction.div_pos_direct halfPositive factorPositive
  have spreadSmall : cylinderSpread blocks <
      (epsilon ^ 2 / 2) / factor :=
    cylinderSpread_lt_of_requiredBlockCount_le targetPositive enough
  calc
    factor * cylinderSpread blocks ≤
        factor * ((epsilon ^ 2 / 2) / factor) :=
      (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        factorPositive spreadSmall).le
    _ = epsilon ^ 2 / 2 := by
      calc
        factor * ((epsilon ^ 2 / 2) / factor) =
            ((epsilon ^ 2 / 2) / factor) * factor :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = epsilon ^ 2 / 2 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (epsilon ^ 2 / 2) factor factorPositive.ne'

/-- A completed canonical prefix meeting the computed squared-probe request
makes every two of its realizations strictly closer than the supplied
positive rational probe tolerance. -/
theorem realizedSquaredProbe_separation_lt_of_requested
    {blocks : List Block} {leftPoint rightPoint : Proj}
    (leftRealizes : CCL.Cylinder.Realizes blocks leftPoint)
    (rightRealizes : CCL.Cylinder.Realizes blocks rightPoint)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    _root_.FiniteMeasure.rationalSeparation
        (probe leftPoint) (probe rightPoint) < epsilon := by
  have squaredLe := realized_probe_separation_sq_le leftRealizes rightRealizes
    probe factor factorPositive.le sensitive
  have budgetLe := scaledCylinderSpread_le_half_sq_of_requested epsilon factor
    epsilonPositive factorPositive enough
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

/-- Projectively rescaled realizations meeting the same finite request obey
the same strict rational probe-separation bound. -/
theorem projectiveRealizedSquaredProbe_separation_lt_of_requested
    {blocks : List Block} {leftPoint rightPoint : Proj}
    (leftRealizes : CCL.Cylinder.ProjectiveRealizes blocks leftPoint)
    (rightRealizes : CCL.Cylinder.ProjectiveRealizes blocks rightPoint)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : requiredSquaredProbeBlockCount epsilon factor ≤
      blocks.length) :
    _root_.FiniteMeasure.rationalSeparation
        (probe leftPoint) (probe rightPoint) < epsilon := by
  have squaredLe := projectiveRealized_probe_separation_sq_le
    leftRealizes rightRealizes probe factor factorPositive.le sensitive
  have budgetLe := scaledCylinderSpread_le_half_sq_of_requested epsilon factor
    epsilonPositive factorPositive enough
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

/-- A finite uniform block budget makes the expectations of any two
canonical realization families strictly closer than the requested rational
tolerance under squared-probe sensitivity. -/
theorem prefixFamilySquaredProbe_expectations_pairwise_separation_lt_requested
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
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) < epsilon := by
  have squaredLe :=
    prefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
      distribution probe factor factorPositive.le sensitive
      leftPoints rightPoints leftRealizes rightRealizes
  have budgetLe : distribution.expectation (fun certificate =>
        factor * cylinderSpread certificate.blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

/-- The same finite request theorem applies directly to projectively
rescaled encoder certificates. -/
theorem projectivePrefixFamilySquaredProbe_expectations_pairwise_separation_lt_requested
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
        (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun certificate =>
          probe (leftPoints certificate))
        (distribution.expectation fun certificate =>
          probe (rightPoints certificate)) < epsilon := by
  have squaredLe :=
    projectivePrefixFamilyProbe_expectation_separation_sq_le_of_squaredSensitive
      distribution probe factor factorPositive.le sensitive
      leftPoints rightPoints leftRealizes rightRealizes
  have budgetLe : distribution.expectation (fun certificate =>
        factor * cylinderSpread certificate.blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun certificate =>
            factor * cylinderSpread certificate.blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

namespace PrefixFamilyProcess

/-- At one finite process state, squared-probe sensitivity controls the exact
powered-L2 distance between any two admitted realization families. -/
theorem probe_poweredL2Distance_le_of_squaredSensitive {index : Type}
    (process : PrefixFamilyProcess index)
    (distribution : _root_.FiniteMeasure.Distribution index)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (state : process.State) (leftPoints rightPoints : index → Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (rightPoints atom.item)) :
    distribution.poweredL2Distance
        (fun item => probe (leftPoints item))
        (fun item => probe (rightPoints item)) ≤
      distribution.expectation fun item =>
        factor * cylinderSpread (process.blocks state item) := by
  change distribution.expectation (fun item =>
      (probe (leftPoints item) - probe (rightPoints item)) ^ 2) ≤
    distribution.expectation fun item =>
      factor * cylinderSpread (process.blocks state item)
  apply distribution.expectation_mono
  intro atom member
  rw [← _root_.FiniteMeasure.rationalSeparation_sq]
  exact realized_probe_separation_sq_le
    (leftRealizes atom member) (rightRealizes atom member)
    probe factor factorNonnegative sensitive

/-- One computed finite process request makes the expectations of every two
admitted realization families strictly closer than a positive rational
tolerance under squared-probe sensitivity. -/
theorem request_squaredProbeExpectations_pairwise_separation_lt
    {index : Type} (process : PrefixFamilyProcess index)
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
        (rightPoints atom.item)) :
    _root_.FiniteMeasure.rationalSeparation
        (distribution.expectation fun item => probe (leftPoints item))
        (distribution.expectation fun item => probe (rightPoints item)) <
      epsilon := by
  let requested := process.request state
    (requiredSquaredProbeBlockCount epsilon factor)
  have poweredL2Le := process.probe_poweredL2Distance_le_of_squaredSensitive
    distribution probe factor factorPositive.le sensitive requested
    leftPoints rightPoints leftRealizes rightRealizes
  have squaredLe :=
    (distribution.expectation_separation_sq_le_poweredL2Distance
      (fun item => probe (leftPoints item))
      (fun item => probe (rightPoints item))).trans poweredL2Le
  have budgetLe : distribution.expectation (fun item =>
        factor * cylinderSpread (process.blocks requested item)) ≤
      epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * cylinderSpread (process.blocks requested item)) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive
          (process.request_length state
            (requiredSquaredProbeBlockCount epsilon factor) atom.item)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have squaresSmall := squaredLe.trans_lt
    (budgetLe.trans_lt (half_sq_lt_sq epsilonPositive))
  exact lt_of_sq_lt_sq_of_nonneg epsilonPositive.le squaresSmall

end PrefixFamilyProcess

end CCL.FiniteMeasure
