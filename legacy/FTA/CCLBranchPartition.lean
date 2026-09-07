import FTA.CCLBranchCharts
import FTA.CCLIntersectionPartition
import FTA.CCLIntersectionSampler
import FTA.ProjectivePathBounds
import FTA.PositiveLowerBound

/-!
# Total guarded partitions for bounded CCL branch charts

A bounded chart alone is not yet a legal Sturm input: its endpoints may be
zeros of the curve common factor, the projective denominator, or a box-edge
condition.  This module combines all six kinds of polynomial into one
nonzero executable guard.  It then chooses clear rational endpoints in two
unit-width bands outside the complete chart interval and invokes the existing
common squarefree-factor partition on the resulting enclosing interval.

The construction is total and uses only finite dense-polynomial arithmetic,
degree recursion, bounded central searches, and a computed natural partition
depth.
-/

namespace FTA
namespace CCLBranchPartition

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathClearance
open FTA.ProjectivePath
open FTA.CCLPathIntersection
open FTA.CCLIntersectionGuard
open FTA.CCLIntersectionPartition
open FTA.CCLIntersectionSampler
open FTA.CauchyProduct
open FTA.SafeCandidates
open FTA.SquarefreeFactorization
open FTA.SturmTransducer
open FTA.PositiveLowerBound
open FTA.RationalPolynomialBounds

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- The curve-root polynomial, projective denominator norm, and four closed
box-intersection conditions whose zeros can alter an arc decision. -/
def arcPolynomials
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    List RatPolynomial :=
  PathClearance.commonFactor (clearedReal p path) (clearedImag p path) ::
    denominatorNorm path :: conditionPolynomials (boxConditions path box)

/-- Product of exactly the nonzero polynomials in the complete arc list. -/
def arcGuard
    (p : GaussianPolynomial) (path : Path) (box : RatBox) : RatPolynomial :=
  nonzeroPolynomialProduct (arcPolynomials p path box)

theorem arcGuard_isZero_false
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    (arcGuard p path box).isZero = false :=
  nonzeroPolynomialProduct_isZero_false _

theorem eval_ne_zero_of_mem_arcPolynomials
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {polynomial : RatPolynomial} {t : ℚ}
    (member : polynomial ∈ arcPolynomials p path box)
    (nonzero : polynomial.isZero = false)
    (guardClear : (arcGuard p path box).eval t ≠ 0) :
    polynomial.eval t ≠ 0 :=
  eval_ne_zero_of_mem_nonzeroPolynomialProduct member nonzero guardClear

theorem commonFactor_mem_arcPolynomials
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    PathClearance.commonFactor (clearedReal p path) (clearedImag p path) ∈
      arcPolynomials p path box := by
  simp [arcPolynomials]

theorem denominatorNorm_mem_arcPolynomials
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    denominatorNorm path ∈ arcPolynomials p path box := by
  simp [arcPolynomials]

theorem condition_mem_arcPolynomials
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {polynomial : RatPolynomial}
    (member : polynomial ∈ conditionPolynomials (boxConditions path box)) :
    polynomial ∈ arcPolynomials p path box := by
  simp [arcPolynomials, member]

/-- Constant guards have no events; nonconstant guards carry the executable
degree-recursive squarefree decomposition used by the common partitioner. -/
inductive ArcGuardFactorization
    (p : GaussianPolynomial) (path : Path) (box : RatBox) where
  | constant (degreeZero : (arcGuard p path box).natDegree = 0)
  | nonconstant (decomposition : Decomposition (arcGuard p path box))

def factorArcGuard
    (p : GaussianPolynomial) (path : Path) (box : RatBox) :
    ArcGuardFactorization p path box := by
  if degreeZero : (arcGuard p path box).natDegree = 0 then
    exact .constant degreeZero
  else
    exact .nonconstant
      (decompose (arcGuard p path box) (arcGuard_isZero_false p path box)
        degreeZero)

/-! ## Clear enclosing interval -/

/-- Unit-width band immediately to the left of a complete chart interval. -/
def leftGuardBand (core : RationalInterval) : RationalInterval :=
  ⟨core.lower - 1, core.lower⟩

/-- Unit-width band immediately to the right of a complete chart interval. -/
def rightGuardBand (core : RationalInterval) : RationalInterval :=
  ⟨core.upper, core.upper + 1⟩

theorem leftGuardBand_proper (core : RationalInterval) :
    (leftGuardBand core).Proper := by
  dsimp [leftGuardBand, RationalInterval.Proper]
  linarith

theorem rightGuardBand_proper (core : RationalInterval) :
    (rightGuardBand core).Proper := by
  dsimp [rightGuardBand, RationalInterval.Proper]
  linarith

/-- A clear interval strictly enclosing the complete bounded chart.  Its
endpoints are selected by bounded central searches against every derivative
chain in the squarefree arc-guard factorization. -/
structure GuardedRoot
    (factors : List Factor) (core : RationalInterval) where
  interval : RationalInterval
  proper : interval.Proper
  coreRefines : core.Refines interval
  lowerClear : (factorEventGuard factors).eval interval.lower ≠ 0
  upperClear : (factorEventGuard factors).eval interval.upper ≠ 0
  lowerStrict : interval.lower < core.lower
  upperStrict : core.upper < interval.upper

theorem GuardedRoot.arcGuard_lowerClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    (root : GuardedRoot decomposition.factors core) :
    (arcGuard p path box).eval root.interval.lower ≠ 0 := by
  rw [decomposition.eval_identity]
  exact mul_ne_zero decomposition.scalar_ne_zero
    (factorProduct_eval_ne_zero_of_eventGuard root.lowerClear)

theorem GuardedRoot.arcGuard_upperClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    (root : GuardedRoot decomposition.factors core) :
    (arcGuard p path box).eval root.interval.upper ≠ 0 := by
  rw [decomposition.eval_identity]
  exact mul_ne_zero decomposition.scalar_ne_zero
    (factorProduct_eval_ne_zero_of_eventGuard root.upperClear)

/-- The guarded outer endpoints avoid the curve common factor whenever the
cleared coordinate pair is nonzero. -/
theorem GuardedRoot.commonFactor_lowerClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    (root : GuardedRoot decomposition.factors core)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval root.interval.lower ≠ 0 :=
  eval_ne_zero_of_mem_arcPolynomials
    (commonFactor_mem_arcPolynomials p path box)
    (PathClearance.commonFactor_isZero_false clearedNonzero)
    root.arcGuard_lowerClear

theorem GuardedRoot.commonFactor_upperClear
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    {decomposition : Decomposition (arcGuard p path box)}
    (root : GuardedRoot decomposition.factors core)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    (PathClearance.commonFactor (clearedReal p path)
      (clearedImag p path)).eval root.interval.upper ≠ 0 :=
  eval_ne_zero_of_mem_arcPolynomials
    (commonFactor_mem_arcPolynomials p path box)
    (PathClearance.commonFactor_isZero_false clearedNonzero)
    root.arcGuard_upperClear

/-- Compute two clear outer endpoints without sacrificing any point of the
bounded complete chart. -/
def guardedRoot (factors : List Factor) (core : RationalInterval)
    (coreProper : core.Proper) : GuardedRoot factors core := by
  let leftBand := leftGuardBand core
  let rightBand := rightGuardBand core
  let lower := factorEventCut factors leftBand.lower leftBand.upper
  let upper := factorEventCut factors rightBand.lower rightBand.upper
  have leftGeometry := factorEventCut_geometry factors
    (leftGuardBand_proper core)
  have rightGeometry := factorEventCut_geometry factors
    (rightGuardBand_proper core)
  have lowerClear := (factorEventCut_spec factors
    (leftGuardBand_proper core)).1
  have upperClear := (factorEventCut_spec factors
    (rightGuardBand_proper core)).1
  have lowerStrict : lower < core.lower := by
    simpa [lower, leftBand, leftGuardBand] using leftGeometry.2.1
  have upperStrict : core.upper < upper := by
    simpa [upper, rightBand, rightGuardBand] using rightGeometry.1
  exact
    { interval := ⟨lower, upper⟩
      proper := by
        exact lowerStrict.trans (coreProper.trans upperStrict)
      coreRefines := by
        exact ⟨lowerStrict.le, upperStrict.le⟩
      lowerClear := by
        simpa [lower, leftBand, leftGuardBand] using lowerClear
      upperClear := by
        simpa [upper, rightBand, rightGuardBand] using upperClear
      lowerStrict := lowerStrict
      upperStrict := upperStrict }

/-! ## Total guarded common partition -/

/-- Complete endpoint-safe partition plan for one bounded chart. -/
inductive ArcPartitionPlan
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (core : RationalInterval) where
  | constant (degreeZero : (arcGuard p path box).natDegree = 0)
  | factored
      (decomposition : Decomposition (arcGuard p path box))
      (root : GuardedRoot decomposition.factors core)
      (partition : CommonFactorPartition decomposition.factors root.interval)

/-- Total finite construction of the combined guarded partition around one
complete chart interval. -/
def buildArcPartitionPlan
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (core : RationalInterval) (coreProper : core.Proper) :
    ArcPartitionPlan p path box core :=
  match factorArcGuard p path box with
  | .constant degreeZero => .constant degreeZero
  | .nonconstant decomposition =>
      let root := guardedRoot decomposition.factors core coreProper
      .factored decomposition root
        (computedCommonFactorPartition decomposition.factors root.interval
          root.proper root.lowerClear root.upperClear)

/-! ## Quantitative terminal-cell decisions -/

/-- Removing one displayed nonzero member from the skip-zero guard leaves an
exact multiplicative remainder. -/
theorem nonzeroPolynomialProduct_eval_eq_mul_erase
    (polynomials : List RatPolynomial) (target : RatPolynomial)
    (member : target ∈ polynomials) (targetNonzero : target.isZero = false)
    (t : ℚ) :
    (nonzeroPolynomialProduct polynomials).eval t =
      target.eval t *
        (nonzeroPolynomialProduct (polynomials.erase target)).eval t := by
  induction polynomials with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      by_cases equal : head = target
      · subst head
        simp [nonzeroPolynomialProduct, targetNonzero]
      · have tailMember : target ∈ tail :=
          (List.mem_cons.mp member).resolve_left (Ne.symm equal)
        have tailIdentity := inductionHypothesis tailMember
        have targetNeHead : target ≠ head := fun equality => equal equality.symm
        have eraseIdentity : (head :: tail).erase target =
            head :: tail.erase target := by
          exact List.erase_cons_tail (not_beq_of_ne equal)
        by_cases headZero : head.isZero = true
        · rw [eraseIdentity]
          simp [nonzeroPolynomialProduct, headZero, tailIdentity]
        · have headNonzero : head.isZero = false :=
            Bool.eq_false_of_not_eq_true headZero
          rw [eraseIdentity]
          simp [nonzeroPolynomialProduct, headNonzero, tailIdentity]
          ring

/-- Positive coefficient upper bound for the guard product left after one
selected member is removed. -/
def erasedProductSqMajorant
    (polynomials : List RatPolynomial) (target : RatPolynomial)
    (interval : RationalInterval) : ℚ :=
  let magnitude := intervalMagnitude interval.lower interval.upper
  max 1 ((denseEvalAbsBound
    (nonzeroPolynomialProduct (polynomials.erase target)) magnitude) ^ 2)

theorem erasedProductSqMajorant_pos
    (polynomials : List RatPolynomial) (target : RatPolynomial)
    (interval : RationalInterval) :
    0 < erasedProductSqMajorant polynomials target interval :=
  zero_lt_one.trans_le (le_max_left (1 : ℚ) _)

theorem erasedProduct_eval_sq_le_majorant
    (polynomials : List RatPolynomial) (target : RatPolynomial)
    (interval : RationalInterval) {t : ℚ}
    (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    (nonzeroPolynomialProduct (polynomials.erase target)).eval t ^ 2 ≤
      erasedProductSqMajorant polynomials target interval := by
  let magnitude := intervalMagnitude interval.lower interval.upper
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos interval.lower interval.upper).le
  have parameterBound : |t| ≤ magnitude :=
    abs_le_intervalMagnitude lower upper
  have absoluteBound := abs_dense_eval_le_denseEvalAbsBound
    (nonzeroPolynomialProduct (polynomials.erase target))
    magnitudeNonnegative parameterBound
  have squareBound := pow_le_pow_left₀
    (abs_nonneg
      ((nonzeroPolynomialProduct (polynomials.erase target)).eval t))
    absoluteBound 2
  have squared :
      (nonzeroPolynomialProduct (polynomials.erase target)).eval t ^ 2 ≤
        denseEvalAbsBound
          (nonzeroPolynomialProduct (polynomials.erase target)) magnitude ^ 2 := by
    simpa [sq_abs] using squareBound
  dsimp [erasedProductSqMajorant]
  exact squared.trans (le_max_right _ _)

/-- Divide a positive lower bound for a skip-zero product by an upper bound
for every other factor, obtaining a positive squared-value lower bound for
one selected nonzero member. -/
def memberCertificateOfProduct
    (polynomials : List RatPolynomial) (target : RatPolynomial)
    (interval : RationalInterval) (member : target ∈ polynomials)
    (targetNonzero : target.isZero = false)
    (productCertificate : PositiveLowerBound.Certificate
      (nonzeroPolynomialProduct polynomials) interval) :
    PositiveLowerBound.Certificate target interval where
  bound := productCertificate.bound /
    erasedProductSqMajorant polynomials target interval
  positive := div_pos productCertificate.positive
    (erasedProductSqMajorant_pos polynomials target interval)
  lower := by
    intro t lower upper
    let remainder := nonzeroPolynomialProduct (polynomials.erase target)
    let majorant := erasedProductSqMajorant polynomials target interval
    have productLower := productCertificate.lower t lower upper
    have productIdentity := nonzeroPolynomialProduct_eval_eq_mul_erase
      polynomials target member targetNonzero t
    have remainderUpper : remainder.eval t ^ 2 ≤ majorant := by
      exact erasedProduct_eval_sq_le_majorant polynomials target interval
        lower upper
    have targetNonnegative : 0 ≤ target.eval t ^ 2 := sq_nonneg _
    have productEvalIdentity :
        (nonzeroPolynomialProduct polynomials).eval t =
          target.eval t * remainder.eval t := by
      simpa [remainder] using productIdentity
    have scaled : productCertificate.bound ≤ target.eval t ^ 2 * majorant := by
      calc
        productCertificate.bound ≤ target.eval t ^ 2 * remainder.eval t ^ 2 := by
          rw [← mul_pow, ← productEvalIdentity]
          exact productLower
        _ ≤ target.eval t ^ 2 * majorant :=
          mul_le_mul_of_nonneg_left remainderUpper targetNonnegative
    apply (div_le_iff₀
      (erasedProductSqMajorant_pos polynomials target interval)).2
    simpa [majorant, mul_comm] using scaled

/-- On an all-interior common cell, multiply the exact factor lower bounds
and restore the decomposition scalar to obtain a positive lower bound for the
whole combined arc guard. -/
def computeArcGuardClearance
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (decomposition : Decomposition (arcGuard p path box))
    (cell : CommonFactorCell decomposition.factors)
    (allInterior : cell.leaves.allInterior = true) :
    PositiveLowerBound.Certificate (arcGuard p path box) cell.interval := by
  have productLower :
      (factorProduct decomposition.factors).eval cell.interval.lower ≠ 0 :=
    factorProduct_eval_ne_zero_of_eventGuard cell.lowerClear
  have productUpper :
      (factorProduct decomposition.factors).eval cell.interval.upper ≠ 0 :=
    factorProduct_eval_ne_zero_of_eventGuard cell.upperClear
  have countsZero := cell.leaves.count_eq_zero_of_allInterior allInterior
  let productCertificate := PositiveLowerBound.computeFactorProduct
    decomposition.factors cell.interval cell.proper productLower productUpper
    countsZero
  exact PositiveLowerBound.Certificate.ofScalarProduct decomposition.scalar
    decomposition.scalar_ne_zero productCertificate decomposition.eval_identity

/-- A zero-event cell with a computed positive lower bound for the entire
combined guard. -/
structure ClearGuardCell
    (p : GaussianPolynomial) (path : Path) (box : RatBox) where
  interval : RationalInterval
  proper : interval.Proper
  certificate : PositiveLowerBound.Certificate
    (arcGuard p path box) interval

/-- Extract a positive squared-value certificate for any displayed nonzero
member of the combined guard. -/
def ClearGuardCell.memberCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (cell : ClearGuardCell p path box) (target : RatPolynomial)
    (member : target ∈ arcPolynomials p path box)
    (targetNonzero : target.isZero = false) :
    PositiveLowerBound.Certificate target cell.interval :=
  memberCertificateOfProduct (arcPolynomials p path box) target cell.interval
    member targetNonzero cell.certificate

/-- The combined guard lower bound yields the positive projective-denominator
certificate consumed by the affine intersection sampler. -/
def ClearGuardCell.denominatorCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (cell : ClearGuardCell p path box)
    (denominatorNonzero : (denominatorNorm path).isZero = false) :
    DenominatorCertificate path cell.interval := by
  let squared := cell.memberCertificate (denominatorNorm path)
    (denominatorNorm_mem_arcPolynomials p path box) denominatorNonzero
  exact
    { bound := min squared.bound 1
      positive := lt_min squared.positive zero_lt_one
      lower := by
        intro t lower upper
        have squareLower := squared.lower t lower upper
        have valueNonnegative : 0 ≤ (denominatorNorm path).eval t := by
          rw [eval_denominatorNorm]
          exact normSq_nonneg _
        by_cases oneLe : 1 ≤ (denominatorNorm path).eval t
        · exact (min_le_right _ _).trans oneLe
        · have valueLeOne : (denominatorNorm path).eval t ≤ 1 :=
            le_of_not_ge oneLe
          exact (min_le_left _ _).trans (squareLower.trans (by
            nlinarith)) }

/-- The combined guard lower bound, together with the executable Bézout
certificate for the gcd-reduced cleared coordinates, yields a direct positive
lower bound for their squared sum. -/
def ClearGuardCell.clearedCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (cell : ClearGuardCell p path box)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    PathClearance.Certificate (clearedReal p path) (clearedImag p path)
      cell.interval := by
  let common := PathClearance.commonFactor
    (clearedReal p path) (clearedImag p path)
  have commonNonzero : common.isZero = false :=
    PathClearance.commonFactor_isZero_false clearedNonzero
  let commonCertificate := cell.memberCertificate common
    (commonFactor_mem_arcPolynomials p path box) commonNonzero
  let reducedCertificate := PathClearance.certificateOfCoprime
    (PathClearance.reducedPairCertificate
      (clearedReal p path) (clearedImag p path) clearedNonzero)
    cell.interval
  exact
    { bound := commonCertificate.bound * reducedCertificate.bound
      positive := mul_pos commonCertificate.positive reducedCertificate.positive
      lower := by
        intro t lower upper
        have commonLower := commonCertificate.lower t lower upper
        have reducedLower := reducedCertificate.lower t lower upper
        have realIdentity : (clearedReal p path).eval t =
            common.eval t *
              (PathClearance.reducedReal
                (clearedReal p path) (clearedImag p path)).eval t := by
          simpa [common] using
            PathClearance.commonFactor_mul_reducedReal_eval
              (clearedReal p path) (clearedImag p path) t
        have imagIdentity : (clearedImag p path).eval t =
            common.eval t *
              (PathClearance.reducedImag
                (clearedReal p path) (clearedImag p path)).eval t := by
          simpa [common] using
            PathClearance.commonFactor_mul_reducedImag_eval
              (clearedReal p path) (clearedImag p path) t
        calc
          commonCertificate.bound * reducedCertificate.bound ≤
              common.eval t ^ 2 *
                ((PathClearance.reducedReal
                  (clearedReal p path) (clearedImag p path)).eval t ^ 2 +
                 (PathClearance.reducedImag
                  (clearedReal p path) (clearedImag p path)).eval t ^ 2) :=
            mul_le_mul commonLower reducedLower reducedCertificate.positive.le
              (sq_nonneg _)
          _ = (clearedReal p path).eval t ^ 2 +
                (clearedImag p path).eval t ^ 2 := by
            rw [realIdentity, imagIdentity]
            ring }

/-- The same synchronized clear-cell guard also supplies the affine
clearance used by the zero-count side of the branch decision. -/
def ClearGuardCell.affineCertificate
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (cell : ClearGuardCell p path box)
    (clearedNonzero : (clearedReal p path).isZero = false ∨
      (clearedImag p path).isZero = false) :
    ProjectivePathBounds.AffineCertificate p path cell.interval :=
  ProjectivePathBounds.affineCertificateOfCleared p path cell.interval
    (cell.clearedCertificate clearedNonzero)

/-- A synchronized common cell containing at least one first-member guard
event. -/
structure EventGuardCell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (decomposition : Decomposition (arcGuard p path box)) where
  cell : CommonFactorCell decomposition.factors
  hasEvent : cell.leaves.allInterior = false

/-- Every count-one guard factor carried by this terminal cell, retained as
an executable finite family rather than an existential choice. -/
def EventGuardCell.eventIntervals
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    List (FactorCountOneInterval decomposition.factors) :=
  cell.cell.leaves.eventIntervals

theorem EventGuardCell.eventIntervals_ne_nil
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    cell.eventIntervals ≠ [] :=
  (cell.cell.leaves.eventIntervals_ne_nil_iff).2 cell.hasEvent

/-- The executable count-one list of a terminal guard cell covers every exact
rational zero of the combined arc guard in that cell, not merely some event
whose existence made the cell terminal. -/
theorem EventGuardCell.eventIntervals_covers_guard_zero
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) {t : ℚ}
    (lower : cell.cell.interval.lower ≤ t)
    (upper : t ≤ cell.cell.interval.upper)
    (guardZero : (arcGuard p path box).eval t = 0) :
    ∃ entry ∈ cell.eventIntervals,
      entry.root.interval.lower ≤ t ∧
        t ≤ entry.root.interval.upper ∧
        entry.factor.polynomial.eval t = 0 := by
  have productZero :
      (factorProduct decomposition.factors).eval t = 0 := by
    rw [decomposition.eval_identity] at guardZero
    exact (mul_eq_zero.mp guardZero).resolve_left decomposition.scalar_ne_zero
  rcases exists_factor_eval_eq_zero_of_factorProduct_eval_eq_zero productZero with
    ⟨factor, factorMember, factorZero⟩
  rcases cell.cell.leaves.eventIntervals_covers_rational_zero factorMember
      lower upper factorZero with
    ⟨entry, entryMember, factorEquality, entryLower, entryUpper⟩
  refine ⟨entry, entryMember, entryLower, entryUpper, ?_⟩
  rw [factorEquality]
  exact factorZero

/-- An event guard cell carries a named squarefree guard factor with one
local real event, not merely a failed Boolean classification. -/
theorem EventGuardCell.exists_factor_count_eq_two
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    ∃ factor ∈ decomposition.factors,
      FTA.Sturm.sturmRootCount2 factor.polynomial cell.cell.interval.lower
        cell.cell.interval.upper = 2 :=
  cell.cell.leaves.exists_count_eq_two_of_allInterior_eq_false cell.hasEvent

/-- The named positive factor can be packaged as the ordinary count-one
interval consumed by the algebraic event-classification pipeline. -/
theorem EventGuardCell.exists_countOneInterval
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)}
    (cell : EventGuardCell decomposition) :
    ∃ factor ∈ decomposition.factors,
      ∃ root : CountOneInterval factor.polynomial,
        root.interval = cell.cell.interval := by
  rcases cell.exists_factor_count_eq_two with
    ⟨factor, factorMember, positiveCount⟩
  let root : CountOneInterval factor.polynomial :=
    { interval := cell.cell.interval
      proper := cell.cell.proper
      countOne := positiveCount
      lowerClear := factor_eval_ne_zero_of_eventGuard factorMember
        cell.cell.lowerClear
      upperClear := factor_eval_ne_zero_of_eventGuard factorMember
        cell.cell.upperClear }
  exact ⟨factor, factorMember, root, rfl⟩

/-- Exact executable decision on one terminal common cell. -/
inductive GuardCellDecision
    (p : GaussianPolynomial) (path : Path) (box : RatBox)
    (decomposition : Decomposition (arcGuard p path box)) where
  | clear (cell : ClearGuardCell p path box)
  | event (cell : EventGuardCell decomposition)

/-- Parameter interval retained by either terminal guard-cell decision. -/
def GuardCellDecision.interval
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {decomposition : Decomposition (arcGuard p path box)} :
    GuardCellDecision p path box decomposition → RationalInterval
  | .clear cell => cell.interval
  | .event cell => cell.cell.interval

def decideGuardCell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (decomposition : Decomposition (arcGuard p path box))
    (cell : CommonFactorCell decomposition.factors) :
    GuardCellDecision p path box decomposition := by
  if allInterior : cell.leaves.allInterior = true then
    exact .clear
      { interval := cell.interval
        proper := cell.proper
        certificate := computeArcGuardClearance decomposition cell allInterior }
  else
    have hasEvent : cell.leaves.allInterior = false := by
      exact Bool.eq_false_of_not_eq_true allInterior
    exact .event ⟨cell, hasEvent⟩

@[simp] theorem decideGuardCell_interval
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    (decomposition : Decomposition (arcGuard p path box))
    (cell : CommonFactorCell decomposition.factors) :
    (decideGuardCell decomposition cell).interval = cell.interval := by
  unfold decideGuardCell
  split <;> rfl

/-- Flatten and decide every synchronized terminal cell of a factored guard
partition. -/
def decideGuardCells
    {p : GaussianPolynomial} {path : Path} {box : RatBox} {core : RationalInterval}
    (decomposition : Decomposition (arcGuard p path box))
    {root : GuardedRoot decomposition.factors core}
    (partition : CommonFactorPartition decomposition.factors root.interval) :
    List (GuardCellDecision p path box decomposition) :=
  partition.cells.map fun cell => decideGuardCell decomposition cell

/-- The decided terminal cells still cover the complete guarded root
interval after the clear/event classification is attached. -/
theorem decideGuardCells_cover
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    (decomposition : Decomposition (arcGuard p path box))
    {root : GuardedRoot decomposition.factors core}
    (partition : CommonFactorPartition decomposition.factors root.interval)
    {t : ℚ} (lower : root.interval.lower ≤ t)
    (upper : t ≤ root.interval.upper) :
    ∃ decision ∈ decideGuardCells decomposition partition,
      decision.interval.lower ≤ t ∧ t ≤ decision.interval.upper := by
  rcases partition.cells_cover lower upper with
    ⟨cell, member, cellLower, cellUpper⟩
  let decision := decideGuardCell decomposition cell
  refine ⟨decision, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨cell, member, rfl⟩
  · simpa only [decision, decideGuardCell_interval] using cellLower
  · simpa only [decision, decideGuardCell_interval] using cellUpper

/-- Membership in the decided terminal family retains refinement into the
guarded outer interval, independently of the clear/event constructor. -/
theorem GuardCellDecision.interval_refines_of_mem_decide
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    (decomposition : Decomposition (arcGuard p path box))
    {root : GuardedRoot decomposition.factors core}
    (partition : CommonFactorPartition decomposition.factors root.interval)
    (decision : GuardCellDecision p path box decomposition)
    (member : decision ∈ decideGuardCells decomposition partition) :
    decision.interval.Refines root.interval := by
  rw [decideGuardCells, List.mem_map] at member
  rcases member with ⟨cell, cellMember, equality⟩
  have refines := partition.cell_refines cell cellMember
  have intervalEquality : decision.interval = cell.interval := by
    rw [← equality, decideGuardCell_interval]
  rw [intervalEquality]
  exact refines

/-- Retain the quantitative all-interior cells of a complete chart plan.
The constant nonzero guard case is represented by the entire bounded chart
interval and its direct constant lower-bound certificate. -/
def clearGuardCellsOfPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} (coreProper : core.Proper) :
    ArcPartitionPlan p path box core → List (ClearGuardCell p path box)
  | .constant degreeZero =>
      [{ interval := core
         proper := coreProper
         certificate := PositiveLowerBound.Certificate.ofConstant
           (arcGuard_isZero_false p path box) degreeZero core }]
  | .factored decomposition _root partition =>
      (decideGuardCells decomposition partition).filterMap fun decision =>
        match decision with
        | .clear cell => some cell
        | .event _ => none

/-- A terminal event cell packaged against the total plan that produced it. -/
structure PlanEventGuardCell
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} (plan : ArcPartitionPlan p path box core) where
  decomposition : Decomposition (arcGuard p path box)
  root : GuardedRoot decomposition.factors core
  partition : CommonFactorPartition decomposition.factors root.interval
  planEquality : plan = .factored decomposition root partition
  cell : EventGuardCell decomposition
  decisionMember : (GuardCellDecision.event cell) ∈
    decideGuardCells decomposition partition

theorem PlanEventGuardCell.cell_refines_root
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} {plan : ArcPartitionPlan p path box core}
    (item : PlanEventGuardCell plan) :
    item.cell.cell.interval.Refines item.root.interval :=
  GuardCellDecision.interval_refines_of_mem_decide item.decomposition
    item.partition (.event item.cell) item.decisionMember

/-- Retain every guarded-event half of a total chart partition. -/
def eventGuardCellsOfPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} :
    (plan : ArcPartitionPlan p path box core) →
      List (PlanEventGuardCell plan)
  | .constant _ => []
  | .factored decomposition root partition =>
      (decideGuardCells decomposition partition).attach.filterMap fun entry =>
        match entry with
        | ⟨.clear _, _⟩ => none
        | ⟨.event cell, decisionMember⟩ => some
            { decomposition := decomposition
              root := root
              partition := partition
              planEquality := rfl
              cell := cell
              decisionMember := decisionMember }

/-- Constructive pointwise coverage of a total guarded plan.  The constant
case and every all-interior terminal cell produce quantitative clearance;
the only alternative is an explicitly retained first-member event cell. -/
inductive GuardCellCoverage
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} (coreProper : core.Proper) :
    (plan : ArcPartitionPlan p path box core) → (t : ℚ) → Prop where
  | clear {plan : ArcPartitionPlan p path box core} {t : ℚ}
      (cell : ClearGuardCell p path box)
      (member : cell ∈ clearGuardCellsOfPlan coreProper plan)
      (lower : cell.interval.lower ≤ t)
      (upper : t ≤ cell.interval.upper) :
      GuardCellCoverage coreProper plan t
  | event
      {plan : ArcPartitionPlan p path box core}
      {decomposition : Decomposition (arcGuard p path box)}
      {root : GuardedRoot decomposition.factors core}
      {partition : CommonFactorPartition decomposition.factors root.interval}
      {t : ℚ}
      (planEquality : plan = .factored decomposition root partition)
      (cell : EventGuardCell decomposition)
      (member : (GuardCellDecision.event cell) ∈
        decideGuardCells decomposition partition)
      (lower : cell.cell.interval.lower ≤ t)
      (upper : t ≤ cell.cell.interval.upper) :
      GuardCellCoverage coreProper plan t

/-- The event-only half of `GuardCellCoverage`, retaining the exact factored
plan and terminal event cell that caused the alternative. -/
inductive GuardEventCoverage
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} :
    (plan : ArcPartitionPlan p path box core) → (t : ℚ) → Prop where
  | event
      {plan : ArcPartitionPlan p path box core}
      {decomposition : Decomposition (arcGuard p path box)}
      {root : GuardedRoot decomposition.factors core}
      {partition : CommonFactorPartition decomposition.factors root.interval}
      {t : ℚ}
      (planEquality : plan = .factored decomposition root partition)
      (cell : EventGuardCell decomposition)
      (member : (GuardCellDecision.event cell) ∈
        decideGuardCells decomposition partition)
      (lower : cell.cell.interval.lower ≤ t)
      (upper : t ≤ cell.cell.interval.upper) :
      GuardEventCoverage plan t

/-- Fully exposed algebraic payload of one guarded-event alternative. -/
inductive PositiveGuardFactorCoverage
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval}
    (plan : ArcPartitionPlan p path box core) (t : ℚ) : Prop where
  | intro
      {decomposition : Decomposition (arcGuard p path box)}
      {root : GuardedRoot decomposition.factors core}
      {partition : CommonFactorPartition decomposition.factors root.interval}
      (planEquality : plan = .factored decomposition root partition)
      (cell : EventGuardCell decomposition)
      (decisionMember : (GuardCellDecision.event cell) ∈
        decideGuardCells decomposition partition)
      (lower : cell.cell.interval.lower ≤ t)
      (upper : t ≤ cell.cell.interval.upper)
      (factor : Factor) (factorMember : factor ∈ decomposition.factors)
      (positiveCount : FTA.Sturm.sturmRootCount2 factor.polynomial
        cell.cell.interval.lower cell.cell.interval.upper = 2) :
      PositiveGuardFactorCoverage plan t

/-- Event-only coverage always names the positive-count squarefree guard
factor responsible for the event cell. -/
theorem GuardEventCoverage.positiveFactor
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} {plan : ArcPartitionPlan p path box core}
    {t : ℚ} (coverage : GuardEventCoverage plan t) :
    PositiveGuardFactorCoverage plan t := by
  cases coverage with
  | event planEquality cell decisionMember lower upper =>
      rcases cell.exists_factor_count_eq_two with
        ⟨factor, factorMember, positiveCount⟩
      exact .intro planEquality cell decisionMember lower upper factor
        factorMember positiveCount

/-- Event-only point coverage is represented by a member of the executable
event-cell family of the same total plan. -/
theorem GuardEventCoverage.mem_eventGuardCellsOfPlan
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} {plan : ArcPartitionPlan p path box core}
    {t : ℚ} (coverage : GuardEventCoverage plan t) :
    ∃ item ∈ eventGuardCellsOfPlan plan,
      item.cell.cell.interval.lower ≤ t ∧
      t ≤ item.cell.cell.interval.upper := by
  cases coverage with
  | @event decomposition root partition t planEquality cell
      decisionMember lower upper =>
      subst plan
      let item : PlanEventGuardCell
          (p := p) (path := path) (box := box) (core := core)
          (.factored decomposition root partition) :=
        { decomposition := decomposition
          root := root
          partition := partition
          planEquality := rfl
          cell := cell
          decisionMember := decisionMember }
      refine ⟨item, ?_, lower, upper⟩
      rw [eventGuardCellsOfPlan, List.mem_filterMap]
      exact ⟨⟨.event cell, decisionMember⟩, by simp, rfl⟩

/-- Every rational parameter of the original bounded chart interval has one
of the two terminal-cell witnesses above. -/
theorem ArcPartitionPlan.guardCellCoverage
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {core : RationalInterval} (coreProper : core.Proper)
    (plan : ArcPartitionPlan p path box core) {t : ℚ}
    (lower : core.lower ≤ t) (upper : t ≤ core.upper) :
    GuardCellCoverage coreProper plan t := by
  cases plan with
  | constant degreeZero =>
      let cell : ClearGuardCell p path box :=
        { interval := core
          proper := coreProper
          certificate := PositiveLowerBound.Certificate.ofConstant
            (arcGuard_isZero_false p path box) degreeZero core }
      exact .clear cell (by
        simp [clearGuardCellsOfPlan, cell]) lower upper
  | factored decomposition root partition =>
      rcases decideGuardCells_cover decomposition partition
          (root.coreRefines.1.trans lower)
          (upper.trans root.coreRefines.2) with
        ⟨decision, decisionMember, decisionLower, decisionUpper⟩
      cases decision with
      | clear cell =>
          exact .clear cell (by
            rw [clearGuardCellsOfPlan, List.mem_filterMap]
            exact ⟨.clear cell, decisionMember, rfl⟩)
            decisionLower decisionUpper
      | event cell =>
          exact .event rfl cell decisionMember decisionLower decisionUpper

/-- Specialization from a proof-bearing bounded chart to its total guarded
partition plan. -/
def buildChartPartitionPlan
    (p : GaussianPolynomial) (box : RatBox)
    {source : CCLBranchPlan.BoundarySource}
    (chart : CCLBranchCharts.BoundedChart source) :
    ArcPartitionPlan p chart.path box chart.interval :=
  buildArcPartitionPlan p chart.path box chart.interval chart.proper

/-- A source-labelled chart together with its fully computed guarded
partition. -/
structure SourceChartPartition
    (p : GaussianPolynomial) (box : RatBox) where
  entry : CCLBranchCharts.SourceChart
  plan : ArcPartitionPlan p entry.chart.path box entry.chart.interval

/-- A source-labelled terminal event cell from one bounded chart plan. -/
structure SourceEventGuardCell
    (p : GaussianPolynomial) (box : RatBox) where
  partition : SourceChartPartition p box
  item : PlanEventGuardCell partition.plan

def eventGuardCellsOfSourcePartition
    {p : GaussianPolynomial} {box : RatBox}
    (partition : SourceChartPartition p box) :
    List (SourceEventGuardCell p box) :=
  (eventGuardCellsOfPlan partition.plan).map fun item =>
    ⟨partition, item⟩

def eventGuardCellsOfSourcePartitions
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box)) :
    List (SourceEventGuardCell p box) :=
  partitions.flatMap eventGuardCellsOfSourcePartition

/-- A flattened terminal event cell retains membership of its labelled source
partition in the input family. -/
theorem SourceEventGuardCell.partition_mem_of_mem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {sourceCell : SourceEventGuardCell p box}
    (member : sourceCell ∈ eventGuardCellsOfSourcePartitions partitions) :
    sourceCell.partition ∈ partitions := by
  rw [eventGuardCellsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨partition, partitionMember, cellMember⟩
  rw [eventGuardCellsOfSourcePartition, List.mem_map] at cellMember
  rcases cellMember with ⟨cell, _cellMember, equality⟩
  cases equality
  exact partitionMember

/-- A pointwise guarded-event witness survives source-labelled flattening. -/
theorem GuardEventCoverage.mem_eventGuardCellsOfSourcePartitions
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {partition : SourceChartPartition p box}
    (partitionMember : partition ∈ partitions) {t : ℚ}
    (coverage : GuardEventCoverage partition.plan t) :
    ∃ sourceCell ∈ eventGuardCellsOfSourcePartitions partitions,
      sourceCell.partition = partition ∧
      sourceCell.item.cell.cell.interval.lower ≤ t ∧
      t ≤ sourceCell.item.cell.cell.interval.upper := by
  rcases coverage.mem_eventGuardCellsOfPlan with
    ⟨item, itemMember, lower, upper⟩
  let sourceCell : SourceEventGuardCell p box := ⟨partition, item⟩
  refine ⟨sourceCell, ?_, rfl, lower, upper⟩
  rw [eventGuardCellsOfSourcePartitions, List.mem_flatMap]
  refine ⟨partition, partitionMember, ?_⟩
  rw [eventGuardCellsOfSourcePartition, List.mem_map]
  exact ⟨item, itemMember, rfl⟩

/-- A source/chart label retained alongside one quantitative all-interior
terminal cell. -/
structure SourceClearGuardCell
    (p : GaussianPolynomial) (box : RatBox) where
  partition : SourceChartPartition p box
  cell : ClearGuardCell p partition.entry.chart.path box

def clearGuardCellsOfSourcePartition
    {p : GaussianPolynomial} {box : RatBox}
    (partition : SourceChartPartition p box) :
    List (SourceClearGuardCell p box) :=
  (clearGuardCellsOfPlan partition.entry.chart.proper partition.plan).map
    fun cell => ⟨partition, cell⟩

def clearGuardCellsOfSourcePartitions
    {p : GaussianPolynomial} {box : RatBox}
    (partitions : List (SourceChartPartition p box)) :
    List (SourceClearGuardCell p box) :=
  partitions.flatMap clearGuardCellsOfSourcePartition

/-- A flattened clear cell retains membership of its labelled source
partition in the input family. -/
theorem SourceClearGuardCell.partition_mem_of_mem
    {p : GaussianPolynomial} {box : RatBox}
    {partitions : List (SourceChartPartition p box)}
    {sourceCell : SourceClearGuardCell p box}
    (member : sourceCell ∈ clearGuardCellsOfSourcePartitions partitions) :
    sourceCell.partition ∈ partitions := by
  rw [clearGuardCellsOfSourcePartitions, List.mem_flatMap] at member
  rcases member with ⟨partition, partitionMember, cellMember⟩
  rw [clearGuardCellsOfSourcePartition, List.mem_map] at cellMember
  rcases cellMember with ⟨cell, _cellMember, equality⟩
  cases equality
  exact partitionMember

/-- Map the total guarded partition constructor across an arbitrary finite
source-chart family. -/
def buildSourceChartPartitions
    (p : GaussianPolynomial) (box : RatBox)
    (entries : List CCLBranchCharts.SourceChart) :
    List (SourceChartPartition p box) :=
  entries.map fun entry =>
    ⟨entry, buildChartPartitionPlan p box entry.chart⟩

/-- Mapping the partition constructor loses no chart: every input entry has
an equal source-labelled partition in the built family. -/
theorem SourceChartPartition.exists_mem_build_of_entry_mem
    {p : GaussianPolynomial} {box : RatBox}
    {entries : List CCLBranchCharts.SourceChart}
    {entry : CCLBranchCharts.SourceChart} (member : entry ∈ entries) :
    ∃ partition ∈ buildSourceChartPartitions p box entries,
      partition.entry = entry := by
  let partition : SourceChartPartition p box :=
    ⟨entry, buildChartPartitionPlan p box entry.chart⟩
  refine ⟨partition, ?_, rfl⟩
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- A built partition's source chart came from the finite input chart
family. -/
theorem SourceChartPartition.entry_mem_of_mem_build
    {p : GaussianPolynomial} {box : RatBox}
    {entries : List CCLBranchCharts.SourceChart}
    {partition : SourceChartPartition p box}
    (member : partition ∈ buildSourceChartPartitions p box entries) :
    partition.entry ∈ entries := by
  rw [buildSourceChartPartitions, List.mem_map] at member
  rcases member with ⟨entry, entryMember, equality⟩
  cases equality
  exact entryMember

@[simp] theorem buildSourceChartPartitions_length
    (p : GaussianPolynomial) (box : RatBox)
    (entries : List CCLBranchCharts.SourceChart) :
    (buildSourceChartPartitions p box entries).length = entries.length := by
  simp [buildSourceChartPartitions]

theorem buildSourceChartPartitions_ne_nil
    (p : GaussianPolynomial) (box : RatBox)
    {entries : List CCLBranchCharts.SourceChart} (nonempty : entries ≠ []) :
    buildSourceChartPartitions p box entries ≠ [] := by
  simpa [buildSourceChartPartitions] using nonempty

end CCLBranchPartition
end FTA
