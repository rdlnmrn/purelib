import RFAP.Winding.Homotopy
import RFAP.Winding.Global

/-!
# Constructive winding on finite closed polygonal walks

The box winding developed earlier is sufficient for root counting, but a
finite monodromy calculation also has to follow one displayed rational sample
through a finite chain of owner boxes.  The resulting trace is a polygonal
walk rather than the boundary of one rectangle.

This file folds the existing affine-edge Cauchy index over an explicit list
of rational Gaussian vertices.  Product and Rouché endpoint corrections are
kept locally and telescope only because the list is explicitly closed.  No
completed curve, limiting path, or topological winding construction occurs.
-/

namespace RFAP.PolygonWinding

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathPolynomial
open RFAP.Winding
open RFAP.PathClearance
open RFAP.SafeCandidates
open RFAP.CauchyProductSigns
open RFAP.CauchyCells
open RFAP.CauchyResolution

/-! ## Finite polygonal walks -/

/-- The affine segment from `start` to `finish`, with displayed parameter
interval `[0,1]`. -/
def segment (p : GaussianPolynomial) (start finish : Gaussian) :
    PolynomialEdge :=
  PolynomialEdge.ofLine p start (finish - start) 0 1

@[simp] theorem line_segment_zero (start finish : Gaussian) :
    line start (finish - start) 0 = start := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [line, ofCoordinate, add_re, add_im, mul_re, mul_im,
      sub_re, sub_im] <;>
    ring1

@[simp] theorem line_segment_one (start finish : Gaussian) :
    line start (finish - start) 1 = finish := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [line, ofCoordinate, add_re, add_im, mul_re, mul_im,
      sub_re, sub_im] <;>
    ring1

/-- Raw winding along a finite open chain.  The list contains the successive
target vertices and `start` is its current source vertex. -/
def chainRaw (p : GaussianPolynomial) : Gaussian → List Gaussian → Int
  | _, [] => 0
  | start, finish :: remaining =>
      (segment p start finish).doubledWinding +
        chainRaw p finish remaining

/-- Terminal vertex of the same finite open chain. -/
def terminal : Gaussian → List Gaussian → Gaussian
  | start, [] => start
  | _, finish :: remaining => terminal finish remaining

/-- Raw winding of the explicitly closed polygon obtained by returning from
the last displayed vertex to `base`. -/
def closedRaw (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian) : Int :=
  chainRaw p base (vertices ++ [base])

/-- A nonzero constant Gaussian polynomial contributes zero raw winding to
every finite open polygonal chain. -/
theorem chainRaw_gaussianConstant_zero
    {constantValue : Gaussian} (nonzero : constantValue ≠ 0) :
    ∀ (start : Gaussian) (vertices : List Gaussian),
      chainRaw (RFAP.GlobalWinding.gaussianConstant constantValue)
        start vertices = 0
  | _, [] => rfl
  | start, finish :: remaining => by
      simp only [chainRaw, segment]
      rw [RFAP.GlobalWinding.gaussianConstant_edge_winding_zero
        nonzero start (finish - start) 0 1,
        chainRaw_gaussianConstant_zero nonzero finish remaining,
        Int.zero_add]

/-- A stationary coordinate segment contributes no Cauchy index. -/
@[simp] theorem coordinate_segment_self_doubledWinding
    (point : Gaussian) :
    (segment RFAP.GlobalWinding.coordinatePolynomial point point).doubledWinding =
      0 := by
  unfold segment PolynomialEdge.doubledWinding PolynomialEdge.ofLine
    pathReal pathImag realPart imagPart composeLine composeLineCoeffs
    RFAP.GlobalWinding.coordinatePolynomial mulLine
  simp only [List.foldl_cons, List.foldl_nil,
    scale_zero_right, shift_zero, zero_add_normalize,
    normalize_zero]
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self]
  rw [normalize_constant_of_ne one_ne_zero]
  simp only [scale_constant,
    RFAP.ConstructiveGaussian.Gaussian.mul_one,
    shift_zero, add_zero_normalize, normalize_constant_zero]
  rw [normalize_normalize, add_constant_zero, normalize_normalize]
  by_cases pointZero : point = 0
  · subst point
    simp only [normalize_constant_zero]
    rfl
  · rw [normalize_constant_of_ne pointZero]
    change RFAP.Sturm.cauchyIndex2 (constant point.re)
      (constant point.im) 0 1 = 0
    by_cases realZero : point.re = 0
    · have secondZero : (constant point.re).isZero = true := by
        simp [realZero, isZero, normalize]
      unfold RFAP.Sturm.cauchyIndex2
      rw [RFAP.Sturm.signedRemainderChain,
        RFAP.Sturm.signedRemainderChainWF_eq]
      simp only [secondZero, ↓reduceIte, RFAP.Sturm.endpointVariation2,
        List.map_cons, List.map_nil, eval_constant]
      exact Int.sub_self _
    · have secondNonzero : (constant point.re).isZero = false := by
        simp [isZero, normalize, realZero]
      have secondCount : (constant point.re).degreeCount = 1 := by
        have positive := degreeCount_pos_of_isZero_false secondNonzero
        have atMostOne := degreeCount_constant_le_one point.re
        omega
      rw [RFAP.Sturm.cauchyIndex2,
        RFAP.Sturm.signedRemainderChain_eq_pair_of_second_degreeCount_one
          secondNonzero secondCount]
      simp only [RFAP.Sturm.endpointVariation2, List.map_cons, List.map_nil,
        eval_constant]
      exact Int.sub_self _

/-- Consecutive copies of the current vertex are semantically stationary
and can be removed from an open polygonal chain. -/
@[simp] theorem coordinate_chainRaw_cons_self
    (point : Gaussian)
    (remaining : List Gaussian) :
    chainRaw RFAP.GlobalWinding.coordinatePolynomial point
        (point :: remaining) =
      chainRaw RFAP.GlobalWinding.coordinatePolynomial point remaining := by
  simp only [chainRaw, coordinate_segment_self_doubledWinding, Int.zero_add]

@[simp] theorem terminal_cons_self
    (point : Gaussian) (remaining : List Gaussian) :
    terminal point (point :: remaining) = terminal point remaining := rfl

theorem terminal_append :
    ∀ (start : Gaussian) (first second : List Gaussian),
      terminal start (first ++ second) =
        terminal (terminal start first) second
  | start, [], second => rfl
  | start, finish :: remaining, second => by
      simp only [List.cons_append, terminal]
      exact terminal_append finish remaining second

theorem chainRaw_append (p : GaussianPolynomial) :
    ∀ (start : Gaussian) (first second : List Gaussian),
      chainRaw p start (first ++ second) =
        chainRaw p start first +
          chainRaw p (terminal start first) second
  | start, [], second => by
      simp only [List.nil_append, chainRaw, terminal]
      rw [Int.zero_add]
  | start, finish :: remaining, second => by
      simp only [List.cons_append, chainRaw, terminal]
      rw [chainRaw_append p finish remaining second]
      ring1

/-! ## Open half-plane chains -/

/-- The endpoint quadrant correction in the right-half-plane formula. -/
def vertexHalfPlaneCorrection2 (p : GaussianPolynomial)
    (point : Gaussian) : Nat :=
  RFAP.Sturm.signJump 1 ((p.eval point).re * (p.eval point).im)

/-- One right-half-plane formula for every edge of an open polygonal
chain. -/
inductive ChainHalfPlaneFormula (p : GaussianPolynomial) :
    Gaussian → List Gaussian → Prop
  | nil (start : Gaussian) : ChainHalfPlaneFormula p start []
  | cons {start finish : Gaussian} {remaining : List Gaussian}
      (edge : RFAP.HalfPlane.Formula
        (pathReal p start (finish - start))
        (pathImag p start (finish - start)) 0 1)
      (tail : ChainHalfPlaneFormula p finish remaining) :
      ChainHalfPlaneFormula p start (finish :: remaining)

theorem ChainHalfPlaneFormula.append
    {p : GaussianPolynomial} :
    ∀ {start : Gaussian} {vertices remaining : List Gaussian},
      ChainHalfPlaneFormula p start vertices →
        ChainHalfPlaneFormula p (terminal start vertices) remaining →
        ChainHalfPlaneFormula p start (vertices ++ remaining)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons edge rest, tail =>
      .cons edge (rest.append tail)

/-- Half-plane edge formulas telescope to the two endpoint quadrant
corrections of an open chain. -/
theorem chainRaw_eq_endpoint_corrections_of_halfPlane
    (p : GaussianPolynomial) :
    ∀ (start : Gaussian) (vertices : List Gaussian),
      ChainHalfPlaneFormula p start vertices →
        chainRaw p start vertices =
          (vertexHalfPlaneCorrection2 p start : Int) -
            vertexHalfPlaneCorrection2 p (terminal start vertices)
  | start, [], .nil _ => by
      simp only [chainRaw, terminal]
      ring1
  | start, finish :: remaining, .cons edge tail => by
      have tailIdentity :=
        chainRaw_eq_endpoint_corrections_of_halfPlane p finish remaining tail
      unfold RFAP.HalfPlane.Formula at edge
      simp only [chainRaw, terminal, segment, PolynomialEdge.doubledWinding]
      dsimp only [PolynomialEdge.ofLine] at edge ⊢
      simp only [eval_pathReal, eval_pathImag, line_segment_zero,
        line_segment_one] at edge
      unfold vertexHalfPlaneCorrection2 at tailIdentity ⊢
      rw [edge, tailIdentity]
      ring1

@[simp] theorem terminal_append_singleton
    (start base : Gaussian) (vertices : List Gaussian) :
    terminal start (vertices ++ [base]) = base := by
  induction vertices generalizing start with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, terminal]
      exact inductionHypothesis head

/-- A closed finite polygon retained in the open right half-plane has raw
winding zero. -/
theorem closedRaw_eq_zero_of_halfPlane
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian)
    (formula : ChainHalfPlaneFormula p base (vertices ++ [base])) :
    closedRaw p base vertices = 0 := by
  unfold closedRaw
  rw [chainRaw_eq_endpoint_corrections_of_halfPlane p base
    (vertices ++ [base]) formula, terminal_append_singleton]
  ring1

/-! ## Modulo-four phase normalization -/

/-- Integer phase of a nonzero formal coordinate pair, measured in quarter
turns.  The two open half-planes receive the odd phases and the two real
half-axes receive the even phases.  The unused zero pair is assigned zero so
that the definition remains total and executable. -/
def finiteSignQuarterPhase (real imaginary : FiniteSign) : Int :=
  match imaginary with
  | .positive => 1
  | .negative => -1
  | .zero =>
      match real with
      | .negative => 2
      | .zero => 0
      | .positive => 0

/-- Explicit correction which makes one stable finite Cauchy event into an
integer phase change plus a multiple of four. -/
def finiteSignQuarterTurns
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : FiniteSign) : Int :=
  (FiniteSign.eventIndex2 Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ -
      (finiteSignQuarterPhase Pᵣ Qᵣ -
        finiteSignQuarterPhase Pₗ Qₗ)) / 4

/-- The local modulo-four winding law is a finite table on the three formal
signs.  Stability and a nonzero center exclude precisely the impossible
rows. -/
theorem finiteSign_eventIndex2_eq_phase_change_add_four_mul
    (Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ : FiniteSign)
    (nonzero : Pₑ ≠ .zero ∨ Qₑ ≠ .zero)
    (PₗStable : FiniteSign.Stable Pₑ Pₗ)
    (QₗStable : FiniteSign.Stable Qₑ Qₗ)
    (PᵣStable : FiniteSign.Stable Pₑ Pᵣ)
    (QᵣStable : FiniteSign.Stable Qₑ Qᵣ) :
    FiniteSign.eventIndex2 Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ =
      finiteSignQuarterPhase Pᵣ Qᵣ -
        finiteSignQuarterPhase Pₗ Qₗ +
        4 * finiteSignQuarterTurns Pₑ Qₑ Pₗ Qₗ Pᵣ Qᵣ := by
  cases Pₑ <;> cases Qₑ <;> cases Pₗ <;> cases Qₗ <;>
    cases Pᵣ <;> cases Qᵣ <;>
    simp_all [FiniteSign.Stable, FiniteSign.eventIndex2,
      FiniteSign.leftEndpointIndex2, FiniteSign.value, FiniteSign.mul,
      finiteSignQuarterPhase, finiteSignQuarterTurns]

/-- Quarter-sector phase of an actual displayed polynomial pair at one
rational parameter. -/
def endpointQuarterPhase
    (R S : CoordinatePolynomial) (x : Coordinate) : Int :=
  finiteSignQuarterPhase
    (FiniteSign.ofCoordinate (R.eval x))
    (FiniteSign.ofCoordinate (S.eval x))

/-- Proof-bearing modulo-four formula on one displayed interval. -/
structure PhaseFormula
    (R S : CoordinatePolynomial) (a b : Coordinate) where
  turns : Int
  index_eq : RFAP.Sturm.cauchyIndex2 R S a b =
    endpointQuarterPhase R S b - endpointQuarterPhase R S a + 4 * turns

/-- Adjacent phase formulas telescope at their common rational endpoint. -/
def PhaseFormula.add
    {R S : CoordinatePolynomial} {a b c : Coordinate}
    (left : PhaseFormula R S a b) (right : PhaseFormula R S b c) :
    PhaseFormula R S a c where
  turns := left.turns + right.turns
  index_eq := by
    rw [RFAP.Sturm.cauchyIndex2_add R S a b c,
      left.index_eq, right.index_eq]
    ring1

/-- One resolved event already carries the complete local modulo-four phase
formula. -/
def phaseFormulaOfEvent
    {R S : CoordinatePolynomial} {interval : RFAP.PathClearance.Interval}
    (event : CauchyEventSigns R S interval) :
    PhaseFormula R S interval.lower interval.upper where
  turns := finiteSignQuarterTurns event.numerator event.denominator
    (FiniteSign.ofCoordinate (R.eval interval.lower))
    (FiniteSign.ofCoordinate (S.eval interval.lower))
    (FiniteSign.ofCoordinate (R.eval interval.upper))
    (FiniteSign.ofCoordinate (S.eval interval.upper))
  index_eq := by
    rw [event.index]
    exact finiteSign_eventIndex2_eq_phase_change_add_four_mul
      event.numerator event.denominator
      (FiniteSign.ofCoordinate (R.eval interval.lower))
      (FiniteSign.ofCoordinate (S.eval interval.lower))
      (FiniteSign.ofCoordinate (R.eval interval.upper))
      (FiniteSign.ofCoordinate (S.eval interval.upper))
      event.nonzero event.numeratorLowerStable event.denominatorLowerStable
      event.numeratorUpperStable event.denominatorUpperStable

/-- A sufficiently narrow subinterval is resolved by the finite event
scanner and therefore has a modulo-four phase formula. -/
def phaseFormulaOfRefinedWidth
    {R S : CoordinatePolynomial}
    {root interval : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate R S root)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      min 1 (signedChainResolutionRadiusSq S R clearance.swap)) :
    PhaseFormula R S interval.lower interval.upper := by
  have radius : RFAP.IntervalSign.sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance.swap :=
    RFAP.CauchyPartition.radius_lt_of_width_lt proper widthSmall
  exact phaseFormulaOfEvent
    (cauchyEventSignsOfRefinedRadiusSq clearance.swap refines radius)

/-- Fixed-depth central-third subdivision for the modulo-four phase law. -/
def phaseFormulaAtDepth
    {R S : CoordinatePolynomial} {root : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate R S root)
    (fuel : Nat) (interval : RFAP.PathClearance.Interval)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Coordinate) ^ fuel *
      (interval.upper - interval.lower) <
        min 1 (signedChainResolutionRadiusSq S R clearance.swap)) :
    PhaseFormula R S interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      exact phaseFormulaOfRefinedWidth clearance refines proper
        (by simpa only [pow_zero,
          RFAP.ConstructiveFraction.one_mul] using sufficient)
  | succ fuel inductionHypothesis =>
      let cut := RFAP.SafeCandidates.centralLower
        interval.lower interval.upper
      have bounds := RFAP.SafeCandidates.centralBounds proper
      have cutLower : interval.lower < cut := by
        simpa only [cut] using bounds.1
      have cutUpper : cut < interval.upper := by
        exact (by simpa only [cut] using bounds.2.1.trans bounds.2.2)
      let leftInterval : RFAP.PathClearance.Interval :=
        { lower := interval.lower
          upper := cut
          valid := cutLower.le }
      let rightInterval : RFAP.PathClearance.Interval :=
        { lower := cut
          upper := interval.upper
          valid := cutUpper.le }
      have leftRefines : leftInterval.Refines root :=
        ⟨refines.1, cutUpper.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root :=
        ⟨refines.1.trans cutLower.le, refines.2⟩
      have widthPositive : 0 < interval.upper - interval.lower :=
        RFAP.ConstructiveFraction.sub_pos_direct proper
      have leftContraction :
          leftInterval.upper - leftInterval.lower ≤
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        dsimp only [leftInterval, cut]
        simp only [RFAP.SafeCandidates.centralLower,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (show (1 / 3 : Coordinate) ≤ 2 / 3 by decide)
            widthPositive.le
        calc
          interval.lower + (interval.upper - interval.lower) / 3 -
                interval.lower =
              (1 / 3 : Coordinate) *
                (interval.upper - interval.lower) := by
            rw [add_sub_cancel_left]
            rw [RFAP.ExplicitField.div_eq_mul_inv,
              RFAP.ExplicitField.div_eq_mul_inv]
            ring1
          _ ≤ (2 / 3 : Coordinate) *
                (interval.upper - interval.lower) := scaled
      have rightContraction :
          rightInterval.upper - rightInterval.lower =
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        dsimp only [rightInterval, cut]
        simp only [RFAP.SafeCandidates.centralLower,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        have scaled : (3 : Coordinate) *
            ((interval.upper - interval.lower) / 3) =
              interval.upper - interval.lower := by
          rw [RFAP.ConstructiveFraction.mul_comm]
          exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (interval.upper - interval.lower) 3 (by decide)
        rw [RFAP.SafeCandidates.sub_add_eq_twice_of_three_mul
          interval.lower interval.upper
          ((interval.upper - interval.lower) / 3) scaled]
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
      have powerNonnegative : 0 ≤ (2 / 3 : Coordinate) ^ fuel :=
        RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Coordinate) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            min 1 (signedChainResolutionRadiusSq S R clearance.swap) := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (leftInterval.upper - leftInterval.lower) ≤
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              leftContraction powerNonnegative
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      have rightSufficient : (2 / 3 : Coordinate) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            min 1 (signedChainResolutionRadiusSq S R clearance.swap) := by
        rw [rightContraction]
        calc
          (2 / 3 : Coordinate) ^ fuel *
              ((2 / 3 : Coordinate) *
                (interval.upper - interval.lower)) =
              (2 / 3 : Coordinate) ^ Nat.succ fuel *
                (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      exact (inductionHypothesis leftInterval leftRefines cutLower
        leftSufficient).add
        (inductionHypothesis rightInterval rightRefines cutUpper
          rightSufficient)

/-- Every proper polynomial path carrying an explicit nonvanishing clearance
certificate has an integer modulo-four phase formula. -/
def phaseFormulaOfClearance
    {R S : CoordinatePolynomial} {root : RFAP.PathClearance.Interval}
    (clearance : RFAP.PathClearance.Certificate R S root)
    (proper : root.lower < root.upper) :
    PhaseFormula R S root.lower root.upper := by
  let leafWidth := min 1
    (signedChainResolutionRadiusSq S R clearance.swap)
  have leafWidthPositive : 0 < leafWidth :=
    lt_min (by decide)
      (signedChainResolutionRadiusSq_pos S R clearance.swap)
  let depth := RFAP.SafeCandidates.geometricDepth
    (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using RFAP.SafeCandidates.geometricDepth_sufficient
      (width := root.upper - root.lower) (epsilon := leafWidth / 2)
      (RFAP.ConstructiveFraction.sub_pos_direct proper).le
      (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive (by decide))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm,
      RFAP.ConstructiveFraction.one_mul] using scaled
  exact phaseFormulaAtDepth clearance depth root ⟨le_rfl, le_rfl⟩ proper
    (by simpa only [leafWidth] using geometric.trans_lt halfBelow)

/-- Quarter-sector phase of a polynomial value at a displayed Gaussian
vertex. -/
def vertexQuarterPhase (p : GaussianPolynomial) (point : Gaussian) : Int :=
  finiteSignQuarterPhase
    (FiniteSign.ofCoordinate (p.eval point).re)
    (FiniteSign.ofCoordinate (p.eval point).im)

@[simp] theorem endpointQuarterPhase_segment_zero
    (p : GaussianPolynomial) (start finish : Gaussian) :
    endpointQuarterPhase
        (pathReal p start (finish - start))
        (pathImag p start (finish - start)) 0 =
      vertexQuarterPhase p start := by
  simp only [endpointQuarterPhase, vertexQuarterPhase,
    eval_pathReal, eval_pathImag, line_segment_zero]

@[simp] theorem endpointQuarterPhase_segment_one
    (p : GaussianPolynomial) (start finish : Gaussian) :
    endpointQuarterPhase
        (pathReal p start (finish - start))
        (pathImag p start (finish - start)) 1 =
      vertexQuarterPhase p finish := by
  simp only [endpointQuarterPhase, vertexQuarterPhase,
    eval_pathReal, eval_pathImag, line_segment_one]

/-- A proof-bearing phase telescope for every edge of an open polygonal
chain. -/
structure ChainPhaseFormula
    (p : GaussianPolynomial) (start : Gaussian)
    (vertices : List Gaussian) where
  turns : Int
  raw_eq : chainRaw p start vertices =
    vertexQuarterPhase p (terminal start vertices) -
      vertexQuarterPhase p start + 4 * turns

namespace ChainPhaseFormula

def nil (p : GaussianPolynomial) (start : Gaussian) :
    ChainPhaseFormula p start [] where
  turns := 0
  raw_eq := by
    simp only [chainRaw, terminal]
    ring1

def cons
    {p : GaussianPolynomial} {start finish : Gaussian}
    {remaining : List Gaussian}
    (edge : PhaseFormula
      (pathReal p start (finish - start))
      (pathImag p start (finish - start)) 0 1)
    (tail : ChainPhaseFormula p finish remaining) :
    ChainPhaseFormula p start (finish :: remaining) where
  turns := edge.turns + tail.turns
  raw_eq := by
    have edgeIdentity := edge.index_eq
    simp only [endpointQuarterPhase_segment_zero,
      endpointQuarterPhase_segment_one] at edgeIdentity
    simp only [chainRaw, terminal, segment, PolynomialEdge.doubledWinding]
    dsimp only [PolynomialEdge.ofLine]
    rw [edgeIdentity, tail.raw_eq]
    ring1

/-- Turn an explicit nonvanishing edge certificate into the corresponding
chain constructor. -/
def consOfClearance
    {p : GaussianPolynomial} {start finish : Gaussian}
    {remaining : List Gaussian}
    (edge : RFAP.PathClearance.Certificate
      (pathReal p start (finish - start))
      (pathImag p start (finish - start))
      { lower := 0, upper := 1, valid := by decide })
    (tail : ChainPhaseFormula p finish remaining) :
    ChainPhaseFormula p start (finish :: remaining) :=
  cons (phaseFormulaOfClearance edge (by decide)) tail

def append
    {p : GaussianPolynomial} {start : Gaussian}
    {vertices remaining : List Gaussian}
    (first : ChainPhaseFormula p start vertices)
    (second : ChainPhaseFormula p (terminal start vertices) remaining) :
    ChainPhaseFormula p start (vertices ++ remaining) where
  turns := first.turns + second.turns
  raw_eq := by
    rw [chainRaw_append p start vertices remaining,
      terminal_append, first.raw_eq, second.raw_eq]
    ring1

end ChainPhaseFormula

/-- Phase formulas for every edge of a closed polygon, including the final
return to its base vertex. -/
abbrev ClosedPhaseFormula
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian) :=
  ChainPhaseFormula p base (vertices ++ [base])

/-- Concatenate one or more copies of a displayed closed vertex list.
`additional` is the number of copies after the first; each non-final copy
includes its return to `base`, while `closedRaw` supplies the final return. -/
def repeatClosedVertices (base : Gaussian) (vertices : List Gaussian) :
    Nat → List Gaussian
  | 0 => vertices
  | additional + 1 =>
      vertices ++ base :: repeatClosedVertices base vertices additional

/-- Repeating one explicit closed polygon adds its raw winding exactly. -/
theorem closedRaw_repeatClosedVertices
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian) : ∀ additional : Nat,
    closedRaw p base (repeatClosedVertices base vertices additional) =
      ((additional + 1 : Nat) : Int) * closedRaw p base vertices
  | 0 => by
      simp only [repeatClosedVertices]
      ring1
  | additional + 1 => by
      simp only [repeatClosedVertices, closedRaw]
      rw [show
        (vertices ++ base :: repeatClosedVertices base vertices additional) ++
            [base] =
          (vertices ++ [base]) ++
            (repeatClosedVertices base vertices additional ++ [base]) by
        simp only [List.append_assoc, List.cons_append, List.nil_append]]
      rw [chainRaw_append p base (vertices ++ [base])
        (repeatClosedVertices base vertices additional ++ [base]),
        terminal_append_singleton]
      change closedRaw p base vertices +
          closedRaw p base (repeatClosedVertices base vertices additional) =
        ((additional + 1 + 1 : Nat) : Int) * closedRaw p base vertices
      rw [closedRaw_repeatClosedVertices p base vertices additional]
      have castSuccessors : ((additional + 1 + 1 : Nat) : Int) =
          (additional : Int) + 1 + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
      have castAdditional : ((additional + 1 : Nat) : Int) =
          (additional : Int) + 1 := by
        simp only [Nat.cast_add, Nat.cast_one]
      rw [castSuccessors, castAdditional]
      ring1

/-! ## Products on a closed walk -/

/-- One existing finite affine product certificate for every segment of an
open polygonal chain. -/
inductive ChainProductFormula (p q : GaussianPolynomial) :
    Gaussian → List Gaussian → Prop
  | nil (start : Gaussian) : ChainProductFormula p q start []
  | cons {start finish : Gaussian} {remaining : List Gaussian}
      (edge : RFAP.WindingProduct.LineProductFormula p q
        start (finish - start) 0 1)
      (tail : ChainProductFormula p q finish remaining) :
      ChainProductFormula p q start (finish :: remaining)

theorem ChainProductFormula.append
    {p q : GaussianPolynomial} :
    ∀ {start : Gaussian} {vertices remaining : List Gaussian},
      ChainProductFormula p q start vertices →
        ChainProductFormula p q (terminal start vertices) remaining →
        ChainProductFormula p q start (vertices ++ remaining)
  | _, [], _, .nil _, tail => tail
  | _, _ :: _, _, .cons edge rest, tail =>
      .cons edge (rest.append tail)

/-- Product certificates for every edge, including the final return edge. -/
abbrev ClosedProductFormula (p q : GaussianPolynomial)
    (base : Gaussian) (vertices : List Gaussian) :=
  ChainProductFormula p q base (vertices ++ [base])

@[simp] theorem lineProductCorrection2_segment_zero
    (p q : GaussianPolynomial) (start finish : Gaussian) :
    RFAP.WindingProduct.lineProductCorrection2
        p q start (finish - start) 0 =
      RFAP.WindingProduct.vertexProductCorrection2 p q start := by
  simp only [RFAP.WindingProduct.lineProductCorrection2, line_segment_zero]

@[simp] theorem lineProductCorrection2_segment_one
    (p q : GaussianPolynomial) (start finish : Gaussian) :
    RFAP.WindingProduct.lineProductCorrection2
        p q start (finish - start) 1 =
      RFAP.WindingProduct.vertexProductCorrection2 p q finish := by
  simp only [RFAP.WindingProduct.lineProductCorrection2, line_segment_one]

/-- Open-chain product formula with the two uncancelled endpoint
corrections displayed explicitly. -/
theorem chainRaw_mul_of_formula
    (p q : GaussianPolynomial) :
    ∀ (start : Gaussian) (vertices : List Gaussian),
      ChainProductFormula p q start vertices →
        chainRaw (p * q) start vertices =
          chainRaw p start vertices + chainRaw q start vertices -
            (RFAP.WindingProduct.vertexProductCorrection2
              p q start : Int) +
            RFAP.WindingProduct.vertexProductCorrection2
              p q (terminal start vertices)
  | start, [], .nil _ => by
      simp only [chainRaw, terminal]
      ring1
  | start, finish :: remaining, .cons edge tail => by
      have tailFormula := chainRaw_mul_of_formula p q finish remaining tail
      unfold RFAP.WindingProduct.LineProductFormula at edge
      simp only [segment, chainRaw, terminal,
        lineProductCorrection2_segment_zero,
        lineProductCorrection2_segment_one] at edge ⊢
      rw [edge, tailFormula]
      ring1

/-- The local product corrections telescope around any explicitly closed
rational polygon. -/
theorem closedRaw_mul_of_formula
    (p q : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian)
    (formula : ClosedProductFormula p q base vertices) :
    closedRaw (p * q) base vertices =
      closedRaw p base vertices + closedRaw q base vertices := by
  unfold closedRaw
  rw [chainRaw_mul_of_formula p q base (vertices ++ [base]) formula,
    terminal_append_singleton]
  ring1

/-! ## Positive coordinate powers -/

/-- The finite product data needed to build the positive coordinate power
on every edge of one closed polygon. -/
inductive ClosedPositivePowerFormula (base : Gaussian)
    (vertices : List Gaussian) : Nat → Prop
  | zero : ClosedPositivePowerFormula base vertices 0
  | succ {exponent : Nat}
      (previous : ClosedPositivePowerFormula base vertices exponent)
      (product : ClosedProductFormula
        (RFAP.GlobalWinding.coordinatePositivePower exponent)
        RFAP.GlobalWinding.coordinatePolynomial base vertices) :
      ClosedPositivePowerFormula base vertices (exponent + 1)

/-- Raising every vertex path value to the displayed positive power
multiplies the raw closed-walk winding by that power. -/
theorem closedRaw_coordinatePositivePower
    (base : Gaussian) (vertices : List Gaussian) :
    ∀ (exponent : Nat), ClosedPositivePowerFormula base vertices exponent →
      closedRaw
          (RFAP.GlobalWinding.coordinatePositivePower exponent)
          base vertices =
        ((exponent + 1 : Nat) : Int) *
          closedRaw RFAP.GlobalWinding.coordinatePolynomial base vertices
  | 0, .zero => by
      change closedRaw RFAP.GlobalWinding.coordinatePolynomial
          base vertices = (1 : Int) *
            closedRaw RFAP.GlobalWinding.coordinatePolynomial base vertices
      ring1
  | exponent + 1, .succ previous product => by
      have productWinding := closedRaw_mul_of_formula
        (RFAP.GlobalWinding.coordinatePositivePower exponent)
        RFAP.GlobalWinding.coordinatePolynomial base vertices product
      have previousWinding :=
        closedRaw_coordinatePositivePower base vertices exponent previous
      change closedRaw
          (RFAP.GlobalWinding.coordinatePositivePower exponent *
            RFAP.GlobalWinding.coordinatePolynomial) base vertices =
        (((exponent + 1 + 1 : Nat) : Int) *
          closedRaw RFAP.GlobalWinding.coordinatePolynomial base vertices)
      rw [productWinding, previousWinding]
      simp only [Nat.cast_add, Nat.cast_one]
      ring1

/-- The fully executable per-edge product checks can be folded into a closed
walk certificate without introducing a new trust boundary. -/
theorem checkedChainProductFormula (p q : GaussianPolynomial) :
    (start : Gaussian) → (vertices : List Gaussian) →
      (∀ current next,
        RFAP.WindingProduct.lineProductFormulaCheck
          p q current (next - current) 0 1 = true) →
      ChainProductFormula p q start vertices
  | start, [], _ => .nil start
  | start, finish :: remaining, checked =>
      .cons
        (RFAP.WindingProduct.lineProductFormula_of_check
          p q start (finish - start) 0 1 (checked start finish))
        (checkedChainProductFormula p q finish remaining checked)

/-! ## Rouché comparison of two synchronized finite walks -/

/-- Sum of the two endpoint corrections occurring when the straight source
value is conjugated, multiplied by the straight target value, and retained
in the open right half-plane. -/
def vertexHomotopyCorrection2 (source target : Gaussian) : Int :=
  let real := source.re * target.re + source.im * target.im
  let imaginary := source.re * target.im - source.im * target.re
  (RFAP.Sturm.signJump 1 (real * imaginary) : Int) +
    RFAP.Sturm.signJump 1 (imaginary * ((-source.im) * target.im))

/-- Complete finite data comparing one source segment with one target
segment.  `LineData` contains the signed-remainder-chain product and
right-half-plane formulas; the endpoint facts justify conjugating the source
index. -/
structure SegmentHomotopyFormula
    (p q : GaussianPolynomial)
    (sourceStart sourceFinish targetStart targetFinish : Gaussian) : Prop where
  sourceStartNonzero : p.eval sourceStart ≠ 0
  sourceFinishNonzero : p.eval sourceFinish ≠ 0
  data : RFAP.WindingHomotopy.LineData
    (pathReal p sourceStart (sourceFinish - sourceStart))
    (pathImag p sourceStart (sourceFinish - sourceStart))
    (pathReal q targetStart (targetFinish - targetStart))
    (pathImag q targetStart (targetFinish - targetStart)) 0 1

/-- One synchronized Rouché segment changes raw winding only by the
difference of its two displayed endpoint corrections. -/
theorem segmentRaw_eq_of_homotopy
    {p q : GaussianPolynomial}
    {sourceStart sourceFinish targetStart targetFinish : Gaussian}
    (formula : SegmentHomotopyFormula p q
      sourceStart sourceFinish targetStart targetFinish) :
    (segment q targetStart targetFinish).doubledWinding =
      (segment p sourceStart sourceFinish).doubledWinding +
        vertexHomotopyCorrection2
          (p.eval sourceStart) (q.eval targetStart) -
        vertexHomotopyCorrection2
          (p.eval sourceFinish) (q.eval targetFinish) := by
  have sourceStartPair :=
    RFAP.WindingProduct.ofLine_coordinatePair_ne_zero p
      sourceStart (sourceFinish - sourceStart) 0 (by
        simpa only [line_segment_zero] using formula.sourceStartNonzero)
  have sourceFinishPair :=
    RFAP.WindingProduct.ofLine_coordinatePair_ne_zero p
      sourceStart (sourceFinish - sourceStart) 1 (by
        simpa only [line_segment_one] using formula.sourceFinishNonzero)
  have conjugate := RFAP.Sturm.cauchyIndex2_neg_denominator
    sourceStartPair sourceFinishPair
  have half := formula.data.halfPlane
  have product := formula.data.product
  unfold RFAP.HalfPlane.Formula at half
  unfold RFAP.CauchyProduct.AuxiliaryProductFormula
    RFAP.CauchyProduct.auxiliaryEndpointCorrection2 at product
  simp only [RFAP.WindingHomotopy.eval_roucheReal,
    RFAP.WindingHomotopy.eval_roucheImag, eval_neg,
    eval_pathReal, eval_pathImag, line_segment_zero,
    line_segment_one] at half product
  rw [conjugate] at product
  unfold segment PolynomialEdge.doubledWinding
    vertexHomotopyCorrection2
  dsimp only [PolynomialEdge.ofLine]
  have targetIdentity :
      RFAP.Sturm.cauchyIndex2
          (pathReal q targetStart (targetFinish - targetStart))
          (pathImag q targetStart (targetFinish - targetStart)) 0 1 =
        RFAP.Sturm.cauchyIndex2
            (pathReal p sourceStart (sourceFinish - sourceStart))
            (pathImag p sourceStart (sourceFinish - sourceStart)) 0 1 +
          RFAP.Sturm.cauchyIndex2
            (RFAP.WindingHomotopy.roucheReal
              (pathReal p sourceStart (sourceFinish - sourceStart))
              (pathImag p sourceStart (sourceFinish - sourceStart))
              (pathReal q targetStart (targetFinish - targetStart))
              (pathImag q targetStart (targetFinish - targetStart)))
            (RFAP.WindingHomotopy.roucheImag
              (pathReal p sourceStart (sourceFinish - sourceStart))
              (pathImag p sourceStart (sourceFinish - sourceStart))
              (pathReal q targetStart (targetFinish - targetStart))
              (pathImag q targetStart (targetFinish - targetStart))) 0 1 +
          (RFAP.Sturm.signJump 1
            (((p.eval sourceStart).re * (q.eval targetStart).im -
              (p.eval sourceStart).im * (q.eval targetStart).re) *
              (-(p.eval sourceStart).im * (q.eval targetStart).im)) : Int) -
          (RFAP.Sturm.signJump 1
            (((p.eval sourceFinish).re * (q.eval targetFinish).im -
              (p.eval sourceFinish).im * (q.eval targetFinish).re) *
              (-(p.eval sourceFinish).im * (q.eval targetFinish).im)) : Int) := by
    rw [product]
    ring1
  rw [targetIdentity, half]
  ring1

/-- Synchronized segment formulas for two open chains with the same finite
number of edges. -/
inductive ChainHomotopyFormula (p q : GaussianPolynomial) :
    Gaussian → List Gaussian → Gaussian → List Gaussian → Prop
  | nil (sourceStart targetStart : Gaussian) :
      ChainHomotopyFormula p q sourceStart [] targetStart []
  | cons
      {sourceStart sourceFinish targetStart targetFinish : Gaussian}
      {sourceRemaining targetRemaining : List Gaussian}
      (edge : SegmentHomotopyFormula p q
        sourceStart sourceFinish targetStart targetFinish)
      (tail : ChainHomotopyFormula p q
        sourceFinish sourceRemaining targetFinish targetRemaining) :
      ChainHomotopyFormula p q
        sourceStart (sourceFinish :: sourceRemaining)
        targetStart (targetFinish :: targetRemaining)

/-- Concatenate synchronized finite homotopies at their explicitly displayed
terminal vertices. -/
theorem ChainHomotopyFormula.append
    {p q : GaussianPolynomial} :
    ∀ {sourceStart targetStart : Gaussian}
      {sourceVertices targetVertices sourceRemaining targetRemaining :
        List Gaussian},
      ChainHomotopyFormula p q sourceStart sourceVertices
          targetStart targetVertices →
        ChainHomotopyFormula p q
          (terminal sourceStart sourceVertices) sourceRemaining
          (terminal targetStart targetVertices) targetRemaining →
        ChainHomotopyFormula p q sourceStart
          (sourceVertices ++ sourceRemaining) targetStart
          (targetVertices ++ targetRemaining)
  | _, _, [], [], _, _, .nil _ _, tail => tail
  | _, _, _ :: _, _ :: _, _, _, .cons edge remaining, tail =>
      .cons edge (remaining.append tail)

/-- Open synchronized chains retain the two uncancelled endpoint
corrections. -/
theorem chainRaw_eq_of_homotopy
    (p q : GaussianPolynomial) :
    ∀ (sourceStart : Gaussian) (sourceVertices : List Gaussian)
      (targetStart : Gaussian) (targetVertices : List Gaussian),
      ChainHomotopyFormula p q sourceStart sourceVertices
        targetStart targetVertices →
      chainRaw q targetStart targetVertices =
        chainRaw p sourceStart sourceVertices +
          vertexHomotopyCorrection2
            (p.eval sourceStart) (q.eval targetStart) -
          vertexHomotopyCorrection2
            (p.eval (terminal sourceStart sourceVertices))
            (q.eval (terminal targetStart targetVertices))
  | sourceStart, [], targetStart, [], .nil _ _ => by
      simp only [chainRaw, terminal]
      ring1
  | sourceStart, sourceFinish :: sourceRemaining,
      targetStart, targetFinish :: targetRemaining, .cons edge tail => by
      have edgeFormula := segmentRaw_eq_of_homotopy edge
      have tailFormula := chainRaw_eq_of_homotopy p q
        sourceFinish sourceRemaining targetFinish targetRemaining tail
      simp only [chainRaw, terminal]
      rw [edgeFormula, tailFormula]
      ring1

/-- Synchronized formulas for two explicitly closed finite polygons. -/
abbrev ClosedHomotopyFormula
    (p q : GaussianPolynomial)
    (sourceBase : Gaussian) (sourceVertices : List Gaussian)
    (targetBase : Gaussian) (targetVertices : List Gaussian) :=
  ChainHomotopyFormula p q
    sourceBase (sourceVertices ++ [sourceBase])
    targetBase (targetVertices ++ [targetBase])

/-- All endpoint corrections telescope when both synchronized chains close. -/
theorem closedRaw_eq_of_homotopy
    (p q : GaussianPolynomial)
    (sourceBase : Gaussian) (sourceVertices : List Gaussian)
    (targetBase : Gaussian) (targetVertices : List Gaussian)
    (formula : ClosedHomotopyFormula p q
      sourceBase sourceVertices targetBase targetVertices) :
    closedRaw q targetBase targetVertices =
      closedRaw p sourceBase sourceVertices := by
  unfold closedRaw
  rw [chainRaw_eq_of_homotopy p q
    sourceBase (sourceVertices ++ [sourceBase])
    targetBase (targetVertices ++ [targetBase]) formula,
    terminal_append_singleton, terminal_append_singleton]
  ring1

/-! ## Explicit normalization certificates -/

/-- A finite certificate that the raw Cauchy-index sum is four times an
ordinary integer winding.  The equality is decidable from the displayed
vertices; recording it avoids importing a completed-curve degree theorem. -/
structure Normalized
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian) where
  winding : Int
  raw_eq : closedRaw p base vertices = 4 * winding

/-- Kernel-checkable constructor for an already displayed integer candidate. -/
def Normalized.ofCheck
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian) (winding : Int)
    (checked : decide (closedRaw p base vertices = 4 * winding) = true) :
    Normalized p base vertices where
  winding := winding
  raw_eq := by simpa only [decide_eq_true_eq] using checked

/-- A closed chain of explicitly nonvanishing rational edges is normalized
without any appeal to a completed curve: its finite endpoint phases telescope
and leave four times the accumulated integer turn count. -/
def Normalized.ofPhaseFormula
    (p : GaussianPolynomial) (base : Gaussian)
    (vertices : List Gaussian)
    (formula : ClosedPhaseFormula p base vertices) :
    Normalized p base vertices where
  winding := formula.turns
  raw_eq := by
    unfold closedRaw
    rw [formula.raw_eq, terminal_append_singleton]
    ring1

end RFAP.PolygonWinding
