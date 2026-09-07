import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.RegionSeparation

/-!
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace CCL.PersistentCCLConditionProfiles

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis
abbrev ProfileAnalysis
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (conditions : List
      CCL.CoordinateFactorization.Polynomial :=
        CCL.CurveBoxConditions.profiledConditionPolynomials
          chart.parameterization.curve box) :=
  CCL.CCLBoundaryCharts.ConditionProfileAnalysis factorAnalysis
    conditions

open RFAP.ComputablePolynomial.DensePolynomial

/-- One nonzero-count Sturm leaf for a final box-condition profile factor. -/
structure ProfileEventLeaf
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) where
  cell : RFAP.SturmEventPartition.Cell
  member : cell ∈ analysis.partition.tree.leaves
  countNonzero :
    (analysis.partition.classify cell member).eventCount ≠ 0

namespace ProfileEventLeaf

def classification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :=
  analysis.partition.classify leaf.cell leaf.member

def state
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    RFAP.SturmNonzeroEvent.State
      analysis.profile.factor.polynomial :=
  leaf.classification.eventState leaf.countNonzero

theorem classification_cell
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    leaf.classification.cell = leaf.cell :=
  analysis.partition.classify_cell leaf.cell leaf.member

theorem state_cell
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) : leaf.state.cell = leaf.cell :=
  leaf.classification_cell

theorem cell_refines_chart
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    leaf.cell.interval.Refines chart.cell.interval := by
  rw [← leaf.classification_cell]
  exact leaf.classification.refines

def request
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) :
    RFAP.SturmNonzeroEvent.State
      analysis.profile.factor.polynomial :=
  RFAP.SturmNonzeroEvent.request
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      leaf.state epsilon

theorem request_refines_chart
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) :
    (leaf.request epsilon).cell.interval.Refines chart.cell.interval :=
  RFAP.SturmNonzeroEvent.intervalRefines_trans
    (RFAP.SturmNonzeroEvent.request_refines
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        leaf.state epsilon)
    (by simpa only [leaf.state_cell] using leaf.cell_refines_chart)

theorem request_width_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (leaf.request epsilon).cell.interval.width ≤ epsilon :=
  RFAP.SturmNonzeroEvent.request_width_le
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      leaf.state epsilon positive

def requestResolution
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) :
    RFAP.CauchyCells.CauchyEventResolution
      (RFAP.SturmRootCount.reducedNumerator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (leaf.request epsilon).cell.interval := by
  apply CCL.CurveBoxEventPartition.polynomialEventResolutionOfBounds
    analysis.profile.factor.polynomial chart.cell (leaf.request epsilon).cell
  · exact leaf.request_refines_chart epsilon
  · have refinesLeaf :
        (leaf.request epsilon).cell.interval.Refines leaf.cell.interval := by
      simpa only [request, leaf.state_cell] using
        RFAP.SturmNonzeroEvent.request_refines
          analysis.profile.factor.polynomial analysis.profile.factor.nonzero
            leaf.state epsilon
    have widthLe : (leaf.request epsilon).cell.interval.width ≤
        leaf.cell.interval.width := RFAP.ConstructiveFraction.sub_le_sub_direct refinesLeaf.2 refinesLeaf.1
    have leafWidthSmall : leaf.cell.interval.width <
        CCL.CurveBoxEventPartition.squarefreeLeafWidth
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact widthLe.trans_lt
      (leafWidthSmall.trans_le
        ((CCL.CurveBoxEventPartition.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell).trans
          (CCL.CurveBoxEventPartition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial
              chart.parameterization.curve box chart.cell)))

/-- Fixed chart-wide coefficient for the gcd-reduced profile residual. -/
def reducedResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  4 * RFAP.IntervalSign.denseEvalSqLipschitzBound
    (RFAP.SturmRootCount.reducedDenominator
      (RFAP.ComputableDerivative.derivative analysis.profile.factor.polynomial)
      analysis.profile.factor.polynomial) chart.cell.interval

theorem reducedResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ reducedResidualCoefficient analysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval).2

theorem reduced_eval_sq_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial).eval parameter ^ 2 ≤
      reducedResidualCoefficient analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let requested := leaf.request epsilon
  let localLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      requested.cell.interval
  let chartLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound reduced
      chart.cell.interval
  have localBound :=
    (leaf.requestResolution epsilon).denominator_eval_sq_le
      requested.countNonzero parameter inside
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [localLipschitz, chartLipschitz, requested, reduced] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        reduced (leaf.request_refines_chart epsilon)
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Coordinate) ≤ 4 by decide)
  have widthSqLe : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      requested.cell.interval.width_nonneg
      (leaf.request_width_le epsilon positive) 2
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_direct coefficientLe widthSqLe
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        requested.cell.interval.width)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        chartNonnegative))

/-- Fixed coefficient for the final squarefree profile factor itself. -/
def factorResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  RFAP.PathClearance.evalSqBound
      (RFAP.ComputableGCD.gcd
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval *
    reducedResidualCoefficient analysis

theorem factorResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :
    0 ≤ factorResidualCoefficient analysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.PathClearance.evalSqBound_nonneg
      (RFAP.ComputableGCD.gcd
        (RFAP.ComputableDerivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial) chart.cell.interval)
    (reducedResidualCoefficient_nonneg analysis)

theorem factor_eval_sq_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      factorResidualCoefficient analysis * epsilon ^ 2 := by
  let event := analysis.profile.factor.polynomial
  let common := RFAP.ComputableGCD.gcd
    (RFAP.ComputableDerivative.derivative event) event
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let commonBound := RFAP.PathClearance.evalSqBound common
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      reducedResidualCoefficient analysis * epsilon ^ 2 := by
    simpa only [event, reduced] using
      leaf.reduced_eval_sq_request_le epsilon positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (reducedResidualCoefficient analysis * epsilon ^ 2) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      reducedEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (reduced.eval parameter))
      (RFAP.PathClearance.evalSqBound_nonneg common
        chart.cell.interval)
  have identity : event.eval parameter =
      common.eval parameter * reduced.eval parameter := by
    simpa only [event, common, reduced,
      RFAP.SturmRootCount.reducedDenominator] using
      RFAP.ComputableGCD.rightFactor_eval_identity
        (RFAP.ComputableDerivative.derivative event) event parameter
  rw [identity, mul_pow]
  change common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
    (commonBound * reducedResidualCoefficient analysis) * epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-! ## Quantitative separation from an apart box edge -/

/-- Coefficient of the squarefree-factor contribution in one finite Bezout
identity. -/
def apartResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Coordinate :=
  2 * RFAP.PathClearance.evalSqBound apart.left
      chart.cell.interval * factorResidualCoefficient analysis

theorem apartResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 ≤ apartResidualCoefficient analysis condition apart :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.PathClearance.evalSqBound_nonneg apart.left
        chart.cell.interval))
    (factorResidualCoefficient_nonneg analysis)

/-- First width: the factor term in the Bezout identity is below `1/2`. -/
def apartResidualWidth
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Coordinate :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth
    (apartResidualCoefficient analysis condition apart) (1 / 2)

theorem apartResidualWidth_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartResidualWidth analysis condition apart :=
  CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
    (apartResidualCoefficient_nonneg analysis condition apart) (by decide)

/-- Uniform positive quadrance lower target for the apart condition value. -/
def apartConditionLower
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Coordinate :=
  (1 / 2) / (2 *
    (RFAP.PathClearance.evalSqBound apart.right
      chart.cell.interval + 1))

theorem apartConditionLower_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartConditionLower analysis condition apart :=
  RFAP.ConstructiveFraction.div_pos_direct (by decide)
    (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (add_pos_of_nonneg_of_pos
        (RFAP.PathClearance.evalSqBound_nonneg apart.right
          chart.cell.interval) (by decide)))

/-- Final width: additionally make condition variation smaller than its
Bezout lower bound. -/
def apartSignWidth
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) : Coordinate :=
  min (apartResidualWidth analysis condition apart)
    (CCL.PersistentCCLRegionSeparation.shrinkingWidth
      (RFAP.IntervalSign.denseEvalSqLipschitzBound condition
        chart.cell.interval)
      (apartConditionLower analysis condition apart))

theorem apartSignWidth_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition) :
    0 < apartSignWidth analysis condition apart :=
  lt_min (apartResidualWidth_pos analysis condition apart)
    (CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
      (by
        exact (RFAP.IntervalSign.denseHornerSqBounds_nonneg
          condition chart.cell.interval).2)
      (apartConditionLower_pos analysis condition apart))

/-- At any positive width no larger than the apart-sign width, the factor
term in the Bezout identity is strictly below `1/2` everywhere in the
requested event. -/
theorem apart_left_contribution_lt_half_of_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    2 * (apart.left.eval parameter *
      analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 := by
  let width := epsilon
  let residualWidth := apartResidualWidth analysis condition apart
  let coefficient := apartResidualCoefficient analysis condition apart
  let leftBound := RFAP.PathClearance.evalSqBound apart.left
    chart.cell.interval
  let residualCoefficient := factorResidualCoefficient analysis
  have widthPositive : 0 < width := positive
  have residualWidthPositive : 0 < residualWidth :=
    apartResidualWidth_pos analysis condition apart
  have widthLe : width ≤ residualWidth :=
    epsilonLe.trans (min_le_left _ _)
  have widthSqLe : width ^ 2 ≤ residualWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct widthPositive.le widthLe 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      apartResidualCoefficient_nonneg analysis condition apart
  have coefficientWidthLe : coefficient * width ^ 2 ≤
      coefficient * residualWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct widthSqLe
      coefficientNonnegative
  have coefficientResidualSmall : coefficient * residualWidth ^ 2 <
      (1 / 2 : Coordinate) := by
    simpa only [residualWidth, coefficient, apartResidualWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        coefficientNonnegative (show (0 : Coordinate) < 1 / 2 by decide)
  have refinesChart := leaf.request_refines_chart width
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have leftEvalBound : apart.left.eval parameter ^ 2 ≤ leftBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound apart.left
      chart.cell.interval parameterInsideChart
  have factorBound : analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      residualCoefficient * width ^ 2 := by
    simpa only [width, residualCoefficient] using
      leaf.factor_eval_sq_request_le width widthPositive parameter inside
  have productBound : apart.left.eval parameter ^ 2 *
        analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
      leftBound * (residualCoefficient * width ^ 2) :=
    RFAP.ConstructiveFraction.mul_le_mul_direct leftEvalBound factorBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct
        (analysis.profile.factor.polynomial.eval parameter))
      (RFAP.PathClearance.evalSqBound_nonneg apart.left
        chart.cell.interval)
  calc
    2 * (apart.left.eval parameter *
        analysis.profile.factor.polynomial.eval parameter) ^ 2 =
        2 * (apart.left.eval parameter ^ 2 *
          analysis.profile.factor.polynomial.eval parameter ^ 2) := by
      rw [mul_pow]
    _ ≤ 2 * (leftBound * (residualCoefficient * width ^ 2)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productBound
        (by decide)
    _ = coefficient * width ^ 2 := by
      dsimp only [coefficient, apartResidualCoefficient, leftBound,
        residualCoefficient]
      ring1
    _ ≤ coefficient * residualWidth ^ 2 := coefficientWidthLe
    _ < 1 / 2 := coefficientResidualSmall

/-- Specialization at the computed apart-sign width. -/
theorem apart_left_contribution_lt_half
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (parameter : Coordinate)
    (inside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        parameter) :
    2 * (apart.left.eval parameter *
      analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 :=
  leaf.apart_left_contribution_lt_half_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl parameter inside

private theorem sum_sq_le_two_sum_sq (left right : Coordinate) :
    (left + right) ^ 2 ≤ 2 * (left ^ 2 + right ^ 2) := by
  have squareNonnegative : 0 ≤ (left - right) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (left - right)
  have enlarged :=
    RFAP.ConstructiveFraction.add_le_add_right_direct squareNonnegative
      ((left + right) ^ 2)
  calc
    (left + right) ^ 2 ≤ (left + right) ^ 2 + (left - right) ^ 2 := by
      simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using enlarged
    _ = 2 * (left ^ 2 + right ^ 2) := by ring1

/-- The apart condition itself is uniformly separated from zero throughout
every request no wider than its computed apart-sign width. -/
theorem apartConditionLower_lt_eval_sq_of_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 := by
  let width := epsilon
  let factorValue := analysis.profile.factor.polynomial.eval parameter
  let conditionValue := condition.eval parameter
  let leftValue := apart.left.eval parameter
  let rightValue := apart.right.eval parameter
  let rightBound := RFAP.PathClearance.evalSqBound apart.right
    chart.cell.interval
  let denominator := 2 * (rightBound + 1)
  have leftSmall : 2 * (leftValue * factorValue) ^ 2 < 1 / 2 := by
    simpa only [width, factorValue, leftValue] using
      leaf.apart_left_contribution_lt_half_of_le condition apart epsilon
        positive epsilonLe parameter inside
  have identity : 1 = leftValue * factorValue +
      rightValue * conditionValue := by
    simpa only [leftValue, factorValue, rightValue, conditionValue] using
      apart.identity parameter
  have totalLower : (1 : Coordinate) ≤
      2 * (leftValue * factorValue) ^ 2 +
        2 * (rightValue * conditionValue) ^ 2 := by
    calc
      (1 : Coordinate) =
          (leftValue * factorValue + rightValue * conditionValue) ^ 2 := by
        rw [← identity]
        decide
      _ ≤ 2 * ((leftValue * factorValue) ^ 2 +
          (rightValue * conditionValue) ^ 2) :=
        sum_sq_le_two_sum_sq _ _
      _ = 2 * (leftValue * factorValue) ^ 2 +
          2 * (rightValue * conditionValue) ^ 2 := by ring1
  have rightStrict : (1 / 2 : Coordinate) <
      2 * (rightValue * conditionValue) ^ 2 := by
    by_contra notStrict
    have rightLe : 2 * (rightValue * conditionValue) ^ 2 ≤ 1 / 2 :=
      le_of_not_gt notStrict
    have firstStep := RFAP.ConstructiveFraction.add_lt_add_right_direct
      leftSmall (2 * (rightValue * conditionValue) ^ 2)
    have secondStep := RFAP.ConstructiveFraction.add_le_add_right_direct
      rightLe (1 / 2 : Coordinate)
    have sumStrict :
        2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 < 1 := by
      calc
        2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 <
            1 / 2 + 2 * (rightValue * conditionValue) ^ 2 := firstStep
        _ ≤ 1 / 2 + 1 / 2 := by
          simpa only [RFAP.ConstructiveFraction.add_comm] using secondStep
        _ = 1 := by decide
    exact (not_lt_of_ge totalLower) sumStrict
  have refinesChart := leaf.request_refines_chart width
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have rightEvalBound : rightValue ^ 2 ≤ rightBound := by
    simpa only [rightValue, rightBound] using
      RFAP.PathClearance.eval_sq_le_evalSqBound apart.right
        chart.cell.interval parameterInsideChart
  have rightBoundLe : rightBound ≤ rightBound + 1 := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      (show (0 : Coordinate) ≤ 1 by decide) rightBound
    simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using shifted
  have conditionSquareNonnegative : 0 ≤ conditionValue ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct conditionValue
  have rightProductUpper :
      2 * (rightValue * conditionValue) ^ 2 ≤
        denominator * conditionValue ^ 2 := by
    rw [mul_pow]
    have valueBound : rightValue ^ 2 * conditionValue ^ 2 ≤
        (rightBound + 1) * conditionValue ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (rightEvalBound.trans rightBoundLe) conditionSquareNonnegative
    calc
      2 * (rightValue ^ 2 * conditionValue ^ 2) ≤
          2 * ((rightBound + 1) * conditionValue ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct valueBound
          (by decide)
      _ = denominator * conditionValue ^ 2 := by
        dsimp only [denominator]
        ring1
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (add_pos_of_nonneg_of_pos
        (RFAP.PathClearance.evalSqBound_nonneg apart.right
          chart.cell.interval) (by decide))
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
  calc
    (1 / 2 : Coordinate) <
        2 * (rightValue * conditionValue) ^ 2 := rightStrict
    _ ≤ denominator * conditionValue ^ 2 := rightProductUpper
    _ = conditionValue ^ 2 * denominator :=
      RFAP.ConstructiveFraction.mul_comm _ _

/-- Specialization at the computed apart-sign width. -/
theorem apartConditionLower_lt_eval_sq
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (parameter : Coordinate)
    (inside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains
        parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 :=
  leaf.apartConditionLower_lt_eval_sq_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl parameter inside

/-- At any positive width no larger than the apart-sign width, the variation
of the apart condition between any two event parameters is smaller than its
uniform quadrance lower bound. -/
theorem condition_eval_sub_sq_lt_lower_of_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    {left right : Coordinate}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart := by
  let width := epsilon
  let requested := leaf.request width
  let chartLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound condition
      chart.cell.interval
  let variationWidth :=
    CCL.PersistentCCLRegionSeparation.shrinkingWidth
      chartLipschitz (apartConditionLower analysis condition apart)
  have widthPositive : 0 < width := positive
  have variationWidthPositive : 0 < variationWidth :=
    CCL.PersistentCCLRegionSeparation.shrinkingWidth_pos
      (by
        simpa only [chartLipschitz] using
          (RFAP.IntervalSign.denseHornerSqBounds_nonneg
            condition chart.cell.interval).2)
      (apartConditionLower_pos analysis condition apart)
  have widthLeVariation : width ≤ variationWidth :=
    epsilonLe.trans (min_le_right _ _)
  have widthSqLeVariation : width ^ 2 ≤ variationWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct widthPositive.le
      widthLeVariation 2
  have chartLipschitzNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg
        condition chart.cell.interval).2
  have variationSmall : chartLipschitz * variationWidth ^ 2 <
      apartConditionLower analysis condition apart := by
    simpa only [variationWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        chartLipschitzNonnegative
        (apartConditionLower_pos analysis condition apart)
  have localVariation := RFAP.IntervalSign.eval_sub_sq_le
    condition requested.cell.interval leftInside rightInside
  have localLeChart :
      RFAP.IntervalSign.denseEvalSqLipschitzBound condition
          requested.cell.interval ≤ chartLipschitz := by
    simpa only [chartLipschitz, requested] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        condition (leaf.request_refines_chart width)
  have parameterDistance : (left - right) ^ 2 ≤
      requested.cell.interval.width ^ 2 :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have requestedWidth : requested.cell.interval.width ≤ width :=
    leaf.request_width_le width widthPositive
  have requestedWidthSq : requested.cell.interval.width ^ 2 ≤ width ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      requested.cell.interval.width_nonneg requestedWidth 2
  have distanceLeVariation : (left - right) ^ 2 ≤ variationWidth ^ 2 :=
    parameterDistance.trans (requestedWidthSq.trans widthSqLeVariation)
  have localNonnegative :
      0 ≤ RFAP.IntervalSign.denseEvalSqLipschitzBound condition
        requested.cell.interval :=
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg condition
      requested.cell.interval).2
  exact localVariation.trans_lt
    ((RFAP.ConstructiveFraction.mul_le_mul_direct localLeChart
      distanceLeVariation
      (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))
      chartLipschitzNonnegative).trans_lt variationSmall)

/-- Specialization at the computed apart-sign width. -/
theorem condition_eval_sub_sq_lt_lower
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    {left right : Coordinate}
    (leftInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains right) :
    (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart :=
  leaf.condition_eval_sub_sq_lt_lower_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl
        leftInside rightInside

private theorem right_sq_le_sub_sq_of_mul_nonpos
    {left right : Coordinate} (product : left * right ≤ 0) :
    right ^ 2 ≤ (left - right) ^ 2 := by
  have swapped : right * left ≤ 0 := by
    simpa only [RFAP.ConstructiveFraction.mul_comm] using product
  have crossNonpositive : 2 * (right * left) ≤ 0 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct swapped
        (show (0 : Coordinate) ≤ 2 by decide)
    simpa only [RFAP.ConstructiveFraction.mul_zero_direct] using scaled
  have extraNonnegative : 0 ≤ left ^ 2 - 2 * (right * left) :=
    RFAP.ConstructiveFraction.sub_nonneg_direct
      (crossNonpositive.trans
        (RFAP.ConstructiveFraction.sq_nonneg_direct left))
  have enlarged :=
    RFAP.ConstructiveFraction.add_le_add_right_direct extraNonnegative
      (right ^ 2)
  calc
    right ^ 2 ≤ right ^ 2 + (left ^ 2 - 2 * (right * left)) := by
      simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using enlarged
    _ = (left - right) ^ 2 := by ring1

/-- Every two values of an apart condition on any sufficiently narrow
requested event have positive product, hence one stable strict sign. -/
theorem condition_eval_mul_pos_of_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    {left right : Coordinate}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right := by
  have variation := leaf.condition_eval_sub_sq_lt_lower_of_le condition apart
    epsilon positive epsilonLe leftInside rightInside
  have rightLower := leaf.apartConditionLower_lt_eval_sq_of_le condition apart
    epsilon positive epsilonLe right rightInside
  have differenceSmall :
      (condition.eval left - condition.eval right) ^ 2 <
        condition.eval right ^ 2 := variation.trans rightLower
  rcases lt_or_ge (0 : Coordinate)
      (condition.eval left * condition.eval right) with positive | nonpositive
  · exact positive
  · have squareOrder := right_sq_le_sub_sq_of_mul_nonpos nonpositive
    exact (not_lt_of_ge squareOrder differenceSmall).elim

/-- Specialization at the computed apart-sign width. -/
theorem condition_eval_mul_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (condition :
      CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    {left right : Coordinate}
    (leftInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (apartSignWidth analysis condition apart)).cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  leaf.condition_eval_mul_pos_of_le condition apart
    (apartSignWidth analysis condition apart)
      (apartSignWidth_pos analysis condition apart) le_rfl
        leftInside rightInside

/-- Uniform separation and stable sign of an apart condition on any
explicitly bounded rational cell.  This is the request-path-independent form
used by complete finite refinement families: callers provide chart
containment, the requested width bound, and the already established
profile-factor residual. -/
theorem apartConditionControl_on_cell
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (cell : RFAP.SturmEventPartition.Cell)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : cell.interval.width ≤ epsilon)
    (factorBound : ∀ parameter : Coordinate,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        factorResidualCoefficient analysis * epsilon ^ 2)
    {left right : Coordinate}
    (leftInside : cell.interval.Contains left)
    (rightInside : cell.interval.Contains right) :
    (∀ parameter : Coordinate, cell.interval.Contains parameter →
      apartConditionLower analysis condition apart <
        condition.eval parameter ^ 2) ∧
      0 < condition.eval left * condition.eval right := by
  let residualWidth := apartResidualWidth analysis condition apart
  let residualCoefficient := factorResidualCoefficient analysis
  let apartCoefficient := apartResidualCoefficient analysis condition apart
  let leftBound := RFAP.PathClearance.evalSqBound apart.left
    chart.cell.interval
  have widthLeResidual : epsilon ≤ residualWidth :=
    epsilonLe.trans (min_le_left _ _)
  have widthSqLeResidual : epsilon ^ 2 ≤ residualWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
      widthLeResidual 2
  have apartCoefficientNonnegative : 0 ≤ apartCoefficient := by
    simpa only [apartCoefficient] using
      apartResidualCoefficient_nonneg analysis condition apart
  have apartCoefficientWidthLe :
      apartCoefficient * epsilon ^ 2 ≤
        apartCoefficient * residualWidth ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      widthSqLeResidual apartCoefficientNonnegative
  have apartCoefficientResidualSmall :
      apartCoefficient * residualWidth ^ 2 < (1 / 2 : Coordinate) := by
    simpa only [apartCoefficient, residualWidth, apartResidualWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        apartCoefficientNonnegative (show (0 : Coordinate) < 1 / 2 by decide)
  have factorContributionSmall : ∀ parameter : Coordinate,
      cell.interval.Contains parameter →
      2 * (apart.left.eval parameter *
        analysis.profile.factor.polynomial.eval parameter) ^ 2 < 1 / 2 := by
    intro parameter parameterInside
    have parameterInsideChart : chart.cell.interval.Contains parameter :=
      ⟨refinesChart.1.trans parameterInside.1,
        parameterInside.2.trans refinesChart.2⟩
    have leftEvalBound : apart.left.eval parameter ^ 2 ≤ leftBound :=
      RFAP.PathClearance.eval_sq_le_evalSqBound apart.left
        chart.cell.interval parameterInsideChart
    have profileBound := factorBound parameter parameterInside
    have productBound : apart.left.eval parameter ^ 2 *
          analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        leftBound * (residualCoefficient * epsilon ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftEvalBound profileBound
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (analysis.profile.factor.polynomial.eval parameter))
        (RFAP.PathClearance.evalSqBound_nonneg apart.left
          chart.cell.interval)
    calc
      2 * (apart.left.eval parameter *
          analysis.profile.factor.polynomial.eval parameter) ^ 2 =
          2 * (apart.left.eval parameter ^ 2 *
            analysis.profile.factor.polynomial.eval parameter ^ 2) := by
        rw [mul_pow]
      _ ≤ 2 * (leftBound * (residualCoefficient * epsilon ^ 2)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productBound
          (by decide)
      _ = apartCoefficient * epsilon ^ 2 := by
        dsimp only [apartCoefficient, apartResidualCoefficient, leftBound,
          residualCoefficient]
        ring1
      _ ≤ apartCoefficient * residualWidth ^ 2 := apartCoefficientWidthLe
      _ < 1 / 2 := apartCoefficientResidualSmall
  have conditionLowerAt : ∀ parameter : Coordinate,
      cell.interval.Contains parameter →
      apartConditionLower analysis condition apart <
        condition.eval parameter ^ 2 := by
    intro parameter parameterInside
    let factorValue := analysis.profile.factor.polynomial.eval parameter
    let conditionValue := condition.eval parameter
    let leftValue := apart.left.eval parameter
    let rightValue := apart.right.eval parameter
    let rightBound := RFAP.PathClearance.evalSqBound apart.right
      chart.cell.interval
    let denominator := 2 * (rightBound + 1)
    have leftSmall : 2 * (leftValue * factorValue) ^ 2 < 1 / 2 := by
      simpa only [leftValue, factorValue] using
        factorContributionSmall parameter parameterInside
    have identity : 1 = leftValue * factorValue +
        rightValue * conditionValue := by
      simpa only [leftValue, factorValue, rightValue, conditionValue] using
        apart.identity parameter
    have totalLower : (1 : Coordinate) ≤
        2 * (leftValue * factorValue) ^ 2 +
          2 * (rightValue * conditionValue) ^ 2 := by
      calc
        (1 : Coordinate) =
            (leftValue * factorValue + rightValue * conditionValue) ^ 2 := by
          rw [← identity]
          decide
        _ ≤ 2 * ((leftValue * factorValue) ^ 2 +
            (rightValue * conditionValue) ^ 2) :=
          sum_sq_le_two_sum_sq _ _
        _ = 2 * (leftValue * factorValue) ^ 2 +
            2 * (rightValue * conditionValue) ^ 2 := by ring1
    have rightStrict : (1 / 2 : Coordinate) <
        2 * (rightValue * conditionValue) ^ 2 := by
      by_contra notStrict
      have rightLe : 2 * (rightValue * conditionValue) ^ 2 ≤ 1 / 2 :=
        le_of_not_gt notStrict
      have firstStep := RFAP.ConstructiveFraction.add_lt_add_right_direct
        leftSmall (2 * (rightValue * conditionValue) ^ 2)
      have secondStep := RFAP.ConstructiveFraction.add_le_add_right_direct
        rightLe (1 / 2 : Coordinate)
      have sumStrict :
          2 * (leftValue * factorValue) ^ 2 +
              2 * (rightValue * conditionValue) ^ 2 < 1 := by
        calc
          2 * (leftValue * factorValue) ^ 2 +
              2 * (rightValue * conditionValue) ^ 2 <
              1 / 2 + 2 * (rightValue * conditionValue) ^ 2 := firstStep
          _ ≤ 1 / 2 + 1 / 2 := by
            simpa only [RFAP.ConstructiveFraction.add_comm] using secondStep
          _ = 1 := by decide
      exact (not_lt_of_ge totalLower) sumStrict
    have parameterInsideChart : chart.cell.interval.Contains parameter :=
      ⟨refinesChart.1.trans parameterInside.1,
        parameterInside.2.trans refinesChart.2⟩
    have rightEvalBound : rightValue ^ 2 ≤ rightBound := by
      simpa only [rightValue, rightBound] using
        RFAP.PathClearance.eval_sq_le_evalSqBound apart.right
          chart.cell.interval parameterInsideChart
    have rightBoundLe : rightBound ≤ rightBound + 1 := by
      have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
        (show (0 : Coordinate) ≤ 1 by decide) rightBound
      simpa only [zero_add, RFAP.ConstructiveFraction.add_comm] using shifted
    have conditionSquareNonnegative : 0 ≤ conditionValue ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct conditionValue
    have rightProductUpper :
        2 * (rightValue * conditionValue) ^ 2 ≤
          denominator * conditionValue ^ 2 := by
      rw [mul_pow]
      have valueBound : rightValue ^ 2 * conditionValue ^ 2 ≤
          (rightBound + 1) * conditionValue ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (rightEvalBound.trans rightBoundLe) conditionSquareNonnegative
      calc
        2 * (rightValue ^ 2 * conditionValue ^ 2) ≤
            2 * ((rightBound + 1) * conditionValue ^ 2) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct valueBound
            (by decide)
        _ = denominator * conditionValue ^ 2 := by
          dsimp only [denominator]
          ring1
    have denominatorPositive : 0 < denominator :=
      RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (add_pos_of_nonneg_of_pos
          (RFAP.PathClearance.evalSqBound_nonneg apart.right
            chart.cell.interval) (by decide))
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    calc
      (1 / 2 : Coordinate) <
          2 * (rightValue * conditionValue) ^ 2 := rightStrict
      _ ≤ denominator * conditionValue ^ 2 := rightProductUpper
      _ = conditionValue ^ 2 * denominator :=
        RFAP.ConstructiveFraction.mul_comm _ _
  let chartLipschitz :=
    RFAP.IntervalSign.denseEvalSqLipschitzBound condition
      chart.cell.interval
  let variationWidth :=
    CCL.PersistentCCLRegionSeparation.shrinkingWidth
      chartLipschitz (apartConditionLower analysis condition apart)
  have widthLeVariation : epsilon ≤ variationWidth :=
    epsilonLe.trans (min_le_right _ _)
  have widthSqLeVariation : epsilon ^ 2 ≤ variationWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
      widthLeVariation 2
  have chartLipschitzNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg
        condition chart.cell.interval).2
  have variationSmall : chartLipschitz * variationWidth ^ 2 <
      apartConditionLower analysis condition apart := by
    simpa only [variationWidth] using
      CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
        chartLipschitzNonnegative
        (apartConditionLower_pos analysis condition apart)
  have localVariation := RFAP.IntervalSign.eval_sub_sq_le
    condition cell.interval leftInside rightInside
  have localLeChart :
      RFAP.IntervalSign.denseEvalSqLipschitzBound condition
          cell.interval ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        condition refinesChart
  have parameterDistance : (left - right) ^ 2 ≤ cell.interval.width ^ 2 :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      cell.interval leftInside rightInside
  have cellWidthSq : cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct cell.interval.width_nonneg
      widthLe 2
  have distanceLeVariation : (left - right) ^ 2 ≤ variationWidth ^ 2 :=
    parameterDistance.trans (cellWidthSq.trans widthSqLeVariation)
  have variation : (condition.eval left - condition.eval right) ^ 2 <
      apartConditionLower analysis condition apart :=
    localVariation.trans_lt
      ((RFAP.ConstructiveFraction.mul_le_mul_direct localLeChart
        distanceLeVariation
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left - right))
        chartLipschitzNonnegative).trans_lt variationSmall)
  have rightLower := conditionLowerAt right rightInside
  have differenceSmall :
      (condition.eval left - condition.eval right) ^ 2 <
        condition.eval right ^ 2 := variation.trans rightLower
  constructor
  · exact conditionLowerAt
  · rcases lt_or_ge (0 : Coordinate)
        (condition.eval left * condition.eval right) with stable | nonpositive
    · exact stable
    · have squareOrder := right_sq_le_sub_sq_of_mul_nonpos nonpositive
      exact (not_lt_of_ge squareOrder differenceSmall).elim

/-- Uniform quadrance separation of an apart condition on an arbitrary
complete-refinement cell. -/
theorem apartConditionLower_lt_eval_sq_on_cell
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (cell : RFAP.SturmEventPartition.Cell)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : cell.interval.width ≤ epsilon)
    (factorBound : ∀ parameter : Coordinate,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        factorResidualCoefficient analysis * epsilon ^ 2)
    (parameter : Coordinate)
    (inside : cell.interval.Contains parameter) :
    apartConditionLower analysis condition apart <
      condition.eval parameter ^ 2 :=
  (apartConditionControl_on_cell cell condition apart epsilon positive
    epsilonLe refinesChart widthLe factorBound inside inside).1 parameter inside

/-- Stable sign projection of the complete apart-condition control. -/
theorem condition_eval_mul_pos_on_cell
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (cell : RFAP.SturmEventPartition.Cell)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ apartSignWidth analysis condition apart)
    (refinesChart : cell.interval.Refines chart.cell.interval)
    (widthLe : cell.interval.width ≤ epsilon)
    (factorBound : ∀ parameter : Coordinate,
      cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter ^ 2 ≤
        factorResidualCoefficient analysis * epsilon ^ 2)
    {left right : Coordinate}
    (leftInside : cell.interval.Contains left)
    (rightInside : cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  (apartConditionControl_on_cell cell condition apart epsilon positive
    epsilonLe refinesChart widthLe factorBound leftInside rightInside).2

end ProfileEventLeaf

/-! ## One finite request width for all apart conditions in a profile -/

/-- Equality-owned conditions impose no shrinking requirement; an apart
condition contributes its coefficient-computed sign width. -/
def relationSignWidth
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis)
    (entry : Sigma fun condition =>
      CCL.CoordinateFactorization.ConditionRelation condition
        analysis.profile.factor) : Coordinate :=
  match entry.2 with
  | .equality _ _ => 1
  | .apart apart => ProfileEventLeaf.apartSignWidth analysis entry.1 apart

theorem relationSignWidth_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis)
    (entry : Sigma fun condition =>
      CCL.CoordinateFactorization.ConditionRelation condition
        analysis.profile.factor) :
    0 < relationSignWidth analysis entry := by
  rcases entry with ⟨condition, relation⟩
  cases relation with
  | equality _ _ =>
      simpa only [relationSignWidth] using
        (show (0 : Coordinate) < 1 by decide)
  | apart apart =>
      simpa only [relationSignWidth] using
        ProfileEventLeaf.apartSignWidth_pos analysis condition apart

def relationSignWidths
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) : List Coordinate :=
  analysis.profile.relations.map (relationSignWidth analysis)

/-- One displayed positive rational width satisfying all apart-condition
requirements of the profile simultaneously. -/
def profileSignWidth
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) : Coordinate :=
  CCL.CurveBoxEventPartition.positiveMinimum
    (relationSignWidths analysis)

theorem profileSignWidth_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :
    0 < profileSignWidth analysis := by
  apply CCL.CurveBoxEventPartition.positiveMinimum_pos
  intro width widthMember
  rw [relationSignWidths, QuotientFreeList.mem_map] at widthMember
  rcases widthMember with ⟨entry, _entryMember, rfl⟩
  exact relationSignWidth_pos analysis entry

theorem profileSignWidth_le_relation
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis)
    (entry : Sigma fun condition =>
      CCL.CoordinateFactorization.ConditionRelation condition
        analysis.profile.factor)
    (member : entry ∈ analysis.profile.relations) :
    profileSignWidth analysis ≤ relationSignWidth analysis entry := by
  apply CCL.CurveBoxEventPartition.positiveMinimum_le_of_mem
  exact QuotientFreeList.mem_map.mpr ⟨entry, member, rfl⟩

theorem profileSignWidth_le_apart
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (member : (⟨condition,
      CCL.CoordinateFactorization.ConditionRelation.apart apart⟩ :
        Sigma fun queried =>
          CCL.CoordinateFactorization.ConditionRelation queried
            analysis.profile.factor) ∈ analysis.profile.relations) :
    profileSignWidth analysis ≤
      ProfileEventLeaf.apartSignWidth analysis condition apart :=
  profileSignWidth_le_relation analysis _ member

namespace ProfileEventLeaf

/-- At the single profile-wide request width, every two evaluations of any
recorded apart condition have the same strict sign. -/
theorem profile_condition_eval_mul_pos
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (condition : CCL.CoordinateFactorization.Polynomial)
    (apart : RFAP.PathClearance.CoprimeCertificate
      analysis.profile.factor.polynomial condition)
    (member : (⟨condition,
      CCL.CoordinateFactorization.ConditionRelation.apart apart⟩ :
        Sigma fun queried =>
          CCL.CoordinateFactorization.ConditionRelation queried
            analysis.profile.factor) ∈ analysis.profile.relations)
    {left right : Coordinate}
    (leftInside : (leaf.request
      (profileSignWidth analysis)).cell.interval.Contains left)
    (rightInside : (leaf.request
      (profileSignWidth analysis)).cell.interval.Contains right) :
    0 < condition.eval left * condition.eval right :=
  leaf.condition_eval_mul_pos_of_le condition apart
    (profileSignWidth analysis) (profileSignWidth_pos analysis)
      (profileSignWidth_le_apart analysis condition apart member)
        leftInside rightInside

end ProfileEventLeaf

/-! ## Exhaustive inside/outside classification of profile roots -/

abbrev ProfileRelation
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :=
  Sigma fun condition =>
    CCL.CoordinateFactorization.ConditionRelation condition
      analysis.profile.factor

def RootNonnegativeOnRequest
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry : ProfileRelation analysis)
    (epsilon : Coordinate) : Prop :=
  ∀ parameter : Coordinate,
    (leaf.request epsilon).cell.interval.Contains parameter →
    analysis.profile.factor.polynomial.eval parameter = 0 →
    0 ≤ entry.1.eval parameter

def ConditionNegativeOnRequest
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry : ProfileRelation analysis)
    (epsilon : Coordinate) : Prop :=
  ∀ parameter : Coordinate,
    (leaf.request epsilon).cell.interval.Contains parameter →
    entry.1.eval parameter < 0

/-- One relation is either nonnegative at every displayed rational parameter
where the profile factor evaluates exactly to zero, or strictly negative
throughout the entire rational request interval. -/
inductive RootConditionClassification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry : ProfileRelation analysis)
    (epsilon : Coordinate) where
  | nonnegative (holds : RootNonnegativeOnRequest leaf entry epsilon)
  | negative (holds : ConditionNegativeOnRequest leaf entry epsilon)

private theorem negative_of_mul_pos_right_neg
    {left right : Coordinate} (product : 0 < left * right)
    (rightNegative : right < 0) : left < 0 := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · exact leftNegative
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        leftPositive rightNegative
    exact (lt_asymm product negative).elim

private theorem positive_of_mul_pos_right_pos
    {left right : Coordinate} (product : 0 < left * right)
    (rightPositive : 0 < right) : 0 < left := by
  rcases lt_trichotomy left 0 with leftNegative | leftZero | leftPositive
  · have negative :=
      RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        leftNegative rightPositive
    exact (lt_asymm product negative).elim
  · rw [leftZero, RFAP.ConstructiveFraction.zero_mul_direct] at product
    exact (lt_irrefl 0 product).elim
  · exact leftPositive

/-- Classify one equality/apart relation using one displayed event sample.
Equality ownership is read exactly at roots; an apart relation transports the
sample's strict sign across the whole request. -/
def classifyRootCondition
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (entry : ProfileRelation analysis)
    (member : entry ∈ analysis.profile.relations)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileSignWidth analysis)
    (sample : Coordinate)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    RootConditionClassification leaf entry epsilon := by
  rcases entry with ⟨condition, relation⟩
  cases relation with
  | equality cofactor factorization =>
      exact .nonnegative (by
        intro parameter _inside factorZero
        rw [CCL.CoordinateFactorization.eval_factorization
          factorization parameter, factorZero,
          RFAP.ConstructiveFraction.zero_mul_direct])
  | apart apart =>
      have apartWidthLe : epsilon ≤
          ProfileEventLeaf.apartSignWidth analysis condition apart :=
        epsilonLe.trans
          (profileSignWidth_le_apart analysis condition apart member)
      have sampleStable := leaf.condition_eval_mul_pos_of_le condition apart
        epsilon positive apartWidthLe sampleInside sampleInside
      by_cases sampleNegative : condition.eval sample < 0
      · exact .negative (by
          intro parameter parameterInside
          exact negative_of_mul_pos_right_neg
            (leaf.condition_eval_mul_pos_of_le condition apart epsilon positive
              apartWidthLe parameterInside sampleInside)
            sampleNegative)
      · have sampleNonnegative : 0 ≤ condition.eval sample :=
          le_of_not_gt sampleNegative
        have sampleNonzero : condition.eval sample ≠ 0 := by
          intro sampleZero
          rw [sampleZero, RFAP.ConstructiveFraction.zero_mul_direct]
            at sampleStable
          exact (lt_irrefl 0 sampleStable).elim
        have samplePositive : 0 < condition.eval sample :=
          lt_of_le_of_ne sampleNonnegative (Ne.symm sampleNonzero)
        exact .nonnegative (by
          intro parameter parameterInside _factorZero
          exact (positive_of_mul_pos_right_pos
            (leaf.condition_eval_mul_pos_of_le condition apart epsilon positive
              apartWidthLe parameterInside sampleInside)
            samplePositive).le)

/-- Finite scan result for a displayed sublist of the profile relations. -/
inductive RootRelationsClassification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate)
    (relations : List (ProfileRelation analysis)) where
  | inside (holds : ∀ entry ∈ relations,
      RootNonnegativeOnRequest leaf entry epsilon)
  | outside (entry : ProfileRelation analysis) (member : entry ∈ relations)
      (fails : ConditionNegativeOnRequest leaf entry epsilon)

/-- Execute the finite equality/apart scan for any displayed relation
sublist whose entries come from the complete profile. -/
def classifyRootRelations
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileSignWidth analysis)
    (sample : Coordinate)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    ∀ (relations : List (ProfileRelation analysis)),
      (∀ entry ∈ relations, entry ∈ analysis.profile.relations) →
        RootRelationsClassification leaf epsilon relations
  | [], _ => .inside (by intro entry member; simp at member)
  | head :: tail, subset =>
      match classifyRootCondition leaf head
          (subset head List.mem_cons_self) epsilon positive epsilonLe sample
            sampleInside with
      | .negative fails => .outside head List.mem_cons_self fails
      | .nonnegative headHolds =>
          match classifyRootRelations leaf epsilon positive epsilonLe sample
              sampleInside tail
              (fun entry member => subset entry
                (List.mem_cons_of_mem head member)) with
          | .outside entry member fails =>
              .outside entry (List.mem_cons_of_mem head member) fails
          | .inside tailHolds =>
              .inside (by
                intro entry member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact headHolds
                · exact tailHolds entry tailMember)

/-- Pointwise list-shaped nonnegativity of every relation in one profile. -/
def RelationsNonnegativeAt
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (parameter : Coordinate) :
    Prop :=
  analysis.profile.relations.Forall fun entry =>
    0 ≤ entry.1.eval parameter

/-- The profile's relation list is aligned with the denominator quadrance
followed by the four cleared box conditions.  The first condition is
automatically nonnegative, so complete relation nonnegativity is equivalent
to the original four-condition box predicate. -/
theorem relationsNonnegativeAt_iff_listedHolds
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) (parameter : Coordinate) :
    RelationsNonnegativeAt analysis parameter ↔
      CCL.CurveBoxConditions.ListedHolds
        chart.parameterization.curve box parameter := by
  let predicate := fun condition :
      CCL.CoordinateFactorization.Polynomial =>
        0 ≤ condition.eval parameter
  have mapped : RelationsNonnegativeAt analysis parameter ↔
      (analysis.profile.relations.map Sigma.fst).Forall predicate := by
    change List.Forall (predicate ∘ Sigma.fst)
        analysis.profile.relations ↔
      List.Forall predicate (analysis.profile.relations.map Sigma.fst)
    exact (List.forall_map_iff (l := analysis.profile.relations)
      (p := predicate) Sigma.fst).symm
  have aligned :
      (analysis.profile.relations.map Sigma.fst).Forall predicate =
        (CCL.CurveBoxConditions.profiledConditionPolynomials
          chart.parameterization.curve box).Forall predicate :=
    congrArg (fun conditions => conditions.Forall predicate)
      analysis.profile.conditions_eq
  have profiled :=
    CCL.CurveBoxConditions.profiledListedHolds_iff_listedHolds
      chart.parameterization.curve box parameter
  exact mapped.trans
    ⟨fun holds => profiled.mp (aligned.mp holds),
      fun holds => aligned.mpr (profiled.mpr holds)⟩

/-- The complete requested profile event is classified semantically: every
aligned denominator/box relation is nonnegative at every displayed rational
profile root, or one fixed aligned relation is strictly negative at every
such root.  `ConditionProfile.conditions_eq` identifies these relations with
the denominator quadrance followed by the four box conditions. -/
inductive ProfileEventBoxClassification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) where
  | inside (holds : ∀ entry ∈ analysis.profile.relations,
      RootNonnegativeOnRequest leaf entry epsilon)
  | outside (entry : ProfileRelation analysis)
      (member : entry ∈ analysis.profile.relations)
      (fails : ConditionNegativeOnRequest leaf entry epsilon)

/-- Compute the whole-profile-event box classification from one displayed
parameter in the profile-wide request. -/
def classifyProfileEventBox
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileSignWidth analysis)
    (sample : Coordinate)
    (sampleInside : (leaf.request epsilon).cell.interval.Contains sample) :
    ProfileEventBoxClassification leaf epsilon := by
  have classified := classifyRootRelations leaf epsilon positive epsilonLe
    sample sampleInside analysis.profile.relations
    (by intro entry member; exact member)
  cases classified with
  | inside allNonnegative =>
      exact .inside allNonnegative
  | outside entry entryMember fails =>
      exact .outside entry entryMember fails

/-- Total whole-event classifier.  The lower endpoint is already a
displayed rational sample in the closed requested cell; no affine point or
denominator choice is needed to determine the profile-root signs. -/
def classifyRequestedProfileEventBox
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    ProfileEventBoxClassification leaf (profileSignWidth analysis) :=
  classifyProfileEventBox leaf (profileSignWidth analysis)
    (profileSignWidth_pos analysis) le_rfl
    (leaf.request (profileSignWidth analysis)).cell.interval.lower
    ⟨le_rfl,
      (leaf.request (profileSignWidth analysis)).cell.proper.le⟩

/-- Affine meaning of the total profile classification.  The inside branch
is conditional on a supplied displayed rational factor zero; it asserts no
root existence.  The outside branch excludes every displayed non-pole
parameter in the whole requested interval and needs no root premise. -/
inductive ProfileEventAffineClassification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) (epsilon : Coordinate) where
  | inside (contains : ∀ parameter : Coordinate,
      (leaf.request epsilon).cell.interval.Contains parameter →
      analysis.profile.factor.polynomial.eval parameter = 0 →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      box.Contains (chart.parameterization.curve.point parameter))
  | outside (excludes : ∀ parameter : Coordinate,
      (leaf.request epsilon).cell.interval.Contains parameter →
      chart.parameterization.curve.denominatorAt parameter ≠ 0 →
      ¬ box.Contains (chart.parameterization.curve.point parameter))

/-- Convert a sufficiently narrow finite aligned-sign request into its exact
affine box semantics, without constructing or quantifying over a completed
root. -/
def classifyProfileEventAffine
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (epsilonLe : epsilon ≤ profileSignWidth analysis) :
    ProfileEventAffineClassification leaf epsilon := by
  let sample := (leaf.request epsilon).cell.interval.lower
  have sampleInside : (leaf.request epsilon).cell.interval.Contains sample :=
    ⟨le_rfl, (leaf.request epsilon).cell.proper.le⟩
  match classifyProfileEventBox leaf epsilon positive epsilonLe sample
      sampleInside with
  | .inside allNonnegative =>
      exact .inside (by
        intro parameter parameterInside factorZero denominatorNonzero
        have relationsNonnegative : RelationsNonnegativeAt analysis
            parameter :=
          List.forall_iff_forall_mem.mpr (by
            intro entry member
            exact allNonnegative entry member parameter parameterInside
              factorZero)
        have listed :=
          (relationsNonnegativeAt_iff_listedHolds analysis parameter).mp
            relationsNonnegative
        have holds :=
          (CCL.CurveBoxConditions.listedHolds_iff_holds
            chart.parameterization.curve box parameter).mp listed
        exact (CCL.CurveBoxConditions.holds_iff_contains
          chart.parameterization.curve box parameter denominatorNonzero).mp
            holds)
  | .outside entry member negative =>
      exact .outside (by
        intro parameter parameterInside denominatorNonzero contained
        have holds :=
          (CCL.CurveBoxConditions.holds_iff_contains
            chart.parameterization.curve box parameter denominatorNonzero).mpr
              contained
        have listed :=
          (CCL.CurveBoxConditions.listedHolds_iff_holds
            chart.parameterization.curve box parameter).mpr holds
        have relationsNonnegative :=
          (relationsNonnegativeAt_iff_listedHolds analysis parameter).mpr
            listed
        have entryNonnegative :=
          (List.forall_iff_forall_mem.mp relationsNonnegative) entry member
        exact (not_lt_of_ge entryNonnegative)
          (negative parameter parameterInside))

/-- Specialization at the computed profile-sign width. -/
def classifyRequestedProfileEventAffine
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    ProfileEventAffineClassification leaf (profileSignWidth analysis) :=
  classifyProfileEventAffine leaf (profileSignWidth analysis)
    (profileSignWidth_pos analysis) le_rfl

/-- Decide whether one already-classified profile leaf carries a nonzero
event count. -/
def profileEventLeaf?
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis)
    (cell : RFAP.SturmEventPartition.Cell)
    (member : cell ∈ analysis.partition.tree.leaves) :
    Option (ProfileEventLeaf analysis) := by
  let classification := analysis.partition.classify cell member
  if countNonzero : classification.eventCount ≠ 0 then
    exact some ⟨cell, member, countNonzero⟩
  else
    exact none

/-- Complete finite list of nonzero leaves for one condition profile. -/
def profileEventLeaves
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (analysis : ProfileAnalysis factorAnalysis) :
    List (ProfileEventLeaf analysis) :=
  analysis.partition.tree.leaves.attach.filterMap fun entry =>
    profileEventLeaf? analysis entry.1 entry.2

theorem profileEventLeaf?_eq_some
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    profileEventLeaf? analysis leaf.cell leaf.member = some leaf := by
  simp only [profileEventLeaf?, dif_pos leaf.countNonzero]

/-- Every proof-bearing nonzero leaf of one profile occurs in its computed
finite list. -/
theorem mem_profileEventLeaves
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (leaf : ProfileEventLeaf analysis) :
    leaf ∈ profileEventLeaves analysis := by
  rw [profileEventLeaves, QuotientFreeList.mem_filterMap]
  refine ⟨⟨leaf.cell, leaf.member⟩, ?_, ?_⟩
  · simp only [QuotientFreeList.mem_attach]
  · exact profileEventLeaf?_eq_some leaf

/-- Homogeneous finite wrapper for the nonzero event leaves of every final
condition profile belonging to one original squarefree factor. -/
abbrev ProfileEventEntry
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :=
  Sigma fun analysis : ProfileAnalysis factorAnalysis =>
    ProfileEventLeaf analysis

/-- Complete finite nonzero-event family after exact splitting against all
four box conditions. -/
def profileEventFamily
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : List (ProfileEventEntry factorAnalysis) :=
  (CCL.CCLBoundaryCharts.analyzeConditionProfiles
    factorAnalysis).flatMap fun analysis =>
      (profileEventLeaves analysis).map fun leaf => ⟨analysis, leaf⟩

theorem mem_profileEventFamily
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    {analysis : ProfileAnalysis factorAnalysis}
    (analysisMember : analysis ∈
      CCL.CCLBoundaryCharts.analyzeConditionProfiles
        factorAnalysis)
    (leaf : ProfileEventLeaf analysis) :
    (⟨analysis, leaf⟩ : ProfileEventEntry factorAnalysis) ∈
      profileEventFamily factorAnalysis := by
  rw [profileEventFamily, QuotientFreeList.mem_flatMap]
  refine ⟨analysis, analysisMember, ?_⟩
  rw [QuotientFreeList.mem_map]
  exact ⟨leaf, mem_profileEventLeaves leaf, rfl⟩

/-- A displayed rational root of an original squarefree factor, assigned by
finite scans to one exact condition profile and one nonzero profile event. -/
structure LocatedProfileEvent
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (parameter : Coordinate) where
  entry : ProfileEventEntry factorAnalysis
  member : entry ∈ profileEventFamily factorAnalysis
  profileZero : entry.1.profile.factor.polynomial.eval parameter = 0
  contains : entry.2.cell.interval.Contains parameter

/-- Execute the profile scan and the aligned Sturm-tree locator.  Thus every
displayed rational root of the original squarefree factor belongs to an
entry of the complete profile-event family. -/
def locateProfileEvent
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (parameter : Coordinate)
    (inside : chart.cell.interval.Contains parameter)
    (factorZero : factorAnalysis.factor.polynomial.eval parameter = 0) :
    LocatedProfileEvent factorAnalysis parameter := by
  let locatedProfile := factorAnalysis.conditionProfiles.locateRoot parameter
    factorZero
  let analysis : ProfileAnalysis factorAnalysis :=
    { profile := locatedProfile.profile
      partition :=
        CCL.CurveBoxEventPartition.classifySquarefreeEvents
          locatedProfile.profile.factor.polynomial
            locatedProfile.profile.factor.nonzero
              locatedProfile.profile.factor.squarefree
                chart.parameterization.curve box chart.cell }
  have analysisMember : analysis ∈
      CCL.CCLBoundaryCharts.analyzeConditionProfiles
        factorAnalysis := by
    rw [CCL.CCLBoundaryCharts.analyzeConditionProfiles,
      QuotientFreeList.mem_map]
    exact ⟨⟨locatedProfile.profile, locatedProfile.member⟩,
      QuotientFreeList.mem_attach _ _, rfl⟩
  let location := analysis.partition.locate parameter inside
  have parameterInside :
      location.classification.cell.interval.Contains parameter := by
    rw [location.classification_cell]
    exact location.contains
  have countNonzero :=
    location.classification.eventCount_ne_zero_of_root parameter
      parameterInside locatedProfile.zero
  let leaf : ProfileEventLeaf analysis :=
    { cell := location.leaf
      member := location.member
      countNonzero := by
        rw [← location.classification_eq]
        exact countNonzero }
  exact
    { entry := ⟨analysis, leaf⟩
      member := mem_profileEventFamily analysisMember leaf
      profileZero := locatedProfile.zero
      contains := location.contains }

end CCL.PersistentCCLConditionProfiles
