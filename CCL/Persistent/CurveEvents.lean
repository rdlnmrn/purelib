import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.CurveClear

/-!
# Persistent projective shrinking of nonzero CCL curve events

Every nonconstant curve analysis has already been split into squarefree
coordinate factors and an aligned finite partition.  This module extracts the
nonzero-count leaves as explicit finite event records.  Each record carries
the existing central-third Sturm transducer and, simultaneously, a homogeneous
projective image bound for its rational boundary chart.

The homogeneous estimate remains valid across an affine pole.  It is therefore
combined with each chart's positive homogeneous-weight lower bound to obtain
the genuine finite `chi^2` shrinking fact needed to couple a narrowing
parameter event to a narrowing winding box without choosing a completed
parameter or root.
-/

namespace CCL.PersistentCCLCurveEvents

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis

open RFAP.ComputablePolynomial.DensePolynomial

/-- One squarefree parameter leaf whose doubled Sturm count is nonzero. -/
structure EventLeaf
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) where
  cell : RFAP.SturmEventPartition.Cell
  member : cell ∈ factorAnalysis.partition.tree.leaves
  countNonzero :
    (factorAnalysis.partition.classify cell member).eventCount ≠ 0

namespace EventLeaf

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
    (leaf : EventLeaf factorAnalysis) :=
  factorAnalysis.partition.classify leaf.cell leaf.member

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
    (leaf : EventLeaf factorAnalysis) :
    RFAP.SturmNonzeroEvent.State factorAnalysis.factor.polynomial :=
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
    (leaf : EventLeaf factorAnalysis) :
    leaf.classification.cell = leaf.cell :=
  factorAnalysis.partition.classify_cell leaf.cell leaf.member

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
    (leaf : EventLeaf factorAnalysis) : leaf.state.cell = leaf.cell := by
  exact leaf.classification_cell

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
    (leaf : EventLeaf factorAnalysis) :
    leaf.cell.interval.Refines chart.cell.interval := by
  rw [← leaf.classification_cell]
  exact leaf.classification.refines

/-- Refine this nonzero parameter event to a requested rational width. -/
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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate) :
    RFAP.SturmNonzeroEvent.State factorAnalysis.factor.polynomial :=
  RFAP.SturmNonzeroEvent.request factorAnalysis.factor.polynomial
    factorAnalysis.factor.nonzero leaf.state epsilon

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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate) :
    (leaf.request epsilon).cell.interval.Refines chart.cell.interval := by
  exact RFAP.SturmNonzeroEvent.intervalRefines_trans
    (RFAP.SturmNonzeroEvent.request_refines
      factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero
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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (leaf.request epsilon).cell.interval.width ≤ epsilon :=
  RFAP.SturmNonzeroEvent.request_width_le
    factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero leaf.state
      epsilon positive

/-- Re-run the finite event scanner on a requested subcell.  Refinement keeps
the cell below the original coefficient-computed resolution width, so this
does not require another search or a root witness. -/
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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate) :
    RFAP.CauchyCells.CauchyEventResolution
      (RFAP.SturmRootCount.reducedNumerator
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial)
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial)
      (leaf.request epsilon).cell.interval := by
  apply CCL.CurveBoxEventPartition.polynomialEventResolutionOfBounds
    factorAnalysis.factor.polynomial chart.cell (leaf.request epsilon).cell
  · exact leaf.request_refines_chart epsilon
  · have refinesLeaf :
        (leaf.request epsilon).cell.interval.Refines leaf.cell.interval := by
      simpa only [request, leaf.state_cell] using
        RFAP.SturmNonzeroEvent.request_refines
          factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero
            leaf.state epsilon
    have widthLe : (leaf.request epsilon).cell.interval.width ≤
        leaf.cell.interval.width :=
      RFAP.ConstructiveFraction.sub_le_sub_direct refinesLeaf.2 refinesLeaf.1
    have leafWidthSmall : leaf.cell.interval.width <
        CCL.CurveBoxEventPartition.squarefreeLeafWidth
          factorAnalysis.factor.polynomial factorAnalysis.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact widthLe.trans_lt
      (leafWidthSmall.trans_le
        ((CCL.CurveBoxEventPartition.squarefreeLeafWidth_le_common
          factorAnalysis.factor.polynomial factorAnalysis.factor.squarefree
            chart.parameterization.curve box chart.cell).trans
          (CCL.CurveBoxEventPartition.commonLeafWidth_le_event
            factorAnalysis.factor.polynomial chart.parameterization.curve box
              chart.cell)))

/-- Fixed finite coefficient for the gcd-reduced event residual. -/
def reducedEventResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : Coordinate :=
  4 * RFAP.IntervalSign.denseEvalSqLipschitzBound
    (RFAP.SturmRootCount.reducedDenominator
      (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
      factorAnalysis.factor.polynomial) chart.cell.interval

theorem reducedEventResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    0 ≤ reducedEventResidualCoefficient factorAnalysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.IntervalSign.denseHornerSqBounds_nonneg
      (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval).2

/-- Every rational parameter in a requested nonzero event has uniformly
small gcd-reduced factor residual.  The bound is quadratic in the requested
width and is obtained solely from finite endpoint signs and Horner bounds. -/
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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (RFAP.SturmRootCount.reducedDenominator
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial).eval parameter ^ 2 ≤
      reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let event := factorAnalysis.factor.polynomial
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
  have refinesChart := leaf.request_refines_chart epsilon
  have lipschitzLe : localLipschitz ≤ chartLipschitz := by
    simpa only [localLipschitz, chartLipschitz, requested, reduced] using
      RFAP.IntervalSign.denseEvalSqLipschitzBound_le_of_refines
        reduced refinesChart
  have chartNonnegative : 0 ≤ chartLipschitz := by
    simpa only [chartLipschitz] using
      (RFAP.IntervalSign.denseHornerSqBounds_nonneg reduced
        chart.cell.interval).2
  have coefficientLe : 4 * localLipschitz ≤ 4 * chartLipschitz :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct lipschitzLe
      (show (0 : Coordinate) ≤ 4 by decide)
  have widthLe := leaf.request_width_le epsilon positive
  have widthSqLe : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      requested.cell.interval.width_nonneg widthLe 2
  have widthSqNonnegative : 0 ≤ requested.cell.interval.width ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct requested.cell.interval.width
  have chartCoefficientNonnegative : 0 ≤ 4 * chartLipschitz :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) chartNonnegative
  change reduced.eval parameter ^ 2 ≤
    (4 * chartLipschitz) * epsilon ^ 2
  exact localBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_direct coefficientLe widthSqLe
      widthSqNonnegative chartCoefficientNonnegative)

/-- Fixed coefficient for the residual of the selected squarefree factor,
including the finite derivative gcd that was divided out before Sturm
counting. -/
def factorEventResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : Coordinate :=
  RFAP.PathClearance.evalSqBound
      (RFAP.ComputableGCD.gcd
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval *
    reducedEventResidualCoefficient factorAnalysis

theorem factorEventResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    0 ≤ factorEventResidualCoefficient factorAnalysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.PathClearance.evalSqBound_nonneg
      (RFAP.ComputableGCD.gcd
        (RFAP.ComputableDerivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial) chart.cell.interval)
    (reducedEventResidualCoefficient_nonneg factorAnalysis)

/-- The selected factor itself is uniformly small on the requested event.
The lift from the reduced Sturm denominator uses the displayed finite
derivative-gcd factor, bounded by a finite Horner scan on the original chart. -/
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
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    factorAnalysis.factor.polynomial.eval parameter ^ 2 ≤
      factorEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let event := factorAnalysis.factor.polynomial
  let common := RFAP.ComputableGCD.gcd
    (RFAP.ComputableDerivative.derivative event) event
  let reduced := RFAP.SturmRootCount.reducedDenominator
    (RFAP.ComputableDerivative.derivative event) event
  let commonBound := RFAP.PathClearance.evalSqBound common
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤ commonBound := by
    exact RFAP.PathClearance.eval_sq_le_evalSqBound common
      chart.cell.interval parameterInsideChart
  have reducedEvalBound : reduced.eval parameter ^ 2 ≤
      reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [event, reduced] using
      leaf.reduced_eval_sq_request_le epsilon positive parameter inside
  have productBound :
      common.eval parameter ^ 2 * reduced.eval parameter ^ 2 ≤
        commonBound *
          (reducedEventResidualCoefficient factorAnalysis * epsilon ^ 2) :=
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
    (commonBound * reducedEventResidualCoefficient factorAnalysis) *
      epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- The explicitly computed product of all other squarefree occurrences in
the finite curve-gcd decomposition. -/
def curveGCDCofactor
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : CCL.CoordinateFactorization.Polynomial :=
  CCL.CoordinateFactorization.factorCofactor
    factorAnalysis.factor.polynomial
    (CCL.CurveEvents.eventDecomposition data
      gcdDegreePositive).factors

/-- Fixed coefficient for the complete curve-gcd residual on a requested
event cell. -/
def gcdEventResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : Coordinate :=
  factorEventResidualCoefficient factorAnalysis *
    RFAP.PathClearance.evalSqBound
      (curveGCDCofactor factorAnalysis) chart.cell.interval

theorem gcdEventResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    0 ≤ gcdEventResidualCoefficient factorAnalysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (factorEventResidualCoefficient_nonneg factorAnalysis)
    (RFAP.PathClearance.evalSqBound_nonneg
      (curveGCDCofactor factorAnalysis) chart.cell.interval)

/-- Every parameter in a requested nonzero squarefree event makes the full
curve gcd uniformly small.  Other factor occurrences are retained as an
explicit finite cofactor and bounded on the original chart. -/
theorem gcd_eval_sq_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let decomposition := CCL.CurveEvents.eventDecomposition data
    gcdDegreePositive
  let cofactor := curveGCDCofactor factorAnalysis
  let cofactorBound := RFAP.PathClearance.evalSqBound cofactor
    chart.cell.interval
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have factorBound :=
    leaf.factor_eval_sq_request_le epsilon positive parameter inside
  have cofactorEvalBound : cofactor.eval parameter ^ 2 ≤ cofactorBound :=
    RFAP.PathClearance.eval_sq_le_evalSqBound cofactor
      chart.cell.interval parameterInsideChart
  have productBound :
      factorAnalysis.factor.polynomial.eval parameter ^ 2 *
          cofactor.eval parameter ^ 2 ≤
        (factorEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
          cofactorBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct factorBound
      cofactorEvalBound
      (RFAP.ConstructiveFraction.sq_nonneg_direct (cofactor.eval parameter))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (factorEventResidualCoefficient_nonneg factorAnalysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have identity :
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
        factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
    calc
      (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).eval parameter =
          (CCL.CoordinateFactorization.factorProduct
            decomposition.factors).eval parameter :=
        decomposition.evalIdentity parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          (CCL.CoordinateFactorization.factorCofactor
            factorAnalysis.factor.polynomial decomposition.factors).eval
              parameter :=
        CCL.CoordinateFactorization.factorProduct_eval_eq_factor_mul_cofactor
          factorAnalysis.factor decomposition.factors factorAnalysis.member
            parameter
      _ = factorAnalysis.factor.polynomial.eval parameter *
          cofactor.eval parameter := by
        rfl
  rw [identity, mul_pow]
  change factorAnalysis.factor.polynomial.eval parameter ^ 2 *
      cofactor.eval parameter ^ 2 ≤
    (factorEventResidualCoefficient factorAnalysis * cofactorBound) *
      epsilon ^ 2
  exact productBound.trans_eq (by ring1)

/-- Finite chart-wide majorant for the two cofactors that lift the executable
curve gcd back to the real and imaginary denominator-cleared coordinates. -/
def curveGCDLiftCoefficient
    (p : GaussianPolynomial) {form : HermitianForm}
    (chart : BoundedChart form) : Coordinate :=
  RFAP.PathClearance.evalSqBound
      (RFAP.ComputableGCD.leftFactor
        (CCL.CurveClear.realPolynomial p
          chart.parameterization.curve)
        (CCL.CurveClear.imaginaryPolynomial p
          chart.parameterization.curve)) chart.cell.interval +
    RFAP.PathClearance.evalSqBound
      (RFAP.ComputableGCD.rightFactor
        (CCL.CurveClear.realPolynomial p
          chart.parameterization.curve)
        (CCL.CurveClear.imaginaryPolynomial p
          chart.parameterization.curve)) chart.cell.interval

theorem curveGCDLiftCoefficient_nonneg
    (p : GaussianPolynomial) {form : HermitianForm}
    (chart : BoundedChart form) : 0 ≤ curveGCDLiftCoefficient p chart :=
  add_nonneg
    (RFAP.PathClearance.evalSqBound_nonneg _ _)
    (RFAP.PathClearance.evalSqBound_nonneg _ _)

/-- Fixed coefficient for the homogeneous denominator-cleared polynomial
residual on a requested nonzero event. -/
def clearedEventResidualCoefficient
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : Coordinate :=
  gcdEventResidualCoefficient factorAnalysis *
    curveGCDLiftCoefficient p chart

theorem clearedEventResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    0 ≤ clearedEventResidualCoefficient factorAnalysis :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    (gcdEventResidualCoefficient_nonneg factorAnalysis)
    (curveGCDLiftCoefficient_nonneg p chart)

/-- Both denominator-cleared coordinate residuals are uniformly small on the
whole requested event cell.  This is the coefficient-computable event-wide
bridge from the squarefree Sturm transducer back to the original curve
substitution. -/
theorem cleared_coordinate_norm_sq_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    (CCL.CurveClear.realPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 +
      (CCL.CurveClear.imaginaryPolynomial p
        chart.parameterization.curve).eval parameter ^ 2 ≤
      clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  let real := CCL.CurveClear.realPolynomial p
    chart.parameterization.curve
  let imaginary := CCL.CurveClear.imaginaryPolynomial p
    chart.parameterization.curve
  let common := CCL.CurveClear.gcdPolynomial p
    chart.parameterization.curve
  let left := RFAP.ComputableGCD.leftFactor real imaginary
  let right := RFAP.ComputableGCD.rightFactor real imaginary
  let liftBound := curveGCDLiftCoefficient p chart
  have refinesChart := leaf.request_refines_chart epsilon
  have parameterInsideChart : chart.cell.interval.Contains parameter :=
    ⟨refinesChart.1.trans inside.1, inside.2.trans refinesChart.2⟩
  have commonEvalBound : common.eval parameter ^ 2 ≤
      gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [common] using
      leaf.gcd_eval_sq_request_le epsilon positive parameter inside
  have leftEvalBound : left.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound left chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound left
      chart.cell.interval parameterInsideChart
  have rightEvalBound : right.eval parameter ^ 2 ≤
      RFAP.PathClearance.evalSqBound right chart.cell.interval :=
    RFAP.PathClearance.eval_sq_le_evalSqBound right
      chart.cell.interval parameterInsideChart
  have cofactorSumBound :
      left.eval parameter ^ 2 + right.eval parameter ^ 2 ≤ liftBound := by
    simpa only [left, right, real, imaginary, liftBound,
      curveGCDLiftCoefficient] using add_le_add leftEvalBound rightEvalBound
  have productBound :
      common.eval parameter ^ 2 *
          (left.eval parameter ^ 2 + right.eval parameter ^ 2) ≤
        (gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
          liftBound :=
    RFAP.ConstructiveFraction.mul_le_mul_direct commonEvalBound
      cofactorSumBound
      (add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (left.eval parameter))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (right.eval parameter)))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (gcdEventResidualCoefficient_nonneg factorAnalysis)
        (RFAP.ConstructiveFraction.sq_nonneg_direct epsilon))
  have realIdentity : real.eval parameter =
      common.eval parameter * left.eval parameter := by
    simpa only [real, imaginary, common, left,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.leftFactor_eval_identity real imaginary parameter
  have imaginaryIdentity : imaginary.eval parameter =
      common.eval parameter * right.eval parameter := by
    simpa only [real, imaginary, common, right,
      CCL.CurveClear.gcdPolynomial] using
      RFAP.ComputableGCD.rightFactor_eval_identity real imaginary parameter
  change real.eval parameter ^ 2 + imaginary.eval parameter ^ 2 ≤
    (gcdEventResidualCoefficient factorAnalysis * liftBound) * epsilon ^ 2
  rw [realIdentity, imaginaryIdentity, mul_pow, mul_pow]
  calc
    common.eval parameter ^ 2 * left.eval parameter ^ 2 +
        common.eval parameter ^ 2 * right.eval parameter ^ 2 =
      common.eval parameter ^ 2 *
        (left.eval parameter ^ 2 + right.eval parameter ^ 2) := by ring1
    _ ≤ (gcdEventResidualCoefficient factorAnalysis * epsilon ^ 2) *
        liftBound := productBound
    _ = (gcdEventResidualCoefficient factorAnalysis * liftBound) *
        epsilon ^ 2 := by ring1

/-- Gaussian form of `cleared_coordinate_norm_sq_request_le`. -/
theorem normSq_clearedEval_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (inside : (leaf.request epsilon).cell.interval.Contains parameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.RationalCurve.clearedEval p
          chart.parameterization.curve).eval
            (RFAP.PathPolynomial.ofCoordinate parameter)) ≤
      clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
  simpa only [CCL.CurveClear.realPolynomial,
    CCL.CurveClear.imaginaryPolynomial,
    CCL.RationalCurve.clearedReal,
    CCL.RationalCurve.clearedImag,
    RFAP.PathPolynomial.eval_realPart,
    RFAP.PathPolynomial.eval_imagPart,
    RFAP.ConstructiveGaussian.Gaussian.normSq] using
      leaf.cleared_coordinate_norm_sq_request_le epsilon positive parameter
        inside

/-- Fixed coefficient converting the homogeneous event residual into an
original-polynomial residual at affine chart points lying in `targetBox`. -/
def affineEventResidualCoefficient
    {p : GaussianPolynomial} {box targetBox : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : Coordinate :=
  clearedEventResidualCoefficient factorAnalysis /
    chart.affineDenominatorPowerNormSqLower p targetBox

theorem affineEventResidualCoefficient_nonneg
    {p : GaussianPolynomial} {box targetBox : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) :
    0 ≤ affineEventResidualCoefficient
      (targetBox := targetBox) factorAnalysis :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (clearedEventResidualCoefficient_nonneg factorAnalysis)
    (chart.affineDenominatorPowerNormSqLower_pos p targetBox).le

/-- Every point where the requested event meets a displayed finite box has
small original-polynomial residual.  The coefficient is uniform over the
whole box and event cell; the chart denominator may approach zero elsewhere. -/
theorem normSq_eval_point_request_le_of_inside
    {p : GaussianPolynomial} {box targetBox : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) (parameter : Coordinate)
    (parameterInside :
      (leaf.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (chart.parameterization.curve.point parameter)) ≤
      affineEventResidualCoefficient (targetBox := targetBox)
        factorAnalysis * epsilon ^ 2 := by
  let curve := chart.parameterization.curve
  let power :=
    (CCL.RationalCurve.clearingState p curve).denominatorPower.eval
      (RFAP.PathPolynomial.ofCoordinate parameter)
  let lower := chart.affineDenominatorPowerNormSqLower p targetBox
  let residual := RFAP.ConstructiveGaussian.Gaussian.normSq
    (p.eval (curve.point parameter))
  have lowerPositive : 0 < lower := by
    simpa only [lower, curve] using
      chart.affineDenominatorPowerNormSqLower_pos p targetBox
  have powerLower : lower ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power := by
    simpa only [lower, power, curve] using
      chart.affineDenominatorPowerNormSqLower_le p targetBox parameter
        denominatorNonzero pointInside
  have clearedBound :=
    leaf.normSq_clearedEval_request_le epsilon positive parameter
      parameterInside
  have semantics := CCL.RationalCurve.eval_clearedEval p curve
    parameter denominatorNonzero
  have clearedProductBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual ≤
        clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 := by
    simpa only [curve, power, residual, semantics,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul] using clearedBound
  have lowerProductBound : lower * residual ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct powerLower
      (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
  change residual ≤
    (clearedEventResidualCoefficient factorAnalysis / lower) * epsilon ^ 2
  calc
    residual ≤
        (clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2) /
          lower := by
      apply (RFAP.ConstructiveFraction.le_div_iff_pos lowerPositive).2
      calc
        residual * lower = lower * residual :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ ≤ RFAP.ConstructiveGaussian.Gaussian.normSq power * residual :=
          lowerProductBound
        _ ≤ clearedEventResidualCoefficient factorAnalysis * epsilon ^ 2 :=
          clearedProductBound
    _ = (clearedEventResidualCoefficient factorAnalysis / lower) *
        epsilon ^ 2 := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      rw [RFAP.ConstructiveFraction.mul_assoc,
        RFAP.ConstructiveFraction.mul_comm (epsilon ^ 2),
        ← RFAP.ConstructiveFraction.mul_assoc]

private theorem sq_le_sq_of_nonneg
    {left right : Coordinate} (order : left ≤ right)
    (leftNonnegative : 0 ≤ left) (rightNonnegative : 0 ≤ right) :
    left ^ 2 ≤ right ^ 2 := by
  rw [pow_two, pow_two]
  exact RFAP.ConstructiveFraction.mul_le_mul_direct order order
    leftNonnegative rightNonnegative

/-- The homogeneous image of a requested nonzero event cell has squared
cross diameter bounded by the original chart coefficient times the requested
parameter width squared.  No affine denominator clearance is required. -/
theorem normSq_cross_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) {left right : Coordinate}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Chordal.Proj.cross
          (chart.projective left) (chart.projective right)) ≤
      CCL.RationalCurveBounds.crossVariationCoefficient
          chart.parameterization.curve chart.cell.interval * epsilon ^ 2 := by
  let requested := leaf.request epsilon
  have requestedRefines := leaf.request_refines_chart epsilon
  have leftChart : chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have crossBound := CCL.RationalCurveBounds.normSq_cross_le
    chart.parameterization.curve chart.cell.interval leftChart rightChart
  have parameterBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    sq_le_sq_of_nonneg (leaf.request_width_le epsilon positive)
      requested.cell.interval.width_nonneg positive.le
  exact crossBound.trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      (CCL.RationalCurveBounds.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval))

/-- The genuine squared-chordal diameter of a requested nonzero event cell is
bounded by a coefficient fixed by the original finite chart times the square
of the requested width.  The full homogeneous-weight lower bound makes this
valid even when the event interval contains an affine pole. -/
theorem chordalSq_request_le
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) (epsilon : Coordinate)
    (positive : 0 < epsilon) {left right : Coordinate}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := leaf.request epsilon
  have requestedRefines := leaf.request_refines_chart epsilon
  have leftChart : chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have parameterBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    sq_le_sq_of_nonneg (leaf.request_width_le epsilon positive)
      requested.cell.interval.width_nonneg positive.le
  exact (chart.chordalSq_le_uniform leftChart rightChart).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      chart.uniformChordalVariationCoefficient_nonneg)

end EventLeaf

namespace LocatedSquarefreeCurveRoot

/-- Repackage the factor selected by the finite first-zero scan as the
factor-analysis record consumed by the persistent event API. -/
@[reducible] def factorAnalysis
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    SquarefreeFactorAnalysis p box chart data gcdDegreePositive where
  factor := located.factor
  member := located.factorMember
  conditionProfiles :=
    CCL.CoordinateFactorization.classifyConditions located.factor
      (CCL.CurveBoxConditions.profiledConditionPolynomials
        chart.parameterization.curve box)
  partition := located.partition

/-- Every displayed rational curve root is assigned to a nonzero squarefree
event leaf.  This is the pointwise coverage theorem for the finite event
enumeration; it introduces neither a completed parameter nor a root set. -/
def eventLeaf
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    EventLeaf (factorAnalysis located) := by
  have parameterInside :
      located.location.classification.cell.interval.Contains parameter := by
    rw [located.location.classification_cell]
    exact located.location.contains
  have countNonzero :=
    located.location.classification.eventCount_ne_zero_of_root parameter
      parameterInside located.factorZero
  exact
    { cell := located.location.leaf
      member := located.location.member
      countNonzero := by
        rw [← located.location.classification_eq]
        exact countNonzero }

end LocatedSquarefreeCurveRoot

/-- Decide whether one already-classified squarefree leaf carries a nonzero
event count. -/
def eventLeaf?
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)
    (cell : RFAP.SturmEventPartition.Cell)
    (member : cell ∈ factorAnalysis.partition.tree.leaves) :
    Option (EventLeaf factorAnalysis) := by
  let classification := factorAnalysis.partition.classify cell member
  if countNonzero : classification.eventCount ≠ 0 then
    exact some
      { cell := cell
        member := member
        countNonzero := countNonzero }
  else
    exact none

/-- Complete finite list of nonzero-count leaves for one squarefree factor. -/
def eventLeaves
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive) : List (EventLeaf factorAnalysis) :=
  factorAnalysis.partition.tree.leaves.attach.filterMap fun entry =>
    eventLeaf? factorAnalysis entry.1 entry.2

theorem eventLeaf?_eq_some
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) :
    eventLeaf? factorAnalysis leaf.cell leaf.member = some leaf := by
  simp only [eventLeaf?, dif_pos leaf.countNonzero]

/-- The finite extraction is extensionally complete: every proof-bearing
nonzero leaf of this partition occurs in the computed list. -/
theorem mem_eventLeaves
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (leaf : EventLeaf factorAnalysis) : leaf ∈ eventLeaves factorAnalysis := by
  rw [eventLeaves, QuotientFreeList.mem_filterMap]
  refine ⟨⟨leaf.cell, leaf.member⟩, ?_, ?_⟩
  · simp only [QuotientFreeList.mem_attach]
  · exact eventLeaf?_eq_some leaf

theorem LocatedSquarefreeCurveRoot.eventLeaf_mem
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    LocatedSquarefreeCurveRoot.eventLeaf located ∈
      eventLeaves (LocatedSquarefreeCurveRoot.factorAnalysis located) :=
  mem_eventLeaves (LocatedSquarefreeCurveRoot.eventLeaf located)

/-- The factor selected by the first-zero scan is one of the factor analyses
computed by the chart analyzer.  Retaining this membership is essential: it
connects pointwise root coverage to the executable event-family list. -/
theorem LocatedSquarefreeCurveRoot.factorAnalysis_mem
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    LocatedSquarefreeCurveRoot.factorAnalysis located ∈
      CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive := by
  rw [CCL.CCLBoundaryCharts.analyzeSquarefreeFactors,
    QuotientFreeList.mem_map]
  refine ⟨⟨located.factor, located.factorMember⟩,
    QuotientFreeList.mem_attach _ _, ?_⟩
  cases located with
  | mk factor factorMember factorZero partition partition_eq location
      boxConditions =>
      simp only [LocatedSquarefreeCurveRoot.factorAnalysis]
      cases partition_eq
      rfl

/-- Homogeneous finite wrapper for the nonzero leaves of every squarefree
factor in one nonconstant chart analysis. -/
abbrev EventEntry
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree} :=
  Sigma fun factorAnalysis : SquarefreeFactorAnalysis p box chart data
    gcdDegreePositive => EventLeaf factorAnalysis

/-- Complete finite nonzero-event family of all repeated-factor-safe
squarefree occurrences in one chart analysis. -/
def eventFamily
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    (factors : List (SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)) :
    List (EventEntry (p := p) (box := box) (form := form) (chart := chart)
      (data := data) (gcdDegreePositive := gcdDegreePositive)) :=
  factors.flatMap fun factorAnalysis =>
    (eventLeaves factorAnalysis).map fun leaf => ⟨factorAnalysis, leaf⟩

theorem mem_eventFamily
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factors : List (SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)}
    {factorAnalysis : SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive}
    (factorMember : factorAnalysis ∈ factors)
    (leaf : EventLeaf factorAnalysis) :
    (⟨factorAnalysis, leaf⟩ : EventEntry (p := p) (box := box)
      (form := form) (chart := chart) (data := data)
      (gcdDegreePositive := gcdDegreePositive)) ∈ eventFamily factors := by
  rw [eventFamily, QuotientFreeList.mem_flatMap]
  refine ⟨factorAnalysis, factorMember, ?_⟩
  rw [QuotientFreeList.mem_map]
  exact ⟨leaf, mem_eventLeaves leaf, rfl⟩

/-- Every displayed rational polynomial root on a non-pole part of an
executed chart is represented by an entry of that chart's complete computed
event family. -/
theorem LocatedSquarefreeCurveRoot.eventLeaf_mem_completeFamily
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      eventFamily
        (CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p box chart
          data gcdDegreePositive) :=
  mem_eventFamily
    (LocatedSquarefreeCurveRoot.factorAnalysis_mem located)
    (LocatedSquarefreeCurveRoot.eventLeaf located)

/-- Transfer pointwise event coverage through the completeness equality
carried by an executed `BoundedAnalysis.events` constructor. -/
theorem LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factors : List (SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive)}
    (factors_eq : factors =
      CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive)
    {parameter : Coordinate}
    (located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
      p box chart data gcdDegreePositive parameter) :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      eventFamily factors := by
  rw [factors_eq]
  exact LocatedSquarefreeCurveRoot.eventLeaf_mem_completeFamily located

/-- Executable location of a displayed polynomial root in the complete
finite nonzero-event family of one nonconstant chart analysis. -/
structure LocatedEvent
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive))
    (parameter : Coordinate) where
  located : CCL.CCLBoundaryCharts.LocatedSquarefreeCurveRoot
    p box chart data gcdDegreePositive parameter
  member :
    (⟨LocatedSquarefreeCurveRoot.factorAnalysis located,
        LocatedSquarefreeCurveRoot.eventLeaf located⟩ :
      EventEntry (p := p) (box := box) (form := form) (chart := chart)
        (data := data) (gcdDegreePositive := gcdDegreePositive)) ∈
      eventFamily factors

def locateEvent
    (p : GaussianPolynomial) (box : Box) {form : HermitianForm}
    (chart : BoundedChart form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SquarefreeFactorAnalysis p box chart data
      gcdDegreePositive))
    (factors_eq : factors =
      CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p box chart
        data gcdDegreePositive)
    (parameter : Coordinate)
    (parameterInside : chart.cell.interval.Contains parameter)
    (denominatorNonzero :
      chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (root : p.eval (chart.parameterization.curve.point parameter) = 0)
    (inside : box.Contains (chart.parameterization.curve.point parameter)) :
    LocatedEvent chart data gcdDegreePositive factors parameter := by
  let located := CCL.CCLBoundaryCharts.locateSquarefreeCurveRoot
    p box chart data gcdDegreePositive parameter parameterInside
      denominatorNonzero root inside
  exact
    { located := located
      member :=
        LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
          factors_eq located }

end CCL.PersistentCCLCurveEvents
