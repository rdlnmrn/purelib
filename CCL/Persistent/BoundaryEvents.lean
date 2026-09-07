import mathlib.Data.ConstructiveList
import CCL.Persistent.CurveEvents

/-!
# Complete finite event families for one CCL boundary

An unresolved Hermitian boundary can have two bounded rational charts.  The
owner calculation must therefore retain the nonzero events of every chart,
not merely the first nonconstant analysis.  This module flattens those
heterogeneous chart-local families into one finite boundary family.

The coverage theorem is pointwise and finite: any displayed rational
polynomial root on the unresolved boundary is located in one explicit member
of that computed family.  No root set or completed parameter is introduced.
-/

namespace CCL.PersistentCCLBoundaryEvents

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev SquarefreeFactorAnalysis :=
  CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary
abbrev EventEntry
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form}
    {data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree} :=
  CCL.PersistentCCLCurveEvents.EventEntry
    (p := p) (box := box) (form := form) (chart := chart)
      (data := data) (gcdDegreePositive := gcdDegreePositive)

/-- One chart-local event together with its exact provenance in the complete
analysis list of the dispatched boundary. -/
structure BoundaryEventEntry
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) where
  chart : BoundedChart atom.form
  data : CCL.CurveEvents.Nontrivial p
    chart.parameterization.curve
  gcdDegreePositive : 0 <
    (CCL.CurveClear.gcdPolynomial p
      chart.parameterization.curve).natDegree
  factors : List (SquarefreeFactorAnalysis p current chart data
    gcdDegreePositive)
  factors_eq : factors =
    CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p current chart
      data gcdDegreePositive
  analysisMember :
    (⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.events data
      gcdDegreePositive factors factors_eq⟩ :
      Sigma fun chart : BoundedChart atom.form =>
        CCL.CCLBoundaryCharts.BoundedAnalysis p current chart) ∈
      boundary.analyses
  event : EventEntry (p := p) (box := current) (form := atom.form)
    (chart := chart) (data := data)
      (gcdDegreePositive := gcdDegreePositive)
  eventMember : event ∈
    CCL.PersistentCCLCurveEvents.eventFamily factors

namespace BoundaryEventEntry

/-- Refine the nonzero Sturm event retained by one member of the complete
boundary family to an arbitrary requested rational parameter width. -/
def request
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate) :=
  entry.event.2.request epsilon

theorem request_width_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (entry.request epsilon).cell.interval.width ≤ epsilon :=
  entry.event.2.request_width_le epsilon positive

/-- Continue a boundary event from any already retained nonzero-count state.
This is used when a finite sample determines a second, data-dependent width. -/
def refineRequest
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary)
    (state : RFAP.SturmNonzeroEvent.State
      entry.event.1.factor.polynomial)
    (epsilon : Coordinate) :
    RFAP.SturmNonzeroEvent.State
      entry.event.1.factor.polynomial :=
  RFAP.SturmNonzeroEvent.request
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon

theorem refineRequest_refines
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary)
    (state : RFAP.SturmNonzeroEvent.State
      entry.event.1.factor.polynomial)
    (epsilon : Coordinate) :
    (entry.refineRequest state epsilon).cell.interval.Refines
      state.cell.interval :=
  RFAP.SturmNonzeroEvent.request_refines
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon

theorem refineRequest_width_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary)
    (state : RFAP.SturmNonzeroEvent.State
      entry.event.1.factor.polynomial)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (entry.refineRequest state epsilon).cell.interval.width ≤ epsilon :=
  RFAP.SturmNonzeroEvent.request_width_le
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon
      positive

/-- Pole-safe squared-chordal shrinking after continuing from an arbitrary
retained event state. -/
theorem chordalSq_refineRequest_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary)
    (state : RFAP.SturmNonzeroEvent.State
      entry.event.1.factor.polynomial)
    (stateRefinesChart : state.cell.interval.Refines
      entry.chart.cell.interval)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside :
      (entry.refineRequest state epsilon).cell.interval.Contains left)
    (rightInside :
      (entry.refineRequest state epsilon).cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (entry.chart.projective left) (entry.chart.projective right) ≤
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := entry.refineRequest state epsilon
  have requestedRefinesChart : requested.cell.interval.Refines
      entry.chart.cell.interval :=
    RFAP.SturmNonzeroEvent.intervalRefines_trans
      (entry.refineRequest_refines state epsilon) stateRefinesChart
  have leftChart : entry.chart.cell.interval.Contains left :=
    ⟨requestedRefinesChart.1.trans leftInside.1,
      leftInside.2.trans requestedRefinesChart.2⟩
  have rightChart : entry.chart.cell.interval.Contains right :=
    ⟨requestedRefinesChart.1.trans rightInside.1,
      rightInside.2.trans requestedRefinesChart.2⟩
  have parameterBound :=
    CCL.RationalCurveBounds.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : requested.cell.interval.width ^ 2 ≤ epsilon ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      requested.cell.interval.width_nonneg
      (entry.refineRequest_width_le state epsilon positive) 2
  exact (entry.chart.chordalSq_le_uniform leftChart rightChart).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      entry.chart.uniformChordalVariationCoefficient_nonneg)

/-- Pole-safe squared-chordal shrinking, lifted through the heterogeneous
complete-boundary event wrapper used by the dispatcher. -/
theorem chordalSq_request_le
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (epsilon : Coordinate)
    (positive : 0 < epsilon) {left right : Coordinate}
    (leftInside : (entry.request epsilon).cell.interval.Contains left)
    (rightInside : (entry.request epsilon).cell.interval.Contains right) :
    CCL.Chordal.chordalSq
        (entry.chart.projective left) (entry.chart.projective right) ≤
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 :=
  entry.event.2.chordalSq_request_le epsilon positive
    leftInside rightInside

/-- Coefficient-computable original-polynomial residual bound for portions of
this heterogeneous boundary event lying in a displayed affine box. -/
def affineResidualCoefficient
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (targetBox : Box) : Coordinate :=
  CCL.PersistentCCLCurveEvents.EventLeaf.affineEventResidualCoefficient
    (targetBox := targetBox) entry.event.1

theorem affineResidualCoefficient_nonneg
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (targetBox : Box) :
    0 ≤ entry.affineResidualCoefficient targetBox :=
  CCL.PersistentCCLCurveEvents.EventLeaf.affineEventResidualCoefficient_nonneg
    (targetBox := targetBox) entry.event.1

/-- Every affine meeting of a requested boundary event with `targetBox` has
the corresponding uniformly small original-polynomial residual. -/
theorem normSq_eval_point_request_le_of_inside
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : BoundaryEventEntry boundary) (targetBox : Box)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (parameter : Coordinate)
    (parameterInside :
      (entry.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.chart.parameterization.curve.point parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.chart.parameterization.curve.point parameter)) ≤
      entry.affineResidualCoefficient targetBox * epsilon ^ 2 := by
  simpa only [affineResidualCoefficient] using
    entry.event.2.normSq_eval_point_request_le_of_inside
      (targetBox := targetBox) epsilon positive parameter parameterInside
        denominatorNonzero pointInside

end BoundaryEventEntry

/-- Extract every nonzero event from one attached chart analysis. -/
def eventEntriesOfAnalysis
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (entry : Sigma fun chart : BoundedChart atom.form =>
      CCL.CCLBoundaryCharts.BoundedAnalysis p current chart)
    (member : entry ∈ boundary.analyses) :
    List (BoundaryEventEntry boundary) :=
  match entry with
  | ⟨_chart, .identicallyZero _realZero _imaginaryZero⟩ => []
  | ⟨_chart, .clear _certificate _residual⟩ => []
  | ⟨chart, .events data gcdDegreePositive factors factors_eq⟩ =>
      (CCL.PersistentCCLCurveEvents.eventFamily factors).attach.map
        fun attached =>
          { chart := chart
            data := data
            gcdDegreePositive := gcdDegreePositive
            factors := factors
            factors_eq := factors_eq
            analysisMember := member
            event := attached.1
            eventMember := attached.2 }

/-- Complete finite nonzero-event family of every bounded chart belonging to
one dispatched Hermitian boundary. -/
def boundaryEventFamily
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) : List (BoundaryEventEntry boundary) :=
  boundary.analyses.attach.flatMap fun attached =>
    eventEntriesOfAnalysis boundary attached.1 attached.2

theorem mem_eventEntriesOfAnalysis_events
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (chart : BoundedChart atom.form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SquarefreeFactorAnalysis p current chart data
      gcdDegreePositive))
    (factors_eq : factors =
      CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p current chart
        data gcdDegreePositive)
    (analysisMember :
      (⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.events data
        gcdDegreePositive factors factors_eq⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          CCL.CCLBoundaryCharts.BoundedAnalysis p current chart) ∈
        boundary.analyses)
    (event : EventEntry (p := p) (box := current) (form := atom.form)
      (chart := chart) (data := data)
        (gcdDegreePositive := gcdDegreePositive))
    (eventMember : event ∈
      CCL.PersistentCCLCurveEvents.eventFamily factors) :
    ({ chart := chart
       data := data
       gcdDegreePositive := gcdDegreePositive
       factors := factors
       factors_eq := factors_eq
       analysisMember := analysisMember
       event := event
       eventMember := eventMember } : BoundaryEventEntry boundary) ∈
      eventEntriesOfAnalysis boundary
        ⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.events data
          gcdDegreePositive factors factors_eq⟩ analysisMember := by
  rw [eventEntriesOfAnalysis, QuotientFreeList.mem_map]
  exact ⟨⟨event, eventMember⟩, QuotientFreeList.mem_attach _ _, rfl⟩

theorem mem_boundaryEventFamily_of_event
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (chart : BoundedChart atom.form)
    (data : CCL.CurveEvents.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (CCL.CurveClear.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (SquarefreeFactorAnalysis p current chart data
      gcdDegreePositive))
    (factors_eq : factors =
      CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p current chart
        data gcdDegreePositive)
    (analysisMember :
      (⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.events data
        gcdDegreePositive factors factors_eq⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          CCL.CCLBoundaryCharts.BoundedAnalysis p current chart) ∈
        boundary.analyses)
    (event : EventEntry (p := p) (box := current) (form := atom.form)
      (chart := chart) (data := data)
        (gcdDegreePositive := gcdDegreePositive))
    (eventMember : event ∈
      CCL.PersistentCCLCurveEvents.eventFamily factors) :
    ({ chart := chart
       data := data
       gcdDegreePositive := gcdDegreePositive
       factors := factors
       factors_eq := factors_eq
       analysisMember := analysisMember
       event := event
       eventMember := eventMember } : BoundaryEventEntry boundary) ∈
      boundaryEventFamily boundary := by
  rw [boundaryEventFamily, QuotientFreeList.mem_flatMap]
  refine ⟨⟨⟨chart,
    CCL.CCLBoundaryCharts.BoundedAnalysis.events data
      gcdDegreePositive factors factors_eq⟩, analysisMember⟩,
    QuotientFreeList.mem_attach _ _, ?_⟩
  exact mem_eventEntriesOfAnalysis_events boundary chart data
    gcdDegreePositive factors factors_eq analysisMember event eventMember

/-- A displayed rational polynomial root on a boundary, located in one
specific member of the complete finite boundary-event family. -/
structure LocatedBoundaryEvent
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian) where
  entry : BoundaryEventEntry boundary
  member : entry ∈ boundaryEventFamily boundary
  parameter : Coordinate
  parameterInside : entry.event.2.cell.interval.Contains parameter
  factorZero : entry.event.1.factor.polynomial.eval parameter = 0
  denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0
  point_eq : entry.chart.parameterization.curve.point parameter = value

namespace LocatedBoundaryEvent

/-- The chart point retained by a located boundary event is exactly the
homogeneous representative of its displayed affine value. -/
theorem projective_equivalent_affine
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {value : Gaussian} (located : LocatedBoundaryEvent boundary value) :
    (located.entry.chart.projective located.parameter).Equivalent
      (CCL.Proj.affine value) := by
  have equivalent :=
    CCL.RationalCurveBounds.projective_equivalent_affine
      located.entry.chart.parameterization.curve located.parameter
        located.denominatorNonzero
  simpa only [CCL.CCLBoundaryCharts.BoundedChart.projective,
    located.point_eq] using equivalent

/-- Any squared-chordal comparison can be transported without loss from the
located chart representation to the displayed affine boundary point. -/
theorem chordalSq_eq_affine
    {p : GaussianPolynomial} {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {value : Gaussian} (located : LocatedBoundaryEvent boundary value)
    (other : CCL.Chordal.Proj) :
    CCL.Chordal.chordalSq
        (located.entry.chart.projective located.parameter) other =
      CCL.Chordal.chordalSq (CCL.Proj.affine value) other := by
  exact CCL.Chordal.chordalSq_eq_of_equivalent_left
    (located.entry.chart.projective_valid located.parameter)
    (CCL.Chordal.Proj.affine_hasNonzeroCoordinate value)
    located.projective_equivalent_affine other

end LocatedBoundaryEvent

/-- Pointwise completeness of the finite boundary-event family. -/
def locateBoundaryRoot
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : Mat2} {current : Box}
    {denominatorMargin : Coordinate} {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Gaussian) (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.RawParser.denominator reference value)) :
    LocatedBoundaryEvent boundary value := by
  let covered := CCL.CCLBoundaryCharts.CurveSource.cover
    boundary.source current marginPositive value inside onBoundary
      denominatorLower
  rcases covered with
    ⟨chart, chartMember, parameter, parameterInside,
      curveDenominatorNonzero, pointEq⟩
  let analysis := CCL.CCLBoundaryCharts.analyzeChart p current chart
  let analysisEntry : Sigma fun chart : BoundedChart atom.form =>
      CCL.CCLBoundaryCharts.BoundedAnalysis p current chart :=
    ⟨chart, analysis⟩
  have analysisMember : analysisEntry ∈ boundary.analyses := by
    rw [boundary.analyses_eq]
    exact QuotientFreeList.mem_map.mpr ⟨chart, chartMember, rfl⟩
  dsimp only [analysisEntry, analysis] at analysisMember
  generalize analysisEq :
    CCL.CCLBoundaryCharts.analyzeChart p current chart = result
      at analysisMember
  cases result with
  | identicallyZero realZero imaginaryZero =>
      exact (CCL.PersistentCCLCurveClear.identicallyZero_absurd
        degreePositive boundary chart realZero imaginaryZero
          analysisMember).elim
  | clear certificate residual =>
      have lower := residual.lower parameter parameterInside
        curveDenominatorNonzero
      have curveRoot :
          p.eval (chart.parameterization.curve.point parameter) = 0 := by
        rw [pointEq]
        exact root
      rw [curveRoot, RFAP.ConstructiveGaussian.Gaussian.normSq_zero] at lower
      exact ((not_lt_of_ge lower) residual.positive).elim
  | events data gcdDegreePositive factors factors_eq =>
      have curveRoot :
          p.eval (chart.parameterization.curve.point parameter) = 0 := by
        rw [pointEq]
        exact root
      have curveInside :
          current.Contains (chart.parameterization.curve.point parameter) := by
        rw [pointEq]
        exact inside
      let located := CCL.CCLBoundaryCharts.locateSquarefreeCurveRoot
        p current chart data gcdDegreePositive parameter parameterInside
          curveDenominatorNonzero curveRoot curveInside
      let event : EventEntry (p := p) (box := current) (form := atom.form)
          (chart := chart) (data := data)
          (gcdDegreePositive := gcdDegreePositive) :=
        ⟨CCL.PersistentCCLCurveEvents.LocatedSquarefreeCurveRoot.factorAnalysis
            located,
          CCL.PersistentCCLCurveEvents.LocatedSquarefreeCurveRoot.eventLeaf
            located⟩
      have eventMember : event ∈
          CCL.PersistentCCLCurveEvents.eventFamily factors := by
        exact CCL.PersistentCCLCurveEvents.LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
          factors_eq located
      let entry : BoundaryEventEntry boundary :=
        { chart := chart
          data := data
          gcdDegreePositive := gcdDegreePositive
          factors := factors
          factors_eq := factors_eq
          analysisMember := analysisMember
          event := event
          eventMember := eventMember }
      exact
        { entry := entry
          member := mem_boundaryEventFamily_of_event boundary chart data
            gcdDegreePositive factors factors_eq analysisMember event eventMember
          parameter := parameter
          parameterInside := by
            exact located.location.contains
          factorZero := located.factorZero
          denominatorNonzero := curveDenominatorNonzero
          point_eq := pointEq }

end CCL.PersistentCCLBoundaryEvents
