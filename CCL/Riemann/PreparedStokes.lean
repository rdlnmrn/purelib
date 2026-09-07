import CCL.Riemann.PreparedCycleModels
import CCL.Riemann.FiniteBilinear
import CCL.Riemann.HyperellipticCells

/-!
# Prepared finite Stokes reduction

This module connects the prepared cycle geometry to the first bilinear
relation.  For a pair of standard differentials it materializes every local
zero-wedge chart on every displayed A- and B-cycle at one finite refinement.
A boundary-reduction certificate identifies the canonical primitive boundary
constructed in `FiniteBilinear` with that explicit finite wedge sum.  Since
each summand is already operationally zero, primitive closure and the Stokes
certificate are then derived.
-/

namespace CCL.Riemann.PreparedStokes

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev WedgeChart {genus : Nat} (curve : HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differential genus) :=
  CCL.Riemann.PreparedSubdivisionModels.WedgeChart curve leftDifferential
    rightDifferential

private theorem zeroInside :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

/-- One finite local wedge contribution, evaluated at a displayed rational
parameter of its actual prepared chart. -/
def chartContribution {genus : Nat} {curve : HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differential genus}
    (chart : WedgeChart curve leftDifferential rightDifferential) :
    CoherentNamed :=
  chart.coefficient 0 zeroInside

/-- Every prepared local wedge contribution is operationally zero. -/
def chartContribution_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differential genus}
    (chart : WedgeChart curve leftDifferential rightDifferential) :
    NamedEquivalent (chartContribution chart).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  chart.zero 0 zeroInside

/-- Recursive finite sum of all displayed local wedge contributions. -/
def wedgeSum {genus : Nat} {curve : HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differential genus} :
    List (WedgeChart curve leftDifferential rightDifferential) -> CoherentNamed
  | [] => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | chart :: remaining =>
      CCL.ProgressiveCoherence.CoherentNamed.add (chartContribution chart)
        (wedgeSum remaining)

/-- A finite list of prepared zero-wedge charts has zero total contribution. -/
def wedgeSum_zero {genus : Nat} {curve : HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differential genus} :
    (charts : List
      (WedgeChart curve leftDifferential rightDifferential)) ->
      NamedEquivalent (wedgeSum charts).name
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name
  | [] => CCL.OperationalEquivalence.NamedEquivalent.refl _
  | chart :: remaining => by
      let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
      have replaceBoth : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (chartContribution chart) (wedgeSum remaining)).name
          (CCL.ProgressiveCoherence.CoherentNamed.add zero zero).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          (chartContribution chart) zero (wedgeSum remaining) zero
          (chartContribution_zero chart) (wedgeSum_zero remaining)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceBoth
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)

/-- All prepared local wedge charts on the displayed A- and B-cycle families
at one finite refinement.  The list is entirely computed from the common
differential-independent geometry. -/
def surfaceCharts {genus : Nat} {curve : HyperellipticCurve genus}
    (geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) :
    List (WedgeChart curve (standardDifferential row)
      (standardDifferential column)) :=
  (List.ofFn fun cycle : Fin genus =>
    CCL.Riemann.PreparedCycleModels.PreparedCycleData.wedgeCharts
        (standardDifferential row) (standardDifferential column)
        ((geometry.aCycle cycle).data refinement) ++
      CCL.Riemann.PreparedCycleModels.PreparedCycleData.wedgeCharts
        (standardDifferential row) (standardDifferential column)
        ((geometry.bCycle cycle).data refinement)).flatten

/-- The explicit finite surface wedge sum at one prepared refinement. -/
def surfaceWedgeSum {genus : Nat} {curve : HyperellipticCurve genus}
    (geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) : CoherentNamed :=
  wedgeSum (surfaceCharts geometry row column refinement)

/-- Local holomorphicity makes every computed finite surface wedge sum zero. -/
def surfaceWedgeSum_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    (geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) :
    NamedEquivalent (surfaceWedgeSum geometry row column refinement).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  wedgeSum_zero (surfaceCharts geometry row column refinement)

/-! ## Edge pairs indexed by the actual hyperelliptic cell surface -/

/-- The operational boundary sum containing one reversed pair for both sheet
lifts of every base edge. -/
def cellularBoundarySum {baseCount : Nat}
    (pairs : Fin baseCount ->
      CCL.Riemann.HyperellipticCells.Sheet ->
        CCL.Riemann.FiniteBilinear.ProgramBoundaryPair) : CoherentNamed :=
  sumNamed fun base =>
    CCL.Riemann.FiniteBilinear.boundarySum fun sheet =>
      (pairs base sheet).toBoundaryPair

/-- Every actual lifted edge pair cancels, first across its two opposite face
occurrences and then across the finite base-edge family. -/
def cellularBoundarySum_zero {baseCount : Nat}
    (pairs : Fin baseCount ->
      CCL.Riemann.HyperellipticCells.Sheet ->
        CCL.Riemann.FiniteBilinear.ProgramBoundaryPair) :
    NamedEquivalent (cellularBoundarySum pairs).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.Riemann.FiniteBilinear.sumNamed_zero
    (fun base =>
      CCL.Riemann.FiniteBilinear.boundarySum fun sheet =>
        (pairs base sheet).toBoundaryPair)
    (fun base =>
      CCL.Riemann.FiniteBilinear.boundarySum_zero fun sheet =>
        (pairs base sheet).toBoundaryPair)

/-- Degree-shaped edge programs for the explicit four-face cell surface.
The indices are not arbitrary: `odd_pairedFaceOccurrences` and
`even_pairedFaceOccurrences` prove that each `(base,sheet)` selects the unique
upper/lower occurrences of the same lifted edge. -/
inductive CellularEdgePairs {genus : Nat}
    (curve : HyperellipticCurve genus) : Type 1
  | odd
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
      (pairs : Fin (CCL.Riemann.HyperellipticCells.oddBaseCount genus) ->
        CCL.Riemann.HyperellipticCells.Sheet ->
          CCL.Riemann.FiniteBilinear.ProgramBoundaryPair)
  | even
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
      (pairs : Fin (CCL.Riemann.HyperellipticCells.evenBaseCount genus) ->
        CCL.Riemann.HyperellipticCells.Sheet ->
          CCL.Riemann.FiniteBilinear.ProgramBoundaryPair)

namespace CellularEdgePairs

/-- The exact number of paired lifted edges in the selected concrete cell
model. -/
def pairCount {genus : Nat} {curve : HyperellipticCurve genus} :
    CellularEdgePairs curve -> Nat
  | .odd _ _ => CCL.Riemann.HyperellipticCells.oddBaseCount genus * 2
  | .even _ _ => CCL.Riemann.HyperellipticCells.evenBaseCount genus * 2

/-- The odd edge-pair bank has exactly the edge count of the constructed odd
cell complex. -/
theorem odd_pairCount {genus : Nat} {curve : HyperellipticCurve genus}
    (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
    (pairs : Fin (CCL.Riemann.HyperellipticCells.oddBaseCount genus) ->
      CCL.Riemann.HyperellipticCells.Sheet ->
        CCL.Riemann.FiniteBilinear.ProgramBoundaryPair) :
    (CellularEdgePairs.odd degree_eq pairs).pairCount =
      (CCL.Riemann.HyperellipticCells.oddCellComplex genus).edges.length := by
  rw [CCL.Riemann.HyperellipticCells.oddCellComplex_edgeCount]
  rfl

/-- The even edge-pair bank likewise includes the terminal infinity edge. -/
theorem even_pairCount {genus : Nat} {curve : HyperellipticCurve genus}
    (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
    (pairs : Fin (CCL.Riemann.HyperellipticCells.evenBaseCount genus) ->
      CCL.Riemann.HyperellipticCells.Sheet ->
        CCL.Riemann.FiniteBilinear.ProgramBoundaryPair) :
    (CellularEdgePairs.even degree_eq pairs).pairCount =
      (CCL.Riemann.HyperellipticCells.evenCellComplex genus).edges.length := by
  rw [CCL.Riemann.HyperellipticCells.evenCellComplex_edgeCount]
  rfl

/-- Sum the programs over precisely the lifted edges of the selected concrete
cell surface. -/
def boundarySum {genus : Nat} {curve : HyperellipticCurve genus} :
    CellularEdgePairs curve -> CoherentNamed
  | .odd _ pairs => cellularBoundarySum pairs
  | .even _ pairs => cellularBoundarySum pairs

/-- The explicit upper/lower occurrence pairing cancels the complete cellular
boundary operationally. -/
def boundarySum_zero {genus : Nat} {curve : HyperellipticCurve genus}
    (pairs : CellularEdgePairs curve) :
    NamedEquivalent pairs.boundarySum.name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  cases pairs with
  | odd degree_eq pairs => exact cellularBoundarySum_zero pairs
  | even degree_eq pairs => exact cellularBoundarySum_zero pairs

end CellularEdgePairs

/-- Finite cut-surface boundary reduction for prepared period schedules.
The supplied finite decomposition identifies the already canonical primitive
boundary endpoint with explicitly displayed reversed internal-edge pairs plus
the computed actual prepared local-wedge contributions.  Cancellation of
every edge pair, local wedge vanishing, and all primitive/path algebra are
derived. -/
structure BoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry) where
  refinement : Fin genus -> Fin genus -> Nat
  edgePairCount : Fin genus -> Fin genus -> Nat
  edgePairs : forall row column : Fin genus,
    Fin (edgePairCount row column) ->
      CCL.Riemann.FiniteBilinear.ProgramBoundaryPair
  boundary_eq_surface : forall row column : Fin genus,
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.Riemann.FiniteBilinear.boundarySum fun index =>
          (edgePairs row column index).toBoundaryPair)
        (surfaceWedgeSum geometry row column
          (refinement row column))).name

namespace BoundaryReduction

/-- The finite boundary reduction and automatic local wedge vanishing close
the canonical primitive path. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : BoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure
      schedules.toPeriodData where
  closed := by
    intro row column
    let paired := CCL.Riemann.FiniteBilinear.boundarySum fun index =>
      (reduction.edgePairs row column index).toBoundaryPair
    let wedges := surfaceWedgeSum geometry row column
      (reduction.refinement row column)
    let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
    have pairedZero : NamedEquivalent paired.name zero.name := by
      simpa only [paired, zero] using
        CCL.Riemann.FiniteBilinear.boundarySum_zero fun index =>
          (reduction.edgePairs row column index).toBoundaryPair
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column
          (reduction.refinement row column)
    have totalZero : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add paired wedges).name
        zero.name :=
      CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.TranscendentalCoherence.coherentAdd_respects
          paired zero wedges zero pairedZero wedgesZero)
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [paired, wedges] using
        reduction.boundary_eq_surface row column)
      totalZero

/-- Consequently the prepared cut-surface reduction constructs the ordinary
finite Stokes certificate used by the bilinear layer. -/
def toStokesCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : BoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.StokesCertificate schedules.toPeriodData :=
  reduction.toFiniteStokesClosure.toStokesCertificate

/-- For a genus-one prepared surface the finite boundary reduction is
automatic.  There is only one differential index, so the antisymmetric
primitive closes algebraically; the displayed local wedge charts still
record, and automatically prove, the zero surface contribution. -/
def genusOne {curve : HyperellipticCurve 1}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry) :
    BoundaryReduction schedules where
  refinement := fun _row _column => 0
  edgePairCount := fun _row _column => 0
  edgePairs := fun _row _column index => Fin.elim0 index
  boundary_eq_surface := by
    intro row column
    let wedges := surfaceWedgeSum geometry row column 0
    let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
    have finishZero : NamedEquivalent
        (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
          schedules.toPeriodData row column).name zero.name := by
      simpa only [zero] using
        (CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne
          schedules.toPeriodData).closed row column
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column 0
    have totalToWedges : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (CCL.Riemann.FiniteBilinear.boundarySum
            (fun index : Fin 0 =>
              (Fin.elim0 index :
                CCL.Riemann.FiniteBilinear.ProgramBoundaryPair).toBoundaryPair))
          wedges).name
        wedges.name := by
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (CCL.ProgressiveCoherence.CoherentNamed.exact 0) wedges).name
        wedges.name
      simpa only [CCL.ProgressiveCoherence.CoherentNamed.add,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        CCL.OperationalFieldLaws.coherentAdd_zero_left wedges
    have totalZero :=
      CCL.OperationalEquivalence.NamedEquivalent.trans totalToWedges wedgesZero
    exact CCL.OperationalEquivalence.NamedEquivalent.trans finishZero
      (CCL.OperationalEquivalence.NamedEquivalent.symm totalZero)

end BoundaryReduction

/-! ## Degree-shaped prepared surface reduction -/

/-- A cut-surface reduction whose reversed edge programs are indexed by the
actual degree-dependent hyperelliptic cell complex.  Unlike the low-level
`BoundaryReduction`, neither an arbitrary edge count nor an unrelated edge
family can enter this interface. -/
structure CellularBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry) where
  refinement : Fin genus -> Fin genus -> Nat
  edgePairs : forall _row _column : Fin genus, CellularEdgePairs curve
  boundary_eq_surface : forall row column : Fin genus,
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (edgePairs row column).boundarySum
        (surfaceWedgeSum geometry row column
          (refinement row column))).name

namespace CellularBoundaryReduction

/-- Actual cell-edge pairing and local wedge vanishing derive the canonical
finite Stokes closure. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularBoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure
      schedules.toPeriodData where
  closed := by
    intro row column
    let paired := (reduction.edgePairs row column).boundarySum
    let wedges := surfaceWedgeSum geometry row column
      (reduction.refinement row column)
    let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
    have pairedZero : NamedEquivalent paired.name zero.name := by
      simpa only [paired, zero] using
        (reduction.edgePairs row column).boundarySum_zero
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column
          (reduction.refinement row column)
    have totalZero : NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add paired wedges).name
        zero.name :=
      CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.TranscendentalCoherence.coherentAdd_respects
          paired zero wedges zero pairedZero wedgesZero)
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (by simpa only [paired, wedges] using
        reduction.boundary_eq_surface row column)
      totalZero

/-- The stronger degree-shaped reduction also supplies the ordinary finite
Stokes certificate used below the prepared layer. -/
def toStokesCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularBoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.StokesCertificate schedules.toPeriodData :=
  reduction.toFiniteStokesClosure.toStokesCertificate

end CellularBoundaryReduction

/-! ## Local two-dimensional triangulated Stokes input -/

/-- Two synchronized primitive-value streams attached to one vertex of a
finite surface triangulation. -/
structure PrimitiveStream where
  left : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation
  right : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation

namespace PrimitiveStream

/-- The exact pair of rational primitive values displayed at one finite
refinement index. -/
def sample (stream : PrimitiveStream) (index : Nat) :
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint :=
  ⟨stream.left.sample index, stream.right.sample index⟩

@[simp] theorem sample_left (stream : PrimitiveStream) (index : Nat) :
    (stream.sample index).left = stream.left.sample index := rfl

@[simp] theorem sample_right (stream : PrimitiveStream) (index : Nat) :
    (stream.sample index).right = stream.right.sample index := rfl

end PrimitiveStream

/-- Exact Gaussian rational one half.  It is applied only after the
division-free edge cancellation theorem has been established. -/
def gaussianHalf : RFAP.ConstructiveGaussian.Gaussian :=
  RFAP.ConstructiveGaussian.Gaussian.inv 2

/-- Standard integral of `dF ∧ dG` on one oriented affine triangle.  The
polygon module keeps doubled areas internally; this final multiplication by
one half restores the ordinary triangle normalization. -/
def triangleIntegral {vertexCount : Nat}
    (points : Fin vertexCount ->
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint)
    (triangle :
      CCL.Riemann.FinitePolygonStokes.OrientedTriangle vertexCount) :
    RFAP.ConstructiveGaussian.Gaussian :=
  gaussianHalf *
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      (points triangle.first) (points triangle.second) (points triangle.third)

/-- One half cancels the division-free factor two exactly. -/
theorem gaussianHalf_mul_two
    (value : RFAP.ConstructiveGaussian.Gaussian) :
    gaussianHalf * (2 * value) = value := by
  unfold gaussianHalf
  rw [← RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
  rw [RFAP.ConstructiveGaussian.Gaussian.inv_mul 2 (by decide)]
  exact RFAP.ConstructiveGaussian.Gaussian.one_mul value

/-- Genuine finite two-dimensional Stokes input for one pair of
differentials.  The triangulation exposes every face and internal edge.  Its
outer boundary is checked exactly against the synchronized symplectic cut
polygon at every rational sample, while the analytic input is split into one
shrinking estimate per local triangle. -/
structure LocalFaceCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  faceLabel : Fin faceCount -> CCL.Riemann.HyperellipticCells.Face
  primitive : Fin vertexCount -> PrimitiveStream
  boundary_matches : forall index : Nat,
    CCL.Riemann.FinitePolygonStokes.edgeListArea
        (fun vertex => (primitive vertex).sample index)
        triangulation.boundary =
      CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column
  faceScale : Fin faceCount -> Coordinate
  faceScale_nonnegative : forall face, 0 <= faceScale face
  face_close : forall face : Fin faceCount, forall index : Nat,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (triangleIntegral
          (fun vertex => (primitive vertex).sample index)
          (triangulation.faces face)) <=
      CCL.FiniteGeometric.quarterRadius (faceScale face) index

namespace LocalFaceCertificate

/-- At every refinement the sum of ordinary local triangle integrals is
exactly the synchronized first-bilinear residual.  Internal-edge cancellation
and the factor-two normalization are both derived. -/
theorem triangleIntegralSum_eq_residualSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) (index : Nat) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleIntegral
          (fun vertex => (certificate.primitive vertex).sample index)
          (certificate.triangulation.faces face)) =
      (CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
        data row column).sample index := by
  let points := fun vertex => (certificate.primitive vertex).sample index
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleIntegral points (certificate.triangulation.faces face)) =
        gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.triangleWedgeSum points
            certificate.triangulation.faces := by
      unfold triangleIntegral
      exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_left gaussianHalf _
    _ = gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.edgeListArea points
            certificate.triangulation.boundary := by
      rw [certificate.triangulation.wedgeSum_eq_boundaryArea points]
    _ = gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column := by
      rw [certificate.boundary_matches index]
    _ = gaussianHalf *
          (2 * CCL.Riemann.FinitePolygonStokes.symplecticPairing
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column) := by
      rw [CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea_eq_two_mul_pairing]
    _ = CCL.Riemann.FinitePolygonStokes.symplecticPairing
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) row column :=
      gaussianHalf_mul_two _
    _ = (CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index := by
      rw [CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual_sample]

/-- Per-face shrinking bounds combine constructively into a shrinking bound
for the synchronized period-pairing residual. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.PeriodMatrix.sumBound certificate.faceScale) index := by
  rw [← certificate.triangleIntegralSum_eq_residualSample index]
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteMatrix.sumFin fun face =>
          triangleIntegral
            (fun vertex => (certificate.primitive vertex).sample index)
            (certificate.triangulation.faces face)) <=
        CCL.Riemann.PeriodMatrix.sumBound (fun face =>
          CCL.FiniteGeometric.quarterRadius
            (certificate.faceScale face) index) :=
      CCL.Riemann.PeriodMatrix.normSq_sumFin_le_sumBound _ _
        (fun face => certificate.face_close face index)
    _ = CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.sumBound certificate.faceScale) index :=
      CCL.Riemann.PeriodMatrix.sumBound_quarterRadius
        certificate.faceScale index

/-- Local face estimates close the actual stateful first-bilinear residual.
No comparison against the already assembled global residual is requested from
the caller. -/
def residual_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingResidual
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let source :=
    CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      (0 : RFAP.ConstructiveGaussian.Gaussian)
  let sourceProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram source
  let zeroProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram zeroSource
  have scaleNonnegative :
      0 <= CCL.Riemann.PeriodMatrix.sumBound certificate.faceScale :=
    CCL.Riemann.PeriodMatrix.sumBound_nonneg certificate.faceScale
      certificate.faceScale_nonnegative
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply CCL.Riemann.FiniteBilinear.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram
      (CCL.Riemann.PeriodMatrix.sumBound certificate.faceScale)
      scaleNonnegative
    intro index
    rw [CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample,
      CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        (source.sample index - 0) <= _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingResidual_equivalent_synchronized
      data row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (CCL.OperationalEquivalence.NamedEquivalent.trans programsEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by simpa only [zeroSource] using
            CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact))))

/-- The canonical accumulated primitive closes as a consequence of the local
two-dimensional triangulation certificate. -/
def closePrimitive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end LocalFaceCertificate

/-! ## Refining two-dimensional cut-surface meshes -/

/-- One completely finite triangulated cut-surface sample.  Vertex and face
counts belong to the sample, so later refinements may genuinely subdivide the
surface rather than forcing a fixed bank of triangles to collapse.  Every
local wedge error has its own rational budget. -/
structure RefiningFaceSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) where
  vertexCount : Nat
  faceCount : Nat
  triangulation :
    CCL.Riemann.FinitePolygonStokes.Triangulation vertexCount faceCount
  faceLabel : Fin faceCount -> CCL.Riemann.HyperellipticCells.Face
  primitive : Fin vertexCount ->
    CCL.Riemann.FinitePolygonStokes.PrimitivePoint
  boundary_matches :
    CCL.Riemann.FinitePolygonStokes.edgeListArea primitive
        triangulation.boundary =
      CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column
  faceBudget : Fin faceCount -> Coordinate
  faceBudget_nonnegative : forall face, 0 <= faceBudget face
  face_close : forall face : Fin faceCount,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (triangleIntegral primitive (triangulation.faces face)) <=
      faceBudget face

namespace RefiningFaceSample

/-- Exact incidence cancellation identifies the sum of one refining mesh's
local triangle integrals with the synchronized period residual. -/
theorem triangleIntegralSum_eq_residualSample {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus} {index : Nat}
    (sample : RefiningFaceSample data row column index) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleIntegral sample.primitive
          (sample.triangulation.faces face)) =
      (CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
        data row column).sample index := by
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face =>
        triangleIntegral sample.primitive
          (sample.triangulation.faces face)) =
        gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.triangleWedgeSum sample.primitive
            sample.triangulation.faces := by
      unfold triangleIntegral
      exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_left gaussianHalf _
    _ = gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.edgeListArea sample.primitive
            sample.triangulation.boundary := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = gaussianHalf *
          CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column := by
      rw [sample.boundary_matches]
    _ = gaussianHalf *
          (2 * CCL.Riemann.FinitePolygonStokes.symplecticPairing
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column) := by
      rw [CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea_eq_two_mul_pairing]
    _ = CCL.Riemann.FinitePolygonStokes.symplecticPairing
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) row column :=
      gaussianHalf_mul_two _
    _ = (CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index := by
      rw [CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual_sample]

/-- The displayed local budgets bound the complete wedge integral at this
finite refinement. -/
theorem residualSample_le_sumBudget {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus} {index : Nat}
    (sample : RefiningFaceSample data row column index) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      CCL.Riemann.PeriodMatrix.sumBound sample.faceBudget := by
  rw [<- sample.triangleIntegralSum_eq_residualSample]
  exact CCL.Riemann.PeriodMatrix.normSq_sumFin_le_sumBound _ _
    sample.face_close

end RefiningFaceSample

/-- A genuine refining cut-surface Stokes certificate.  Each index displays a
new finite triangulation, so its number of local faces may grow.  The only
global estimate is the mechanically summed bank of per-face rational budgets;
no bound on the already assembled period residual is assumed. -/
structure RefiningLocalFaceCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  sample : forall index : Nat, RefiningFaceSample data row column index
  scale : Coordinate
  scale_nonnegative : 0 <= scale
  summedBudget_close : forall index : Nat,
    CCL.Riemann.PeriodMatrix.sumBound (sample index).faceBudget <=
      CCL.FiniteGeometric.quarterRadius scale index

namespace RefiningLocalFaceCertificate

/-- Local triangle estimates and exact incidence yield geometric convergence
of the synchronized first-bilinear residual to zero. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column)
    (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      CCL.FiniteGeometric.quarterRadius certificate.scale index :=
  (certificate.sample index).residualSample_le_sumBudget.trans
    (certificate.summedBudget_close index)

/-- The stateful first-bilinear residual is operationally zero because every
finite comparison is discharged by a later refining cut-surface mesh. -/
def residual_zero {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingResidual
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let source :=
    CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      (0 : RFAP.ConstructiveGaussian.Gaussian)
  let sourceProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram source
  let zeroProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram zeroSource
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply CCL.Riemann.FiniteBilinear.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram certificate.scale certificate.scale_nonnegative
    intro index
    rw [CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample,
      CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        (source.sample index - 0) <= _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingResidual_equivalent_synchronized
      data row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (CCL.OperationalEquivalence.NamedEquivalent.trans programsEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by simpa only [zeroSource] using
            CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact))))

/-- Refining local Stokes closes the accumulated primitive. -/
def closePrimitive {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end RefiningLocalFaceCertificate

/-- Only the independent strict-upper entries require refining surface
meshes; diagonal closure and the lower triangle remain algebraic. -/
structure UpperRefiningLocalFaceReduction {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  certificate : forall row column : Fin genus,
    row.val < column.val -> RefiningLocalFaceCertificate data row column

namespace UpperRefiningLocalFaceReduction

def toUpperTriangularStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperRefiningLocalFaceReduction data) :
    CCL.Riemann.FiniteBilinear.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperRefiningLocalFaceReduction data) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toFiniteStokesClosure

/-- A genus-two proof has exactly one independent refining surface mesh. -/
def genusTwo {curve : HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : RefiningLocalFaceCertificate data 0 1) :
    UpperRefiningLocalFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      omega0
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      omega0
    subst row
    subst column
    exact certificate

end UpperRefiningLocalFaceReduction

/-! ## Canonical handlewise decomposition

The arbitrary triangulation interface above is the geometric interface used
for an actual refining cut-surface mesh.  Separately, the standard
symplectic boundary has a useful exact algebraic decomposition: each handle
commutator `0, a, a+b, b` splits along the diagonal `0 -- (a+b)`.  Its two
triangle values need not tend to zero individually; in general they do not.
The certificate below therefore asks only for a shrinking bound on the sum
over the complete finite handle bank.  It exposes the exact terms whose
cancellation is being certified without falsely presenting a fixed handle
polygon as a refining local surface mesh. -/

/-- First triangle in the canonical subdivision of one handle commutator. -/
def firstHandleTriangleIntegral
    (a b : CCL.Riemann.FinitePolygonStokes.PrimitivePoint) :
    RFAP.ConstructiveGaussian.Gaussian :=
  gaussianHalf *
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero a (a.add b)

/-- Second triangle in the canonical subdivision of one handle commutator. -/
def secondHandleTriangleIntegral
    (a b : CCL.Riemann.FinitePolygonStokes.PrimitivePoint) :
    RFAP.ConstructiveGaussian.Gaussian :=
  gaussianHalf *
    CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero (a.add b) b

/-- The two canonical triangles give exactly the ordinary determinant of the
two primitive increments. -/
theorem handleTriangleIntegral_add
    (a b : CCL.Riemann.FinitePolygonStokes.PrimitivePoint) :
    firstHandleTriangleIntegral a b + secondHandleTriangleIntegral a b =
      a.left * b.right - b.left * a.right := by
  have firstWedge :
      CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
          CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero a (a.add b) =
        a.left * b.right - b.left * a.right := by
    unfold CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
    ring1
  have secondWedge :
      CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
          CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero (a.add b) b =
        a.left * b.right - b.left * a.right := by
    unfold CCL.Riemann.FinitePolygonStokes.triangleWedgeArea
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.zero
      CCL.Riemann.FinitePolygonStokes.PrimitivePoint.add
    ring1
  rw [firstHandleTriangleIntegral, secondHandleTriangleIntegral,
    firstWedge, secondWedge]
  calc
    gaussianHalf * (a.left * b.right - b.left * a.right) +
          gaussianHalf * (a.left * b.right - b.left * a.right) =
        gaussianHalf *
          (2 * (a.left * b.right - b.left * a.right)) := by ring1
    _ = a.left * b.right - b.left * a.right :=
      gaussianHalf_mul_two _

/-- One of the two displayed canonical triangles for a synchronized handle
sample. -/
def handleTriangleIntegral {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (row column cycle : Fin genus) (face : Fin 2) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian :=
  let a := CCL.Riemann.FinitePolygonStokes.aIncrement
    (sampledMatrix data.aMatrix index) row column cycle
  let b := CCL.Riemann.FinitePolygonStokes.bIncrement
    (sampledMatrix data.bMatrix index) row column cycle
  if face = 0 then firstHandleTriangleIntegral a b
  else secondHandleTriangleIntegral a b

/-- Summing the two triangles of one handle gives its exact synchronized
symplectic-pairing summand. -/
theorem handleTriangleSum_eq_pairingTerm {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (row column cycle : Fin genus) (index : Nat) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun face : Fin 2 =>
        handleTriangleIntegral data row column cycle face index) =
      sampledMatrix data.aMatrix index row cycle *
          sampledMatrix data.bMatrix index column cycle -
        sampledMatrix data.bMatrix index row cycle *
          sampledMatrix data.aMatrix index column cycle := by
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change handleTriangleIntegral data row column cycle 0 index +
      RFAP.ConstructiveFiniteMatrix.sumFin (fun face : Fin 1 =>
        handleTriangleIntegral data row column cycle face.succ index) = _
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change handleTriangleIntegral data row column cycle 0 index +
      (handleTriangleIntegral data row column cycle 1 index + 0) = _
  rw [RFAP.ConstructiveGaussian.Gaussian.add_zero]
  unfold handleTriangleIntegral
  simp only [ite_true, OfNat.ofNat]
  exact handleTriangleIntegral_add _ _

/-- The complete bank of canonical handle triangles sums exactly to the
synchronized first-bilinear residual. -/
theorem handleTriangleSum_eq_residualSample {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve)
    (row column : Fin genus) (index : Nat) :
    RFAP.ConstructiveFiniteMatrix.sumFin (fun cycle =>
        RFAP.ConstructiveFiniteMatrix.sumFin (fun face : Fin 2 =>
          handleTriangleIntegral data row column cycle face index)) =
      (CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
        data row column).sample index := by
  rw [CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual_sample]
  unfold CCL.Riemann.FinitePolygonStokes.symplecticPairing
  exact RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (fun cycle => handleTriangleSum_eq_pairingTerm
      data row column cycle index)

/-- Canonical handlewise Stokes input.  All exact boundary terms are fixed by
the symplectic period matrices.  The remaining datum is one shrinking bound
on their complete sum; no individual fixed handle triangle is asserted to
shrink. -/
structure HandleFaceCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  scale : Coordinate
  scale_nonnegative : 0 <= scale
  total_close : forall index : Nat,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
          RFAP.ConstructiveFiniteMatrix.sumFin fun face : Fin 2 =>
            handleTriangleIntegral data row column cycle face index) <=
      CCL.FiniteGeometric.quarterRadius scale index

namespace HandleFaceCertificate

/-- The exact handle decomposition transports its displayed shrinking bound
to the synchronized residual. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) (index : Nat) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      CCL.FiniteGeometric.quarterRadius certificate.scale index := by
  rw [<- handleTriangleSum_eq_residualSample data row column index]
  exact certificate.total_close index

/-- Canonical handlewise estimates close the stateful residual. -/
def residual_zero {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingResidual
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let source :=
    CCL.Riemann.FiniteBilinear.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      (0 : RFAP.ConstructiveGaussian.Gaussian)
  let sourceProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram source
  let zeroProgram :=
    CCL.Riemann.FiniteBilinear.geometricRefinementProgram zeroSource
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply CCL.Riemann.FiniteBilinear.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram certificate.scale
        certificate.scale_nonnegative
    intro index
    rw [CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample,
      CCL.Riemann.FiniteBilinear.geometricRefinementProgram_integralSample]
    change RFAP.ConstructiveGaussian.Gaussian.normSq
        (source.sample index - 0) <= _
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingResidual_equivalent_synchronized
      data row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (CCL.OperationalEquivalence.NamedEquivalent.trans programsEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.Riemann.FiniteBilinear.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by simpa only [zeroSource] using
            CCL.Riemann.FiniteBilinear.geometricZero_equivalent_exact))))

/-- The canonical accumulated primitive closes from the complete handle-bank
cancellation modulus. -/
def closePrimitive {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end HandleFaceCertificate

/-- Only strict-upper differential pairs need a canonical handle-bank
cancellation modulus. -/
structure UpperHandleFaceReduction {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  certificate : forall row column : Fin genus,
    row.val < column.val -> HandleFaceCertificate data row column

namespace UpperHandleFaceReduction

def toUpperTriangularStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperHandleFaceReduction data) :
    CCL.Riemann.FiniteBilinear.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperHandleFaceReduction data) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toFiniteStokesClosure

/-- In genus two, one cancellation modulus over the four exact handle
triangle terms is the complete independent first-relation input. -/
def genusTwo {curve : HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : HandleFaceCertificate data 0 1) :
    UpperHandleFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      omega0
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      omega0
    subst row
    subst column
    exact certificate

end UpperHandleFaceReduction

/-- Only independent strict-upper entries require local triangulated surface
data; skew symmetry and diagonal cancellation remain automatic. -/
structure UpperLocalFaceReduction {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  certificate : forall row column : Fin genus,
    row.val < column.val -> LocalFaceCertificate data row column

namespace UpperLocalFaceReduction

/-- Independent local face certificates construct the generic upper-triangle
Stokes closure. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperLocalFaceReduction data) :
    CCL.Riemann.FiniteBilinear.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

/-- Expand the local face proofs to the complete genus-generic finite Stokes
closure. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperLocalFaceReduction data) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toFiniteStokesClosure

/-- In genus two, the single `(0,1)` triangulated surface certificate is the
entire independent Stokes input. -/
def genusTwo {curve : HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : LocalFaceCertificate data 0 1) :
    UpperLocalFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      omega0
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      omega0
    subst row
    subst column
    exact certificate

end UpperLocalFaceReduction

/-! ## Exact finite-program surface comparison -/

/-- Repackage one displayed cellular boundary plus its local wedge sum as a
finite Gaussian refinement program. -/
def cellularBoundaryProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve)
    (pairs : CellularEdgePairs curve) (row column : Fin genus)
    (refinement : Nat) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed
    (CCL.ProgressiveCoherence.CoherentNamed.add pairs.boundarySum
      (surfaceWedgeSum geometry row column refinement))

/-- One shrinking finite comparison with the actual cellular boundary closes
the corresponding canonical Stokes primitive.  Edge cancellation and local
wedge vanishing are consequences of the degree-shaped surface data. -/
def closePrimitive_of_cellularProgramComparison {genus : Nat}
    {curve : HyperellipticCurve genus}
    (geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve)
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry)
    (row column : Fin genus) (refinement : Nat)
    (pairs : CellularEdgePairs curve) (bridgeScale : Coordinate)
    (bridgeScale_nonnegative : 0 <= bridgeScale)
    (sample_close : forall index : Nat,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (((CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
            schedules.toPeriodData row column).model index).integralSample -
          ((cellularBoundaryProgram geometry pairs row column refinement).model
            index).integralSample) <=
        CCL.FiniteGeometric.quarterRadius bridgeScale index) :
    NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let paired := pairs.boundarySum
  let wedges := surfaceWedgeSum geometry row column refinement
  let total := CCL.ProgressiveCoherence.CoherentNamed.add paired wedges
  let boundaryProgram := cellularBoundaryProgram geometry pairs row column
    refinement
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have programsEquivalent : NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
        schedules.toPeriodData row column).output.name
      boundaryProgram.output.name := by
    apply CCL.Riemann.FiniteBilinear.refinementProgram_output_equivalent_of_samples_close
      _ _ bridgeScale bridgeScale_nonnegative
    intro index
    simpa only [boundaryProgram] using sample_close index
  have boundaryProgramEquivalent : NamedEquivalent total.name
      boundaryProgram.output.name := by
    simpa only [total, boundaryProgram, cellularBoundaryProgram, paired,
      wedges] using
      CCL.Riemann.FiniteBilinear.ofCoherentNamed_output_equivalent total
  have pairedZero : NamedEquivalent paired.name zero.name := by
    simpa only [paired, zero] using pairs.boundarySum_zero
  have wedgesZero : NamedEquivalent wedges.name zero.name := by
    simpa only [wedges, zero] using
      surfaceWedgeSum_zero geometry row column refinement
  have totalZero : NamedEquivalent total.name zero.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentAdd_respects
        paired zero wedges zero pairedZero wedgesZero)
      (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish_equivalent_program
      schedules.toPeriodData row column)
    (CCL.OperationalEquivalence.NamedEquivalent.trans programsEquivalent
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          boundaryProgramEquivalent)
        totalZero))

/-- Strong prepared Stokes input stated as a geometrically shrinking rational
distance between the period-pairing program and the finite cellular boundary.
Literal quadrature-centre equality is not required.  The operational boundary
equivalence is derived from this executable modulus. -/
structure CellularProgramBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry) where
  refinement : Fin genus -> Fin genus -> Nat
  edgePairs : forall _row _column : Fin genus, CellularEdgePairs curve
  bridgeScale : Fin genus -> Fin genus -> Coordinate
  bridgeScale_nonnegative : forall row column,
    0 <= bridgeScale row column
  sample_close : forall row column : Fin genus, forall index : Nat,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
          schedules.toPeriodData row column).model index).integralSample -
        ((cellularBoundaryProgram geometry (edgePairs row column) row column
          (refinement row column)).model index).integralSample) <=
      CCL.FiniteGeometric.quarterRadius (bridgeScale row column) index

namespace CellularProgramBoundaryReduction

/-- Exact samplewise equality is a special case of the shrinking comparison,
with zero bridge scale. -/
def ofSamplesEq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (refinement : Fin genus -> Fin genus -> Nat)
    (edgePairs : forall _row _column : Fin genus, CellularEdgePairs curve)
    (sample_eq : forall row column : Fin genus, forall index : Nat,
      ((CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
        schedules.toPeriodData row column).model index).integralSample =
      ((cellularBoundaryProgram geometry (edgePairs row column) row column
        (refinement row column)).model index).integralSample) :
    CellularProgramBoundaryReduction schedules where
  refinement := refinement
  edgePairs := edgePairs
  bridgeScale := fun _ _ => 0
  bridgeScale_nonnegative := fun _ _ => by decide
  sample_close := by
    intro row column index
    rw [sample_eq row column index,
      RFAP.ConstructiveGaussian.Gaussian.sub_self,
      RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
    exact CCL.FiniteGeometric.quarterRadius_nonneg (by decide) index

/-- The shrinking finite comparison constructs the degree-shaped operational
surface reduction. -/
def toCellularBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularProgramBoundaryReduction schedules) :
    CellularBoundaryReduction schedules where
  refinement := reduction.refinement
  edgePairs := reduction.edgePairs
  boundary_eq_surface := by
    intro row column
    let total := CCL.ProgressiveCoherence.CoherentNamed.add
      (reduction.edgePairs row column).boundarySum
      (surfaceWedgeSum geometry row column
        (reduction.refinement row column))
    let boundaryProgram := cellularBoundaryProgram geometry
      (reduction.edgePairs row column) row column
        (reduction.refinement row column)
    have programsEquivalent : NamedEquivalent
        (CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
          schedules.toPeriodData row column).output.name
        boundaryProgram.output.name := by
      apply CCL.Riemann.FiniteBilinear.refinementProgram_output_equivalent_of_samples_close
        _ _ (reduction.bridgeScale row column)
          (reduction.bridgeScale_nonnegative row column)
      intro index
      simpa only [boundaryProgram] using reduction.sample_close row column index
    have boundaryProgramEquivalent : NamedEquivalent total.name
        boundaryProgram.output.name := by
      simpa only [total, boundaryProgram, cellularBoundaryProgram] using
        CCL.Riemann.FiniteBilinear.ofCoherentNamed_output_equivalent total
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish_equivalent_program
        schedules.toPeriodData row column)
      (CCL.OperationalEquivalence.NamedEquivalent.trans programsEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          boundaryProgramEquivalent))

/-- Consequently the complete Stokes closure follows from request-indexed
rational program comparisons and the automatic cell-edge cancellation. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularProgramBoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure
      schedules.toPeriodData :=
  reduction.toCellularBoundaryReduction.toFiniteStokesClosure

end CellularProgramBoundaryReduction

/-! ## Independent upper-triangular surface comparisons -/

/-- Prepared finite Stokes data with no redundant diagonal or lower-triangle
fields.  Only strict upper-triangular differential pairs carry a surface
program comparison; the generic skew-symmetry theorem reconstructs all other
entries. -/
structure UpperCellularProgramBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry) where
  refinement : forall row column : Fin genus, row.val < column.val -> Nat
  edgePairs : forall row column : Fin genus,
    (less : row.val < column.val) -> CellularEdgePairs curve
  bridgeScale : forall row column : Fin genus,
    row.val < column.val -> Coordinate
  bridgeScale_nonnegative : forall row column : Fin genus,
    (less : row.val < column.val) -> 0 <= bridgeScale row column less
  sample_close : forall row column : Fin genus,
    (less : row.val < column.val) -> forall index : Nat,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
          schedules.toPeriodData row column).model index).integralSample -
        ((cellularBoundaryProgram geometry (edgePairs row column less)
          row column (refinement row column less)).model index).integralSample) <=
      CCL.FiniteGeometric.quarterRadius
        (bridgeScale row column less) index

namespace UpperCellularProgramBoundaryReduction

/-- Close precisely the independent upper-triangular primitive entries. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : UpperCellularProgramBoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.UpperTriangularStokesClosure
      schedules.toPeriodData where
  closed_of_lt := by
    intro row column less
    exact closePrimitive_of_cellularProgramComparison geometry schedules
      row column (reduction.refinement row column less)
      (reduction.edgePairs row column less)
      (reduction.bridgeScale row column less)
      (reduction.bridgeScale_nonnegative row column less)
      (reduction.sample_close row column less)

/-- Skew-symmetry and automatic diagonal cancellation expand the independent
prepared comparisons to the complete finite Stokes closure. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : UpperCellularProgramBoundaryReduction schedules) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure schedules.toPeriodData :=
  reduction.toUpperTriangularStokesClosure.toFiniteStokesClosure

/-- Package the unique genus-two off-diagonal surface comparison as the
complete independent prepared Stokes input. -/
def genusTwo {curve : HyperellipticCurve 2}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.PeriodSchedules curve geometry)
    (refinement : Nat) (pairs : CellularEdgePairs curve)
    (bridgeScale : Coordinate) (bridgeScale_nonnegative : 0 <= bridgeScale)
    (sample_close : forall index : Nat,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (((CCL.Riemann.FiniteBilinear.periodPairingCycleSumProgram
            schedules.toPeriodData 0 1).model index).integralSample -
          ((cellularBoundaryProgram geometry pairs 0 1 refinement).model
            index).integralSample) <=
        CCL.FiniteGeometric.quarterRadius bridgeScale index) :
    UpperCellularProgramBoundaryReduction schedules where
  refinement := by
    intro row column less
    exact refinement
  edgePairs := by
    intro row column less
    exact pairs
  bridgeScale := by
    intro row column less
    exact bridgeScale
  bridgeScale_nonnegative := by
    intro row column less
    exact bridgeScale_nonnegative
  sample_close := by
    intro row column less index
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      omega0
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      omega0
    subst row
    subst column
    exact sample_close index

end UpperCellularProgramBoundaryReduction

/-- Compatible prepared schedules use the same finite Stokes reduction after
their ordinary period schedules have been derived. -/
abbrev CompatibleBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  BoundaryReduction schedules.toPeriodSchedules

/-- Compatible prepared schedules with edge programs indexed by the actual
degree-dependent hyperelliptic cell model. -/
abbrev CompatibleCellularBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  CellularBoundaryReduction schedules.toPeriodSchedules

/-- Compatible schedules with the stronger geometrically controlled
finite-program Stokes comparison. -/
abbrev CompatibleCellularProgramBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  CellularProgramBoundaryReduction schedules.toPeriodSchedules

/-- Compatible schedules with only the independent upper-triangular prepared
surface comparisons. -/
abbrev CompatibleUpperCellularProgramBoundaryReduction {genus : Nat}
    {curve : HyperellipticCurve genus}
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  UpperCellularProgramBoundaryReduction schedules.toPeriodSchedules

end CCL.Riemann.PreparedStokes
