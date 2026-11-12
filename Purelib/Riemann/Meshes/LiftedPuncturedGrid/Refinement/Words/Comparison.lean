module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Requests

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Corrections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction.Physical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues.Requests
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Tactic.Ring

/-! # Complete old-word to fresh-basis comparison on one numerical bank

The actual A and full corrected-B reductions retain all physical, face and
annular terms. Their six requests precede one common stage and one original
face bank and triangle-reading cache. Every estimate consumes those same
observations; no final sample comparison is an input.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates (FaceResidualRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet annulusSheet stripSheet freshSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {periods : Paired.PeriodPrograms.Prepared paired}
    {annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})}
    {strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})}
    {rowIndex : Fin genus} {source : retained.PairCompilation oldBank newBank periods annuli strips rowIndex}
    {freshOrdered : BasedBranchBank.Ordered newBank freshSheet}
    {freshPaired : OrderedBranchPairs.Ordered.Paired freshOrdered}
    {fresh : Paired.PeriodPrograms.Prepared freshPaired} {basis : fresh.GeometricBasis}
    {boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences retained.fine.mesh.triangulation.faces)}
    {factory : boundary = retained.fine.boundaryComponents}
    (coordinates : PairCoordinates source basis boundary factory)

/-- The actual resplit source-A cochain value minus its computed fresh corrected-period combination. -/
@[expose] def aDifference (reading : OrientedEdge retained.fine.vertices.count → Canonical) : Canonical :=
  retained.fine.edges.chainValue retained.fine.vertices reading
    (retained.included.resplit source.aClosed.walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet -
    coordinates.a.coordinates.periodValue reading

/-- The actual resplit full corrected-B value minus its computed fresh corrected-period combination. -/
@[expose] def bDifference (reading : OrientedEdge retained.fine.vertices.count → Canonical) : Canonical :=
  retained.fine.edges.chainValue retained.fine.vertices reading
    (retained.included.resplit source.bClosed.walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet -
    coordinates.b.coordinates.periodValue reading

/-- The actual A difference is the sum of all three retained remainders, without dropping physical loops. -/
theorem aDifference_eq (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    coordinates.aDifference reading =
      gaussianSum (coordinates.a.loops.rows.map (fun entry => (entry.1 : Canonical) *
        SewingRetraction.wordValue reading entry.2)) + coordinates.a.coordinates.faceResidual reading +
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue reading occurrence.word)
        source.a.compiled.regulars :=
  (congrArg (fun amount : Canonical => amount - coordinates.a.coordinates.periodValue reading)
    (coordinates.a_values reading anti)).trans (by ring1)

/-- Full corrected B retains its physical, face and annular terms in the exact source-to-basis difference. -/
theorem bDifference_eq (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    coordinates.bDifference reading =
      gaussianSum (coordinates.b.loops.rows.map (fun entry => (entry.1 : Canonical) *
        SewingRetraction.wordValue reading entry.2)) + coordinates.b.coordinates.faceResidual reading +
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue reading occurrence.word)
        source.b.compiled.regulars :=
  (congrArg (fun amount : Canonical => amount - coordinates.b.coordinates.periodValue reading)
    (coordinates.b_values reading anti)).trans (by ring1)

variable (differential : Differential genus)
variable (domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars)
variable (target : Rational) (positive : 0 < target) (minimum : Nat)

/-- The same source compilation, coordinate cache and six original remainder requests, with their exact common stage.

Physical requests retain their actual exterior/hole factories. Face and
annular requests retain their original signed lists and chart factories.
The common allowance is computed before observations, and the retained
stage is the maximum of these actual requests and the supplied minimum.
-/
abbrev ComparisonRequests (polynomial : Option (Ordinary curve.polynomial) := none) :=
  ({value : retained.PairCompilation oldBank newBank periods annuli strips rowIndex // value = source} ×
    {_data : PairCoordinates source basis boundary factory // _data = coordinates}) ×
  (physical :
    PhysicalLoopRequests.Preparation retained.fine domains differential
      (coordinates.a.loops.loopTarget (Aggregate.perTerm target 3))
      (coordinates.a.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial ×
    PhysicalLoopRequests.Preparation retained.fine domains differential
      (coordinates.b.loops.loopTarget (Aggregate.perTerm target 3))
      (coordinates.b.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial) ×
  (faces :
    FaceResidualRequest coordinates.a.coordinates differential domains (Aggregate.perTerm target 3)
      (Aggregate.perTerm_positive positive 3) polynomial ×
    FaceResidualRequest coordinates.b.coordinates differential domains (Aggregate.perTerm target 3)
      (Aggregate.perTerm_positive positive 3) polynomial) ×
  (annular :
    Compilation.CorrectionRequest source.a differential domains (Aggregate.perTerm target 3)
      (Aggregate.perTerm_positive positive 3) polynomial ×
    Compilation.CorrectionRequest source.b differential domains (Aggregate.perTerm target 3)
      (Aggregate.perTerm_positive positive 3) polynomial) ×
  {index : Nat // index = max minimum (max (max physical.1.index physical.2.index)
    (max (max faces.1.request.index faces.2.request.index) (max annular.1.request.index annular.2.request.index)))}

namespace ComparisonRequests

/-- Assemble given request caches and their scalar maximum without reducing their geometric producers. -/
private def withRequests {polynomial : Option (Ordinary curve.polynomial)}
    (physical :
      PhysicalLoopRequests.Preparation retained.fine domains differential
        (coordinates.a.loops.loopTarget (Aggregate.perTerm target 3))
        (coordinates.a.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial ×
      PhysicalLoopRequests.Preparation retained.fine domains differential
        (coordinates.b.loops.loopTarget (Aggregate.perTerm target 3))
        (coordinates.b.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial)
    (faces :
      FaceResidualRequest coordinates.a.coordinates differential domains (Aggregate.perTerm target 3)
        (Aggregate.perTerm_positive positive 3) polynomial ×
      FaceResidualRequest coordinates.b.coordinates differential domains (Aggregate.perTerm target 3)
        (Aggregate.perTerm_positive positive 3) polynomial)
    (annular :
      Compilation.CorrectionRequest source.a differential domains (Aggregate.perTerm target 3)
        (Aggregate.perTerm_positive positive 3) polynomial ×
      Compilation.CorrectionRequest source.b differential domains (Aggregate.perTerm target 3)
        (Aggregate.perTerm_positive positive 3) polynomial) :
    ComparisonRequests coordinates differential domains target positive minimum polynomial :=
  let index : {value : Nat // value = max minimum (max (max physical.1.index physical.2.index)
      (max (max faces.1.request.index faces.2.request.index) (max annular.1.request.index annular.2.request.index)))} :=
    ⟨max minimum (max (max physical.1.index physical.2.index)
      (max (max faces.1.request.index faces.2.request.index)
        (max annular.1.request.index annular.2.request.index))), rfl⟩
  ⟨⟨⟨source, rfl⟩, ⟨coordinates, rfl⟩⟩, physical, faces, annular, index⟩

end ComparisonRequests

/-- Prepare all actual A/full-B remainder requests and their common stage before constructing any numerical bank. -/
def requestComparison (polynomial : Option (Ordinary curve.polynomial) := none) :
    ComparisonRequests coordinates differential domains target positive minimum polynomial :=
  let component := Aggregate.perTerm target 3
  have componentPositive := Aggregate.perTerm_positive positive 3
  let aPhysical :=
    coordinates.a.preparePhysicalLoops domains differential component componentPositive minimum polynomial
  let bPhysical :=
    coordinates.b.preparePhysicalLoops domains differential component componentPositive minimum polynomial
  let aFace := coordinates.a.coordinates.requestFaceResidual differential domains component componentPositive polynomial
  let bFace := coordinates.b.coordinates.requestFaceResidual differential domains component componentPositive polynomial
  let aAnnular := source.a.requestCorrections differential domains component componentPositive polynomial
  let bAnnular := source.b.requestCorrections differential domains component componentPositive polynomial
  ComparisonRequests.withRequests coordinates differential domains target positive minimum (polynomial := polynomial)
    ⟨aPhysical, bPhysical⟩ ⟨aFace, bFace⟩ ⟨aAnnular, bAnnular⟩

namespace ComparisonRequests

variable {coordinates differential domains target positive minimum}
variable {polynomial : Option (Ordinary curve.polynomial)}
variable (kept : ComparisonRequests coordinates differential domains target positive minimum polynomial)

/-- Read the same whole original coordinate and physical-loop cache. -/
@[expose] def data : PairCoordinates source basis boundary factory := kept.1.2.val

/-- The actual coordinate owner remains unchanged. -/
theorem data_eq : kept.data = coordinates := kept.1.2.property

/-- Read the same complete original source compilation, including its closed words and root owners. -/
@[expose] def sourceCompilation : retained.PairCompilation oldBank newBank periods annuli strips rowIndex :=
  kept.1.1.val

/-- The original source compilation retains its complete identity. -/
theorem sourceCompilation_eq : kept.sourceCompilation = source := kept.1.1.property

/-- Read the actual retained A exterior/hole request cache. -/
@[expose] def aPhysical :
    PhysicalLoopRequests.Preparation retained.fine domains differential
      (coordinates.a.loops.loopTarget (Aggregate.perTerm target 3))
      (coordinates.a.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial := kept.2.1.1

/-- Read the actual retained full-B exterior/hole request cache. -/
@[expose] def bPhysical :
    PhysicalLoopRequests.Preparation retained.fine domains differential
      (coordinates.b.loops.loopTarget (Aggregate.perTerm target 3))
      (coordinates.b.loops.loopTarget_positive (Aggregate.perTerm_positive positive 3)) minimum polynomial := kept.2.1.2

/-- Read the actual A source-minus-basis signed-face request. -/
@[expose] def aFace : FaceResidualRequest coordinates.a.coordinates differential domains (Aggregate.perTerm target 3)
    (Aggregate.perTerm_positive positive 3) polynomial := kept.2.2.1.1

/-- Read the actual full-B source-minus-basis signed-face request. -/
@[expose] def bFace : FaceResidualRequest coordinates.b.coordinates differential domains (Aggregate.perTerm target 3)
    (Aggregate.perTerm_positive positive 3) polynomial := kept.2.2.1.2

/-- Read the actual compiled A annular correction request. -/
@[expose] def aAnnular : Compilation.CorrectionRequest source.a differential domains (Aggregate.perTerm target 3)
    (Aggregate.perTerm_positive positive 3) polynomial := kept.2.2.2.1.1

/-- Read the actual compiled full-B annular correction request. -/
@[expose] def bAnnular : Compilation.CorrectionRequest source.b differential domains (Aggregate.perTerm target 3)
    (Aggregate.perTerm_positive positive 3) polynomial := kept.2.2.2.1.2

/-- Read the selected common numerical stage of those same six requests. -/
@[expose] def index : Nat := kept.2.2.2.2.val

/-- The stage is exactly the retained six request maxima together with the supplied minimum. -/
theorem index_eq : kept.index = max minimum (max (max kept.aPhysical.index kept.bPhysical.index)
    (max (max kept.aFace.request.index kept.bFace.request.index)
      (max kept.aAnnular.request.index kept.bAnnular.request.index))) := kept.2.2.2.2.property

/-- The selected stage retains the supplied numerical floor. -/
theorem minimum_le : minimum ≤ kept.index :=
  (Data.Nat.Order.le_max_left _ _).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual A exterior and hole requests. -/
theorem aPhysical_le : kept.aPhysical.index ≤ kept.index :=
  (((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual full-B exterior and hole requests. -/
theorem bPhysical_le : kept.bPhysical.index ≤ kept.index :=
  (((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual A signed-face request. -/
theorem aFace_le : kept.aFace.request.index ≤ kept.index :=
  ((((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual full-B signed-face request. -/
theorem bFace_le : kept.bFace.request.index ≤ kept.index :=
  ((((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual A annular correction request. -/
theorem aAnnular_le : kept.aAnnular.request.index ≤ kept.index :=
  ((((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- The selected stage pays the actual full-B annular correction request. -/
theorem bAnnular_le : kept.bAnnular.request.index ≤ kept.index :=
  ((((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
    (Data.Nat.Order.le_max_right _ _)).trans (Data.Nat.Order.le_max_right _ _)).trans_eq kept.index_eq.symm

/-- Every later shared bank pays the actual A source-to-basis difference, including all three remainders. -/
theorem a_accurate
    (kept : ComparisonRequests coordinates differential domains target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared retained.fine.mesh)
    (later : kept.index ≤ stage) :
    normSq (coordinates.aDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) <
      target := by
  have physical := coordinates.a.physicalLoops_accurate degree (Aggregate.perTerm_positive positive 3)
    kept.aPhysical readings (kept.aPhysical_le.trans later)
  have face := kept.aFace.accurate (kept.aFace_le.trans later) readings
  have annular := kept.aAnnular.accurate (kept.aAnnular_le.trans later) readings
  have bounded := Budget.Aggregate.normSq_add_add_lt _ _ _ positive physical.le face.le annular.le
  have same := coordinates.aDifference_eq (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
    (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values)
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq amount < target) same) bounded

/-- Every later shared bank pays the complete corrected-B source-to-fresh-basis cochain difference. -/
theorem b_accurate
    (kept : ComparisonRequests coordinates differential domains target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains} (readings : TriangleReadings shared retained.fine.mesh)
    (later : kept.index ≤ stage) :
    normSq (coordinates.bDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) <
      target := by
  have physical := coordinates.b.physicalLoops_accurate degree (Aggregate.perTerm_positive positive 3)
    kept.bPhysical readings (kept.bPhysical_le.trans later)
  have face := kept.bFace.accurate (kept.bFace_le.trans later) readings
  have annular := kept.bAnnular.accurate (kept.bAnnular_le.trans later) readings
  have bounded := Budget.Aggregate.normSq_add_add_lt _ _ _ positive physical.le face.le annular.le
  have same := coordinates.bDifference_eq (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
    (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values)
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq amount < target) same) bounded

/-- The actual physical, source-minus-basis face and annular common comparison data for both A and full B. -/
@[expose] def Comparison {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type _ :=
  (kept.aPhysical.Comparison shared × kept.bPhysical.Comparison shared) ×
  (kept.aFace.Comparison shared × kept.bFace.Comparison shared) ×
  (kept.aAnnular.Comparison shared × kept.bAnnular.Comparison shared)

/-- Execute all six original comparison families once, sharing the GIVEN exact polynomial primitive bank. -/
def compare {stage : Nat}
    (shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    kept.Comparison shared :=
  let aPhysical := kept.aPhysical.compare shared
  let bPhysical := kept.bPhysical.compare shared
  let aFace := kept.aFace.compare shared
  let bFace := kept.bFace.compare shared
  let aAnnular := kept.aAnnular.compare shared
  let bAnnular := kept.bAnnular.compare shared
  ⟨⟨aPhysical, bPhysical⟩, ⟨aFace, bFace⟩, ⟨aAnnular, bAnnular⟩⟩

/-- SAME-bank retained polynomial comparisons internally pay every remainder of the actual source-A basis difference. -/
theorem a_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared retained.fine.mesh) (compared : kept.Comparison shared)
    (later : kept.index ≤ stage) :
    normSq (coordinates.aDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) <
      target := by
  have physical := coordinates.a.physicalLoops_comparison_accurate degree (Aggregate.perTerm_positive positive 3)
    kept.aPhysical readings compared.1.1 (kept.aPhysical_le.trans later)
  have face := kept.aFace.comparison_accurate (kept.aFace_le.trans later) compared.2.1.1 readings
  have annular := kept.aAnnular.comparison_accurate (kept.aAnnular_le.trans later) compared.2.2.1 readings
  have bounded := Budget.Aggregate.normSq_add_add_lt _ _ _ positive physical.le face.le annular.le
  have same := coordinates.aDifference_eq (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
    (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values)
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq amount < target) same) bounded

/-- SAME-bank retained polynomial comparisons pay full corrected B without dropping its physical, face or annular terms.
-/
theorem b_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) {stage : Nat}
    {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared retained.fine.mesh) (compared : kept.Comparison shared)
    (later : kept.index ≤ stage) :
    normSq (coordinates.bDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)) <
      target := by
  have physical := coordinates.b.physicalLoops_comparison_accurate degree (Aggregate.perTerm_positive positive 3)
    kept.bPhysical readings compared.1.2 (kept.bPhysical_le.trans later)
  have face := kept.bFace.comparison_accurate (kept.bFace_le.trans later) compared.2.1.2 readings
  have annular := kept.bAnnular.comparison_accurate (kept.bAnnular_le.trans later) compared.2.2.2 readings
  have bounded := Budget.Aggregate.normSq_add_add_lt _ _ _ positive physical.le face.le annular.le
  have same := coordinates.bDifference_eq (CanonicalEdgeValues.edgeValuation retained.fine.mesh readings.values)
    (CanonicalEdgeValues.edgeValuation_reverse retained.fine.mesh readings.values)
  exact Eq.mpr (congrArg (fun amount : Canonical => normSq amount < target) same) bounded

end ComparisonRequests

/-- The whole request factory and one numerical bank and reading cache at its exact selected common stage. -/
abbrev ComparisonPreparation (polynomial : Option (Ordinary curve.polynomial) := none) :=
  (requests : {value : ComparisonRequests coordinates differential domains target positive minimum polynomial //
    value = coordinates.requestComparison differential domains target positive minimum polynomial}) ×
  (numerics : {value : FacePrimitiveBank differential requests.val.index domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) //
    value = FacePrimitiveBank.buildRequested differential requests.val.index domains polynomial}) ×
  {value : TriangleReadings numerics.val retained.fine.mesh //
    value = TriangleReadings.build numerics.val retained.fine.mesh}

/-- Realize given whole requests with one original numerical bank and one original triangle-reading constructor. -/
private def withComparisonRequests {polynomial : Option (Ordinary curve.polynomial)}
    (requests : {value : ComparisonRequests coordinates differential domains target positive minimum polynomial //
      value = coordinates.requestComparison differential domains target positive minimum polynomial}) :
    ComparisonPreparation coordinates differential domains target positive minimum polynomial :=
  let numerics : {value : FacePrimitiveBank differential requests.val.index domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) //
      value = FacePrimitiveBank.buildRequested differential requests.val.index domains polynomial} :=
    ⟨FacePrimitiveBank.buildRequested differential requests.val.index domains polynomial, rfl⟩
  let readings : {value : TriangleReadings numerics.val retained.fine.mesh //
      value = TriangleReadings.build numerics.val retained.fine.mesh} :=
    ⟨TriangleReadings.build numerics.val retained.fine.mesh, rfl⟩
  ⟨requests, numerics, readings⟩

/-- Prepare all six requests and their stage, then construct one shared numerical bank and triangle-reading cache. -/
def prepareComparison (polynomial : Option (Ordinary curve.polynomial) := none) :
    ComparisonPreparation coordinates differential domains target positive minimum polynomial :=
  let requests : {value : ComparisonRequests coordinates differential domains target positive minimum polynomial //
      value = coordinates.requestComparison differential domains target positive minimum polynomial} :=
    ⟨coordinates.requestComparison differential domains target positive minimum polynomial, rfl⟩
  withComparisonRequests coordinates differential domains target positive minimum (polynomial := polynomial) requests

namespace ComparisonPreparation

variable {coordinates differential domains target positive minimum}
variable {polynomial : Option (Ordinary curve.polynomial)}
variable (kept : ComparisonPreparation coordinates differential domains target positive minimum polynomial)

/-- Read the same whole six-request preparation, before its numerical realization. -/
@[expose] def requests : ComparisonRequests coordinates differential domains target positive minimum polynomial :=
  kept.1.val

/-- Read the sufficient common stage selected by those same requests. -/
@[expose] def index : Nat := kept.requests.index

/-- Read the same original face bank used for all six remainder estimates. -/
@[expose] def numerics : FacePrimitiveBank differential kept.index domains
    (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) := kept.2.1.val

/-- Read the same original triangle observations shared by A and full corrected B. -/
@[expose] def readings : TriangleReadings kept.numerics retained.fine.mesh := kept.2.2.val

/-- The whole request cache is its single original comparison preparation. -/
theorem requests_eq : kept.requests =
    coordinates.requestComparison differential domains target positive minimum polynomial := kept.1.property

/-- The retained numerical bank is its original constructor at the actual selected stage. -/
theorem numerics_eq (kept : ComparisonPreparation coordinates differential domains target positive minimum) :
    kept.numerics = FacePrimitiveBank.build differential kept.index domains :=
  kept.2.1.property.trans (FacePrimitiveBank.buildRequested_none differential kept.index domains)

/-- The whole retained bank is its one actual selected constructor at the exact original request stage. -/
theorem numerics_requested_eq : kept.numerics =
    FacePrimitiveBank.buildRequested differential kept.index domains polynomial := kept.2.1.property

/-- The retained observations are the original reading constructor on that same numerical bank. -/
theorem readings_eq : kept.readings = TriangleReadings.build kept.numerics retained.fine.mesh := kept.2.2.property

/-- The actual shared numerical stage retains the supplied minimum. -/
theorem minimum_le : minimum ≤ kept.index := kept.requests.minimum_le

/-- The actual shared observations pay the complete source-A to computed fresh-basis cochain difference. -/
theorem a_accurate
    (kept : ComparisonPreparation coordinates differential domains target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.aDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.readings.values)) <
      target := kept.requests.a_accurate degree kept.readings (Nat.le_refl _)

/-- The same actual observations pay the complete full corrected-B to computed fresh-basis cochain difference. -/
theorem b_accurate
    (kept : ComparisonPreparation coordinates differential domains target positive minimum)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.bDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.readings.values)) <
      target := kept.requests.b_accurate degree kept.readings (Nat.le_refl _)

/-- The actual six comparison families on this SAME stored original numerical bank. -/
@[expose] def Comparison : Type _ := kept.requests.Comparison kept.numerics

/-- Execute all six retained comparison families once after the one original bank and reading cache are fixed. -/
def compare : kept.Comparison := kept.requests.compare kept.numerics

/-- The SAME retained polynomial comparison data pay the complete actual source-A basis difference internally. -/
theorem a_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) (compared : kept.Comparison) :
    normSq (coordinates.aDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.readings.values)) <
      target := kept.requests.a_comparison_accurate degree kept.readings compared (Nat.le_refl _)

/-- The SAME retained polynomial comparison data pay the complete full corrected-B basis difference internally. -/
theorem b_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) (compared : kept.Comparison) :
    normSq (coordinates.bDifference (CanonicalEdgeValues.edgeValuation retained.fine.mesh kept.readings.values)) <
      target := kept.requests.b_comparison_accurate degree kept.readings compared (Nat.le_refl _)

end ComparisonPreparation

/-- One actual whole preparation and the SAME six post-bank comparison caches, on its selected numerator and stage. -/
@[expose] def Comparison (polynomial : Option (Ordinary curve.polynomial) := none) : Type _ :=
  (prepared : ComparisonPreparation coordinates differential domains target positive minimum polynomial) ×
    prepared.Comparison

/-- Construct the actual requests, one bank and one reading cache, then retain all six common comparisons once. -/
def compare (polynomial : Option (Ordinary curve.polynomial) := none) :
    Comparison coordinates differential domains target positive minimum polynomial :=
  let prepared := coordinates.prepareComparison differential domains target positive minimum polynomial
  let compared := ComparisonPreparation.compare prepared
  ⟨prepared, compared⟩

namespace Comparison

variable {coordinates differential domains target positive minimum}
    {polynomial : Option (Ordinary curve.polynomial)}
    (compared : Comparison coordinates differential domains target positive minimum polynomial)

/-- Read the SAME whole original preparation, including request, bank and reading factories. -/
@[expose] def preparation : ComparisonPreparation coordinates differential domains target positive minimum polynomial :=
  compared.1

/-- Read the SAME six actual post-bank comparison cache products without another producer call. -/
@[expose] def comparisons : compared.preparation.Comparison := compared.2

/-- The actual retained A difference meets its request from this SAME complete constructor result. -/
theorem a_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.aDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh compared.preparation.readings.values)) < target :=
  ComparisonPreparation.a_comparison_accurate compared.preparation degree compared.comparisons

/-- The actual full corrected-B difference meets its request from this SAME complete constructor result. -/
theorem b_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.bDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh compared.preparation.readings.values)) < target :=
  ComparisonPreparation.b_comparison_accurate compared.preparation degree compared.comparisons

end Comparison

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates
