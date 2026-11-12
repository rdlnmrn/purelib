module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

/-! # One ordinary-numerator bank for a closed fragment word and paired cochains

The six actual cochain requests precede the one model/primitive pipeline.
Its selected face stage meets their retained common floor. The returned
comparison products and the closed-word model comparison consume that same
primitive bank. Identifying the closed fragment value with a particular
resplit cochain remains a separate directed, rooted incidence statement.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment (SplitSheets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets.Closed
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Topology.Polygon.Stokes (triangleEdgeOccurrences)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original clearance}
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
    (differential : Differential genus)
    (domains : FaceDomainBank retained.fine.frames retained.fineBase.faces.regulars)
    (target : Rational) (positive : 0 < target) (minimum : Nat)

variable {sampleCount : Nat} {requestTarget tolerance : Rational}
    {points : List Canonical} {index : Nat} {oldNumerator : CoefficientPolynomial}
    {oldBudgets : FaceMeshBudgets differential points tolerance (numerator := oldNumerator) domains}
    {oldNumerics : FacePrimitiveBank differential index (numerator := oldNumerator) domains}
    {oldShared : FaceSharedMeshes (numerator := oldNumerator) oldBudgets oldNumerics}
    {axes : PrimitiveAxes retained.fineBase.bank.grid}
    {parents : List (CenteredEdge curve differential)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := retained.fineBase) axes splits}
    {requests : RequestedParents sampleCount requestTarget parents}
    {entries : SplitSheets domains fragments requests}
    {point : LiftedPoint 2} {root : Named}
    {geometry : CenteredPathChain parents (start := point) (finish := point)}
    {roots : RootChain parents root root}
    {included : ∀ value ∈ Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (word : Fragment.SplitSheets.Closed oldShared entries geometry roots included)
    (polynomial : Ordinary curve.polynomial)
    (wordTarget : Rational) (wordPositive : 0 < wordTarget) (minimumFloor modelStage : Nat)

namespace ComparisonRequests

/-- The actual six requests, one paid closed-word bank, and all comparisons on that SAME bank.

The request and numerical constructors are retained whole. The selected
numerical floor is the actual request index, while the source floor and
model stage remain independent. No equality between a fragment sum and a
resplit period value is imposed by this cache product.
-/
abbrev WordPreparation :=
  (needed : {value : ComparisonRequests coordinates differential domains target positive minimum (some polynomial) //
    value = coordinates.requestComparison differential domains target positive minimum (some polynomial)}) ×
  (Σ prepared : {value : PolynomialPreparation.Preparation word polynomial.val polynomial.property
      wordTarget wordPositive minimumFloor modelStage (some needed.val.index) //
    value = PolynomialPreparation.buildAtFaceStage word polynomial.val polynomial.property
      wordTarget wordPositive minimumFloor modelStage needed.val.index},
  Σ _readings : {value : TriangleReadings prepared.val.primitiveBank retained.fine.mesh //
    value = TriangleReadings.build prepared.val.primitiveBank retained.fine.mesh},
  {value : needed.val.Comparison prepared.val.primitiveBank //
    value = needed.val.compare prepared.val.primitiveBank})

/-- Allocate the six original requests before one genuine-P model and primitive bank, then compare on that bank.

The closed word supplies the unchanged physical leaves, endpoint caches and
signed joins. Its original pipeline executes once with the actual common
request floor. Only after that bank exists are its triangle readings and
six original post-bank comparisons prepared.
-/
def prepareWord : WordPreparation coordinates differential domains target positive minimum word polynomial
    wordTarget wordPositive minimumFloor modelStage :=
  let needed : {value : ComparisonRequests coordinates differential domains target positive minimum (some polynomial) //
      value = coordinates.requestComparison differential domains target positive minimum (some polynomial)} :=
    ⟨coordinates.requestComparison differential domains target positive minimum (some polynomial), rfl⟩
  let prepared : {value : PolynomialPreparation.Preparation word polynomial.val polynomial.property
      wordTarget wordPositive minimumFloor modelStage (some needed.val.index) //
      value = PolynomialPreparation.buildAtFaceStage word polynomial.val polynomial.property
        wordTarget wordPositive minimumFloor modelStage needed.val.index} :=
    ⟨PolynomialPreparation.buildAtFaceStage word polynomial.val polynomial.property
      wordTarget wordPositive minimumFloor modelStage needed.val.index, rfl⟩
  let readings : {value : TriangleReadings prepared.val.primitiveBank retained.fine.mesh //
      value = TriangleReadings.build prepared.val.primitiveBank retained.fine.mesh} :=
    ⟨TriangleReadings.build prepared.val.primitiveBank retained.fine.mesh, rfl⟩
  let compared : {value : needed.val.Comparison prepared.val.primitiveBank //
      value = needed.val.compare prepared.val.primitiveBank} :=
    ⟨needed.val.compare prepared.val.primitiveBank, rfl⟩
  ⟨needed, prepared, readings, compared⟩

namespace WordPreparation

variable {coordinates differential domains target positive minimum word polynomial
  wordTarget wordPositive minimumFloor modelStage}
variable (prepared : WordPreparation coordinates differential domains target positive minimum word polynomial
  wordTarget wordPositive minimumFloor modelStage)

/-- Read the same actual six pre-observation requests and their common index. -/
@[expose] def cochainRequests :
    ComparisonRequests coordinates differential domains target positive minimum (some polynomial) := prepared.1.val

/-- Read the one complete closed-word source/model/primitive/shared/comparison preparation. -/
@[expose] def numerical : PolynomialPreparation.Preparation word polynomial.val polynomial.property
    wordTarget wordPositive minimumFloor modelStage (some prepared.cochainRequests.index) := prepared.2.1.val

/-- Read the actual triangle cache on the primitive bank shared by every retained comparison. -/
@[expose] def triangles : TriangleReadings prepared.numerical.primitiveBank retained.fine.mesh :=
  prepared.2.2.1.val

/-- Read the six actual post-bank comparison products on that identical primitive bank. -/
@[expose] def comparison : prepared.cochainRequests.Comparison prepared.numerical.primitiveBank := prepared.2.2.2.val

/-- The complete pre-observation requests retain their single original factory. -/
theorem requests_eq : prepared.cochainRequests =
    coordinates.requestComparison differential domains target positive minimum (some polynomial) :=
  prepared.1.property

/-- The original model/numerical pipeline retains the actual request index as its independent floor. -/
theorem numerical_eq : prepared.numerical = PolynomialPreparation.buildAtFaceStage word polynomial.val
    polynomial.property wordTarget wordPositive minimumFloor modelStage prepared.cochainRequests.index :=
  prepared.2.1.property

/-- The numerical stage genuinely meets the actual retained common request floor. -/
theorem cochainRequests_le : prepared.cochainRequests.index ≤ prepared.numerical.faceStage :=
  prepared.numerical.minimumStage_le rfl

/-- The triangle readings retain their single constructor on the shared primitive bank. -/
theorem triangles_eq : prepared.triangles =
    TriangleReadings.build prepared.numerical.primitiveBank retained.fine.mesh := prepared.2.2.1.property

/-- The whole post-bank comparison cache retains its original one-execution factory. -/
theorem comparison_eq : prepared.comparison = prepared.cochainRequests.compare prepared.numerical.primitiveBank :=
  prepared.2.2.2.property

/-- The literal closed-word gap value obeys its independently requested ordinary-model error. -/
theorem model_accurate : normSq (prepared.numerical.comparison.value -
    (PathModel.mk (PolynomialWork.Models.cells
      requests.covered prepared.numerical.work prepared.numerical.models)).integralSample) < wordTarget :=
  prepared.numerical.accurate

/-- The actual ordered outgoing gaps, including the retained closing slot, satisfy the same paid model bound. -/
theorem gaps_accurate : normSq (gaussianSum
    (Fragment.SplitSheets.Closed.gaps prepared.numerical.sharedMeshes entries geometry roots
      prepared.numerical.word) -
    (PathModel.mk (PolynomialWork.Models.cells
      requests.covered prepared.numerical.work prepared.numerical.models)).integralSample) < wordTarget :=
  prepared.numerical.gaps_accurate

/-- Every original fragment still contributes its literal outgoing occurrence, including stationary roles. -/
theorem gaps_length :
    (Fragment.SplitSheets.Closed.gaps prepared.numerical.sharedMeshes entries geometry roots
      prepared.numerical.word).length = Fragment.SplitSheets.fragmentCount entries :=
  prepared.numerical.gaps_length

/-- The same bank pays the full source-A physical, face and annular cochain difference. -/
theorem a_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.aDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh prepared.triangles.values)) < target :=
  prepared.cochainRequests.a_comparison_accurate degree prepared.triangles
    prepared.comparison prepared.cochainRequests_le

/-- The same bank pays full corrected B while retaining every physical, face and annular occurrence. -/
theorem b_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    normSq (coordinates.bDifference
      (CanonicalEdgeValues.edgeValuation retained.fine.mesh prepared.triangles.values)) < target :=
  prepared.cochainRequests.b_comparison_accurate degree prepared.triangles
    prepared.comparison prepared.cochainRequests_le

end WordPreparation

end ComparisonRequests

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates
