module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents.Polynomial.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.GeometricBasis
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Comparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Coordinates
import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words.Paired
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

/-! # The original paired comparison on a given certified next-budget cache

The same finite P budget can select additional fresh-source floors before
any new model or primitive observation. One original pipeline then feeds
the existing paired WordPreparation, triangle cache and all six actual
comparisons. No second budget, primitive, shared bank or comparison is
prepared to recover a producer equation.
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

namespace WordPreparation

/-- Complete original producer factories identify the entire four-field word preparation.

The proof eliminates only equalities of the retained certified cache
values, one dependency at a time. No imported builder is unfolded or
executed and no equality beneath a function is introduced.
-/
theorem eq_of_factories
    (first last : WordPreparation coordinates differential domains target positive minimum word polynomial
      wordTarget wordPositive minimumFloor modelStage) : first = last := by
  rcases first with ⟨firstRequests, firstNumerical, firstTriangles, firstCompared⟩
  rcases last with ⟨lastRequests, lastNumerical, lastTriangles, lastCompared⟩
  have requestsEq : firstRequests = lastRequests :=
    Subtype.ext (firstRequests.property.trans lastRequests.property.symm)
  cases requestsEq
  have numericalEq : firstNumerical = lastNumerical :=
    Subtype.ext (firstNumerical.property.trans lastNumerical.property.symm)
  cases numericalEq
  have trianglesEq : firstTriangles = lastTriangles :=
    Subtype.ext (firstTriangles.property.trans lastTriangles.property.symm)
  cases trianglesEq
  have comparedEq : firstCompared = lastCompared :=
    Subtype.ext (firstCompared.property.trans lastCompared.property.symm)
  cases comparedEq
  rfl

end WordPreparation

/-- Consume the SAME given next-budget cache and retained original six-request product in the existing word pipeline.

The returned product is the original WordPreparation family. Its whole
numerical factory is derived by the original given-budget constructor;
all post-bank comparisons use that same single P primitive bank.
-/
def prepareWordWithBudgets
    (needed : {value : ComparisonRequests coordinates differential domains target positive minimum (some polynomial) //
      value = coordinates.requestComparison differential domains target positive minimum (some polynomial)})
    (nextBudgets : PolynomialPreparation.Budgets word polynomial.val wordTarget wordPositive) :
    {prepared : WordPreparation coordinates differential domains target positive minimum word polynomial
        wordTarget wordPositive minimumFloor modelStage //
      prepared = prepareWord coordinates differential domains target positive minimum word polynomial
          wordTarget wordPositive minimumFloor modelStage ∧
        prepared.cochainRequests = needed.val ∧ prepared.numerical.meshBudgets = nextBudgets.val} :=
  let built := PolynomialPreparation.buildAtFaceStageWithBudgets word polynomial.val polynomial.property
    wordTarget wordPositive minimumFloor modelStage needed.val.index nextBudgets
  let numerical : {value : PolynomialPreparation.Preparation word polynomial.val polynomial.property
      wordTarget wordPositive minimumFloor modelStage (some needed.val.index) //
      value = PolynomialPreparation.buildAtFaceStage word polynomial.val polynomial.property
        wordTarget wordPositive minimumFloor modelStage needed.val.index} :=
    ⟨built.val, built.property.1⟩
  let readings : {value : TriangleReadings numerical.val.primitiveBank retained.fine.mesh //
      value = TriangleReadings.build numerical.val.primitiveBank retained.fine.mesh} :=
    ⟨TriangleReadings.build numerical.val.primitiveBank retained.fine.mesh, rfl⟩
  let compared : {value : needed.val.Comparison numerical.val.primitiveBank //
      value = needed.val.compare numerical.val.primitiveBank} :=
    ⟨needed.val.compare numerical.val.primitiveBank, rfl⟩
  let prepared : WordPreparation coordinates differential domains target positive minimum word polynomial
      wordTarget wordPositive minimumFloor modelStage := ⟨needed, numerical, readings, compared⟩
  ⟨prepared, WordPreparation.eq_of_factories
    (coordinates := coordinates) (differential := differential) (domains := domains)
    (target := target) (positive := positive) (minimum := minimum) (word := word)
    (polynomial := polynomial) (wordTarget := wordTarget) (wordPositive := wordPositive)
    (minimumFloor := minimumFloor) (modelStage := modelStage) prepared
    (prepareWord coordinates differential domains target positive minimum word polynomial
      wordTarget wordPositive minimumFloor modelStage), rfl, built.property.2⟩

end ComparisonRequests

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement.PairCoordinates

end
