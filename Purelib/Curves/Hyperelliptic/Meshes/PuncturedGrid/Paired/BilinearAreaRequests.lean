module
import Purelib.Data.List.Membership
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Integration.Path.PairedAreaComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.PairedSources

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Integration.Path.PairedIncrementComparison
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Requested opposite-sheet comparison for the full two-differential source
area. Each component uses its own whole-edge request on the same paired walk. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearAreaRequests

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.PairedAreaComparison
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Surface.Sewing

open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (Requests)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars}

namespace BilinearAreaRequest

/-- The exact original source-chart owner determined by the retained lifted mesh. -/
@[reducible, expose] def SelectedOwner := SourceChartComparison.ownerFromMesh mesh

/-- The sum of actual source increments on two distinct original sheets equals the retained two-sheet sum.

The two bounded sheet indices must be different, so the retained zero and one
source increments occur exactly once, in either displayed order. -/
private theorem source_sum {start finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge base.bank.grid start
  finish}
    (head : EdgeOccurrences mesh edge) (values : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (left right : Fin 2) (different : left ≠ right) :
    (head.source left).increment values + (head.source right).increment values =
      head.zeroSource.increment values + head.oneSource.increment values := by
  revert right
  refine Data.Fin.cases_induction ?_ ?_ left
  · intro right
    refine Data.Fin.cases_induction ?_ ?_ right
    · intro different; exact (different rfl).elim
    · intro remaining
      refine Data.Fin.cases_induction ?_ ?_ remaining
      · intro _; rfl
      · intro impossible; exact Fin.elim0 impossible
  · intro remaining
    refine Data.Fin.cases_induction ?_ ?_ remaining
    · intro right
      refine Data.Fin.cases_induction ?_ ?_ right
      · intro _
        change head.oneSource.increment values + head.zeroSource.increment values =
          head.zeroSource.increment values + head.oneSource.increment values
        exact Data.Gaussian.Basic.Canonical.add_comm _ _
      · intro remaining
        refine Data.Fin.cases_induction ?_ ?_ remaining
        · intro different; exact (different rfl).elim
        · intro impossible; exact Fin.elim0 impossible
    · intro impossible; exact Fin.elim0 impossible

/-- Every actual retained paired source occurrence satisfies the original paid opposite-sheet increment bound.

The different sheets share the original request spine and sufficiently late
sample stage. Each head bound and recursive tail keep their own source parents. -/
theorem pair_errors {differential : Differentials.Basic.Differential genus} {error : Fraction.Rational} {stage : Nat}
    {bank : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings bank mesh) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk mesh walk) (requests : PairedWalk.Requests domains differential error paired)
      (left right : Fin 2), left ≠ right → requests.index ≤ stage →
      ∀ pair ∈ PairedSources.pairs (owner := SelectedOwner (mesh := mesh)) paired left right,
        Data.Gaussian.Norm.Basic.normSq (pair.1.increment readings.values + pair.2.increment readings.values) ≤
          error
  | _, _, _, .nil _, .nil _, _, _, _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, .cons (edge := edge) head tail, .cons request remaining, left, right, different, later, pair, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · change Data.Gaussian.Norm.Basic.normSq ((head.source left).increment readings.values +
          (head.source right).increment readings.values) ≤ error
        rw [source_sum head readings.values left right different]
        exact (head.accurate readings readings request
          ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans later)).le
      · have injective := ((edges.edge edge).bijection
          (BranchCellBank.referenceAt base.bank.toBranchCellBank _ edge.vertices.1).toLoop (BranchCellBank.referenceAt
            base.bank.toBranchCellBank _ edge.vertices.2).toLoop).forward_injective
        exact pair_errors readings tail remaining _ _ (fun equal => different (injective equal))
          ((Data.Nat.Order.le_max_right _ _).trans later) pair member

end BilinearAreaRequest

set_option genInjectivity false in
/-- The complete original two-differential opposite-sheet area request.

Each differential keeps its own magnitude reference and whole-edge request bank on the same retained paired walk. -/
structure BilinearAreaRequest {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk base.bank.grid start finish} (paired :
      WalkOccurrences.PairedWalk mesh walk)
    (error : Fraction.Rational) where
  /-- The original requested full area-comparison tolerance is strictly positive. -/ positive : 0 < error
  /-- The cached original fourth-power walk-count and joint magnitude weight. -/ weight : Fraction.Rational
  /-- The weight retains the exact original edge count and maximum of the two magnitude references. -/ weight_eq :
    weight = 64 * (walk.edgeCount : Fraction.Rational)^4 * max leftFixed.bound rightFixed.bound
  /-- The cached positive tolerance shared by the original whole-edge request banks. -/ perEdge : Fraction.Rational
  /-- The edge tolerance is exactly the original weighted allowance of the target and retained weight. -/ perEdge_eq :
    perEdge = Weighted.allowance error weight
  /-- The original whole-edge request bank for the first retained differential. -/ left : PairedWalk.Requests domains
    leftDifferential perEdge paired
  /-- The original whole-edge request bank for the second retained differential. -/ right : PairedWalk.Requests domains
    rightDifferential perEdge paired

constructive_injectivity BilinearAreaRequest

namespace BilinearAreaRequest

variable {leftDifferential rightDifferential : Differential genus}
  {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains rightDifferential}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    base.bank.grid start finish} {paired :
    PairedWalk mesh walk} {error :
    Rational}

/-- The original complete walk-count and joint-magnitude comparison weight is nonnegative.

The natural edge count has nonnegative fourth power. Its fixed positive factor
and the retained nonnegative magnitude maximum preserve that bound. -/
theorem weight_nonnegative (leftFixed : FaceMagnitudeBank domains leftDifferential)
    (rightFixed : FaceMagnitudeBank domains rightDifferential) (walk : Walks.Walk base.bank.grid start finish) :
    0 ≤ 64 * (walk.edgeCount : Fraction.Rational)^4 * max leftFixed.bound rightFixed.bound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (leftFixed.nonnegative.trans (Fraction.Order.Basic.le_max_left _ _))

/-- Cache the original joint weight and positive edge allowance, then prepare both distinct differential requests on the
same retained paired walk. -/
@[expose] def build (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains
  rightDifferential)
    (paired : WalkOccurrences.PairedWalk mesh walk) (error : Fraction.Rational) (positive : 0 < error) :
    BilinearAreaRequest leftFixed rightFixed paired error :=
  let weight := 64 * (walk.edgeCount : Fraction.Rational)^4 * max leftFixed.bound rightFixed.bound
  let perEdge := Weighted.allowance error weight
  have perEdgePositive := Weighted.allowance_positive positive (weight_nonnegative leftFixed rightFixed walk)
  ⟨positive, weight, rfl, perEdge, rfl,
    Requests.build domains leftDifferential perEdge perEdgePositive paired,
    Requests.build domains rightDifferential perEdge perEdgePositive paired⟩

/-- The common stage paying both original magnitude references and both retained whole-edge request banks. -/
@[expose] def index (request : BilinearAreaRequest leftFixed rightFixed paired error) : Nat :=
  max (max leftFixed.index rightFixed.index) (max request.left.index request.right.index)

/-- The actual paired source-occurrence selection on the original mesh owner and two retained sheets. -/
@[reducible, expose] def SelectedSources (paired : WalkOccurrences.PairedWalk mesh walk) (left right : Fin 2) :=
  PairedSources.Selection
    (owner := SelectedOwner (mesh := mesh)) paired left right

/-- The original primitive bank for one retained differential at the supplied numerical stage. -/
@[reducible, expose] def BankAt (differential : Differentials.Basic.Differential genus) (stage : Nat) :=
  PrimitiveData.FacePrimitiveBank differential stage domains

/-- The original magnitude certificate on the exact retained triangle primitive values. -/
@[reducible, expose] def RetainedMagnitude (values : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :=
  Readings.EdgeMagnitude
    (owner := SourceChartComparison.ownerFromMesh mesh) values

/-- The actual original triangle reading parent on its retained primitive bank. -/
@[reducible, expose] def ParentReadings {differential : Differentials.Basic.Differential genus} {stage : Nat}
    (bank : PrimitiveData.FacePrimitiveBank differential stage domains) := TrianglePrimitiveReadings.TriangleReadings
      bank mesh

/-- The original source increment pair in the selected direct or conjugate bilinear view. -/
@[reducible, expose] def SourceValue (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :=
  PairedAreaComparison.point view
    (source.increment leftValues) (source.increment rightValues)

/-- The actual selected source pairs with the second retained point negated for opposite-sheet comparison. -/
@[reducible, expose] def PointPairs (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (entries : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length × SewnPrimitiveContacts.SourceEdge
      mesh.triangles.length)) :=
  entries.map (fun pair =>
    (SourceValue view leftValues rightValues pair.1,
      PairedAreaComparison.negative (SourceValue view leftValues rightValues pair.2)))

/-- The retained complete observation and summary of an original ordered source polygon. -/
@[reducible, expose] def SourceObservation (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) :=
  PairedAreaComparison.Observation (sources.map (SourceValue view leftValues rightValues))

/-- Four times the maximum of the two original retained magnitude bounds. -/
@[reducible, expose] def NumericBound (leftFixed : FaceMagnitudeBank domains leftDifferential)
    (rightFixed : FaceMagnitudeBank domains rightDifferential) : Fraction.Rational :=
  (4 : Fraction.Rational) * max leftFixed.bound rightFixed.bound

/-- The actual cached paired-area comparison on the original source selection, view, allowance and magnitude bound. -/
@[reducible, expose] def PairComparison (view : PairedAreaComparison.View)
    (request : BilinearAreaRequest leftFixed rightFixed paired error)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    {leftSheet rightSheet : Fin 2} (selection : SelectedSources paired leftSheet rightSheet) :=
  PairedAreaComparison.Cached
    (PointPairs view leftValues rightValues selection.entries) request.perEdge (NumericBound leftFixed rightFixed)

set_option genInjectivity false in
/-- The actual original opposite-sheet area comparison with both differential parents retained.

The exact view, request, stage, primitive banks, magnitude references, source observations and numeric summaries remain
linked by readback equalities. -/
structure Realization (view : PairedAreaComparison.View)
    (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : ParentReadings leftBank) (rightReadings : ParentReadings rightBank)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet) where
  /-- The actual retained original paired source-occurrence selection. -/ selection : SelectedSources paired leftSheet
    rightSheet
  /-- The retained original direct or conjugate comparison view. -/ viewParent : PairedAreaComparison.View
  /-- The retained view is exactly the supplied original view. -/ viewParent_eq : viewParent = view
  /-- The actual original bilinear request consumed by this realization. -/ requestParent : BilinearAreaRequest
    leftFixed rightFixed paired error
  /-- The retained request is exactly the supplied original request. -/ requestParent_eq : requestParent = request
  /-- The retained actual numerical sample stage. -/ sampleStage : Nat
  /-- The retained sample stage equals the original supplied stage. -/ sampleStage_eq : sampleStage = stage
  /-- The original request is paid at that exact retained sample stage. -/ validity : request.index ≤ sampleStage
  /-- The actual original left differential magnitude reference. -/ leftFixedParent : FaceMagnitudeBank domains
    leftDifferential
  /-- The retained left magnitude parent is exactly the supplied original reference. -/ leftFixedParent_eq :
    leftFixedParent = leftFixed
  /-- The actual original right differential magnitude reference. -/ rightFixedParent : FaceMagnitudeBank domains
    rightDifferential
  /-- The retained right magnitude parent is exactly the supplied original reference. -/ rightFixedParent_eq :
    rightFixedParent = rightFixed
  /-- The actual original left differential primitive bank at the retained stage. -/ leftBankParent : BankAt
    leftDifferential stage
  /-- The retained left primitive parent is exactly the supplied original bank. -/ leftBankParent_eq : leftBankParent =
    leftBank
  /-- The actual original right differential primitive bank at the retained stage. -/ rightBankParent : BankAt
    rightDifferential stage
  /-- The retained right primitive parent is exactly the supplied original bank. -/ rightBankParent_eq : rightBankParent
    = rightBank
  /-- The retained original magnitude certificate on the actual left reading values. -/ leftMagnitude :
    RetainedMagnitude leftReadings.values
  /-- The actual left magnitude certificate preserves the original fixed bound. -/ leftMagnitude_bound :
    leftMagnitude.bound = leftFixed.bound
  /-- The actual left magnitude certificate preserves the original reference stage. -/ leftMagnitude_index :
    leftMagnitude.index = leftFixed.index
  /-- The retained original magnitude certificate on the actual right reading values. -/ rightMagnitude :
    RetainedMagnitude rightReadings.values
  /-- The actual right magnitude certificate preserves the original fixed bound. -/ rightMagnitude_bound :
    rightMagnitude.bound = rightFixed.bound
  /-- The actual right magnitude certificate preserves the original reference stage. -/ rightMagnitude_index :
    rightMagnitude.index = rightFixed.index
  /-- The actual original left triangle reading parent. -/ leftParent : ParentReadings leftBank
  /-- The retained left reading parent is exactly the supplied original bank reading. -/ leftParent_eq : leftParent =
    leftReadings
  /-- The actual original right triangle reading parent. -/ rightParent : ParentReadings rightBank
  /-- The retained right reading parent is exactly the supplied original bank reading. -/ rightParent_eq : rightParent =
    rightReadings
  /-- The cached actual paired-area comparison on the retained original source selection. -/ numeric : PairComparison
    view request leftReadings.values rightReadings.values selection
  /-- The complete original source observation on the retained left sheet. -/ leftSources : SourceObservation view
    leftReadings.values rightReadings.values (paired.sources leftSheet)
  /-- The original left source summary area is exactly the corresponding retained numeric comparison area. -/
    leftArea_eq : leftSources.summary.areaValue = numeric.firstSummary.areaValue
  /-- The complete original source observation on the retained right sheet. -/ rightSources : SourceObservation view
    leftReadings.values rightReadings.values (paired.sources rightSheet)
  /-- The original right source summary area is exactly the corresponding retained numeric comparison area. -/
    rightArea_eq : rightSources.summary.areaValue = numeric.secondSummary.areaValue

constructive_injectivity Realization

namespace Realization

variable {view : Purelib.Integration.Path.PairedAreaComparison.View}
  {request : BilinearAreaRequest leftFixed rightFixed paired error}
  {stage : Nat} {leftBank : FacePrimitiveBank
    leftDifferential stage domains}
  {rightBank : FacePrimitiveBank rightDifferential
    stage domains}
  {leftReadings : ParentReadings leftBank} {rightReadings : ParentReadings rightBank}
  {later : request.index ≤ stage} {leftSheet rightSheet : Fin 2} {different : leftSheet ≠ rightSheet}

/-- The actual cached original opposite-sheet area discrepancy. -/
@[expose] def residual (result : Realization view request leftReadings rightReadings later leftSheet rightSheet
  different) : Gaussian :=
  result.numeric.residual

/-- The cached complete original quantitative area-comparison bound. -/
@[expose] def areaBound (result : Realization view request leftReadings rightReadings later leftSheet rightSheet
  different) : Fraction.Rational :=
  result.numeric.areaBound

/-- The retained residual is the difference of the two actual original source polygons in their selected view. -/
theorem residual_readback (result : Realization view request leftReadings rightReadings later leftSheet rightSheet
  different) :
    result.residual =
      PairedIncrementArea.area ((paired.sources leftSheet).map (SourceValue view leftReadings.values
        rightReadings.values)) -
      PairedIncrementArea.area ((paired.sources rightSheet).map (SourceValue view leftReadings.values
        rightReadings.values)) := by
  rw [residual, result.numeric.residual_eq, ← result.leftArea_eq, ← result.rightArea_eq,
    result.leftSources.area_readback, result.rightSources.area_readback]

/-- The actual cached area bound is exactly the original complete weight times its retained per-edge allowance. -/
theorem budget_identity (result : Realization view request leftReadings rightReadings later leftSheet rightSheet
  different) :
    result.areaBound = request.weight * request.perEdge := by
  rw [areaBound, result.numeric.bound_readback, PointPairs, Data.List.Map.length_map]
  have count : result.selection.entries.length = walk.edgeCount :=
    result.selection.entries_count.trans result.selection.count_eq
  exact (congrArg (fun count : Nat =>
    PairedAreaComparison.BoundSpecification count request.perEdge
      (NumericBound leftFixed rightFixed)) count).trans (by
    change 16 * (walk.edgeCount : Fraction.Rational)^4 * request.perEdge *
      (4 * max leftFixed.bound rightFixed.bound) = request.weight * request.perEdge
    rw [request.weight_eq]
    ring1)

/-- The original requested tolerance pays the complete retained numeric area bound. -/
theorem budget (result : Realization view request leftReadings rightReadings later leftSheet rightSheet different) :
    result.areaBound ≤ error := by
  rw [result.budget_identity, request.perEdge_eq]
  exact Weighted.mul_allowance_le request.positive.le
    (request.weight_eq ▸ weight_nonnegative leftFixed rightFixed walk)

/-- The original requested tolerance bounds the squared norm of the actual cached area residual. -/
theorem pay (result : Realization view request leftReadings rightReadings later leftSheet rightSheet different) :
    Data.Gaussian.Norm.Basic.normSq result.residual ≤ error := result.numeric.pay result.budget

end Realization

/-- Reading the first values from the original mapped source pairs preserves their actual first-source order. -/
private theorem mapped_first
    (value : SewnPrimitiveContacts.SourceEdge mesh.triangles.length → PrimitivePoint)
    (pairs : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length × SewnPrimitiveContacts.SourceEdge
      mesh.triangles.length)) :
    (pairs.map (fun pair => (value pair.1, PairedAreaComparison.negative (value pair.2)))).map Prod.fst =
      (pairs.map Prod.fst).map value := by
  induction pairs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (value head.1)) ih

/-- Reading the second values from the original mapped source pairs preserves their actual negated second-source order.
-/
private theorem mapped_second
    (value : SewnPrimitiveContacts.SourceEdge mesh.triangles.length → PrimitivePoint)
    (pairs : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length × SewnPrimitiveContacts.SourceEdge
      mesh.triangles.length)) :
    (pairs.map (fun pair => (value pair.1, PairedAreaComparison.negative (value pair.2)))).map Prod.snd =
      (pairs.map Prod.snd).map (fun source => PairedAreaComparison.negative (value source)) := by
  induction pairs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons (PairedAreaComparison.negative (value head.2))) ih

/-- Acquire the original direct bilinear comparison using the supplied retained source selection.

Both original magnitude references and primitive banks are preserved, and both complete source summaries reuse the
actual numeric comparison caches. -/
@[expose] def realizePairedWithSources (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet)
    (selection : SelectedSources paired leftSheet rightSheet) :
    Realization .paired request leftReadings rightReadings later leftSheet rightSheet different := by
  let value := SourceValue .paired leftReadings.values rightReadings.values
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans later
  let retainedLeftMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) leftFixed ((Data.Nat.Order.le_max_left _ _).trans fixedLater)
      leftReadings
  let retainedRightMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) rightFixed ((Data.Nat.Order.le_max_right _ _).trans fixedLater)
      rightReadings
  have requestsLater := (Data.Nat.Order.le_max_right _ _).trans later
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative leftFixed rightFixed walk
  have perEdgePositive : 0 < request.perEdge := by
    rw [request.perEdge_eq]
    exact Weighted.allowance_positive request.positive weightNonnegative
  let bound := 4 * max leftFixed.bound rightFixed.bound
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (leftFixed.nonnegative.trans (Fraction.Order.Basic.le_max_left _ _))
  have bounded (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) : PrimitivePoint.Bounded (value source)
    bound :=
    ⟨by
      have h := (retainedLeftMagnitude.source_bounded source).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Basic.le_max_left leftFixed.bound rightFixed.bound) (by decide))
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl,
     by
      have h := (retainedRightMagnitude.source_bounded source).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Basic.le_max_right leftFixed.bound rightFixed.bound) (by decide))
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl⟩
  let pairs := selection.entries
  let points := pairs.map (fun pair => (value pair.1, PairedAreaComparison.negative (value pair.2)))
  have errors : ∀ point ∈ points, PrimitivePoint.Bounded (point.1.sub point.2) request.perEdge := by
    intro point member
    obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
    change pair ∈ selection.entries at present
    rw [selection.entries_eq] at present
    have first := pair_errors leftReadings paired request.left leftSheet rightSheet different
      ((Data.Nat.Order.le_max_left _ _).trans requestsLater) pair present
    have second := pair_errors rightReadings paired request.right leftSheet rightSheet different
      ((Data.Nat.Order.le_max_right _ _).trans requestsLater) pair present
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (pair.1.increment leftReadings.values - -pair.2.increment
        leftReadings.values) ≤ _
      have scalar : pair.1.increment leftReadings.values - -pair.2.increment leftReadings.values = pair.1.increment
        leftReadings.values + pair.2.increment leftReadings.values := by ring1
      rewrite [scalar]
      change Fraction.Order.Basic.LessEqual _ _
      change Fraction.Order.Basic.LessEqual _ _ at first
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using first
    · change Data.Gaussian.Basic.Canonical.normSq (pair.1.increment rightReadings.values - -pair.2.increment
        rightReadings.values) ≤ _
      have scalar : pair.1.increment rightReadings.values - -pair.2.increment rightReadings.values = pair.1.increment
        rightReadings.values + pair.2.increment rightReadings.values := by ring1
      rewrite [scalar]
      change Fraction.Order.Basic.LessEqual _ _
      change Fraction.Order.Basic.LessEqual _ _ at second
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using second
  have firstBound : ∀ point ∈ points, PrimitivePoint.Bounded point.1 bound := by
    intro point member
    obtain ⟨pair, _, rfl⟩ := Map.mem_map.mp member
    exact bounded pair.1
  have secondBound : ∀ point ∈ points, PrimitivePoint.Bounded point.2 bound := by
    intro point member
    obtain ⟨pair, _, rfl⟩ := Map.mem_map.mp member
    exact ⟨by simpa only [PairedAreaComparison.negative,
        Data.Gaussian.Basic.Canonical.normSq_neg] using (bounded pair.2).1,
      by simpa only [PairedAreaComparison.negative,
        Data.Gaussian.Basic.Canonical.normSq_neg] using (bounded pair.2).2⟩
  let numeric := Cached.realize points request.perEdge bound perEdgePositive.le boundNonnegative
    errors firstBound secondBound
  have firstEq : points.map Prod.fst = (paired.sources leftSheet).map value := by
    exact ((by exact mapped_first value pairs) :
      points.map Prod.fst = (pairs.map Prod.fst).map value).trans
      (congrArg (List.map value) (selection.first_entries.symm.trans selection.first_eq))
  have secondEq : points.map Prod.snd = (paired.sources rightSheet).map (fun source => PairedAreaComparison.negative
    (value source)) := by
    exact ((by exact mapped_second value pairs) :
      points.map Prod.snd = (pairs.map Prod.snd).map
        (fun source => PairedAreaComparison.negative (value source))).trans
      (congrArg (List.map (fun source => PairedAreaComparison.negative (value source)))
        (selection.second_entries.symm.trans selection.second_eq))
  let leftSources : SourceObservation .paired leftReadings.values rightReadings.values (paired.sources leftSheet) :=
    { entries := numeric.first
      entries_eq := numeric.first_eq.trans
        ((congrArg (List.map Prod.fst) numeric.pairs_eq).trans firstEq)
      summary := numeric.firstSummary }
  have rightCanonical : numeric.second.map PairedAreaComparison.negative = (paired.sources rightSheet).map value := by
    have retainedSecond := numeric.second_eq.trans
      ((congrArg (List.map Prod.snd) numeric.pairs_eq).trans secondEq)
    exact (congrArg (List.map PairedAreaComparison.negative) retainedSecond).trans
      (PairedAreaComparison.negative_map value (paired.sources rightSheet))
  let rightSources : SourceObservation .paired leftReadings.values rightReadings.values (paired.sources rightSheet) :=
    { entries := numeric.second.map PairedAreaComparison.negative
      entries_eq := rightCanonical
      summary := PairedAreaComparison.negateSummary numeric.secondSummary }
  exact { selection := selection
          viewParent := .paired
          viewParent_eq := rfl
          requestParent := request
          requestParent_eq := rfl
          sampleStage := stage
          sampleStage_eq := rfl
          validity := later
          leftFixedParent := leftFixed
          leftFixedParent_eq := rfl
          rightFixedParent := rightFixed
          rightFixedParent_eq := rfl
          leftBankParent := leftBank
          leftBankParent_eq := rfl
          rightBankParent := rightBank
          rightBankParent_eq := rfl
          leftMagnitude := retainedLeftMagnitude
          leftMagnitude_bound := rfl
          leftMagnitude_index := rfl
          rightMagnitude := retainedRightMagnitude
          rightMagnitude_bound := rfl
          rightMagnitude_index := rfl
          leftParent := leftReadings
          leftParent_eq := rfl
          rightParent := rightReadings
          rightParent_eq := rfl
          numeric := numeric
          leftSources := leftSources
          leftArea_eq := rfl
          rightSources := rightSources
          rightArea_eq := rfl }

/-- Acquire the original conjugate bilinear comparison using the supplied retained source selection.

The original first component is conjugated, both differential parents remain distinct, and both source summaries reuse
the actual numeric caches. -/
@[expose] def realizeConjugateWithSources (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet)
    (selection : SelectedSources paired leftSheet rightSheet) :
    Realization .conjugate request leftReadings rightReadings later leftSheet rightSheet different := by
  let value := SourceValue .conjugate leftReadings.values rightReadings.values
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans later
  let retainedLeftMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) leftFixed ((Data.Nat.Order.le_max_left _ _).trans fixedLater)
      leftReadings
  let retainedRightMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) rightFixed ((Data.Nat.Order.le_max_right _ _).trans fixedLater)
      rightReadings
  have requestsLater := (Data.Nat.Order.le_max_right _ _).trans later
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative leftFixed rightFixed walk
  have perEdgePositive : 0 < request.perEdge := by
    rw [request.perEdge_eq]
    exact Weighted.allowance_positive request.positive weightNonnegative
  let bound := 4 * max leftFixed.bound rightFixed.bound
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (leftFixed.nonnegative.trans (Fraction.Order.Basic.le_max_left _ _))
  have bounded (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) : PrimitivePoint.Bounded (value source)
    bound :=
    ⟨by
      have h := (Data.Gaussian.Norm.Basic.normSq_conj _).trans_le
        ((retainedLeftMagnitude.source_bounded source).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Order.Basic.le_max_left leftFixed.bound rightFixed.bound) (by decide)))
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl,
     by
      have h := (retainedRightMagnitude.source_bounded source).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Basic.le_max_right leftFixed.bound rightFixed.bound) (by decide))
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at h
      convert h using 1; rfl⟩
  let pairs := selection.entries
  let points := pairs.map (fun pair => (value pair.1, PairedAreaComparison.negative (value pair.2)))
  have errors : ∀ point ∈ points, PrimitivePoint.Bounded (point.1.sub point.2) request.perEdge := by
    intro point member
    obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
    change pair ∈ selection.entries at present
    rw [selection.entries_eq] at present
    have first := pair_errors leftReadings paired request.left leftSheet rightSheet different
      ((Data.Nat.Order.le_max_left _ _).trans requestsLater) pair present
    have second := pair_errors rightReadings paired request.right leftSheet rightSheet different
      ((Data.Nat.Order.le_max_right _ _).trans requestsLater) pair present
    constructor
    · change Data.Gaussian.Basic.Canonical.normSq (Data.Gaussian.Basic.conj (pair.1.increment
        leftReadings.values) -
        -Data.Gaussian.Basic.conj (pair.2.increment leftReadings.values)) ≤ _
      have scalar : Data.Gaussian.Basic.conj (pair.1.increment leftReadings.values) -
          -Data.Gaussian.Basic.conj (pair.2.increment leftReadings.values) =
          Data.Gaussian.Basic.conj (pair.1.increment leftReadings.values) +
            Data.Gaussian.Basic.conj (pair.2.increment leftReadings.values) := by ring1
      rewrite [scalar, ← Data.Gaussian.Basic.conj_add]
      have h := (Data.Gaussian.Norm.Basic.normSq_conj _).trans_le first
      change Fraction.Order.Basic.LessEqual _ _ at h
      change Fraction.Order.Basic.LessEqual _ _
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
    · change Data.Gaussian.Basic.Canonical.normSq (pair.1.increment rightReadings.values - -pair.2.increment
        rightReadings.values) ≤ _
      have scalar : pair.1.increment rightReadings.values - -pair.2.increment rightReadings.values = pair.1.increment
        rightReadings.values + pair.2.increment rightReadings.values := by ring1
      rewrite [scalar]
      change Fraction.Order.Basic.LessEqual _ _
      change Fraction.Order.Basic.LessEqual _ _ at second
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using second
  have firstBound : ∀ point ∈ points, PrimitivePoint.Bounded point.1 bound := by
    intro point member
    obtain ⟨pair, _, rfl⟩ := Map.mem_map.mp member
    exact bounded pair.1
  have secondBound : ∀ point ∈ points, PrimitivePoint.Bounded point.2 bound := by
    intro point member
    obtain ⟨pair, _, rfl⟩ := Map.mem_map.mp member
    exact ⟨by simpa only [PairedAreaComparison.negative,
        Data.Gaussian.Basic.Canonical.normSq_neg] using (bounded pair.2).1,
      by simpa only [PairedAreaComparison.negative,
        Data.Gaussian.Basic.Canonical.normSq_neg] using (bounded pair.2).2⟩
  let numeric := Cached.realize points request.perEdge bound perEdgePositive.le boundNonnegative
    errors firstBound secondBound
  have firstEq : points.map Prod.fst = (paired.sources leftSheet).map value := by
    exact ((by exact mapped_first value pairs) :
      points.map Prod.fst = (pairs.map Prod.fst).map value).trans
      (congrArg (List.map value) (selection.first_entries.symm.trans selection.first_eq))
  have secondEq : points.map Prod.snd = (paired.sources rightSheet).map (fun source => PairedAreaComparison.negative
    (value source)) := by
    exact ((by exact mapped_second value pairs) :
      points.map Prod.snd = (pairs.map Prod.snd).map
        (fun source => PairedAreaComparison.negative (value source))).trans
      (congrArg (List.map (fun source => PairedAreaComparison.negative (value source)))
        (selection.second_entries.symm.trans selection.second_eq))
  let leftSources : SourceObservation .conjugate leftReadings.values rightReadings.values (paired.sources leftSheet) :=
    { entries := numeric.first
      entries_eq := numeric.first_eq.trans
        ((congrArg (List.map Prod.fst) numeric.pairs_eq).trans firstEq)
      summary := numeric.firstSummary }
  have rightCanonical : numeric.second.map PairedAreaComparison.negative = (paired.sources rightSheet).map value := by
    have retainedSecond := numeric.second_eq.trans
      ((congrArg (List.map Prod.snd) numeric.pairs_eq).trans secondEq)
    exact (congrArg (List.map PairedAreaComparison.negative) retainedSecond).trans
      (PairedAreaComparison.negative_map value (paired.sources rightSheet))
  let rightSources : SourceObservation .conjugate leftReadings.values rightReadings.values (paired.sources rightSheet)
    :=
    { entries := numeric.second.map PairedAreaComparison.negative
      entries_eq := rightCanonical
      summary := PairedAreaComparison.negateSummary numeric.secondSummary }
  exact { selection := selection
          viewParent := .conjugate
          viewParent_eq := rfl
          requestParent := request
          requestParent_eq := rfl
          sampleStage := stage
          sampleStage_eq := rfl
          validity := later
          leftFixedParent := leftFixed
          leftFixedParent_eq := rfl
          rightFixedParent := rightFixed
          rightFixedParent_eq := rfl
          leftBankParent := leftBank
          leftBankParent_eq := rfl
          rightBankParent := rightBank
          rightBankParent_eq := rfl
          leftMagnitude := retainedLeftMagnitude
          leftMagnitude_bound := rfl
          leftMagnitude_index := rfl
          rightMagnitude := retainedRightMagnitude
          rightMagnitude_bound := rfl
          rightMagnitude_index := rfl
          leftParent := leftReadings
          leftParent_eq := rfl
          rightParent := rightReadings
          rightParent_eq := rfl
          numeric := numeric
          leftSources := leftSources
          leftArea_eq := rfl
          rightSources := rightSources
          rightArea_eq := rfl }

/-- Select the actual original paired source occurrences once and acquire their direct bilinear comparison at the paid
common stage. -/
@[expose] def realize (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet) :
    Realization .paired request leftReadings rightReadings later leftSheet rightSheet different :=
  realizePairedWithSources request leftReadings rightReadings later leftSheet rightSheet different
    (PairedSources.realize (owner := SelectedOwner (mesh := mesh)) paired leftSheet rightSheet)

/-- Select the actual original paired source occurrences once and acquire their conjugate bilinear comparison at the
paid common stage. -/
@[expose] def realizeConjugate (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet) :
    Realization .conjugate request leftReadings rightReadings later leftSheet rightSheet different :=
  realizeConjugateWithSources request leftReadings rightReadings later leftSheet rightSheet different
    (PairedSources.realize (owner := SelectedOwner (mesh := mesh)) paired leftSheet rightSheet)

/-- The two actual source polygons agree to the requested tolerance. This is an area comparison, not a claim that either
polygon has small area. -/
theorem accurate (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet) :
    let value := fun source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length =>
      (⟨source.increment leftReadings.values, source.increment rightReadings.values⟩ : PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((paired.sources leftSheet).map value) -
      PairedIncrementArea.area ((paired.sources rightSheet).map value)) ≤ error := by
  intro value
  let result := realize request leftReadings rightReadings later leftSheet rightSheet different
  have paid := result.pay
  rw [result.residual_readback] at paid
  exact paid

/-- Opposite-sheet conjugate polygons use the same retained whole-edge requests. Both components change sign, preserving
their paired area. -/
theorem conjugate_accurate (request : BilinearAreaRequest leftFixed rightFixed paired error)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet) :
    let value := fun source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length =>
      (⟨Data.Gaussian.Basic.conj (source.increment leftReadings.values), source.increment rightReadings.values⟩
        : PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((paired.sources leftSheet).map value) -
      PairedIncrementArea.area ((paired.sources rightSheet).map value)) ≤ error := by
  intro value
  let result := realizeConjugate request leftReadings rightReadings later leftSheet rightSheet different
  have paid := result.pay
  rw [result.residual_readback] at paid
  exact paid

end BilinearAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearAreaRequests

end
