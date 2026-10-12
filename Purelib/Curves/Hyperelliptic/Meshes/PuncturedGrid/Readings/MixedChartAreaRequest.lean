module
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Topology.Mesh

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Mixed chart-area comparison for two retained differential banks

The existing chart-area request compares one retained value to the actual
source increments. A mixed value `conj left + coefficient * right` has no
`FacePrimitiveBank` of its own, but its per-source chart difference is the
conjugate-linear combination of the two single-differential chart requests.
This module glues the two requests with `pathArea_difference_bound` and pays
the combined magnitude, which is the only genuinely new analytic step of the
value-parameterized region chain.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (SignedSourceChartRequest
  oppositeSource)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (SourceChartRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Integration.Path.IncrementArea (pathArea)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

set_option genInjectivity false in
/-- The mixed chart request caches both single-differential source requests at one allowance and pays their
conjugate-linear combination. -/
structure MixedChartAreaRequest (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    (domains : Domains owner)
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential)
    (coefficient : Data.Gaussian.Basic.Canonical) (sources : Sources owner) (target : Fraction.Rational) where
  /-- The original requested complete mixed area tolerance is strictly positive. -/ positive : 0 < target
  /-- The cached complete occurrence-count and mixed-magnitude error weight. -/ weight : Fraction.Rational
  /-- The weight is exactly the original fourth-power occurrence expression with the retained mixing coefficient. -/
    weight_eq : weight = 32 * (1 + normSq coefficient) * (sources.length : Fraction.Rational) ^ 4 *
    (8 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient + 2)
  /-- The cached common positive allowance for both original single-differential requests. -/ allowance :
    Fraction.Rational
  /-- The allowance is the minimum of the mixed-error unit ceiling and the original weighted target budget. -/
    allowance_eq : allowance = min (1 / (2 * (1 + normSq coefficient)))
    (Weighted.allowance target weight)
  /-- The actual common retained allowance is strictly positive. -/ allowance_positive : 0 < allowance
  /-- The original left-differential chart requests on every retained signed source occurrence. -/ left :
    SourceChartRequests leftDifferential domains allowance sources
  /-- The original right-differential chart requests on the same actual source occurrences. -/ right :
    SourceChartRequests rightDifferential domains allowance sources
  /-- The cached stage paying both original magnitude banks and both retained source request banks. -/ index : Nat
  /-- The stage is exactly the maximum of the original two magnitude and two request stages. -/ index_eq : index = max
    leftFixed.index (max rightFixed.index (max left.index right.index))

constructive_injectivity MixedChartAreaRequest

namespace MixedChartAreaRequest

variable {leftDifferential rightDifferential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical} {sources : Sources owner} {target :
    Purelib.Data.Rat.Fraction.Rational}

/-- The complete mixed area weight is nonnegative for the original magnitude banks and occurrence count. -/
public theorem weight_nonnegative (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (sources : Sources owner) :
    0 ≤ 32 * (1 + normSq coefficient) * (sources.length : Fraction.Rational) ^ 4 *
      (8 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient + 2) :=
   Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
     (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 32)
    (add_nonneg (by decide) (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient)))
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient))
      (by decide))

/-- Prepare both original differential requests at one paid allowance and cache the complete common stage. -/
@[expose] def build (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    (domains : Domains owner)
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential)
    (coefficient : Data.Gaussian.Basic.Canonical) (sources : Sources owner)
    (nonloop : Nonloop owner sources)
    (target : Fraction.Rational) (positive : 0 < target) :
    MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential domains leftFixed rightFixed coefficient
      sources target :=
  let weight := 32 * (1 + normSq coefficient) * (sources.length : Fraction.Rational) ^ 4 *
    (8 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient + 2)
  let allowance := min (1 / (2 * (1 + normSq coefficient)))
    (Weighted.allowance target weight)
  have weightNonnegative : 0 ≤ weight :=
    weight_nonnegative leftFixed rightFixed coefficient sources
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct (by decide) (Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive
      coefficient))
    (Weighted.allowance_positive positive weightNonnegative)
  let left := SourceChartRequests.build leftDifferential domains allowance allowancePositive sources nonloop
  let right := SourceChartRequests.build rightDifferential domains allowance allowancePositive sources nonloop
  ⟨positive, weight, rfl, allowance, rfl, allowancePositive, left, right,
    max leftFixed.index (max rightFixed.index (max left.index right.index)), rfl⟩

/-- The common request stage pays the first original magnitude bank's validity floor. -/
theorem left_magnitude_le (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) : leftFixed.index ≤ request.index :=
  request.index_eq ▸ Data.Nat.Order.le_max_left _ _

/-- The common request stage pays the second original magnitude bank's validity floor. -/
theorem right_magnitude_le (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) : rightFixed.index ≤ request.index :=
  request.index_eq ▸ (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The common request stage pays the first retained signed chart request bank. -/
theorem left_chart_le (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) : request.left.index ≤ request.index :=
  request.index_eq ▸ (Data.Nat.Order.le_max_left _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))

/-- The common request stage pays the second retained signed chart request bank. -/
theorem right_chart_le (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) : request.right.index ≤ request.index :=
  request.index_eq ▸ (Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))

/-- The retained conjugate-linear error allowance is at most one. -/
private theorem allowance_small (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) :
    2 * (1 + normSq coefficient) * request.allowance ≤ 1 := by
  have scalePositive := Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive coefficient
  have small : request.allowance ≤ 1 / (2 * (1 + normSq coefficient)) :=
    request.allowance_eq ▸ Fraction.Order.Basic.min_le_left _ _
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small scalePositive.le
  refine bound.trans_eq ?_
  rw [Fraction.Field.mul_comm, Fraction.Field.div_mul_cancel_of_ne _ _
    scalePositive.ne']

/-- The mixed per-source chart difference is the conjugate-linear combination of the two single-differential
differences. -/
private theorem source_errors (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target)
    {stage : Nat} {leftData : PrimitiveBank owner leftDifferential stage domains}
    {rightData : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftData) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightData)
    (leftLater : request.left.index ≤ stage) (rightLater : request.right.index ≤ stage) :
    ∀ source ∈ sources,
      normSq (source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient) -
        CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
          rightReadings.values coefficient)
          (source.project owner.mesh.triangulation.faces)) ≤ 2 * (1 + normSq coefficient) * request.allowance := by
  intro source member
  have leftBound := (request.left.accurate leftReadings leftLater source member).le
  have rightBound := (request.right.accurate rightReadings rightLater source member).le
  have support := request.left.supported source member
  rw [EdgeMagnitude.source_increment_mixValues (owner := owner),
    EdgeMagnitude.edgeValuation_mixValues (owner := owner) coefficient support]
  have expand : (conj (source.increment leftReadings.values) + coefficient * source.increment rightReadings.values) -
      (conj (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project
        owner.mesh.triangulation.faces)) +
        coefficient * CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
          owner.mesh.triangulation.faces)) =
      conj (source.increment leftReadings.values -
        CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project
          owner.mesh.triangulation.faces)) +
      coefficient * (source.increment rightReadings.values -
        CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
          owner.mesh.triangulation.faces)) := by
    simp only [← Data.Gaussian.Basic.conj_eq_canonical]
    rw [EdgeMagnitude.conj_sub]
    ring1
  simp only [Data.Gaussian.Basic.conj_eq_canonical]
  rw [expand]
  have estimate : normSq (conj (source.increment leftReadings.values -
      CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project owner.mesh.triangulation.faces))
        +
      coefficient * (source.increment rightReadings.values -
        CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
          owner.mesh.triangulation.faces))) ≤
      2 * (normSq (source.increment leftReadings.values -
        CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project
          owner.mesh.triangulation.faces)) +
        normSq coefficient * normSq (source.increment rightReadings.values -
          CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
            owner.mesh.triangulation.faces))) := by
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Basic.conj_eq_canonical] using
      EdgeMagnitude.normSq_conj_add_mul
        (source.increment leftReadings.values -
          CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project
            owner.mesh.triangulation.faces))
        (source.increment rightReadings.values -
          CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
            owner.mesh.triangulation.faces)) coefficient
  refine estimate.trans ?_
  have inner : normSq (source.increment leftReadings.values -
      CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values (source.project owner.mesh.triangulation.faces))
        +
      normSq coefficient * normSq (source.increment rightReadings.values -
        CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values (source.project
          owner.mesh.triangulation.faces)) ≤
      request.allowance + normSq coefficient * request.allowance :=
    Fraction.Order.Arithmetic.add_le_add_direct leftBound (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      rightBound (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
      decide : (0 : Fraction.Rational) ≤ 2)
  exact scaled.trans_eq (by ring1)

/-- The actual combined per-source error budget from the retained common allowance and mixing coefficient. -/
@[expose] def ErrorBudget (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target) : Fraction.Rational :=
  2 * (1 + normSq coefficient) * request.allowance

/-- The complete mixed increment magnitude budget from both original retained magnitude banks. -/
@[expose, reducible] def MagnitudeBudget (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical) :
      Fraction.Rational :=
  8 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient + 2

/-- The exact pair of original triangle reading banks at their shared stage with the retained mixing coefficient. -/
@[expose, reducible] def Sample (domains : Domains owner)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) (coefficient :
      Data.Gaussian.Basic.Canonical) :=
  SourceChartComparison.MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient

/-- The cached original source observations on the exact mixed reading sample and retained occurrence list. -/
@[expose, reducible] def Observations (sample : Sample (owner := owner) domains leftDifferential rightDifferential
  coefficient)
    (sources : Sources owner) :=
  SourceChartComparison.SourceObservations sample.values sources

/-- The source/chart comparison on the supplied original observation cache with the retained mixed error and magnitude
budgets. -/
@[expose, reducible] def ComparisonData (request : MixedChartAreaRequest (owner := owner) leftDifferential
  rightDifferential
    domains leftFixed rightFixed coefficient sources target)
    (sample : Sample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (source : Observations sample sources) :=
  SourceChartComparison.Comparison sample.values sources source (ErrorBudget request)
    (MagnitudeBudget leftFixed rightFixed coefficient)

set_option genInjectivity false in
/-- Both actual input banks/readings and the selected signed request are retained, together with their original-parent
equalities and cached comparison. The supplied source polygon is physically retained by comparison.source. -/
structure Realization (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target)
    (sample : Sample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (source : Observations sample sources) where
  /-- The actual retained mixed chart request whose comparison is realized. -/ selection : MixedChartAreaRequest (owner
    := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target
  /-- The retained selection is exactly the originally supplied request. -/ selection_eq : selection = request
  /-- The actual original pair of triangle reading banks and mixing coefficient. -/ readings : Sample (owner := owner)
    domains leftDifferential rightDifferential coefficient
  /-- The retained readings are exactly the supplied original sample. -/ readings_eq : readings = sample
  /-- The original sample stage pays the complete retained request schedule. -/ later : request.index ≤ sample.stage
  /-- The cached comparison consuming the exact supplied original source observations. -/ comparison : ComparisonData
    request sample source

constructive_injectivity Realization

/-- Realize against the original supplied source observations. No source increments or source summary are evaluated by
this executable constructor. -/
@[expose] def realize (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target)
    (sample : Sample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (source : Observations sample sources) (later : request.index ≤ sample.stage) :
    Realization request sample source :=
  have leftLater := request.left_chart_le.trans later
  have rightLater := request.right_chart_le.trans later
  let magnitude := sample.magnitude leftFixed rightFixed
    (request.left_magnitude_le.trans later) (request.right_magnitude_le.trans later)
  have errorNonnegative : 0 ≤ ErrorBudget request :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient))) request.allowance_positive.le
  let comparison := SourceChartComparison.realizeSupplied source magnitude (ErrorBudget request)
    errorNonnegative (by exact allowance_small request)
    (by exact source_errors request sample.leftReadings sample.rightReadings leftLater rightLater)
  ⟨request, rfl, sample, rfl, later, comparison⟩

namespace Realization

variable {request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target}
  {sample : Sample (owner := owner) domains leftDifferential rightDifferential coefficient}
  {source : Observations sample sources}

/-- The cached actual source-area minus chart-area residual. -/
@[expose] def residual (realization : Realization request sample source) : Gaussian := realization.comparison.residual
/-- The cached squared-norm bound for the actual mixed source/chart residual. -/
@[expose] def areaBound (realization : Realization request sample source) : Fraction.Rational :=
  realization.comparison.areaBound
/-- The cached area of the acquired canonical chart increment summary. -/
@[expose] def chartArea (realization : Realization request sample source) : Gaussian :=
  realization.comparison.chartSummary.area

/-- Retrieve each original forward/backward chart witness at the actual ordered occurrence. The bound is retained
explicitly, including for repeated sources. -/
@[expose] def leftRequestAt (realization : Realization request sample source) (occurrence : Fin sources.length) :
    SignedSourceChartRequests.SignedSourceChartRequest
      (sources[occurrence.val]'occurrence.isLt) leftDifferential domains realization.selection.allowance :=
  realization.selection.left.at occurrence

/-- Retrieve the original right-differential signed chart request at the exact bounded source occurrence. -/
@[expose] def rightRequestAt (realization : Realization request sample source) (occurrence : Fin sources.length) :
    SignedSourceChartRequests.SignedSourceChartRequest
      (sources[occurrence.val]'occurrence.isLt) rightDifferential domains realization.selection.allowance :=
  realization.selection.right.at occurrence

/-- The retained reading stage pays the original left-differential request bank. -/
theorem left_stage (realization : Realization request sample source) :
    realization.selection.left.index ≤ realization.readings.stage := by
  rw [realization.selection_eq, realization.readings_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸
      realization.later)))

/-- The retained reading stage pays the original right-differential request bank. -/
theorem right_stage (realization : Realization request sample source) :
    realization.selection.right.index ≤ realization.readings.stage := by
  rw [realization.selection_eq, realization.readings_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸
      realization.later)))

/-- The original strict single-reading certificate remains available at each retained occurrence; deriving the weak
mixed bound does not discard it. -/
theorem left_occurrence_accurate (realization : Realization request sample source)
    (occurrence : Fin sources.length) :
    normSq ((sources[occurrence.val]'occurrence.isLt).increment realization.readings.leftReadings.values -
      CanonicalEdgeValues.edgeValuation owner.mesh realization.readings.leftReadings.values
        ((sources[occurrence.val]'occurrence.isLt).project owner.mesh.triangulation.faces)) <
      realization.selection.allowance :=
  realization.selection.left.at_accurate occurrence realization.readings.leftReadings realization.left_stage

/-- The original right-differential strict chart error certificate remains valid at the actual retained source
occurrence. -/
theorem right_occurrence_accurate (realization : Realization request sample source)
    (occurrence : Fin sources.length) :
    normSq ((sources[occurrence.val]'occurrence.isLt).increment realization.readings.rightReadings.values -
      CanonicalEdgeValues.edgeValuation owner.mesh realization.readings.rightReadings.values
        ((sources[occurrence.val]'occurrence.isLt).project owner.mesh.triangulation.faces)) <
      realization.selection.allowance :=
  realization.selection.right.at_accurate occurrence realization.readings.rightReadings realization.right_stage

/-- The realized comparison retains exactly the originally supplied source observation cache. -/
theorem source_identity (realization : Realization request sample source) :
    realization.comparison.source = source := realization.comparison.source_eq

/-- The retained residual is the original cached source area minus the actual acquired chart summary area. -/
theorem residual_cached (realization : Realization request sample source) :
    realization.residual = source.summary.area - realization.chartArea :=
  realization.comparison.residual_cached

/-- The retained chart area reads the canonical projected source word in original occurrence order. -/
theorem chart_readback (realization : Realization request sample source) :
    realization.chartArea = Purelib.Topology.Mesh.RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh
      sample.values)
      (sources.map (fun occurrence => occurrence.project owner.mesh.triangulation.faces)) := by
  change realization.comparison.chartSummary.area = _
  rw [realization.comparison.chartSummary.area_eq, realization.comparison.chart_eq]
  unfold SourceChartComparison.ChartIncrements RetracingWords.wordArea
  rw [Data.List.Map.map_map]
  rfl

/-- The cached residual equals the original source polygon area minus its canonical projected-edge word area. -/
theorem residual_readback (realization : Realization request sample source) :
    realization.residual = IncrementArea.pathArea (sources.map (fun occurrence => occurrence.increment sample.values)) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh sample.values)
        (sources.map (fun occurrence => occurrence.project owner.mesh.triangulation.faces)) :=
  realization.comparison.residual_readback

/-- The cached complete area bound equals the original request weight times its retained allowance. -/
theorem budget_identity (realization : Realization request sample source) :
    realization.areaBound = request.weight * request.allowance := by
  rw [areaBound, realization.comparison.bound_readback, ErrorBudget, MagnitudeBudget, request.weight_eq]
  ring1

/-- The retained weighted allowance pays the complete original mixed area target. -/
theorem budget (realization : Realization request sample source) : realization.areaBound ≤ target := by
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸
    weight_nonnegative leftFixed rightFixed coefficient sources
  rw [realization.budget_identity]
  calc
    request.weight * request.allowance ≤
        request.weight * Weighted.allowance target request.weight := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ weightNonnegative
      rw [request.allowance_eq]
      exact Fraction.Order.Basic.min_le_right _ _
    _ ≤ target := Weighted.mul_allowance_le request.positive.le weightNonnegative

/-- The squared norm of the actual retained mixed source/chart residual is bounded by its cached area bound. -/
theorem bounded (realization : Realization request sample source) :
    normSq realization.residual ≤ realization.areaBound := realization.comparison.numeric.bounded

/-- Pay and read the already realized comparison. The constructor is never called by this theorem, and both exact
reading parents remain accessible. -/
theorem pay (realization : Realization request sample source) : normSq realization.residual ≤ target :=
  realization.comparison.pay realization.budget

end Realization

/-- Preserve the original numeric contract using the retained comparison. Actual stem callers consume the cached
realization directly. -/
theorem accurate (request : MixedChartAreaRequest (owner := owner) leftDifferential rightDifferential
    domains leftFixed rightFixed coefficient sources target)
    {stage : Nat} (later : request.index ≤ stage)
    {leftData : PrimitiveBank owner leftDifferential stage domains}
    {rightData : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftData) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightData) :
    normSq (IncrementArea.pathArea (sources.map (fun source =>
        source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient))) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues (owner := owner)
        leftReadings.values rightReadings.values coefficient))
        (sources.map (fun source => source.project owner.mesh.triangulation.faces))) ≤ target := by
  let sample := SourceChartComparison.MixedReadings.ofReadings (owner := owner) coefficient leftReadings rightReadings
  let source := SourceChartComparison.SourceObservations.realize sample.values sources
  let realization := realize request sample source later
  have paid := realization.pay
  rw [realization.residual_readback] at paid
  exact paid

end MixedChartAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
