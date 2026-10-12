module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemCancellation
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.AreaComparison
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Topology.Mesh

@[expose] public section

/-! Requested cancellation of the actual corrected excursion's stem areas.
The two chart transfers and the opposite-sheet source comparison use one
fixed magnitude bank and one later numerical bank. The hole is untouched. -/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAreaRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk (build)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_reverse)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A paid cancellation request for the two actual stem chart areas of a corrected branch excursion.

The same paired placement and fixed magnitude reference supply both source/chart transfers and the intervening
opposite-sheet comparison. -/
structure StemAreaRequest (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank
  domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The requested total stem error is strictly positive. -/ positive : 0 < target
  /-- The retained allowance for each of the three stem-area comparisons. -/ partTarget : Fraction.Rational
  /-- The common comparison allowance is exactly one tenth of the requested target. -/ partTarget_eq : partTarget =
    target / 10
  /-- The actual paired source placement of the retained branch stem. -/ paired : WalkOccurrences.PairedWalk lifted.mesh
    (bank.rows.get branch).stem
  /-- The opposite-sheet source-area request on that exact paired stem. -/ opposite : AreaRequest fixed paired
    partTarget
  /-- The source/chart transfer request for the selected outward stem sheet. -/ outward : SourceChartAreaRequest fixed
    (paired.sources sheet) partTarget
  /-- The source/chart transfer request for the other stem sheet. -/ other : SourceChartAreaRequest fixed
    (paired.sources (BranchCutLifts.otherSheet sheet)) partTarget
  /-- The cached common stage paying the three retained stem-area requests. -/ index : Nat
  /-- The retained stage is the maximum of the opposite-sheet and both source/chart request stages. -/ index_eq : index
    = max opposite.index (max outward.index other.index)

constructive_injectivity StemAreaRequest

namespace StemAreaRequest

variable {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential} {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {sheet : Fin 2} {target : Purelib.Data.Rat.Fraction.Rational}

/-- Select the paired stem once, prepare the three area requests at the common one-tenth allowance and cache their
maximum stage. -/
def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains
  differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 < target)
      :
    StemAreaRequest bank fixed branch sheet target :=
  let partTarget := target / 10
  have partPositive : 0 < partTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let paired := PairedWalk.build lifted.mesh (bank.rows.get branch).stem
  let opposite := AreaRequest.build fixed paired partTarget partPositive
  let outward := SourceChartAreaRequest.build fixed (paired.sources sheet)
    (SignedSourceChartRequests.paired_sources_nonloop paired sheet) partTarget partPositive
  let other := SourceChartAreaRequest.build fixed (paired.sources (BranchCutLifts.otherSheet sheet))
    (SignedSourceChartRequests.paired_sources_nonloop paired _) partTarget partPositive
  ⟨positive, partTarget, rfl, paired, opposite, outward, other, max opposite.index (max outward.index other.index), rfl⟩

/-- A sheet differs from its opposite sheet in the double cover. -/
private theorem otherSheet_different (sheet : Fin 2) :
    sheet ≠ BranchCutLifts.otherSheet sheet :=
  (by decide +kernel : ∀ sheet : Fin 2, sheet ≠ BranchCutLifts.otherSheet sheet) sheet

/-- The actual single-differential reading parent on the retained lifted mesh. -/
@[reducible] def AreaSample :=
  SourceChartComparison.SingleReadings (owner := SourceChartComparison.ownerFromMesh lifted.mesh) domains differential

/-- The paid common stem stage also pays its retained opposite-sheet area request. -/
theorem OppositeStage (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) (later : request.index
      ≤ sample.stage) :
    request.opposite.index ≤ sample.stage :=
  (Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)

/-- The actual opposite-sheet source comparison on the retained request and sample. -/
@[reducible] def OppositePart (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) (later : request.index
      ≤ sample.stage) :=
  AreaRequest.Realization request.opposite sample.readings (OppositeStage request sample later) sheet
    (BranchCutLifts.otherSheet sheet) (by exact otherSheet_different sheet)

/-- The first source/chart realization reusing the source observation acquired by the opposite-sheet comparison. -/
@[reducible] def FirstPart (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) {later : request.index
      ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.outward sample opposite.leftSources

/-- The second source/chart realization reusing the other acquired source observation. -/
@[reducible] def SecondPart (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) {later : request.index
      ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.other sample opposite.rightSources

/-- The cached stem residual equals the difference of the two retained chart areas. -/
@[reducible] def ResidualIdentity {request : StemAreaRequest bank fixed branch sheet target}
    {sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)} {later : request.index
      ≤ sample.stage}
    {opposite : OppositePart request sample later}
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (residual : Data.Gaussian.Basic.Canonical) : Prop := residual = first.chartArea - second.chartArea

/-- The cached stem bound combines the two source/chart errors with the intervening opposite-sheet error. -/
@[reducible] def BoundIdentity {request : StemAreaRequest bank fixed branch sheet target}
    {sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)} {later : request.index
      ≤ sample.stage}
    (opposite : OppositePart request sample later)
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (bound : Fraction.Rational) : Prop := bound = 2 * (first.areaBound + 2 * (opposite.areaBound + second.areaBound))

set_option genInjectivity false in
/-- The actual stem-area realization on the retained request and reading parent.

Both chart transfers reuse the source observations acquired by the opposite-sheet comparison, and the combined cached
bound pays the requested target. -/
structure Realization (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) (later : request.index
      ≤ sample.stage) where
  /-- The retained stem request used by this realization. -/ selection : StemAreaRequest bank fixed branch sheet target
  /-- The retained selection is exactly the supplied request. -/ selection_eq : selection = request
  /-- The retained actual triangle reading parent. -/ readingParent : AreaSample (lifted := lifted) (domains := domains)
    (differential := differential)
  /-- The retained reading parent is exactly the supplied sample. -/ readingParent_eq : readingParent = sample
  /-- The actual opposite-sheet comparison retaining both source observations reused by the chart transfers. -/ opposite
    : OppositePart request sample later
  /-- The first source/chart comparison consuming the retained outward source observation. -/ first : FirstPart request
    sample opposite
  /-- The second source/chart comparison consuming the retained other-sheet source observation. -/ second : SecondPart
    request sample opposite
  /-- The cached signed discrepancy of the two retained stem chart areas. -/ residual : Data.Gaussian.Basic.Canonical
  /-- The residual cache satisfies the actual retained chart-area identity. -/ residual_eq : ResidualIdentity first
    second residual
  /-- The cached complete three-comparison stem-area bound. -/ areaBound : Fraction.Rational
  /-- The bound cache satisfies the retained three-comparison arithmetic identity. -/ areaBound_eq : BoundIdentity
    opposite first second areaBound
  /-- The actual residual squared norm is bounded by the cached area bound. -/ bounded : normSq residual ≤ areaBound
  /-- The requested target pays the complete cached three-comparison area bound. -/ budget : areaBound ≤ target

constructive_injectivity Realization

/-- Acquire the opposite-sheet source observations once and reuse both in their chart transfers, retaining the complete
paid stem-area residual. -/
def realize (request : StemAreaRequest bank fixed branch sheet target)
    (sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)) (later : request.index
      ≤ sample.stage) : Realization request sample later :=
  let opposite := AreaRequest.realize request.opposite sample.readings (OppositeStage request sample later) sheet
    (BranchCutLifts.otherSheet sheet) (by exact otherSheet_different sheet)
  have chartLater := (Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let first := SourceChartAreaRequest.realize request.outward sample opposite.leftSources
    ((Nat.Order.le_max_left _ _).trans chartLater)
  let second := SourceChartAreaRequest.realize request.other sample opposite.rightSources
    ((Nat.Order.le_max_right _ _).trans chartLater)
  let residual := first.chartArea - second.chartArea
  let areaBound := 2 * (first.areaBound + 2 * (opposite.areaBound + second.areaBound))
  have firstBound : normSq (opposite.leftSources.summary.area - first.chartArea) ≤ first.areaBound := by
    rw [← first.residual_cached]; exact first.bounded
  have middleBound : normSq (opposite.leftSources.summary.area - opposite.rightSources.summary.area) ≤
    opposite.areaBound := by
    rw [← opposite.residual_eq]; exact opposite.bounded
  have secondBound : normSq (opposite.rightSources.summary.area - second.chartArea) ≤ second.areaBound := by
    rw [← second.residual_cached]; exact second.bounded
  have bounded : normSq residual ≤ areaBound :=
    AreaComparison.stem_chain first.chartArea opposite.leftSources.summary.area
      opposite.rightSources.summary.area second.chartArea firstBound middleBound secondBound
  have budget : areaBound ≤ target := by
    have inner := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct first.budget
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct opposite.budget second.budget) (by
            decide : (0 : Fraction.Rational) ≤ 2)))
      (by decide : (0 : Fraction.Rational) ≤ 2)
    refine inner.trans_eq ?_
    rw [request.partTarget_eq]
    exact AreaComparison.stem_tenth_payment target
  ⟨request, rfl, sample, rfl, opposite, first, second, residual, rfl, areaBound, rfl, bounded, budget⟩

namespace Realization

variable {request : StemAreaRequest bank fixed branch sheet target} {sample : AreaSample (lifted := lifted) (domains :=
  domains) (differential := differential)}
  {later : request.index ≤ sample.stage}

/-- The cached residual is the difference of the two actual retained stem-word areas. -/
theorem residual_readback (result : Realization request sample later) :
    result.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh sample.values)
      (bank.stemWord branch sheet) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh sample.values) (bank.stemWord branch
        (BranchCutLifts.otherSheet sheet)) := by
  have cached : result.residual = result.first.chartArea - result.second.chartArea := result.residual_eq
  rw [cached, result.first.chart_readback, result.second.chart_readback,
    request.paired.sources_project sheet,
    request.paired.sources_project (BranchCutLifts.otherSheet sheet)]
  rfl

/-- The requested target bounds the squared norm of the cached stem residual. -/
theorem pay (result : Realization request sample later) : normSq result.residual ≤ target :=
  result.bounded.trans result.budget

end Realization

namespace Realization

/-- The cached stem residual equals the sum of the actual outward and return word areas. -/
theorem return_readback {request : StemAreaRequest bank fixed branch sheet target}
    {sample : AreaSample (lifted := lifted) (domains := domains) (differential := differential)} {later : request.index
      ≤ sample.stage}
    (result : Realization request sample later) :
    result.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh sample.values)
      (bank.stemWord branch sheet) +
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh sample.values) (bank.returnWord branch
        sheet) := by
  rw [bank.returnWord_reverse, RetracingWords.wordArea_reverse _ (CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
    sample.values)]
  exact result.residual_readback

end Realization

/-- At a paid stage, the difference of the two actual stem-word areas has squared norm at most the requested target. -/
theorem accurate (request : StemAreaRequest bank fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) :
    normSq (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
      branch sheet) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord branch
        (BranchCutLifts.otherSheet sheet))) ≤ target := by
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh lifted.mesh) readings
  let result := realize request sample later
  have paid := result.pay
  rw [result.residual_readback] at paid
  exact paid

/-- This is precisely the first defect in `stemError_bound`, for the actual return word and the valuation consumed by
the corrected identity. -/
theorem return_area_accurate (request : StemAreaRequest bank fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) :
    normSq (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.stemWord
      branch sheet) +
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) (bank.returnWord branch
        sheet)) ≤ target := by
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh lifted.mesh) readings
  let result := realize request sample later
  have paid := result.pay
  rw [result.return_readback] at paid
  exact paid

end StemAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAreaRequests
