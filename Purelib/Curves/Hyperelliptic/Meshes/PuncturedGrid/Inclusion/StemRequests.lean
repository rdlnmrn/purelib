module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.AreaComparison
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! Pay both stem defects for the original branch excursion on the enlarged
mesh, using one retained paired placement and one later primitive bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (orderedRoute orderedRoute_value)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {current : LiftedPuncturedGrid next}
  (bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted)
    (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)

/-- The retained branch stem resplit along the supplied coordinate inclusion. -/
@[expose] def stem (branch : BranchIsolation.Data.Index branches) :=
  included.resplit (bank.rows.get branch).stem ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))

/-- The retained branch boundary resplit along the same coordinate inclusion. -/
@[expose] def hole (branch : BranchIsolation.Data.Index branches) :=
  included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))

variable {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
  next.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The squared stem-plus-boundary edge count times the retained primitive magnitude bound. -/
@[expose] def magnitude (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch :
  BranchIsolation.Data.Index branches) : Fraction.Rational :=
  (((stem bank included branch).append (hole bank included branch)).edgeCount : Fraction.Rational) ^ 2 * (4 *
    fixed.bound)

/-- The resplit stem and boundary magnitude bound is nonnegative. -/
theorem magnitude_nonnegative (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch :
  BranchIsolation.Data.Index branches) :
    0 ≤ magnitude bank included fixed branch :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

set_option genInjectivity false in
/-- A paid comparison between a resplit based branch excursion and its retained hole boundary.

One paired stem placement carries the opposite-sheet area, both source/chart comparisons and increment cancellation, all
paid at a common stage. -/
structure IncludedStemRequest (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The requested total stem error is strictly positive. -/ positive : 0 < target
  /-- The cached magnitude bound for the actual resplit stem and hole boundary. -/ magnitude : Fraction.Rational
  /-- The cached magnitude equals the actual resplit stem and boundary bound. -/ magnitude_eq : magnitude =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests.magnitude bank included fixed branch
  /-- The retained allowance for cancellation of the two opposite-sheet stem increments. -/ incrementTarget :
    Fraction.Rational
  /-- The increment allowance is the weighted share of one quarter of the target. -/ incrementTarget_eq :
    incrementTarget = Weighted.allowance (target / 4) (4 * magnitude)
  /-- The actual paired placement of the resplit stem on the enlarged mesh. -/ paired : WalkOccurrences.PairedWalk
    current.mesh (stem bank included branch)
  /-- The original opposite-sheet source-area request on that retained paired placement. -/ opposite : AreaRequest fixed
    paired (target / 4 / 10)
  /-- The source/chart area request for the retained outward stem sheet. -/ outward : SourceChartAreaRequest fixed
    (paired.sources sheet) (target / 4 / 10)
  /-- The source/chart area request for the other retained stem sheet. -/ other : SourceChartAreaRequest fixed
    (paired.sources (BranchCutLifts.otherSheet sheet)) (target / 4 / 10)
  /-- The increment-cancellation request on the same paired stem and original differential. -/ increment :
    PairedWalk.IncrementRequest paired domains differential sheet incrementTarget
  /-- The cached common stage paying all four retained request families. -/ index : Nat
  /-- The common stage is the nested maximum of the retained area and increment request stages. -/ index_eq : index =
    max opposite.index (max outward.index (max other.index increment.index))

constructive_injectivity IncludedStemRequest

namespace IncludedStemRequest

variable {bank included} {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains differential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2} {target :
    Purelib.Data.Rat.Fraction.Rational}

/-- Prepare one paired resplit stem and all its area and increment requests using the retained magnitude reference. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion
  base.bank.grid next.bank.grid)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch : BranchIsolation.Data.Index branches)
    (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 < target) : IncludedStemRequest bank included fixed
      branch sheet target :=
  let magnitude := Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests.magnitude bank included fixed branch
  let incrementTarget := Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have partPositive : 0 < target / 4 / 10 := Fraction.Order.Field.div_pos_direct quarterPositive (by decide)
  let paired := PairedWalk.build current.mesh (stem bank included branch)
  let opposite := AreaRequest.build fixed paired _ partPositive
  let outward := SourceChartAreaRequest.build fixed (paired.sources sheet)
    (SignedSourceChartRequests.paired_sources_nonloop paired sheet) _ partPositive
  let other := SourceChartAreaRequest.build fixed (paired.sources (BranchCutLifts.otherSheet sheet))
    (SignedSourceChartRequests.paired_sources_nonloop paired _) _ partPositive
  let increment := IncrementRequest.build paired domains differential sheet incrementTarget
    (Weighted.allowance_positive quarterPositive
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (magnitude_nonnegative bank included fixed branch)))
  ⟨positive, magnitude, rfl, incrementTarget, rfl, paired, opposite, outward, other, increment,
    max opposite.index (max outward.index (max other.index increment.index)), rfl⟩

/-- A sheet differs from its opposite sheet in the double cover. -/
private theorem otherSheet_different (sheet : Fin 2) :
    sheet ≠ BranchCutLifts.otherSheet sheet :=
  (by decide +kernel : ∀ sheet : Fin 2, sheet ≠ BranchCutLifts.otherSheet sheet) sheet

/-- The actual single-differential reading parent on the enlarged mesh. -/
@[expose, reducible] def AreaSample :=
  SourceChartComparison.SingleReadings (owner := SourceChartComparison.ownerFromMesh current.mesh) domains differential

/-- The paid common stem stage also pays its retained opposite-sheet area request. -/
theorem OppositeStage (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) :
    request.opposite.index ≤ sample.stage :=
  (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)

/-- The actual opposite-sheet source comparison on the retained request and sample. -/
@[expose, reducible] def OppositePart (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) :=
  AreaRequest.Realization request.opposite sample.readings (OppositeStage request sample later) sheet
    (BranchCutLifts.otherSheet sheet) (by exact otherSheet_different sheet)

/-- The first source/chart realization reusing the source observation acquired by the opposite-sheet comparison. -/
@[expose, reducible] def FirstPart (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.outward sample opposite.leftSources

/-- The second source/chart realization reusing the other acquired source observation. -/
@[expose, reducible] def SecondPart (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.other sample opposite.rightSources

/-- The cached stem residual equals the difference of the two retained chart areas. -/
@[expose, reducible] def ResidualIdentity {request : IncludedStemRequest bank included fixed branch sheet target}
    {sample : AreaSample (current := current) (domains := domains) (differential := differential)} {later :
      request.index ≤ sample.stage}
    {opposite : OppositePart request sample later}
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (residual : Data.Gaussian.Basic.Canonical) : Prop := residual = first.chartArea - second.chartArea

/-- The cached stem bound combines the two source/chart errors with the intervening opposite-sheet error. -/
@[expose, reducible] def BoundIdentity {request : IncludedStemRequest bank included fixed branch sheet target}
    {sample : AreaSample (current := current) (domains := domains) (differential := differential)} {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later)
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (bound : Fraction.Rational) : Prop := bound = 2 * (first.areaBound + 2 * (opposite.areaBound + second.areaBound))

set_option genInjectivity false in
/-- The realized stem-area comparison retaining its exact request and reading parent.

Both source/chart realizations reuse the opposite-sheet source observations; the cached chart residual and bound are
paid by one quarter of the target. -/
structure AreaRealization (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) where
  /-- The retained stem request used by this realization. -/ selection : IncludedStemRequest bank included fixed branch
    sheet target
  /-- The retained selection is exactly the supplied request. -/ selection_eq : selection = request
  /-- The retained actual triangle reading parent. -/ readingParent : AreaSample (current := current) (domains :=
    domains) (differential := differential)
  /-- The retained reading parent is exactly the supplied sample. -/ readingParent_eq : readingParent = sample
  /-- The actual opposite-sheet area comparison with both acquired source observations retained. -/ opposite :
    OppositePart request sample later
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
  /-- The complete retained area bound is paid by one quarter of the target. -/ budget : areaBound ≤ target / 4

constructive_injectivity AreaRealization

/-- Acquire the opposite-sheet source observations once, reuse them in both source/chart comparisons and cache the paid
chart-area residual. -/
@[expose] def realizeArea (request : IncludedStemRequest bank included fixed branch sheet target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) : AreaRealization request sample later :=
  let opposite := AreaRequest.realize request.opposite sample.readings (OppositeStage request sample later) sheet
    (BranchCutLifts.otherSheet sheet) (by exact otherSheet_different sheet)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let first := SourceChartAreaRequest.realize request.outward sample opposite.leftSources
    ((Data.Nat.Order.le_max_left _ _).trans chartLater)
  let second := SourceChartAreaRequest.realize request.other sample opposite.rightSources
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans chartLater))
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
  have budget : areaBound ≤ target / 4 := by
    have inner := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct first.budget
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct opposite.budget second.budget) (by
            decide : (0 : Fraction.Rational) ≤ 2)))
      (by decide : (0 : Fraction.Rational) ≤ 2)
    refine inner.trans_eq ?_
    exact AreaComparison.stem_tenth_payment (target / 4)
  ⟨request, rfl, sample, rfl, opposite, first, second, residual, rfl, areaBound, rfl, bounded, budget⟩

namespace AreaRealization

variable {request : IncludedStemRequest bank included fixed branch sheet target} {sample : AreaSample (current :=
  current) (domains := domains) (differential := differential)}
  {later : request.index ≤ sample.stage}

/-- The retained residual is the difference of the actual indexed resplit stem word areas on the two sheets. -/
theorem residual_readback (result : AreaRealization request sample later) :
    result.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh sample.values)
      (current.edges.indexedEdges current.vertices (stem bank included branch) sheet) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh sample.values) (current.edges.indexedEdges
        current.vertices (stem bank included branch) (BranchCutLifts.otherSheet sheet)) := by
  have cached : result.residual = result.first.chartArea - result.second.chartArea := result.residual_eq
  rw [cached, result.first.chart_readback, result.second.chart_readback,
    request.paired.sources_project sheet,
    request.paired.sources_project (BranchCutLifts.otherSheet sheet)]

/-- One quarter of the original target bounds the actual retained area residual. -/
theorem pay (result : AreaRealization request sample later) : normSq result.residual ≤ target / 4 :=
  result.bounded.trans result.budget

end AreaRealization

/-- The actual resplit stem-plus-boundary word value obeys the cached request magnitude at a paid reading stage. -/
private theorem magnitude_bound (request : IncludedStemRequest bank included fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices ((stem bank included branch).append (hole bank included branch))
        sheet)) ≤
        request.magnitude := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) fixed later readings
  let observation := WordObservations.realize retainedMagnitude (current.edges.indexedEdges current.vertices ((stem bank
    included branch).append (hole bank included branch)) sheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback, WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
    current.mesh readings.values) (current.edges.indexedEdges current.vertices ((stem bank included branch).append (hole
    bank included branch)) sheet)) ≤
    ((current.edges.indexedEdges current.vertices ((stem bank included branch).append (hole bank included branch))
      sheet).length : Fraction.Rational) ^ 2 * (4 * fixed.bound) at cached
  rw [current.edges.indexedEdges_length] at cached
  rw [request.magnitude_eq, Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests.magnitude]
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using cached
/-- At the paid common stage, the original resplit based excursion and its hole boundary differ in squared area by at
most the requested target. -/
theorem loop_area_accurate (request : IncludedStemRequest bank included fixed branch sheet target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : request.index ≤ stage) :
    normSq (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get branch).reference.walk (FramedBranchCellBank.baseMember base.bank)) sheet) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
          branch)))
        (RootEdgeBank.target current.edges (included.resplit (bank.rows.get branch).stem
          ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))) sheet))) ≤ target := by
  let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
  let outward := current.edges.indexedEdges current.vertices (stem bank included branch) sheet
  let other := current.edges.indexedEdges current.vertices (stem bank included branch) (BranchCutLifts.otherSheet sheet)
  let boundary := current.edges.indexedEdges current.vertices (hole bank included branch)
    (RootEdgeBank.target current.edges (stem bank included branch) sheet)
  have oppositeLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans (request.opposite.index_eq ▸ oppositeLater)
  have incrementLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)))
  have mag := request.magnitude_bound readings fixedLater
  rw [current.edges.indexedEdges_append, SewingRetraction.wordValue_append] at mag
  have inc := request.increment.accurate readings incrementLater
  have magNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸ magnitude_nonnegative bank included fixed branch
  have oldBound {value : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Data.Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct (oldBound mag) inc (Data.Gaussian.Norm.Basic.normSq_nonneg
    _) magNonnegative
  have weighted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have budget : 4 * request.magnitude * request.incrementTarget ≤ target / 4 := by
    rw [request.incrementTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magNonnegative)
  have cross : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (SewingRetraction.wordValue value outward +
    SewingRetraction.wordValue value boundary)
      (-(SewingRetraction.wordValue value outward + SewingRetraction.wordValue value other))) ≤ target / 4 := by
    have bound := BoundaryRibbon.area_bound (SewingRetraction.wordValue value outward + SewingRetraction.wordValue value
      boundary)
      (-(SewingRetraction.wordValue value outward + SewingRetraction.wordValue value other))
    rw [Data.Gaussian.Norm.Basic.normSq_neg] at bound
    exact bound.trans ((show 4 * Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value outward +
      SewingRetraction.wordValue value boundary) *
        Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value outward + SewingRetraction.wordValue
          value other) =
        4 * (Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value outward +
          SewingRetraction.wordValue value boundary) *
          Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value outward +
            SewingRetraction.wordValue value other)) by ring1).trans_le
      (weighted.trans ((by ring1 : 4 * (request.magnitude * request.incrementTarget) =
        4 * request.magnitude * request.incrementTarget).trans_le budget)))
  rw [bank.resplit_loop_area included current.edges current.vertices
    (fun point member => (BranchCellBank.referenceAt next.bank.toBranchCellBank point member).toLoop) branch sheet value
      (CanonicalEdgeValues.edgeValuation_reverse current.mesh readings.values)]
  change normSq ((RetracingWords.wordArea value boundary + (RetracingWords.wordArea value outward -
    RetracingWords.wordArea value other) +
    BoundaryRibbon.area (SewingRetraction.wordValue value outward + SewingRetraction.wordValue value boundary)
      (-(SewingRetraction.wordValue value outward + SewingRetraction.wordValue value other))) -
    RetracingWords.wordArea value boundary) ≤ target
  rw [show RetracingWords.wordArea value boundary + (RetracingWords.wordArea value outward - RetracingWords.wordArea
    value other) +
      BoundaryRibbon.area (SewingRetraction.wordValue value outward + SewingRetraction.wordValue value boundary)
        (-(SewingRetraction.wordValue value outward + SewingRetraction.wordValue value other)) -
      RetracingWords.wordArea value boundary = (RetracingWords.wordArea value outward - RetracingWords.wordArea value
        other) +
        BoundaryRibbon.area (SewingRetraction.wordValue value outward + SewingRetraction.wordValue value boundary)
          (-(SewingRetraction.wordValue value outward + SewingRetraction.wordValue value other)) by ring1]
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh current.mesh) readings
  let areaComparison := request.realizeArea sample later
  have areaPaid := oldBound areaComparison.pay
  rw [areaComparison.residual_readback] at areaPaid
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct areaPaid
      cross) (by decide))
  apply canonicalBound
  exact estimate.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end IncludedStemRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
