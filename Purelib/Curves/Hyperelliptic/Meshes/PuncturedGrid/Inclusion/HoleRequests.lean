module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Paths.PreparedPathWinding

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.AreaComparison
import Purelib.Polynomial.Dense.Basic
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
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Compare an original enclosing-cell lap with its full two-sheet word on
the enlarged mesh. Unlike a current physical hole, this interior contour
needs both source-to-canonical chart-area comparisons. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
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
open Purelib.Riemann.Paths.PreparedPathWinding
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_append)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation orderedRoute
  orderedRoute_value)
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

/-- The original enclosing branch-cell boundary resplit on the enlarged grid. -/
@[expose] def boundary (branch : BranchIsolation.Data.Index branches) :=
  included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))

/-- This is one actual two-lap walk: the first circuit changes the sheet before the second begins. It is not a
concatenation of unrelated lifts. -/
theorem resplit_hole_double_indexed (branch : BranchIsolation.Data.Index branches) :
    let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
      branch))
    current.edges.indexedEdges current.vertices (walk.append walk) 0 =
      current.edges.indexedEdges current.vertices walk 0 ++ current.edges.indexedEdges current.vertices walk 1 := by
  intro walk
  have winding : ClearPath.rawWinding (bank.rows.get branch).boundary.path = 4 := by
    rw [(bank.rows.get branch).boundary_eq, CellBoundary.Cell.boundaryWalk_winding]
    exact BranchCellWinding.selected_winding_four base.bank.toBranchCellBank branch
  have changed := RootEdgeBank.target_odd current.edges walk
    (included.vertex ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))) 0
    (((included.resplit_winding _ _).trans winding).trans (by decide)) 0
  rw [current.edges.indexedEdges_append, changed]
  rfl

variable {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
  next.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- The squared resplit boundary edge count times the retained primitive magnitude bound. -/
@[expose] def magnitude (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch :
  BranchIsolation.Data.Index branches) : Fraction.Rational :=
  ((boundary bank included branch).edgeCount : Fraction.Rational) ^ 2 * (4 * fixed.bound)

/-- The retained resplit enclosing-boundary magnitude bound is nonnegative. -/
theorem magnitude_nonnegative (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch :
  BranchIsolation.Data.Index branches) :
    0 ≤ magnitude bank included fixed branch :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

set_option genInjectivity false in
/-- A paid comparison of either original enclosing-cell lap with its actual two-sheet contour on the enlarged grid.

The same paired placement carries opposite-sheet, both source/chart and increment-cancellation requests; the retained
magnitude pays the lap-total cross term. -/
structure IncludedHoleRequest (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) (target : Fraction.Rational) where
  /-- The requested total hole error is strictly positive. -/ positive : 0 < target
  /-- The cached magnitude bound for the actual resplit enclosing boundary. -/ magnitude : Fraction.Rational
  /-- The cached magnitude reads the actual resplit enclosing boundary. -/ magnitude_eq : magnitude =
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests.magnitude bank included fixed branch
  /-- The retained allowance for cancellation of the two sheet increments. -/ totalTarget : Fraction.Rational
  /-- The increment allowance is the weighted share of one quarter of the target. -/ totalTarget_eq : totalTarget =
    Weighted.allowance (target / 4) (4 * magnitude)
  /-- The actual paired source placement on the resplit enclosing boundary. -/ paired : WalkOccurrences.PairedWalk
    current.mesh (boundary bank included branch)
  /-- The opposite-sheet source-area request on that exact paired boundary. -/ opposite : AreaRequest fixed paired
    (target / 4 / 10)
  /-- The source/chart transfer for the retained sheet-zero occurrences. -/ zero : SourceChartAreaRequest fixed
    (paired.sources 0) (target / 4 / 10)
  /-- The source/chart transfer for the retained sheet-one occurrences. -/ one : SourceChartAreaRequest fixed
    (paired.sources 1) (target / 4 / 10)
  /-- The increment-cancellation request on the same paired enclosing boundary. -/ total : PairedWalk.IncrementRequest
    paired domains differential 0 totalTarget
  /-- The cached common stage paying every retained boundary comparison request. -/ index : Nat
  /-- The stage is exactly the nested maximum of the three area requests and increment request. -/ index_eq : index =
    max opposite.index (max zero.index (max one.index total.index))

constructive_injectivity IncludedHoleRequest

namespace IncludedHoleRequest

variable {bank included} {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains differential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {target :
    Purelib.Data.Rat.Fraction.Rational}

/-- Prepare one paired resplit enclosing boundary and retain every area and increment request with its paid cross-term
allowance. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion
  base.bank.grid next.bank.grid)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (branch : BranchIsolation.Data.Index branches)
    (target : Fraction.Rational) (positive : 0 < target) : IncludedHoleRequest bank included fixed branch target :=
  let magnitude := Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests.magnitude bank included fixed branch
  let totalTarget := Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have partPositive : 0 < target / 4 / 10 := Fraction.Order.Field.div_pos_direct quarterPositive (by decide)
  let paired := PairedWalk.build current.mesh (boundary bank included branch)
  let opposite := AreaRequest.build fixed paired _ partPositive
  let zero := SourceChartAreaRequest.build fixed (paired.sources 0) (SignedSourceChartRequests.paired_sources_nonloop
    paired 0) _ partPositive
  let one := SourceChartAreaRequest.build fixed (paired.sources 1) (SignedSourceChartRequests.paired_sources_nonloop
    paired 1) _ partPositive
  let total := IncrementRequest.build paired domains differential 0 totalTarget
    (Weighted.allowance_positive quarterPositive
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (magnitude_nonnegative bank included fixed branch)))
  ⟨positive, magnitude, rfl, totalTarget, rfl, paired, opposite, zero, one, total,
    max opposite.index (max zero.index (max one.index total.index)), rfl⟩

/-- The actual single-differential reading parent on the enlarged mesh. -/
@[expose, reducible] def AreaSample :=
  SourceChartComparison.SingleReadings (owner := SourceChartComparison.ownerFromMesh current.mesh) domains differential

/-- The paid common hole stage also pays its retained opposite-sheet area request. -/
theorem OppositeStage (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) :
    request.opposite.index ≤ sample.stage :=
  (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)

/-- The actual opposite-sheet source comparison on the retained request and sample. -/
@[expose, reducible] def OppositePart (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) :=
  AreaRequest.Realization request.opposite sample.readings (OppositeStage request sample later) 0 1 (by
      decide : (0 : Fin 2) ≠ 1)

/-- The first source/chart realization reusing the source observation acquired by the opposite-sheet comparison. -/
@[expose, reducible] def FirstPart (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.zero sample opposite.leftSources

/-- The second source/chart realization reusing the other acquired source observation. -/
@[expose, reducible] def SecondPart (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later) :=
  SourceChartAreaRequest.Realization request.one sample opposite.rightSources

/-- The cached hole residual equals the difference of the two retained chart areas. -/
@[expose, reducible] def ResidualIdentity {request : IncludedHoleRequest bank included fixed branch target}
    {sample : AreaSample (current := current) (domains := domains) (differential := differential)} {later :
      request.index ≤ sample.stage}
    {opposite : OppositePart request sample later}
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (residual : Data.Gaussian.Basic.Canonical) : Prop := residual = first.chartArea - second.chartArea

/-- The cached hole bound combines the two source/chart errors with the intervening opposite-sheet error. -/
@[expose, reducible] def BoundIdentity {request : IncludedHoleRequest bank included fixed branch target}
    {sample : AreaSample (current := current) (domains := domains) (differential := differential)} {later :
      request.index ≤ sample.stage}
    (opposite : OppositePart request sample later)
    (first : FirstPart request sample opposite) (second : SecondPart request sample opposite)
    (bound : Fraction.Rational) : Prop := bound = 2 * (first.areaBound + 2 * (opposite.areaBound + second.areaBound))

set_option genInjectivity false in
/-- The acquired two-sheet hole-area comparison retaining its exact request and reading parent.

Both chart transfers reuse the source observations acquired by the opposite-sheet comparison, and the cached residual is
paid by one quarter of the target. -/
structure AreaRealization (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) where
  /-- The retained hole request used by this realization. -/ selection : IncludedHoleRequest bank included fixed branch
    target
  /-- The retained selection is exactly the supplied request. -/ selection_eq : selection = request
  /-- The retained actual triangle reading parent. -/ readingParent : AreaSample (current := current) (domains :=
    domains) (differential := differential)
  /-- The retained reading parent is exactly the supplied sample. -/ readingParent_eq : readingParent = sample
  /-- The actual opposite-sheet comparison retaining both source observations reused by the chart transfers. -/ opposite
    : OppositePart request sample later
  /-- The first source/chart comparison consuming the retained sheet-zero source observation. -/ first : FirstPart
    request sample opposite
  /-- The second source/chart comparison consuming the retained sheet-one source observation. -/ second : SecondPart
    request sample opposite
  /-- The cached signed discrepancy of the two retained hole chart areas. -/ residual : Data.Gaussian.Basic.Canonical
  /-- The residual cache satisfies the actual retained chart-area identity. -/ residual_eq : ResidualIdentity first
    second residual
  /-- The cached complete three-comparison hole-area bound. -/ areaBound : Fraction.Rational
  /-- The bound cache satisfies the retained three-comparison arithmetic identity. -/ areaBound_eq : BoundIdentity
    opposite first second areaBound
  /-- The actual residual squared norm is bounded by the cached area bound. -/ bounded : normSq residual ≤ areaBound
  /-- The complete retained area bound is paid by one quarter of the target. -/ budget : areaBound ≤ target / 4

constructive_injectivity AreaRealization

/-- Acquire the paired boundary observations once and reuse both in their chart transfers, retaining the complete paid
hole-area residual. -/
@[expose] def realizeArea (request : IncludedHoleRequest bank included fixed branch target)
    (sample : AreaSample (current := current) (domains := domains) (differential := differential)) (later :
      request.index ≤ sample.stage) : AreaRealization request sample later :=
  let opposite := AreaRequest.realize request.opposite sample.readings (OppositeStage request sample later) 0 1 (by
    decide : (0 : Fin 2) ≠ 1)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let first := SourceChartAreaRequest.realize request.zero sample opposite.leftSources
    ((Data.Nat.Order.le_max_left _ _).trans chartLater)
  let second := SourceChartAreaRequest.realize request.one sample opposite.rightSources
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

variable {request : IncludedHoleRequest bank included fixed branch target} {sample : AreaSample (current := current)
  (domains := domains) (differential := differential)}
  {later : request.index ≤ sample.stage}

/-- The cached residual is the difference of the actual resplit enclosing-boundary areas on sheets zero and one. -/
theorem residual_readback (result : AreaRealization request sample later) :
    result.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh sample.values)
      (current.edges.indexedEdges current.vertices (boundary bank included branch) 0) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh sample.values) (current.edges.indexedEdges
        current.vertices (boundary bank included branch) 1) := by
  have cached : result.residual = result.first.chartArea - result.second.chartArea := result.residual_eq
  rw [cached, result.first.chart_readback, result.second.chart_readback,
    request.paired.sources_project 0, request.paired.sources_project 1]

/-- One quarter of the original target bounds the actual retained area residual. -/
theorem pay (result : AreaRealization request sample later) : normSq result.residual ≤ target / 4 :=
  result.bounded.trans result.budget

end AreaRealization

/-- At a paid stage, the actual sheet-zero enclosing-boundary word value obeys the retained magnitude bound. -/
private theorem magnitude_bound (request : IncludedHoleRequest bank included fixed branch target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : fixed.index ≤ stage) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices (boundary bank included branch) 0)) ≤ request.magnitude := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh current.mesh) fixed later readings
  let observation := WordObservations.realize retainedMagnitude (current.edges.indexedEdges current.vertices (boundary
    bank included branch) 0)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback, WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation
    current.mesh readings.values) (current.edges.indexedEdges current.vertices (boundary bank included branch) 0)) ≤
    ((current.edges.indexedEdges current.vertices (boundary bank included branch) 0).length : Fraction.Rational) ^ 2 *
      (4 * fixed.bound) at cached
  rw [current.edges.indexedEdges_length] at cached
  rw [request.magnitude_eq, Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests.magnitude]
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using cached

/-- Twice either actual lap approximates the full two-sheet word, including the cross term of its lap totals. This does
not assert that its area is zero. -/
theorem lap_accurate (request : IncludedHoleRequest bank included fixed branch target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : request.index ≤ stage) (sheet : Fin 2) :
    let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
    let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem (base.bank.cell_mem
      branch))
    let lap := current.edges.indexedEdges current.vertices walk sheet
    normSq (RetracingWords.wordArea value lap + RetracingWords.wordArea value lap -
      RetracingWords.wordArea value (current.edges.indexedEdges current.vertices walk 0 ++ current.edges.indexedEdges
        current.vertices walk 1)) ≤ target := by
  intro value walk lap
  have oppositeLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans (request.opposite.index_eq ▸ oppositeLater)
  have totalLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
    ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)))
  have total := request.total.accurate readings totalLater
  have magnitude := request.magnitude_bound readings fixedLater
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  let zero := current.edges.indexedEdges current.vertices walk 0
  let one := current.edges.indexedEdges current.vertices walk 1
  have cross : normSq (BoundaryRibbon.area (SewingRetraction.wordValue value zero) (SewingRetraction.wordValue value
    one)) ≤ target / 4 := by
    rw [show BoundaryRibbon.area (SewingRetraction.wordValue value zero) (SewingRetraction.wordValue value one) =
      BoundaryRibbon.area (SewingRetraction.wordValue value zero) (SewingRetraction.wordValue value zero +
        SewingRetraction.wordValue value one) by
        rw [IncrementArea.area_add_right, IncrementArea.area_self, Data.Gaussian.Basic.zero_add]]
    have nonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸ magnitude_nonnegative bank included fixed branch
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct (oldBound magnitude) total
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) nonnegative
    have estimate := (BoundaryRibbon.area_bound (SewingRetraction.wordValue value zero) (SewingRetraction.wordValue
      value zero + SewingRetraction.wordValue value one)).trans
      ((by ring1 : 4 * Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value zero) *
        Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value zero + SewingRetraction.wordValue
        value one) =
        4 * (Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value zero) *
          Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value zero + SewingRetraction.wordValue
          value one))).le.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)))
    apply canonicalBound
    apply estimate.trans
    rw [show 4 * (request.magnitude * request.totalTarget) = (4 * request.magnitude) * request.totalTarget by ring1,
      request.totalTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
  have finish (a b : Data.Gaussian.Basic.Canonical) (first : normSq a ≤ target / 4) (last : normSq b ≤ target / 4) :
      normSq (a - b) ≤ target :=
    canonicalBound (((Data.Gaussian.Norm.Bounds.normSq_sub_le_two a b).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (oldBound
      first) (oldBound last)) (by decide))).trans_eq
      ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  let sample := SingleReadings.ofReadings (owner := SourceChartComparison.ownerFromMesh current.mesh) readings
  let areaComparison := request.realizeArea sample later
  have areaPaid := areaComparison.pay
  rw [areaComparison.residual_readback] at areaPaid
  have areaError := areaPaid
  have cases : sheet = 0 ∨ sheet = 1 := by
    have bound := sheet.isLt
    by_cases zero : sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change sheet.val = 1; omega))
  change normSq (RetracingWords.wordArea value (current.edges.indexedEdges current.vertices walk sheet) +
    RetracingWords.wordArea value (current.edges.indexedEdges current.vertices walk sheet) - RetracingWords.wordArea
      value (zero ++ one)) ≤ target
  rw [RetracingWords.wordArea_append]
  rcases cases with rfl | rfl
  · have equal (a b c : Data.Gaussian.Basic.Canonical) : a + a - (a + b + c) = (a - b) - c := by ring1
    exact (congrArg normSq (equal (RetracingWords.wordArea value zero) (RetracingWords.wordArea value one) _)).trans_le
      (finish _ _ areaError cross)
  · have reversed : normSq (RetracingWords.wordArea value one - RetracingWords.wordArea value zero) ≤ target / 4 := by
      rw [show RetracingWords.wordArea value one - RetracingWords.wordArea value zero = -(RetracingWords.wordArea value
        zero - RetracingWords.wordArea value one) by ring1, Data.Gaussian.Basic.Canonical.normSq_neg]
      exact areaError
    have equal (a b c : Data.Gaussian.Basic.Canonical) : b + b - (a + b + c) = (b - a) - c := by ring1
    exact (congrArg normSq (equal (RetracingWords.wordArea value zero) (RetracingWords.wordArea value one) _)).trans_le
      (finish _ _ reversed cross)

end IncludedHoleRequest

/-- Pay the original excursion's stems and the single-lap/two-lap area comparison together. The full enclosing-cell
double word is retained. -/
theorem included_branch_area_accurate (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (branch : BranchIsolation.Data.Index branches) (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 < target)
      :
    let part := target / 10
    let partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide)
    let stems := IncludedStemRequest.build bank included fixed branch sheet part partPositive
    let holes := IncludedHoleRequest.build bank included fixed branch part partPositive
    ∀ stage (shared : PrimitiveData.FacePrimitiveBank differential stage domains) (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh),
      max stems.index holes.index ≤ stage →
      let value := CanonicalEdgeValues.edgeValuation current.mesh readings.values
      let walk := included.resplit (bank.rows.get branch).boundary ((base.bank.cell branch).anchor_mem
        (base.bank.cell_mem branch))
      let loop := current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get branch).reference.walk (FramedBranchCellBank.baseMember base.bank)) sheet
      normSq (RetracingWords.wordArea value loop + RetracingWords.wordArea value loop -
        RetracingWords.wordArea value (current.edges.indexedEdges current.vertices (walk.append walk) 0)) ≤ target := by
  intro part partPositive stems holes stage shared readings later value walk loop
  rw [resplit_hole_double_indexed bank included branch]
  let arrival := RootEdgeBank.target current.edges (included.resplit (bank.rows.get branch).stem
    ((base.bank.cell branch).anchor_mem (base.bank.cell_mem branch))) sheet
  let lap := current.edges.indexedEdges current.vertices walk arrival
  let double := current.edges.indexedEdges current.vertices walk 0 ++ current.edges.indexedEdges current.vertices walk 1
  have stemBound := stems.loop_area_accurate readings ((Data.Nat.Order.le_max_left _ _).trans later)
  have holeBound := holes.lap_accurate readings ((Data.Nat.Order.le_max_right _ _).trans later) arrival
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have twice : normSq ((RetracingWords.wordArea value loop - RetracingWords.wordArea value lap) +
      (RetracingWords.wordArea value loop - RetracingWords.wordArea value lap)) ≤ 4 * part :=
    canonicalBound (((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (oldBound
        stemBound) (oldBound stemBound)) (by decide))).trans_eq (by ring1))
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
      ((RetracingWords.wordArea value loop - RetracingWords.wordArea value lap) + (RetracingWords.wordArea value loop -
        RetracingWords.wordArea value lap))
      (RetracingWords.wordArea value lap + RetracingWords.wordArea value lap - RetracingWords.wordArea value
        double)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (oldBound
      twice) (oldBound holeBound)) (by decide))
  have equal : (RetracingWords.wordArea value loop - RetracingWords.wordArea value lap) + (RetracingWords.wordArea value
    loop - RetracingWords.wordArea value lap) +
      (RetracingWords.wordArea value lap + RetracingWords.wordArea value lap - RetracingWords.wordArea value double) =
      RetracingWords.wordArea value loop + RetracingWords.wordArea value loop - RetracingWords.wordArea value double :=
        by ring1
  rw [equal] at estimate
  exact canonicalBound (estimate.trans_eq ((by ring1 : 2 * (4 * part + part) = target / 10 * 10).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
