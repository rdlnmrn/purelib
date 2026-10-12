module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CornerJumpBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

public section

/-! One face-and-sheet request bank pays actual crossing corner replacements. -/
section

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared
  VerticalPrepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared (Sample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared (Sample)

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests

set_option genInjectivity false in
/-- Scalar grid requests are shared by every crossing touching a face and sheet. -/
structure CornerGrids (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (tolerance : Fraction.Rational)
  where
  /-- The retained scalar grid request bank for every original sheet and regular-face position. -/ entries :
    Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector (fun position : Fin
    faces.regulars.length =>
    EnergyPreflight.Request ((fixed sheet).get position).get tolerance))
  /-- The cached common stage paying all original corner-grid requests. -/ index : Nat
  /-- Every retained face-and-sheet grid request is paid by the common stage. -/ index_ge : ∀ sheet position,
    ((entries.get sheet).get position).index ≤ index

constructive_injectivity CornerGrids

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.CornerGrids

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.CornerGrids in
/-- Prepare each original face-and-sheet grid request once and cache the maximum stage of the complete bank. -/
@[expose] def build (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (tolerance : Fraction.Rational)
  (positive : 0 < tolerance) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.CornerGrids fixed tolerance := by
  let entries := DependentVector.ofFn (fun sheet : Fin 2 => DependentVector.ofFn
    (fun position : Fin faces.regulars.length => EnergyPreflight.Request.build
      ((fixed sheet).get position).get tolerance positive))
  let index := entries.maximum (fun _ row => row.maximum (fun _ entry => entry.index))
  refine ⟨entries, index, ?_⟩
  intro sheet position
  exact ((entries.get sheet).get_le_maximum (fun _ entry => entry.index) position).trans
    (entries.get_le_maximum (fun _ row => row.maximum (fun _ entry => entry.index)) sheet)

/-- The retained scalar grid request for the selected original sheet, face and differential basis index. -/
@[expose] def row (grids : CrossingCornerRequests.CornerGrids fixed tolerance)
  (sheet : Fin 2) (position : Fin faces.regulars.length) (basis : Fin genus) :=
  (((grids.entries.get sheet).get position).rows.get basis)

/-- Every retained basis row is paid by the common corner-grid stage. -/
theorem row_index_le (grids : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.CornerGrids fixed
  tolerance) (sheet : Fin 2) (position : Fin faces.regulars.length) (basis : Fin genus) :
    (grids.row sheet position basis).index ≤ grids.index :=
  (((grids.entries.get sheet).get position).index_eq basis).trans_le (grids.index_ge sheet position)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.CornerGrids

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome

/-- The actual normalized corner determinant jump for a matched horizontal crossing, with zero for certified separation.
-/
@[expose] def cornerJump
    (outcome : CrossingBank.HorizontalOutcome request first nextPosition)
    (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) : Data.Gaussian.Basic.Canonical :=
  match outcome with
  | .matched joined =>
      Numerics.cornerJump
        cache i j firstPosition nextPosition firstSheet joined.crossing.next.sheet 3 2
  | .separated _ => 0

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.HorizontalPrepared.Sample

/-- The actual horizontal sample endpoint jump is close to the retained corner jump once the original magnitude and
shared grid requests are paid. -/
theorem
  corner_jump_bound
    {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome}
    {cache : RegularMeshes.Numerics domains stage}
    (sample : HorizontalPrepared.Sample prepared cache.normalize)
    (firstMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (secondMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {cornerTolerance : Fraction.Rational} (grids :
      CrossingCornerRequests.CornerGrids fixed cornerTolerance) (gridLater :
      grids.index ≤ stage)
    (positive : 0 < cornerTolerance) (small : 16 * cornerTolerance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (HorizontalPrepared.Sample.endpointJump sample -
      outcome.cornerJump cache.normalize i j) ≤
      512 * (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * cornerTolerance := by
  cases prepared with
  | @matched joined allocated =>
      rcases sample with ⟨left, right⟩
      dsimp only [HorizontalPrepared.Sample.endpointJump,
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome.cornerJump]
      have bound := HorizontalCrossing.corner_jump_bound
        joined allocated.trace firstMagnitude secondMagnitude firstLater secondLater positive small
        (grids.row firstSheet firstPosition i) ((grids.row_index_le firstSheet firstPosition i).trans gridLater)
        (grids.row joined.crossing.next.sheet nextPosition i) ((grids.row_index_le joined.crossing.next.sheet
          nextPosition i).trans gridLater)
        (grids.row firstSheet firstPosition j) ((grids.row_index_le firstSheet firstPosition j).trans gridLater)
        (grids.row joined.crossing.next.sheet nextPosition j) ((grids.row_index_le joined.crossing.next.sheet
          nextPosition j).trans gridLater)
        cache left right
      exact bound
  | separated obstruction =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ _
      rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg firstMagnitude.nonnegative
          secondMagnitude.nonnegative)) (by decide))) positive.le

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.HorizontalPrepared.Sample

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome

/-- The actual normalized corner determinant jump for a matched vertical crossing, with zero for certified separation.
-/
@[expose] def cornerJump
    (outcome : CrossingBank.VerticalOutcome request first nextPosition)
    (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) : Data.Gaussian.Basic.Canonical :=
  match outcome with
  | .matched joined =>
      Numerics.cornerJump
        cache i j firstPosition nextPosition firstSheet joined.crossing.next.sheet 1 2
  | .separated _ => 0

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.VerticalPrepared.Sample

/-- The actual vertical sample endpoint jump is close to the retained corner jump once the original magnitude and shared
grid requests are paid. -/
theorem
  corner_jump_bound
    {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome}
    {cache : RegularMeshes.Numerics domains stage}
    (sample : VerticalPrepared.Sample prepared cache.normalize)
    (firstMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (secondMagnitude : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (firstLater : firstMagnitude.index ≤ stage) (secondLater : secondMagnitude.index ≤ stage)
    {cornerTolerance : Fraction.Rational} (grids :
      CrossingCornerRequests.CornerGrids fixed cornerTolerance) (gridLater :
      grids.index ≤ stage)
    (positive : 0 < cornerTolerance) (small : 16 * cornerTolerance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (VerticalPrepared.Sample.endpointJump sample -
      outcome.cornerJump cache.normalize i j) ≤
      512 * (4 * (firstMagnitude.bound + secondMagnitude.bound) + 1) * cornerTolerance := by
  cases prepared with
  | @matched joined allocated =>
      rcases sample with ⟨left, right⟩
      dsimp only [VerticalPrepared.Sample.endpointJump,
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome.cornerJump]
      have bound := VerticalCrossing.corner_jump_bound
        joined allocated.trace firstMagnitude secondMagnitude firstLater secondLater positive small
        (grids.row firstSheet firstPosition i) ((grids.row_index_le firstSheet firstPosition i).trans gridLater)
        (grids.row joined.crossing.next.sheet nextPosition i) ((grids.row_index_le joined.crossing.next.sheet
          nextPosition i).trans gridLater)
        (grids.row firstSheet firstPosition j) ((grids.row_index_le firstSheet firstPosition j).trans gridLater)
        (grids.row joined.crossing.next.sheet nextPosition j) ((grids.row_index_le joined.crossing.next.sheet
          nextPosition j).trans gridLater)
        cache left right
      exact bound
  | separated obstruction =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ _
      rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg firstMagnitude.nonnegative
          secondMagnitude.nonnegative)) (by decide))) positive.le

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerRequests.VerticalPrepared.Sample

end
