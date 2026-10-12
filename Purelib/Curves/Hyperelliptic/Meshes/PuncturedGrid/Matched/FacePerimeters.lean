module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
meta import Mathlib.Tactic.Linter.Lint

public section

/-! One perimeter cache per actual face and sheet, shared by every crossing. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.RectangularObservationAssembly
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared
  VerticalPrepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.HorizontalPrepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.VerticalPrepared

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

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

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

namespace FacePerimeters

/-- The aligned paired differential values on the actual observation cells of one retained face and sheet. -/
@[expose] def faceValues (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :=
  fun column row point => (⟨(cache.atDomain position sheet i).anchors.alignedValue
      (cache.atDomain position sheet i).offsets column row point,
    (cache.atDomain position sheet j).anchors.alignedValue
      (cache.atDomain position sheet j).offsets column row point⟩ : Stokes.PrimitivePoint)

end FacePerimeters

set_option genInjectivity false in
/-- One cached perimeter assembly per retained regular face and sheet.

Every crossing reads these same assemblies and perimeters on the supplied numerical bank. -/
structure FacePerimeters (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) where
  /-- The actual clipped observation assemblies on each original face and sheet. -/ assemblies :
    Data.Vector.DependentVector (fun position : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 => ObservationMesh.ClippedAssembly
      ((request.entries.get sheet).meshes.entries.get position)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.faceValues cache i j position sheet)))
  /-- The retained perimeters of those exact clipped assemblies. -/ perimeters : Data.Vector.DependentVector (fun
    position : Fin faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 => ((assemblies.get position).get sheet).Perimeter))

constructive_injectivity FacePerimeters

namespace FacePerimeters

/-- Build each retained face-and-sheet assembly once and cache its perimeter. -/
@[expose] def build (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) :
  FacePerimeters (request := request) cache i j := by
  let assemblies := DependentVector.ofFn (fun position : Fin faces.regulars.length =>
    DependentVector.ofFn (fun sheet : Fin 2 => ClippedAssembly.build
      ((request.entries.get sheet).meshes.entries.get position)
        (faceValues cache i j position sheet)))
  exact ⟨assemblies, DependentVector.ofFn (fun position => DependentVector.ofFn (fun sheet =>
    Perimeter.build ((assemblies.get position).get sheet)))⟩

end FacePerimeters

namespace FacePerimeters.HorizontalOutcome

/-- The cached top-to-bottom area difference for a matched crossing, or zero for certified separation. -/
@[expose] def perimeterDifference (perimeters :
  FacePerimeters (request := request) cache i j)
    (outcome : CrossingBank.HorizontalOutcome request first nextPosition) : Data.Gaussian.Basic.Canonical :=
  match outcome with
  | .matched joined => ((perimeters.perimeters.get firstPosition).get firstSheet).top -
      ((perimeters.perimeters.get nextPosition).get joined.crossing.next.sheet).bottom
  | .separated _ => 0

end FacePerimeters.HorizontalOutcome

namespace FacePerimeters.HorizontalPrepared.Sample

/-- The actual horizontal crossing sample reads the same retained face-perimeter difference. -/
theorem areaDifference_eq_cache
    {outcome : CrossingBank.HorizontalOutcome request first nextPosition}
    {prepared : CrossingRequests.HorizontalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome}
    (perimeters : FacePerimeters (request := request)
      cache i j)
    (sample : HorizontalPrepared.Sample prepared cache) :
    HorizontalPrepared.Sample.areaDifference sample =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
        outcome := by
  cases prepared with
  | matched allocated =>
      exact HorizontalPrepared.Sample.areaDifference_eq_perimeters sample
        ((perimeters.assemblies.get firstPosition).get firstSheet) ((perimeters.assemblies.get nextPosition).get _)
        ((perimeters.perimeters.get firstPosition).get firstSheet) ((perimeters.perimeters.get nextPosition).get _)
  | separated obstruction => rfl

end FacePerimeters.HorizontalPrepared.Sample

namespace FacePerimeters.VerticalOutcome

/-- The cached right-to-left area difference for a matched crossing, or zero for certified separation. -/
@[expose] def perimeterDifference (perimeters :
  FacePerimeters (request := request) cache i j)
    (outcome : CrossingBank.VerticalOutcome request first nextPosition) : Data.Gaussian.Basic.Canonical :=
  match outcome with
  | .matched joined => ((perimeters.perimeters.get firstPosition).get firstSheet).right -
      ((perimeters.perimeters.get nextPosition).get joined.crossing.next.sheet).left
  | .separated _ => 0

end FacePerimeters.VerticalOutcome

namespace FacePerimeters.VerticalPrepared.Sample

/-- The actual vertical crossing sample reads the same retained face-perimeter difference. -/
theorem areaDifference_eq_cache
    {outcome : CrossingBank.VerticalOutcome request first nextPosition}
    {prepared : CrossingRequests.VerticalPrepared (PeriodMatrix.standardDifferential i)
      (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor outcome}
    (perimeters : FacePerimeters (request := request)
      cache i j)
    (sample : VerticalPrepared.Sample prepared cache) :
    VerticalPrepared.Sample.areaDifference sample =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
        outcome := by
  cases prepared with
  | matched allocated =>
      exact VerticalPrepared.Sample.areaDifference_eq_perimeters sample
        ((perimeters.assemblies.get firstPosition).get firstSheet) ((perimeters.assemblies.get nextPosition).get _)
        ((perimeters.perimeters.get firstPosition).get firstSheet) ((perimeters.perimeters.get nextPosition).get _)
  | separated obstruction => rfl

end FacePerimeters.VerticalPrepared.Sample

section CrossingRequests
variable {retained : CrossingBank request mesh}
  {allocated : CrossingRequests
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained}
  {cache : Numerics domains stage}

open Purelib.Algebra.FiniteSum.Fin (sumFin)

namespace FacePerimeters.CrossingRequests

/-- The complete signed sum of retained crossing perimeter differences, with vertical terms positive. -/
@[expose] def pairedPerimeter (retained : CrossingBank request mesh)
  (perimeters :
  FacePerimeters (request := request) cache i j) :
  Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
      (((retained.vertical.get a).get b).get c)))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
      (((retained.horizontal.get a).get b).get c))))

end FacePerimeters.CrossingRequests

namespace CrossingSamples.CrossingRequests.Samples

/-- The actual crossing-area difference equals the signed perimeter sum from the shared cache. -/
theorem
  areaDifference_eq_pairedPerimeter
    (samples : CrossingRequests.Samples allocated cache)
    (perimeters : FacePerimeters (request := request)
      cache i j) :
    samples.areaDifference =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter retained
      perimeters := by
  unfold CrossingRequests.Samples.areaDifference
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter
  simp only
    [Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalPrepared.Sample.areaDifference_eq_cache
    perimeters,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalPrepared.Sample.areaDifference_eq_cache
      perimeters, -eq_self, -iff_self]
  rfl

end CrossingSamples.CrossingRequests.Samples

namespace CrossingTotal.CrossingRequests.TotalRequest

/-- At the paid crossing stage, the cached perimeter total minus its retained endpoint correction satisfies the
aggregate target. -/
theorem
  pairedPerimeter_bound
    {target : Fraction.Rational}
    (total : CrossingRequests.TotalRequest
      retained i j firstParent secondParent target floor)
    {samples : CrossingRequests.Samples total.allocated cache}
    (accounting : CrossingRequests.Accounting samples)
    (perimeters : FacePerimeters (request := request)
      cache i j)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.CrossingRequests.pairedPerimeter retained
      perimeters - accounting.endpoints) ≤ target := by
  rw [←
    CrossingSamples.CrossingRequests.Samples.areaDifference_eq_pairedPerimeter
    samples perimeters,
    ← accounting.area_eq]
  exact TotalRequest.accounting_bound total accounting later

end CrossingTotal.CrossingRequests.TotalRequest

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
