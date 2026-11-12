module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

@[expose] public section

/-! Retain conjugated basis-pair perimeters on every actual regular face and
sheet. All values come from the supplied shared primitive bank. -/
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (RegularFace bank)}
  {domains : FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational} {stage : Nat}

namespace ConjugateFacePerimeters

/-- The aligned basis-pair values on one actual face and sheet, conjugating the first component. -/
def conjugateFaceValues (cache : Numerics domains stage) (first second : Fin genus)
    (position : Fin faces.length) (sheet : Fin 2) :=
  fun (column row : Fin (((domains.get position).domain sheet).steps + 1)) (point : Gaussian) =>
    ConjugateIncrementComparison.conjugateFirst
      ⟨(cache.atDomain position sheet first).anchors.alignedValue
          (cache.atDomain position sheet first).offsets column row point,
        (cache.atDomain position sheet second).anchors.alignedValue
          (cache.atDomain position sheet second).offsets column row point⟩

end ConjugateFacePerimeters

set_option genInjectivity false in
/-- The complete retained conjugate assemblies and their actual face perimeters.

Both basis components come from the same supplied primitive cache, and the dependent vectors preserve every face and
sheet owner. -/
structure ConjugateFacePerimeters (request : TwoSheetRequest coarse fixed target)
    (cache : Numerics domains stage) (first second : Fin genus) where
  /-- The retained conjugate clipped assembly for every actual face and sheet. -/ assemblies :
    DependentVector (fun position : Fin faces.length => DependentVector (fun sheet : Fin 2 =>
    ClippedAssembly ((request.entries.get sheet).meshes.entries.get position)
      (ConjugateFacePerimeters.conjugateFaceValues cache first second position
        sheet)))
  /-- The cached perimeter of each retained conjugate assembly. -/ perimeters : DependentVector (fun
    position : Fin faces.length => DependentVector (fun sheet : Fin 2 =>
    ((assemblies.get position).get sheet).Perimeter))

constructive_injectivity ConjugateFacePerimeters

namespace ConjugateFacePerimeters

/-- Cache all conjugate face assemblies and their perimeters from the supplied shared numerical bank. -/
def build (request : TwoSheetRequest coarse fixed target) (cache : Numerics
  domains stage) (first second : Fin genus) :
    ConjugateFacePerimeters request cache first second
      :=
  let assemblies := DependentVector.ofFn fun position => DependentVector.ofFn fun sheet =>
    ClippedAssembly.build ((request.entries.get sheet).meshes.entries.get position)
      (ConjugateFacePerimeters.conjugateFaceValues cache first second position
        sheet)
  ⟨assemblies, DependentVector.ofFn fun position => DependentVector.ofFn fun sheet =>
    Perimeter.build ((assemblies.get position).get sheet)⟩

variable {request : TwoSheetRequest coarse
  fixed target} {cache : Numerics
  domains stage} {first second : Fin genus}

/-- Read the selected oriented side from the retained conjugate face perimeter. -/
def area (retained : ConjugateFacePerimeters request
  cache first second)
    (position : Fin faces.length) (sheet : Fin 2) : GridSide → Gaussian
  | .bottom => ((retained.perimeters.get position).get sheet).bottom
  | .right => ((retained.perimeters.get position).get sheet).right
  | .top => ((retained.perimeters.get position).get sheet).top
  | .left => ((retained.perimeters.get position).get sheet).left

end ConjugateFacePerimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
