module
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
-- Exposed cap builders retain the original bound for each finite sum entry.
public import Purelib.Algebra.FiniteSum.Fin.Rational
-- Exposed cap builders retain the original finite-sum nonnegativity certificate.
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReadingTargetRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound
public import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! Automatic fixed slope ceilings and per-face exterior reading caps. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace DomainPrimitives

variable {face : Meshes.PuncturedGridFaces.RegularFace bank} {models :
  Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face} {sheet : Fin 2}
  {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet} {box :
    Rational.Box}

set_option genInjectivity false in
/-- One original face's common boundary slope ceiling and positive exterior-reading cap.

The retained sum bounds every original basis row on the exact prepared observation mesh. -/
structure FaceExteriorTolerance (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight
  domain)
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box) (target : Fraction.Rational) where
  /-- The cached total boundary slope of the original basis rows. -/ slope : Fraction.Rational
  /-- The slope is exactly the finite sum of the original overlap slopes. -/ slope_eq : slope = FiniteSum.Fin.sumFin
    (fun row => Readings.RectangularSeamBounds.boundarySlope (preflight.overlaps.get row))
  /-- The retained total slope is nonnegative. -/ nonnegative : 0 ≤ slope
  /-- Every original basis-row slope is bounded by the retained total. -/ row_le : ∀ row,
    Readings.RectangularSeamBounds.boundarySlope (preflight.overlaps.get row) ≤ slope
  /-- The positive reading cap for the exact original boundary rows, columns and slope. -/ budget :
    Polynomial.Rectangle.ClippedExteriorTolerance mesh.boundaryColumns mesh.boundaryRows slope target

constructive_injectivity FaceExteriorTolerance

namespace FaceExteriorTolerance

/-- Each original basis overlap has a nonnegative boundary slope.

The retained numerator and inverse bounds multiply the original box diagonal
with nonnegative rational factors. -/
theorem slope_nonnegative (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain) (row
  : Fin genus) :
    0 ≤ Readings.RectangularSeamBounds.boundarySlope (preflight.overlaps.get row) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (preflight.overlaps.get row).numeratorUpper_nonnegative
      (preflight.overlaps.get row).inverseUpper_positive.le))
    face.cell.box.diagonalSq_nonneg

/-- Cache the original basis-slope sum and allocate the positive exterior-reading cap on the same prepared mesh. -/
@[expose] def build (preflight : Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight domain)
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh domain.cuts box) (target : Fraction.Rational) (positive :
      0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance preflight mesh target
      :=
  let slope := FiniteSum.Fin.sumFin (fun row => Readings.RectangularSeamBounds.boundarySlope (preflight.overlaps.get
    row))
  let nonnegative := FiniteSum.Rational.Order.weight_sum_nonnegative _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance.slope_nonnegative
    preflight)
  ⟨slope, rfl, nonnegative, FiniteSum.Fin.Rational.entry_le_sum _
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance.slope_nonnegative
    preflight),
    Polynomial.Rectangle.ClippedExteriorTolerance.build mesh.boundaryColumns mesh.boundaryRows slope target nonnegative
      positive⟩

end FaceExteriorTolerance
end DomainPrimitives

namespace RegularMeshes.TwoSheetRequest

variable {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {energyTarget target : Fraction.Rational}

/-- The dependent collection of retained exterior-reading caps on every original face and both sheets. -/
abbrev ExteriorCaps (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  energyTarget) (target : Fraction.Rational) :=
  Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector (fun position : Fin faces.length =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance ((fixed sheet).get
      position).get
      ((energy.entries.get sheet).meshes.entries.get position) target))

namespace ExteriorCaps

variable {energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed energyTarget}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps
  in
/-- Prepare a positive exterior-reading cap for each original face on both retained sheet meshes. -/
@[expose] def build (energy : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  energyTarget) (target : Fraction.Rational) (positive : 0 < target) :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps energy target :=
  Data.Vector.DependentVector.ofFn fun sheet : Fin 2 => Data.Vector.DependentVector.ofFn fun position : Fin faces.length
    =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance.build ((fixed
      sheet).get position).get
      ((energy.entries.get sheet).meshes.entries.get position) target positive

/-- Read the cached cap of the original sheet and face. -/
@[expose] def values (caps :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps energy target)
  (sheet : Fin 2) (position : Fin faces.length) : Fraction.Rational :=
  ((caps.get sheet).get position).budget.cap

/-- Every retained exterior-reading cap is positive. -/
theorem positive (caps :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps energy target)
  (sheet : Fin 2) (position : Fin faces.length) :
    0 < caps.values sheet position := ((caps.get sheet).get position).budget.positive

/-- Tightening uses the cached caps and preserves all prepared face meshes. -/
@[expose] def refined (caps :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps energy target) :
  Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed energyTarget :=
  energy.limitReadings caps.values caps.positive

/-- Every original basis-pair exterior error meets the supplied target after tightening to the retained caps. -/
theorem pair_bound (caps :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps energy target)
  (stage : Nat) (later : caps.refined.index ≤ stage)
    (sheet : Fin 2) (position : Fin faces.length) (first second : Fin genus) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound caps.refined stage
      later sheet position first second ≤ target := by
  let entry := (caps.refined.entries.get sheet).entries.get position
  let rowLater := ((caps.refined.entries.get sheet).index_ge position).trans ((caps.refined.index_ge sheet).trans later)
  let left := entry.modelRequest.rowAtStage stage rowLater first
  let right := entry.modelRequest.rowAtStage stage rowLater second
  let budget := ((caps.get sheet).get position).budget
  have readingLe : entry.readingTarget ≤ budget.cap := energy.limitReadings_target_le caps.values caps.positive sheet
    position
  have leftLe : left.globalBound ≤ budget.cap := left.accurate.le.trans readingLe
  have rightLe : right.globalBound ≤ budget.cap := right.accurate.le.trans readingLe
  have bound := budget.pair_bound (left.edgeBound_nonnegative.trans left.edgeBound_le_globalBound) leftLe rightLe
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.DomainPrimitives.FaceExteriorTolerance.slope_nonnegative
      ((fixed sheet).get position).get first)
    (((caps.get sheet).get position).row_le first) (((caps.get sheet).get position).row_le second)
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound]
  rw [show (caps.refined.entries.get sheet).meshes.entries.get position =
      (energy.entries.get sheet).meshes.entries.get position from energy.limitReadings_mesh caps.values caps.positive
        sheet position]
  exact bound

end ExteriorCaps
end RegularMeshes.TwoSheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
