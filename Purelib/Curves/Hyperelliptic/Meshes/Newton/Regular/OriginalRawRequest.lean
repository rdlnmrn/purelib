module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
public import Purelib.Riemann.Periods.NewtonRawPeriodGeometry
public import Purelib.Riemann.RootContinuation.NewtonOriginalEnergyComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Retain one raw grid, select its actual original-period sheet, and pay the
transfer to the original sampler with half the positive observation margin. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest

open Purelib

open Purelib.Riemann.Normalization
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank)
  (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (radius : Fraction.Rational)
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

set_option genInjectivity false in
/-- One retained raw Newton grid with its original-period sheet and paid sampler comparison.

Allocate half the positive observation margin to the original sampler transfer and retain a common sufficient stage. -/
structure RegularOriginalRawRequest (floor : Nat) where
  /-- The original-period sheet selected on the retained raw grid. -/ newSheet : Fin 2
  /-- The actual original regular raw request on the selected sheet. -/ raw :
    Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations preparation radius regular
    newSheet floor
  /-- The selected sheet equals the canonical original-period sheet of the retained grid. -/ sheet_eq : newSheet =
    Periods.NewtonCanonicalPeriodReadback.canonicalPeriodSheet (lifted := lifted) (sheet := sheet)
    (Periods.NewtonRawPeriodGeometry.periodGeometry raw.grid)
  /-- The original sampler comparison paid by half the retained positive observation margin. -/ comparison :
    RootContinuation.NewtonOriginalEnergyComparison.OriginalEnergyComparison prepared
    (Periods.NewtonRawPeriodGeometry.periodGeometry raw.grid)
    (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2) floor
  /-- The cached common stage for the raw request and original sampler comparison. -/ index : Nat
  /-- The common stage is exactly the maximum of the two retained original request stages. -/ index_eq : index = max
    raw.index comparison.request.index
  /-- The original raw request is ready by the retained common stage. -/ raw_le : raw.index ≤ index
  /-- The original sampler comparison is ready by the retained common stage. -/ comparison_le : comparison.request.index
    ≤ index

constructive_injectivity RegularOriginalRawRequest

namespace RegularOriginalRawRequest

/-- Build one original raw grid, select its actual canonical period sheet and prepare the half-margin sampler
comparison. -/
@[expose] def build (positive : 0 < radius) (floor : Nat) :
    Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest.RegularOriginalRawRequest prepared observations preparation
      radius regular floor :=
  let grid := RootContinuation.NewtonRawEnergyGrid.RawEnergyGrid.build observations preparation radius positive
  let newSheet := Periods.NewtonCanonicalPeriodReadback.canonicalPeriodSheet (lifted := lifted) (sheet := sheet)
    (Periods.NewtonRawPeriodGeometry.periodGeometry grid)
  let raw := Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest.build prepared observations preparation
    radius regular grid newSheet floor
  let comparison := RootContinuation.NewtonOriginalEnergyComparison.OriginalEnergyComparison.build prepared
    (Periods.NewtonRawPeriodGeometry.periodGeometry raw.grid)
    (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations / 2)
    (Fraction.Order.Field.div_pos_direct (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant_positive
      observations) (by decide)) floor
  ⟨newSheet, raw, rfl, comparison, max raw.index comparison.request.index, rfl, Data.Nat.Order.le_max_left _ _,
    Data.Nat.Order.le_max_right _ _⟩

variable {prepared observations preparation radius regular} {floor : Nat}

/-- The retained common stage meets the original requested floor. -/
theorem floor_le (request : Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest.RegularOriginalRawRequest prepared
  observations preparation radius regular floor) :
    floor ≤ request.index := request.raw.floor_le.trans request.raw_le

end RegularOriginalRawRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.OriginalRawRequest
