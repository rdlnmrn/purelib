module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Readings.RectangularPointOwnerBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-! Select both owner-error budgets before evaluating the shared primitive
banks. Actual point owners are retained, including at zero-length junctions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest

open Purelib.Riemann.Normalization

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

/-- The original first-differential grid-owner accuracy request at one sixteenth of the tolerance. -/
@[expose] def FirstOwnerBudget (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (tolerance : Normalization.InverseRootPolynomial.Coordinate) :=
  Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy occurrence.compared.entered.globalBounds
    occurrence.compared.entered.domain.steps (tolerance / 16)

/-- The corresponding recast second-differential owner request at the same allocated tolerance. -/
@[expose] def SecondOwnerBudget (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance :
  Normalization.InverseRootPolynomial.Coordinate) :=
  Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy (occurrence.recastComparison
    other).entered.globalBounds
    (occurrence.recastComparison other).entered.domain.steps (tolerance / 16)

set_option genInjectivity false in
/-- Both original point-owner error budgets on one retained exterior occurrence.

The paired request keeps the original and recast domains distinct while allowing a common later reading stage. -/
structure OwnerRequest (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance :
  Normalization.InverseRootPolynomial.Coordinate) where
  /-- The retained owner-error budget for the original first differential. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.FirstOwnerBudget occurrence tolerance
  /-- The retained owner-error budget for the recast second differential. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.SecondOwnerBudget occurrence other tolerance

constructive_injectivity OwnerRequest

namespace OwnerRequest
variable {occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential} {tolerance : Normalization.InverseRootPolynomial.Coordinate}

/-- Allocate both original owner-error budgets from the supplied positive tolerance before reading primitive values. -/
@[expose] def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (tolerance : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < tolerance) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other tolerance :=
  let small := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 16)
  ⟨GridPrimitiveAccuracy.build _ _ (tolerance / 16) small,
    Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.build _ _ (tolerance / 16) small⟩

/-- The common stage dominating both retained owner-error budgets. -/
@[expose] def index (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
  other tolerance) : Nat := max request.first.index request.second.index

/-- Four times one sixteenth of a rational value is at most one quarter of that value. -/
private theorem four_sixteenths (value : Normalization.InverseRootPolynomial.Coordinate) : 4 * (value / 16) ≤ value / 4
  := by
  apply (Fraction.Order.Field.le_div_iff_pos (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)).mpr
  exact ((show (4 * (value / 16)) * 4 = (value / 16) * 16 by ring1).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))).le

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest
/-- The actual first point-owner reading differs from the containing cell's aligned value by at most a quarter
tolerance.

The common late request stage and original cell containment pay the comparison. -/
theorem first_bound (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
  other tolerance) {index count : Nat} (later : request.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) {points : Fin
      count → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (vertex : Fin count) (column row : Fin (occurrence.compared.entered.domain.steps + 1))
    (inside : (occurrence.compared.entered.domain.geometry.box column row).Contains (points vertex)) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex - data.anchors.alignedValue data.offsets column row
      (points vertex)) ≤ tolerance / 4 := open Purelib.Integration in by
  let selected := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex request.first index
    ((Data.Nat.Order.le_max_left ..).trans later)
  have bound := Readings.RectangularPointOwnerBounds.point_cell_bound selected readings
    occurrence.compared.entered.domain.patch.cell_refines vertex column row inside
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct selected.accurate.le (by decide)).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest.four_sixteenths tolerance))

/-- The recast second point-owner reading differs from its actual containing cell value by at most a quarter tolerance.

Its own retained domain and common late request stage supply the bound. -/
theorem second_bound (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence
  other tolerance) {index count : Nat} (later : request.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index) {points
      : Fin count → Normalization.InverseRootPolynomial.Gaussian}
    (readings : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (vertex : Fin count) (column row : Fin ((occurrence.recastComparison other).entered.domain.steps + 1))
    (inside : ((occurrence.recastComparison other).entered.domain.geometry.box column row).Contains (points vertex)) :
    Data.Gaussian.Norm.Basic.normSq (readings.values vertex - data.anchors.alignedValue data.offsets column row
      (points vertex)) ≤ tolerance / 4 := open Purelib.Integration in by
  let selected := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex request.second index
    ((Data.Nat.Order.le_max_right ..).trans later)
  have bound := Readings.RectangularPointOwnerBounds.point_cell_bound selected readings (occurrence.recastComparison
    other).entered.domain.patch.cell_refines vertex column row inside
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct selected.accurate.le (by decide)).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest.four_sixteenths tolerance))

end OwnerRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest

end
