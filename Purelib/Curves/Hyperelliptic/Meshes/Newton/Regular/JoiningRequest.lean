module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.RetainedCapJoiningComparison
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! A positive error request for the regular Newton-to-cap joining comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {firstIndex secondIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}

/-- Compact dependent type for the two automatic cap preparations. -/
@[expose] def JoiningCapRequest (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars)
    (firstIndex secondIndex : Fin genus) (error : Fraction.Rational) (floor : Nat) :=
  PuncturedGrid.Exterior.PairedCapRequest

      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))

      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex)) error floor

set_option genInjectivity false in
/-- A paid regular Newton-to-cap joining request on the original two magnitude banks.

Its retained factor, lap request, automatic cap request and common stage pay the complete requested joining error. -/
structure RegularJoiningRequest (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) (error : Fraction.Rational) (floor : Nat) where
  /-- The cached common polarized exterior factor bound. -/ factor : Fraction.Rational
  /-- The cached factor is the maximum of the original two magnitude-bank factor bounds. -/ factor_eq : factor = max
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
    paired) grid.shrunk.included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) grid.shrunk.included second)
  /-- The cached exterior factor is nonnegative. -/ factor_nonnegative : 0 ≤ factor
  /-- The retained positive cap-comparison target. -/ capTarget : Fraction.Rational
  /-- The retained cap target is strictly positive. -/ cap_positive : 0 < capTarget
  /-- The retained cap target is at most one. -/ cap_small : capTarget ≤ 1
  /-- The factor-weighted cap target is paid by one eighth of the total error. -/ cap_paid : (16 * factor + 5) *
    capTarget ≤ error / 8
  /-- The retained exterior lap request at one eighth of the total error. -/ lap :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest first second (error / 8)
  /-- The paired cap request on the same automatic preparations and retained cap target. -/ caps :
    Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.JoiningCapRequest regular domains firstIndex secondIndex
    capTarget floor
  /-- The cached common evaluation stage. -/ index : Nat
  /-- The common stage is the maximum of the caller floor, both magnitude banks and both retained requests. -/ index_eq
    : index = max floor (max first.index (max second.index (max lap.index caps.index)))

constructive_injectivity RegularJoiningRequest

namespace RegularJoiningRequest
variable {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational} {floor : Nat}

/-- A positive joining error and nonnegative factor admit the displayed positive cap allocation bounded by one. -/
theorem cap_budget (factor error : Fraction.Rational) (nonnegative : 0 ≤ factor) (positive : 0 < error) :
    0 < min 1 ((error / 8) / (16 * factor + 5)) ∧
    min 1 ((error / 8) / (16 * factor + 5)) ≤ 1 ∧
    (16 * factor + 5) * min 1 ((error / 8) / (16 * factor + 5)) ≤ error / 8 := by
  have partPositive : 0 < error / 8 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have weightPositive : 0 < 16 * factor + 5 := by
    calc
      0 < (5 : Fraction.Rational) := by decide
      _ = 0 + 5 := by ring1
      _ ≤ 16 * factor + 5 := Fraction.Order.Arithmetic.add_le_add_right_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) 5
  refine ⟨Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct partPositive weightPositive),
    Fraction.Order.Basic.min_le_left _ _, ?_⟩
  have small : min 1 ((error / 8) / (16 * factor + 5)) ≤ (error / 8) / (16 * factor + 5) :=
    Fraction.Order.Basic.min_le_right _ _
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small weightPositive.le
  exact (Fraction.Field.mul_comm _ _).trans_le (paid.trans_eq (Fraction.Field.div_mul_cancel_of_ne (error / 8) (16 *
    factor + 5) weightPositive.ne'))

/-- Acquire both comparisons after choosing coefficient-independent budgets.
The stored index includes both magnitude banks, both requests and the caller floor. -/
@[expose] def build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (firstPrepared :
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))
    (lastPrepared :
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex))
    (first_eq : firstPrepared =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))
    (last_eq : lastPrepared =
      PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
      Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.RegularJoiningRequest (paired := paired) regular first second
      error floor := by
  let factor : Rational := max
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
    paired) grid.shrunk.included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) grid.shrunk.included second)
  have nonnegative : 0 ≤ factor :=
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
    (paired := paired)
    grid.shrunk.included first).trans (Fraction.Order.Basic.le_max_left _ _)
  have partPositive : 0 < error / 8 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let capTarget : Rational := min 1 ((error / 8) / (16 * factor + 5))
  have budget := Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.RegularJoiningRequest.cap_budget factor error
    nonnegative positive
  let lap : Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest first second (error / 8) :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest.build first second (error / 8)
    partPositive
  let acquired := PuncturedGrid.Exterior.PairedCapRequest.build firstPrepared
    lastPrepared capTarget budget.1 floor
  let caps : Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.JoiningCapRequest regular domains firstIndex secondIndex
    capTarget floor :=
    cast (congrArg₂ (fun first last => PuncturedGrid.Exterior.PairedCapRequest
      first last capTarget floor) first_eq last_eq) acquired
  exact ⟨factor, rfl, nonnegative, capTarget, budget.1, budget.2.1, budget.2.2, lap, caps,
    max floor (max first.index (max second.index (max lap.index caps.index))), rfl⟩

variable (request : Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.RegularJoiningRequest (paired := paired)
  regular first second error floor)

/-- The common request stage dominates the supplied minimum floor. -/
theorem floor_le : floor ≤ request.index := by rw [request.index_eq]; exact Data.Nat.Order.le_max_left _ _

/-- The common request stage dominates the original first magnitude bank's stage. -/
theorem first_le : first.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The common request stage dominates the original second magnitude bank's stage. -/
theorem second_le : second.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _
    _))

/-- The common request stage dominates the retained exterior lap request. -/
theorem lap_le : request.lap.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans (Data.Nat.Order.le_max_right _ _)))

/-- The common request stage dominates the retained paired cap request. -/
theorem caps_le : request.caps.index ≤ request.index := by
  rw [request.index_eq]
  exact (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _
    _).trans (Data.Nat.Order.le_max_right _ _)))

/-- The retained cap allowance is at most its original positive cap target. -/
private theorem allowance_le : request.caps.allowance ≤ request.capTarget := by
  rw [request.caps.allowance_eq]
  have denominator : 0 < request.caps.coefficient + 1 := by
    calc
      0 < (1 : Fraction.Rational) := by decide
      _ = 0 + 1 := by ring1
      _ ≤ request.caps.coefficient + 1 := Fraction.Order.Arithmetic.add_le_add_right_direct
        request.caps.coefficient_nonnegative 1
  apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
  have oneLe : (1 : Fraction.Rational) ≤ request.caps.coefficient + 1 :=
    (show (1 : Fraction.Rational) = 0 + 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.add_le_add_right_direct request.caps.coefficient_nonnegative 1)
  exact (mul_one request.capTarget).symm.trans_le (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe
    request.cap_positive.le)

/-- The original lap, linear terminal and quadratic cap contributions fit the complete joining tolerance. -/
private theorem paid : 4 * (error / 8 + 16 * request.factor * request.caps.allowance + request.capTarget +
    4 * request.caps.allowance^2) ≤ error := by
  have small : request.caps.allowance ≤ 1 := request.allowance_le.trans request.cap_small
  have square : request.caps.allowance^2 ≤ request.capTarget := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small request.caps.positive.le
    rw [mul_one] at bound
    exact (show request.caps.allowance^2 = request.caps.allowance * request.caps.allowance by ring1).trans_le
      (bound.trans request.allowance_le)
  have linear := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.allowance_le
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16) request.factor_nonnegative)
  have squared := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have terms := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct linear (le_refl
    request.capTarget)) squared
  have capBound : 16 * request.factor * request.caps.allowance + request.capTarget + 4 * request.caps.allowance^2 ≤
    error / 8 :=
    terms.trans ((show 16 * request.factor * request.capTarget + request.capTarget + 4 * request.capTarget =
      (16 * request.factor + 5) * request.capTarget by ring1).trans_le request.cap_paid)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    (le_refl (error / 8)) capBound)
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have arrange : 4 * (error / 8 + 16 * request.factor * request.caps.allowance + request.capTarget + 4 *
    request.caps.allowance^2) =
      4 * (error / 8 + (16 * request.factor * request.caps.allowance + request.capTarget + 4 *
        request.caps.allowance^2)) := by ring1
  exact arrange.trans_le (scaled.trans_eq ((show 4 * (error / 8 + error / 8) = (error / 8) * 8 by ring1).trans
    (Fraction.Field.div_mul_cancel_of_ne error 8 (by decide))))

variable {stage depth otherDepth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
    firstIndex) stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
    secondIndex) stage box}
  {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
  {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}

/-- The original cap evaluator consumes the retained requests at a common
later stage. No primitive or triangle bank is reacquired. -/
@[expose] def evaluate (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
  (Periods.PeriodMatrix.standardDifferential firstIndex) stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
      secondIndex) stage box)
    (leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains)
    (rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains)
    (depth otherDepth readingIndex : Nat) (later : request.index ≤ stage) (readingLater : request.caps.readingIndex ≤
      readingIndex) :
    PuncturedGrid.Exterior.PairedCapRequest.Evaluation request.caps sample
      otherSample leftBank rightBank depth otherDepth readingIndex :=
  request.caps.evaluate sample otherSample leftBank rightBank depth otherDepth readingIndex (request.caps_le.trans
    later) readingLater

/-- Every later common sample satisfies the requested error, with no caller
period bound, terminal-product certificate or coefficient vector. -/
theorem accurate
    (evaluated : PuncturedGrid.Exterior.PairedCapRequest.Evaluation request.caps
      sample otherSample leftBank rightBank depth otherDepth readingIndex)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right
      : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (newSheet : Fin 2)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Data.Gaussian.Norm.Basic.normSq (2 *
      ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) < error := by
  have bound := Hyperelliptic.Meshes.Newton.RetainedCapJoiningComparison.retained_exterior_cap_joining_accurate (paired
    := paired) request.lap left right (request.lap_le.trans later)
    (request.first_le.trans later) (request.second_le.trans later) newSheet evaluated attached degree
  rw [← request.factor_eq] at bound
  exact bound.trans_le request.paid

end RegularJoiningRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest
