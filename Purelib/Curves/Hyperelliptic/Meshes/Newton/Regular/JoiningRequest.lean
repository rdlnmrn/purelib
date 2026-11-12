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

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

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

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {firstIndex secondIndex : Fin genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}

/-- Compact dependent type for the two automatic cap preparations. -/
@[expose] def JoiningCapRequest (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap) (domains :
  Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars)
    (firstIndex secondIndex : Fin genus) (error : Fraction.Rational) (floor : Nat) :=
  Exterior.PairedCapRequest

      (ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))

      (ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex)) error floor

set_option genInjectivity false in
/-- A paid regular Newton-to-cap joining request on the original two magnitude banks.

Its retained factor, lap request, automatic cap request and common stage pay the complete requested joining error. -/
structure RegularJoiningRequest (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) (error : Fraction.Rational) (floor : Nat) where
  /-- The cached common polarized exterior factor bound. -/ factor : Fraction.Rational
  /-- The cached factor is the maximum of the original two magnitude-bank factor bounds. -/ factor_eq : factor = max
    (Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
    paired) grid.shrunk.included first)
    (Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) grid.shrunk.included second)
  /-- The cached exterior factor is nonnegative. -/ factor_nonnegative : 0 ≤ factor
  /-- The retained positive cap-comparison target. -/ capTarget : Fraction.Rational
  /-- The retained cap target is strictly positive. -/ cap_positive : 0 < capTarget
  /-- The retained cap target is at most one. -/ cap_small : capTarget ≤ 1
  /-- The factor-weighted cap target is paid by one eighth of the total error. -/ cap_paid : (16 * factor + 5) *
    capTarget ≤ error / 8
  /-- The retained exterior lap request at one eighth of the total error. -/ lap :
    Exterior.LapRequest.ExteriorLapRequest first second (error / 8)
  /-- The paired cap request on the same automatic preparations and retained cap target. -/ caps :
    JoiningCapRequest regular domains firstIndex secondIndex
    capTarget floor
  /-- The cached common evaluation stage. -/ index : Nat
  /-- The common stage is the maximum of the caller floor, both magnitude banks and both retained requests. -/ index_eq
    : index = max floor (max first.index (max second.index (max lap.index caps.index)))

constructive_injectivity RegularJoiningRequest

namespace RegularJoiningRequest
variable {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {first : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational} {floor : Nat}

/-- A positive joining error and nonnegative factor admit the displayed positive cap allocation bounded by one. -/
theorem cap_budget (factor error : Fraction.Rational) (nonnegative : 0 ≤ factor) (positive : 0 < error) :
    0 < min 1 ((error / 8) / (16 * factor + 5)) ∧
    min 1 ((error / 8) / (16 * factor + 5)) ≤ 1 ∧
    (16 * factor + 5) * min 1 ((error / 8) / (16 * factor + 5)) ≤ error / 8 := by
  have partPositive : 0 < error / 8 := Field.div_pos_direct positive (by decide)
  have weightPositive : 0 < 16 * factor + 5 := by
    calc
      0 < (5 : Fraction.Rational) := by decide
      _ = 0 + 5 := by ring1
      _ ≤ 16 * factor + 5 := Arithmetic.add_le_add_right_direct
        (Arithmetic.mul_nonneg_direct (by decide) nonnegative) 5
  refine ⟨Basic.lt_min (by decide) (Field.div_pos_direct partPositive weightPositive),
    Basic.min_le_left _ _, ?_⟩
  have small : min 1 ((error / 8) / (16 * factor + 5)) ≤ (error / 8) / (16 * factor + 5) :=
    Basic.min_le_right _ _
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct small weightPositive.le
  exact (Fraction.Field.mul_comm _ _).trans_le (paid.trans_eq (Fraction.Field.div_mul_cancel_of_ne (error / 8) (16 *
    factor + 5) weightPositive.ne'))

/-- Acquire both comparisons after choosing coefficient-independent budgets.
The stored index includes both magnitude banks, both requests and the caller floor. -/
@[expose] def build (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (firstPrepared :
      ExteriorProgram.AllSurfacePreparation
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))
    (lastPrepared :
      ExteriorProgram.AllSurfacePreparation
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex))
    (first_eq : firstPrepared =
      ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))
    (last_eq : lastPrepared =
      ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
      RegularJoiningRequest (paired := paired) regular first second
      error floor := by
  let factor : Rational := max
    (Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
    paired) grid.shrunk.included first)
    (Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) grid.shrunk.included second)
  have nonnegative : 0 ≤ factor :=
    (Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
    (paired := paired)
    grid.shrunk.included first).trans (Basic.le_max_left _ _)
  have partPositive : 0 < error / 8 := Field.div_pos_direct positive (by decide)
  let capTarget : Rational := min 1 ((error / 8) / (16 * factor + 5))
  have budget := RegularJoiningRequest.cap_budget factor error
    nonnegative positive
  let lap : Exterior.LapRequest.ExteriorLapRequest first second (error / 8) :=
    Exterior.LapRequest.ExteriorLapRequest.build first second (error / 8)
    partPositive
  let acquired := Exterior.PairedCapRequest.build firstPrepared
    lastPrepared capTarget budget.1 floor
  let caps : JoiningCapRequest regular domains firstIndex secondIndex
    capTarget floor :=
    cast (congrArg₂ (fun first last => Exterior.PairedCapRequest
      first last capTarget floor) first_eq last_eq) acquired
  exact ⟨factor, rfl, nonnegative, capTarget, budget.1, budget.2.1, budget.2.2, lap, caps,
    max floor (max first.index (max second.index (max lap.index caps.index))), rfl⟩

variable (request : RegularJoiningRequest (paired := paired)
  regular first second error floor)

/-- The common request stage dominates the supplied minimum floor. -/
theorem floor_le : floor ≤ request.index := by rw [request.index_eq]; exact Nat.Order.le_max_left _ _

/-- The common request stage dominates the original first magnitude bank's stage. -/
theorem first_le : first.index ≤ request.index := by
  rw [request.index_eq]
  exact (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)

/-- The common request stage dominates the original second magnitude bank's stage. -/
theorem second_le : second.index ≤ request.index := by
  rw [request.index_eq]
  exact (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _
    _))

/-- The common request stage dominates the retained exterior lap request. -/
theorem lap_le : request.lap.index ≤ request.index := by
  rw [request.index_eq]
  exact (Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _
    _).trans (Nat.Order.le_max_right _ _)))

/-- The common request stage dominates the retained paired cap request. -/
theorem caps_le : request.caps.index ≤ request.index := by
  rw [request.index_eq]
  exact (Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _
    _).trans (Nat.Order.le_max_right _ _)))

/-- The retained cap allowance is at most its original positive cap target. -/
private theorem allowance_le : request.caps.allowance ≤ request.capTarget := by
  rw [request.caps.allowance_eq]
  have denominator : 0 < request.caps.coefficient + 1 := by
    calc
      0 < (1 : Fraction.Rational) := by decide
      _ = 0 + 1 := by ring1
      _ ≤ request.caps.coefficient + 1 := Arithmetic.add_le_add_right_direct
        request.caps.coefficient_nonnegative 1
  apply (Field.div_le_iff_pos denominator).mpr
  have oneLe : (1 : Fraction.Rational) ≤ request.caps.coefficient + 1 :=
    (show (1 : Fraction.Rational) = 0 + 1 by ring1).trans_le
      (Arithmetic.add_le_add_right_direct request.caps.coefficient_nonnegative 1)
  exact (mul_one request.capTarget).symm.trans_le (Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe
    request.cap_positive.le)

/-- The original lap, linear terminal and quadratic cap contributions fit the complete joining tolerance. -/
private theorem paid : 4 * (error / 8 + 16 * request.factor * request.caps.allowance + request.capTarget +
    4 * request.caps.allowance^2) ≤ error := by
  have small : request.caps.allowance ≤ 1 := request.allowance_le.trans request.cap_small
  have square : request.caps.allowance^2 ≤ request.capTarget := by
    have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct small request.caps.positive.le
    rw [mul_one] at bound
    exact (show request.caps.allowance^2 = request.caps.allowance * request.caps.allowance by ring1).trans_le
      (bound.trans request.allowance_le)
  have linear := Arithmetic.mul_le_mul_of_nonneg_left_direct request.allowance_le
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16) request.factor_nonnegative)
  have squared := Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
      decide : (0 : Fraction.Rational) ≤ 4)
  have terms := Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct linear (le_refl
    request.capTarget)) squared
  have capBound : 16 * request.factor * request.caps.allowance + request.capTarget + 4 * request.caps.allowance^2 ≤
    error / 8 :=
    terms.trans ((show 16 * request.factor * request.capTarget + request.capTarget + 4 * request.capTarget =
      (16 * request.factor + 5) * request.capTarget by ring1).trans_le request.cap_paid)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct
    (le_refl (error / 8)) capBound)
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have arrange : 4 * (error / 8 + 16 * request.factor * request.caps.allowance + request.capTarget + 4 *
    request.caps.allowance^2) =
      4 * (error / 8 + (16 * request.factor * request.caps.allowance + request.capTarget + 4 *
        request.caps.allowance^2)) := by ring1
  exact arrange.trans_le (scaled.trans_eq ((show 4 * (error / 8 + error / 8) = (error / 8) * 8 by ring1).trans
    (Fraction.Field.div_mul_cancel_of_ne error 8 (by decide))))

variable {stage depth otherDepth readingIndex : Nat} {box : Rational.Box}
  {sample : Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
    firstIndex) stage box}
  {otherSample : Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
    secondIndex) stage box}
  {leftBank : Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
  {rightBank : Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}

/-- The original cap evaluator consumes the retained requests at a common
later stage. No primitive or triangle bank is reacquired. -/
@[expose] def evaluate (sample : Charts.Reciprocal.Cap.Primitives.Sample cap
  (Periods.PeriodMatrix.standardDifferential firstIndex) stage box)
    (otherSample : Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
      secondIndex) stage box)
    (leftBank : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains)
    (rightBank : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains)
    (depth otherDepth readingIndex : Nat) (later : request.index ≤ stage) (readingLater : request.caps.readingIndex ≤
      readingIndex) :
    Exterior.PairedCapRequest.Evaluation request.caps sample
      otherSample leftBank rightBank depth otherDepth readingIndex :=
  request.caps.evaluate sample otherSample leftBank rightBank depth otherDepth readingIndex (request.caps_le.trans
    later) readingLater

/-- Every later common sample satisfies the requested error, with no caller
period bound, terminal-product certificate or coefficient vector. -/
theorem accurate
    (evaluated : Exterior.PairedCapRequest.Evaluation request.caps
      sample otherSample leftBank rightBank depth otherDepth readingIndex)
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right
      : TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : request.index ≤ stage) (newSheet : Fin 2)
    (attached : Exterior.Caps.AllSurfacePreparation.CapAttachment
      (ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Gaussian.Norm.Basic.normSq (2 *
      ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) -
      Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) < error := by
  have bound := RetainedCapJoiningComparison.retained_exterior_cap_joining_accurate (paired
    := paired) request.lap left right (request.lap_le.trans later)
    (request.first_le.trans later) (request.second_le.trans later) newSheet evaluated attached degree
  rw [← request.factor_eq] at bound
  exact bound.trans_le request.paid

end RegularJoiningRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest
