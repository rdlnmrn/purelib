module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods
public import Purelib.Topology.Surface.Boundary.HandleAreaBudgets
import Init.Data.List.OfFn
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.CornerFamily
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.Prepared

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Surface.Boundary.HandleAreaBudgets

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Data

/-! Two corrected differential families on one numerical surface stage.
The determinant comparison pays every row and both finite-sum count factors.
It approximates the full residual, not a falsely vanishing boundary term. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.Prepared (SurfaceRequest SurfaceBudget)
open Purelib.Topology.Surface.Boundary.HandleAreaBudgets (HandleAreaBudget)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}

set_option genInjectivity false in
/-- Two corrected differential surface requests sharing one exact numerical stage.

Each retained family keeps its own requested execution stage, with a cached maximum paying both. -/
structure TwoSurface (prepared : PeriodPrograms.Prepared paired) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (first second : Fin genus) (target : Fraction.Rational) (minimumStage : Nat) where
  /-- The retained corrected surface request for the first original differential. -/ left : Prepared.SurfaceRequest
    prepared domains first target minimumStage
  /-- The retained corrected surface request for the second original differential. -/ right : Prepared.SurfaceRequest
    prepared domains second target minimumStage
  /-- The exact common numerical stage used by both original primitive banks. -/ numericalIndex : Nat
  /-- The first retained family uses the exact common numerical stage. -/ left_index : left.family.numericalIndex =
    numericalIndex
  /-- The second retained family uses the exact common numerical stage. -/ right_index : right.family.numericalIndex =
    numericalIndex
  /-- The cached common execution stage paying both corrected surface families. -/ stage : Nat
  /-- The common execution stage is exactly the maximum of both original requested stages. -/ stage_eq : stage = max
    left.family.requested.stage right.family.requested.stage

constructive_injectivity TwoSurface

/-- Build both original surface budgets and primitive banks at one shared numerical stage, then retain their common
execution maximum. -/
@[expose] def TwoSurface.build (prepared : PeriodPrograms.Prepared paired) (domains : DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars)
    (first second : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimumStage : Nat) :
    TwoSurface prepared domains first second target
      minimumStage :=
  let left := SurfaceBudget.build prepared domains first target positive
  let right := SurfaceBudget.build prepared domains second target positive
  let numericalIndex := max left.minimum right.minimum
  let leftNumerics := FacePrimitiveBank.build (PeriodMatrix.standardDifferential first) numericalIndex domains
  let rightNumerics := FacePrimitiveBank.build (PeriodMatrix.standardDifferential second) numericalIndex domains
  let leftRequest := left.requestWith (Nat.Order.le_max_left _ _) leftNumerics minimumStage
  let rightRequest := right.requestWith (Nat.Order.le_max_right _ _) rightNumerics minimumStage
  ⟨leftRequest, rightRequest, numericalIndex, rfl, rfl,
    max leftRequest.family.requested.stage rightRequest.family.requested.stage, rfl⟩

/-- The nonnegative finite maximum of the supplied rational list, using zero for the empty list. -/
@[expose] def maximum : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | value :: rest => max value (maximum rest)

/-- The retained finite rational maximum is nonnegative for every input list. -/
theorem maximum_nonnegative (values : List Fraction.Rational) : 0 ≤
  maximum values := by
  induction values with
  | nil => exact le_rfl
  | cons value rest ih => exact ih.trans (Fraction.Order.Basic.le_max_right _ _)

/-- Every actual member of a rational list is bounded by its retained finite maximum. -/
private theorem le_maximum {values : List Fraction.Rational} {value : Fraction.Rational} (member : value ∈ values) :
    value ≤ maximum values := by
  induction values with
  | nil => cases member
  | cons head rest ih =>
    rcases List.Membership.mem_cons.mp member with rfl | present
    · exact Fraction.Order.Basic.le_max_left _ _
    · exact (ih present).trans (Fraction.Order.Basic.le_max_right _ _)

/-- The maximum original center bound among both A/B periods of the two differential rows at one handle. -/
@[expose] def rowMagnitude (prepared : PeriodPrograms.Prepared paired) (first second index : Fin genus) :
  Fraction.Rational :=
  max (max (prepared.periodData.aProgram first index).integral.centerBound
    (prepared.periodData.aProgram second index).integral.centerBound)
    (max (prepared.periodData.bProgram first index).integral.centerBound
      (prepared.periodData.bProgram second index).integral.centerBound)

set_option genInjectivity false in
/-- A complete finite determinant request on two original corrected differential surface families.

The retained row bounds and common magnitude pay every handle contribution and the complete finite-sum error. -/
structure BilinearRequest (prepared : PeriodPrograms.Prepared paired) (domains : DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars)
    (first second : Fin genus) (target : Fraction.Rational) (minimumStage : Nat) where
  /-- The retained list of actual original per-handle row magnitude bounds. -/ magnitudes : List Fraction.Rational
  /-- The row-bound cache is exactly the original complete finite row-magnitude list. -/ magnitudes_eq : magnitudes =
    List.ofFn (rowMagnitude prepared first second)
  /-- The cached common upper bound for all original row magnitudes. -/ magnitude : Fraction.Rational
  /-- The common magnitude is exactly the retained list's nonnegative finite maximum. -/ magnitude_eq : magnitude =
    maximum magnitudes
  /-- The retained complete handle-area budget paid by the original target and row magnitude. -/ budget :
    HandleAreaBudgets.HandleAreaBudget magnitude genus target
  /-- The two original surface families requested at the retained per-row tolerance. -/ surface :
    TwoSurface prepared domains first second
    budget.rowTarget minimumStage

constructive_injectivity BilinearRequest

namespace BilinearRequest

variable {prepared : Prepared paired} {domains :
  FaceDomainBank lifted.frames base.faces.regulars}
  {first second : Fin genus} {target : Rational} {minimumStage : Nat}

/-- Cache every original row magnitude and its maximum, then prepare both corrected surface families using the paid
handle-area budget. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (first second : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimumStage : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest prepared domains first second
      target minimumStage :=
  let magnitudes := List.ofFn (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.rowMagnitude prepared
    first second)
  let magnitude := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.maximum magnitudes
  let budget := HandleAreaBudget.build magnitude
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.maximum_nonnegative magnitudes) genus target
    positive
  ⟨magnitudes, rfl, magnitude, rfl, budget,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.TwoSurface.build prepared domains first second
    budget.rowTarget budget.row_positive minimumStage⟩

/-- Each actual original handle row magnitude is bounded by the request's cached common magnitude. -/
private theorem row_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest
  prepared domains first second target minimumStage) (index : Fin genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.rowMagnitude prepared first second index ≤
      request.magnitude := by
  rw [request.magnitude_eq, request.magnitudes_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.le_maximum (List.OfFn.Basic.mem_ofFn.mpr
    ⟨index, rfl⟩)

/-- The finite alternating A/B period determinant using the original model samples at the supplied stage. -/
@[expose] def determinant (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus) (stage : Nat) :
  Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    ((prepared.periodData.aProgram first index).integral.model stage).integralSample *
      ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
    ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
      ((prepared.periodData.aProgram second index).integral.model stage).integralSample)

/-- Four paid Gaussian entry errors bound the resulting two-product determinant error by the retained common magnitude.
-/
private theorem determinant_error {a b c d aa bb cc dd : Data.Gaussian.Basic.Canonical} {magnitude error :
  Fraction.Rational}
    (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (aBound : Data.Gaussian.Norm.Basic.normSq a ≤ magnitude) (bBound : Data.Gaussian.Norm.Basic.normSq
      b ≤ magnitude)
    (cBound : Data.Gaussian.Norm.Basic.normSq c ≤ magnitude) (dBound : Data.Gaussian.Norm.Basic.normSq
      d ≤ magnitude)
    (aError : Data.Gaussian.Norm.Basic.normSq (aa - a) ≤ error) (bError :
      Data.Gaussian.Norm.Basic.normSq (bb - b) ≤ error)
    (cError : Data.Gaussian.Norm.Basic.normSq (cc - c) ≤ error) (dError :
      Data.Gaussian.Norm.Basic.normSq (dd - d) ≤ error) :
    Data.Gaussian.Norm.Basic.normSq ((aa * dd - bb * cc) - (a * d - b * c)) ≤ 32 * (magnitude + 1) * error :=
  PrimitivePoint.area_difference_bound (first := ⟨a, c⟩) (last := ⟨b, d⟩)
    (changedFirst := ⟨aa, cc⟩) (changedLast := ⟨bb, dd⟩)
    nonnegative errorNonnegative small
    ⟨by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using aBound,
      by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using cBound⟩
    ⟨by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bBound,
      by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using dBound⟩
    ⟨by
      simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using aError,
      by
        simpa only [PrimitivePoint.sub,
          Data.Gaussian.Norm.Basic.normSq_eq_canonical] using cError⟩
    ⟨by
      simpa only [PrimitivePoint.sub,
        Data.Gaussian.Norm.Basic.normSq_eq_canonical] using bError,
      by
        simpa only [PrimitivePoint.sub,
          Data.Gaussian.Norm.Basic.normSq_eq_canonical] using dError⟩

/-- The original corrected surface word pair and corresponding model determinant row satisfy the retained per-row
squared-error bound. -/
private theorem row_error (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest
  prepared domains first second target minimumStage)
    (index : Fin genus) (stage : Nat) (later : request.surface.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((SewingRetraction.wordValue request.surface.left.value (prepared.aWord
      index) * SewingRetraction.wordValue request.surface.right.value (prepared.bWord index) -
      SewingRetraction.wordValue request.surface.left.value (prepared.bWord index) * SewingRetraction.wordValue
        request.surface.right.value (prepared.aWord index)) -
      (((prepared.periodData.aProgram first index).integral.model stage).integralSample *
        ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
      ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
        ((prepared.periodData.aProgram second index).integral.model stage).integralSample)) ≤
      32 * (request.magnitude + 1) * request.budget.rowTarget := by
  have bound := request.row_le index
  change max (max _ _) (max _ _) ≤ request.magnitude at bound
  have leftBound := (Fraction.Order.Basic.le_max_left _ _).trans bound
  have rightBound := (Fraction.Order.Basic.le_max_right _ _).trans bound
  have aBounds := And.intro ((Fraction.Order.Basic.le_max_left _ _).trans leftBound)
    ((Fraction.Order.Basic.le_max_right _ _).trans leftBound)
  have bBounds := And.intro ((Fraction.Order.Basic.le_max_left _ _).trans rightBound)
    ((Fraction.Order.Basic.le_max_right _ _).trans rightBound)
  have leftLater := (Nat.Order.le_max_left _ _).trans (request.surface.stage_eq ▸ later)
  have rightLater := (Nat.Order.le_max_right _ _).trans (request.surface.stage_eq ▸ later)
  exact determinant_error
    request.budget.magnitude_nonnegative request.budget.row_positive.le
    request.budget.row_le_one
    (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      (((prepared.periodData.aProgram first index).integral.sample_bounded stage).trans aBounds.1))
    (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
      (((prepared.periodData.bProgram first index).integral.sample_bounded stage).trans bBounds.1))
    (by
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          using (((prepared.periodData.aProgram second index).integral.sample_bounded stage).trans aBounds.2))
    (by
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          using (((prepared.periodData.bProgram second index).integral.sample_bounded stage).trans bBounds.2))
    (request.surface.left.a_accurate index stage leftLater).le
    (request.surface.left.b_accurate index stage leftLater).le
    (request.surface.right.a_accurate index stage rightLater).le
    (request.surface.right.b_accurate index stage rightLater).le

/-- Arbitrary requested squared error for the actual finite period determinant versus the complete polarized surface
residual. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest prepared
  domains first second target minimumStage)
    (stage : Nat) (later : request.surface.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (BilinearIdentity.bilinearResidual prepared request.surface.left.value
      request.surface.right.value -
      determinant prepared first
        second stage) < target := by
  rw [← BilinearIdentity.bilinear_formula prepared _ _ request.surface.left.value_reverse
    request.surface.right.value_reverse,
    determinant,
    ← FiniteSum.Fin.sumFin_sub]
  have rowBound (index : Fin genus) := request.row_error index stage later
  have weightNonnegative : 0 ≤ 32 * (request.magnitude + 1) := Fraction.Order.Arithmetic.mul_nonneg_direct
    (by decide +kernel) (add_nonneg request.budget.magnitude_nonnegative (by decide))
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.budget.row_paid
    weightNonnegative).trans
    (WeightedAggregateBudget.weighted_perTerm_le request.budget.handle_positive weightNonnegative genus)
  have estimate := Indexed.normSq_sumFin_le _ _ (fun index => (rowBound index).trans paid)
  have total := Aggregate.count_mul_perTerm_lt request.budget.handle_positive genus
  have expanded : (genus : Fraction.Rational)^2 * Aggregate.perTerm request.budget.handleTarget genus =
      (genus : Fraction.Rational) * ((genus : Fraction.Rational) * Aggregate.perTerm request.budget.handleTarget genus)
        := by ring1
  have targetLe : request.budget.handleTarget ≤ target := by
    rw [request.budget.handleTarget_eq]
    exact Fraction.Order.Field.divide_le_self request.budget.positive.le (by decide +kernel)
  exact (estimate.trans_lt (expanded.trans_lt total)).trans_le targetLe

/-- The witness-sampled determinant and the model-level determinant at the same late stage differ by a
coefficient-independent geometric amount. Callers supply the four entry offsets (A first, B first, A second, B second).
-/
theorem witness_determinant_close (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest prepared domains first second target
  minimumStage)
    (stage : Nat)
    (witnessError : Fraction.Rational) (witness_nonnegative : 0 ≤ witnessError)
    (witness_small : witnessError ≤ 1)
    (boundA1 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.aProgram first differential).integral.errorScale 1) stage ≤ witnessError)
    (boundA2 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.aProgram second differential).integral.errorScale 1) stage ≤ witnessError)
    (boundB1 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.bProgram first differential).integral.errorScale 1) stage ≤ witnessError)
    (boundB2 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.bProgram second differential).integral.errorScale 1) stage ≤ witnessError) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index : Fin genus =>
        (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
          PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index) -
        (((prepared.periodData.aProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
          ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.aProgram second index).integral.model stage).integralSample))) ≤
      (genus : Fraction.Rational) * ((genus : Fraction.Rational) * (32 * (request.magnitude + 1) * witnessError)) := by
  have each (index : Fin genus) :
      Data.Gaussian.Norm.Basic.normSq ((PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first
        index *
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
          PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index) -
        (((prepared.periodData.aProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
          ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.aProgram second index).integral.model stage).integralSample)) ≤
      32 * (request.magnitude + 1) * witnessError := by
    have bound := request.row_le index
    change max (max _ _) (max _ _) ≤ request.magnitude at bound
    have leftBound := (Fraction.Order.Basic.le_max_left _ _).trans bound
    have rightBound := (Fraction.Order.Basic.le_max_right _ _).trans bound
    have aBounds := And.intro ((Fraction.Order.Basic.le_max_left _ _).trans leftBound)
      ((Fraction.Order.Basic.le_max_right _ _).trans leftBound)
    have bBounds := And.intro ((Fraction.Order.Basic.le_max_left _ _).trans rightBound)
      ((Fraction.Order.Basic.le_max_right _ _).trans rightBound)
    refine (determinant_error
      request.budget.magnitude_nonnegative witness_nonnegative witness_small
      (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        (((prepared.periodData.aProgram first index).integral.sample_bounded stage).trans aBounds.1))
      (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        (((prepared.periodData.bProgram first index).integral.sample_bounded stage).trans bBounds.1))
      (by
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
            using (((prepared.periodData.aProgram second index).integral.sample_bounded stage).trans aBounds.2))
      (by
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
            using (((prepared.periodData.bProgram second index).integral.sample_bounded stage).trans bBounds.2))
      ?_ ?_ ?_ ?_).trans_eq (by ring1)
    · exact (PeriodMatrix.sampledMatrix_aProgram_close prepared.periodData first index stage).trans (boundA1 index)
    · exact (PeriodMatrix.sampledMatrix_bProgram_close prepared.periodData first index stage).trans (boundB1 index)
    · exact (PeriodMatrix.sampledMatrix_aProgram_close prepared.periodData second index stage).trans (boundA2 index)
    · exact (PeriodMatrix.sampledMatrix_bProgram_close prepared.periodData second index stage).trans (boundB2 index)
  exact (Indexed.normSq_sumFin_le _ _ each).trans_eq (by ring1)

/-- The synchronized witness-level period determinant at a late stage is close to the exact corrected pairing
`bilinearResidual`. This composes the model convergence `accurate` with the witness offset. -/
theorem synchronized_determinant_close (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest prepared domains first second target
  minimumStage)
    (stage : Nat) (later : request.surface.stage ≤ stage)
    (witnessError : Fraction.Rational) (witness_nonnegative : 0 ≤ witnessError)
    (witness_small : witnessError ≤ 1)
    (boundA1 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.aProgram first differential).integral.errorScale 1) stage ≤ witnessError)
    (boundA2 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.aProgram second differential).integral.errorScale 1) stage ≤ witnessError)
    (boundB1 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.bProgram first differential).integral.errorScale 1) stage ≤ witnessError)
    (boundB2 : ∀ differential : Fin genus,
      Geometric.Basic.quarterRadius
        (max (prepared.periodData.bProgram second differential).integral.errorScale 1) stage ≤ witnessError) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index : Fin genus =>
        (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
          PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index)) -
      BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value) <
      2 * ((genus : Fraction.Rational) * ((genus : Fraction.Rational) * (32 * (request.magnitude + 1) * witnessError)) +
        target) := by
  have model := request.accurate stage later
  have witness := request.witness_determinant_close stage witnessError witness_nonnegative witness_small
    boundA1 boundA2 boundB1 boundB2
  have modelLe : Data.Gaussian.Norm.Basic.normSq
    (determinant prepared first second
    stage -
      BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value) < target := by
    have h : determinant prepared
      first second stage -
        BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value =
        -(BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value -
          determinant prepared first
            second stage) := by ring1
    rw [h, Data.Gaussian.Norm.Basic.normSq_neg]
    exact model
  have decomp : FiniteSum.Fin.sumFin (fun index : Fin genus =>
        (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
          PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index)) -
        BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value =
      (FiniteSum.Fin.sumFin (fun index : Fin genus =>
          (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
              PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
              PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index) -
          (((prepared.periodData.aProgram first index).integral.model stage).integralSample *
              ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
            ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
              ((prepared.periodData.aProgram second index).integral.model stage).integralSample))) +
      (determinant prepared first
        second stage -
        BilinearIdentity.bilinearResidual prepared request.surface.left.value request.surface.right.value) := by
    have hsub : FiniteSum.Fin.sumFin (fun index : Fin genus =>
        (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
          PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
            PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index) -
        (((prepared.periodData.aProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.bProgram second index).integral.model stage).integralSample -
          ((prepared.periodData.bProgram first index).integral.model stage).integralSample *
            ((prepared.periodData.aProgram second index).integral.model stage).integralSample)) =
        FiniteSum.Fin.sumFin (fun index : Fin genus =>
          (PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage first index *
              PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage second index -
            PeriodMatrix.sampledMatrix prepared.periodData.bMatrix stage first index *
              PeriodMatrix.sampledMatrix prepared.periodData.aMatrix stage second index)) -
          determinant prepared first
            second stage := by
      rw [determinant,
        FiniteSum.Fin.sumFin_sub]
    rw [hsub]
    ring1
  rw [decomp]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_direct witness (le_refl _)).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct modelLe _)))

end BilinearRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
