module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Riemann.Periods

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared
  VerticalPrepared)
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

open Purelib.Algebra.FiniteSum.Fin (sumFin)

/-- Bound a Gaussian triple sum over two face indices and a sheet by four times the fourth power of the face count and
the common squared-norm bound. -/
theorem CrossingTotal.triple_bound {n : Nat} (values : Fin n → Fin 2 → Fin n → Data.Gaussian.Basic.Canonical)
    (bound : Fraction.Rational) (bounded : ∀ a b c, Data.Gaussian.Norm.Basic.normSq (values a b c) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b =>
      FiniteSum.Fin.sumFin (values a b)))) ≤ 4 * (n : Fraction.Rational)^4 * bound := by
  have estimate := Indexed.normSq_sumFin_le _
    ((2 : Fraction.Rational)^2 * ((n : Fraction.Rational)^2 * bound)) (fun a =>
      Indexed.normSq_sumFin_le _ ((n : Fraction.Rational)^2 * bound) (fun b =>
        Indexed.normSq_sumFin_le (values a b) bound (bounded a b)))
  exact estimate.trans_eq (by ring1)

section CrossingRequests
variable {retained : CrossingBank request mesh}
  {allocated : CrossingRequests
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained}
  {cache : Numerics domains stage}

/-- The complete sum of horizontal crossing residuals over both retained face indices and the intermediate sheet. -/
@[expose] def
  CrossingSamples.CrossingRequests.Samples.horizontalTotal
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.Sample.residual (prepared := (((allocated.horizontal.get a).get b).get c)) (cache := cache)
      (((samples.horizontal.get a).get b).get c))))

/-- At a paid stage, the horizontal crossing total obeys the fourth-power face-count bound. -/
theorem
  CrossingSamples.CrossingRequests.Samples.horizontalTotal_bound
  (samples : CrossingRequests.Samples allocated cache) (positive : 0 < tolerance)
    (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq samples.horizontalTotal ≤ 4 * (faces.regulars.length : Fraction.Rational)^4
      * tolerance :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound _ tolerance (Samples.horizontal_bound
    allocated cache samples positive later)

/-- The complete sum of vertical crossing residuals over both retained face indices and the intermediate sheet. -/
@[expose] def
  CrossingSamples.CrossingRequests.Samples.verticalTotal
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.Sample.residual (prepared := (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c))))

/-- At a paid stage, the vertical crossing total obeys the fourth-power face-count bound. -/
theorem
  CrossingSamples.CrossingRequests.Samples.verticalTotal_bound
  (samples : CrossingRequests.Samples allocated cache) (positive : 0 < tolerance)
    (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq samples.verticalTotal ≤ 4 * (faces.regulars.length : Fraction.Rational)^4 *
      tolerance :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.triple_bound _ tolerance (Samples.vertical_bound
    allocated cache samples positive later)

/-- The signed crossing correction, vertical residual total minus horizontal residual total. -/
@[expose] def
  CrossingSamples.CrossingRequests.Samples.total
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  samples.verticalTotal - samples.horizontalTotal

/-- The signed crossing correction has squared norm at most sixteen times the fourth power of the face count and the
positive per-entry tolerance. -/
theorem
  CrossingSamples.CrossingRequests.Samples.total_bound
  (samples : CrossingRequests.Samples allocated cache) (positive : 0 < tolerance)
    (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq samples.total ≤ 16 * (faces.regulars.length : Fraction.Rational)^4 *
      tolerance := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two
    samples.verticalTotal samples.horizontalTotal).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.verticalTotal_bound
      samples positive later)
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.horizontalTotal_bound
        samples positive later)) (show (0 : Fraction.Rational) ≤ 2 by decide))
  exact estimate.trans_eq (by ring1)

set_option genInjectivity false in
/-- A paid request for the complete signed crossing correction.

It retains the two differential indices, parent sheets, crossing bank and a positive per-entry allowance fitting the
aggregate target. -/
structure CrossingTotal.CrossingRequests.TotalRequest (retained : CrossingBank request mesh) (i j : Fin
  genus)
    (firstParent secondParent : Fin 2) (target : Fraction.Rational) (floor : Nat) where
  /-- The positive allowance shared by the retained crossing entries. -/ perEntry : Fraction.Rational
  /-- The retained per-entry allowance is strictly positive. -/ positive : 0 < perEntry
  /-- The fourth-power crossing-count weight fits the aggregate target. -/ paid : 16 * (faces.regulars.length :
    Fraction.Rational)^4 * perEntry ≤ target
  /-- The actual crossing requests on the retained bank and standard differential pair. -/ allocated :
    CrossingRequests (PeriodMatrix.standardDifferential i) (PeriodMatrix.standardDifferential j)
    firstParent secondParent perEntry floor retained

constructive_injectivity CrossingTotal.CrossingRequests.TotalRequest

/-- The crossing aggregation weight is nonnegative for every finite face count. -/
public theorem CrossingTotal.CrossingRequests.weight_nonnegative (count : Nat) : (0 : Fraction.Rational) ≤ 16 * (count
  : Fraction.Rational)^4 := by
  have equal : (16 : Fraction.Rational) * (count : Fraction.Rational)^4 = 16 * ((count : Fraction.Rational)^2)^2 := by
    ring1
  rw [equal]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Allocate the positive weighted crossing allowance and prepare its requests on the retained bank. -/
@[expose] def CrossingTotal.CrossingRequests.TotalRequest.build (retained : CrossingBank request mesh) (i j
  : Fin genus)
    (firstParent secondParent : Fin 2) (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent target floor := by
  let perEntry := Weighted.allowance target (16 * (faces.regulars.length : Fraction.Rational)^4)
  have entryPositive := Weighted.allowance_positive positive
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.weight_nonnegative
    faces.regulars.length)
  exact ⟨perEntry, entryPositive,
    Weighted.mul_allowance_le positive.le
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.weight_nonnegative
      faces.regulars.length),
    CrossingRequests.build (PeriodMatrix.standardDifferential i) (PeriodMatrix.standardDifferential j)
      firstParent secondParent perEntry floor retained entryPositive⟩

/-- The paid crossing request bounds the actual signed residual total by its aggregate target. -/
theorem CrossingTotal.CrossingRequests.TotalRequest.bound {target : Fraction.Rational}
    (total : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests.TotalRequest retained i j
      firstParent secondParent target floor)
    (samples : CrossingRequests.Samples total.allocated cache) (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq samples.total ≤ target :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.total_bound samples
    total.positive later).trans total.paid

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
