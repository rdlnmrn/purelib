module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OddExteriorWeights
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! One cached exterior allowance pays both original A/B coefficients. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {aRows bRows : List (Int × List (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))}

set_option genInjectivity false in
/-- A common positive exterior allowance paying the two original weighted boundary coefficients.

The actual Gaussian coefficient casts and their squared norms are cached, and both weighted errors are bounded by one
quarter of the original target. -/
structure TwoExteriorBudget (a : PhysicalLoopSplit lifted aRows) (b :
  PhysicalLoopSplit lifted bRows)
    (target : SewnPrimitiveFaces.Coordinate) where
  /-- The cached Gaussian cast of the original A exterior coefficient. -/ aValue : Data.Gaussian.Basic.Canonical
  /-- The cached A value is exactly the original exterior coefficient cast. -/ aValue_eq : aValue =
    (a.exteriorCoefficient : Data.Gaussian.Basic.Canonical)
  /-- The cached Gaussian cast of the original B exterior coefficient. -/ bValue : Data.Gaussian.Basic.Canonical
  /-- The cached B value is exactly the original exterior coefficient cast. -/ bValue_eq : bValue =
    (b.exteriorCoefficient : Data.Gaussian.Basic.Canonical)
  /-- The cached squared norm of the retained A coefficient value. -/ aNorm : SewnPrimitiveFaces.Coordinate
  /-- The cached A norm reads that exact original retained Gaussian coefficient. -/ aNorm_eq : aNorm =
    Data.Gaussian.Norm.Basic.normSq aValue
  /-- The cached squared norm of the retained B coefficient value. -/ bNorm : SewnPrimitiveFaces.Coordinate
  /-- The cached B norm reads that exact original retained Gaussian coefficient. -/ bNorm_eq : bNorm =
    Data.Gaussian.Norm.Basic.normSq bValue
  /-- The cached sum of the two original coefficient squared norms plus one. -/ coefficient :
    SewnPrimitiveFaces.Coordinate
  /-- The common denominator is exactly the two retained squared norms plus one. -/ coefficient_eq : coefficient = aNorm
    + bNorm + 1
  /-- The retained common exterior allowance for both original rows. -/ allowance : SewnPrimitiveFaces.Coordinate
  /-- The allowance is one quarter of the target divided by the retained common denominator. -/ allowance_eq : allowance
    = (target / 4) / coefficient
  /-- The retained common allowance is strictly positive. -/ positive : 0 < allowance
  /-- The retained allowance pays the original A coefficient weight within one quarter of the requested target. -/ aPaid
    : (aNorm + 1) * allowance ≤ target / 4
  /-- The retained allowance pays the original B coefficient weight within one quarter of the requested target. -/ bPaid
    : (bNorm + 1) * allowance ≤ target / 4

constructive_injectivity TwoExteriorBudget

namespace TwoExteriorBudget

/-- Two nonnegative coefficient norms share a positive allowance that pays each weighted error within one quarter of the
target. -/
theorem pay {a b target : SewnPrimitiveFaces.Coordinate} (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (positive : 0 < target) :
    0 < (target / 4) / (a + b + 1) ∧
      (a + 1) * ((target / 4) / (a + b + 1)) ≤ target / 4 ∧
      (b + 1) * ((target / 4) / (a + b + 1)) ≤ target / 4 := by
  have denominatorPositive : 0 < a + b + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (add_nonneg aNonnegative bNonnegative) (by decide)
  have smallPositive := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : SewnPrimitiveFaces.Coordinate) < 4))
      denominatorPositive
  have exactPayment : (a + b + 1) * ((target / 4) / (a + b + 1)) = target / 4 :=
    (by
        ring1 : (a + b + 1) * ((target / 4) / (a + b + 1)) = ((target / 4) / (a + b + 1)) * (a + b + 1)).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')
  have aLe : a + 1 ≤ a + b + 1 := Fraction.Order.Arithmetic.add_le_add_direct (((Fraction.Field.zero_add
    a).symm.trans_le (Fraction.Order.Arithmetic.add_le_add_right_direct bNonnegative a)).trans_eq
    (Fraction.Field.add_comm b a)) (le_refl 1)
  have bLe : b + 1 ≤ a + b + 1 := Fraction.Order.Arithmetic.add_le_add_direct ((Fraction.Field.zero_add b).symm.trans_le
    (Fraction.Order.Arithmetic.add_le_add_right_direct aNonnegative b)) (le_refl 1)
  exact ⟨smallPositive,
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct aLe smallPositive.le).trans_eq exactPayment,
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bLe smallPositive.le).trans_eq exactPayment⟩

/-- Cache the actual original A and B exterior coefficient casts and norms, then construct their single paid exterior
allowance. -/
@[expose] def build (a : PhysicalLoopSplit lifted aRows) (b : PhysicalLoopSplit
  lifted bRows)
    (target : SewnPrimitiveFaces.Coordinate) (positive : 0 < target) :
      TwoExteriorBudget a b target :=
  let aValue := WeightedPeriods.integer a.exteriorCoefficient
  let bValue := WeightedPeriods.integer b.exteriorCoefficient
  let aNorm := Data.Gaussian.Norm.Basic.normSq aValue
  let bNorm := Data.Gaussian.Norm.Basic.normSq bValue
  let coefficient := aNorm + bNorm + 1
  let allowance := (target / 4) / coefficient
  have paid := pay
    (Data.Gaussian.Norm.Basic.normSq_nonneg aValue) (Data.Gaussian.Norm.Basic.normSq_nonneg bValue) positive
  ⟨aValue, WeightedPeriods.integer_eq _, bValue, WeightedPeriods.integer_eq _,
    aNorm, rfl, bNorm, rfl, coefficient, rfl, allowance, rfl, paid.1, paid.2.1, paid.2.2⟩

variable {a : PhysicalLoopSplit lifted aRows} {b :
  PhysicalLoopSplit lifted bRows} {target :
  Coordinate}

/-- The original A exterior coefficient weight times the retained allowance is at most one quarter of the target. -/
theorem a_paid (budget : TwoExteriorBudget a b target) :
    (Data.Gaussian.Norm.Basic.normSq (a.exteriorCoefficient : Data.Gaussian.Basic.Canonical) + 1) *
      budget.allowance ≤ target / 4 := by
  have equal := budget.aNorm_eq.trans (congrArg Data.Gaussian.Norm.Basic.normSq budget.aValue_eq)
  exact (congrArg (fun scalar => (scalar + 1) * budget.allowance) equal).symm.trans_le budget.aPaid

/-- The original B exterior coefficient weight times the retained allowance is at most one quarter of the target. -/
theorem b_paid (budget : TwoExteriorBudget a b target) :
    (Data.Gaussian.Norm.Basic.normSq (b.exteriorCoefficient : Data.Gaussian.Basic.Canonical) + 1) *
      budget.allowance ≤ target / 4 := by
  have equal := budget.bNorm_eq.trans (congrArg Data.Gaussian.Norm.Basic.normSq budget.bValue_eq)
  exact (congrArg (fun scalar => (scalar + 1) * budget.allowance) equal).symm.trans_le budget.bPaid

/-- One canonical boundary estimate pays both original weighted rows. -/
theorem accurate (budget : TwoExteriorBudget a b target)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (small : Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value
      lifted.exteriorBoundaries.flatten) < budget.allowance) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (a.exterior.map (fun entry
      =>
      (entry.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2))) < target / 4 ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (b.exterior.map (fun entry
      =>
      (entry.1 : Data.Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2))) < target / 4 :=
  ⟨(a.odd_bound branch value budget.positive small).trans_le budget.a_paid,
    (b.odd_bound branch value budget.positive small).trans_le budget.b_paid⟩

end TwoExteriorBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
