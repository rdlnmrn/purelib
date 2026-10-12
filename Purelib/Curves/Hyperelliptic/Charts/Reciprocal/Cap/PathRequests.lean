module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring

public section

/-!
# Retained sample banks for complete cap-side requests

Retain every local request and its integration block before selecting the
common model floor. Evaluation reuses those blocks in the original order.
Finite Cauchy--Schwarz pays both occurrences of the parent count for the
downstream chart and area requests.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent Bank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}

namespace Bank

/-- Local primitive requests retained on the original cap path bank.

The dependent product follows the original parent order and keeps each parent's exact target and floor. -/
@[expose] public def Requests : {parents : List (PathCover.Parent curve differential)} → PathCover.Bank cap differential
  count parents →
    InverseRootPolynomial.Coordinate → Nat → Type 3
  | _, .nil, _, _ => PUnit
  | _, .cons data remaining, target, floor =>
      PreparedPrimitives.Request data target floor ×
        Requests remaining target floor

namespace Requests

/-- Request each original parent once at the common target and floor, retaining its original properness witness. -/
@[expose] public def build : {parents : List (PathCover.Parent curve differential)} → (bank : PathCover.Bank cap
  differential count parents) →
    (target : InverseRootPolynomial.Coordinate) → 0 < target → (floor : Nat) →
      PreparedDyadicRefinements.AllParentsProper parents →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor
  | _, .nil, _, _, _, _ => ⟨⟩
  | _, .cons data remaining, target, positive, floor, proper =>
      ⟨PreparedPrimitives.Request.build data target positive floor proper.1,
        build remaining target positive
        floor proper.2⟩

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests
/-- The common model stage is the maximum of all retained local request stages and the original floor. -/
@[expose] public def index : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor → Nat
  | _, .nil, _, floor, _ => floor
  | _, .cons _ _, _, _, requests => max requests.1.index (index requests.2)

/-- The retained common model stage is at least the original request floor. -/
theorem floor_le : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential
  count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → (requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor) → floor ≤ index requests
  | _, .nil, _, _, _ => Nat.le_refl _
  | _, .cons _ _, _, _, requests => requests.1.floor_le.trans (Purelib.Data.Nat.Order.le_max_left _ _)

end Requests

/-- Evaluated local requests on one shared cap sample.

Each factor retains its original integration block and belongs to the corresponding original parent request. -/
@[expose] public def Samples {index : Nat} {box : Rational.Box} : {parents : List (PathCover.Parent
  curve differential)} →
    {bank : PathCover.Bank cap differential count parents} → {target : InverseRootPolynomial.Coordinate} → {floor : Nat}
      →
    Requests bank target floor → Primitives.Sample cap
      differential index box → Type 3
  | _, .nil, _, _, _, _ => PUnit
  | _, .cons _ _, _, _, requests, capSample =>
      PreparedPrimitives.Sample requests.1 capSample ×
        Samples requests.2 capSample

namespace Samples

/-- Evaluate all retained parent requests on the same later cap sample without rebuilding their integration blocks. -/
@[expose] public def build {index : Nat} {box : Rational.Box} : {parents : List (PathCover.Parent curve
  differential)} →
    {bank : PathCover.Bank cap differential count parents} → {target : InverseRootPolynomial.Coordinate} → {floor : Nat}
      →
    (requests : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor) → (capSample :
      Primitives.Sample cap differential index box) →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests.index requests ≤ index →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample
  | _, .nil, _, _, _, _, _ => ⟨⟩
  | _, .cons _ _, _, _, requests, capSample, later =>
      ⟨PreparedPrimitives.Sample.build requests.1 capSample ((Purelib.Data.Nat.Order.le_max_left _ _).trans later),
        build requests.2 capSample
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Extract the actual retained blocks without running their preparation again. -/
@[expose] public def blocks {index : Nat} {box : Rational.Box} {capSample : Primitives.Sample cap
  differential index box} :
    {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Requests bank target floor} →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank.Samples requests capSample →
      PreparedDirectDyadicRefinements.DirectBlockRefinement parents
  | _, .nil, _, _, _, _ => .nil
  | _, .cons _ _, _, _, _, samples => .cons samples.1.integration.block
    (blocks samples.2)

end Samples

end Bank

/-- The sum of paired row differences is the difference of their original component sums. -/
private theorem row_error_sum (rows : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map (fun row => row.1 - row.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map Prod.fst) - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (rows.map Prod.snd) := by
  induction rows with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons row rows previous =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, previous]
      ring1

/-- A common row-error ceiling bounds the sum of squared row errors by the exact finite row count. -/
private theorem row_norm_sum_le (rows : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) (bound :
  InverseRootPolynomial.Coordinate)
    (bounded : ∀ row ∈ rows, Data.Gaussian.Norm.Basic.normSq (row.1 - row.2) ≤ bound) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (rows.map (fun row => row.1 - row.2)) ≤ (rows.length :
      InverseRootPolynomial.Coordinate) * bound := by
  induction rows with
  | nil => change (0 : InverseRootPolynomial.Coordinate) ≤ 0 * bound; exact le_of_eq (by ring1)
  | cons row rows previous =>
      have tail := previous (fun other member => bounded other (List.mem_cons_of_mem _ member))
      have scalar := bounded row (List.mem_cons_self ..)
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      change Data.Gaussian.Basic.Canonical.normSq (row.1 - row.2) + Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum
        (rows.map (fun row => row.1 - row.2)) ≤ _
      apply (Fraction.Order.Arithmetic.add_le_add_direct scalar tail).trans_eq
      simp only [List.length_cons, Purelib.Algebra.NatCast.add, Nat.cast_one]
      ring1

/-- A common row-error ceiling bounds the squared difference of component sums by the squared finite row count. -/
theorem row_error_le (rows : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) (bound :
  InverseRootPolynomial.Coordinate)
    (bounded : ∀ row ∈ rows, Data.Gaussian.Norm.Basic.normSq (row.1 - row.2) ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map Prod.fst) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.map Prod.snd)) ≤ (rows.length :
      InverseRootPolynomial.Coordinate) ^ 2 * bound := by
  have sum := Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (rows.map (fun row => row.1 - row.2))
  rw [row_error_sum, Purelib.Data.List.Map.length_map] at sum
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply (sum.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (row_norm_sum_le rows bound bounded)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))).trans_eq
  ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
