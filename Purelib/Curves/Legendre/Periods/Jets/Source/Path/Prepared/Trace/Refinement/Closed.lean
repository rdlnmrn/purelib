module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Primitive
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Signed return payment for actual source refinement on a closed old Spine

The original root-closed walk and the supplied old materialized path share
the same original prepared path and lineage. One actual closing comparison
pays its literal final-minus-initial contribution. Its old accuracy remains
charged alongside the original complete source-refinement charge; neither
old endpoint reading is replaced or assumed equal.

This bounds the actual selected source-row cell integral sum. Independent
geometric integral models, canonical cycle realization and arbitrary global
requested payment require their own comparison and allocation certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Compared

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
    {ambient : Box} {accuracy : AccuracyRequest}
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    {owner : Owner ((Paths.polynomial parameter).eval base)}
    (closed : RootClosedWalk grid base owner)
    (row : Row) (diameter : Rational) (positive : 0 < diameter) (request : AccuracyRequest)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner closed.traced.prepared))
    (factory : materialized = closed.traced.lineage.ownerPath)
    (observed : Primitive.Spine (row.expression parameter) accuracy materialized)
    (retained : Compared (frame := frame) (basis := basis) (count := count) (floor := floor) (targets := targets)
      row diameter positive request closed.traced.lineage centers materialized factory observed)

/-- Close this SAME actual source comparison and retain its genuine return join, old-reading comparison and payment.

The old materialized path has its exact factory on closed.traced.lineage,
so the return certificate concerns its actual original endpoint Owners.
Both old observation requests remain unchanged. The source integral bound
adds the actual old closing allowance to the existing counted refinement
charge; no arbitrary requested final bound or reading equality is input.
-/
def withClosing {Result : Type u}
    (consume :
      (retainedJoin : OwnerJoin closed.traced.finishOwner owner) →
      retainedJoin = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn →
      (join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner) →
      join = Eq.mp (congrArg (fun terminal : Owner ((Paths.polynomial parameter).eval base) =>
        OwnerJoin terminal owner) closed.traced.finishOwner_eq) retainedJoin →
      (compared : Primitive.Closing.Comparison observed join) →
      compared = Primitive.Closing.Comparison.build observed join →
      Norm.Basic.normSq retained.endpointContribution < accuracy.tolerance →
      Norm.Basic.normSq (gaussianSum retained.integrals) ≤
        2 * (((2 * retained.childCount + 3 * closed.traced.prepared.stepCount : Nat) : Rational) *
          retained.charge + accuracy.tolerance) → Result) : Result :=
  closed.withClosing materialized observed
    (fun retainedJoin joinFactory join indexFactory compared comparisonFactory => by
      have endpoint : observed.last.value - observed.first.value = -compared.jump := by
        rewrite [compared.jump_eq]
        ring1
      have endpointBound : Norm.Basic.normSq retained.endpointContribution < accuracy.tolerance :=
        ((congrArg Norm.Basic.normSq retained.endpointContribution_eq).trans
          ((congrArg Norm.Basic.normSq endpoint).trans (Norm.Basic.normSq_neg compared.jump))).trans_lt
            compared.jump_lt
      have original := compared.integral_le_return_residual (gaussianSum retained.integrals)
      have paid := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct retained.integral_error_le
          (Data.Rat.Fraction.Order.Basic.le_refl accuracy.tolerance))
        (by decide +kernel : (0 : Rational) ≤ 2)
      exact consume retainedJoin joinFactory join indexFactory compared comparisonFactory endpointBound
        ((original.trans paid).trans_eq (congrArg (fun count : Nat =>
          2 * ((count : Rational) * retained.charge + accuracy.tolerance)) retained.residualCount_eq)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Compared

end
