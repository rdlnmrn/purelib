module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
public import Purelib.Integration.Path.IncrementAreaJoins
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.IncrementAreaJoins

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Literal cap blocks with their retained endpoint corrections

The full original fine cap path is kept between two explicit corrections.
An incoming junction is combined with the first correction. Cached summaries
retain every internal excursion and cross term, and the resulting block has
exactly the incoming connector plus the retained endpoint increment as total.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells (ComparedCell)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)

variable {genus count index depth readingIndex floor : Nat} {curve :
  Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index} {box
    : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {owners : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Endpoints cap cell} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest bounds target floor}
  {compared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

set_option genInjectivity false in
/-- The original fine cap path with two explicit endpoint corrections and its cached summary.

The incoming connector is retained in the first correction, and the summary preserves all original internal excursions
and cross terms. -/
structure CorrectedCell (compared : ParentCells.ComparedCell comparison source capSample depth)
    (reading : PairRequest.Evaluation request compared.sample readingIndex) (entry : InverseRootPolynomial.Gaussian)
      where
  /-- The cached first endpoint correction including the original incoming connector. -/ first :
    InverseRootPolynomial.Gaussian
  /-- The first correction is the original cap value minus the retained reading plus incoming connector. -/ first_eq :
    first = compared.sample.firstValue - reading.firstValue + entry
  /-- The cached original last endpoint correction. -/ last : InverseRootPolynomial.Gaussian
  /-- The last correction is the retained endpoint reading minus the original cap endpoint value. -/ last_eq : last =
    reading.lastValue - compared.sample.lastValue
  /-- The cached summary of the original fine cap path between its two actual corrections. -/ summary :
    IncrementArea.Summary (first :: (compared.capPath ++ [last]))
  /-- The summary reuses the original cap summary with the retained first correction prepended and last correction
    appended. -/ summary_eq : summary = (Summary.prepend compared.capSummary first).append (IncrementArea.Summary.build
    [last])

constructive_injectivity CorrectedCell

namespace CorrectedCell

/-- Attach the two actual endpoint corrections to the cached original fine cap path without rebuilding its summary. -/
def build (compared : ParentCells.ComparedCell comparison source capSample depth)
    (reading : PairRequest.Evaluation request compared.sample readingIndex) (entry : InverseRootPolynomial.Gaussian) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared reading entry :=
  let first := compared.sample.firstValue - reading.firstValue + entry
  let last := reading.lastValue - compared.sample.lastValue
  ⟨first, rfl, last, rfl, (Summary.prepend compared.capSummary first).append (IncrementArea.Summary.build [last]), rfl⟩

variable {reading : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request
  compared.sample readingIndex} {entry : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

/-- The corrected original cap block total is exactly the incoming connector plus retained endpoint increment. -/
theorem total (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared reading
  entry) : corrected.summary.total = entry + reading.increment := by
  rw [corrected.summary_eq]
  change (corrected.first + compared.capSummary.total) + (corrected.last + 0) = _
  rw [compared.cap_total, compared.sample.increment_eq, corrected.first_eq, corrected.last_eq, reading.increment_eq]
  ring1

/-- A nonnegative original rational quarter-budget is bounded by its full budget. -/
private theorem quarter_le {value : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ value) : value / 4 ≤ value :=
  by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
  simpa only [Fraction.Field.mul_one_direct] using
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : InverseRootPolynomial.Coordinate) ≤ 4)
      nonnegative

/-- Two pairs of original quarter-budgets combine to the full rational allowance. -/
private theorem four_quarters (value : InverseRootPolynomial.Coordinate) : 2 * (value / 4 + value / 4) = value := by
  rw [show 2 * (value / 4 + value / 4) = value / 4 * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

variable {tolerance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest bounds (tolerance / 4) floor}
  {reading : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request
    compared.sample readingIndex}

/-- The original incoming connector and first endpoint discrepancy pay the retained first correction bound. -/
theorem first_bound (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared
  reading entry) (nonnegative : 0 ≤ tolerance)
    (small : Data.Gaussian.Norm.Basic.normSq entry ≤ tolerance / 4) : Data.Gaussian.Norm.Basic.normSq
      corrected.first ≤ tolerance := by
  rw [corrected.first_eq]
  exact ((Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (reading.first_close.le.trans
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.quarter_le
      (Fraction.Order.Field.div_nonneg_direct nonnegative (by decide)))) small)
    (by decide))).trans_eq (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.four_quarters
      tolerance)

/-- The original final endpoint discrepancy pays the retained last correction bound. -/
theorem last_bound (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared
  reading entry) (nonnegative : 0 ≤ tolerance) :
    Data.Gaussian.Norm.Basic.normSq corrected.last ≤ tolerance := by
  rw [corrected.last_eq, show reading.lastValue - compared.sample.lastValue = -(compared.sample.lastValue -
    reading.lastValue) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  exact reading.last_close.le.trans
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.quarter_le
    (Fraction.Order.Field.div_nonneg_direct nonnegative (by decide))).trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.quarter_le nonnegative))

/-- The corrected original total differs from its retained fine cap total by at most the paid tolerance. -/
theorem total_error (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared
  reading entry) (small : Data.Gaussian.Norm.Basic.normSq entry ≤ tolerance / 4) :
    Data.Gaussian.Norm.Basic.normSq (corrected.summary.total - compared.capSummary.total) ≤ tolerance := by
  rw [corrected.total, compared.cap_total, show entry + reading.increment - compared.sample.increment =
    entry - (compared.sample.increment - reading.increment) by ring1]
  exact ((Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add small reading.close.le) (by decide))).trans_eq
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.four_quarters tolerance)

/-- The corrected original total satisfies the retained cap magnitude bound plus paid discrepancy. -/
theorem total_bound (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared
  reading entry) {bound : InverseRootPolynomial.Coordinate}
    (small : Data.Gaussian.Norm.Basic.normSq entry ≤ tolerance / 4) (bounded :
      Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq corrected.summary.total ≤ 2 * (bound + tolerance) := by
  rw [show corrected.summary.total = compared.capSummary.total + (corrected.summary.total - compared.capSummary.total)
    by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add bounded (corrected.total_error small)) (by decide))

/-- The original endpoint corrections change the retained fine cap area by the explicit tolerance and magnitude bound.
-/
theorem area_error (corrected : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell compared
  reading entry) {bound : InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ tolerance) (small : Data.Gaussian.Norm.Basic.normSq entry ≤ tolerance / 4)
    (bounded : Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (corrected.summary.area - compared.capSummary.area) ≤ 24 * tolerance *
      bound + 16 * tolerance ^ 2 := by
  have firstBound := corrected.first_bound nonnegative small
  have lastBound := corrected.last_bound nonnegative
  have totalBound := Summary.prepend_total_bound compared.capSummary corrected.first firstBound bounded
  have firstArea := Summary.prepend_area_error compared.capSummary corrected.first firstBound bounded
  have lastArea : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (Summary.prepend compared.capSummary
    corrected.first).total corrected.last) ≤
      4 * (2 * (tolerance + bound)) * tolerance := by
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct totalBound lastBound
      (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans totalBound)
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq (Summary.prepend compared.capSummary corrected.first).total *
        Data.Gaussian.Norm.Basic.normSq corrected.last := BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq (Summary.prepend compared.capSummary corrected.first).total *
        Data.Gaussian.Norm.Basic.normSq corrected.last) := by
        ring1
      _ ≤ 4 * (2 * (tolerance + bound) * tolerance) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)
      _ = _ := by ring1
  have difference : corrected.summary.area - (Summary.prepend compared.capSummary corrected.first).area =
      BoundaryRibbon.area (Summary.prepend compared.capSummary corrected.first).total corrected.last := by
    rw [corrected.summary_eq]
    change (_ + (0 + BoundaryRibbon.area corrected.last 0) + BoundaryRibbon.area _ (corrected.last + 0)) - _ = _
    simp only [IncrementArea.area_zero_right, Data.Gaussian.Basic.add_zero]
    ring1
  have lastPaid : Data.Gaussian.Norm.Basic.normSq (corrected.summary.area - (Summary.prepend
    compared.capSummary corrected.first).area) ≤
      4 * (2 * (tolerance + bound)) * tolerance := by rw [difference]; exact lastArea
  have paid := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via corrected.summary.area (Summary.prepend compared.capSummary
    corrected.first).area compared.capSummary.area).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add lastPaid firstArea) (by decide))
  exact paid.trans_eq (by ring1)

end CorrectedCell
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
