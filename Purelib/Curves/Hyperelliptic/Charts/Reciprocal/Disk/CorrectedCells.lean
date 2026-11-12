module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Bounds.Quarter
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

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Bounds.Quarter (four_quarters)

open Purelib.Data.Gaussian.Norm

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
  HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    ArcSamples.Data regular cell}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index} {box
    : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {owners : ArcOwners.Endpoints cap cell} {bounds :
    PairData regular owners}
  {target : Coordinate} {request :
    PairRequest bounds target floor}
  {compared : ComparedCell comparison source capSample
    depth}

set_option genInjectivity false in
/-- The original fine cap path with two explicit endpoint corrections and its cached summary.

The incoming connector is retained in the first correction, and the summary preserves all original internal excursions
and cross terms. -/
structure CorrectedCell (compared : ComparedCell comparison source capSample depth)
    (reading : PairRequest.Evaluation request compared.sample readingIndex) (entry : Gaussian)
      where
  /-- The cached first endpoint correction including the original incoming connector. -/ first :
    Gaussian
  /-- The first correction is the original cap value minus the retained reading plus incoming connector. -/ first_eq :
    first = compared.sample.firstValue - reading.firstValue + entry
  /-- The cached original last endpoint correction. -/ last : Gaussian
  /-- The last correction is the retained endpoint reading minus the original cap endpoint value. -/ last_eq : last =
    reading.lastValue - compared.sample.lastValue
  /-- The cached summary of the original fine cap path between its two actual corrections. -/ summary :
    Summary (first :: (compared.capPath ++ [last]))
  /-- The summary reuses the original cap summary with the retained first correction prepended and last correction
    appended. -/ summary_eq : summary = (Summary.prepend compared.capSummary first).append (Summary.build
    [last])

constructive_injectivity CorrectedCell

namespace CorrectedCell

/-- Attach the two actual endpoint corrections to the cached original fine cap path without rebuilding its summary. -/
def build (compared : ComparedCell comparison source capSample depth)
    (reading : PairRequest.Evaluation request compared.sample readingIndex) (entry : Gaussian) :
      CorrectedCell compared reading entry :=
  let first := compared.sample.firstValue - reading.firstValue + entry
  let last := reading.lastValue - compared.sample.lastValue
  ⟨first, rfl, last, rfl, (Summary.prepend compared.capSummary first).append (Summary.build [last]), rfl⟩

variable {reading : PairRequest.Evaluation request
  compared.sample readingIndex} {entry : Gaussian}

/-- The corrected original cap block total is exactly the incoming connector plus retained endpoint increment. -/
theorem total (corrected : CorrectedCell compared reading
  entry) : corrected.summary.total = entry + reading.increment := by
  rw [corrected.summary_eq]
  change (corrected.first + compared.capSummary.total) + (corrected.last + 0) = _
  rw [compared.cap_total, compared.sample.increment_eq, corrected.first_eq, corrected.last_eq, reading.increment_eq]
  ring1

/-- A nonnegative original rational quarter-budget is bounded by its full budget. -/
private theorem quarter_le {value : Coordinate} (nonnegative : 0 ≤ value) : value / 4 ≤ value :=
  by
  apply (Field.div_le_iff_pos (by decide)).mpr
  simpa only [Fraction.Field.mul_one_direct] using
    Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Coordinate) ≤ 4)
      nonnegative

variable {tolerance : Coordinate} {request :
  PairRequest bounds (tolerance / 4) floor}
  {reading : PairRequest.Evaluation request
    compared.sample readingIndex}

/-- The original incoming connector and first endpoint discrepancy pay the retained first correction bound. -/
theorem first_bound (corrected : CorrectedCell compared
  reading entry) (nonnegative : 0 ≤ tolerance)
    (small : Basic.normSq entry ≤ tolerance / 4) : Basic.normSq
      corrected.first ≤ tolerance := by
  rw [corrected.first_eq]
  exact ((Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (reading.first_close.le.trans
      (quarter_le
      (Field.div_nonneg_direct nonnegative (by decide)))) small)
    (by decide))).trans_eq (four_quarters
      tolerance)

/-- The original final endpoint discrepancy pays the retained last correction bound. -/
theorem last_bound (corrected : CorrectedCell compared
  reading entry) (nonnegative : 0 ≤ tolerance) :
    Basic.normSq corrected.last ≤ tolerance := by
  rw [corrected.last_eq, show reading.lastValue - compared.sample.lastValue = -(compared.sample.lastValue -
    reading.lastValue) by ring1, Basic.normSq_neg]
  exact reading.last_close.le.trans
    ((quarter_le
    (Field.div_nonneg_direct nonnegative (by decide))).trans
    (quarter_le nonnegative))

/-- The corrected original total differs from its retained fine cap total by at most the paid tolerance. -/
theorem total_error (corrected : CorrectedCell compared
  reading entry) (small : Basic.normSq entry ≤ tolerance / 4) :
    Basic.normSq (corrected.summary.total - compared.capSummary.total) ≤ tolerance := by
  rw [corrected.total, compared.cap_total, show entry + reading.increment - compared.sample.increment =
    entry - (compared.sample.increment - reading.increment) by ring1]
  exact ((Bounds.normSq_sub_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add small reading.close.le) (by decide))).trans_eq
      (four_quarters tolerance)

/-- The corrected original total satisfies the retained cap magnitude bound plus paid discrepancy. -/
theorem total_bound (corrected : CorrectedCell compared
  reading entry) {bound : Coordinate}
    (small : Basic.normSq entry ≤ tolerance / 4) (bounded :
      Basic.normSq compared.capSummary.total ≤ bound) :
    Basic.normSq corrected.summary.total ≤ 2 * (bound + tolerance) := by
  rw [show corrected.summary.total = compared.capSummary.total + (corrected.summary.total - compared.capSummary.total)
    by ring1]
  exact (Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add bounded (corrected.total_error small)) (by decide))

/-- The original endpoint corrections change the retained fine cap area by the explicit tolerance and magnitude bound.
-/
theorem area_error (corrected : CorrectedCell compared
  reading entry) {bound : Coordinate}
    (nonnegative : 0 ≤ tolerance) (small : Basic.normSq entry ≤ tolerance / 4)
    (bounded : Basic.normSq compared.capSummary.total ≤ bound) :
    Basic.normSq (corrected.summary.area - compared.capSummary.area) ≤ 24 * tolerance *
      bound + 16 * tolerance ^ 2 := by
  have firstBound := corrected.first_bound nonnegative small
  have lastBound := corrected.last_bound nonnegative
  have totalBound := Summary.prepend_total_bound compared.capSummary corrected.first firstBound bounded
  have firstArea := Summary.prepend_area_error compared.capSummary corrected.first firstBound bounded
  have lastArea : Basic.normSq (area (Summary.prepend compared.capSummary
    corrected.first).total corrected.last) ≤
      4 * (2 * (tolerance + bound)) * tolerance := by
    have product := Arithmetic.mul_le_mul_direct totalBound lastBound
      (Basic.normSq_nonneg _)
      ((Basic.normSq_nonneg _).trans totalBound)
    calc
      _ ≤ 4 * Basic.normSq (Summary.prepend compared.capSummary corrected.first).total *
        Basic.normSq corrected.last := area_bound _ _
      _ = 4 * (Basic.normSq (Summary.prepend compared.capSummary corrected.first).total *
        Basic.normSq corrected.last) := by
        ring1
      _ ≤ 4 * (2 * (tolerance + bound) * tolerance) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)
      _ = _ := by ring1
  have difference : corrected.summary.area - (Summary.prepend compared.capSummary corrected.first).area =
      area (Summary.prepend compared.capSummary corrected.first).total corrected.last := by
    rw [corrected.summary_eq]
    change (_ + (0 + area corrected.last 0) + area _ (corrected.last + 0)) - _ = _
    simp only [IncrementArea.area_zero_right, Data.Gaussian.Basic.add_zero]
    ring1
  have lastPaid : Basic.normSq (corrected.summary.area - (Summary.prepend
    compared.capSummary corrected.first).area) ≤
      4 * (2 * (tolerance + bound)) * tolerance := by rw [difference]; exact lastArea
  have paid := (Bounds.normSq_sub_le_via corrected.summary.area (Summary.prepend compared.capSummary
    corrected.first).area compared.capSummary.area).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add lastPaid firstArea) (by decide))
  exact paid.trans_eq (by ring1)

end CorrectedCell
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
