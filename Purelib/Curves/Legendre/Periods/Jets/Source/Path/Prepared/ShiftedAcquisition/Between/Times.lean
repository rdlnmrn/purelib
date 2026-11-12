module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Computed absolute-time payments on one original retained source query

One genuine strip admission pays every finite selected absolute time.
Both later roots are continuations of the same old query; the difference
of their offsets has the local unit bound required by the original Taylor
constructor, including zero-width and constant-direction cases.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

/-- Two exact absolute scalar offsets differ by their original time width times the SAME direction. -/
theorem interpolated_difference (first last : Rational) (direction : Canonical) :
    (⟨last, 0⟩ : Canonical) * direction - (⟨first, 0⟩ : Canonical) * direction =
      (⟨last - first, 0⟩ : Canonical) * direction := by
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Any ordered two times in the same original unit interval give a locally unit-admitted offset difference.

The sole actual strip payment is the original total-direction admission.
No actual later patch, changed Range, selected-node minimum or local-step
admission is assumed. This quantitative law includes zero width/direction.
-/
theorem interpolated_difference_unit
    {parameter direction : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (admitted : Norm.Basic.normSq direction ≤ range.stripBound)
    (first last : Rational) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1)
    (ordered : first ≤ last) :
    Norm.Basic.normSq ((⟨last, 0⟩ : Canonical) * direction - (⟨first, 0⟩ : Canonical) * direction) ≤ 1 := by
  have width : 0 ≤ last - first ∧ last - first ≤ 1 :=
    ⟨Order.Arithmetic.sub_nonneg_direct ordered,
      (Order.Arithmetic.sub_le_sub_direct lastInside.2 firstInside.1).trans_eq (by ring1)⟩
  have scalar : Norm.Basic.normSq (⟨last - first, 0⟩ : Canonical) ≤ 1 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact RationalEmbedding.Bounds.unit_parameter width.1 width.2
  have multiplied := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalar (Norm.Basic.normSq_nonneg direction)
  have directionUnit : Norm.Basic.normSq direction ≤ 1 :=
    admitted.trans (range.stripBound_le_shiftedBound.trans
      (range.shiftedBound_le_bound.trans (Order.Basic.min_le_left _ _)))
  exact (congrArg Norm.Basic.normSq (interpolated_difference first last direction)).trans_le
    ((Norm.Basic.normSq_mul _ _).trans_le
      ((multiplied.trans_eq (Field.one_mul _)).trans directionUnit))

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- Materialize both actual absolute-time Steps with their whole factories from ONE original strip admission.

The supplied old observation is not queried again. Both independent
parameter continuations consume that identical original Point, then retain
their original advanceRetained factory equations. Absolute time containment,
rather than a desired later-patch step payment, proves both admissions.
-/
def absoluteStepsAtTimes
    {parameter direction : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (admitted : Norm.Basic.normSq direction ≤ range.stripBound)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)
    (observed : CellModels.Observations frame (liftedCell parent)
      prepared.preparation.cell.models prepared.preparation.query.requests time)
    (observed_eq : observed = prepared.preparation.query.observe frame time inside.1 inside.2)
    (first last : Rational) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    let firstOffset := (⟨first, 0⟩ : Canonical) * direction
    let lastOffset := (⟨last, 0⟩ : Canonical) * direction
    let firstPaid := (range.interpolated_admitted first firstInside direction admitted).trans
      (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)
    let lastPaid := (range.interpolated_admitted last lastInside direction admitted).trans
      (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound)
    { firstStep : Variation.Point.Step observed.retained.sample firstOffset //
      firstStep = prepared.advanceRetained range time inside observed observed_eq firstOffset firstPaid } ×
    { lastStep : Variation.Point.Step observed.retained.sample lastOffset //
      lastStep = prepared.advanceRetained range time inside observed observed_eq lastOffset lastPaid } :=
  prepared.absoluteSteps range time inside observed observed_eq _ _
    ((range.interpolated_admitted first firstInside direction admitted).trans
      (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound))
    ((range.interpolated_admitted last lastInside direction admitted).trans
      (range.stripBound_le_shiftedBound.trans range.shiftedBound_le_bound))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
