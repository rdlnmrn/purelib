module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Bounds
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint.Bounds.Envelope
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Pre-mesh row ceilings for the same original shifted physical parent

The original parent patch computes its enlarged physical box and radicand
floor once. They determine one rational ceiling for all four derivative
rows on every actual acquired child, independently of its fine width,
child count, neighborhood coefficient count or later parameter increment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step (Joint)

/-- The original positive denominator value gives a positive quarter-of-quarter shifted floor. -/
private theorem originalFloor_positive {parameter : Canonical} {frame : Paths.Frame parameter}
    {basis : Differential 1} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (patch : PreparedPatch parent) (count : Nat) :
    0 < ((patch.neighborhood count).base.site.denominatorValue / 4) / 4 :=
  Order.Field.div_pos_direct
    (Order.Field.div_pos_direct (patch.neighborhood count).base.site.denominatorValue_positive
      (by decide +kernel : (0 : Rational) < 4))
    (by decide +kernel : (0 : Rational) < 4)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample increment} {width : AccuracyRequest}

/-- Every actual child value ceiling is paid by the original-parent envelope at every later increment index.

The actual entry patch supplies its own seed and cached rootLower. Its
original affine incidence, radius payment and retained residual derive
the fixed box/floor comparisons internally. No numerical H is an input.
-/
theorem child_valueCeiling_le
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (index : Fin retained.parents.covered.parents.length) (modelCount : Nat)
    (laterIncrement : Canonical) (coordinate : Fin 2) :
    Joint.valueCeiling ((retained.parents.coveredParents.entry index).val.neighborhood modelCount)
        laterIncrement coordinate ≤ Joint.shiftedEnvelopeCeiling (patch.neighborhood count) := by
  have bound := Joint.valueCeiling_le_box _ laterIncrement coordinate
    (retained.child_box_refines_enlarge index modelCount)
    (ContinuedNeighborhood.rootFloor_positive (originalFloor_positive patch count))
    (retained.child_rootLower_ge index modelCount)
  exact bound.trans_eq (Joint.shiftedEnvelopeCeiling_eq (patch.neighborhood count)
    (originalFloor_positive patch count)).symm

/-- Every actual child first ceiling, including its original inverse box, obeys the same pre-mesh envelope. -/
theorem child_firstCeiling_le
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (index : Fin retained.parents.covered.parents.length) (modelCount : Nat)
    (laterIncrement : Canonical) (coordinate : Fin 2) :
    Joint.firstCeiling ((retained.parents.coveredParents.entry index).val.neighborhood modelCount)
        laterIncrement coordinate ≤ Joint.shiftedEnvelopeCeiling (patch.neighborhood count) := by
  have bound := Joint.firstCeiling_le_box _ laterIncrement coordinate
    (retained.child_box_refines_enlarge index modelCount)
    (ContinuedNeighborhood.rootFloor_positive (originalFloor_positive patch count))
    (retained.child_rootLower_ge index modelCount)
  exact bound.trans_eq (Joint.shiftedEnvelopeCeiling_eq (patch.neighborhood count)
    (originalFloor_positive patch count)).symm

/-- Both orders and coordinates of every actual cached child have the same computed original-parent ceiling.

The constant depends only on the retained original parent patch and its
original coefficient count. It is independent of acquisition width,
adaptive child count, model count, observation stages and both parameter
increment indices; actual signed owner relations remain separate.
-/
theorem child_rowCeiling_le
    (retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width)
    (index : Fin retained.parents.covered.parents.length) (modelCount : Nat)
    (laterIncrement : Canonical) (order coordinate : Fin 2) :
    Joint.rowCeiling ((retained.parents.coveredParents.entry index).val.neighborhood modelCount)
        laterIncrement order coordinate ≤ Joint.shiftedEnvelopeCeiling (patch.neighborhood count) := by
  have bound := Joint.rowCeiling_le_box _ laterIncrement order coordinate
    (retained.child_box_refines_enlarge index modelCount)
    (ContinuedNeighborhood.rootFloor_positive (originalFloor_positive patch count))
    (retained.child_rootLower_ge index modelCount)
  exact bound.trans_eq (Joint.shiftedEnvelopeCeiling_eq (patch.neighborhood count)
    (originalFloor_positive patch count)).symm

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
