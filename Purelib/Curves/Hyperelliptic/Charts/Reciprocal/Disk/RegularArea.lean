module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat.Fraction.Order

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# Full area comparison with the signed shared cap primitive

The source/cap drift estimate controls every dyadic intermediate vertex.
Its ribbon estimate retains and pays the open endpoint correction, and the
resulting area request is independent of the additional spatial depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive (sourceValue
  sourceValue_left)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment (RegularAlignment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison.RegularAlignment (comparisonValue
  comparison_error)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea dyadicDifference)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    Data regular cell}
  {index : Nat} {box : Geometry.Rational.Box} {capSample :
    Cap.Primitives.Sample cap differential index box}
  {retained : Sample comparison capSample}

namespace Data

/-- The fixed full-area discrepancy scale for the retained signed shared cap primitive and original source slope. -/
@[expose] def regularAreaScale (comparison : Data regular cell) : Coordinate :=
  (Data.regularScale comparison) * (144 * data.sourceSlope + 160 *
    (Data.regularScale comparison))

/-- The retained source slope and signed regular comparison scale give a nonnegative area bound. -/
theorem regularAreaScale_nonnegative (comparison : Data regular cell) : 0 ≤
  (regularAreaScale comparison) :=
  Arithmetic.mul_nonneg_direct (Data.regularScale_nonnegative comparison)
    (add_nonneg (Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Data.regularScale_nonnegative
        comparison)))

end Data

namespace RegularAlignment

/-- The anchored value used to state the full inverse-arc area estimate. -/
@[expose] def capValue (sample : RegularAlignment retained) (parameter :
  Coordinate) : Gaussian :=
  sample.primitive.eval (parent.edge.point parameter)⁻¹ - sample.primitive.eval (parent.edge.point
    edge.left.parameter)⁻¹

/-- The anchored retained signed cap primitive vanishes at the original left endpoint. -/
theorem capValue_left (sample : RegularAlignment retained) :
  (capValue sample) edge.left.parameter = 0 :=
  by
  exact Data.Gaussian.Basic.sub_self _

/-- Read the retained signed shared cap primitive's increment across the actual inverse cell endpoints. -/
@[expose] def increment (sample : RegularAlignment retained) : Gaussian :=
  sample.primitive.eval (parent.edge.point edge.right.parameter)⁻¹ - sample.primitive.eval (parent.edge.point
    edge.left.parameter)⁻¹

/-- The anchored retained signed primitive reads back its original cell increment at the right endpoint. -/
theorem capValue_right (sample : RegularAlignment retained) :
  (capValue sample) edge.right.parameter =
  (increment sample) := by
  rfl

/-- The original source and retained signed shared primitive drift satisfies its geometric scale times squared
subinterval width. -/
theorem drift_bound (source : SourcePrimitive data index) (right :
  RegularAlignment retained)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Basic.normSq ((CellPrimitive.sourceValue source edge last -
      (capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (capValue right) first)) ≤
      quarterRadius (Data.regularScale comparison) index * (last - first) ^ 2 := by
  have identity : (CellPrimitive.sourceValue source edge last -
    (capValue right) last) -
      (CellPrimitive.sourceValue source edge first -
        (capValue right) first) =
      RegularAlignment.comparisonValue right source last - RegularAlignment.comparisonValue right source first := by
    dsimp only [CellPrimitive.sourceValue,
      capValue,
      RegularAlignment.comparisonValue]
    ring1
  rw [identity]
  exact RegularAlignment.comparison_error right source firstInside lastInside

/-- The anchored original source and retained signed cap value satisfy the original covered cell's geometric error
bound. -/
theorem point_error_bound (source : SourcePrimitive data index) (right :
  RegularAlignment retained)
    {parameter : Coordinate} (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter) :
    Basic.normSq (CellPrimitive.sourceValue source edge parameter -
      (capValue right) parameter) ≤
      quarterRadius (Data.regularScale comparison) index * (edge.right.parameter -
        edge.left.parameter) ^ 2 := by
  have estimate := drift_bound source right
    ⟨le_rfl, cell.ordered.le⟩ inside
  rw [CellPrimitive.sourceValue_left,
    capValue_left,
    Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.sub_zero] at estimate
  exact estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.pow_le_pow_direct (Arithmetic.sub_nonneg_direct inside.1)
      (Arithmetic.sub_le_sub_right_direct inside.2 _) 2)
    (quarterRadius_nonneg (Data.regularScale_nonnegative comparison) index))

/-- Each retained signed cap subarc increment satisfies the original source slope and regular discrepancy ceiling. -/
theorem cap_increment_bound (source : SourcePrimitive data index) (right :
  RegularAlignment retained)
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter) :
    Basic.normSq
      ((capValue right) last -
      (capValue right) first) ≤
      (2 * (data.sourceSlope + quarterRadius (Data.regularScale comparison) index)) *
        (last - first) ^ 2 := by
  have sourceBound : Basic.normSq (CellPrimitive.sourceValue source edge last -
    CellPrimitive.sourceValue source edge first) ≤ data.sourceSlope * (last - first) ^ 2 := by
    have identity : CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first =
        source.primitive.value.eval (parent.edge.point last) - source.primitive.value.eval (parent.edge.point first) :=
          by
      dsimp only [CellPrimitive.sourceValue]; ring1
    rw [identity]
    exact source.increment_bound ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans edge.right.inside.2⟩
      ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans edge.right.inside.2⟩
  have identity : (capValue right) last -
    (capValue right) first =
      (CellPrimitive.sourceValue source edge last - CellPrimitive.sourceValue source edge first) -
        ((CellPrimitive.sourceValue source edge last -
          (capValue right) last) -
          (CellPrimitive.sourceValue source edge first -
          (capValue right) first)) := by ring1
  rw [identity]
  exact (Bounds.normSq_sub_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add sourceBound (drift_bound
        source right firstInside lastInside)) (by decide)).trans_eq (by ring1))

/-- The complete finite ribbon retains its open endpoint correction. The bound is independent of the additional dyadic
spatial depth. -/
theorem ribbon_bound (source : SourcePrimitive data index) (right :
  RegularAlignment retained) (depth : Nat) :
    Basic.normSq (dyadicDifference (CellPrimitive.sourceValue source
      edge) (capValue right) depth
      edge.left.parameter edge.right.parameter) ≤
      8 * quarterRadius (Data.regularScale comparison) index * (8 * data.sourceSlope +
        9 * quarterRadius (Data.regularScale comparison) index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound (CellPrimitive.sourceValue source edge)
    (capValue right)
    (Arithmetic.mul_nonneg_direct (quarterRadius_nonneg
      (Data.regularScale_nonnegative comparison) index)
      (Arithmetic.sq_nonneg_direct _))
    (fun _ inside => point_error_bound source
      right inside)
    (fun _ _ firstInside lastInside =>
      cap_increment_bound source right
      firstInside lastInside)
    (fun _ _ firstInside lastInside =>
      drift_bound source right firstInside
      lastInside)
    depth ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩ cell.ordered.le
  exact estimate.trans_eq (by ring1)

/-- Paying, rather than dropping, the endpoint term compares the full anchored primitive areas. All intermediate dyadic
excursions are retained. -/
theorem area_error (source : SourcePrimitive data index) (right :
  RegularAlignment retained) (depth : Nat) :
    Basic.normSq (dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      dyadicArea (capValue
        right) depth edge.left.parameter edge.right.parameter) ≤
      quarterRadius (Data.regularScale comparison) index * (144 * data.sourceSlope +
        160 * quarterRadius (Data.regularScale comparison) index) *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
  let endpoint := area
    ((capValue right) edge.right.parameter)
    (CellPrimitive.sourceValue source edge edge.right.parameter -
      (capValue right) edge.right.parameter)
  have rightBound := cap_increment_bound source
    right
    ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le, le_rfl⟩
  rw [capValue_left,
    Data.Gaussian.Basic.sub_zero] at rightBound
  have endpointBound : Basic.normSq endpoint ≤
      8 * (data.sourceSlope + quarterRadius (Data.regularScale comparison) index) *
        quarterRadius (Data.regularScale comparison) index *
        (edge.right.parameter - edge.left.parameter) ^ 4 := by
    have multiplied := Arithmetic.mul_le_mul_direct rightBound
      (point_error_bound source right
        ⟨cell.ordered.le, le_rfl⟩) (Basic.normSq_nonneg _)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg data.sourceSlope_nonnegative (quarterRadius_nonneg
            (Data.regularScale_nonnegative comparison) index)))
        (Arithmetic.sq_nonneg_direct _))
    calc
      Basic.normSq endpoint ≤ 4 * Basic.normSq
        ((capValue right) edge.right.parameter)
        *
          Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (capValue right)
            edge.right.parameter) := area_bound _ _
      _ = 4 * (Basic.normSq
        ((capValue right) edge.right.parameter)
        *
          Basic.normSq (CellPrimitive.sourceValue source edge edge.right.parameter -
            (capValue right)
            edge.right.parameter)) := by ring1
      _ ≤ 4 * ((2 * (data.sourceSlope + quarterRadius (Data.regularScale comparison)
        index) * (edge.right.parameter - edge.left.parameter) ^ 2) *
          (quarterRadius (Data.regularScale comparison) index * (edge.right.parameter
            - edge.left.parameter) ^ 2)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct multiplied (by decide)
      _ = _ := by ring1
  have identity : dyadicArea (CellPrimitive.sourceValue source edge) depth edge.left.parameter
    edge.right.parameter -
      dyadicArea (capValue
        right) depth edge.left.parameter edge.right.parameter =
      dyadicDifference (CellPrimitive.sourceValue source edge)
        (capValue right) depth
        edge.left.parameter edge.right.parameter + endpoint := by
    rw [dyadicDifference, CellPrimitive.sourceValue_left,
      capValue_left]
    dsimp only [endpoint, area]
    ring1
  rw [identity]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (ribbon_bound source right
        depth) endpointBound) (by decide)).trans_eq (by ring1))

/-- A pre-index scale supplies the geometric area rate at every spatial depth. Increasing the inverse-model index
controls the entire local area, not merely the final integral. -/
theorem area_error_geometric (source : SourcePrimitive data index) (right :
  RegularAlignment retained) (depth : Nat) :
    Basic.normSq (dyadicArea (CellPrimitive.sourceValue source edge)
      depth edge.left.parameter edge.right.parameter -
      dyadicArea (capValue
        right) depth edge.left.parameter edge.right.parameter) ≤
      quarterRadius (Data.regularAreaScale
        comparison) index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  have errorLe : quarterRadius (Data.regularScale comparison) index ≤
    (Data.regularScale comparison) := by
    simpa only [quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (Data.regularScale_nonnegative comparison) (Nat.zero_le index)
  apply (area_error source right depth).trans
  have coefficient : quarterRadius (Data.regularScale comparison) index * (144 *
    data.sourceSlope + 160 * quarterRadius (Data.regularScale comparison) index) ≤
      quarterRadius (Data.regularScale comparison) index * (144 * data.sourceSlope +
        160 * (Data.regularScale comparison)) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel)))
      (quarterRadius_nonneg (Data.regularScale_nonnegative comparison) index)
  have identity : quarterRadius (Data.regularScale comparison) index * (144 *
    data.sourceSlope + 160 * (Data.regularScale comparison)) =
      quarterRadius (Data.regularAreaScale
        comparison) index := by
    rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow,
      Data.regularAreaScale]
    ring1
  rw [identity] at coefficient
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
    (Arithmetic.pow_nonneg_direct (Arithmetic.sub_nonneg_direct cell.ordered.le) 4)

end RegularAlignment

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
