module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.DyadicPairedIncrementComparison
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-! Conjugate comparison on the complete retained increment lists. -/
namespace Purelib.Integration.Path.DyadicConjugateIncrementComparison.PairedIncrementArea

open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- Conjugating the first primitive coordinate commutes with the exact directed primitive difference. -/
theorem conjugateFirst_sub (first last : Stokes.PrimitivePoint) :
    ConjugateIncrementComparison.conjugateFirst (Stokes.PrimitivePoint.sub first last) =
      Stokes.PrimitivePoint.sub (ConjugateIncrementComparison.conjugateFirst first)
        (ConjugateIncrementComparison.conjugateFirst last) := by
  apply congrArg₂ Stokes.PrimitivePoint.mk
  · apply Basic.ext
    · rfl
    · simp only [ConjugateIncrementComparison.conjugateFirst, Stokes.PrimitivePoint.sub, Data.Gaussian.Basic.conj,
        Basic.sub_im, -eq_self, -iff_self]; ring1
  · rfl

/-- Conjugating the first coordinate of every original increment commutes with the retained total. -/
theorem total_conjugate (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (values.map ConjugateIncrementComparison.conjugateFirst) =
      ConjugateIncrementComparison.conjugateFirst (PairedIncrementArea.total values) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change (ConjugateIncrementComparison.conjugateFirst head).add (PairedIncrementArea.total (tail.map
        ConjugateIncrementComparison.conjugateFirst)) =
        ConjugateIncrementComparison.conjugateFirst (head.add (PairedIncrementArea.total tail))
      rw [ih]
      apply congrArg₂ Stokes.PrimitivePoint.mk
      · exact (Basic.conj_add _ _).symm
      · rfl

end Purelib.Integration.Path.DyadicConjugateIncrementComparison.PairedIncrementArea

namespace Purelib.Integration.Path.DyadicConjugateIncrementComparison.Bilinear

open Purelib.Integration.Path.DyadicConjugateIncrementComparison.PairedIncrementArea (conjugateFirst_sub)

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Topology.Polygon in
/-- Mapping first-coordinate conjugation over the original dyadic increments equals subdividing the conjugated original
values. -/
theorem increments_conjugate (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedPrimitivePaths.increments values depth first last).map ConjugateIncrementComparison.conjugateFirst =
      DyadicPairedPrimitivePaths.increments (fun parameter => ConjugateIncrementComparison.conjugateFirst (values
        parameter)) depth first last := by
  induction depth generalizing first last with
  | zero =>
    exact congrArg List.singleton (DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub _ _)
  | succ depth ih => rw [DyadicPairedPrimitivePaths.increments, Data.List.Map.map_append, ih, ih]; rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- First-coordinate conjugation preserves the original depth-independent paired dyadic area comparison.

The separate left and right movement certificates and original difference-drift bound remain attached to the exact two
paths and endpoints. -/
theorem increments_conjugate_area_difference_bound (left right : Fraction.Rational → Stokes.PrimitivePoint)
    {lower upper error slope : Fraction.Rational} (errorNonnegative : 0 ≤ error) (slopeNonnegative : 0 ≤ slope)
    (leftBound : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (left last) (left first)) (slope * (last -
        first) ^ 2))
    (rightBound : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (right last) (right first)) (slope * (last -
        first) ^ 2))
    (errors : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub
        (Stokes.PrimitivePoint.sub (left last) (right last))
        (Stokes.PrimitivePoint.sub (left first) (right first))) (error * (last - first) ^ 2))
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((DyadicPairedPrimitivePaths.increments left depth first
      last).map ConjugateIncrementComparison.conjugateFirst) -
      PairedIncrementArea.area ((DyadicPairedPrimitivePaths.increments right depth first last).map
        ConjugateIncrementComparison.conjugateFirst)) ≤
      16 * error * slope * (last - first) ^ 4 := by
  rw [DyadicConjugateIncrementComparison.Bilinear.increments_conjugate,
    DyadicConjugateIncrementComparison.Bilinear.increments_conjugate]
  apply DyadicPairedIncrementComparison.increments_area_difference_bound _ _ errorNonnegative slopeNonnegative
    (fun first last firstInside lastInside => ConjugateIncrementComparison.conjugateFirst_error (leftBound first last
      firstInside lastInside))
    (fun first last firstInside lastInside => ConjugateIncrementComparison.conjugateFirst_error (rightBound first last
      firstInside lastInside))
    _ depth firstInside lastInside ordered
  intro first last firstInside lastInside
  rw [← DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub, ←
    DyadicConjugateIncrementComparison.PairedIncrementArea.conjugateFirst_sub]
  exact ConjugateIncrementComparison.conjugateFirst_error (errors first last firstInside lastInside)

end Purelib.Integration.Path.DyadicConjugateIncrementComparison.Bilinear
