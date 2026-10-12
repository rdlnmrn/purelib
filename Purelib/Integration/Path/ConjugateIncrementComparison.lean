module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map

public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
public import Purelib.Data.Gaussian.Norm.Bounds

open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

public section

/-! Conjugating the first increment preserves every scalar error and size
bound used by the finite polygon comparison. -/
namespace Purelib.Integration.Path.ConjugateIncrementComparison

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Gaussian.Basic (conj)

open Purelib.Topology.Polygon in
/-- Conjugate only the left coordinate of the exact original primitive point. -/
@[expose] def conjugateFirst (point : Stokes.PrimitivePoint) : PrimitivePoint := ⟨conj point.left, point.right⟩

open Purelib.Data.Gaussian in
/-- Gaussian conjugation commutes with the original directed difference. -/
private theorem conj_sub (first last : Basic.Canonical) : Data.Gaussian.Basic.conj (first - last) =
  Data.Gaussian.Basic.conj first
  - Data.Gaussian.Basic.conj last := by
  apply Basic.ext
  · rfl
  · simp only [Data.Gaussian.Basic.conj, Basic.sub_im]; ring1

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon
/-- Conjugating the first primitive coordinate preserves its original two-coordinate squared-norm bound. -/
theorem conjugateFirst_bounded {point : Stokes.PrimitivePoint} {bound : PairedIncrementArea.Coordinate}
    (bounded : Bounded point bound) : Bounded
      (conjugateFirst point) bound :=
  ⟨(show Basic.Canonical.normSq (Data.Gaussian.Basic.conj point.left) = Basic.Canonical.normSq point.left from by
    simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Basic.normSq_conj point.left).trans_le bounded.1, bounded.2⟩

/-- Conjugating the first coordinate of both original points preserves their paired difference bound. -/
theorem conjugateFirst_error {first last : Stokes.PrimitivePoint} {bound : PairedIncrementArea.Coordinate}
    (bounded : Bounded (Stokes.PrimitivePoint.sub first last) bound) :
    Bounded (Stokes.PrimitivePoint.sub (conjugateFirst
      first) (conjugateFirst last)) bound := by
  constructor
  · change Basic.Canonical.normSq (Data.Gaussian.Basic.conj first.left - Data.Gaussian.Basic.conj last.left) ≤ bound
    rw [← conj_sub]
    rw [show Basic.Canonical.normSq (Data.Gaussian.Basic.conj (first.left - last.left)) = Basic.Canonical.normSq
      (first.left
      - last.left) from by simpa only [Norm.Basic.normSq_eq_canonical] using Norm.Basic.normSq_conj (first.left -
      last.left)]
    exact bounded.1
  · exact bounded.2

end

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- First-coordinate conjugation preserves the original fourth-power paired area-difference estimate.

The original ordered pairs, separate magnitude bounds and common difference certificates remain attached to their
respective inputs. -/
theorem conjugate_area_difference_bound (pairs : List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)) {error bound :
  PairedIncrementArea.Coordinate}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, Bounded (Stokes.PrimitivePoint.sub pair.1 pair.2)
      error)
    (leftBound : ∀ pair ∈ pairs, Bounded pair.1 bound) (rightBound : ∀ pair ∈ pairs,
      Bounded pair.2 bound) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (pairs.map (fun pair =>
      conjugateFirst pair.1)) -
      PairedIncrementArea.area (pairs.map (fun pair => conjugateFirst pair.2))) ≤
      16 * (pairs.length : PairedIncrementArea.Coordinate)^4 * error * bound := by
  let changed := pairs.map (fun pair => (conjugateFirst pair.1,
    conjugateFirst pair.2))
  have estimate := PairedIncrementComparison.area_difference_bound changed errorNonnegative boundNonnegative
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      exact conjugateFirst_error (errors original present))
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      exact conjugateFirst_bounded (leftBound original present))
    (by
      intro pair member
      obtain ⟨original, present, rfl⟩ := Map.mem_map.mp member
      exact conjugateFirst_bounded (rightBound original present))
  have first : changed.map Prod.fst = pairs.map (fun pair => conjugateFirst pair.1) := by
    rw [Map.map_map]; rfl
  have last : changed.map Prod.snd = pairs.map (fun pair => conjugateFirst pair.2) := by
    rw [Map.map_map]; rfl
  rw [first, last, show changed.length = pairs.length from Map.length_map _ _] at estimate
  exact estimate

end Purelib.Integration.Path.ConjugateIncrementComparison
