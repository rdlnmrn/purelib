module

import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.OfFn.Basic

public import Purelib.Integration.Path.CenteredPathIncrements
public import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-! Join the existing finite source parameter lists without erasing their
internal increments. These identities feed the retained parent-run estimate. -/
namespace Purelib.Integration.Path.Dyadic.SourceListResampling

open Purelib.Integration.Path.Dyadic
open Purelib.Topology.Polygon
open Purelib.Data.List
open Purelib.Integration.Path
open Purelib.Data.Gaussian
open Purelib.Riemann.Readings

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic.SourceResampling (Coordinate Chain widths rawArea resampling_bound)

/-- Read the last retained parameter, using the original first parameter for an empty list. -/
@[expose] def terminal (first : SourceResampling.Coordinate) : List SourceResampling.Coordinate →
  SourceResampling.Coordinate
  | [] => first
  | next :: rest => Purelib.Integration.Path.Dyadic.SourceListResampling.terminal next rest

/-- List the original primitive displacements along the retained ordered parameter points. -/
@[expose] def increments (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) (first :
  SourceResampling.Coordinate) : List SourceResampling.Coordinate → List Stokes.PrimitivePoint
  | [] => []
  | next :: rest => Stokes.PrimitivePoint.sub (values next) (values first) ::
    Purelib.Integration.Path.Dyadic.SourceListResampling.increments values next rest

/-- The terminal of concatenated points is the second list's terminal starting at the exact first-list terminal. -/
theorem terminal_append (first : SourceResampling.Coordinate) (left right : List SourceResampling.Coordinate) :
    SourceListResampling.terminal first (left ++ right) = SourceListResampling.terminal (SourceListResampling.terminal
      first left) right := by
  induction left generalizing first with
  | nil => rfl
  | cons next rest ih => exact ih next

/-- The terminal of the indexed successor list is the original family's last indexed vertex. -/
theorem terminal_ofFn {count : Nat} (parameters : Fin (count + 1) → SourceResampling.Coordinate) :
    SourceListResampling.terminal (parameters 0) (List.ofFn (fun edge : Fin count => parameters edge.succ)) = parameters
      (Fin.last count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ]
    exact ih (fun vertex => parameters vertex.succ)

/-- The terminal readback of a retained chain is its exact indexed last endpoint. -/
theorem Chain.terminal_eq {first last : SourceResampling.Coordinate} {points : List SourceResampling.Coordinate}
    (chain : SourceResampling.Chain first points last) : SourceListResampling.terminal first points = last := by
  induction chain with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Concatenate retained ordered chains at their exact shared endpoint. -/
theorem Chain.append {first middle last : SourceResampling.Coordinate} {left right : List SourceResampling.Coordinate}
    (a : SourceResampling.Chain first left middle) (b : SourceResampling.Chain middle right last) :
      SourceResampling.Chain first (left ++ right) last := by
  induction a with
  | nil => exact b
  | cons ordered _ ih => exact .cons ordered (ih b)

/-- Concatenating two retained lists at the original terminal preserves their common step-width bound. -/
theorem widths_append {first width : SourceResampling.Coordinate} {left right : List SourceResampling.Coordinate}
    (a : SourceResampling.widths first left width) (b : SourceResampling.widths (SourceListResampling.terminal first
      left) right width) :
    SourceResampling.widths first (left ++ right) width := by
  induction left generalizing first with
  | nil => exact b
  | cons next rest ih => exact ⟨a.1, ih a.2 b⟩

/-- Original increments over concatenated parameters split at the exact first-list terminal. -/
theorem increments_append (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) (first :
  SourceResampling.Coordinate) (left right : List SourceResampling.Coordinate) :
    SourceListResampling.increments values first (left ++ right) = SourceListResampling.increments values first left ++
      SourceListResampling.increments values (SourceListResampling.terminal first left) right := by
  induction left generalizing first with
  | nil => rfl
  | cons next rest ih => exact congrArg (List.cons (Stokes.PrimitivePoint.sub (values next) (values first))) (ih next)

/-- List increments over indexed successor parameters equal the exact original indexed path increments. -/
theorem increments_ofFn (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) {count : Nat}
    (parameters : Fin (count + 1) → SourceResampling.Coordinate) :
    SourceListResampling.increments values (parameters 0) (List.ofFn (fun edge : Fin count => parameters edge.succ)) =
      CenteredPathIncrements.increments (fun vertex => values (parameters vertex)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [OfFn.Basic.ofFn_succ, SourceListResampling.increments,
      CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
    exact congrArg (List.cons (Stokes.PrimitivePoint.sub (values (parameters (Fin.succ 0))) (values (parameters 0))))
      (ih (fun vertex => parameters vertex.succ))

/-- The retained increment total is the exact terminal primitive value minus the original first value. -/
theorem increments_total (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) (first :
  SourceResampling.Coordinate) (points : List SourceResampling.Coordinate) :
    PairedIncrementArea.total (SourceListResampling.increments values first points) = Stokes.PrimitivePoint.sub (values
      (SourceListResampling.terminal first points)) (values first) := by
  induction points generalizing first with
  | nil =>
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> change 0 = _ - _ <;> dsimp only [SourceListResampling.terminal] <;>
      ring1
  | cons next rest ih =>
    change (Stokes.PrimitivePoint.sub (values next) (values first)).add (PairedIncrementArea.total
      (SourceListResampling.increments values next rest)) = _
    rw [ih]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.add,
      SourceListResampling.terminal] <;> ring1

/-- The retained increment area is the original raw path area minus its exact endpoint chord area. -/
theorem increments_area (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) (first :
  SourceResampling.Coordinate) (points : List SourceResampling.Coordinate) :
    PairedIncrementArea.area (SourceListResampling.increments values first points) = SourceResampling.rawArea values
      first points -
      Stokes.edgeArea (values first) (values (SourceListResampling.terminal first points)) := by
  induction points generalizing first with
  | nil => change 0 = 0 - Stokes.edgeArea (values first) (values first); dsimp only [Stokes.edgeArea]; ring1
  | cons next rest ih =>
    rw [SourceListResampling.increments, PairedAreaBlocks.area_cons, SourceListResampling.increments_total, ih]
    dsimp only [SourceResampling.rawArea, SourceListResampling.terminal, Stokes.edgeArea, Stokes.PrimitivePoint.sub]
    ring1

/-- Shared-endpoint original parameter chains satisfy the same width-controlled comparison for their retained increment
areas.

The endpoint chord terms cancel using the two exact chain witnesses; the original density, width and endpoint span
remain in the sixteenfold squared bound. -/
theorem increment_resampling_bound (values : SourceResampling.Coordinate → Stokes.PrimitivePoint) {density width :
  SourceResampling.Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (values b) (values a)) (density * (b - a) ^
        2))
    {first last : SourceResampling.Coordinate} {left right : List SourceResampling.Coordinate}
    (leftChain : SourceResampling.Chain first left last) (rightChain : SourceResampling.Chain first right last)
    (lower : 0 ≤ first) (upper : last ≤ 1)
    (leftSteps : SourceResampling.widths first left width) (rightSteps : SourceResampling.widths first right width) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (SourceListResampling.increments values first left) -
      PairedIncrementArea.area (SourceListResampling.increments values first right)) ≤
        16 * density ^ 2 * width ^ 2 * (last - first) ^ 2 := by
  rw [SourceListResampling.increments_area, SourceListResampling.increments_area, SourceListResampling.Chain.terminal_eq
    leftChain, SourceListResampling.Chain.terminal_eq rightChain]
  have canceled :
      (SourceResampling.rawArea values first left - Stokes.edgeArea (values first) (values last)) -
        (SourceResampling.rawArea values first right - Stokes.edgeArea (values first) (values last)) =
      SourceResampling.rawArea values first left - SourceResampling.rawArea values first right := by ring1
  rw [canceled]
  exact SourceResampling.resampling_bound values increment leftChain rightChain lower upper leftSteps rightSteps

end Purelib.Integration.Path.Dyadic.SourceListResampling

end
