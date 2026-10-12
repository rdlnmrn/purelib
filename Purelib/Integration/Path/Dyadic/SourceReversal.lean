module
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.Dyadic.SourceListResampling
public import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Reverse the retained source parameters and certify their existing increments.
Repeated parameters survive reversal, including stationary owner junctions. -/
namespace Purelib.Integration.Path.Dyadic.SourceReversal

open Purelib.Data.Rat.Fraction.Compatibility

section
open Purelib.Integration.Path.Dyadic
/-- Reverse the original parameter chain while moving its initial endpoint to the end. -/
def reverseParameters : SourceResampling.Coordinate → List SourceResampling.Coordinate → List
  SourceResampling.Coordinate
  | _, [] => []
  | first, next :: rest => Purelib.Integration.Path.Dyadic.SourceReversal.reverseParameters next rest ++ [first]

/-- The reversed chain ends at the original initial parameter. -/
theorem terminal_reverseParameters (first : SourceResampling.Coordinate) (points : List SourceResampling.Coordinate) :
    SourceListResampling.terminal (SourceListResampling.terminal first points) (SourceReversal.reverseParameters first
      points) = first := by
  cases points with
  | nil => rfl
  | cons next rest => rw [SourceReversal.reverseParameters, SourceListResampling.terminal_append]; rfl

end

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Topology.Polygon in
/-- The exact reversed parameter chain produces the reversed and negated original primitive increments. -/
theorem increments_reverseParameters (values : SourceResampling.Coordinate → Stokes.PrimitivePoint)
    (first : SourceResampling.Coordinate) (points : List SourceResampling.Coordinate) :
    SourceListResampling.increments values (SourceListResampling.terminal first points)
      (SourceReversal.reverseParameters first points) =
      PairedAreaReversal.reverseIncrements (SourceListResampling.increments values first points) := by
  induction points generalizing first with
  | nil => rfl
  | cons next rest ih =>
    rw [SourceReversal.reverseParameters, SourceListResampling.increments_append]
    change SourceListResampling.increments values (SourceListResampling.terminal next rest)
      (SourceReversal.reverseParameters next rest) ++
      SourceListResampling.increments values (SourceListResampling.terminal (SourceListResampling.terminal next rest)
        (SourceReversal.reverseParameters next rest)) [first] = _
    rw [SourceReversal.terminal_reverseParameters, ih]
    change _ = PairedAreaReversal.reverseIncrements (Stokes.PrimitivePoint.sub (values next) (values first) ::
      SourceListResampling.increments values next rest)
    rw [PairedAreaReversal.reverseIncrements_cons]
    apply congrArg (fun tail => PairedAreaReversal.reverseIncrements (SourceListResampling.increments values next rest)
      ++ tail)
    apply congrArg (fun point => [point])
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp [Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero] <;> ring1

open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
/-- Reverse an originally decreasing parameter chain into an ordered increasing chain.

The input order is retained as a chain on negated parameters, and the returned chain keeps the original terminal and
initial endpoints. -/
theorem reverseParameters_chain {first last : SourceResampling.Coordinate} {points : List SourceResampling.Coordinate}
    (chain : SourceResampling.Chain (-first) (points.map (fun point => -point)) (-last)) :
    SourceResampling.Chain last (SourceReversal.reverseParameters first points) first := by
  induction points generalizing first with
  | nil =>
    have equal := chain.nil_eq
    have endpoints := congrArg (fun value : SourceResampling.Coordinate => -value) equal
    simp only [neg_neg] at endpoints
    exact endpoints ▸ SourceResampling.Chain.nil first
  | cons next rest ih =>
    have parts := chain.cons_parts
    have ordered := Fraction.Order.Arithmetic.neg_le_neg_direct parts.1
    simp only [neg_neg] at ordered
    exact SourceListResampling.Chain.append (ih parts.2) (.cons ordered (.nil first))

open Purelib.Integration.Path.Dyadic in
/-- Reversing the original decreasing chain preserves its retained common step-width bound. -/
theorem reverseParameters_widths {first width : SourceResampling.Coordinate} {points : List SourceResampling.Coordinate}
    (bounded : SourceResampling.widths (-first) (points.map (fun point => -point)) width) :
    SourceResampling.widths (SourceListResampling.terminal first points) (SourceReversal.reverseParameters first points)
      width := by
  induction points generalizing first with
  | nil => trivial
  | cons next rest ih =>
    apply SourceListResampling.widths_append (ih bounded.2)
    rw [SourceReversal.terminal_reverseParameters]
    exact ⟨(show first - next = -next - -first by ring1).trans_le bounded.1, True.intro⟩

end Purelib.Integration.Path.Dyadic.SourceReversal
