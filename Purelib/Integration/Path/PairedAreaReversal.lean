module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

/-! Reverse a retained increment path without reevaluating its primitive owners.
Both the total and the full area change sign; cached summaries transport directly. -/
namespace Purelib.Integration.Path.PairedAreaReversal

open Purelib.Data.List

open Purelib.Topology.Polygon
open Purelib.Integration.Path
open Purelib.Data.Gaussian

public section
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Integration.Path.PairedIncrementArea (total area terms Summary)

open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

/-- Reverse the retained increment order and negate both coordinates of each original increment.

Both primitive coordinates are negated after reversing the supplied finite list. The original occurrence order is
reversed without reevaluating either primitive. -/
@[expose] def reverseIncrements (values : List Stokes.PrimitivePoint) : List PrimitivePoint :=
  values.reverse.map (fun point => Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero point)

/-- Reversing an increment cons appends the negated original head after the reversed tail.

The unchanged reversed tail precedes the negated original head; each coordinate and occurrence order is retained. -/
theorem reverseIncrements_cons (first : Stokes.PrimitivePoint) (rest : List Stokes.PrimitivePoint) :
    PairedAreaReversal.reverseIncrements (first :: rest) = PairedAreaReversal.reverseIncrements rest ++
      [Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero first] := by
  rewrite [PairedAreaReversal.reverseIncrements, Reverse.reverse_cons, Map.map_append, List.map_cons, List.map_nil]
  exact Eq.refl _

/-- The total of reversed increments is the negative of the original two-coordinate total.

Structural recursion follows the original increment list, using the same paired total and Gaussian scalar operations. -/
theorem total_reverseIncrements (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (PairedAreaReversal.reverseIncrements values) = Stokes.PrimitivePoint.sub
      Stokes.PrimitivePoint.zero (PairedIncrementArea.total values) := by
  induction values with
  | nil =>
    apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      dsimp only [PairedAreaReversal.reverseIncrements, List.reverse_nil, List.map_nil, PairedIncrementArea.total,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Stokes.PrimitivePoint.zero, Stokes.PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1
  | cons first rest ih =>
    rw [PairedAreaReversal.reverseIncrements_cons, PairedAreaBlocks.total_append, ih]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;>
      simp only [PairedIncrementArea.total, List.map_cons, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Stokes.PrimitivePoint.sub,
        Stokes.PrimitivePoint.zero, -eq_self, -iff_self] <;> ring1

/-- Reversing the retained increments negates their signed paired area.

The same finite increment list determines both areas. Concatenation and the reversed cached total transport the signed
area identity. -/
theorem area_reverseIncrements (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (PairedAreaReversal.reverseIncrements values) = -PairedIncrementArea.area values := by
  induction values with
  | nil => change (0 : Basic.Canonical) = -0; exact neg_zero.symm
  | cons first rest ih =>
    rw [PairedAreaReversal.reverseIncrements_cons, PairedAreaBlocks.area_append, ih,
      PairedAreaReversal.total_reverseIncrements, PairedAreaBlocks.area_cons]
    simp only [PairedIncrementArea.area, PairedIncrementArea.terms, PairedIncrementArea.total, List.map_cons,
      List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
      Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero, Stokes.edgeArea, -eq_self, -iff_self]
    ring1

/-- Negating a primitive point commutes with conjugating its first coordinate.

Conjugation changes only the first Gaussian coordinate. Direct scalar identities commute it with the displayed
two-coordinate negation. -/
private theorem opposite_conjugate (point : Stokes.PrimitivePoint) :
    Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero (ConjugateIncrementComparison.conjugateFirst point) =
      ConjugateIncrementComparison.conjugateFirst (Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero point) := by
  apply congrArg₂ Stokes.PrimitivePoint.mk
  · apply Basic.ext
    · rfl
    · dsimp [ConjugateIncrementComparison.conjugateFirst, Stokes.PrimitivePoint.zero, Stokes.PrimitivePoint.sub,
        Data.Gaussian.Basic.conj]
      ring1
  · rfl

/-- Increment reversal commutes with conjugating the first coordinate of every original point.

Every retained point is conjugated at the same reversed occurrence. Structural recursion preserves the original tail and
final singleton. -/
theorem reverseIncrements_conjugate (values : List Stokes.PrimitivePoint) :
    PairedAreaReversal.reverseIncrements (values.map ConjugateIncrementComparison.conjugateFirst) =
      (PairedAreaReversal.reverseIncrements values).map conjugateFirst := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    rw [List.map_cons, PairedAreaReversal.reverseIncrements_cons, PairedAreaReversal.reverseIncrements_cons,
      Map.map_append, ih]
    exact congrArg (fun tail => (PairedAreaReversal.reverseIncrements rest).map
      ConjugateIncrementComparison.conjugateFirst ++ tail)
      (congrArg (fun point => [point]) (PairedAreaReversal.opposite_conjugate first))

/-- Reversing the original increments negates their first-coordinate-conjugated area.

Conjugation commutes with reversing the retained increment occurrences, and the same paired area is negated. -/
theorem conjugate_area_reverseIncrements (values : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area ((PairedAreaReversal.reverseIncrements values).map
      ConjugateIncrementComparison.conjugateFirst) = -PairedIncrementArea.area (values.map
      ConjugateIncrementComparison.conjugateFirst) := by
  rewrite [← PairedAreaReversal.reverseIncrements_conjugate, PairedAreaReversal.area_reverseIncrements]
  exact Eq.refl _

/-- Reversing both original increment lists preserves the squared norm of their area difference.

Both signed areas change sign under reversal. Their difference is therefore the negative of the original difference,
with unchanged squared norm. -/
theorem reverse_area_error (first last : List Stokes.PrimitivePoint) :
    Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area (PairedAreaReversal.reverseIncrements first) - PairedIncrementArea.area
        (PairedAreaReversal.reverseIncrements last)) =
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area first - PairedIncrementArea.area last) := by
  rw [PairedAreaReversal.area_reverseIncrements, PairedAreaReversal.area_reverseIncrements]
  rw [show -PairedIncrementArea.area first - -PairedIncrementArea.area last = -(PairedIncrementArea.area first -
    PairedIncrementArea.area last) by ring1]
  exact Norm.Basic.normSq_neg _

/-- Reverse a retained paired summary by negating its cached total and area.

The returned summary is indexed by the exact reversed original increment list and reuses the original cached values with
their reversal equalities. -/
@[expose] def Summary.reverse (values : List Stokes.PrimitivePoint) (summary : PairedIncrementArea.Summary values) :
    PairedIncrementArea.Summary (PairedAreaReversal.reverseIncrements values) where
  totalValue := Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero summary.totalValue
  total_eq := by
    rewrite [summary.total_eq, PairedAreaReversal.total_reverseIncrements]
    exact Eq.refl _
  areaValue := -summary.areaValue
  area_eq := by
    rewrite [summary.area_eq, PairedAreaReversal.area_reverseIncrements]
    exact Eq.refl _

end

end Purelib.Integration.Path.PairedAreaReversal

namespace Purelib.Integration.Path.PairedAreaReversal

open Purelib.Data.List
open Purelib.Topology.Polygon

/-- Reversing concatenated increment lists reverses their parts and exchanges order.

The original reversal negates every retained increment while reading the input
spine backwards. The append identity preserves both original parts completely. -/
public theorem reverseIncrements_append (left right : List Stokes.PrimitivePoint) :
    reverseIncrements (left ++ right) = reverseIncrements right ++ reverseIncrements left := by
  dsimp only [reverseIncrements, -eq_self, -iff_self]
  rewrite [Reverse.reverse_append, Map.map_append]
  rfl

/-- Reversing retained increment blocks reverses their order and each complete block.

Structural concatenation preserves every original increment and retained block boundary. -/
public theorem reverseIncrements_flatten (blocks : List (List Stokes.PrimitivePoint)) :
    PairedAreaReversal.reverseIncrements blocks.flatten = (blocks.reverse.map
      PairedAreaReversal.reverseIncrements).flatten := by
  induction blocks with
  | nil => rfl
  | cons first rest ih =>
    rw [List.flatten_cons, reverseIncrements_append, ih, Data.List.Reverse.reverse_cons,
      Data.List.Map.map_append, Data.List.Flatten.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Data.List.Append.append_nil, -eq_self,
      -iff_self]
    rfl

end Purelib.Integration.Path.PairedAreaReversal
