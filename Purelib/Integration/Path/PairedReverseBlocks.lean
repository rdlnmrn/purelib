module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.PairedAreaReversal
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Reverse complete retained blocks with their order, endpoint errors and magnitudes. -/
namespace Purelib.Integration.Path.PairedReverseBlocks

open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.Readings
open Purelib.Topology.Polygon
/-- Reversing the original increments preserves a two-coordinate bound on their total. -/
theorem reversed_total_bounded (values : List Stokes.PrimitivePoint) {bound : PairedIncrementArea.Coordinate}
    (bounded : PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total values) bound) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (PairedIncrementArea.total (PairedAreaReversal.reverseIncrements values))
      bound := by
  rw [PairedAreaReversal.total_reverseIncrements]
  constructor
  · simpa only [Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero, zero_sub, Basic.Canonical.normSq_neg, -eq_self,
      -iff_self] using bounded.1
  · simpa only [Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero, zero_sub, Basic.Canonical.normSq_neg, -eq_self,
      -iff_self] using bounded.2

/-- An original total close to the negative source gives a reversed total equally close to the original source. -/
theorem reversed_total_error (values : List Stokes.PrimitivePoint) (source : Stokes.PrimitivePoint) {error :
  PairedIncrementArea.Coordinate}
    (bounded : PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total values)
      (Stokes.PrimitivePoint.sub Stokes.PrimitivePoint.zero source)) error) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (PairedIncrementArea.total
      (PairedAreaReversal.reverseIncrements values)) source) error := by
  rw [PairedAreaReversal.total_reverseIncrements]
  have scalar (first last : Basic.Canonical) :
      Basic.Canonical.normSq ((0 - first) - last) =
        Basic.Canonical.normSq (first - (0 - last)) := by
    rw [show (0 - first) - last = -(first - (0 - last)) by ring1, Basic.Canonical.normSq_neg]
  exact ⟨(scalar _ _).trans_le bounded.1, (scalar _ _).trans_le bounded.2⟩

end Purelib.Integration.Path.PairedReverseBlocks
