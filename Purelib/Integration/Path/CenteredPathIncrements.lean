module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Riemann.Periods.CenteredBilinearPath
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

public section

/-! Read every adjacent increment from the retained centered vector. Its
full paired increment area is exactly the cached centered path area. -/
namespace Purelib.Integration.Path.CenteredPathIncrements
open Purelib.Riemann.Periods
open Purelib.Integration.Path
open Purelib.Topology.Polygon

open Purelib.Data.List

open scoped Purelib.Data.Nat

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {count : Nat}

/-- List the consecutive primitive-point differences of the original nonempty indexed path. -/
@[expose] def increments (values : Fin (count + 1) → Stokes.PrimitivePoint) : List PrimitivePoint :=
  List.ofFn (fun edge : Fin count => (Stokes.PrimitivePoint.sub (values edge.succ)) (values edge.castSucc))

/-- The consecutive increment list has exactly the original path's edge count. -/
theorem increments_length (values : Fin (count + 1) → Stokes.PrimitivePoint) :
    (CenteredPathIncrements.increments values).length = count := OfFn.Basic.length_ofFn

/-- The exact increment total equals the original final point minus the original initial point.

The first edge and the retained successor tail telescope by scalar coordinate cancellation. The endpoint indices remain
the original initial coordinate and Fin.last. -/
theorem increments_total (values : Fin (count + 1) → Stokes.PrimitivePoint) :
    PairedIncrementArea.total (CenteredPathIncrements.increments values) =
      (Stokes.PrimitivePoint.sub (values (Fin.last count))) (values 0) := by
  induction count with
  | zero =>
    change Stokes.PrimitivePoint.zero = (Stokes.PrimitivePoint.sub (values 0)) (values 0)
    cases values 0
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.zero, Stokes.PrimitivePoint.sub] <;>
      ring1
  | succ count ih =>
    rw [CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
    change ((Stokes.PrimitivePoint.sub (values 1)) (values 0)).add
      (PairedIncrementArea.total (CenteredPathIncrements.increments (fun vertex => values vertex.succ))) = _
    rw [ih]
    have initial : (0 : Fin (count + 1)).succ = (1 : Fin (count + 2)) := by
      apply Fin.ext
      rfl
    have final : (Fin.last count).succ = Fin.last (count + 1) := by apply Fin.ext; rfl
    rw [initial, final]
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.add, Stokes.PrimitivePoint.sub] <;>
      ring1

/-- Adding the difference from the first primitive point to the last recovers the last point.

Both primitive-point coordinates satisfy the same scalar addition/subtraction identity. The proof keeps those two
original coordinates separate. -/
private theorem add_difference (first last : Stokes.PrimitivePoint) : first.add ((Stokes.PrimitivePoint.sub last) first)
  = last := by
  cases first; cases last
  apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.add, Stokes.PrimitivePoint.sub] <;>
    ring1

open Purelib.Algebra in
/-- Tracing the original consecutive increments from the first value recovers the original indexed path area. -/
theorem increments_trace (values : Fin (count + 1) → Stokes.PrimitivePoint) :
    PairedIncrementArea.traceArea (values 0) (CenteredPathIncrements.increments values) = CenteredBilinearPath.area
      values := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [CenteredPathIncrements.increments, OfFn.Basic.ofFn_succ]
    change Stokes.edgeArea (values 0) ((values 0).add ((Stokes.PrimitivePoint.sub (values 1)) (values 0))) +
      PairedIncrementArea.traceArea ((values 0).add ((Stokes.PrimitivePoint.sub (values 1)) (values 0)))
        (CenteredPathIncrements.increments (fun vertex => values vertex.succ)) = _
    rw [CenteredPathIncrements.add_difference]
    exact (congrArg (Stokes.edgeArea (values 0) (values 1) + ·) (ih (fun vertex => values vertex.succ))).trans
      (FiniteSum.Fin.sumFin_succ
        (fun edge : Fin (count + 1) => Stokes.edgeArea (values edge.castSucc) (values edge.succ))).symm

namespace Sample
variable {values : Fin (count + 1) → Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- Read consecutive differences from the retained sample's original centered-value cache. -/
@[expose] def increments (sample : CenteredBilinearPath.Sample values) : List PrimitivePoint :=
  CenteredPathIncrements.increments (fun vertex => sample.centered vertex)

/-- The retained sample increment list has the original path edge count. -/
theorem increments_length (sample : CenteredBilinearPath.Sample values) : (CenteredPathIncrements.Sample.increments
  sample).length = count :=
  CenteredPathIncrements.increments_length _

/-- Centering the retained sample leaves its exact consecutive increment list unchanged. -/
theorem increments_raw (sample : CenteredBilinearPath.Sample values) :
    (CenteredPathIncrements.Sample.increments sample) = CenteredPathIncrements.increments values := by
  apply OfFn.Basic.ofFn_congr
  intro edge
  change (Stokes.PrimitivePoint.sub (sample.centered edge.succ)) (sample.centered edge.castSucc) = _
  rw [sample.centered_eq, sample.centered_eq]
  apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub] <;> ring1

/-- The retained sample increment total equals its original uncentered final point minus its initial point. -/
theorem increments_total (sample : CenteredBilinearPath.Sample values) :
    PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample) = (Stokes.PrimitivePoint.sub (values
      (Fin.last count))) (values 0) := by
  rw [CenteredPathIncrements.Sample.increments, CenteredPathIncrements.increments_total, sample.centered_eq,
    sample.centered_eq]
  apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub] <;> ring1

/-- The retained sample's consecutive increments have its exact cached centered area.

The retained centered initial value is zero. The original increment trace identity then identifies the paired area with
the same cached centered-area reading. -/
theorem increments_area (sample : CenteredBilinearPath.Sample values) :
    PairedIncrementArea.area (CenteredPathIncrements.Sample.increments sample) = sample.centeredArea := by
  have zero : sample.centered 0 = PrimitivePoint.zero := by
    rw [sample.centered_eq]
    cases values 0
    apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub, Stokes.PrimitivePoint.zero] <;>
      ring1
  have traced := CenteredPathIncrements.increments_trace (fun vertex => sample.centered vertex)
  rw [zero] at traced
  exact (PairedIncrementArea.area_eq_trace (CenteredPathIncrements.Sample.increments sample)).trans (traced.trans
    sample.centeredArea_eq.symm)

/-- Retain an increment summary using the sample's existing centered-area cache.

The total is computed from the exact sample increments; the area reading is reused with its proved original-list
identity. -/
@[expose] def incrementSummary (sample : CenteredBilinearPath.Sample values) : PairedIncrementArea.Summary
  (CenteredPathIncrements.Sample.increments sample) where
  totalValue := PairedIncrementArea.total (CenteredPathIncrements.Sample.increments sample)
  total_eq := rfl
  areaValue := sample.centeredArea
  area_eq := (CenteredPathIncrements.Sample.increments_area sample).symm

end Sample
end Purelib.Integration.Path.CenteredPathIncrements

end
