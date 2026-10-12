module
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Integration.Energy.Polygon

public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Integration.Path.EnergyRibbonCombination
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

@[expose] public section

/-! Scalar energy ribbons read back into paired primitive areas with the
complete cross-owner endpoint correction. Pointwise equalities suffice. -/

namespace Purelib.Integration.Path.EnergyRibbonReadback

open Purelib.Algebra in
open Purelib.Integration.Energy in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Read a retained Gaussian ribbon difference as the difference of two primitive path areas with endpoint correction.

The supplied vertex equalities retain both original paths; their terminal and initial cross areas give the exact signed
correction. -/
theorem difference_readback {count : Nat} (ribbon : BoundaryRibbon.Ribbon count)
    {leftValues rightValues : Fin (count + 1) → Stokes.PrimitivePoint}
    (leftEq : ∀ vertex, Polygon.energyPrimitivePoint (ribbon.left vertex) = leftValues vertex)
    (rightEq : ∀ vertex, Polygon.energyPrimitivePoint (ribbon.right vertex) = rightValues vertex) :
    ribbon.difference = CenteredBilinearPath.area leftValues - CenteredBilinearPath.area rightValues -
      (Stokes.edgeArea (rightValues (Fin.last count)) (leftValues (Fin.last count)) - Stokes.edgeArea (rightValues 0)
        (leftValues 0)) := by
  have leftArea : ribbon.leftArea = CenteredBilinearPath.area leftValues := by
    refine ribbon.leftArea_eq.trans ?_
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Stokes.edgeArea (Polygon.energyPrimitivePoint (ribbon.left edge.castSucc))
      (Polygon.energyPrimitivePoint (ribbon.left edge.succ)) = _
    rw [leftEq edge.castSucc, leftEq edge.succ]
  have rightArea : ribbon.rightArea = CenteredBilinearPath.area rightValues := by
    refine ribbon.rightArea_eq.trans ?_
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    change Stokes.edgeArea (Polygon.energyPrimitivePoint (ribbon.right edge.castSucc))
      (Polygon.energyPrimitivePoint (ribbon.right edge.succ)) = _
    rw [rightEq edge.castSucc, rightEq edge.succ]
  have endpoint : ribbon.endpointCorrection =
      Stokes.edgeArea (rightValues (Fin.last count)) (leftValues (Fin.last count)) - Stokes.edgeArea (rightValues 0)
        (leftValues 0) := by
    rw [ribbon.endpointCorrection_eq, ribbon.errors_eq, ribbon.errors_eq,
      BoundaryRibbon.area_sub_self_right, BoundaryRibbon.area_sub_self_right]
    change Stokes.edgeArea (Polygon.energyPrimitivePoint (ribbon.right (Fin.last count)))
      (Polygon.energyPrimitivePoint (ribbon.left (Fin.last count))) -
      Stokes.edgeArea (Polygon.energyPrimitivePoint (ribbon.right 0)) (Polygon.energyPrimitivePoint (ribbon.left 0)) = _
    rw [rightEq (Fin.last count), leftEq (Fin.last count), rightEq 0, leftEq 0]
  rw [ribbon.difference_eq, leftArea, rightArea, endpoint]

end Purelib.Integration.Path.EnergyRibbonReadback
