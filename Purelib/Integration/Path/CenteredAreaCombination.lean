module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic

public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

@[expose] public section

/-! Exact coefficient expansion of centered path areas. Cached pair samples
supply homogeneous bounds without losing any open endpoint correction. -/
namespace Purelib.Integration.Path.CenteredAreaCombination

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

open Purelib.Riemann.Periods.CenteredBilinearPath (area Sample)

open Purelib.Algebra in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Pointwise equality of the retained primitive vertices preserves their exact path area. -/
private theorem area_congr {count : Nat} {first last : Fin (count + 1) → Stokes.PrimitivePoint}
    (equal : ∀ vertex, first vertex = last vertex) : CenteredBilinearPath.area first = CenteredBilinearPath.area last :=
      by
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  exact congrArg₂ Stokes.edgeArea (equal edge.castSucc) (equal edge.succ)

open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The retained centered sample area equals the area of original vertices after subtracting the original first vertex.
-/
theorem Sample.centeredArea_eq_differences {count : Nat} {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (sample : CenteredBilinearPath.Sample values) : sample.centeredArea = CenteredBilinearPath.area (fun vertex =>
      (Stokes.PrimitivePoint.sub (values vertex)) (values 0)) :=
  sample.centeredArea_eq.trans (CenteredAreaCombination.area_congr sample.centered_eq)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- Expand primitive path area under separate finite left and right coefficient combinations.

Both coefficient families retain their original order and factors, with the original vertex count fixed in every paired
area. -/
theorem area_combination {count leftCount rightCount : Nat}
    (left : Fin leftCount → Basic.Canonical) (right : Fin rightCount → Basic.Canonical)
    (first : Fin leftCount → Fin (count + 1) → Basic.Canonical)
    (second : Fin rightCount → Fin (count + 1) → Basic.Canonical) :
    CenteredBilinearPath.area (fun vertex => ⟨sumFin (fun row => left row * first row vertex),
      FiniteSum.Fin.sumFin (fun row => right row * second row vertex)⟩) =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * CenteredBilinearPath.area (fun
        vertex => ⟨first i vertex, second j vertex⟩))) := by
  unfold CenteredBilinearPath.area
  have edges := FiniteSum.Fin.sumFin_congr (fun edge : Fin count =>
    BilinearCombination.edgeArea_combination left right (fun row => first row edge.castSucc) (fun row => first row
      edge.succ)
      (fun row => second row edge.castSucc) (fun row => second row edge.succ))
  exact edges.trans (BilinearCombination.sumFin_combination left right _)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- The retained combined centered area is the exact double coefficient sum of retained paired centered areas.

The combined and paired samples remain distinct owners, linked through their original centered-value equations. -/
theorem Sample.centeredArea_combination {count leftCount rightCount : Nat}
    (left : Fin leftCount → Basic.Canonical) (right : Fin rightCount → Basic.Canonical)
    (first : Fin leftCount → Fin (count + 1) → Basic.Canonical)
    (second : Fin rightCount → Fin (count + 1) → Basic.Canonical)
    (combined : CenteredBilinearPath.Sample (fun vertex => ⟨sumFin (fun row => left row * first row vertex),
      FiniteSum.Fin.sumFin (fun row => right row * second row vertex)⟩))
    (pairs : (i : Fin leftCount) → (j : Fin rightCount) → CenteredBilinearPath.Sample (fun vertex => ⟨first i vertex,
      second j vertex⟩)) :
    combined.centeredArea = FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (pairs i
      j).centeredArea)) := by
  have scalar {size : Nat} (coefficients before after : Fin size → Basic.Canonical) :
      FiniteSum.Fin.sumFin (fun row => coefficients row * after row) - FiniteSum.Fin.sumFin (fun row => coefficients row
        * before row) =
        FiniteSum.Fin.sumFin (fun row => coefficients row * (after row - before row)) := by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    ring1
  have points (vertex : Fin (count + 1)) :
      (Stokes.PrimitivePoint.sub (Stokes.PrimitivePoint.mk (FiniteSum.Fin.sumFin (fun row => left row * first row
        vertex))
        (FiniteSum.Fin.sumFin (fun row => right row * second row vertex))))
        ⟨sumFin (fun row => left row * first row 0), FiniteSum.Fin.sumFin (fun row => right row * second row 0)⟩ =
      ⟨sumFin (fun row => left row * (first row vertex - first row 0)),
        FiniteSum.Fin.sumFin (fun row => right row * (second row vertex - second row 0))⟩ :=
    congrArg₂ Stokes.PrimitivePoint.mk (scalar left _ _) (scalar right _ _)
  refine (CenteredAreaCombination.Sample.centeredArea_eq_differences combined).trans
    ((CenteredAreaCombination.area_congr points).trans ?_)
  refine (CenteredAreaCombination.area_combination left right (fun row vertex => first row vertex - first row 0)
    (fun row vertex => second row vertex - second row 0)).trans ?_
  apply FiniteSum.Fin.sumFin_congr
  intro i
  apply FiniteSum.Fin.sumFin_congr
  intro j
  exact congrArg (fun value => left i * right j * value) (CenteredAreaCombination.Sample.centeredArea_eq_differences
    (pairs i j)).symm

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- A uniform paired centered-area bound controls the combined area by both counts and both coefficient norm sums.

The original two coefficient families and all retained centered samples remain fixed, preserving the separate left and
right factors. -/
theorem Sample.centeredArea_combination_bound {count leftCount rightCount : Nat}
    (left : Fin leftCount → Basic.Canonical) (right : Fin rightCount → Basic.Canonical)
    (first : Fin leftCount → Fin (count + 1) → Basic.Canonical)
    (second : Fin rightCount → Fin (count + 1) → Basic.Canonical)
    (combined : CenteredBilinearPath.Sample (fun vertex => ⟨sumFin (fun row => left row * first row vertex),
      FiniteSum.Fin.sumFin (fun row => right row * second row vertex)⟩))
    (pairs : (i : Fin leftCount) → (j : Fin rightCount) → CenteredBilinearPath.Sample (fun vertex => ⟨first i vertex,
      second j vertex⟩))
    {target : BoundaryRibbon.Coordinate} (bounded : ∀ i j, Data.Gaussian.Norm.Basic.normSq (pairs i j).centeredArea ≤
      target)
      :
    Data.Gaussian.Norm.Basic.normSq combined.centeredArea ≤ (leftCount : BoundaryRibbon.Coordinate) * (rightCount :
      BoundaryRibbon.Coordinate) *
      FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq (left i)) * FiniteSum.Fin.sumFin (fun j =>
        Data.Gaussian.Norm.Basic.normSq (right j)) * target := by
  rw [CenteredAreaCombination.Sample.centeredArea_combination left right first second combined pairs]
  exact BilinearCombination.combination_bound left right _ bounded

end Purelib.Integration.Path.CenteredAreaCombination
