module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic

public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Integration.Path.CenteredAreaCombination
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

@[expose] public section

/-! Homogeneous comparison of two cached centered areas. The same coefficient
vector weights both sides, while all basis-pair errors remain explicit. -/
namespace Purelib.Integration.Path.CenteredAreaDifference

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {count otherCount leftCount rightCount : Nat}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
/-- Uniform paired centered-area difference bounds control the two retained combined sample areas.

The two paths may have different vertex counts; both coefficient families and the separate left and right sample owners
remain fixed in the exact count-and-norm estimate. -/
theorem Sample.centeredArea_difference_bound
    (left : Fin leftCount → Basic.Canonical) (right : Fin rightCount → Basic.Canonical)
    (firstLeft : Fin leftCount → Fin (count + 1) → Basic.Canonical)
    (firstRight : Fin leftCount → Fin (otherCount + 1) → Basic.Canonical)
    (secondLeft : Fin rightCount → Fin (count + 1) → Basic.Canonical)
    (secondRight : Fin rightCount → Fin (otherCount + 1) → Basic.Canonical)
    (combinedLeft : CenteredBilinearPath.Sample (fun vertex => ⟨sumFin (fun row => left row * firstLeft row vertex),
      FiniteSum.Fin.sumFin (fun row => right row * secondLeft row vertex)⟩))
    (combinedRight : CenteredBilinearPath.Sample (fun vertex => ⟨sumFin (fun row => left row * firstRight row vertex),
      FiniteSum.Fin.sumFin (fun row => right row * secondRight row vertex)⟩))
    (leftPairs : (i : Fin leftCount) → (j : Fin rightCount) →
      CenteredBilinearPath.Sample (fun vertex => ⟨firstLeft i vertex, secondLeft j vertex⟩))
    (rightPairs : (i : Fin leftCount) → (j : Fin rightCount) →
      CenteredBilinearPath.Sample (fun vertex => ⟨firstRight i vertex, secondRight j vertex⟩))
    {target : BoundaryRibbon.Coordinate}
    (bounded : ∀ i j, Data.Gaussian.Norm.Basic.normSq ((leftPairs i j).centeredArea - (rightPairs i j).centeredArea) ≤
      target) :
    Data.Gaussian.Norm.Basic.normSq (combinedLeft.centeredArea - combinedRight.centeredArea) ≤
      (leftCount : BoundaryRibbon.Coordinate) * (rightCount : BoundaryRibbon.Coordinate) *
        FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Norm.Basic.normSq (left i)) * FiniteSum.Fin.sumFin (fun j =>
          Data.Gaussian.Norm.Basic.normSq (right j)) * target := by
  rw [CenteredAreaCombination.Sample.centeredArea_combination left right firstLeft secondLeft combinedLeft leftPairs,
    CenteredAreaCombination.Sample.centeredArea_combination left right firstRight secondRight combinedRight rightPairs]
  have equal :
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (leftPairs i j).centeredArea)) -
        FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j * (rightPairs i j).centeredArea))
          =
      FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (fun j => left i * right j *
        ((leftPairs i j).centeredArea - (rightPairs i j).centeredArea))) := by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro j
    ring1
  rw [equal]
  exact BilinearCombination.combination_bound left right _ bounded

end Purelib.Integration.Path.CenteredAreaDifference
