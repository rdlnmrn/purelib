module

import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast

/-!
# Actual endpoint root bounds with a distinct observed candidate

The original degree-one companion root reads as one half even when its
cyclic observation uses zero as the candidate. The paid original realization
therefore checks the final formal-root reading bound independently of any
claim that an observed candidate is itself the exact original root.
-/

namespace TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Polynomial.Dense.Roots.Tower.Reading (Parameters Request Realization)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming Observation → CyclicObservation
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading (ColumnBound)
open Purelib.Algebra.Ring (GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction

/-- The original linear polynomial has its root at one half. -/
private def source : DensePolynomial Canonical := ⟨[1, -(1 / 2)]⟩

/-- The original constructor retains its one companion adjunction and actual quotient. -/
private def tower : Tower Canonical inferInstance inferInstance source :=
  Tower.prepare source (by decide +kernel) 1 (by decide +kernel)

/-- The same original fixed-radius bounds are computed before observing zero as a candidate. -/
private def parameters : Parameters tower Norm.weight 1 1 :=
  Parameters.prepare tower Norm.weight 1 1 (by decide) (by decide)

/-- The original positive target is represented directly without recursive numeral casting. -/
private def target : Rational := Cast.fromInt 1024

/-- A positive target determines the original sufficient backward stage request. -/
private def request : Request parameters target := Request.prepare parameters target (by decide +kernel)

/-- The actual original observation pays its column residual while using a candidate different from its exact root. -/
private def realized : Realization request.budget GaussianReading.identity rfl :=
  Realization.step _ _
    (CyclicObservation.prepare _ GaussianReading.identity rfl 0 (by decide +kernel)
      (1 / 4) (by decide +kernel) (by unfold ColumnBound; decide +kernel))
    (by decide +kernel) (Realization.constant _ _ (by decide))

/-- The original source residual at the observed zero candidate is nonzero. -/
private theorem candidate_not_root : source.eval 0 ≠ 0 := by decide +kernel

/-- The same cached endpoint reads its original formal root as one half and not as the zero candidate. -/
private theorem actual_root_reading :
    realized.finalReading.read (tower.blocks[0]'(by decide +kernel)).point = 1 / 2 ∧
      realized.finalReading.read (tower.blocks[0]'(by decide +kernel)).point ≠ 0 := by decide +kernel

/-- The original pre-observation parameter total has its exact source-fixed value. -/
private theorem source_root_bound : parameters.rootBoundTotal = 1 / 2 := by decide +kernel

/-- Every original bounded block occurrence satisfies the actual cached final-reading bound. -/
private theorem final_roots_bounded (index : Fin tower.blocks.length) :
    Norm.Basic.normSq (realized.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤
      parameters.rootBoundTotal := realized.root_normSq_le index

/-- The same original membership view preserves the complete final-reading bound without a new root enumeration. -/
private theorem final_blocks_bounded : ∀ block ∈ tower.blocks,
    Norm.Basic.normSq (realized.finalReading.read block.point) ≤ parameters.rootBoundTotal :=
  realized.blocks_normSq_le

end TestPurelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots
