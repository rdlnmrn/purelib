module

import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Recurrence
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.GetD
import Purelib.Tactic.QuotientFreeOmega

/-!
# Complete original source coordinates with repeated and zero roots

Automatic preprocessing of `2*z*(z-1/2)^2` supplies its original common
coefficient algebra and bank. The full source companion and characteristic
basis reconstruct an independently displayed five-value recurrence solution,
including its zero-root transient and repeated-root generalized coordinate.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Recurrence

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Multiplicity
open Purelib.LinearAlgebra.Matrix

/-- The actual nonmonic source has a repeated half root and a single zero-root transient. -/
private def source : DensePolynomial Canonical := ⟨[2, -2, 1 / 2, 0]⟩

/-- The original source retains its normalized coefficient table. -/
private theorem normalized : source.normalize = source := by decide +kernel

/-- Its original coefficient table is nonzero. -/
private theorem nonzero : source.isZero = false := by decide +kernel

/-- The actual source has three characteristic coordinates, including multiplicity. -/
private theorem degree : source.natDegree = 3 := by decide +kernel

/-- The original automatic preprocessing supplies the same complete positive-degree payload. -/
private def preprocessing : Squarefree.Decomposition.Compute.PositivePreprocessing source :=
  match Squarefree.Decomposition.Compute.preprocess source with
  | .positive retained => retained
  | .zero zero => False.elim (Bool.noConfusion (nonzero.symm.trans zero))
  | .constant _ degreeZero => False.elim (by
      have impossible : (3 : Nat) = 0 := degree.symm.trans degreeZero
      cases impossible)

/-- The original constant opposite cofactor and preprocessing retain this same source side. -/
private def input : Basis.Coprime.Side.PositiveSideInput source (DensePolynomial.constant 1) :=
  { sourceNormalized := normalized, preprocessing := preprocessing
    oppositeNonzero := by decide +kernel
    sourceOppositeCoprime := Coprime.Operations.CoprimeCertificate.constantRight nonzero }

/-- One actual original prepared bank supplies every formal root and source coefficient image. -/
private def prepared := Roots.prepare input

/-- The complete source recurrence uses only that same original prepared bank. -/
private def recurrence := Roots.Recurrence.prepare prepared

/-- The original final coefficient embedding is read from those same already retained factor stages. -/
private def coefficientMap := Roots.Stages.Images.coefficientMap prepared.separation.prepared.stages

/-- The actual full characteristic word has the independently known original cubic size. -/
private theorem full_count : recurrence.fullWord.length = 3 := recurrence.source_count.trans degree

/-- The same mapped source retains its original cubic degree. -/
private theorem mapped_degree : prepared.mapped.natDegree = 3 :=
  (Roots.Recurrence.degree_eq prepared).trans degree

/-- The actual complete word and original generalized orders preserve both the repeated and zero modes. -/
private theorem original_orders : recurrence.fullWord.map Fin.val = [0, 0, 1] ∧
    List.ofFn (fun column => recurrence.basis.occurrences.orders column) = [0, 1, 0] := by decide +kernel

/-- The nonmonic source-leading reciprocal is computed in the original Gaussian field. -/
private theorem coefficient_inverse : recurrence.coefficientInverse = (⟨1 / 2, 0⟩ : Canonical) := by decide +kernel

/-- The retained original companion consumes that same mapped half reciprocal. -/
private theorem companion_inverse : recurrence.companion.leadingInverse = coefficientMap (⟨1 / 2, 0⟩ : Canonical) :=
  recurrence.companion_inverse.trans (recurrence.leadingInverse_eq.trans (congrArg coefficientMap coefficient_inverse))

/-- The independent five-value source solution is displayed entirely in original Gaussian coefficients. -/
private def originalValues : Vec Canonical 5 :=
  .cons 4 (.cons (5 / 2) (.cons (9 / 4) (.cons (13 / 8) (.cons (17 / 16) .nil))))

/-- The same original embedding materializes those independent values in the actual final coefficient algebra. -/
private def values := Vec.map coefficientMap originalValues

/-- Both complete original source rows are kernel-checked with their original finite bounds. -/
private theorem checked_rows : ∀ start : Fin 2,
    let bound : start.val + prepared.mapped.natDegree < 5 :=
      (congrArg (fun degree => start.val + degree) mapped_degree).symm ▸ Nat.add_lt_add_right start.isLt 3
    sumFin (fun column : Fin prepared.mapped.natDegree =>
      getD recurrence.companion.coefficients column.val 0 *
        values ⟨start.val + column.val, Nat.lt_trans (Nat.add_lt_add_left column.isLt start.val) bound⟩) +
      prepared.mapped.leadingCoeff * values ⟨start.val + prepared.mapped.natDegree, bound⟩ = 0 := by decide +kernel

/-- Every complete original source row is one of those same independently checked bounded rows. -/
private theorem satisfies : recurrence.companion.Satisfies values := by
  intro start bound
  have inside : start < 2 := by
    have degree := mapped_degree
    omega0
  exact checked_rows ⟨start, inside⟩

/-- The full original characteristic prefix fits inside the independent five-value horizon. -/
private theorem enough : recurrence.fullWord.length ≤ 5 := full_count.symm ▸ (by decide : 3 ≤ 5)

/-- The actual full original inverse extracts coefficients from that same independent recurrence prefix. -/
private def recovered := recurrence.basis.coordinates (Split.take enough values)

/-- The recovered coordinates are the independent repeated-root coefficients one and two, and transient three. -/
private theorem recovered_coordinates : ∀ column : Fin 3,
    recovered ⟨column.val, full_count.symm ▸ column.isLt⟩ =
      coefficientMap ((.cons 1 (.cons 2 (.cons 3 .nil)) : Vec Canonical 3) column) := by decide +kernel

/-- The full source-basis construction reconstructs all five original independently supplied values. -/
private theorem reconstructed : Rectangular.apply (recurrence.basis.horizon 5) recovered = values :=
  recurrence.horizon_reconstruct values enough satisfies

/-- The same actual complete coordinates satisfy the original full source recurrence. -/
private theorem produced_satisfies :
    recurrence.companion.Satisfies (Rectangular.apply (recurrence.basis.horizon 5) recovered) :=
  recurrence.horizon_satisfies 5 recovered

/-- Equal full-source horizons determine the same original finite coefficient vector uniquely. -/
private theorem independent (first second : Vec prepared.separation.Scalar recurrence.fullWord.length)
    (equal : Rectangular.apply (recurrence.basis.horizon 5) first =
      Rectangular.apply (recurrence.basis.horizon 5) second) : first = second :=
  recurrence.horizon_independent 5 enough first second equal

/-- Checked same original caches restore the complete source recurrence without reconstructing its parents. -/
private theorem restore : Roots.Recurrence.ofCaches prepared
    recurrence.coefficientInverse recurrence.coefficientInverse_eq
    recurrence.leadingInverse recurrence.leadingInverse_eq
    recurrence.leadingUnit recurrence.companion recurrence.companion_eq recurrence.fullWord recurrence.fullWord_eq
    recurrence.basis recurrence.basis_eq = recurrence := rfl

end TestPurelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Recurrence
