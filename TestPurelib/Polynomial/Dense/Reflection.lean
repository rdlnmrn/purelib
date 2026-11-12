module

import Purelib.Polynomial.Dense.Reflection
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Formal reflection over zero-divisor and zero coefficient rings

A scalar nilpotent evaluation loses a nonzero original coefficient. The finite
formal shift retains that same coefficient in its distinguished column and
rules out false formal equality. A separate one-element coefficient ring
checks the construction without a nontriviality or degree premise.
-/

namespace TestPurelib.Polynomial.Dense.Reflection

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Quadratic
open Purelib.LinearAlgebra.Matrix

/-- The same original pair algebra at parameter zero retains its square-zero coordinate. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nilpotent coefficient has nonzero second coordinate. -/
private def epsilon : Dual := Pair.generator

/-- The original descending table has one nonzero nilpotent coefficient at degree two. -/
private def polynomial : DensePolynomial Dual := ⟨[epsilon, 0, 0]⟩

/-- An ordinary scalar evaluation at the same nilpotent loses that nonzero coefficient. -/
private theorem scalar_evaluation_zero : polynomial.eval epsilon = 0 := by decide +kernel

/-- The original normalized table still contains its nonzero leading coefficient. -/
private theorem normalized_nonzero : polynomial.normalize ≠ (0 : DensePolynomial Dual).normalize := by decide +kernel

/-- One actual cached four-dimensional nilpotent shift supplies the formal evaluation algebra. -/
private def cyclic := Cyclic.shift Dual 4 (by decide +kernel)

/-- Formal evaluation reads the original nilpotent coefficient at its original degree-two slot. -/
private theorem formal_coefficient :
    ((Map.map (Cyclic.Element.scalar cyclic) polynomial).eval (Cyclic.Element.root cyclic)).matrix
      2 cyclic.origin = epsilon :=
  (Reflection.coefficient_readback cyclic rfl polynomial 2).trans (by decide +kernel)

/-- The original degree-one coefficient is zero in the same retained finite formal evaluation. -/
private theorem formal_zero_slot :
    ((Map.map (Cyclic.Element.scalar cyclic) polynomial).eval (Cyclic.Element.root cyclic)).matrix
      1 cyclic.origin = 0 :=
  (Reflection.coefficient_readback cyclic rfl polynomial 1).trans (by decide +kernel)

/-- The original finite shift distinguishes the nonzero polynomial from zero despite its scalar evaluation. -/
private theorem formal_not_zero : ¬ Reflection.Agreement polynomial 0 :=
  fun agreement => normalized_nonzero (Reflection.normalize_eq polynomial 0 agreement)

namespace ZeroRing

/-- The one-element coefficient addition retains its only possible value. -/
local instance : Add Unit := ⟨fun _ _ => ()⟩

/-- The one-element coefficient multiplication retains its only possible value. -/
local instance : Mul Unit := ⟨fun _ _ => ()⟩

/-- The one-element coefficient negation retains its only possible value. -/
local instance : Neg Unit := ⟨fun _ => ()⟩

/-- The one-element coefficient zero is its only value. -/
local instance : Zero Unit := ⟨()⟩

/-- The one-element coefficient unit is the same only value. -/
local instance : One Unit := ⟨()⟩

/-- The original finite scalar operation builder verifies the one-element commutative ring. -/
local instance : CommRing Unit := Purelib.Algebra.Ring.commRingOfAxioms
  (fun _ _ _ => rfl) (fun value => by cases value; rfl) (fun _ => rfl)
  (fun _ _ _ => rfl) (fun _ _ => rfl) (fun value => by cases value; rfl)
  (fun _ _ _ => rfl) (fun _ _ => ()) (fun _ _ => rfl)

/-- The source retains three coefficient slots even though every coefficient is zero. -/
private def polynomial : DensePolynomial Unit := ⟨[(), (), ()]⟩

/-- The computed four-dimensional finite shift evaluates both actual tables equally over the zero ring. -/
private theorem agreement : Reflection.Agreement polynomial 0 := by
  unfold Reflection.Agreement
  decide +kernel

/-- The same formal reflection API returns equality of the original normalized coefficient tables. -/
private theorem normalized_eq : polynomial.normalize = (0 : DensePolynomial Unit).normalize :=
  Reflection.normalize_eq polynomial 0 agreement

end ZeroRing

end TestPurelib.Polynomial.Dense.Reflection
