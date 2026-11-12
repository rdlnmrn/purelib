module

import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Companion.Execution

/-!
# Companion execution over a ring with zero divisors

The original quadratic pair at parameter zero has a nonzero square-zero
coordinate. A leading-unit companion operates over that same ring without
an explicit-field instance or a nonzero-product law.
-/

namespace TestPurelib.Polynomial.Recurrence.Ring

open Purelib.Algebra.Quadratic
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data renaming Vector → Vec

/-- The original two-coordinate ring with a square-zero generator. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The original nonzero nilpotent coordinate. -/
private def epsilon : Dual := Pair.generator

/-- The original monic source with its nilpotent exact root. -/
private def polynomial : DensePolynomial Dual := ⟨[1, -epsilon]⟩

/-- The original leading-unit constructor uses no field structure on Dual. -/
private def companion : Companion polynomial := Companion.ofUnit polynomial (by decide) 1 (by decide)

/-- Its retained initial state has the same source-computed dimension. -/
private def initial : Vec Dual polynomial.natDegree := .cons 1 .nil

/-- The retained generator is an actual nonzero coordinate. -/
private theorem epsilon_nonzero : epsilon ≠ 0 := by decide +kernel

/-- Its exact square is zero in the original coordinate ring. -/
private theorem epsilon_square : epsilon * epsilon = 0 := by decide +kernel

/-- The original nilpotent coordinate zeros its same source polynomial. -/
private theorem source_zero : polynomial.eval epsilon = 0 := by decide +kernel

/-- The initial retained companion reading is one. -/
private theorem reading_initial : companion.reading initial 0 = 1 := by decide +kernel

/-- One actual companion transition reads the nonzero nilpotent. -/
private theorem reading_next : companion.reading initial 1 = epsilon := by decide +kernel

/-- The following actual transition reads its exact zero square. -/
private theorem reading_square : companion.reading initial 2 = 0 := by decide +kernel

end TestPurelib.Polynomial.Recurrence.Ring
