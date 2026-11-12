module

import Purelib.Algebra.Quadratic.Pair.Norm.Rational

/-!
# Original quadratic-pair inversion at a nonsquare rational parameter

The cached finite inspection of two excludes every rational root. It certifies
inversion for every nonzero pair at that parameter, alongside exact closed
coordinates for one plus the generator and a degenerate square-parameter norm.
-/

namespace TestPurelib.Algebra.QuadraticPairNorm

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Data.Rat.Fraction

example : (⟨1, 1⟩ : Pair Rational (-2)).norm = -1 := by decide +kernel
example : (⟨1, 1⟩ : Pair Rational (-2)).inverse = ⟨-1, 1⟩ := by decide +kernel
example : (⟨2, 1⟩ : Pair Rational (-4)).norm = 0 := by decide +kernel

example (value : Pair Rational (-2)) (nonzero : value ≠ 0) : value.norm ≠ 0 :=
  Pair.norm_ne_zero_of_inspection (Square.inspect 2) (by decide +kernel) nonzero

example (value : Pair Rational (-2)) (nonzero : value ≠ 0) : value * value.inverse = 1 :=
  Pair.mul_inverse_of_inspection (Square.inspect 2) (by decide +kernel) value nonzero

example (value : Pair Rational (-2)) (nonzero : value ≠ 0) : value.inverse * value = 1 :=
  Pair.inverse_mul_of_inspection (Square.inspect 2) (by decide +kernel) value nonzero

end TestPurelib.Algebra.QuadraticPairNorm
