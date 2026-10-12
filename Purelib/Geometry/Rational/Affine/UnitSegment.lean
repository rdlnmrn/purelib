module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Affine
public import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational

section
@[expose] public section

/-!
# Finite radial bounds for a primitive factor

Integrate the finite polynomial u G(w u^e) on the displayed unit segment,
where e is one or two. The existing finite subdivision estimate gives a
bound for G(w) from its Euler differential expression. The auxiliary
polynomial is used only in the proof; executable callers retain their
original factor and a refinement-independent numerical ceiling.
-/

namespace Purelib.Geometry.Rational.Affine.UnitSegment
open _root_.Purelib.Data.Gaussian.Cast.Path (ofCoordinate)
open _root_.Purelib.Geometry.Rational.Affine (line)

/-- The degenerate rational box consisting of the real unit segment. -/
public def unitBox : Rational.Box := ⟨0, 1, 0, 0,
  by decide, le_rfl⟩

/-- The affine line from zero in direction one is the real embedding of its parameter. -/
public theorem unit_line (parameter : Fraction.Rational) :
  Affine.line 0 1 parameter = Path.ofCoordinate parameter := by
  rw [Affine.line, _root_.mul_one, _root_.zero_add]

end Purelib.Geometry.Rational.Affine.UnitSegment

end
