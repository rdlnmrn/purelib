module
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.CCL.Transducer.Mode.Grammar
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Constants.Inverse
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Data.CCL.Transducer.Mode.Parser

/-! ## Matrix effect of complete controller chunks -/

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL.Transducer
/-- Read the parser block kind corresponding to the retained initial-high or subsequent-loop kind. -/
def regularBlockKind : Mode.Basic.RegularKind →
    Parser.Syntax.BlockKind
  | .initialHigh => .initialHigh
  | .loop => .loop

/-- A regular unary true bit preserves the exact retained parser matrix. -/
public theorem fold_regular_unary_matrix
    (parser : Encoding.Parser.State) (kind : Mode.Basic.RegularKind)
    (count : Nat)
    (phase : parser.phase = Mode.Grammar.regularRawPhase kind count) :
    ([true].foldl Parser.State.step parser).matrix =
      parser.matrix := by
  cases parser with
  | mk parserPhase matrix history =>
      cases kind <;> simp only [Mode.Grammar.regularRawPhase] at phase <;>
        subst parserPhase <;> rfl

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open _root_.Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A regular false separator and sector code right-multiply the retained parser matrix by that exact completed block
matrix. -/
public theorem fold_regular_sector_matrix
    (parser : Encoding.Parser.State) (kind : Mode.Basic.RegularKind)
    (count : Nat) (phase : parser.phase = Mode.Grammar.regularRawPhase kind count)
    (sector : ComplexContinuedFraction.Encoding.Sector) :
    ((false :: sector.code).foldl Parser.State.step parser).matrix =
      Matrix2.mul parser.matrix
        (Block.Matrix.blockMatrix
          (regularBlockKind kind) count sector) := by
  cases parser with
  | mk parserPhase matrix history =>
      cases kind <;> simp only [Mode.Grammar.regularRawPhase] at phase <;>
        subst parserPhase <;> cases sector <;> rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Normalizing gamma-to-count times a value in either regular branch recovers the exact original value. -/
theorem regularNormalized_scaled (kind : Mode.Basic.RegularKind)
    (count : Nat) (value : Basic.Canonical) :
    Parser.Semantics.Basic.normalizedValue (regularBlockKind kind) count
        (Power.natPow Basic.Canonical.gamma count * value) = value := by
  cases kind <;>
    simp only [Parser.Semantics.Basic.normalizedValue]
  all_goals
    let power := Power.natPow Basic.Canonical.gamma count
    have powerNonzero : power ≠ 0 :=
      Power.natPow_ne_zero_direct Basic.Canonical.gamma Constants.Inverse.gamma_ne count
    have cancellation : power * power⁻¹ = 1 :=
      Basic.Canonical.mul_inv_cancel power powerNonzero
    calc
      power * value * power⁻¹ = (power * power⁻¹) * value := by
        apply Basic.ext <;>
          simp only [Basic.mul_re, Basic.mul_im] <;> ring1
      _ = value := by
        rw [cancellation, Basic.one_mul]

end Purelib.Data.CCL.Transducer.Mode.Parser

end
