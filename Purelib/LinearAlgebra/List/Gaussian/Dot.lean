module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Data.List.Gaussian.Arithmetic
import Purelib.Tactic.Ring

open Purelib

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.LinearAlgebra.List.Gaussian.Dot

set_option backward.match.sparseCases false in
/-- Finite dot product; missing coordinates are not manufactured. -/
def dot : List Data.Gaussian.Basic.Canonical → List
  Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical
  | left :: leftTail, right :: rightTail =>
      left * right + dot leftTail rightTail
  | _, _ => 0

/-- Taking the finite Gaussian dot product commutes with coefficientwise addition.

The recursion stops when the direction list ends, preserving the original conventions for unequal list lengths. -/
theorem dot_addPartials : ∀ left right direction,
    dot (Data.List.Gaussian.Arithmetic.addCoefficients left right) direction =
      dot left direction + dot right direction
  | [], right, direction => by
      simp only [Data.List.Gaussian.Arithmetic.addCoefficients]
      cases direction <;>
        simp only [-eq_self, -iff_self, dot, Data.Gaussian.Basic.zero_add] <;> rfl
  | left :: leftTail, [], direction => by
      simp only [Data.List.Gaussian.Arithmetic.addCoefficients]
      cases direction <;>
        simp only [-eq_self, -iff_self, dot, Data.Gaussian.Basic.add_zero] <;> rfl
  | left :: leftTail, right :: rightTail, [] => by
      change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.zero_re,
          Data.Gaussian.Basic.zero_im] <;> ring1
  | left :: leftTail, right :: rightTail,
      direction :: directionTail => by
      rw [Data.List.Gaussian.Arithmetic.addCoefficients, dot,
        dot, dot,
        dot_addPartials]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.mul_im] <;> ring1

/-- Scaling every left coefficient scales the finite Gaussian dot product.

Both sides retain the same direction list and truncate at the first exhausted list. -/
theorem dot_scalePartials (factor : Data.Gaussian.Basic.Canonical) : ∀
  partials direction,
    dot (Data.List.Gaussian.Arithmetic.scalePartials factor partials) direction =
      factor * dot partials direction
  | [], direction => by
      cases direction <;>
        simp only [-eq_self, -iff_self, Data.List.Gaussian.Arithmetic.scalePartials, List.map,
          dot, Data.Gaussian.Basic.mul_zero] <;> rfl
  | coefficient :: partials, [] => by
      simp only [-eq_self, -iff_self, Data.List.Gaussian.Arithmetic.scalePartials, List.map,
        dot, Data.Gaussian.Basic.mul_zero] ; rfl
  | coefficient :: partials, direction :: directions => by
      have inductionHypothesis :=
        dot_scalePartials factor partials directions
      change dot (List.map (fun value => factor * value) partials) directions =
        factor * dot partials directions at inductionHypothesis
      rw [Data.List.Gaussian.Arithmetic.scalePartials, List.map, dot,
        dot, inductionHypothesis]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.mul_im] <;> ring1

end Purelib.LinearAlgebra.List.Gaussian.Dot

end
