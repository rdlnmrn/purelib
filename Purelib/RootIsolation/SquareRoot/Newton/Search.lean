module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Grid.Nearest.Basic
public import Purelib.RootIsolation.SquareRoot.Newton.Basic

import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.RootIsolation

section
/-!
# Rounded, checked finite square-root proposals

Round each speculative Newton point to a dyadic grid before checking it and
before computing the next point.  This avoids carrying the exact Newton
orbit's rapidly growing denominators into an accepted root sample.

The predicate, not Newton convergence or a rounding estimate, certifies the
returned point.  A finite unsuccessful search returns `none`; callers retain
their independently proved total fallback.  No floating-point arithmetic or
external certificate producer is involved.
-/

@[expose] public section

namespace Purelib.CCL.Geometry.CheckedSquareRootNewton

end Purelib.CCL.Geometry.CheckedSquareRootNewton

section
namespace Purelib.RootIsolation.SquareRoot.Newton.Search

open Purelib.CCL.Geometry.CheckedSquareRootNewton
/-- A real radicand suggests axis-aligned samples.  Check both projections
before retaining a spurious small off-axis coordinate.  The exact predicate
still checks the selected occurrence and accuracy: the real-coefficient
test is only a cheap way to choose useful proposals. -/
private def axisCandidate
  (parameter : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] (point : Canonical) :
    Option {point : Canonical // acceptable point} :=
  if parameter.im = 0 then
    let realPoint : Canonical := ⟨point.re, 0⟩
    if valid : acceptable realPoint then some ⟨realPoint, valid⟩
    else
      let imaginaryPoint : Canonical := ⟨0, point.im⟩
      if valid : acceptable imaginaryPoint then some ⟨imaginaryPoint, valid⟩
      else none
  else none
end Purelib.RootIsolation.SquareRoot.Newton.Search
end

namespace Purelib.RootIsolation.SquareRoot.Newton.Search

/-- Every returned sample carries the caller's exact finite check.  A rejected
proposal receives two more binary grid digits on the next iteration.  For
real radicands, certified axis projections are preferred when available. -/
def search (parameter : Canonical) (acceptable :
  Canonical → Prop)
    [DecidablePred acceptable] : Nat → Fraction.Rational → Canonical →
      Option {point : Canonical // acceptable point}
  | 0, _grid, _proposal => none
  | fuel + 1, grid, proposal =>
      let point := Grid.Nearest.Basic.rounded grid proposal
      let axisResult : Option {point : Canonical // acceptable point} :=
        if parameter.im = 0 then
          let realPoint : Canonical := ⟨point.re, 0⟩
          if valid : acceptable realPoint then some ⟨realPoint, valid⟩
          else
            let imaginaryPoint : Canonical := ⟨0, point.im⟩
            if valid : acceptable imaginaryPoint then some ⟨imaginaryPoint, valid⟩
            else none
        else none
      match axisResult with
      | some accepted => some accepted
      | none =>
          if valid : acceptable point then some ⟨point, valid⟩
          else search parameter acceptable fuel (grid / 4)
            (SquareRoot.Newton.Basic.step parameter point)

end Purelib.RootIsolation.SquareRoot.Newton.Search

end

end

section
section
@[expose] public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.RootIsolation.SquareRoot.Newton.Search

/-- Check axis projections for a real radicand, then the original proposed point.

Each accepted point carries the caller's exact predicate; a failed finite check returns no candidate. -/
def select (parameter : Canonical) (acceptable :
  Canonical → Prop) [DecidablePred acceptable]
    (point : Canonical) : Option {value : Canonical // acceptable value} :=
  let axisResult : Option {value : Canonical // acceptable value} :=
    if parameter.im = 0 then
      let realPoint : Canonical := ⟨point.re, 0⟩
      if valid : acceptable realPoint then some ⟨realPoint, valid⟩
      else
        let imaginaryPoint : Canonical := ⟨0, point.im⟩
        if valid : acceptable imaginaryPoint then some ⟨imaginaryPoint, valid⟩
        else none
    else none
  match axisResult with
  | some accepted => some accepted
  | none => if valid : acceptable point then some ⟨point, valid⟩ else none

/-- One positive-fuel search step checks the rounded proposal, then quarters the grid and continues Newton iteration if
rejected.

The original axis-specific selection order and accepted proof are retained. A rejected rounded proposal advances the
same recursive search with one less step. -/
theorem search_step (parameter : Canonical)
  (acceptable : Canonical → Prop) [DecidablePred acceptable]
    (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical) :
    search parameter acceptable (fuel + 1) grid proposal =
      match select parameter acceptable (Grid.Nearest.Basic.rounded grid proposal) with
      | some accepted => some accepted
      | none => search parameter acceptable fuel (grid / 4) (SquareRoot.Newton.Basic.step
        parameter (Grid.Nearest.Basic.rounded grid proposal)) := by
  by_cases axis : parameter.im = 0
  · by_cases real : acceptable (⟨(Grid.Nearest.Basic.rounded grid proposal).re, 0⟩ : Canonical)
    · simp only [search,
        select, if_pos axis, dif_pos real, -eq_self, -iff_self]
      rfl
    · by_cases imaginary : acceptable (⟨0, (Grid.Nearest.Basic.rounded grid proposal).im⟩ : Canonical)
      · simp only [search,
          select, if_pos axis,
          dif_neg real, dif_pos imaginary, -eq_self, -iff_self]
        rfl
      · by_cases valid : acceptable (Grid.Nearest.Basic.rounded grid proposal)
        · simp only [search,
            select, if_pos axis,
            dif_neg real, dif_neg imaginary, dif_pos valid, -eq_self, -iff_self]
          rfl
        · simp only [search,
            select, if_pos axis,
            dif_neg real, dif_neg imaginary, dif_neg valid, -eq_self, -iff_self]
          rfl
  · by_cases valid : acceptable (Grid.Nearest.Basic.rounded grid proposal)
    · simp only [search,
        select, if_neg axis, dif_pos valid, -eq_self, -iff_self]
      rfl
    · simp only [search,
        select, if_neg axis, dif_neg valid, -eq_self, -iff_self]
      rfl

end Purelib.RootIsolation.SquareRoot.Newton.Search

end

end
