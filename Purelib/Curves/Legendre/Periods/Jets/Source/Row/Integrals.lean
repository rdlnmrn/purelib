module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Fin.Two
import Purelib.Tactic.Ring

/-! # The exact linear combination of six numerical Legendre channels

The original connection and scalar coefficients act on the same finite
six-channel samples. Pointwise equality and ordered addition preserve
these combinations without identifying source or geometric owners.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Row

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre.PicardFuchs

/-- Combine the six original numerical integrals with the actual selected connection or scalar row coefficients. -/
@[expose] def combine (parameter : Canonical) : Row → (Fin 6 → Canonical) → Canonical
  | .inl coordinate, values => Fin.cases
      (Clearance.connectionDenominator parameter * values 2 - (parameter * values 0 - values 1))
      (fun _ => Clearance.connectionDenominator parameter * values 3 -
        (parameter * values 0 - parameter * values 1)) coordinate
  | .inr _, values => 4 * parameter * (1 - parameter) * values 4 +
      4 * (1 - 2 * parameter) * values 2 - values 0

/-- Pointwise equality of the SAME six scalar readings preserves the selected exact row combination. -/
theorem combine_congr (parameter : Canonical) (row : Row) (first last : Fin 6 → Canonical)
    (each : ∀ index, first index = last index) :
    combine parameter row first = combine parameter row last := by
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
      · cases zero
        change _ * first 2 - (parameter * first 0 - first 1) = _
        rewrite [each 2, each 0, each 1]
        rfl
      · cases one
        change _ * first 3 - (parameter * first 0 - parameter * first 1) = _
        rewrite [each 3, each 0, each 1]
        rfl
  | inr _ =>
      change 4 * parameter * (1 - parameter) * first 4 + 4 * (1 - 2 * parameter) * first 2 - first 0 = _
      rewrite [each 4, each 2, each 0]
      rfl

/-- An empty six-channel numerical word has zero selected row combination. -/
theorem combine_zero (parameter : Canonical) (row : Row) :
    combine parameter row (fun _ => 0) = 0 := by
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
      · cases zero
        change _ * 0 - (parameter * 0 - 0) = 0
        ring1
      · cases one
        change _ * 0 - (parameter * 0 - parameter * 0) = 0
        ring1
  | inr _ =>
      change 4 * parameter * (1 - parameter) * 0 + 4 * (1 - 2 * parameter) * 0 - 0 = 0
      ring1

/-- Ordered addition of two actual six-channel sample vectors adds their exact selected row combinations. -/
theorem combine_add (parameter : Canonical) (row : Row) (first last : Fin 6 → Canonical) :
    combine parameter row (fun index => first index + last index) =
      combine parameter row first + combine parameter row last := by
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
      · cases zero
        change Clearance.connectionDenominator parameter * (first 2 + last 2) -
          (parameter * (first 0 + last 0) - (first 1 + last 1)) =
            (Clearance.connectionDenominator parameter * first 2 - (parameter * first 0 - first 1)) +
            (Clearance.connectionDenominator parameter * last 2 - (parameter * last 0 - last 1))
        ring1
      · cases one
        change Clearance.connectionDenominator parameter * (first 3 + last 3) -
          (parameter * (first 0 + last 0) - parameter * (first 1 + last 1)) =
            (Clearance.connectionDenominator parameter * first 3 - (parameter * first 0 - parameter * first 1)) +
            (Clearance.connectionDenominator parameter * last 3 - (parameter * last 0 - parameter * last 1))
        ring1
  | inr _ =>
      change 4 * parameter * (1 - parameter) * (first 4 + last 4) +
        4 * (1 - 2 * parameter) * (first 2 + last 2) - (first 0 + last 0) =
          (4 * parameter * (1 - parameter) * first 4 + 4 * (1 - 2 * parameter) * first 2 - first 0) +
          (4 * parameter * (1 - parameter) * last 4 + 4 * (1 - 2 * parameter) * last 2 - last 0)
      ring1

end Purelib.Curves.Legendre.Periods.Jets.Source.Row

end
