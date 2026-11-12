module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
public import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Data.Gaussian.Scale
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Maximum-coordinate variation of the same cached cell restrictions

Only the original cached affine restriction and its physical displacement
are used. Nonnegative ordered widths preserve the original total rational
variation, including zero-width and constant physical cells.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

/-- The same cached restricted cell retains its original rational-width Gaussian displacement. -/
private theorem displacement_scale (cell : CellModel) {first last : Rational}
    (cached : Polynomial.Ascending.Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).displacement = Scale.scale (last - first) cell.displacement := by
  have scalar : (Cast.Path.ofCoordinate last - Cast.Path.ofCoordinate first) * cell.displacement =
      Scale.scale (last - first) cell.displacement := by
    apply Data.Gaussian.Basic.ext
    · change (last - first) * cell.displacement.re - (0 - 0) * cell.displacement.im =
        (last - first) * cell.displacement.re
      ring1
    · change (last - first) * cell.displacement.im + (0 - 0) * cell.displacement.re =
        (last - first) * cell.displacement.im
      ring1
  exact (displacement_eq cell cached).trans scalar

/-- The original ordered cached child contributes exactly its nonnegative width times the parent variation. -/
theorem maximum_displacement (cell : CellModel) {first last : Rational}
    (cached : Polynomial.Ascending.Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) (nonnegative : 0 ≤ last - first) :
    Norm.Components.maximum (model cell cached).displacement =
      (last - first) * Norm.Components.maximum cell.displacement :=
  (congrArg Norm.Components.maximum (displacement_scale cell cached)).trans
    (Norm.Components.maximum_scale (last - first) nonnegative cell.displacement)

/-- A complete ordered family of the same cached restrictions preserves the original physical variation.

The original interval-chain operations supply nonnegative widths and their
exact sum one. The cache family is retained as an input; no canonical
restriction is reconstructed and no repeated occurrence is discarded.
-/
theorem sum_maximum_displacement {count : Nat} (cell : CellModel)
    (first last : Fin count → Rational)
    (cached : (index : Fin count) → Polynomial.Ascending.Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate (first index)) (Cast.Path.ofCoordinate (last index)))
    (nonnegative : ∀ index, 0 ≤ last index - first index)
    (complete : sumFin (fun index => last index - first index) = 1) :
    sumFin (fun index => Norm.Components.maximum (model cell (cached index)).displacement) =
      Norm.Components.maximum cell.displacement :=
  (sumFin_congr (fun index => maximum_displacement cell (cached index) (nonnegative index))).trans
    ((sumFin_mul_right _ _).trans ((congrArg (fun width : Rational =>
      width * Norm.Components.maximum cell.displacement) complete).trans
        (Data.Rat.Fraction.Field.one_mul _)))

end Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

end
