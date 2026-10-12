module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import all Purelib.Geometry.Rational.Box.CenteredSquare

import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Power.Isolation
import Purelib.RootIsolation.Power.Isolation.Track
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Newton
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Source.Refinement

open Purelib.Data.Gaussian

/-- The source state used to compute the Newton correction is retained inside
its resulting robust owner. -/
theorem unitRobustSourceState_refinesBox
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.Refines
        (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
          index) := open Purelib.Algebra.Field in by
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let q := r / 4
  have qNonnegative : (0 : Fraction.Rational) ≤ q :=
    Fraction.Order.Field.div_nonneg_direct
      (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
      (by decide)
  have twiceQLe : 2 * q ≤ r := by
    have inverseFour : (4 : Fraction.Rational)⁻¹ = 1 / 4 := by decide
    dsimp only [q]
    rw [ExplicitField.div_eq_mul_inv, inverseFour]
    have coefficient : (2 : Fraction.Rational) * (1 / 4) = 1 / 2 := by decide
    calc
      2 * (r * (1 / 4 : Fraction.Rational)) =
          ((2 : Fraction.Rational) * (1 / 4)) * r := by ring1
      _ = (1 / 2 : Fraction.Rational) * r := by rw [coefficient]
      _ ≤ 1 * r :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree
            degreeAtLeastTwo).le
      _ = r := by ring1
  exact Box.CenteredSquare.box_refines_centeredSquare_of_anchor_near qNonnegative
    (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
    (Power.Unit.Source.unitRobustSourceState_diagonalSq_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
    (Power.Unit.Newton.unitRobustNewton_displacement_le_quarterRadius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index)
    twiceQLe
end Purelib.RootIsolation.Power.Unit.Source.Refinement

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Source.Refinement

open Purelib.Data.Gaussian

/-- The robust source state refines its own original isolated track's initial box. -/
theorem unitRobustSourceState_refinesInitial
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo index).box.Refines
        (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial.box :=
  (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index).nested
    (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo index).initial
    (Power.Unit.Radius.unitRobustSourceRadius parameterUnit degree degreeAtLeastTwo)
    (Power.Unit.Radius.unitRobustSourceRadius_pos parameterUnit degree degreeAtLeastTwo)
end Purelib.RootIsolation.Power.Unit.Source.Refinement

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Source.Refinement

open Purelib.Data.Gaussian

/-- The two source states retain the original isolation family's positive
coordinate separation. -/
theorem unitRobustSourceState_pairwiseSeparated
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (left right : Fin degree.value) (different : left ≠ right) :
    (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
      degreeAtLeastTwo left).box.Separated
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right).box := by
  let castIndex : Fin degree.value →
      Fin (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).natDegree :=
    Fin.cast (Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree parameter degree).symm
  have castDifferent : castIndex left ≠ castIndex right := by
    intro equal
    apply different
    apply Fin.ext
    have values := congrArg (fun index => index.val) equal
    change left.val = right.val at values
    exact values
  have initialSeparated := FTA.Squarefree.AdapterResult.trackAt_pairwiseSeparated
    (Power.Isolation.isolationResult parameterNonzero degree degreeAtLeastTwo)
    (castIndex left) (castIndex right) castDifferent
  exact Box.Separated.of_refines initialSeparated
    (unitRobustSourceState_refinesInitial parameterNonzero parameterUnit degree
      degreeAtLeastTwo left)
    (unitRobustSourceState_refinesInitial parameterNonzero parameterUnit degree
      degreeAtLeastTwo right)
end Purelib.RootIsolation.Power.Unit.Source.Refinement

end
