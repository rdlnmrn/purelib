module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Newton.Square.Separated
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Newton
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Power.Unit.Box.Winding

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Each fixed robust owner has raw winding four. -/
theorem unitRobustBox_rawWindingFour
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value) :
    Winding.Box.Basic.quadrupledBoxWinding (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)
      (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
        index) = 4 := open Purelib.Geometry.Rational in by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let source := Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let newton := Power.Unit.Newton.unitRobustNewton parameterNonzero parameterUnit degree
    degreeAtLeastTwo index
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  have degreeTwo : 2 ≤ p.natDegree := by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact degreeAtLeastTwo
  have targetRefines :
      (Box.Square.Centered.Affine.centeredSquare
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box) r
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le).Refines
          ambient := by
    rw [← Power.Unit.Box.unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
      degree degreeAtLeastTwo index]
    exact Power.Unit.Box.unitRobustBox_refinesAmbient parameterNonzero parameterUnit degree
      degreeAtLeastTwo index
  have displacement :
      normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    rw [← newton.point_eq]
    exact Power.Unit.Box.unitRobustNewton_displacement_le_radius_sq parameterNonzero
      parameterUnit degree degreeAtLeastTwo index
  have taylor :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient *
        r ^ 2) ≤ separation.margin := by
    simpa only [separation, Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation] using
      Power.Unit.Radius.unitRobustRadius_taylor parameterUnit degree degreeAtLeastTwo
  rw [Power.Unit.Box.unitRobustBox_eq_centeredNewtonSquare parameterNonzero parameterUnit
    degree degreeAtLeastTwo index]
  exact Winding.Box.Newton.Square.Separated.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
    degreeTwo newton source.refinesAmbient
    (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo)
    targetRefines displacement taylor
end Purelib.RootIsolation.Power.Unit.Box.Winding

end
