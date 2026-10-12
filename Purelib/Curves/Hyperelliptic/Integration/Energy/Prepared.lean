module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
public import Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Integration.Energy.Cell
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Topology.PreparedCycleModels
public import Purelib.Topology.BranchedCover.Double.Attachment
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Matrix
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Tactic.Ring

/-!
# Geometry-backed finite surface energy

The second bilinear relation consumes lower sums on finitely many rational
surface boxes.  This module prevents those lower sums from being supplied as
unattached pairs of rational numbers: every raw cell names one face of the
explicit hyperelliptic cell complex, carries one proper rational box, uses its
exact rational content as area, proves the curve denominator apart throughout
that box, and verifies a lower bound for the displayed algebraic differential
density.

The remaining global comparison is precisely the finite cut-surface
second-relation calculation: the sum of these checked local contributions is
bounded by the synchronized A/B period pairing.  Once that comparison and the
already finite normalization comparison are displayed, the generic transport
layer derives pointwise positivity.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Rational
open Purelib.Approximation.Rational
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Integration.Energy
open Purelib.Curves.Hyperelliptic.Periods.Matrix
open Purelib.Curves.Hyperelliptic.Periods.Normalization
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational.Box
open Purelib.Geometry.Rational.Box.Square.Centered
open Purelib.Integration.Energy
open Purelib.Integration.Energy.Cell
open _root_.Purelib.Integration.Energy renaming Cell -> Cell
open Purelib.LinearAlgebra.Gaussian
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Inverse
open Purelib.LinearAlgebra.Matrix.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Periods
open Purelib.Riemann.Topology
open Purelib.Topology.BranchedCover.Double

open Purelib.Riemann.Periods.PeriodMatrix (geometricMatrixOfNamed sample_geometricMatrixOfNamed
  oneByOneEntryApproximation OneByOneEntryCandidateLowerCertificate)

open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Riemann.Periods.PeriodMatrix (PeriodData sampledMatrix ScalarCandidateLowerCertificate
  ScalarTailSeparationCertificate canonicalScaledInverse)

set_option genInjectivity false in
/-- One checked rational surface box for the algebraic differential `p(x) dx/y`.

The two division-free density inequalities cover the two possible sizes of the sheet norm: below one,
`density_below_numerator` controls the quotient, while above one `density_valid` does. Together they give a
square-root-free lower bound for `‖p(x)/y‖²` whenever `y² = f(x)`. The positive denominator bound also keeps the whole
box clear of branch points. -/
structure PreparedEnergy.SurfaceCell {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus) where
  /-- The original finite lifted face containing this surface contribution. -/ face : Attachment.Face
  /-- The retained rational box on the original curve. -/ box : Rational.Box
  /-- Both side lengths of the retained box are strictly positive. -/ proper : box.Proper
  /-- The retained rational lower bound for the differential squared-norm density. -/ densityLower : Fraction.Rational
  /-- The retained density lower bound is nonnegative. -/ densityLower_nonnegative : 0 <= densityLower
  /-- The retained uniform squared-norm lower bound for the original curve polynomial on this box. -/ denominatorLower :
    Fraction.Rational
  /-- The retained polynomial denominator lower bound is strictly positive. -/ denominatorLower_positive : 0 <
    denominatorLower
  /-- Every point of the original box satisfies the retained polynomial squared-norm lower bound. -/ denominator_apart :
    forall point : Data.Gaussian.Basic.Canonical, box.Contains point ->
    denominatorLower <=
      Data.Gaussian.Norm.Basic.normSq (curve.polynomial.eval point)
  /-- The density lower bound is below the original numerator squared norm throughout the box. -/
    density_below_numerator : forall point : Data.Gaussian.Basic.Canonical, box.Contains point ->
    densityLower <=
      Data.Gaussian.Norm.Basic.normSq
        ((EvaluationLower.coefficientPolynomial coefficients).eval point)
  /-- Multiplying the density lower bound by the original radicand squared norm stays below the numerator squared norm
    throughout the box. -/ density_valid : forall point : Data.Gaussian.Basic.Canonical, box.Contains point ->
    densityLower *
        Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval point) <=
      Data.Gaussian.Norm.Basic.normSq
        ((EvaluationLower.coefficientPolynomial coefficients).eval point)

constructive_injectivity PreparedEnergy.SurfaceCell

set_option genInjectivity false in
/-- One surface cell together with the strict density fact needed to make its exact positive box area contribute
strictly positive energy. -/
structure PositiveSurfaceCell {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus) where
  /-- The original geometry-backed surface cell. -/ cell :
    Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients
  /-- The original surface-cell density lower bound is strictly positive. -/ density_positive : 0 < cell.densityLower

constructive_injectivity PositiveSurfaceCell

namespace PreparedEnergy.SurfaceCell

/-- Build a fully checked surface cell from a face, a proper rational box, and two decidable rational positivity checks.

All denominator-apartness and density-validity fields follow from the finite polynomial bounds above. -/
@[expose] def ofBox {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus) (face : Attachment.Face) (box : Rational.Box)
    (proper : box.Proper)
    (numeratorPositive :
      0 < EvaluationLower.uniformNormLower (EvaluationLower.coefficientPolynomial coefficients) box)
    (denominatorPositive :
      0 < EvaluationLower.uniformNormLower curve.polynomial box) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients where
  face := face
  box := box
  proper := proper
  densityLower :=
    EvaluationLower.uniformNormLower (EvaluationLower.coefficientPolynomial coefficients) box /
      (1 + Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial box)
  densityLower_nonnegative :=
    Fraction.Order.Field.div_nonneg_direct numeratorPositive.le
      ((by decide : (0 : Fraction.Rational) < 1).trans
        ((by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial box) 1
          rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted
          exact shifted))).le
  denominatorLower := EvaluationLower.uniformNormLower curve.polynomial box
  denominatorLower_positive := denominatorPositive
  denominator_apart := fun point inside =>
    EvaluationLower.uniformNormLower_le curve.polynomial inside
  density_below_numerator := by
    intro point inside
    let numeratorLower :=
      EvaluationLower.uniformNormLower (EvaluationLower.coefficientPolynomial coefficients) box
    let denominatorScale :=
      1 + Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial box
    have denominatorScalePositive : 0 < denominatorScale :=
      (by decide : (0 : Fraction.Rational) < 1).trans
        ((by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial box) 1
          rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted
          exact shifted))
    have numeratorNonnegative : 0 <= numeratorLower := numeratorPositive.le
    have one_le_scale : (1 : Fraction.Rational) <= denominatorScale :=
      (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
          curve.polynomial box).le))
    calc
      numeratorLower / denominatorScale <= numeratorLower :=
        (Fraction.Order.Field.div_le_iff_pos
          denominatorScalePositive).2 (by
            calc
              numeratorLower = numeratorLower * 1 := by ring1
              _ <= numeratorLower * denominatorScale :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                  one_le_scale numeratorNonnegative)
      _ <= Data.Gaussian.Norm.Basic.normSq
          ((EvaluationLower.coefficientPolynomial coefficients).eval point) :=
        EvaluationLower.uniformNormLower_le (EvaluationLower.coefficientPolynomial coefficients) inside
  density_valid := by
    intro point inside
    let numeratorLower :=
      EvaluationLower.uniformNormLower (EvaluationLower.coefficientPolynomial coefficients) box
    let denominatorScale :=
      1 + Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial box
    have denominatorScalePositive : 0 < denominatorScale :=
      (by decide : (0 : Fraction.Rational) < 1).trans
        ((by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial box) 1
          rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted
          exact shifted))
    have quotientNonnegative : 0 <= numeratorLower / denominatorScale :=
      Fraction.Order.Field.div_nonneg_direct numeratorPositive.le
        denominatorScalePositive.le
    calc
      numeratorLower / denominatorScale *
          Data.Gaussian.Norm.Basic.normSq
            (curve.polynomial.eval point) <=
        numeratorLower / denominatorScale * denominatorScale :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (calc
          Data.Gaussian.Norm.Basic.normSq
              (curve.polynomial.eval point) <=
              Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
                curve.polynomial box :=
            Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant
              curve.polynomial inside
          _ <= denominatorScale := (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using
            (Fraction.Order.Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) <= 1)
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial box))))
        quotientNonnegative
      _ = numeratorLower :=
        Algebra.Field.ExplicitField.div_mul_cancel numeratorLower
          (ne_of_gt denominatorScalePositive)
      _ <= Data.Gaussian.Norm.Basic.normSq
          ((EvaluationLower.coefficientPolynomial coefficients).eval point) :=
        EvaluationLower.uniformNormLower_le (EvaluationLower.coefficientPolynomial coefficients) inside

/-- The same two rational checks automatically make the constructed density lower bound strictly positive. -/
theorem ofBox_density_positive {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus) (face : Attachment.Face) (box : Rational.Box)
    (proper : box.Proper)
    (numeratorPositive :
      0 < EvaluationLower.uniformNormLower (EvaluationLower.coefficientPolynomial coefficients) box)
    (denominatorPositive :
      0 < EvaluationLower.uniformNormLower curve.polynomial box) :
    0 < (ofBox curve coefficients face box
      proper numeratorPositive
      denominatorPositive).densityLower :=
  Fraction.Order.Field.div_pos_direct numeratorPositive
    ((by decide : (0 : Fraction.Rational) < 1).trans
      ((by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial box) 1
        rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted
        exact shifted)))

/-- Construct one strictly positive surface box for every displayed nonzero differential combination.

A bounded coefficient-count scan chooses a common clear rational point, and an explicit minimum of two rational safe
radii shrinks a proper square around it. -/
@[expose] def findPositive {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients)
    (face : Attachment.Face) : Curves.Hyperelliptic.Integration.Energy.Prepared.PositiveSurfaceCell curve coefficients
      := by
  let numerator := EvaluationLower.coefficientPolynomial coefficients
  let clear := EvaluationLower.findClearEvaluation curve coefficients nonzero
  let ambient := BoxTransport.centeredBox clear.point 1 (by decide)
  let numeratorValue :=
    Data.Gaussian.Norm.Basic.normSq (numerator.eval clear.point)
  let denominatorValue :=
    Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval clear.point)
  let numeratorLipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound numerator ambient
  let denominatorLipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound curve.polynomial ambient
  let numeratorRadius := Purelib.Polynomial.Geometry.EvaluationLower.sampledSafeRadius numeratorValue numeratorLipschitz
  let denominatorRadius :=
    Purelib.Polynomial.Geometry.EvaluationLower.sampledSafeRadius denominatorValue denominatorLipschitz
  let radius := min 1 (min numeratorRadius denominatorRadius)
  have numeratorValuePositive : 0 < numeratorValue :=
    Data.Gaussian.Norm.Basic.normSq_pos clear.numerator_nonzero
  have denominatorValuePositive : 0 < denominatorValue :=
    Data.Gaussian.Norm.Basic.normSq_pos clear.denominator_nonzero
  have numeratorLipschitzPositive : 0 < numeratorLipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos numerator ambient
  have denominatorLipschitzPositive : 0 < denominatorLipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos curve.polynomial ambient
  have numeratorRadiusPositive : 0 < numeratorRadius := by
    unfold numeratorRadius Purelib.Polynomial.Geometry.EvaluationLower.sampledSafeRadius
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct numeratorValuePositive
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          numeratorLipschitzPositive)) (by decide)
  have denominatorRadiusPositive : 0 < denominatorRadius := by
    unfold denominatorRadius Purelib.Polynomial.Geometry.EvaluationLower.sampledSafeRadius
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct denominatorValuePositive
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          denominatorLipschitzPositive)) (by decide)
  have radiusPositive : 0 < radius := by
    unfold radius
    exact Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min numeratorRadiusPositive
      denominatorRadiusPositive)
  have radius_le_one : radius <= 1 := by
    unfold radius
    exact Fraction.Order.Basic.min_le_left _ _
  have radius_le_numerator : radius <= numeratorRadius := by
    unfold radius
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have radius_le_denominator : radius <= denominatorRadius := by
    unfold radius
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  let cellBox := BoxTransport.centeredBox clear.point radius
    radiusPositive.le
  have cellProper : cellBox.Proper := by
    change clear.point.re - radius < clear.point.re + radius /\
      clear.point.im - radius < clear.point.im + radius
    constructor
    · have lower := Fraction.Order.Arithmetic.sub_lt_sub_left_direct radiusPositive clear.point.re
      have zero : clear.point.re - (0 : Fraction.Rational) = clear.point.re := by ring1
      rewrite [zero] at lower
      have upper := Fraction.Order.Arithmetic.add_lt_add_left_direct radiusPositive clear.point.re
      rewrite [Fraction.Field.add_comm clear.point.re (0 : Fraction.Rational), Fraction.zero_add] at upper
      exact lower.trans upper
    · have lower := Fraction.Order.Arithmetic.sub_lt_sub_left_direct radiusPositive clear.point.im
      have zero : clear.point.im - (0 : Fraction.Rational) = clear.point.im := by ring1
      rewrite [zero] at lower
      have upper := Fraction.Order.Arithmetic.add_lt_add_left_direct radiusPositive clear.point.im
      rewrite [Fraction.Field.add_comm clear.point.im (0 : Fraction.Rational), Fraction.zero_add] at upper
      exact lower.trans upper
  have clearInside : cellBox.Contains clear.point := by
    change clear.point.re - radius <= clear.point.re /\
      clear.point.re <= clear.point.re + radius /\
      clear.point.im - radius <= clear.point.im /\
      clear.point.im <= clear.point.im + radius
    constructor
    · have lower := Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusPositive.le clear.point.re
      have zero : clear.point.re - (0 : Fraction.Rational) = clear.point.re := by ring1
      rewrite [zero] at lower
      exact lower
    constructor
    · have upper := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl clear.point.re) radiusPositive.le
      rewrite [Fraction.Field.add_comm clear.point.re (0 : Fraction.Rational), Fraction.zero_add] at upper
      exact upper
    constructor
    · have lower := Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusPositive.le clear.point.im
      have zero : clear.point.im - (0 : Fraction.Rational) = clear.point.im := by ring1
      rewrite [zero] at lower
      exact lower
    · have upper := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl clear.point.im) radiusPositive.le
      rewrite [Fraction.Field.add_comm clear.point.im (0 : Fraction.Rational), Fraction.zero_add] at upper
      exact upper
  have cellRefines : cellBox.Refines ambient := by
    exact
      ⟨Fraction.Order.Arithmetic.sub_le_sub_left_direct radius_le_one
          clear.point.re,
        by
          calc
            clear.point.re + radius = radius + clear.point.re :=
              Fraction.Field.add_comm _ _
            _ <= 1 + clear.point.re :=
              Fraction.Order.Arithmetic.add_le_add_right_direct radius_le_one clear.point.re
            _ = clear.point.re + 1 :=
              Fraction.Field.add_comm _ _,
        Fraction.Order.Arithmetic.sub_le_sub_left_direct radius_le_one
          clear.point.im,
        by
          calc
            clear.point.im + radius = radius + clear.point.im :=
              Fraction.Field.add_comm _ _
            _ <= 1 + clear.point.im :=
              Fraction.Order.Arithmetic.add_le_add_right_direct radius_le_one clear.point.im
            _ = clear.point.im + 1 :=
              Fraction.Field.add_comm _ _⟩
  have numeratorLowerPositive :
      0 < Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox := by
    unfold Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower
    rw [BoxTransport.centeredBox_diagonalSq]
    exact EvaluationLower.sampledNormLower_positive_of_radius numeratorValuePositive
      numeratorLipschitzPositive radiusPositive radius_le_one
      radius_le_numerator
  have denominatorLowerPositive :
      0 < Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower curve.polynomial clear.point ambient cellBox :=
        by
    unfold Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower
    rw [BoxTransport.centeredBox_diagonalSq]
    exact EvaluationLower.sampledNormLower_positive_of_radius denominatorValuePositive
      denominatorLipschitzPositive radiusPositive radius_le_one
      radius_le_denominator
  let denominatorScale :=
    1 + Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial ambient
  have denominatorScalePositive : 0 < denominatorScale :=
    (by decide : (0 : Fraction.Rational) < 1).trans
      ((by
        have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
          (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial ambient) 1
        rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted
        exact shifted))
  let cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients :=
    { face := face
      box := cellBox
      proper := cellProper
      densityLower :=
        Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox /
          denominatorScale
      densityLower_nonnegative :=
        Fraction.Order.Field.div_nonneg_direct
          numeratorLowerPositive.le denominatorScalePositive.le
      denominatorLower :=
        Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower curve.polynomial clear.point ambient cellBox
      denominatorLower_positive := denominatorLowerPositive
      denominator_apart := fun point inside =>
        EvaluationLower.sampledNormLower_le curve.polynomial clear.point clearInside
          cellRefines inside
      density_below_numerator := by
        intro point inside
        have numeratorNonnegative :
            0 <= Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox :=
          numeratorLowerPositive.le
        have one_le_scale : (1 : Fraction.Rational) <= denominatorScale := by
          unfold denominatorScale
          exact (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self,
            -iff_self] using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
              curve.polynomial ambient).le))
        calc
          Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox /
                denominatorScale <=
              Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox :=
            (Fraction.Order.Field.div_le_iff_pos
              denominatorScalePositive).2 (by
                calc
                  Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox =
                      Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox
                        *
                        1 := by ring1
                  _ <= Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient
                    cellBox *
                        denominatorScale :=
                    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      one_le_scale numeratorNonnegative)
          _ <= Data.Gaussian.Norm.Basic.normSq
                (numerator.eval point) :=
            EvaluationLower.sampledNormLower_le numerator clear.point clearInside cellRefines
              inside
      density_valid := by
        intro point inside
        have pointAmbient := cellRefines.contains inside
        have quotientNonnegative :
            0 <= Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox /
              denominatorScale :=
          Fraction.Order.Field.div_nonneg_direct
            numeratorLowerPositive.le denominatorScalePositive.le
        calc
          Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox /
                denominatorScale *
              Data.Gaussian.Norm.Basic.normSq
                (curve.polynomial.eval point) <=
            Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox /
              denominatorScale * denominatorScale :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (calc
                Data.Gaussian.Norm.Basic.normSq
                    (curve.polynomial.eval point) <=
                    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
                      curve.polynomial ambient :=
                  Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant
                    curve.polynomial pointAmbient
                _ <= denominatorScale := by
                  unfold denominatorScale
                  exact (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using
                    (Fraction.Order.Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) <= 1)
                    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial ambient))))
              quotientNonnegative
          _ = Purelib.Polynomial.Geometry.EvaluationLower.sampledNormLower numerator clear.point ambient cellBox :=
            Algebra.Field.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorScalePositive)
          _ <= Data.Gaussian.Norm.Basic.normSq
              (numerator.eval point) :=
            EvaluationLower.sampledNormLower_le numerator clear.point clearInside cellRefines
              inside }
  exact
    { cell := cell
      density_positive :=
        Fraction.Order.Field.div_pos_direct numeratorLowerPositive
          denominatorScalePositive }

/-- Forget the geometric sidecar only at the generic rational-energy layer. The area is computed from the displayed box
rather than supplied separately. -/
@[expose] def toEnergyCell {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) :
    Integration.Energy.Cell where
  areaLower := Content.boxContent cell.box
  densityLower := cell.densityLower
  areaLower_nonnegative := Content.boxContent_nonneg cell.box
  densityLower_nonnegative := cell.densityLower_nonnegative

/-- The displayed denominator is uniformly nonzero on the whole rational box. -/
theorem denominator_normSq_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {point :
      Data.Gaussian.Basic.Canonical}
    (inside : cell.box.Contains point) :
    0 < Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval point) :=
  cell.denominatorLower_positive.trans_le (cell.denominator_apart point inside)

/-- The stronger-denominator branch of the division-free local check is a lower bound for `‖p‖²/‖f‖²`. The actual `p/y`
density is handled below by combining this fact with `density_below_numerator`. -/
theorem densityLower_le_quotient {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {point :
      Data.Gaussian.Basic.Canonical}
    (inside : cell.box.Contains point) :
    cell.densityLower <=
      Data.Gaussian.Norm.Basic.normSq
          ((EvaluationLower.coefficientPolynomial coefficients).eval point) /
        Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval point) :=
  (Fraction.Order.Field.le_div_iff_pos
    (cell.denominator_normSq_positive inside)).2
      (cell.density_valid point inside)

/-- Square-root-free physical-density comparison.

If `sheetNorm` is the squared norm of a sheet value, so that its square is `‖f(x)‖²`, the two local density checks imply
`densityLower * sheetNorm ≤ ‖p(x)‖²`. The proof splits at one and uses only ordered rational arithmetic. -/
theorem densityLower_mul_sheetNorm_le_numerator {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {point :
      Data.Gaussian.Basic.Canonical}
    (inside : cell.box.Contains point) (sheetNorm : Fraction.Rational)
    (sheetNormNonnegative : 0 <= sheetNorm)
    (sheetNorm_sq : sheetNorm ^ 2 =
      Data.Gaussian.Norm.Basic.normSq
        (curve.polynomial.eval point)) :
    cell.densityLower * sheetNorm <=
      Data.Gaussian.Norm.Basic.normSq
        ((EvaluationLower.coefficientPolynomial coefficients).eval point) := by
  by_cases small : sheetNorm <= 1
  · calc
      cell.densityLower * sheetNorm <= cell.densityLower * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small
          cell.densityLower_nonnegative
      _ = cell.densityLower := by ring1
      _ <= Data.Gaussian.Norm.Basic.normSq
          ((EvaluationLower.coefficientPolynomial coefficients).eval point) :=
        cell.density_below_numerator point inside
  · have one_le_sheetNorm : (1 : Fraction.Rational) <= sheetNorm :=
      (lt_of_not_ge small).le
    have sheetNorm_le_sq : sheetNorm <= sheetNorm ^ 2 := by
      calc
        sheetNorm = 1 * sheetNorm := by ring1
        _ <= sheetNorm * sheetNorm :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            one_le_sheetNorm sheetNormNonnegative
        _ = sheetNorm ^ 2 := by ring1
    calc
      cell.densityLower * sheetNorm <=
          cell.densityLower * sheetNorm ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sheetNorm_le_sq cell.densityLower_nonnegative
      _ = cell.densityLower *
          Data.Gaussian.Norm.Basic.normSq
            (curve.polynomial.eval point) := by rw [sheetNorm_sq]
      _ <= Data.Gaussian.Norm.Basic.normSq
          ((EvaluationLower.coefficientPolynomial coefficients).eval point) :=
        cell.density_valid point inside

/-- Every checked cell density is therefore a genuine lower bound for the standard hyperelliptic differential density
`‖p(x)/y‖²` at an exact sheet value `y`. -/
theorem densityLower_le_differentialNormSq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) {point sheet
      : Data.Gaussian.Basic.Canonical}
    (inside : cell.box.Contains point)
    (sheet_square : sheet * sheet = curve.polynomial.eval point) :
    cell.densityLower <=
      Data.Gaussian.Norm.Basic.normSq
        ((EvaluationLower.coefficientPolynomial coefficients).eval point / sheet) := by
  have denominatorNonzero : curve.polynomial.eval point ≠ 0 := by
    intro denominatorZero
    have positive := cell.denominator_normSq_positive inside
    rw [denominatorZero,
      Data.Gaussian.Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl 0 positive)
  have sheetNonzero : sheet ≠ 0 := by
    intro sheetZero
    apply denominatorNonzero
    rw [← sheet_square, sheetZero,
      Data.Gaussian.Basic.zero_mul]
  have sheetNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq sheet :=
    Data.Gaussian.Norm.Basic.normSq_pos sheetNonzero
  have sheetNormSquare :
      Data.Gaussian.Norm.Basic.normSq sheet ^ 2 =
        Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval point) := by
    calc
      Data.Gaussian.Norm.Basic.normSq sheet ^ 2 =
          Data.Gaussian.Norm.Basic.normSq sheet *
            Data.Gaussian.Norm.Basic.normSq sheet := by ring1
      _ = Data.Gaussian.Norm.Basic.normSq (sheet * sheet) :=
        (Data.Gaussian.Norm.Basic.normSq_mul sheet sheet).symm
      _ = Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval point) := by rw [sheet_square]
  rw [Data.Gaussian.Field.normSq_div _ _ sheetNonzero]
  exact (Fraction.Order.Field.le_div_iff_pos sheetNormPositive).2
    (cell.densityLower_mul_sheetNorm_le_numerator inside _
      sheetNormPositive.le sheetNormSquare)

/-- Properness supplies strict positivity of the exact box area. -/
theorem area_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) :
    0 < cell.toEnergyCell.areaLower :=
  Content.boxContent_pos_of_proper cell.proper

end PreparedEnergy.SurfaceCell

/-- Generic energy cells obtained from a finite family of checked surface boxes. -/
@[expose] def energyCells {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cells : Fin cellCount -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients) :
    Fin cellCount -> Integration.Energy.Cell :=
  fun index => (cells index).toEnergyCell

/-- Exact finite lower surface sum of the geometry-backed rational boxes. -/
@[expose] def surfaceEnergy {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cells : Fin cellCount -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients) : Coordinate :=
  Cell.cellEnergy (energyCells cells)

/-- A singleton geometry-backed surface sum is exactly its box content times its checked density lower bound. -/
theorem surfaceEnergy_one {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {coefficients : EvaluationLower.GaussianVector genus}
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients) :
    surfaceEnergy (fun _ : Fin 1 => cell) =
      Content.boxContent cell.box * cell.densityLower := by
  unfold surfaceEnergy Cell.cellEnergy
    energyCells
    Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell.toEnergyCell Cell.contribution
  rw [FiniteSum.Fin.sumFin_succ]
  change _ + 0 = _
  ring1

/-- Exact rational contribution of displayed reversed internal-edge pairs. Every pair is represented by one value and
its additive inverse. -/
@[expose] def pairedBoundarySum {edgePairCount : Nat}
    (edgePairValues : Fin edgePairCount -> Fraction.Rational) : Coordinate :=
  FiniteSum.Fin.sumFin fun index =>
    edgePairValues index + -edgePairValues index

/-- All displayed internal-edge pairs cancel by finite rational arithmetic. -/
theorem pairedBoundarySum_zero {edgePairCount : Nat}
    (edgePairValues : Fin edgePairCount -> Fraction.Rational) :
    pairedBoundarySum edgePairValues = 0 := by
  unfold pairedBoundarySum
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun _ => (0 : Fraction.Rational)) (fun index => by ring1)]
  exact FiniteSum.Fin.sumFin_zero

set_option genInjectivity false in
/-- Exact finite cut-surface decomposition for an arbitrary displayed Gaussian-rational differential combination.

Unlike the normalized transport record below, this interface does not presuppose an inverse of the A-period matrix. -/
structure RawBoundaryReduction {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : EvaluationLower.GaussianVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients) where
  /-- The number of retained opposite internal-edge pairs in this finite decomposition. -/ edgePairCount : Nat
  /-- The retained rational contribution of each original internal-edge pair before its opposite is added. -/
    edgePairValues : Fin edgePairCount -> Fraction.Rational
  /-- The retained rational difference between the complete finite energy and the displayed lower sum. -/ remainder :
    Fraction.Rational
  /-- The retained decomposition remainder is nonnegative. -/ remainder_nonnegative : 0 <= remainder
  /-- The synchronized raw A/B pairing equals the original surface sum, cancelling edge pairs and retained remainder. -/
    raw_eq_decomposition :
    Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) =
      surfaceEnergy cells +
        pairedBoundarySum edgePairValues + remainder

constructive_injectivity RawBoundaryReduction

namespace RawBoundaryReduction

/-- Paired internal edges cancel, leaving the checked local surface sum below the raw A/B boundary pairing at the same
finite sample. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : EvaluationLower.GaussianVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.RawBoundaryReduction data coefficients sampleIndex
      cells) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <= Energy.unnormalizedEnergyForm
      coefficients (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  have raw_eq :
      Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) =
        Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
    calc
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells +
          Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum reduction.edgePairValues +
            reduction.remainder :=
        reduction.raw_eq_decomposition
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
        rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
        ring1
  calc
    Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
      Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder :=
      (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) reduction.remainder_nonnegative))
    _ = Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := raw_eq.symm

end RawBoundaryReduction

set_option genInjectivity false in
/-- Exact finite cut-surface decomposition of the raw second-relation pairing.

The local lower sum is accompanied by explicitly paired internal edges and a nonnegative rational remainder for the
difference between lower cell bounds and the complete finite surface computation. -/
structure BoundaryReduction {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)) where
  /-- The number of retained opposite internal-edge pairs in this finite decomposition. -/ edgePairCount : Nat
  /-- The retained rational contribution of each original internal-edge pair before its opposite is added. -/
    edgePairValues : Fin edgePairCount -> Fraction.Rational
  /-- The retained rational difference between the complete finite energy and the displayed lower sum. -/ remainder :
    Fraction.Rational
  /-- The retained decomposition remainder is nonnegative. -/ remainder_nonnegative : 0 <= remainder
  /-- The synchronized raw A/B pairing equals the original surface sum, cancelling edge pairs and retained remainder. -/
    raw_eq_decomposition :
    Energy.unnormalizedEnergyForm
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) =
      surfaceEnergy cells +
        pairedBoundarySum edgePairValues + remainder

constructive_injectivity BoundaryReduction

namespace BoundaryReduction

/-- The exact decomposition, automatic edge cancellation, and nonnegative remainder derive the surface lower bound
consumed by energy transport. -/
theorem surfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.BoundaryReduction data vector sampleIndex cells) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <= Energy.unnormalizedEnergyForm
      (Energy.scaledNormalizedCoefficients data sampleIndex
        vector)
      (sampledMatrix data.aMatrix sampleIndex)
      (sampledMatrix data.bMatrix sampleIndex) := by
  have raw_eq :
      Energy.unnormalizedEnergyForm
          (Energy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) =
        Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
    calc
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells +
          Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum reduction.edgePairValues +
            reduction.remainder :=
        reduction.raw_eq_decomposition
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
        rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
        ring1
  calc
    Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
      Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder :=
      (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) reduction.remainder_nonnegative))
    _ = Energy.unnormalizedEnergyForm
          (Energy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) := raw_eq.symm

end BoundaryReduction

/-! ## Controlled finite boundary error

At a finite quadrature index the boundary calculation need not be literally
exact.  The operational second relation instead supplies a displayed
nonnegative rational error which can be driven below the positive local
surface contribution. -/

set_option genInjectivity false in
/-- Finite cut-surface decomposition with an explicit rational boundary error. Every quantity in the identity is a
displayed rational at the chosen sample index. -/
structure ControlledBoundaryReduction {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector genus)
    (sampleIndex : Nat)
    (cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)) where
  /-- The number of retained opposite internal-edge pairs in this finite decomposition. -/ edgePairCount : Nat
  /-- The retained rational contribution of each original internal-edge pair before its opposite is added. -/
    edgePairValues : Fin edgePairCount -> Fraction.Rational
  /-- The retained rational error in this finite cut-surface boundary calculation. -/ boundaryError : Fraction.Rational
  /-- The retained finite boundary error is nonnegative. -/ boundaryError_nonnegative : 0 <= boundaryError
  /-- The retained rational difference between the complete finite energy and the displayed lower sum. -/ remainder :
    Fraction.Rational
  /-- The retained decomposition remainder is nonnegative. -/ remainder_nonnegative : 0 <= remainder
  /-- The synchronized raw pairing plus its retained boundary error equals the original surface sum, edge pairs and
    remainder. -/ raw_add_error_eq_decomposition :
    Energy.unnormalizedEnergyForm
          (Energy.scaledNormalizedCoefficients data sampleIndex
            vector)
          (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) + boundaryError =
      surfaceEnergy cells +
        pairedBoundarySum edgePairValues + remainder

constructive_injectivity ControlledBoundaryReduction

namespace ControlledBoundaryReduction

/-- A raw-energy lower bound on the displayed canonical cells constructs the controlled boundary reduction with zero
displayed boundary error.

This is the assembly step from the homogeneous energy comparison to the controlled reduction consumed by the tail
request. -/
@[expose] def ofSurfaceLower {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (lower : Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
      Energy.unnormalizedEnergyForm
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex)) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex cells where
  edgePairCount := 0
  edgePairValues := fun index => Fin.elim0 index
  boundaryError := 0
  boundaryError_nonnegative := le_rfl
  remainder :=
    Energy.unnormalizedEnergyForm
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) - Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells
  remainder_nonnegative :=
    Fraction.Order.Arithmetic.sub_nonneg_direct lower
  raw_add_error_eq_decomposition := by
    rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
    ring1

/-- The surface contribution after paying the displayed finite boundary error. -/
@[expose] def effectiveSurfaceEnergy {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells) :
    Coordinate :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells - reduction.boundaryError

/-- Automatic paired-edge cancellation turns the controlled decomposition into the usable raw-energy lower bound. -/
theorem effectiveSurfaceEnergy_le_raw {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells) :
    reduction.effectiveSurfaceEnergy <=
      Energy.unnormalizedEnergyForm
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex) := by
  have decomposition :
      Energy.unnormalizedEnergyForm
            (Energy.scaledNormalizedCoefficients data sampleIndex
              vector)
            (sampledMatrix data.aMatrix sampleIndex)
            (sampledMatrix data.bMatrix sampleIndex) + reduction.boundaryError =
        Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
    calc
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells +
          Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum reduction.edgePairValues +
            reduction.remainder :=
        reduction.raw_add_error_eq_decomposition
      _ = Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder := by
        rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
        ring1
  have surface_le_raw_add_error :
      Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
        Energy.unnormalizedEnergyForm
              (Energy.scaledNormalizedCoefficients data
                sampleIndex vector)
              (sampledMatrix data.aMatrix sampleIndex)
              (sampledMatrix data.bMatrix sampleIndex) +
            reduction.boundaryError := by
    calc
      Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells <=
        Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells + reduction.remainder :=
        (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
          (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          reduction.remainder_nonnegative))
      _ = _ := decomposition.symm
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    surface_le_raw_add_error (-reduction.boundaryError)
  unfold Prepared.ControlledBoundaryReduction.effectiveSurfaceEnergy
  simpa only [Fraction.Arithmetic.sub_eq_add_neg_direct] using
    (shifted.trans (le_of_eq (by ring1)))

/-- Once the controlled error is smaller than the positive surface sum, the effective raw-energy lower bound is strictly
positive. -/
theorem effectiveSurfaceEnergy_positive {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells)
    (error_lt_surface : reduction.boundaryError < Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
      :
    0 < reduction.effectiveSurfaceEnergy := by
  unfold Prepared.ControlledBoundaryReduction.effectiveSurfaceEnergy
  exact Fraction.Order.Arithmetic.sub_pos_direct error_lt_surface

/-- Package the positive effective lower bound as the singleton cell consumed by the generic normalization transport.

Its area is derived from the geometry-backed surface family and boundary error, not supplied separately. -/
@[expose] def effectiveCell {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells)
    (error_lt_surface : reduction.boundaryError < Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
      :
    Integration.Energy.Cell where
  areaLower := reduction.effectiveSurfaceEnergy
  densityLower := 1
  areaLower_nonnegative :=
    (reduction.effectiveSurfaceEnergy_positive error_lt_surface).le
  densityLower_nonnegative := by decide

/-- Singleton effective-energy family used after paying the controlled boundary error. -/
@[expose] def effectiveCells {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells)
    (error_lt_surface : reduction.boundaryError < Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
      :
    Fin 1 -> Integration.Energy.Cell :=
  fun _ => reduction.effectiveCell error_lt_surface

/-- The singleton effective-cell energy is exactly the original surface sum minus its retained boundary error. -/
@[simp] theorem cellEnergy_effectiveCells {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex
      cells)
    (error_lt_surface : reduction.boundaryError < Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy cells)
      :
    Purelib.Integration.Energy.Cell.cellEnergy
        (reduction.effectiveCells error_lt_surface) =
      reduction.effectiveSurfaceEnergy := by
  unfold Cell.cellEnergy
  rw [FiniteSum.Fin.sumFin_succ]
  change reduction.effectiveSurfaceEnergy * 1 + 0 =
    reduction.effectiveSurfaceEnergy
  rw [Fraction.Field.mul_one_direct, _root_.add_zero]

end ControlledBoundaryReduction

namespace BoundaryReduction

/-- An exact decomposition is the zero-error special case of the controlled finite boundary interface. -/
@[expose] def toControlled {genus cellCount : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {vector : EvaluationLower.RationalVector genus}
    {sampleIndex : Nat}
    {cells : Fin cellCount ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
        (Energy.scaledNormalizedCoefficients data sampleIndex
          vector)}
    (reduction : Curves.Hyperelliptic.Integration.Energy.Prepared.BoundaryReduction data vector sampleIndex cells) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction data vector sampleIndex cells where
  edgePairCount := reduction.edgePairCount
  edgePairValues := reduction.edgePairValues
  boundaryError := 0
  boundaryError_nonnegative := by decide
  remainder := reduction.remainder
  remainder_nonnegative := reduction.remainder_nonnegative
  raw_add_error_eq_decomposition := by
    rw [_root_.add_zero]
    exact reduction.raw_eq_decomposition

end BoundaryReduction

/-- Fixed face used for the automatically constructed positive local box.

Either lifted upper face is an actual face of both degree-shape cell models; the zero lift gives one canonical finite
choice. -/
@[expose] def canonicalSurfaceFace : Attachment.Face where
  hemisphere := .upper
  lift := Attachment.sheetZero

/-- Canonical positive local surface cell for any explicitly nonzero raw differential combination. Its construction
precedes period normalization. -/
@[expose] def canonicalRawPositiveCell {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients) :
    PositiveSurfaceCell curve coefficients :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell.findPositive curve coefficients nonzero
    canonicalSurfaceFace

/-- The fixed singleton lower-sum family associated with a raw coefficient vector. In particular, it does not vary with
the period sample index. -/
@[expose] def rawRequestCells {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients) :
    Fin 1 -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients :=
  fun _ => (canonicalRawPositiveCell curve coefficients nonzero).cell

/-- The canonical raw singleton has a fixed strictly positive rational lower energy before any boundary comparison or
matrix inverse is used. -/
theorem rawRequestSurfaceEnergy_positive {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : EvaluationLower.GaussianVector genus)
    (nonzero : Energy.NonzeroGaussianVector coefficients) :
    0 < surfaceEnergy
      (rawRequestCells curve coefficients nonzero) := by
  unfold surfaceEnergy
  apply Cell.cellEnergy_positive_of_cell _ 0
  · exact (canonicalRawPositiveCell curve coefficients
      nonzero).cell.area_positive
  · exact (canonicalRawPositiveCell curve coefficients
      nonzero).density_positive

set_option genInjectivity false in
/-- One global pre-normalization second-relation certificate.

For every raw coefficient vector and synchronized sample, it may isolate any one checked surface box in the finite
boundary decomposition. Restricting this interface to a singleton prevents duplicated cells from asserting an artificial
lower sum larger than the total raw energy. -/
structure RawCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) where
  /-- For every original coefficient vector, synchronized sample and single checked cell, retain its exact raw
    cut-surface decomposition. -/ boundaryReduction : forall (coefficients : EvaluationLower.GaussianVector genus)
    (sampleIndex : Nat) (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      coefficients),
    RawBoundaryReduction data coefficients sampleIndex (fun _ : Fin 1
      => cell)

constructive_injectivity RawCertificate

/-- Minimal raw second-relation statement.

Every one checked surface box is bounded by the synchronized period-pairing energy for the same coefficient vector and
sample. The cancellable edge-pair list and nonnegative remainder of `RawCertificate` are reconstructed from this
inequality. -/
structure RawSurfaceLowerCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve) where
  /-- Every single checked cell lower sum is bounded by the raw pairing at the same original coefficient vector and
    sample. -/ lower : forall (coefficients : EvaluationLower.GaussianVector genus) (sampleIndex : Nat)
    (cell : Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients),
    surfaceEnergy (fun _ : Fin 1 => cell) <=
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex)

namespace RawSurfaceLowerCertificate

/-- The raw finite surface theorem already forces every synchronized `A`-period sample to have trivial left kernel, in
arbitrary genus and before any inverse certificate is supplied.

A purported nonzero kernel vector has zero boundary energy, while its canonically constructed rational surface box has
strictly positive lower energy. -/
theorem aPeriodSample_leftKernel_trivial {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (sampleIndex : Nat)
    (coefficients : EvaluationLower.GaussianVector genus)
    (kernel : forall cycle,
      Energy.periodCombination coefficients
        (sampledMatrix data.aMatrix sampleIndex) cycle = 0) :
    forall row, coefficients row = 0 := by
  intro row
  by_cases coefficientZero : coefficients row = 0
  · exact coefficientZero
  · let nonzero : Energy.NonzeroGaussianVector
        coefficients :=
      { index := row
        coefficient_nonzero := coefficientZero }
    let positiveCell := Curves.Hyperelliptic.Integration.Energy.Prepared.canonicalRawPositiveCell curve coefficients
      nonzero
    have localPositive :
        0 < Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun _ : Fin 1 => positiveCell.cell) := by
      unfold Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy
      apply Cell.cellEnergy_positive_of_cell _ 0
      · exact positiveCell.cell.area_positive
      · exact positiveCell.density_positive
    have localLower := certificate.lower coefficients sampleIndex
      positiveCell.cell
    have rawZero :=
      Energy.unnormalizedEnergyForm_eq_zero_of_aPeriods_zero
        coefficients (sampledMatrix data.aMatrix sampleIndex)
          (sampledMatrix data.bMatrix sampleIndex) kernel
    rw [rawZero] at localLower
    exact (not_lt_of_ge localLower localPositive).elim

/-- The all-pivots fraction-free inverse calculation therefore returns a nonzero scalar at every synchronized finite
sample.

This is a genuine generic-genus consequence of raw surface energy; the still-separate uniform tail lower bound is needed
only to apartify the persistent inverse name. -/
theorem sampledCompleteScaledInverse_scalar_nonzero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (sampleIndex : Nat)
      :
    (PivotedScaledInverse.completeScaledInverse
      (sampledMatrix data.aMatrix sampleIndex)).scalar ≠ 0 := by
  apply PivotedScaledInverse.completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
  intro coefficients kernel row
  exact certificate.aPeriodSample_leftKernel_trivial sampleIndex coefficients
    kernel row

/-- The same nonvanishing statement for the canonical geometric inverse approximation used by persistent normalization.
-/
theorem canonicalInverseScalar_sample_nonzero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (sampleIndex : Nat)
      :
    (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex ≠ 0 := by
  let sampled := sampledMatrix data.aMatrix sampleIndex
  let computed :=
    PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex =
        computed.scalar := by
    unfold canonicalScaledInverse computed sampled
    have samples :=
      PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) sampleIndex
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply certificate.sampledCompleteScaledInverse_scalar_nonzero sampleIndex
  rw [← scalarSample, scalarZero]

/-- Raw surface energy computes the complete finite prefix of inverse-scalar separation.

Consequently one finite anchor/tail clearance check constructs the uniform persistent inverse certificate in every
genus. -/
@[expose] def toScalarSeparationCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (anchor : Nat)
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          Geometric.Basic.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    PeriodMatrix.ScalarSeparationCertificate data.aMatrix :=
  PeriodMatrix.ScalarSeparationCertificate.ofSampleNonzero anchor
    certificate.canonicalInverseScalar_sample_nonzero tailPositive

/-- Apartification-ready inverse lower bound obtained from raw energy and one tail-clearance check. -/
@[expose] def toScalarCandidateLowerCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (anchor : Nat)
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          Geometric.Basic.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  (certificate.toScalarSeparationCertificate anchor
    tailPositive).toScalarCandidateLowerCertificate

/-- The uniform lower bound plus one displayed anchor/tail check also gives the tail-separation certificate consumed by
the tail-compatible theorem, with the anchor selected internally from the uniform bound. -/
@[expose] def toTailSeparationCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) (anchor : Nat)
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          Geometric.Basic.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    ScalarTailSeparationCertificate data.aMatrix :=
  (certificate.toScalarCandidateLowerCertificate anchor
    tailPositive).toScalarTailSeparationCertificate

/-- Materialize the exact legacy decomposition with no artificial boundary pairs and with the displayed difference as
its nonnegative remainder. -/
@[expose] def toRawCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data) :
      Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data where
  boundaryReduction := by
    intro coefficients sampleIndex cell
    let raw := Energy.unnormalizedEnergyForm coefficients
      (sampledMatrix data.aMatrix sampleIndex)
      (sampledMatrix data.bMatrix sampleIndex)
    let localEnergy := Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (fun _ : Fin 1 => cell)
    exact
      { edgePairCount := 0
        edgePairValues := fun index => Fin.elim0 index
        remainder := raw - localEnergy
        remainder_nonnegative :=
          Fraction.Order.Arithmetic.sub_nonneg_direct
            (certificate.lower coefficients sampleIndex cell)
        raw_eq_decomposition := by
          rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
          unfold raw localEnergy
          ring1 }

end RawSurfaceLowerCertificate

namespace RawCertificate

/-- Forget the redundant decomposition fields while retaining precisely the surface lower theorem they prove. -/
theorem toRawSurfaceLowerCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.RawSurfaceLowerCertificate data where
  lower := by
    intro coefficients sampleIndex cell
    exact (certificate.boundaryReduction coefficients sampleIndex cell).surfaceEnergy_le_raw

/-- The decomposed raw certificate has the same generic finite-sample nondegeneracy consequence as its minimal
surface-lower presentation. -/
theorem aPeriodSample_leftKernel_trivial {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (sampleIndex : Nat) (coefficients : EvaluationLower.GaussianVector genus)
    (kernel : forall cycle,
      Energy.periodCombination coefficients
        (sampledMatrix data.aMatrix sampleIndex) cycle = 0) :
    forall row, coefficients row = 0 :=
  certificate.toRawSurfaceLowerCertificate.aPeriodSample_leftKernel_trivial
    sampleIndex coefficients kernel

/-- Every complete fraction-free scalar sample is nonzero under the legacy raw decomposition as well. -/
theorem sampledCompleteScaledInverse_scalar_nonzero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (sampleIndex : Nat) :
    (PivotedScaledInverse.completeScaledInverse
      (sampledMatrix data.aMatrix sampleIndex)).scalar ≠ 0 :=
  certificate.toRawSurfaceLowerCertificate.sampledCompleteScaledInverse_scalar_nonzero
    sampleIndex

/-- Raw decompositions also compute all finite prefix separation data; one tail-clearance check produces the persistent
inverse lower bound. -/
@[expose] def toScalarCandidateLowerCertificate_of_tail {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (anchor : Nat)
    (tailPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
            ((canonicalScaledInverse data.aMatrix).scalar.sample anchor) / 2 -
          Geometric.Basic.quarterRadius
            (canonicalScaledInverse data.aMatrix).scalar.errorScale anchor) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toRawSurfaceLowerCertificate.toScalarCandidateLowerCertificate
    anchor tailPositive

end RawCertificate

/-- The standard genus-one differential coefficient is explicitly nonzero. -/
@[expose] def genusOneUnitNonzero :
    Energy.NonzeroGaussianVector
      Energy.genusOneUnitCoefficients where
  index := 0
  coefficient_nonzero := by
    rw [Energy.genusOneUnitCoefficients_apply]
    decide

/-- Fixed positive local energy for the sole standard genus-one differential. It depends only on the curve, not on a
period sample index. -/
@[expose] def genusOneRawEnergy
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1) :
    Coordinate :=
  surfaceEnergy
    (rawRequestCells curve
      Energy.genusOneUnitCoefficients
      genusOneUnitNonzero)

/-- The fixed canonical unit-differential surface box has strictly positive raw energy. -/
theorem genusOneRawEnergy_positive
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1) :
    0 < genusOneRawEnergy curve :=
  rawRequestSurfaceEnergy_positive curve
    Energy.genusOneUnitCoefficients
    genusOneUnitNonzero

/-- A one-entry coefficient polynomial is constant. -/
@[simp] theorem coefficientPolynomial_one_eval
    (coefficients : EvaluationLower.GaussianVector 1) (point : Data.Gaussian.Basic.Canonical) :
    (Purelib.Polynomial.Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point = coefficients 0 := by
  unfold EvaluationLower.coefficientPolynomial
  rw [OfFn.Basic.ofFn_succ, List.ofFn_zero]
  change (0 : Data.Gaussian.Basic.Canonical) * point + coefficients 0 = coefficients 0
  rewrite [Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.zero_add]
  rfl

/-- Fixed curve-dependent reference box used for all genus-one coefficient samples. -/
@[expose] def genusOneReferenceCell
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1) :
    PositiveSurfaceCell curve
      Energy.genusOneUnitCoefficients :=
  canonicalRawPositiveCell curve
    Energy.genusOneUnitCoefficients genusOneUnitNonzero

/-- Reuse the canonical unit-differential box for an arbitrary genus-one coefficient.

Its density is the unit density scaled by any displayed lower bound for the coefficient squared norm. -/
@[expose] def genusOneScaledReferenceSurfaceCell
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients := by
  let reference := (genusOneReferenceCell curve).cell
  exact
    { face := reference.face
      box := reference.box
      proper := reference.proper
      densityLower := coefficientLower * reference.densityLower
      densityLower_nonnegative :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          coefficientLowerNonnegative reference.densityLower_nonnegative
      denominatorLower := reference.denominatorLower
      denominatorLower_positive := reference.denominatorLower_positive
      denominator_apart := reference.denominator_apart
      density_below_numerator := by
        intro point inside
        have unitDensity := reference.density_below_numerator point inside
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            unitDensity coefficientLowerNonnegative
        calc
          coefficientLower * reference.densityLower <=
              coefficientLower *
                Data.Gaussian.Norm.Basic.normSq
                  ((EvaluationLower.coefficientPolynomial
                    Energy.genusOneUnitCoefficients).eval
                      point) := scaled
          _ = coefficientLower := by
            rw [coefficientPolynomial_one_eval,
              Energy.genusOneUnitCoefficients_apply,
              Data.Gaussian.Norm.Basic.normSq_one]
            ring1
          _ <= Data.Gaussian.Norm.Basic.normSq (coefficients 0) :=
            coefficient_lower
          _ = Data.Gaussian.Norm.Basic.normSq
                ((EvaluationLower.coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval]
      density_valid := by
        intro point inside
        have unitDensity := reference.density_valid point inside
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            unitDensity coefficientLowerNonnegative
        calc
          (coefficientLower * reference.densityLower) *
                Data.Gaussian.Norm.Basic.normSq
                  (curve.polynomial.eval point) =
              coefficientLower *
                (reference.densityLower *
                  Data.Gaussian.Norm.Basic.normSq
                    (curve.polynomial.eval point)) := by ring1
          _ <= coefficientLower *
                Data.Gaussian.Norm.Basic.normSq
                  ((EvaluationLower.coefficientPolynomial
                    Energy.genusOneUnitCoefficients).eval
                      point) := scaled
          _ = coefficientLower := by
            rw [coefficientPolynomial_one_eval,
              Energy.genusOneUnitCoefficients_apply,
              Data.Gaussian.Norm.Basic.normSq_one]
            ring1
          _ <= Data.Gaussian.Norm.Basic.normSq (coefficients 0) :=
            coefficient_lower
          _ = Data.Gaussian.Norm.Basic.normSq
                ((EvaluationLower.coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval] }

/-- Retain the singleton reference box with density scaled by the supplied coefficient squared-norm lower bound. -/
@[expose] def genusOneScaledReferenceSurfaceCells
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    Fin 1 -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients :=
  fun _ => genusOneScaledReferenceSurfaceCell curve coefficients
    coefficientLower coefficientLowerNonnegative coefficient_lower

/-- Exact homogeneity of the reused singleton surface lower sum. -/
theorem surfaceEnergy_genusOneScaledReferenceSurfaceCells
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    surfaceEnergy
        (genusOneScaledReferenceSurfaceCells curve coefficients
          coefficientLower coefficientLowerNonnegative coefficient_lower) =
      coefficientLower * genusOneRawEnergy curve := by
  unfold genusOneScaledReferenceSurfaceCells
  rw [surfaceEnergy_one]
  unfold genusOneScaledReferenceSurfaceCell
  dsimp only
  unfold genusOneRawEnergy
    rawRequestCells
  rw [surfaceEnergy_one]
  change
    Content.boxContent (genusOneReferenceCell curve).cell.box *
        (coefficientLower *
          (genusOneReferenceCell curve).cell.densityLower) =
      coefficientLower *
        (Content.boxContent
            (genusOneReferenceCell curve).cell.box *
          (genusOneReferenceCell curve).cell.densityLower)
  ring1

/-- A positive coefficient lower bound makes the reused reference-cell density strictly positive. -/
theorem genusOneScaledReferenceSurfaceCell_density_positive
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) {coefficientLower : Fraction.Rational}
    (coefficientLowerPositive : 0 < coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    0 < (genusOneScaledReferenceSurfaceCell curve coefficients
      coefficientLower coefficientLowerPositive.le
        coefficient_lower).densityLower :=
  Fraction.Order.Arithmetic.mul_pos_direct coefficientLowerPositive
    (genusOneReferenceCell curve).density_positive

/-- One plus the polynomial squared-norm majorant on the fixed genus-one reference box. -/
@[expose] def genusOneDenominatorUpper
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1) :
    Coordinate :=
  1 + Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial
    (genusOneReferenceCell curve).cell.box

/-- The fixed reference-box denominator upper bound is strictly positive. -/
theorem genusOneDenominatorUpper_positive
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1) :
    0 < genusOneDenominatorUpper curve :=
  (by decide : (0 : Fraction.Rational) < 1).trans
    ((by
      have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
        (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos curve.polynomial
        (genusOneReferenceCell curve).cell.box) 1;
      rewrite [Fraction.Field.add_comm 1 (0 : Fraction.Rational), Fraction.zero_add] at shifted; exact shifted))

/-- Reuse one fixed denominator-clear box for an arbitrary genus-one coefficient whose squared norm has the displayed
rational lower bound. -/
@[expose] def genusOneUniformSurfaceCell
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients := by
  let reference := (genusOneReferenceCell curve).cell
  let denominatorUpper := genusOneDenominatorUpper curve
  have denominatorUpperPositive : 0 < denominatorUpper :=
    genusOneDenominatorUpper_positive curve
  exact
    { face := reference.face
      box := reference.box
      proper := reference.proper
      densityLower := coefficientLower / denominatorUpper
      densityLower_nonnegative :=
        Fraction.Order.Field.div_nonneg_direct
          coefficientLowerNonnegative denominatorUpperPositive.le
      denominatorLower := reference.denominatorLower
      denominatorLower_positive := reference.denominatorLower_positive
      denominator_apart := reference.denominator_apart
      density_below_numerator := by
        intro point inside
        have coefficientNonnegative : 0 <= coefficientLower :=
          coefficientLowerNonnegative
        have one_le_upper : (1 : Fraction.Rational) <= denominatorUpper := by
          unfold denominatorUpper genusOneDenominatorUpper
          exact (by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self,
            -iff_self] using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
            (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
              curve.polynomial reference.box).le))
        calc
          coefficientLower / denominatorUpper <= coefficientLower :=
            (Fraction.Order.Field.div_le_iff_pos
              denominatorUpperPositive).2 (by
                calc
                  coefficientLower = coefficientLower * 1 := by ring1
                  _ <= coefficientLower * denominatorUpper :=
                    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      one_le_upper coefficientNonnegative)
          _ <= Data.Gaussian.Norm.Basic.normSq (coefficients 0) :=
            coefficient_lower
          _ = Data.Gaussian.Norm.Basic.normSq
                ((EvaluationLower.coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval]
      density_valid := by
        intro point inside
        have quotientNonnegative :
            0 <= coefficientLower / denominatorUpper :=
          Fraction.Order.Field.div_nonneg_direct
            coefficientLowerNonnegative denominatorUpperPositive.le
        calc
          coefficientLower / denominatorUpper *
                Data.Gaussian.Norm.Basic.normSq
                  (curve.polynomial.eval point) <=
              coefficientLower / denominatorUpper * denominatorUpper :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (calc
                Data.Gaussian.Norm.Basic.normSq
                    (curve.polynomial.eval point) <=
                    Dense.Gaussian.Bounds.Box.denseEvalNormMajorant
                      curve.polynomial reference.box :=
                  Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormMajorant
                    curve.polynomial inside
                _ <= denominatorUpper := by
                  unfold denominatorUpper
                    genusOneDenominatorUpper
                  exact (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using
                    (Fraction.Order.Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) <= 1)
                    (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant curve.polynomial reference.box))))
              quotientNonnegative
          _ = coefficientLower :=
            Algebra.Field.ExplicitField.div_mul_cancel coefficientLower
              (ne_of_gt denominatorUpperPositive)
          _ <= Data.Gaussian.Norm.Basic.normSq (coefficients 0) :=
            coefficient_lower
          _ = Data.Gaussian.Norm.Basic.normSq
                ((EvaluationLower.coefficientPolynomial coefficients).eval point) := by
            rw [coefficientPolynomial_one_eval] }

/-- Retain the singleton reference box with density equal to the coefficient lower bound divided by its fixed
denominator upper bound. -/
@[expose] def genusOneUniformSurfaceCells
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    Fin 1 -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients :=
  fun _ => genusOneUniformSurfaceCell curve coefficients
    coefficientLower
    coefficientLowerNonnegative coefficient_lower

/-- A positive coefficient lower bound makes the fixed-box quotient density strictly positive. -/
theorem genusOneUniformSurfaceCell_density_positive
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) {coefficientLower : Fraction.Rational}
    (coefficientLowerPositive : 0 < coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    0 < (genusOneUniformSurfaceCell curve coefficients coefficientLower
      coefficientLowerPositive.le coefficient_lower).densityLower :=
  Fraction.Order.Field.div_pos_direct coefficientLowerPositive
    (genusOneDenominatorUpper_positive curve)

/-- Exact fixed-box lower energy as a function of only the coefficient norm lower. -/
@[expose] def genusOneUniformSurfaceEnergy
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficientLower : Fraction.Rational) : Coordinate :=
  Content.boxContent (genusOneReferenceCell curve).cell.box *
    (coefficientLower / genusOneDenominatorUpper curve)

/-- The fixed-box singleton lower sum is exactly its retained box content times the uniform quotient density. -/
theorem surfaceEnergy_genusOneUniformSurfaceCells
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    (coefficients : EvaluationLower.GaussianVector 1) (coefficientLower : Fraction.Rational)
    (coefficientLowerNonnegative : 0 <= coefficientLower)
    (coefficient_lower : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0)) :
    surfaceEnergy
        (genusOneUniformSurfaceCells curve coefficients
          coefficientLower
          coefficientLowerNonnegative coefficient_lower) =
      genusOneUniformSurfaceEnergy curve coefficientLower := by
  unfold surfaceEnergy Cell.cellEnergy
    energyCells
      genusOneUniformSurfaceCells
      genusOneUniformSurfaceCell
    genusOneUniformSurfaceEnergy
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell.toEnergyCell
    Cell.contribution
  rw [FiniteSum.Fin.sumFin_succ]
  change _ + 0 = _
  ring1

/-- A positive coefficient lower bound gives strictly positive uniform fixed-box energy. -/
theorem genusOneUniformSurfaceEnergy_positive
    (curve : Hyperelliptic.Basic.HyperellipticCurve 1)
    {coefficientLower : Fraction.Rational} (positive : 0 < coefficientLower) :
    0 < genusOneUniformSurfaceEnergy curve coefficientLower :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Content.boxContent_pos_of_proper
      (genusOneReferenceCell curve).cell.proper)
    (Fraction.Order.Field.div_pos_direct positive
      (genusOneDenominatorUpper_positive curve))

/-- Uniform squared-norm bound already carried by the sole B-period sampler. -/
@[expose] def genusOneBPeriodBound
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  (oneByOneEntryApproximation data.bMatrix).centerBound

/-- The retained uniform squared-norm bound for B-period samples is nonnegative. -/
theorem genusOneBPeriodBound_nonnegative
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) :
    0 <= genusOneBPeriodBound data :=
  (oneByOneEntryApproximation data.bMatrix).centerBound_nonneg

/-- Explicit genus-one A-period lower bound obtained by dividing the square of the fixed raw surface energy by one plus
the uniform B-period bound. -/
@[expose] def genusOneAPeriodLowerSq
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  genusOneRawEnergy curve ^ 2 / (1 +
    genusOneBPeriodBound data)

/-- Embedding a rational as a real Gaussian gives squared norm equal to its square. -/
@[simp] theorem normSq_gaussianOfRational (value : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq
        (Energy.gaussianOfRational value) = value ^ 2 := by
  simp only [Energy.gaussianOfRational,
    Data.Gaussian.Norm.Basic.normSq]
  ring1

/-- A nonzero one-entry real vector has a nonzero zeroth coefficient. -/
theorem nonzeroVector_one_coefficient
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    vector 0 ≠ 0 := by
  have indexZero : nonzero.index = 0 := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ nonzero.index.isLt)
  have coefficientNonzero := nonzero.coefficient_nonzero
  rw [indexZero] at coefficientNonzero
  exact coefficientNonzero

/-- In dimension one the adjugate-scaled coefficient has squared norm `v² ‖A‖⁶`. The proof uses only the scaled identity
and the already finite one-by-one scalar calculation. -/
theorem normSq_scaledNormalizedCoefficients_one
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq
        (Energy.scaledNormalizedCoefficients data index
          vector 0) =
      vector 0 ^ 2 *
        Data.Gaussian.Norm.Basic.normSq
          (sampledMatrix data.aMatrix index 0 0) ^ 3 := by
  let sampled := sampledMatrix data.aMatrix index
  let inverse := PivotedScaledInverse.completeScaledInverse sampled
  let coefficients :=
    Energy.scaledNormalizedCoefficients data index vector
  have entryIdentity :
      coefficients 0 * sampled 0 0 =
        Energy.gaussianOfRational (vector 0) *
          inverse.scalar := by
    have identity := Energy.periodCombination_scaled_a
      vector sampled inverse
    have entry := congrArg (fun result => result 0) identity
    change Energy.periodCombination coefficients sampled 0 =
      Energy.gaussianOfRational (vector 0) *
        inverse.scalar at entry
    rw [Energy.periodCombination,
      Multiplication.vectorMatrix_apply,
      FiniteSum.Fin.sumFin_succ] at entry
    change coefficients 0 * sampled 0 0 + 0 = _ at entry
    rw [Data.Gaussian.Basic.add_zero] at entry
    exact entry
  have normIdentity := congrArg
    Data.Gaussian.Norm.Basic.normSq entryIdentity
  rw [Data.Gaussian.Norm.Basic.normSq_mul,
    Data.Gaussian.Norm.Basic.normSq_mul,
    normSq_gaussianOfRational,
    PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
      at normIdentity
  let aNorm := Data.Gaussian.Norm.Basic.normSq (sampled 0 0)
  change Data.Gaussian.Norm.Basic.normSq (coefficients 0) =
    vector 0 ^ 2 * aNorm ^ 3
  apply Fraction.Field.mul_right_cancel_of_ne
    (show aNorm ≠ 0 by
      intro normZero
      exact aNonzero
        (Data.Gaussian.Norm.Basic.normSq_eq_zero.mp normZero))
  calc
    Data.Gaussian.Norm.Basic.normSq (coefficients 0) * aNorm =
        vector 0 ^ 2 * aNorm ^ 4 := normIdentity
    _ = (vector 0 ^ 2 * aNorm ^ 3) * aNorm := by ring1

/-- Uniform lower bound for every adjugate-scaled genus-one coefficient at a synchronized sample. -/
@[expose] def genusOneScaledCoefficientLower
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector 1) : Coordinate :=
  vector 0 ^ 2 * genusOneAPeriodLowerSq data ^ 3

/-- The retained uniform squared-norm bound of the original genus-one A-period sampler. -/
@[expose] def genusOneAPeriodBound
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  (oneByOneEntryApproximation data.aMatrix).centerBound

/-- The retained uniform squared-norm bound for A-period samples is nonnegative. -/
theorem genusOneAPeriodBound_nonnegative
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : 0 <= genusOneAPeriodBound data :=
  (oneByOneEntryApproximation data.aMatrix).centerBound_nonneg

/-- A strictly positive bound larger than every squared norm of the one-by-one complete inverse scalar. -/
@[expose] def genusOneScalarNormUpper
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : Coordinate :=
  1 + genusOneAPeriodBound data ^ 4

/-- The fourth-power A-period majorant plus one is strictly positive. -/
theorem genusOneScalarNormUpper_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) : 0 < genusOneScalarNormUpper data := by
  unfold genusOneScalarNormUpper
  exact (by decide : (0 : Fraction.Rational) < 1).trans_le
    ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
      (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (genusOneAPeriodBound_nonnegative data) 4))))

/-- Every synchronized genus-one complete-inverse scalar satisfies the fixed squared-norm upper bound. -/
theorem synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (Certificate.synchronizedScaledInverse data index).scalar <=
      genusOneScalarNormUpper data := by
  rw [Certificate.synchronizedScaledInverse,
    PivotedScaledInverse.normSq_completeScaledInverse_one_scalar]
  have entryBound :
      Data.Gaussian.Norm.Basic.normSq
          (sampledMatrix data.aMatrix index 0 0) <=
        genusOneAPeriodBound data :=
    (oneByOneEntryApproximation data.aMatrix).sample_bounded index
  unfold genusOneScalarNormUpper
  exact (Fraction.Order.Arithmetic.pow_le_pow_direct
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) entryBound 4).trans
    ((by simpa only [Fraction.zero_add, -eq_self, -iff_self] using (Fraction.Order.Arithmetic.add_le_add_right_direct
      (by decide : (0 : Fraction.Rational) <= 1) ((genusOneAPeriodBound
      data ^ 4)))))

/-- Index-independent normalized energy lower obtained from the fixed surface box and the uniform inverse-scalar upper
bound. -/
@[expose] def genusOneUniformNormalizedEnergyLower
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector 1) : Coordinate :=
  genusOneUniformSurfaceEnergy curve
      (genusOneScaledCoefficientLower data vector) /
    genusOneScalarNormUpper data

/-- Sample-independent normalized lower based only on the canonical unit box and exact genus-one coefficient
homogeneity. -/
@[expose] def genusOneScaledReferenceNormalizedEnergyLower
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector 1) : Coordinate :=
  (genusOneScaledCoefficientLower data vector *
    genusOneRawEnergy curve) /
    genusOneScalarNormUpper data

/-- Exact normalized lower contributed by the scaled canonical box at one synchronized sample. -/
@[expose] def genusOneScaledReferenceNormalizedEnergyAt
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : EvaluationLower.RationalVector 1) :
    Coordinate :=
  (genusOneScaledCoefficientLower data vector *
    genusOneRawEnergy curve) /
    Data.Gaussian.Norm.Basic.normSq
      (Certificate.synchronizedScaledInverse data index).scalar

/-- Minimal genus-one global surface theorem.

It compares the one canonical positive box for the standard differential `dx/y` with the synchronized raw period
pairing. Exact one-dimensional homogeneity derives every other coefficient case; no arbitrary-box quantifier is
included. -/
structure GenusOneUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) where
  /-- At every synchronized sample, the canonical unit-differential box energy is below the original genus-one period
    pairing. -/ lower : forall sampleIndex : Nat,
    genusOneRawEnergy curve <=
      Energy.unnormalizedEnergyForm
        Energy.genusOneUnitCoefficients
        (sampledMatrix data.aMatrix sampleIndex)
        (sampledMatrix data.bMatrix sampleIndex)

namespace GenusOneUnitSurfaceLowerCertificate

/-- The unit surface inequality forces a uniform lower bound for the sole genus-one A-period. The proof uses only the
finite Lagrange identity and the already carried uniform B-period bound. -/
@[expose] def toOneByOneEntryCandidateLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data) :
    OneByOneEntryCandidateLowerCertificate data.aMatrix where
  lowerSq := Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq data
  positive := by
    unfold Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct
        (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy_positive curve) 2)
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
          using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneBPeriodBound_nonnegative data)))))
  sample_lower := by
    intro index
    let coefficients := Energy.genusOneUnitCoefficients
    let energy := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve
    let a := sampledMatrix data.aMatrix index 0 0
    let b := sampledMatrix data.bMatrix index 0 0
    let bBound := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneBPeriodBound data
    let denominator := 1 + bBound
    have energyPositive : 0 < energy := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy_positive
      curve
    have energyLeRaw :
        energy <= Energy.unnormalizedEnergyForm coefficients
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) :=
      certificate.lower index
    have energySqLeRawSq :
        energy ^ 2 <=
          Energy.unnormalizedEnergyForm coefficients
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) ^ 2 :=
      Fraction.Order.Arithmetic.pow_le_pow_direct energyPositive.le
        energyLeRaw 2
    have rawSqLeProduct :
        Energy.unnormalizedEnergyForm coefficients
              (sampledMatrix data.aMatrix index)
              (sampledMatrix data.bMatrix index) ^ 2 <=
          Data.Gaussian.Norm.Basic.normSq a *
            Data.Gaussian.Norm.Basic.normSq b := by
      exact Energy.unnormalizedEnergyForm_genusOne_unit_sq_le
        (sampledMatrix data.aMatrix index) (sampledMatrix data.bMatrix index)
    have bLeBound :
        Data.Gaussian.Norm.Basic.normSq b <= bBound :=
      (oneByOneEntryApproximation data.bMatrix).sample_bounded index
    have bLeDenominator :
        Data.Gaussian.Norm.Basic.normSq b <= denominator :=
      bLeBound.trans ((by simpa only [Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) <= 1) (bBound))))
    have productLe :
        Data.Gaussian.Norm.Basic.normSq a *
              Data.Gaussian.Norm.Basic.normSq b <=
          Data.Gaussian.Norm.Basic.normSq a * denominator :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        bLeDenominator
        (Data.Gaussian.Norm.Basic.normSq_nonneg a)
    have energySqLe :
        energy ^ 2 <=
          Data.Gaussian.Norm.Basic.normSq a * denominator :=
      energySqLeRawSq.trans (rawSqLeProduct.trans productLe)
    have denominatorPositive : 0 < denominator :=
      (by decide : (0 : Fraction.Rational) < 1).trans_le
        ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
          using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneBPeriodBound_nonnegative data))))
    change Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq data <=
      Data.Gaussian.Norm.Basic.normSq
        ((oneByOneEntryApproximation data.aMatrix).sample index)
    unfold Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq
    apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    exact energySqLe

/-- Fraction-free inverse separation derived from the single unit surface comparison. -/
@[expose] def toScalarCandidateLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toOneByOneEntryCandidateLowerCertificate.toScalarCandidateLowerCertificate

/-- The retained surface lower certificate makes the scaled coefficient lower bound positive for a nonzero rational
vector. -/
theorem genusOneScaledCoefficientLower_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector := by
  have vectorSqPositive : 0 < vector 0 ^ 2 := by
    have gaussianPositive := Data.Gaussian.Norm.Basic.normSq_pos
      (Energy.gaussianOfRational_ne_zero
        (Curves.Hyperelliptic.Integration.Energy.Prepared.nonzeroVector_one_coefficient nonzero))
    simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.normSq_gaussianOfRational] using gaussianPositive
  exact Fraction.Order.Arithmetic.mul_pos_direct vectorSqPositive
    (Fraction.Order.Arithmetic.pow_pos_direct
      certificate.toOneByOneEntryCandidateLowerCertificate.positive 3)

/-- The retained surface lower certificate bounds every synchronized scaled coefficient by the same rational lower
bound. -/
theorem genusOneScaledCoefficientLower_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector <=
      Data.Gaussian.Norm.Basic.normSq
        (Energy.scaledNormalizedCoefficients data index
          vector 0) := by
  let lowerCertificate :=
    certificate.toOneByOneEntryCandidateLowerCertificate
  let aNorm := Data.Gaussian.Norm.Basic.normSq
    (sampledMatrix data.aMatrix index 0 0)
  have aLower : Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq data <= aNorm :=
    lowerCertificate.sample_lower index
  have aNormPositive : 0 < aNorm :=
    lowerCertificate.positive.trans_le aLower
  have aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0 := by
    intro entryZero
    change 0 < Data.Gaussian.Norm.Basic.normSq
      (sampledMatrix data.aMatrix index 0 0) at aNormPositive
    rw [entryZero, Data.Gaussian.Norm.Basic.normSq_zero] at aNormPositive
    exact lt_irrefl 0 aNormPositive
  rw [Curves.Hyperelliptic.Integration.Energy.Prepared.normSq_scaledNormalizedCoefficients_one data index vector
    aNonzero]
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct
      lowerCertificate.positive.le aLower 3)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 0))

/-- Canonical reused-box cells for one adjugate-scaled genus-one coefficient. -/
@[expose] def scaledReferenceRequestCells
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) : Fin 1 ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      (Energy.scaledNormalizedCoefficients data index vector) :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceSurfaceCells curve
    (Energy.scaledNormalizedCoefficients data index vector)
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)

/-- Unit surface energy, Gaussian homogeneity, and the coefficient lower bound give the complete raw-energy comparison
for the reused request box. -/
theorem scaledReferenceRequestSurfaceEnergy_le_raw
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy (certificate.scaledReferenceRequestCells index vector
      nonzero) <=
      Energy.unnormalizedEnergyForm
        (Energy.scaledNormalizedCoefficients data index
          vector)
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) := by
  let coefficients :=
    Energy.scaledNormalizedCoefficients data index vector
  let coefficientLower := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector
  have coefficientLowerLe : coefficientLower <=
      Data.Gaussian.Norm.Basic.normSq (coefficients 0) :=
    certificate.genusOneScaledCoefficientLower_le index vector
  have unitLower := certificate.lower index
  rw [show Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy
      (certificate.scaledReferenceRequestCells index vector nonzero) =
        coefficientLower * Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve by
    exact Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy_genusOneScaledReferenceSurfaceCells curve
      coefficients
      coefficientLower
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      coefficientLowerLe]
  rw [Energy.unnormalizedEnergyForm_one_eq_normSq_mul_unit]
  calc
    coefficientLower * Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve <=
        Data.Gaussian.Norm.Basic.normSq (coefficients 0) *
          Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLowerLe (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy_positive curve).le
    _ <= Data.Gaussian.Norm.Basic.normSq (coefficients 0) *
          Energy.unnormalizedEnergyForm
            Energy.genusOneUnitCoefficients
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unitLower
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)

/-- Materialize the exact zero-edge-pair decomposition consumed by normalized energy transport. -/
@[expose] def scaledReferenceBoundaryReduction
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.BoundaryReduction data vector index
      (certificate.scaledReferenceRequestCells index vector nonzero) := by
  let raw := Energy.unnormalizedEnergyForm
    (Energy.scaledNormalizedCoefficients data index vector)
    (sampledMatrix data.aMatrix index) (sampledMatrix data.bMatrix index)
  let localEnergy := Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy
    (certificate.scaledReferenceRequestCells index vector nonzero)
  exact
    { edgePairCount := 0
      edgePairValues := fun edge => Fin.elim0 edge
      remainder := raw - localEnergy
      remainder_nonnegative :=
        Fraction.Order.Arithmetic.sub_nonneg_direct
          (certificate.scaledReferenceRequestSurfaceEnergy_le_raw index vector
            nonzero)
      raw_eq_decomposition := by
        rw [Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum_zero]
        unfold raw localEnergy
        ring1 }

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

/-- The legacy arbitrary-cell theorem contains, in particular, the one unit surface inequality actually needed for
genus-one inverse separation. -/
theorem toGenusOneUnitSurfaceLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data where
  lower := by
    intro sampleIndex
    exact (certificate.boundaryReduction
      Energy.genusOneUnitCoefficients sampleIndex
      (Curves.Hyperelliptic.Integration.Energy.Prepared.rawRequestCells curve
        Energy.genusOneUnitCoefficients
        Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUnitNonzero 0)).surfaceEnergy_le_raw

/-- A single raw cut-surface certificate forces uniform separation of the sole genus-one A-period through its minimal
unit theorem. -/
@[expose] def toOneByOneEntryCandidateLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    OneByOneEntryCandidateLowerCertificate data.aMatrix :=
  certificate.toGenusOneUnitSurfaceLowerCertificate.toOneByOneEntryCandidateLowerCertificate

/-- The exact one-by-one scalar calculation converts the raw-energy A-period lower bound into the canonical
fraction-free inverse certificate. -/
@[expose] def toScalarCandidateLowerCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    ScalarCandidateLowerCertificate data.aMatrix :=
  certificate.toOneByOneEntryCandidateLowerCertificate.toScalarCandidateLowerCertificate

/-- The retained surface lower certificate makes the scaled coefficient lower bound positive for a nonzero rational
vector. -/
theorem genusOneScaledCoefficientLower_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector := by
  have vectorSqPositive : 0 < vector 0 ^ 2 := by
    have gaussianPositive := Data.Gaussian.Norm.Basic.normSq_pos
      (Energy.gaussianOfRational_ne_zero
        (Curves.Hyperelliptic.Integration.Energy.Prepared.nonzeroVector_one_coefficient nonzero))
    simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.normSq_gaussianOfRational] using gaussianPositive
  exact Fraction.Order.Arithmetic.mul_pos_direct vectorSqPositive
    (Fraction.Order.Arithmetic.pow_pos_direct
      certificate.toOneByOneEntryCandidateLowerCertificate.positive 3)

/-- The retained surface lower certificate bounds every synchronized scaled coefficient by the same rational lower
bound. -/
theorem genusOneScaledCoefficientLower_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector <=
      Data.Gaussian.Norm.Basic.normSq
        (Energy.scaledNormalizedCoefficients data index
          vector 0) := by
  let lowerCertificate :=
    certificate.toOneByOneEntryCandidateLowerCertificate
  let aNorm := Data.Gaussian.Norm.Basic.normSq
    (sampledMatrix data.aMatrix index 0 0)
  have aLower : Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneAPeriodLowerSq data <= aNorm := by
    exact lowerCertificate.sample_lower index
  have aNormPositive : 0 < aNorm :=
    lowerCertificate.positive.trans_le aLower
  have aNonzero : sampledMatrix data.aMatrix index 0 0 ≠ 0 := by
    intro entryZero
    change 0 < Data.Gaussian.Norm.Basic.normSq
      (sampledMatrix data.aMatrix index 0 0) at aNormPositive
    rw [entryZero, Data.Gaussian.Norm.Basic.normSq_zero] at aNormPositive
    exact lt_irrefl 0 aNormPositive
  rw [Curves.Hyperelliptic.Integration.Energy.Prepared.normSq_scaledNormalizedCoefficients_one data index vector
    aNonzero]
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct
      lowerCertificate.positive.le aLower 3)
    (Fraction.Order.Arithmetic.sq_nonneg_direct (vector 0))

/-- A nonzero genus-one rational vector has a strictly positive fixed normalized energy lower bound. -/
theorem genusOneUniformNormalizedEnergyLower_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector :=
  Fraction.Order.Field.div_pos_direct
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceEnergy_positive curve
      (certificate.genusOneScaledCoefficientLower_positive nonzero))
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScalarNormUpper_positive data)

/-- Fixed-box cells for the scaled coefficient at one synchronized sample. -/
@[expose] def genusOneUniformRequestCells
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) : Fin 1 ->
      Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      (Energy.scaledNormalizedCoefficients data index vector) :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceCells curve
    (Energy.scaledNormalizedCoefficients data index vector)
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)

/-- Exact normalized energy of the fixed-box cell at one synchronized sample. -/
@[expose] def genusOneUniformNormalizedEnergyAt
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (index : Nat) (vector : EvaluationLower.RationalVector 1) :
    Coordinate :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceEnergy curve
      (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector) /
    Data.Gaussian.Norm.Basic.normSq
      (Certificate.synchronizedScaledInverse data index).scalar

/-- The explicit fixed-box quotient equals the synchronized normalized energy of the same retained request cells. -/
theorem genusOneUniformNormalizedEnergyAt_eq
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    genusOneUniformNormalizedEnergyAt data index
      vector =
      Certificate.synchronizedNormalizedEnergyLower data index
        (Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells
          (certificate.genusOneUniformRequestCells index vector nonzero)) := by
  unfold genusOneUniformNormalizedEnergyAt
    Certificate.synchronizedNormalizedEnergyLower
  rw [← Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy_genusOneUniformSurfaceCells curve
    (Energy.scaledNormalizedCoefficients data index vector)
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector)
    (certificate.genusOneScaledCoefficientLower_positive nonzero).le
    (certificate.genusOneScaledCoefficientLower_le index vector)]
  rfl

end RawCertificate

/-- For a nonnegative numerator, increasing a positive denominator decreases the quotient. -/
private theorem div_le_div_of_denominator_le
    {numerator denominator upper : Fraction.Rational}
    (numeratorNonnegative : 0 <= numerator)
    (denominatorPositive : 0 < denominator)
    (upperPositive : 0 < upper) (denominatorLe : denominator <= upper) :
    numerator / upper <= numerator / denominator := by
  apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).2
  have quotientNonnegative : 0 <= numerator / upper :=
    Fraction.Order.Field.div_nonneg_direct numeratorNonnegative
      upperPositive.le
  calc
    numerator / upper * denominator <= numerator / upper * upper :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorLe
        quotientNonnegative
    _ = numerator := Algebra.Field.ExplicitField.div_mul_cancel numerator
      (ne_of_gt upperPositive)

namespace GenusOneUnitSurfaceLowerCertificate

/-- A nonzero genus-one rational vector has a positive normalized energy lower bound from the scaled reference box. -/
theorem genusOneScaledReferenceNormalizedEnergyLower_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data vector :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (certificate.genusOneScaledCoefficientLower_positive nonzero)
      (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy_positive curve))
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScalarNormUpper_positive data)

/-- The exact scaled reference-box quotient is the normalized cell energy consumed by transport at the synchronized
sample. -/
theorem genusOneScaledReferenceNormalizedEnergyAt_eq
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyAt data index vector
      =
      Certificate.synchronizedNormalizedEnergyLower data index
        (Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells
          (certificate.scaledReferenceRequestCells index vector nonzero)) := by
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyAt
    Certificate.synchronizedNormalizedEnergyLower
  rw [show Cell.cellEnergy
      (Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells
        (certificate.scaledReferenceRequestCells index vector nonzero)) =
        Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector *
          Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve by
    exact Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy_genusOneScaledReferenceSurfaceCells curve
      (Energy.scaledNormalizedCoefficients data index vector)
      (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector)
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      (certificate.genusOneScaledCoefficientLower_le index vector)]

/-- The sample-independent scaled reference energy survives every synchronized genus-one inverse denominator. -/
theorem genusOneScaledReferenceNormalizedEnergyLower_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data vector <=
      Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyAt data index vector := by
  have numeratorNonnegative :
      0 <= Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector *
        Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy curve :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (certificate.genusOneScaledCoefficientLower_positive nonzero).le
      (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneRawEnergy_positive curve).le
  have scalarPositive : 0 < Data.Gaussian.Norm.Basic.normSq
      (Certificate.synchronizedScaledInverse data index).scalar :=
    Data.Gaussian.Norm.Basic.normSq_pos
      (Certificate.synchronizedScaledInverse_scalar_nonzero data
        certificate.toScalarCandidateLowerCertificate index)
  exact Curves.Hyperelliptic.Integration.Energy.Prepared.div_le_div_of_denominator_le numeratorNonnegative
    scalarPositive
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScalarNormUpper_positive data)
    (Curves.Hyperelliptic.Integration.Energy.Prepared.synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper data
      index)

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

/-- The fixed positive normalized lower survives every synchronized sample. -/
theorem genusOneUniformNormalizedEnergyLower_le
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (index : Nat) (vector : EvaluationLower.RationalVector 1)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector <=
      genusOneUniformNormalizedEnergyAt data index
        vector := by
  have surfacePositive : 0 < Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceEnergy curve
      (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledCoefficientLower data vector) :=
    Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceEnergy_positive curve
      (certificate.genusOneScaledCoefficientLower_positive nonzero)
  have scalarPositive : 0 < Data.Gaussian.Norm.Basic.normSq
      (Certificate.synchronizedScaledInverse data index).scalar :=
    Data.Gaussian.Norm.Basic.normSq_pos
      (Certificate.synchronizedScaledInverse_scalar_nonzero data
        certificate.toScalarCandidateLowerCertificate index)
  exact Curves.Hyperelliptic.Integration.Energy.Prepared.div_le_div_of_denominator_le surfacePositive.le scalarPositive
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScalarNormUpper_positive data)
    (Curves.Hyperelliptic.Integration.Energy.Prepared.synchronizedScaledInverse_normSq_le_genusOneScalarNormUpper data
      index)

end RawCertificate

/-- The synchronized scaled coefficients are nonzero by the finite inverse identity, so the bounded clear-point search
constructs a positive box without additional analytic input. -/
@[expose] def canonicalPositiveCell {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    PositiveSurfaceCell curve
      (Energy.scaledNormalizedCoefficients data sampleIndex
        vector) :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell.findPositive curve
    (Energy.scaledNormalizedCoefficients data sampleIndex
      vector)
    (Energy.scaledNormalizedCoefficients_nonzero data
      inverseLower sampleIndex vector nonzero)
    canonicalSurfaceFace

/-- Singleton finite surface family generated canonically for one request. -/
@[expose] def requestCells {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Fin 1 -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
      (Energy.scaledNormalizedCoefficients data sampleIndex
        vector) :=
  fun _ => (canonicalPositiveCell data inverseLower sampleIndex vector
    nonzero).cell

/-- The generated singleton has strictly positive finite lower energy before any global surface-to-boundary comparison
is used. -/
theorem requestSurfaceEnergy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < surfaceEnergy
      (requestCells data inverseLower sampleIndex vector nonzero) := by
  unfold surfaceEnergy
  apply Cell.cellEnergy_positive_of_cell _ 0
  · exact (canonicalPositiveCell data inverseLower sampleIndex vector
      nonzero).cell.area_positive
  · exact (canonicalPositiveCell data inverseLower sampleIndex vector
      nonzero).density_positive

namespace RawCertificate

/-- Specialize the inverse-independent raw boundary theorem to the adjugate-scaled coefficients used by one normalized
positivity request. -/
@[expose] def normalizedBoundaryReduction {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.BoundaryReduction data vector sampleIndex
      (Curves.Hyperelliptic.Integration.Energy.Prepared.requestCells data inverseLower sampleIndex vector nonzero) := by
  let coefficients :=
    Energy.scaledNormalizedCoefficients data sampleIndex vector
  let coefficientsNonzero :=
    Energy.scaledNormalizedCoefficients_nonzero data
      inverseLower sampleIndex vector nonzero
  let reduction := certificate.boundaryReduction coefficients sampleIndex
    (Curves.Hyperelliptic.Integration.Energy.Prepared.rawRequestCells curve coefficients coefficientsNonzero 0)
  exact
    { edgePairCount := reduction.edgePairCount
      edgePairValues := reduction.edgePairValues
      remainder := reduction.remainder
      remainder_nonnegative := reduction.remainder_nonnegative
      raw_eq_decomposition := by
        change
          Energy.unnormalizedEnergyForm coefficients
                (sampledMatrix data.aMatrix sampleIndex)
                (sampledMatrix data.bMatrix sampleIndex) =
            Curves.Hyperelliptic.Integration.Energy.Prepared.surfaceEnergy
                (Curves.Hyperelliptic.Integration.Energy.Prepared.rawRequestCells curve coefficients
                  coefficientsNonzero) +
              Curves.Hyperelliptic.Integration.Energy.Prepared.pairedBoundarySum reduction.edgePairValues +
                reduction.remainder
        exact reduction.raw_eq_decomposition }

end RawCertificate

/-- Radius-independent coefficient of the automatic quadratic-form perturbation budget. -/
@[expose] def budgetSlope {genus : Nat} (vector : EvaluationLower.RationalVector genus) : Coordinate :=
  FiniteSum.Fin.sumFin fun row =>
    FiniteSum.Fin.sumFin fun column =>
      (vector row * vector column) ^ 2 + 1

/-- The finite sum of squared coefficient products plus one is nonnegative. -/
theorem budgetSlope_nonnegative {genus : Nat}
    (vector : EvaluationLower.RationalVector genus) : 0 <=
      budgetSlope vector := by
  unfold budgetSlope
  calc
    0 = FiniteSum.Fin.sumFin
        (fun _ : Fin genus => (0 : Fraction.Rational)) :=
      FiniteSum.Fin.sumFin_zero.symm
    _ <= FiniteSum.Fin.sumFin (fun row =>
        FiniteSum.Fin.sumFin fun column =>
          (vector row * vector column) ^ 2 + 1) := by
      apply Order.Positivity.sumFin_mono
      intro row
      calc
        0 = FiniteSum.Fin.sumFin
            (fun _ : Fin genus => (0 : Fraction.Rational)) :=
          FiniteSum.Fin.sumFin_zero.symm
        _ <= FiniteSum.Fin.sumFin (fun column =>
            (vector row * vector column) ^ 2 + 1) := by
          apply Order.Positivity.sumFin_mono
          intro column
          exact add_nonneg
            (Fraction.Order.Arithmetic.sq_nonneg_direct
              (vector row * vector column)) (by decide)

/-- For a constant entrywise radius, the entire automatically generated finite double-sum budget is exactly linear in
that radius. -/
theorem automaticBudget_eq_budgetSlope_mul {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodMatrix.NormalizedPeriodData curve)
    (vector : EvaluationLower.RationalVector genus) (radius : Fraction.Rational)
    (positive : 0 < radius) :
    Purelib.LinearAlgebra.Matrix.Rational.Budget.totalBudget
        (Budget.automaticBudget vector
          (Positivity.automaticRadius data radius positive)) =
      budgetSlope vector * radius := by
  unfold Budget.totalBudget budgetSlope
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun row => FiniteSum.Fin.sumFin fun column =>
      ((vector row * vector column) ^ 2 + 1) * radius)
    (fun row => by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [Budget.automaticBudget_apply,
        Positivity.automaticRadius_apply])]
  rw [FiniteSum.Fin.sumFin_congr (fun row =>
    FiniteSum.Fin.sumFin_mul_right
      (fun column => (vector row * vector column) ^ 2 + 1) radius)]
  exact FiniteSum.Fin.sumFin_mul_right _ _

/-- Canonical linear radius whose square lies below a positive public target. -/
@[expose] def targetRadius (target : Fraction.Rational) : Coordinate :=
  min 1 (target / 2)

/-- A positive public target gives a positive clipped half-target radius. -/
theorem targetRadius_positive {target : Fraction.Rational} (positive : 0 < target) :
    0 < targetRadius target := by
  unfold targetRadius
  exact Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct positive (by decide))

/-- The clipped target radius is at most one. -/
theorem targetRadius_le_one (target : Fraction.Rational) : targetRadius
  target <= 1 :=
  Fraction.Order.Basic.min_le_left _ _

/-- The clipped half-target radius has square strictly below the original positive target. -/
theorem targetRadius_sq_lt_target {target : Fraction.Rational}
    (positive : 0 < target) : targetRadius target ^ 2 < target := by
  have radiusPositive := targetRadius_positive positive
  have square_le_radius : targetRadius target ^ 2 <=
    targetRadius target := by
    rw [pow_two]
    calc
      targetRadius target *
        targetRadius target <=
        targetRadius target * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (targetRadius_le_one target) radiusPositive.le
      _ = targetRadius target := by ring1
  exact square_le_radius.trans_lt
    ((Fraction.Order.Basic.min_le_right (1 : Fraction.Rational) (target / 2)).trans_lt
      (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self positive))

/-- Comparison budget for transporting one synchronized exact matrix to the persistent normalized centre. -/
@[expose] def comparisonBudget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (radius : Fraction.Rational)
    (positive : 0 < radius) : Coordinate :=
  Budget.totalBudget
    (Budget.automaticBudget vector
      (Positivity.automaticRadius
        (Certificate.normalizedData data inverseLower)
        radius positive))

/-- Exact normalized lower energy of the automatically generated positive surface singleton. -/
@[expose] def requestNormalizedEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) : Coordinate :=
  Certificate.synchronizedNormalizedEnergyLower data sampleIndex
    (energyCells
      (requestCells data inverseLower sampleIndex vector nonzero))

/-- Positive energy left after paying the exact-sample-to-centre comparison budget. -/
@[expose] def requestClearance {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (comparisonRadius : Fraction.Rational)
    (comparisonPositive : 0 < comparisonRadius) : Coordinate :=
  requestNormalizedEnergy data inverseLower sampleIndex vector nonzero
    -
    comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive

/-- A persistent-table refinement radius small enough for the automatically derived operational comparison with the raw
synchronized matrix. -/
@[expose] def comparisonRefinementRadius (comparisonRadius : Fraction.Rational) : Coordinate :=
  comparisonRadius / 16

/-- A positive comparison radius gives a positive sixteenth-radius refinement. -/
theorem comparisonRefinementRadius_positive {comparisonRadius : Fraction.Rational}
    (positive : 0 < comparisonRadius) :
    0 < comparisonRefinementRadius comparisonRadius := by
  unfold comparisonRefinementRadius
  exact Fraction.Order.Field.div_pos_direct positive (by decide)

/-- The sixteenth-radius refinement square fits strictly within the synchronization comparison allowance. -/
theorem comparisonRefinementRadius_sq_lt_target
    {comparisonRadius : Fraction.Rational} (positive : 0 < comparisonRadius) :
    comparisonRefinementRadius comparisonRadius ^ 2 <
      Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let small := comparisonRefinementRadius comparisonRadius
  let large := comparisonRadius / 8
  have largePositive : 0 < large :=
    Fraction.Order.Field.div_pos_direct positive (by decide)
  have smallPositive : 0 < small :=
    comparisonRefinementRadius_positive positive
  have smallEq : small = large / 2 := by
    unfold small large comparisonRefinementRadius
    rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
      Algebra.Field.ExplicitField.div_eq_mul_inv,
      Algebra.Field.ExplicitField.div_eq_mul_inv]
    rw [show (16 : Fraction.Rational)⁻¹ = (8 : Fraction.Rational)⁻¹ *
        (2 : Fraction.Rational)⁻¹ by decide]
    ring1
  have smallLtLarge : small < large := by
    rw [smallEq]
    exact Purelib.Data.Rat.Fraction.Order.Field.half_lt_self largePositive
  have squares : small ^ 2 < large ^ 2 := by
    simp only [pow_two]
    calc
      small * small < large * small :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          smallLtLarge smallPositive
      _ < large * large :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          largePositive smallLtLarge
  calc
    comparisonRefinementRadius comparisonRadius ^ 2 = small ^ 2 := rfl
    _ < large ^ 2 := squares
    _ = SynchronizedNormalization.comparisonTarget
          comparisonRadius := by
      unfold large SynchronizedNormalization.comparisonTarget
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
        Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        (comparisonRadius * (8 : Fraction.Rational)⁻¹) ^ 2 =
            comparisonRadius ^ 2 * ((8 : Fraction.Rational)⁻¹ ^ 2) := by ring1
        _ = comparisonRadius ^ 2 * (64 : Fraction.Rational)⁻¹ := by
          rw [← Fraction.Field.inv_pow_direct]
          rw [show (8 : Fraction.Rational) ^ 2 = 64 by ring1]

/-- Canonical output radius, simultaneously restricted by the public target and by both the operational-comparison and
positive-energy budgets. -/
@[expose] def requestOutputRadius {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (sampleIndex : Nat) (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (target : Fraction.Rational)
    (comparisonRadius : Fraction.Rational)
    (comparisonPositive : 0 < comparisonRadius) : Coordinate :=
  min (targetRadius target)
    (min (comparisonRefinementRadius comparisonRadius)
      (requestClearance data inverseLower sampleIndex vector nonzero
        comparisonRadius comparisonPositive /
          (1 + budgetSlope vector) / 2))

/-- Positive target and comparison clearance give a positive common output radius. -/
theorem requestOutputRadius_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : EvaluationLower.RationalVector genus}
    {nonzero : EvaluationLower.NonzeroVector vector} {target comparisonRadius : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector
          nonzero) :
    0 < requestOutputRadius data inverseLower sampleIndex
      vector nonzero target
      comparisonRadius comparisonPositive := by
  have clearancePositive :
      0 < requestClearance data inverseLower sampleIndex vector nonzero
        comparisonRadius comparisonPositive :=
    Fraction.Order.Arithmetic.sub_pos_direct comparison_lt_energy
  have slopeDenominatorPositive : 0 < 1 + budgetSlope vector :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (budgetSlope_nonnegative vector))))
  unfold requestOutputRadius
  exact Fraction.Order.Basic.lt_min (targetRadius_positive
    targetPositive)
    (Fraction.Order.Basic.lt_min (comparisonRefinementRadius_positive
      comparisonPositive)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct clearancePositive
          slopeDenominatorPositive) (by decide)))

/-- The computed request output radius has squared refinement target below the original public target. -/
theorem requestOutputRadius_sq_lt_target {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : EvaluationLower.RationalVector genus}
    {nonzero : EvaluationLower.NonzeroVector vector} {target comparisonRadius : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector
          nonzero) :
    Purelib.Data.Rat.Quadratic.Bounds.squaredRefinementTarget
        (requestOutputRadius data inverseLower sampleIndex
          vector nonzero target
          comparisonRadius comparisonPositive) <
      target := by
  let radius := requestOutputRadius data inverseLower sampleIndex
    vector nonzero
    target comparisonRadius comparisonPositive
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_targetRadius : radius <= targetRadius target := by
    unfold radius requestOutputRadius
    exact Fraction.Order.Basic.min_le_left _ _
  unfold Quadratic.Bounds.squaredRefinementTarget
  exact
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radius_le_targetRadius 2).trans_lt
        (targetRadius_sq_lt_target targetPositive)

/-- The automatically chosen table refinement is also fine enough for the operational synchronized-normalization
comparison. -/
theorem requestOutputRadius_sq_lt_comparisonTarget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : EvaluationLower.RationalVector genus}
    {nonzero : EvaluationLower.NonzeroVector vector} {target comparisonRadius : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector
          nonzero) :
    Purelib.Data.Rat.Quadratic.Bounds.squaredRefinementTarget
        (requestOutputRadius data inverseLower sampleIndex
          vector nonzero target
          comparisonRadius comparisonPositive) <
      SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let radius := requestOutputRadius data inverseLower sampleIndex
    vector nonzero
    target comparisonRadius comparisonPositive
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_comparison :
      radius <= comparisonRefinementRadius comparisonRadius := by
    unfold radius requestOutputRadius
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  unfold Quadratic.Bounds.squaredRefinementTarget
  exact
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radius_le_comparison 2).trans_lt
        (comparisonRefinementRadius_sq_lt_target comparisonPositive)

/-- The chosen output radius automatically leaves a strict positive margin after both finite perturbation budgets. -/
theorem requestBudgets_lt_energy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {sampleIndex : Nat} {vector : EvaluationLower.RationalVector genus}
    {nonzero : EvaluationLower.NonzeroVector vector} {target comparisonRadius : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
        requestNormalizedEnergy data inverseLower sampleIndex vector
          nonzero) :
    let radius := requestOutputRadius data inverseLower sampleIndex
      vector
      nonzero target comparisonRadius comparisonPositive
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Certificate.normalizedData data inverseLower)
              radius
              (requestOutputRadius_positive targetPositive
                comparisonPositive
                comparison_lt_energy))) +
        comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive <
      requestNormalizedEnergy data inverseLower sampleIndex vector
        nonzero := by
  let clearance := requestClearance data inverseLower sampleIndex
    vector nonzero
    comparisonRadius comparisonPositive
  let slope := budgetSlope vector
  let energyRadius := clearance / (1 + slope) / 2
  let radius := requestOutputRadius data inverseLower sampleIndex
    vector nonzero
    target comparisonRadius comparisonPositive
  have clearancePositive : 0 < clearance :=
    Fraction.Order.Arithmetic.sub_pos_direct comparison_lt_energy
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have slopeDenominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by
          simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
            using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) slopeNonnegative)))
  have energyRadiusPositive : 0 < energyRadius := by
    unfold energyRadius
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct clearancePositive
        slopeDenominatorPositive) (by decide)
  have radiusPositive : 0 < radius :=
    requestOutputRadius_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_energyRadius : radius <= energyRadius := by
    unfold radius requestOutputRadius energyRadius clearance slope
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  have slope_le_denominator : slope <= 1 + slope := by
    exact (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using
      (Fraction.Order.Arithmetic.add_le_add_right_direct (by decide : (0 : Fraction.Rational) <= 1) (slope)))
  have scaled_le_half : slope * radius <= clearance / 2 := by
    calc
      slope * radius <= (1 + slope) * energyRadius :=
        Fraction.Order.Arithmetic.mul_le_mul_direct slope_le_denominator
          radius_le_energyRadius radiusPositive.le
          slopeDenominatorPositive.le
      _ = clearance / 2 := by
        unfold energyRadius
        calc
          (1 + slope) * (clearance / (1 + slope) / 2) =
              (clearance / (1 + slope) * (1 + slope)) / 2 := by
            simp only [Fraction.Field.div_eq_mul_inv_direct]
            ring1
          _ = clearance / 2 := by
            rw [Algebra.Field.ExplicitField.div_mul_cancel clearance
              (ne_of_gt slopeDenominatorPositive)]
  have output_lt_clearance : slope * radius < clearance :=
    scaled_le_half.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self clearancePositive)
  have outputBudget_lt_clearance :
      Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Certificate.normalizedData data inverseLower)
              radius radiusPositive)) < clearance := by
    rw [automaticBudget_eq_budgetSlope_mul]
    exact output_lt_clearance
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    outputBudget_lt_clearance
    (comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive)
  simpa only [radius,
    show requestOutputRadius_positive targetPositive comparisonPositive
        comparison_lt_energy = radiusPositive from rfl] using
    (shifted.trans_le (le_of_eq (by
      unfold clearance requestClearance
      ring1)))

/-- Output radius for an explicitly supplied positive energy.

This is the same finite budget calculation as `requestOutputRadius`, separated from the canonical positive-cell search
so fixed certified cells can reuse it. -/
@[expose] def outputRadiusFromEnergy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (target comparisonRadius : Fraction.Rational)
    (comparisonPositive : 0 < comparisonRadius) (energy : Fraction.Rational) :
    Coordinate :=
  min (targetRadius target)
    (min (comparisonRefinementRadius comparisonRadius)
      ((energy - comparisonBudget data inverseLower vector
        comparisonRadius
          comparisonPositive) / (1 + budgetSlope vector) / 2))

/-- The output radius is positive when the supplied energy strictly exceeds the comparison budget. -/
theorem outputRadiusFromEnergy_positive {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {target comparisonRadius energy : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    0 < outputRadiusFromEnergy data inverseLower vector target
      comparisonRadius
      comparisonPositive energy := by
  have clearancePositive :
      0 < energy - comparisonBudget data inverseLower vector
        comparisonRadius
        comparisonPositive :=
    Fraction.Order.Arithmetic.sub_pos_direct comparison_lt_energy
  have slopeDenominatorPositive : 0 < 1 + budgetSlope vector :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self] using
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (budgetSlope_nonnegative vector))))
  unfold outputRadiusFromEnergy
  exact Fraction.Order.Basic.lt_min (targetRadius_positive
    targetPositive)
    (Fraction.Order.Basic.lt_min (comparisonRefinementRadius_positive
      comparisonPositive)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct clearancePositive
          slopeDenominatorPositive) (by decide)))

/-- The radius computed from supplied energy meets the original squared public target. -/
theorem outputRadiusFromEnergy_sq_lt_target {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {target comparisonRadius energy : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    Purelib.Data.Rat.Quadratic.Bounds.squaredRefinementTarget
        (outputRadiusFromEnergy data inverseLower vector target
          comparisonRadius
          comparisonPositive energy) < target := by
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_targetRadius : radius <= targetRadius target := by
    unfold radius outputRadiusFromEnergy
    exact Fraction.Order.Basic.min_le_left _ _
  unfold Quadratic.Bounds.squaredRefinementTarget
  exact
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radius_le_targetRadius 2).trans_lt
        (targetRadius_sq_lt_target targetPositive)

/-- The radius computed from supplied energy meets the synchronized comparison allowance. -/
theorem outputRadiusFromEnergy_sq_lt_comparisonTarget {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {target comparisonRadius energy : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    Purelib.Data.Rat.Quadratic.Bounds.squaredRefinementTarget
        (outputRadiusFromEnergy data inverseLower vector target
          comparisonRadius
          comparisonPositive energy) <
      SynchronizedNormalization.comparisonTarget
        comparisonRadius := by
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_comparison :
      radius <= comparisonRefinementRadius comparisonRadius := by
    unfold radius outputRadiusFromEnergy
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  unfold Quadratic.Bounds.squaredRefinementTarget
  exact
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radius_le_comparison 2).trans_lt
        (comparisonRefinementRadius_sq_lt_target comparisonPositive)

/-- Both automatic finite perturbation budgets fit strictly below the supplied energy.

The chosen output radius spends at most half the positive clearance remaining after the original comparison budget. -/
theorem outputRadiusFromEnergy_budgets_lt_energy {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {target comparisonRadius energy : Fraction.Rational}
    (targetPositive : 0 < target)
    (comparisonPositive : 0 < comparisonRadius)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy) :
    let radius := outputRadiusFromEnergy data inverseLower vector
      target
      comparisonRadius comparisonPositive energy
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Certificate.normalizedData data inverseLower)
              radius
              (outputRadiusFromEnergy_positive targetPositive
                comparisonPositive comparison_lt_energy))) +
        comparisonBudget data inverseLower vector comparisonRadius
          comparisonPositive < energy := by
  let clearance := energy - comparisonBudget data inverseLower vector
    comparisonRadius comparisonPositive
  let slope := budgetSlope vector
  let energyRadius := clearance / (1 + slope) / 2
  let radius := outputRadiusFromEnergy data inverseLower vector target
    comparisonRadius comparisonPositive energy
  have clearancePositive : 0 < clearance :=
    Fraction.Order.Arithmetic.sub_pos_direct comparison_lt_energy
  have slopeNonnegative : 0 <= slope := budgetSlope_nonnegative vector
  have slopeDenominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by
          simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
            using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) slopeNonnegative)))
  have energyRadiusPositive : 0 < energyRadius := by
    unfold energyRadius
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct clearancePositive
        slopeDenominatorPositive) (by decide)
  have radiusPositive : 0 < radius :=
    outputRadiusFromEnergy_positive targetPositive comparisonPositive
      comparison_lt_energy
  have radius_le_energyRadius : radius <= energyRadius := by
    unfold radius outputRadiusFromEnergy energyRadius clearance slope
    exact (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)
  have slope_le_denominator : slope <= 1 + slope :=
    (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using (Fraction.Order.Arithmetic.add_le_add_right_direct (by
      decide : (0 : Fraction.Rational) <= 1) (slope)))
  have scaled_le_half : slope * radius <= clearance / 2 := by
    calc
      slope * radius <= (1 + slope) * energyRadius :=
        Fraction.Order.Arithmetic.mul_le_mul_direct slope_le_denominator
          radius_le_energyRadius radiusPositive.le
          slopeDenominatorPositive.le
      _ = clearance / 2 := by
        unfold energyRadius
        calc
          (1 + slope) * (clearance / (1 + slope) / 2) =
              (clearance / (1 + slope) * (1 + slope)) / 2 := by
            simp only [Fraction.Field.div_eq_mul_inv_direct]
            ring1
          _ = clearance / 2 := by
            rw [Algebra.Field.ExplicitField.div_mul_cancel clearance
              (ne_of_gt slopeDenominatorPositive)]
  have outputBudget_lt_clearance :
      Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Certificate.normalizedData data inverseLower)
              radius radiusPositive)) < clearance := by
    rw [automaticBudget_eq_budgetSlope_mul]
    exact scaled_le_half.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self clearancePositive)
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    outputBudget_lt_clearance
    (comparisonBudget data inverseLower vector comparisonRadius
      comparisonPositive)
  simpa only [radius,
    show outputRadiusFromEnergy_positive targetPositive
      comparisonPositive
        comparison_lt_energy = radiusPositive from rfl] using
    (shifted.trans_le (le_of_eq (by
      unfold clearance
      ring1)))

/-- One prepared second-relation request.

Local area, denominator apartness, and density validity live in `SurfaceCell`; the global cut-surface identity is
displayed by `BoundaryReduction`. -/
@[expose] def requestSampleIndex {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Fraction.Rational) (comparisonPositive : 0 < comparisonRadius) :
    Nat :=
  SynchronizedNormalization.synchronizedSampleIndex data
    inverseLower comparisonRadius comparisonPositive

set_option genInjectivity false in
/-- The comparison radius determines, rather than merely accompanies, the one shared raw normalization index. -/
structure ComparisonSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (_inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  /-- The retained positive matrix-entry comparison radius. -/ radius : Fraction.Rational
  /-- The retained comparison radius is strictly positive. -/ positive : 0 < radius
  /-- The retained raw sample index determined by the original comparison radius. -/ sampleIndex : Nat
  /-- The retained sample index is exactly the index computed from this original comparison radius. -/ sampleIndex_eq :
    sampleIndex =
    requestSampleIndex data _inverseLower radius positive

constructive_injectivity ComparisonSchedule

namespace ComparisonSchedule

/-- Construct the comparison schedule with the exact synchronized index determined by the retained positive radius. -/
@[expose] def ofRadius {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (radius : Fraction.Rational) (positive : 0 < radius) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.ComparisonSchedule data inverseLower where
  radius := radius
  positive := positive
  sampleIndex := Curves.Hyperelliptic.Integration.Energy.Prepared.requestSampleIndex data inverseLower radius positive
  sampleIndex_eq := rfl

end ComparisonSchedule

/-- A comparison radius computed solely from the sample-independent genus-one normalized energy lower. -/
@[expose] def genusOneComparisonRadius
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector 1) : Coordinate :=
  genusOneUniformNormalizedEnergyLower data vector /
    (1 + budgetSlope vector) / 2

/-- Comparison radius computed from the sharper unit-surface homogeneity lower, without an arbitrary-coefficient surface
theorem. -/
@[expose] def genusOneScaledReferenceComparisonRadius
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    (data : PeriodData curve) (vector : EvaluationLower.RationalVector 1) : Coordinate :=
  genusOneScaledReferenceNormalizedEnergyLower data vector /
    (1 + budgetSlope vector) / 2

namespace GenusOneUnitSurfaceLowerCertificate

/-- The scaled reference-box energy gives a positive comparison radius for every nonzero genus-one vector. -/
theorem genusOneScaledReferenceComparisonRadius_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius data vector :=
      by
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (certificate.genusOneScaledReferenceNormalizedEnergyLower_positive
        nonzero)
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
          using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope_nonnegative vector))))))
    (by decide)

/-- The automatic comparison budget is strictly below the scaled reference energy before selecting the synchronized
sample. -/
theorem genusOneScaledReferenceComparisonBudget_lt_energy
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget data
      certificate.toScalarCandidateLowerCertificate vector
        (Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius data vector)
        (certificate.genusOneScaledReferenceComparisonRadius_positive nonzero) <
      Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data vector := by
  let energy := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data
    vector
  let slope := Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector
  let radius := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius data vector
  have energyPositive : 0 < energy :=
    certificate.genusOneScaledReferenceNormalizedEnergyLower_positive nonzero
  have slopeNonnegative : 0 <= slope := Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope_nonnegative vector
  have denominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by
          simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
            using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) slopeNonnegative)))
  have radiusPositive : 0 < radius :=
    certificate.genusOneScaledReferenceComparisonRadius_positive nonzero
  have slope_le_denominator : slope <= 1 + slope :=
    (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using (Fraction.Order.Arithmetic.add_le_add_right_direct (by
      decide : (0 : Fraction.Rational) <= 1) (slope)))
  have budget_le_half : slope * radius <= energy / 2 := by
    calc
      slope * radius <= (1 + slope) * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          slope_le_denominator radiusPositive.le
      _ = energy / 2 := by
        unfold radius Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius energy
          slope
        calc
          (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) *
                (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data
                  vector /
                  (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) / 2) =
              (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data vector
                /
                (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) *
                  (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector)) / 2 := by
            simp only [Fraction.Field.div_eq_mul_inv_direct]
            ring1
          _ = Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyLower data vector
            / 2 := by
            rw [Algebra.Field.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorPositive)]
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget
  rw [Curves.Hyperelliptic.Integration.Energy.Prepared.automaticBudget_eq_budgetSlope_mul]
  exact budget_le_half.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self energyPositive)

/-- The unit surface theorem determines the normalization comparison schedule for every nonzero genus-one rational
vector. -/
@[expose] def genusOneScaledReferenceComparisonSchedule
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (vector : EvaluationLower.RationalVector 1) (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.ComparisonSchedule data
      certificate.toScalarCandidateLowerCertificate :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.ComparisonSchedule.ofRadius
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceComparisonRadius data vector)
    (certificate.genusOneScaledReferenceComparisonRadius_positive nonzero)

end GenusOneUnitSurfaceLowerCertificate

namespace RawCertificate

/-- The fixed-box raw certificate gives a positive comparison radius for every nonzero genus-one vector. -/
theorem genusOneComparisonRadius_positive
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    0 < Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius data vector := by
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (certificate.genusOneUniformNormalizedEnergyLower_positive nonzero)
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        ((by simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
          using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope_nonnegative vector))))))
    (by decide)

/-- The automatically chosen comparison budget is strictly smaller than the fixed normalized energy lower, before any
sample index is selected. -/
theorem genusOneComparisonBudget_lt_uniformEnergy
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    {vector : EvaluationLower.RationalVector 1} (nonzero : EvaluationLower.NonzeroVector vector) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget data
      certificate.toScalarCandidateLowerCertificate vector
        (Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius data vector)
        (certificate.genusOneComparisonRadius_positive nonzero) <
      Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector := by
  let energy := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector
  let slope := Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector
  let radius := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius data vector
  have energyPositive : 0 < energy :=
    certificate.genusOneUniformNormalizedEnergyLower_positive nonzero
  have slopeNonnegative : 0 <= slope := Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope_nonnegative vector
  have denominatorPositive : 0 < 1 + slope :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      ((by
          simpa only [Fraction.Field.add_comm _ (0 : Fraction.Rational), Fraction.zero_add, -eq_self, -iff_self]
            using (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) slopeNonnegative)))
  have radiusPositive : 0 < radius :=
    certificate.genusOneComparisonRadius_positive nonzero
  have slope_le_denominator : slope <= 1 + slope :=
    (by simpa only [Fraction.zero_add, -eq_self, -iff_self] using (Fraction.Order.Arithmetic.add_le_add_right_direct (by
      decide : (0 : Fraction.Rational) <= 1) (slope)))
  have budget_le_half : slope * radius <= energy / 2 := by
    calc
      slope * radius <= (1 + slope) * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          slope_le_denominator radiusPositive.le
      _ = energy / 2 := by
        unfold radius Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius energy slope
        calc
          (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) *
                (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector /
                  (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) / 2) =
              (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector /
                (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector) *
                  (1 + Curves.Hyperelliptic.Integration.Energy.Prepared.budgetSlope vector)) / 2 := by
            simp only [Fraction.Field.div_eq_mul_inv_direct]
            ring1
          _ = Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformNormalizedEnergyLower data vector / 2 :=
            by
            rw [Algebra.Field.ExplicitField.div_mul_cancel _
              (ne_of_gt denominatorPositive)]
  unfold Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget
  rw [Curves.Hyperelliptic.Integration.Energy.Prepared.automaticBudget_eq_budgetSlope_mul]
  exact budget_le_half.trans_lt (Purelib.Data.Rat.Fraction.Order.Field.half_lt_self energyPositive)

/-- The radius and synchronized index needed for genus-one normalization are fully determined by the raw certificate and
the requested vector. -/
@[expose] def genusOneComparisonSchedule
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (vector : EvaluationLower.RationalVector 1) (nonzero : EvaluationLower.NonzeroVector vector) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.ComparisonSchedule data
      certificate.toScalarCandidateLowerCertificate :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.ComparisonSchedule.ofRadius
    (Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneComparisonRadius data vector)
    (certificate.genusOneComparisonRadius_positive nonzero)

end RawCertificate

set_option genInjectivity false in
/-- A geometry-backed normalized energy request at one synchronized sample.

The comparison radius determines the retained sample index; the original canonical cells carry an exact boundary
reduction and enough normalized energy to pay the comparison budget. -/
structure RequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained comparison radius and its exact synchronized sample index. -/ comparison :
    ComparisonSchedule data inverseLower
  /-- The exact boundary decomposition for the original canonical request cells at the retained comparison sample. -/
    boundaryReduction : BoundaryReduction data vector
    comparison.sampleIndex
    (requestCells data inverseLower
      comparison.sampleIndex vector nonzero)
  /-- The comparison perturbation budget is strictly below the normalized energy of the same original request cells. -/
    comparisonBudget_lt_energy :
    comparisonBudget data inverseLower vector comparison.radius
        comparison.positive <
      requestNormalizedEnergy data inverseLower
        comparison.sampleIndex vector nonzero

constructive_injectivity RequestCertificate

set_option genInjectivity false in
/-- Once a global raw cut-surface theorem is available, one normalized request only has to exhibit a finite
normalization-comparison radius whose budget clears the automatically generated positive local energy. -/
structure RawRequestSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained comparison radius and its exact synchronized sample index. -/ comparison :
    ComparisonSchedule data inverseLower
  /-- The comparison perturbation budget is strictly below the normalized energy of the same original request cells. -/
    comparisonBudget_lt_energy :
    comparisonBudget data inverseLower vector comparison.radius
        comparison.positive <
      requestNormalizedEnergy data inverseLower
        comparison.sampleIndex vector nonzero

constructive_injectivity RawRequestSchedule

/-- The computed comparison schedule discharges the exact-sample-to-centre closeness proposition required by the generic
energy transport layer. -/
theorem requestCenter_close {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (comparison : ComparisonSchedule data inverseLower)
    (comparison_lt_energy :
      comparisonBudget data inverseLower vector comparison.radius
          comparison.positive <
        requestNormalizedEnergy data inverseLower
          comparison.sampleIndex
          vector nonzero)
    (row column : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (Certificate.normalizedData data inverseLower)
            (Quadratic.Bounds.squaredRefinementTarget
              (requestOutputRadius data inverseLower
                comparison.sampleIndex
                vector nonzero target comparison.radius comparison.positive))
            (Quadratic.Bounds.squaredRefinementTarget_positive
              (requestOutputRadius_positive positive
                comparison.positive
                comparison_lt_energy)) row column -
          Certificate.synchronizedNormalizedMatrix data
            comparison.sampleIndex row column) <
      comparison.radius ^ 2 :=
  SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
    data inverseLower comparison.radius comparison.positive
      comparison.sampleIndex comparison.sampleIndex_eq
      (Quadratic.Bounds.squaredRefinementTarget
        (requestOutputRadius data inverseLower comparison.sampleIndex
          vector
          nonzero target comparison.radius comparison.positive))
      (Quadratic.Bounds.squaredRefinementTarget_positive
        (requestOutputRadius_positive positive comparison.positive
          comparison_lt_energy))
      (requestOutputRadius_sq_lt_comparisonTarget positive
        comparison.positive
        comparison_lt_energy) row column

namespace RequestCertificate

/-- Expand the geometry-backed request into the generic finite transport interface. All local positivity fields are
derived from box properness and the checked density bound. -/
@[expose] def toTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RequestCertificate data inverseLower vector nonzero
      target
      positive) :
    Certificate.TransportRequestCertificate data inverseLower
      vector nonzero target positive where
  sampleIndex := certificate.comparison.sampleIndex
  cellCount := 1
  cells := Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells
    (Curves.Hyperelliptic.Integration.Energy.Prepared.requestCells data inverseLower
    certificate.comparison.sampleIndex vector nonzero)
  positiveCell := 0
  positiveCell_area :=
    (Curves.Hyperelliptic.Integration.Energy.Prepared.canonicalPositiveCell data inverseLower
      certificate.comparison.sampleIndex vector nonzero).cell.area_positive
  positiveCell_density :=
    (Curves.Hyperelliptic.Integration.Energy.Prepared.canonicalPositiveCell data inverseLower
      certificate.comparison.sampleIndex vector nonzero).density_positive
  energy_le_raw := certificate.boundaryReduction.surfaceEnergy_le_raw
  refinementRadius := Curves.Hyperelliptic.Integration.Energy.Prepared.requestOutputRadius data inverseLower
    certificate.comparison.sampleIndex vector nonzero target
      certificate.comparison.radius certificate.comparison.positive
  refinementRadiusPositive :=
    Curves.Hyperelliptic.Integration.Energy.Prepared.requestOutputRadius_positive positive
      certificate.comparison.positive
      certificate.comparisonBudget_lt_energy
  refinementTarget_lt_target :=
    Curves.Hyperelliptic.Integration.Energy.Prepared.requestOutputRadius_sq_lt_target positive
      certificate.comparison.positive
      certificate.comparisonBudget_lt_energy
  comparisonRadius := certificate.comparison.radius
  comparisonRadiusPositive := certificate.comparison.positive
  synchronized_close := Curves.Hyperelliptic.Integration.Energy.Prepared.requestCenter_close (positive := positive)
    certificate.comparison certificate.comparisonBudget_lt_energy
  margin := by
    simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget,
      Curves.Hyperelliptic.Integration.Energy.Prepared.requestNormalizedEnergy] using
      Curves.Hyperelliptic.Integration.Energy.Prepared.requestBudgets_lt_energy positive certificate.comparison.positive
        certificate.comparisonBudget_lt_energy

end RequestCertificate

namespace RawCertificate

/-- In genus one the raw cut-surface theorem itself constructs every finite normalization request: a fixed box supplies
energy, its uniform lower chooses the comparison radius, and the persistent samplers choose the shared index. -/
@[expose] def genusOneTransportRequestCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data)
    (vector : EvaluationLower.RationalVector 1) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Certificate.TransportRequestCertificate data
      certificate.toScalarCandidateLowerCertificate vector nonzero target
        positive := by
  let inverseLower := certificate.toScalarCandidateLowerCertificate
  let comparison := certificate.genusOneComparisonSchedule vector nonzero
  let sampleIndex := comparison.sampleIndex
  let cells := certificate.genusOneUniformRequestCells sampleIndex vector nonzero
  let energy := genusOneUniformNormalizedEnergyAt data
    sampleIndex vector
  have comparison_lt_energy :
      Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget data inverseLower vector comparison.radius
          comparison.positive < energy := by
    exact (certificate.genusOneComparisonBudget_lt_uniformEnergy nonzero).trans_le
      (certificate.genusOneUniformNormalizedEnergyLower_le sampleIndex vector
        nonzero)
  let refinementRadius := Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy data inverseLower
    vector target
    comparison.radius comparison.positive energy
  have refinementPositive : 0 < refinementRadius :=
    Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_positive positive comparison.positive
      comparison_lt_energy
  let reduction := certificate.boundaryReduction
    (Energy.scaledNormalizedCoefficients data sampleIndex
      vector) sampleIndex (cells 0)
  exact
    { sampleIndex := sampleIndex
      cellCount := 1
      cells := Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells cells
      positiveCell := 0
      positiveCell_area := (cells 0).area_positive
      positiveCell_density := by
        exact Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneUniformSurfaceCell_density_positive curve
          (Energy.scaledNormalizedCoefficients data
            sampleIndex vector)
          (certificate.genusOneScaledCoefficientLower_positive nonzero)
          (certificate.genusOneScaledCoefficientLower_le sampleIndex vector)
      energy_le_raw := reduction.surfaceEnergy_le_raw
      refinementRadius := refinementRadius
      refinementRadiusPositive := refinementPositive
      refinementTarget_lt_target :=
        Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_sq_lt_target positive
          comparison.positive
          comparison_lt_energy
      comparisonRadius := comparison.radius
      comparisonRadiusPositive := comparison.positive
      synchronized_close := by
        intro row column
        exact
          SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
            data inverseLower comparison.radius comparison.positive
              sampleIndex comparison.sampleIndex_eq
              (Quadratic.Bounds.squaredRefinementTarget
                refinementRadius)
              (Quadratic.Bounds.squaredRefinementTarget_positive
                refinementPositive)
              (Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_sq_lt_comparisonTarget positive
                comparison.positive comparison_lt_energy) row column
      margin := by
        rw [← certificate.genusOneUniformNormalizedEnergyAt_eq sampleIndex
          vector nonzero]
        simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget,
          show Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_positive positive
            comparison.positive
              comparison_lt_energy = refinementPositive from rfl] using
          Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_budgets_lt_energy positive
            comparison.positive
            comparison_lt_energy }

/-- A raw genus-one cut-surface certificate therefore supplies the complete finite normalized positivity transport, with
no separate radius schedule. -/
@[expose] def genusOneTransportCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve} (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    Certificate.TransportCertificate data
      certificate.toScalarCandidateLowerCertificate where
  certify := fun vector nonzero target positive =>
    certificate.genusOneTransportRequestCertificate vector nonzero target
      positive

end RawCertificate

namespace GenusOneUnitSurfaceLowerCertificate

/-- The single unit-differential surface inequality constructs one complete normalized positivity request.

Genus-one homogeneity supplies the requested coefficient cells and the synchronized comparison schedule. -/
@[expose] def genusOneTransportRequestCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data)
    (vector : EvaluationLower.RationalVector 1) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) :
    Certificate.TransportRequestCertificate data
      certificate.toScalarCandidateLowerCertificate vector nonzero target
        positive := by
  let inverseLower := certificate.toScalarCandidateLowerCertificate
  let comparison :=
    certificate.genusOneScaledReferenceComparisonSchedule vector nonzero
  let sampleIndex := comparison.sampleIndex
  let cells := certificate.scaledReferenceRequestCells sampleIndex vector
    nonzero
  let energy := Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceNormalizedEnergyAt data
    sampleIndex
    vector
  have comparison_lt_energy :
      Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget data inverseLower vector comparison.radius
          comparison.positive < energy := by
    exact
      (certificate.genusOneScaledReferenceComparisonBudget_lt_energy
        nonzero).trans_le
      (certificate.genusOneScaledReferenceNormalizedEnergyLower_le sampleIndex
        vector nonzero)
  let refinementRadius := Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy data inverseLower
    vector target
    comparison.radius comparison.positive energy
  have refinementPositive : 0 < refinementRadius :=
    Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_positive positive comparison.positive
      comparison_lt_energy
  exact
    { sampleIndex := sampleIndex
      cellCount := 1
      cells := Curves.Hyperelliptic.Integration.Energy.Prepared.energyCells cells
      positiveCell := 0
      positiveCell_area := (cells 0).area_positive
      positiveCell_density := by
        exact Curves.Hyperelliptic.Integration.Energy.Prepared.genusOneScaledReferenceSurfaceCell_density_positive curve
          (Energy.scaledNormalizedCoefficients data
            sampleIndex vector)
          (certificate.genusOneScaledCoefficientLower_positive nonzero)
          (certificate.genusOneScaledCoefficientLower_le sampleIndex vector)
      energy_le_raw :=
        (certificate.scaledReferenceBoundaryReduction sampleIndex vector
          nonzero).surfaceEnergy_le_raw
      refinementRadius := refinementRadius
      refinementRadiusPositive := refinementPositive
      refinementTarget_lt_target :=
        Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_sq_lt_target positive
          comparison.positive
          comparison_lt_energy
      comparisonRadius := comparison.radius
      comparisonRadiusPositive := comparison.positive
      synchronized_close := by
        intro row column
        exact
          SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
            data inverseLower comparison.radius comparison.positive
              sampleIndex comparison.sampleIndex_eq
              (Quadratic.Bounds.squaredRefinementTarget
                refinementRadius)
              (Quadratic.Bounds.squaredRefinementTarget_positive
                refinementPositive)
              (Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_sq_lt_comparisonTarget positive
                comparison.positive comparison_lt_energy) row column
      margin := by
        rw [← certificate.genusOneScaledReferenceNormalizedEnergyAt_eq
          sampleIndex vector nonzero]
        simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget,
          show Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_positive positive
            comparison.positive
              comparison_lt_energy = refinementPositive from rfl] using
          Curves.Hyperelliptic.Integration.Energy.Prepared.outputRadiusFromEnergy_budgets_lt_energy positive
            comparison.positive
            comparison_lt_energy }

/-- A genus-one unit surface inequality supplies the entire finite normalized energy transport, so no arbitrary
coefficient or box family remains in the public analytic input. -/
@[expose] def genusOneTransportCertificate
    {curve : Hyperelliptic.Basic.HyperellipticCurve 1}
    {data : PeriodData curve}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.GenusOneUnitSurfaceLowerCertificate data) :
    Certificate.TransportCertificate data
      certificate.toScalarCandidateLowerCertificate where
  certify := fun vector nonzero target positive =>
    certificate.genusOneTransportRequestCertificate vector nonzero target
      positive

end GenusOneUnitSurfaceLowerCertificate

namespace RawRequestSchedule

/-- Pay the retained boundary error and transport the same tail-separated sample into the normalized energy request. -/
@[expose] def toRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (schedule : Curves.Hyperelliptic.Integration.Energy.Prepared.RawRequestSchedule data inverseLower vector nonzero
      target
      positive)
    (raw : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    Curves.Hyperelliptic.Integration.Energy.Prepared.RequestCertificate data inverseLower vector nonzero target positive
      where
  comparison := schedule.comparison
  boundaryReduction := raw.normalizedBoundaryReduction inverseLower
    schedule.comparison.sampleIndex vector nonzero
  comparisonBudget_lt_energy := schedule.comparisonBudget_lt_energy

end RawRequestSchedule

set_option genInjectivity false in
/-- Pointwise prepared surface data for every nonzero rational vector and positive output request. -/
structure Certificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  /-- For every nonzero vector and positive target, return a geometry-backed request with exact boundary reduction and
    paid comparison budget. -/ certify : forall (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    RequestCertificate data inverseLower vector nonzero target positive

constructive_injectivity Certificate

namespace Certificate

/-- Forget geometry only after constructing every field of the established raw-cell transport certificate. -/
@[expose] def toTransportCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.Certificate data inverseLower) :
    Certificate.TransportCertificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toTransportRequestCertificate

end Certificate

set_option genInjectivity false in
/-- Pointwise normalization schedules kept separate from the global raw cut-surface theorem. This contains no local
cells or boundary identity. -/
structure RawTransportSchedule {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  /-- For every original nonzero vector and positive target, retain its finite normalization comparison schedule. -/
    schedule : forall (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    RawRequestSchedule data inverseLower vector nonzero target positive

constructive_injectivity RawTransportSchedule

namespace RawTransportSchedule

/-- Combine one raw second-relation theorem with the finite normalization schedules to recover the established prepared
energy certificate. -/
@[expose] def toCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (schedule : Curves.Hyperelliptic.Integration.Energy.Prepared.RawTransportSchedule data inverseLower)
    (raw : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
      Curves.Hyperelliptic.Integration.Energy.Prepared.Certificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (schedule.schedule vector nonzero target positive).toRequestCertificate raw

/-- The same combination directly constructs persistent normalized pointwise positivity through the generic transport
layer. -/
@[expose] def toTransportCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (schedule : Curves.Hyperelliptic.Integration.Energy.Prepared.RawTransportSchedule data inverseLower)
    (raw : Curves.Hyperelliptic.Integration.Energy.Prepared.RawCertificate data) :
    Certificate.TransportCertificate data inverseLower :=
  (schedule.toCertificate raw).toTransportCertificate

end RawTransportSchedule

/-! ## Controlled-error request interface -/

set_option genInjectivity false in
/-- One second-relation request whose finite cut-surface calculation may have a displayed rational boundary error.

The error is paid before normalization, and the remaining strictly positive energy is the only lower bound passed to the
generic transport layer. -/
structure ControlledRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained comparison radius and its exact synchronized sample index. -/ comparison :
    ComparisonSchedule data inverseLower
  /-- The original request-cell boundary decomposition with its retained finite error at the same comparison sample. -/
    boundaryReduction : ControlledBoundaryReduction data vector
    comparison.sampleIndex
    (requestCells data inverseLower comparison.sampleIndex vector
      nonzero)
  /-- The retained finite boundary error is strictly below the original checked surface lower sum. -/
    boundaryError_lt_surface : boundaryReduction.boundaryError <
    surfaceEnergy
      (requestCells data inverseLower comparison.sampleIndex vector
        nonzero)
  /-- The retained positive radius for refining the persistent normalized matrix. -/ refinementRadius :
    Fraction.Rational
  /-- The retained persistent refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The squared refinement target is strictly below the original positive output target. -/ refinementTarget_lt_target
    :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The squared refinement target fits strictly within the retained synchronized comparison allowance. -/
    refinementTarget_lt_comparisonTarget :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      SynchronizedNormalization.comparisonTarget comparison.radius
  /-- The output and comparison perturbation budgets together fit strictly below the normalized energy remaining after
    boundary error. -/ margin :
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (Certificate.normalizedData data inverseLower)
              refinementRadius refinementRadiusPositive)) +
        comparisonBudget data inverseLower vector comparison.radius
          comparison.positive <
      Certificate.synchronizedNormalizedEnergyLower data
        comparison.sampleIndex
        (boundaryReduction.effectiveCells boundaryError_lt_surface)

constructive_injectivity ControlledRequestCertificate

namespace ControlledRequestCertificate

/-- Pay the finite boundary error and erase the geometric sidecars only after constructing the positive singleton lower
cell. -/
@[expose] def toTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledRequestCertificate data inverseLower
      vector
      nonzero target positive) :
    Certificate.TransportRequestCertificate data inverseLower
      vector nonzero target positive where
  sampleIndex := certificate.comparison.sampleIndex
  cellCount := 1
  cells := certificate.boundaryReduction.effectiveCells
    certificate.boundaryError_lt_surface
  positiveCell := 0
  positiveCell_area :=
    certificate.boundaryReduction.effectiveSurfaceEnergy_positive
      certificate.boundaryError_lt_surface
  positiveCell_density := by
    change (0 : Fraction.Rational) < 1
    decide
  energy_le_raw := by
    rw [Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction.cellEnergy_effectiveCells]
    exact certificate.boundaryReduction.effectiveSurfaceEnergy_le_raw
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparison.radius
  comparisonRadiusPositive := certificate.comparison.positive
  synchronized_close := by
    intro row column
    exact
      SynchronizedNormalization.centerMatrix_close_synchronized_of_index_eq
        data inverseLower certificate.comparison.radius
          certificate.comparison.positive certificate.comparison.sampleIndex
            certificate.comparison.sampleIndex_eq
          (Quadratic.Bounds.squaredRefinementTarget
            certificate.refinementRadius)
          (Quadratic.Bounds.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)
          certificate.refinementTarget_lt_comparisonTarget row column
  margin := by
    simpa only [Curves.Hyperelliptic.Integration.Energy.Prepared.comparisonBudget] using certificate.margin

end ControlledRequestCertificate

set_option genInjectivity false in
/-- Pointwise geometry-backed energy data with a controlled finite boundary error at every rational request. -/
structure ControlledCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  /-- For every nonzero vector and positive target, retain a geometry-backed request whose boundary and comparison
    errors are paid. -/ certify : forall (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    ControlledRequestCertificate data inverseLower vector nonzero
      target
      positive

constructive_injectivity ControlledCertificate

namespace ControlledCertificate

/-- Controlled finite boundary errors construct the generic pointwise energy transport certificate. -/
@[expose] def toTransportCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledCertificate data inverseLower) :
    Certificate.TransportCertificate data inverseLower where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toTransportRequestCertificate

end ControlledCertificate

/-! ## Tail-compatible controlled energy transport -/

/-- A retained synchronized raw sample has nonzero complete inverse scalar. This uses only the tail anchor estimate and
makes no assertion about any discarded coarse centre. -/
theorem tailSynchronizedScaledInverse_scalar_nonzero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix)
    (sampleIndex : Nat) (anchor_le : inverseTail.anchor <= sampleIndex) :
    (Certificate.synchronizedScaledInverse data sampleIndex).scalar
      ≠ 0 := by
  let inverse :=
    Certificate.synchronizedScaledInverse data sampleIndex
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample sampleIndex =
        inverse.scalar := by
    unfold canonicalScaledInverse inverse
      Certificate.synchronizedScaledInverse
    have samples :=
      PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) sampleIndex
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply inverseTail.sample_nonzero_of_anchor_le sampleIndex anchor_le
  rw [scalarSample, scalarZero]

set_option genInjectivity false in
/-- One geometry-backed second-relation request for a tail-apartified inverse.

The selected raw sample lies after the certified anchor. A finite boundary error is subtracted from the displayed
surface cells before exact normalization and entrywise transport to the persistent centre. -/
structure TailControlledRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix)
    (vector : EvaluationLower.RationalVector genus) (nonzero : EvaluationLower.NonzeroVector vector)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The retained synchronized raw sample chosen after the original inverse-separation anchor. -/ sampleIndex : Nat
  /-- The original inverse-separation anchor is no later than the retained raw sample index. -/ anchor_le :
    inverseTail.anchor <= sampleIndex
  /-- The number of retained checked surface cells in this original finite request. -/ cellCount : Nat
  /-- The checked surface cells indexed by the exact scaled coefficients at the retained raw sample. -/ cells : Fin
    cellCount -> Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve
    (Energy.scaledNormalizedCoefficients data sampleIndex
      vector)
  /-- The controlled boundary decomposition for these exact cells, scaled coefficients and retained raw sample. -/
    boundaryReduction : ControlledBoundaryReduction data vector
    sampleIndex cells
  /-- The retained finite boundary error is strictly below the original checked surface lower sum. -/
    boundaryError_lt_surface :
    boundaryReduction.boundaryError < surfaceEnergy cells
  /-- The retained positive radius for refining the persistent normalized matrix. -/ refinementRadius :
    Fraction.Rational
  /-- The retained persistent refinement radius is strictly positive. -/ refinementRadiusPositive : 0 < refinementRadius
  /-- The squared refinement target is strictly below the original positive output target. -/ refinementTarget_lt_target
    :
    Quadratic.Bounds.squaredRefinementTarget refinementRadius <
      target
  /-- The retained positive entrywise radius comparing the persistent center with the original synchronized matrix. -/
    comparisonRadius : Fraction.Rational
  /-- The retained entrywise comparison radius is strictly positive. -/ comparisonRadiusPositive : 0 < comparisonRadius
  /-- Every persistent center entry is within the retained comparison radius of its matching original synchronized
    matrix entry. -/ synchronized_close : forall row column : Fin genus,
    Data.Gaussian.Norm.Basic.normSq
        (Positivity.centerMatrix
            (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
              inverseTail.toScaledInverseCertificate)
            (Quadratic.Bounds.squaredRefinementTarget
              refinementRadius)
            (Quadratic.Bounds.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          Certificate.synchronizedNormalizedMatrix data
            sampleIndex row column) <
      comparisonRadius ^ 2
  /-- The output and comparison perturbation budgets together fit strictly below the normalized energy remaining after
    boundary error. -/ margin :
    Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
                inverseTail.toScaledInverseCertificate)
              refinementRadius refinementRadiusPositive)) +
        Budget.totalBudget
          (Budget.automaticBudget vector
            (Positivity.automaticRadius
              (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
                inverseTail.toScaledInverseCertificate)
              comparisonRadius comparisonRadiusPositive)) <
      Certificate.synchronizedNormalizedEnergyLower data
        sampleIndex
        (boundaryReduction.effectiveCells boundaryError_lt_surface)

constructive_injectivity TailControlledRequestCertificate

namespace TailControlledRequestCertificate

/-- Convert the controlled cut-surface calculation into the generic presentation-independent raw-sample transport. -/
@[expose] def toSampleTransportRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate data inverseTail
      vector
      nonzero target positive) :
    Certificate.SampleTransportRequestCertificate
      (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate)
      vector nonzero target positive where
  sampleIndex := certificate.sampleIndex
  scalarNonzero := Curves.Hyperelliptic.Integration.Energy.Prepared.tailSynchronizedScaledInverse_scalar_nonzero
    inverseTail
    certificate.sampleIndex certificate.anchor_le
  cellCount := 1
  cells := certificate.boundaryReduction.effectiveCells
    certificate.boundaryError_lt_surface
  positiveCell := 0
  positiveCell_area :=
    certificate.boundaryReduction.effectiveSurfaceEnergy_positive
      certificate.boundaryError_lt_surface
  positiveCell_density := by
    change (0 : Fraction.Rational) < 1
    decide
  energy_le_raw := by
    rw [Curves.Hyperelliptic.Integration.Energy.Prepared.ControlledBoundaryReduction.cellEnergy_effectiveCells]
    exact certificate.boundaryReduction.effectiveSurfaceEnergy_le_raw
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparisonRadius
  comparisonRadiusPositive := certificate.comparisonRadiusPositive
  synchronized_close := certificate.synchronized_close
  margin := certificate.margin

/-- Pay the retained boundary error and transport the same tail-separated sample into the normalized energy request. -/
@[expose] def toRequestCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    {vector : EvaluationLower.RationalVector genus} {nonzero : EvaluationLower.NonzeroVector vector}
    {target : Fraction.Rational} {positive : 0 < target}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.TailControlledRequestCertificate data inverseTail
      vector
      nonzero target positive) :
    Certificate.RequestCertificate
      (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate)
      vector nonzero target positive :=
  certificate.toSampleTransportRequestCertificate.toRequestCertificate

end TailControlledRequestCertificate

set_option genInjectivity false in
/-- Pointwise controlled surface calculations for a tail-normalized period matrix. -/
structure TailControlledCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseTail : ScalarTailSeparationCertificate data.aMatrix) where
  /-- For every nonzero vector and positive target, retain a controlled request using the original separated inverse
    tail. -/ certify : forall (vector : EvaluationLower.RationalVector genus)
    (nonzero : EvaluationLower.NonzeroVector vector) (target : Fraction.Rational)
    (positive : 0 < target),
    TailControlledRequestCertificate data inverseTail vector nonzero
      target
      positive

constructive_injectivity TailControlledCertificate

namespace TailControlledCertificate

/-- All public normalized energy fields are derived after paying the finite boundary error and transporting one retained
exact quotient sample. -/
@[expose] def toEnergyCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseTail : ScalarTailSeparationCertificate data.aMatrix}
    (certificate : Curves.Hyperelliptic.Integration.Energy.Prepared.TailControlledCertificate data inverseTail) :
    Purelib.Curves.Hyperelliptic.Integration.Energy.Certificate
      (PeriodMatrix.NormalizedPeriodData.ofScaledInverse data
        inverseTail.toScaledInverseCertificate) where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

end TailControlledCertificate

/-- Prepared schedules retain the geometry-backed surface interface at the same synchronized period data used by their
A/B programs. -/
abbrev CompatibleCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix) :=
  Certificate schedules.toPeriodData inverseLower

/-- Prepared schedules retain the controlled-error surface interface at the same synchronized period data used by their
A/B programs. -/
abbrev CompatibleControlledCertificate {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix) :=
  ControlledCertificate schedules.toPeriodData inverseLower

end Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

end

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergySurface

/-- The same geometry-backed surface cell indexed by the original curve and coefficient vector. -/
abbrev SurfaceCell {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.PreparedEnergySurface.GaussianVector genus) :=
  Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy.SurfaceCell curve coefficients

end Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergySurface

end
