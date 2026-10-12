module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.PeriodMonodromy
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Data.Fin.Lemmas
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Curves.Legendre

open Purelib.LinearAlgebra.Gaussian

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Curves.Legendre.Periods.Positive.Enclosure

/-- Consume the existing finite period positivity interface. One request in the unit direction supplies the reusable
enclosure for every finite word. -/
def enclosureOfPeriodPositivity {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter}
    (data : PeriodMonodromy.NormalizedData frame)
    (positivity : PeriodMatrix.PointwisePositivity data.normalized) :
    Positive.Basic.PositiveEnclosure data.ratio := by
  let direction : QuadraticForm.RationalVector 1 := Data.Vector.Basic.vectorOfFn fun _ => 1
  have directionNonzero : QuadraticForm.NonzeroVector direction := ⟨0, by decide⟩
  let certificate := positivity.certify direction directionNonzero 1 (by decide)
  let prepared := data.normalized.prepareOmegaEntry certificate.refinementTarget
    certificate.refinementPositive 0 0
  refine
    { state := prepared.name.state
      lower := certificate.epsilon
      positive := certificate.epsilon_positive
      inside_lower := ?_ }
  intro value inside
  have lower := certificate.compatible_positive
    (LinearAlgebra.Matrix.matrixOfFn fun _ _ => value) (by
      intro row column
      have rowZero : row = 0 := Fin.ext (by
        change row.val = 0
        omega)
      have columnZero : column = 0 := Fin.ext (by
        change column.val = 0
        omega)
      subst row
      subst column
      rw [LinearAlgebra.Matrix.matrixOfFn_apply]
      exact inside)
  change certificate.epsilon ≤ value.im
  have quadratic : Purelib.LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm direction
      (LinearAlgebra.Matrix.matrixOfFn fun _ _ => value) = value.im := by
    unfold Purelib.LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    change (1 * value.im * 1 + 0) + 0 = value.im
    ring1
  rw [quadratic] at lower
  exact lower.le

end Purelib.Curves.Legendre.Periods.Positive.Enclosure

end
