module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation

open Purelib.Data.Rat

open Purelib.Geometry.Path.Gaussian

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Polynomial.Ascending.Gaussian

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis

/-! ## Uniform local semantics -/

set_option genInjectivity false in
/-- The explicitly generated algebraic observation answering one rational parameter query. Its parameter is required to
be exactly the queried one; the observation's decomposition and bound therefore certify the local polynomial model at
that point. -/
structure UniformObservation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) (parameter : Fraction.Rational) where
  /-- The retained finite local observation for the original cell polynomial and allowance. -/ observation :
    Cell.Basic.LocalObservation cell.polynomial cell.localAllowance
  /-- The retained observation uses exactly the requested rational parameter. -/ parameter_eq : observation.parameter =
    parameter
  /-- The algebraic sheet and differential-reading evidence for this exact retained observation. -/ algebraic :
    Basis.AlgebraicObservation curve differential liftedCell cell
    observation
  /-- The retained quotient-state radius and observation error together fit the original cell allowance. -/
    semantic_error_le :
    2 *
        (4 *
            ((Value.differentialValue differential algebraic.point
              algebraic.sheetValue.value
              algebraic.sheetValue.apart).name.process.ball
                algebraic.readingState).radiusSq +
          Data.Gaussian.Norm.Basic.normSq observation.error) <=
      cell.localAllowance

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.UniformObservation

namespace UniformObservation

/-- Every later finite reading admitted by the certified quotient state lies within the cell's displayed local allowance
of the polynomial value. The factor eight pays constructively for comparing two points of one squared ball; the final
factor two is the Gaussian triangle estimate. -/
theorem candidate_error_le
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {start finish : Lifted.Basic.LiftedPoint 2} {liftedCell : Lifted.Basic.LiftedCell start finish}
    {cell : Cell.Basic.CellModel}
    {parameter : Fraction.Rational}
    (uniform : Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.UniformObservation curve differential liftedCell
      cell parameter)
    {candidate : Data.Gaussian.Basic.Canonical}
    (possible :
      (Value.differentialValue differential uniform.algebraic.point
        uniform.algebraic.sheetValue.value
        uniform.algebraic.sheetValue.apart).name.process.Possible
          uniform.algebraic.readingState candidate) :
    Data.Gaussian.Norm.Basic.normSq
        (candidate - Evaluation.eval cell.polynomial
          ⟨parameter, 0⟩) <= cell.localAllowance := by
  let value := Value.differentialValue differential uniform.algebraic.point
    uniform.algebraic.sheetValue.value uniform.algebraic.sheetValue.apart
  let ball := value.name.process.ball uniform.algebraic.readingState
  have candidateInside : ball.Contains candidate :=
    value.name.process.possible_inside possible
  have readingInside : ball.Contains uniform.observation.integrandReading :=
    value.name.process.possible_inside uniform.algebraic.readingPossible
  have candidateReadingIdentity :
      candidate - uniform.observation.integrandReading =
        (candidate - ball.center) +
          (ball.center - uniform.observation.integrandReading) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  have candidateReadingBound :
      Data.Gaussian.Norm.Basic.normSq
          (candidate - uniform.observation.integrandReading) <=
        4 * ball.radiusSq := by
    rw [candidateReadingIdentity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((candidate - ball.center) +
            (ball.center - uniform.observation.integrandReading)) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq
                (candidate - ball.center) +
              Data.Gaussian.Norm.Basic.normSq
                (ball.center - uniform.observation.integrandReading)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add candidateInside (by
            have reversed :
                ball.center - uniform.observation.integrandReading =
                  -(uniform.observation.integrandReading - ball.center) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Data.Gaussian.Basic.sub_re,
                  Data.Gaussian.Basic.sub_im,
                  Data.Gaussian.Basic.neg_re,
                  Data.Gaussian.Basic.neg_im] <;> ring1
            rw [reversed,
              Data.Gaussian.Norm.Basic.normSq_neg]
            exact readingInside)) (by decide)
      _ = 4 * ball.radiusSq := by ring1
  have totalIdentity :
      candidate - Evaluation.eval cell.polynomial
          ⟨parameter, 0⟩ =
        (candidate - uniform.observation.integrandReading) +
          uniform.observation.error := by
    have inputEqual :
        (⟨parameter, 0⟩ : Data.Gaussian.Basic.Canonical) =
          ⟨uniform.observation.parameter, 0⟩ := by
      rw [uniform.parameter_eq]
    rw [inputEqual, ← uniform.observation.decomposition]
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [totalIdentity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add candidateReadingBound le_rfl) (by decide)).trans
        uniform.semantic_error_le)

end UniformObservation

set_option genInjectivity false in
/-- Productive uniform semantics for a nonstationary integration cell. A query supplies a rational unit-interval
parameter and receives a finite algebraic sheet value, an admitted differential reading, and the checked model-error
inequality at that exact parameter. -/
structure UniformCellCertificate {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) where
  /-- At every rational unit-interval parameter, return the retained algebraic observation and its quantitative model
    guarantee. -/ query : forall parameter : Fraction.Rational,
    (0 : Fraction.Rational) <= parameter ->
    parameter <= 1 ->
      UniformObservation curve differential liftedCell cell
        parameter

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.UniformCellCertificate

set_option genInjectivity false in
/-- A stationary cell contributes exactly zero regardless of its integrand. Every nonstationary cell must instead carry
the uniform algebraic model contract. In particular, an empty observation list can no longer certify an arbitrary
nonzero segment as a period integrand. -/
inductive ValidCellCertificate {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) : Type 2
  /-- The original cell has equal endpoints and therefore zero displacement. -/ | stationary (equal : cell.start =
    cell.finish) :
      ValidCellCertificate curve differential
        liftedCell cell
  /-- The original cell has a productive algebraic model certificate at every rational unit-interval parameter. -/ |
    uniform (certificate :
      UniformCellCertificate curve differential liftedCell
        cell) :
      ValidCellCertificate curve differential
        liftedCell cell

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.ValidCellCertificate

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets

set_option genInjectivity false in
/-- A query at every rational unit parameter, together with enough explicit error budget to control every later reading
of the admitted CCL state. -/
structure UniformObservation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) (parameter : Fraction.Rational) where
  /-- The retained finite local observation for the original cell polynomial and allowance. -/ observation :
    Cell.Basic.LocalObservation cell.polynomial cell.localAllowance
  /-- The retained observation uses exactly the requested rational parameter. -/ parameter_eq : observation.parameter =
    parameter
  /-- The algebraic sheet and differential-reading evidence for this exact retained observation. -/ algebraic :
    Jets.AlgebraicObservation curve differential liftedCell cell
    observation
  /-- The retained quotient-state radius and observation error together fit the original cell allowance. -/
    semantic_error_le :
    2 *
        (4 *
            (((differential.value algebraic.point
              algebraic.sheetValue.value
              algebraic.sheetValue.apart).name.process.ball
                algebraic.readingState).radiusSq) +
          Data.Gaussian.Norm.Basic.normSq observation.error) <=
      cell.localAllowance

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

namespace UniformObservation

/-- Every admitted later reading remains within the displayed local polynomial allowance. The proof is independent of
the odd exponent once the coherent arithmetic name has been constructed. -/
theorem candidate_error_le
  {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : OddPower.Basic.OddPowerDifferential}
    {start finish : Lifted.Basic.LiftedPoint 2} {liftedCell : Lifted.Basic.LiftedCell start finish}
    {cell : Cell.Basic.CellModel} {parameter : Fraction.Rational}
    (uniform : Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation curve differential liftedCell
      cell parameter)
    {candidate : Data.Gaussian.Basic.Canonical}
    (possible :
      (differential.value uniform.algebraic.point
        uniform.algebraic.sheetValue.value
        uniform.algebraic.sheetValue.apart).name.process.Possible
          uniform.algebraic.readingState candidate) :
    Data.Gaussian.Norm.Basic.normSq
        (candidate - Evaluation.eval cell.polynomial
          ⟨parameter, 0⟩) <= cell.localAllowance := by
  let value := differential.value uniform.algebraic.point
    uniform.algebraic.sheetValue.value uniform.algebraic.sheetValue.apart
  let ball := value.name.process.ball uniform.algebraic.readingState
  have candidateInside : ball.Contains candidate :=
    value.name.process.possible_inside possible
  have readingInside : ball.Contains uniform.observation.integrandReading :=
    value.name.process.possible_inside uniform.algebraic.readingPossible
  have candidateReadingIdentity :
      candidate - uniform.observation.integrandReading =
        (candidate - ball.center) +
          (ball.center - uniform.observation.integrandReading) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  have candidateReadingBound :
      Data.Gaussian.Norm.Basic.normSq
          (candidate - uniform.observation.integrandReading) <=
        4 * ball.radiusSq := by
    rw [candidateReadingIdentity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((candidate - ball.center) +
            (ball.center - uniform.observation.integrandReading)) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq
                (candidate - ball.center) +
              Data.Gaussian.Norm.Basic.normSq
                (ball.center - uniform.observation.integrandReading)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add candidateInside (by
            have reversed :
                ball.center - uniform.observation.integrandReading =
                  -(uniform.observation.integrandReading - ball.center) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Data.Gaussian.Basic.sub_re,
                  Data.Gaussian.Basic.sub_im,
                  Data.Gaussian.Basic.neg_re,
                  Data.Gaussian.Basic.neg_im] <;> ring1
            rw [reversed,
              Data.Gaussian.Norm.Basic.normSq_neg]
            exact readingInside)) (by decide)
      _ = 4 * ball.radiusSq := by ring1
  have totalIdentity :
      candidate - Evaluation.eval cell.polynomial
          ⟨parameter, 0⟩ =
        (candidate - uniform.observation.integrandReading) +
          uniform.observation.error := by
    have inputEqual : (⟨parameter, 0⟩ : Data.Gaussian.Basic.Canonical) =
        ⟨uniform.observation.parameter, 0⟩ := by
      rw [uniform.parameter_eq]
    rw [inputEqual, ← uniform.observation.decomposition]
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re,
        Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [totalIdentity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add candidateReadingBound le_rfl) (by decide)).trans
        uniform.semantic_error_le)

end UniformObservation

set_option genInjectivity false in
/-- A nonstationary cell must answer every rational unit-interval query with uniform odd-power algebraic evidence. -/
structure UniformCellCertificate {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) where
  /-- At every rational unit-interval parameter, return the retained algebraic observation and its quantitative model
    guarantee. -/ query : forall parameter : Fraction.Rational, 0 <= parameter -> parameter <= 1 ->
    UniformObservation curve differential liftedCell cell
      parameter

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformCellCertificate

set_option genInjectivity false in
/-- A stationary cell or a uniform certificate for the retained odd-power differential.

A nonstationary cell must answer every bounded rational parameter query with the original sheet evidence and paid local
model bound. -/
inductive ValidCellCertificate {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPower.Basic.OddPowerDifferential)
    {start finish : Lifted.Basic.LiftedPoint 2} (liftedCell : Lifted.Basic.LiftedCell start finish)
    (cell : Cell.Basic.CellModel) : Type 2
  /-- The original cell has equal endpoints and therefore zero displacement. -/ | stationary (equal : cell.start =
    cell.finish) :
      ValidCellCertificate curve differential liftedCell
        cell
  /-- The original cell has a productive algebraic model certificate at every rational unit-interval parameter. -/ |
    uniform (certificate :
      UniformCellCertificate curve differential liftedCell cell)
        :
      ValidCellCertificate curve differential liftedCell
        cell

constructive_injectivity Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.ValidCellCertificate

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets

end
