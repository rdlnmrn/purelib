module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Dense.Gaussian.Companion.Arithmetic.Bounds
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Recursive arithmetic on original polynomial residual channels

Each input keeps its actual numerical residual certificate and original
coherent channel. One stored companion elimination and computed norm budget
give the same kind of quantitative evidence on the unchanged output operation,
so later arithmetic consumes that exact retained result program.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Companion (Operation Elimination)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Norm.Basic (normSq)

namespace Arithmetic

/-- The selected operation on its same two original coherent input channels. -/
@[expose] def channel (operation : Operation) (first second : CoherentNamed) : CoherentNamed :=
  match operation with
  | .add => CoherentNamed.add first second
  | .mul => CoherentNamed.mul first second

/-- The selected operation on both retained geometric sample programs at their unchanged finite indices. -/
def geometric (operation : Operation) (first second : GeometricApproximation) : GeometricApproximation :=
  match operation with
  | .add => first.add second
  | .mul => first.mul second

/-- The actual selected geometric sample is the original scalar operation on both same-index input readings. -/
theorem geometric_sample (operation : Operation) (first second : GeometricApproximation) (index : Nat) :
    (geometric operation first second).sample index = operation.value (first.sample index) (second.sample index) := by
  cases operation <;> rfl

/-- Original arithmetic channels realize an actual stored target with the selected same-index sample operation. -/
def agreesWith (operation : Operation) (first second : CoherentNamed) (left right target : GeometricApproximation)
    (firstEq : NamedEquivalent first.name left.toApproximation.toNamed)
    (secondEq : NamedEquivalent second.name right.toApproximation.toNamed)
    (sample_eq : ∀ index, target.sample index = operation.value (left.sample index) (right.sample index)) :
    NamedEquivalent (channel operation first second).name target.toApproximation.toNamed := by
  cases operation with
  | add => exact Geometric.Coherent.Comparison.add_agreesWith first second left right target firstEq secondEq sample_eq
  | mul => exact Geometric.Coherent.Comparison.mul_agreesWith first second left right target firstEq secondEq sample_eq

/-- Original channel/sample comparisons transport through the actual selected arithmetic operation. -/
def agrees (operation : Operation) (first second : CoherentNamed) (left right : GeometricApproximation)
    (firstEq : NamedEquivalent first.name left.toApproximation.toNamed)
    (secondEq : NamedEquivalent second.name right.toApproximation.toNamed) :
    NamedEquivalent (channel operation first second).name (geometric operation left right).toApproximation.toNamed :=
  agreesWith operation first second left right (geometric operation left right) firstEq secondEq
    (fun index => geometric_sample operation left right index)

end Arithmetic

variable {firstPolynomial secondPolynomial : CoefficientPolynomial} {firstChannel secondChannel : CoherentNamed}

set_option genInjectivity false in
/-- Two original residual certificates with their retained arithmetic elimination, sample program and computed bound.

The actual input records and their identities remain stored. The companions
consume their original polynomials; the output program reads their same cached
samples at unchanged indices. Its quantitative result can be consumed by
further arithmetic without a new root-isolation or branch-selection premise.
-/
structure Arithmetic (operation : Operation) (originalFirst : Residual firstPolynomial firstChannel)
    (originalSecond : Residual secondPolynomial secondChannel) where
  /-- The actual retained first original numerical residual certificate. -/
  first : Residual firstPolynomial firstChannel
  /-- The stored first certificate is the original supplied record. -/
  first_eq : first = originalFirst
  /-- The actual retained second original numerical residual certificate. -/
  second : Residual secondPolynomial secondChannel
  /-- The stored second certificate is the original supplied record. -/
  second_eq : second = originalSecond
  /-- The actual companion computed from the first original polynomial. -/
  firstCompanion : Dense.Companion firstPolynomial
  /-- The actual companion computed from the second original polynomial. -/
  secondCompanion : Dense.Companion secondPolynomial
  /-- The selected tensor/pencil elimination on those same retained companions. -/
  elimination : Elimination operation firstCompanion secondCompanion
  /-- The same computed norm/inverse-row cache at both actual input sample bounds. -/
  bounds : Dense.Gaussian.Companion.Arithmetic.Bounds elimination first.source.centerBound second.source.centerBound
  /-- The actual retained arithmetic result sample program. -/
  result : GeometricApproximation
  /-- The result reads the same original input sample programs through the selected operation. -/
  result_eq : result = Arithmetic.geometric operation first.source second.source
  /-- The unchanged original coherent operation agrees with those same retained result samples. -/
  equivalent : NamedEquivalent (Arithmetic.channel operation firstChannel secondChannel).name
    result.toApproximation.toNamed
  /-- The computed output polynomial residual scale. -/
  residualScale : Rational
  /-- The scale consumes the same original input scales and retained elimination multiplier. -/
  residualScale_eq : residualScale = bounds.multiplier * (first.scale + second.scale)

constructive_injectivity Arithmetic

namespace Arithmetic

/-- Compute arithmetic residual evidence on the same two retained original numerical inputs. -/
def ofResiduals (operation : Operation) (first : Residual firstPolynomial firstChannel)
    (second : Residual secondPolynomial secondChannel) : Arithmetic operation first second :=
  let firstCompanion := Dense.Companion.ofPositive firstPolynomial first.degreePositive
  let secondCompanion := Dense.Companion.ofPositive secondPolynomial second.degreePositive
  let elimination := Elimination.ofCompanions operation firstCompanion secondCompanion
  let bounds := Dense.Gaussian.Companion.Arithmetic.Bounds.prepare elimination
    first.source.centerBound second.source.centerBound first.source.centerBound_nonneg second.source.centerBound_nonneg
  let result := geometric operation first.source second.source
  let equivalent := agreesWith operation firstChannel secondChannel first.source second.source result
    first.equivalent second.equivalent (fun index => geometric_sample operation first.source second.source index)
  let residualScale := bounds.multiplier * (first.scale + second.scale)
  ⟨first, rfl, second, rfl, firstCompanion, secondCompanion, elimination, bounds,
    result, rfl, equivalent, residualScale, rfl⟩

variable {operation : Operation} {first : Residual firstPolynomial firstChannel}
variable {second : Residual secondPolynomial secondChannel}

/-- Read the actual stored arithmetic elimination's coefficient polynomial. -/
@[expose] def polynomial (arithmetic : Arithmetic operation first second) : CoefficientPolynomial :=
  arithmetic.elimination.polynomial

/-- The actual computed arithmetic polynomial has positive degree. -/
theorem degreePositive (arithmetic : Arithmetic operation first second) : 0 < arithmetic.polynomial.natDegree :=
  arithmetic.elimination.degree_pos

/-- The retained computed residual scale is nonnegative. -/
theorem residualScale_nonnegative (arithmetic : Arithmetic operation first second) : 0 ≤ arithmetic.residualScale := by
  rewrite [arithmetic.residualScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct arithmetic.bounds.multiplier_nonnegative
    (Fraction.Order.Arithmetic.add_le_add_direct arithmetic.first.scale_nonnegative arithmetic.second.scale_nonnegative)

/-- The retained arithmetic result reads the operation on the same two original numerical samples. -/
theorem result_sample (arithmetic : Arithmetic operation first second) (index : Nat) :
    arithmetic.result.sample index =
      operation.value (arithmetic.first.source.sample index) (arithmetic.second.source.sample index) := by
  rewrite [arithmetic.result_eq]
  exact geometric_sample _ _ _ _

/-- Every actual output reading satisfies the polynomial residual bound computed from both same stored input bounds. -/
theorem sample_residual (arithmetic : Arithmetic operation first second) (index : Nat) :
    normSq (arithmetic.polynomial.eval (arithmetic.result.sample index)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius arithmetic.residualScale index := by
  have estimate := arithmetic.bounds.normSq_polynomial_le
    (arithmetic.first.source.sample index) (arithmetic.second.source.sample index)
    (arithmetic.first.source.sample_bounded index) (arithmetic.second.source.sample_bounded index)
  unfold Dense.Gaussian.Companion.Arithmetic.Bounds.PolynomialBound
    Dense.Gaussian.Companion.Arithmetic.Bounds.polynomialBudget
    Dense.Gaussian.Companion.Arithmetic.Bounds.sourceErrors at estimate
  have sources := Fraction.Order.Arithmetic.add_le_add_direct
    (arithmetic.first.bound index) (arithmetic.second.bound index)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sources
    arithmetic.bounds.multiplier_nonnegative
  rewrite [arithmetic.result_sample index]
  exact estimate.trans (paid.trans_eq (by
    rewrite [arithmetic.residualScale_eq,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    ring0))

/-- Retain the actual computed arithmetic result program as input evidence for a later original-channel operation. -/
@[expose] def residualCertificate (arithmetic : Arithmetic operation first second) :
    Residual arithmetic.polynomial (channel operation firstChannel secondChannel) :=
  Residual.ofGeometric arithmetic.degreePositive arithmetic.result arithmetic.equivalent
    arithmetic.residualScale arithmetic.residualScale_nonnegative arithmetic.sample_residual

/-- Further arithmetic reads the same actual stored result program from its retained residual certificate. -/
theorem residualCertificate_source (arithmetic : Arithmetic operation first second) :
    arithmetic.residualCertificate.source = arithmetic.result := rfl

/-- Further arithmetic retains the same actual computed residual scale. -/
theorem residualCertificate_scale (arithmetic : Arithmetic operation first second) :
    arithmetic.residualCertificate.scale = arithmetic.residualScale := rfl

end Arithmetic

end Purelib.Polynomial.Approximation.Gaussian

end
