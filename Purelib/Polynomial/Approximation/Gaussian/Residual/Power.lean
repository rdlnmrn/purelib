module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner.Power
public import Purelib.Approximation.Gaussian.Provenance.Power
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Arithmetic.Neg
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Power equations checked from original quantitative polynomial residuals

The coefficient test concerns the same retained polynomial. Its operational
equation supplies a finite-power law on the unchanged original channel.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)

variable {polynomial : CoefficientPolynomial} {channel : CoherentNamed}

/-- A checked power-polynomial identity yields its finite-power equation at the original residual channel.

The coefficient equality and quantitative residual concern the same retained
polynomial. Additive cancellation consumes its operational zero equation; no
individual approximate sample is asserted to solve that equation exactly.
-/
def powerIdentity (residual : Residual polynomial channel) (parameter : Canonical) (degree : RootDegree)
    (same : polynomial = Power.Gaussian.rootPolynomial parameter degree) :
    PowerIdentity channel degree.value parameter := by
  have equation := residual.equation
  rewrite [same] at equation
  let power := Name.Coherent.Power.namedPower channel degree.value
  let exactParameter := CoherentNamed.Coherence.exact parameter
  have zeroDifference := (Horner.polynomialEval_rootPolynomial parameter degree channel).symm.trans equation
  have negative : Equivalence.NamedEquivalent (CoherentNamed.neg exactParameter).name
      (CoherentNamed.Coherence.exact (-parameter)).name := Arithmetic.Neg.exactNeg parameter
  have replaceNegative := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects power power
    (CoherentNamed.neg exactParameter) (CoherentNamed.Coherence.exact (-parameter))
    (Equivalence.NamedEquivalent.refl _) negative
  exact Coherent.Additive.equivalent_of_sub_zero power exactParameter (replaceNegative.trans zeroDifference)

set_option genInjectivity false in
/-- The actual polynomial's checked monic pure-power form or its proved coefficient mismatch.

Degree and parameter are read from the same retained polynomial. A successful
check retains its structural identity and the original-channel power equation;
a mismatch asserts only that this particular coefficient form is absent.
-/
inductive PowerForm (residual : Residual polynomial channel) where
  /-- The same original coefficient table supplies its checked power identity. -/
  | recognized (same : polynomial = Power.Gaussian.rootPolynomial (-polynomial.eval 0)
      ⟨polynomial.natDegree, residual.degreePositive⟩)
      (identity : PowerIdentity channel polynomial.natDegree (-polynomial.eval 0))
  /-- The original coefficients differ from the monic pure-power candidate. -/
  | other (different : polynomial ≠ Power.Gaussian.rootPolynomial (-polynomial.eval 0)
      ⟨polynomial.natDegree, residual.degreePositive⟩)

constructive_injectivity PowerForm

/-- Check the original polynomial once and derive its power law only when that exact coefficient identity holds. -/
def inspectPower (residual : Residual polynomial channel) : PowerForm residual :=
  let degree : RootDegree := ⟨polynomial.natDegree, residual.degreePositive⟩
  let parameter := -polynomial.eval 0
  if same : polynomial = Power.Gaussian.rootPolynomial parameter degree then
    .recognized same (residual.powerIdentity parameter degree same)
  else .other same

/-- A proved original coefficient identity returns that same power equation and retained structural witness. -/
theorem inspectPower_recognized (residual : Residual polynomial channel)
    (same : polynomial = Power.Gaussian.rootPolynomial (-polynomial.eval 0)
      ⟨polynomial.natDegree, residual.degreePositive⟩) :
    residual.inspectPower = .recognized same
      (residual.powerIdentity (-polynomial.eval 0) ⟨polynomial.natDegree, residual.degreePositive⟩ same) := by
  unfold inspectPower
  dsimp only
  split
  · rfl
  · rename_i different
    exact (different same).elim

/-- A proved coefficient mismatch remains the same typed non-power outcome. -/
theorem inspectPower_other (residual : Residual polynomial channel)
    (different : polynomial ≠ Power.Gaussian.rootPolynomial (-polynomial.eval 0)
      ⟨polynomial.natDegree, residual.degreePositive⟩) : residual.inspectPower = .other different := by
  unfold inspectPower
  dsimp only
  split
  · rename_i same
    exact (different same).elim
  · rfl

/-- Read an exact scalar from the same quantitative monic linear residual on its original channel. -/
def scalar? (residual : Residual polynomial channel) :
    Option (Provenance.Rational.Basic.RationalSidecar channel) :=
  if one : polynomial.natDegree = 1 then
    match residual.inspectPower with
    | .recognized _ identity => some ⟨-polynomial.eval 0, by
        have equation := identity
        rewrite [one] at equation
        exact (Name.Coherent.Power.namedPower_one channel).symm.trans equation⟩
    | .other _ => none
  else none

/-- A residual of degree other than one supplies no scalar through the monic-linear reader. -/
theorem scalar?_of_degree_ne_one (residual : Residual polynomial channel) (degree : polynomial.natDegree ≠ 1) :
    residual.scalar? = none := by
  unfold scalar?
  rewrite [dif_neg degree]
  rfl

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
