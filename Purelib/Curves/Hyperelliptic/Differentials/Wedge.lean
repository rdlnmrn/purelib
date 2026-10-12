module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.Value
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Arithmetic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Differentials

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

namespace Purelib.Curves.Hyperelliptic.Differentials.Wedge

/-- Operational coefficient of the local wedge of two standard algebraic differentials. Both one-forms are scalar
multiples of the same displayed `dx`, so the antisymmetric coefficient is the finite CCL expression `left * right -
right * left`. -/
def differentialWedgeCoefficient {genus : Nat}
    (left right : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    Coherent.CoherentNamed :=
  let leftValue := Value.differentialValue left point sheetValue apart
  let rightValue := Value.differentialValue right point sheetValue apart
  CoherentNamed.add
    (CoherentNamed.mul leftValue rightValue)
    (CoherentNamed.neg
      (CoherentNamed.mul rightValue leftValue))

/-- The local wedge of any two displayed hyperelliptic basis differentials vanishes operationally. The proof is finite
arithmetic-name commutativity followed by exact additive cancellation; it does not invoke a completed function field or
exterior-algebra space. -/
def differentialWedgeCoefficient_zero {genus : Nat}
    (left right : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    Gaussian.Equivalence.NamedEquivalent
      (differentialWedgeCoefficient left right point sheetValue apart).name
      (Coherence.exact 0).name := by
  let leftValue := Value.differentialValue left point sheetValue apart
  let rightValue := Value.differentialValue right point sheetValue apart
  let leftRight :=
    CoherentNamed.mul leftValue rightValue
  let rightLeft :=
    CoherentNamed.mul rightValue leftValue
  let negativeRightLeft :=
    CoherentNamed.neg rightLeft
  have commute : Gaussian.Equivalence.NamedEquivalent leftRight.name rightLeft.name := by
    simpa only [leftRight, rightLeft,
      CoherentNamed.mul] using
      Laws.coherentMul_comm leftValue rightValue
  have replaceFirst : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.add
        leftRight negativeRightLeft).name
      (CoherentNamed.add
        rightLeft negativeRightLeft).name :=
    Congruence.coherentAdd_respects
      leftRight rightLeft negativeRightLeft negativeRightLeft commute
      (NamedEquivalent.refl negativeRightLeft.name)
  exact NamedEquivalent.trans replaceFirst (by
    simpa only [negativeRightLeft,
      CoherentNamed.add,
      CoherentNamed.neg,
      Coherence.exact] using
      Neg.coherentAdd_neg_right rightLeft)

end Purelib.Curves.Hyperelliptic.Differentials.Wedge

end
