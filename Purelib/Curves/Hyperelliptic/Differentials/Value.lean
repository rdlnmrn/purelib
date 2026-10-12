module
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Curves.Hyperelliptic

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

namespace Purelib.Curves.Hyperelliptic.Differentials.Value

/-- The named coefficient `x^k/y` of the differential. The affine path displacement is applied exactly once by
`CellModel.integralSample`; it is not duplicated inside this coefficient. -/
def differentialValue {genus : Nat}
    (differential : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    Coherent.CoherentNamed :=
  CoherentNamed.div
    (Power.namedPower (Coherence.exact point)
      differential.exponent)
    sheetValue apart

/-- Replacing the division-ready sheet name by an operationally equivalent one preserves the named differential
coefficient. Apartness is supplied separately on the two finite processes; no lower bound is transported through an
asserted completed value. -/
def differentialValue_respects_sheet {genus : Nat}
    (differential : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (first second : Coherent.CoherentNamed)
    (firstApart : Named.Apart first.name)
    (secondApart : Named.Apart second.name)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    Gaussian.Equivalence.NamedEquivalent
      (differentialValue differential point first firstApart).name
      (differentialValue differential point second secondApart).name := by
  let numerator := Power.namedPower
    (Coherence.exact point)
      differential.exponent
  exact Equivalence.coherentDiv_respects
    numerator numerator first second firstApart secondApart
      (NamedEquivalent.refl numerator.name)
      equivalent

/-- The differential coefficient center bound is the point norm power divided by the retained sheet lower bound. -/
@[simp] theorem differentialValue_centerBound {genus : Nat}
    (differential : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name) :
    (differentialValue differential point sheetValue
      apart).name.process.centerBound =
      Data.Gaussian.Norm.Basic.normSq point ^ differential.exponent /
        apart.certificate.lowerSq := by
  change (Power.namedPower (Coherence.exact point)
      differential.exponent).name.process.centerBound /
        apart.certificate.lowerSq =
      Data.Gaussian.Norm.Basic.normSq point ^ differential.exponent /
        apart.certificate.lowerSq
  rw [Power.namedPower_exact_centerBound]

/-- A possible finite quotient reading exposes an actual candidate of the stored denominator name; the numerator is the
exact displayed rational power. -/
theorem differentialValue_possible_components {genus : Nat}
    (differential : Differentials.Basic.Differential genus) (point : Data.Gaussian.Basic.Canonical)
    (sheetValue : Coherent.CoherentNamed)
    (apart : Named.Apart sheetValue.name)
    (state : (differentialValue differential point sheetValue
      apart).name.process.State)
    {candidate : Data.Gaussian.Basic.Canonical}
    (possible : (differentialValue differential point sheetValue
      apart).name.process.Possible
      state candidate) :
    ∃ denominator : Data.Gaussian.Basic.Canonical,
      sheetValue.name.process.Possible state.2 denominator ∧
        candidate = point ^ differential.exponent / denominator := by
  rcases possible with
    ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  refine ⟨denominator, denominatorPossible, ?_⟩
  rw [Power.namedPower_exact_possible_eq point differential.exponent state.1
    numeratorPossible]

end Purelib.Curves.Hyperelliptic.Differentials.Value

end
