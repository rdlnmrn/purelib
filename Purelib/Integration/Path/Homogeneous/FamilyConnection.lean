module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Integration.Budget.Trace.Family
public import Purelib.Integration.Path.HomogeneousTraceConnection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

public section

/-! Concatenate the paid parent traces on their exact increment paths.
The final endpoint potential remains an explicit sheet-return obligation. -/
namespace Purelib.Integration.Path.Homogeneous.FamilyConnection

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Budget.Trace.Family (basisFamilyLoss basisFamilyLoss_common BasisFamilyAllowance)

open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
set_option genInjectivity false in
/-- An ordered family of homogeneous traces retaining shared endpoints, potentials and original path lists.

Each original segment count pays its own energy contribution plus the common allowance; the indexed family keeps the
exact input coefficients and concatenation chain. -/
inductive BasisTraceFamily {genus : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (energy allowance : IncrementArea.Coordinate) :
    List Nat → List (List IncrementArea.Gaussian) → IncrementArea.Gaussian → IncrementArea.Gaussian →
      IncrementArea.Gaussian → IncrementArea.Gaussian → Type where
  /-- The empty trace family at one retained endpoint and potential. -/ | nil (first potential : IncrementArea.Gaussian)
    : Purelib.Integration.Path.Homogeneous.FamilyConnection.BasisTraceFamily coefficients energy allowance [] [] first
    first potential potential
  /-- Prepend the exact head trace to its endpoint-compatible retained tail family. -/ | cons {count : Nat} {counts :
    List Nat} {path : List IncrementArea.Gaussian} {paths : List (List IncrementArea.Gaussian)}
      {first middle last firstPotential middlePotential lastPotential : IncrementArea.Gaussian}
      (head : HomogeneousTraceConnection.HomogeneousTrace coefficients path first middle firstPotential middlePotential
        ((count : IncrementArea.Coordinate) * energy + allowance))
      (tail : Purelib.Integration.Path.Homogeneous.FamilyConnection.BasisTraceFamily coefficients energy allowance
        counts paths middle last middlePotential lastPotential) :
      Purelib.Integration.Path.Homogeneous.FamilyConnection.BasisTraceFamily coefficients energy allowance (count ::
        counts) (path :: paths) first last firstPotential lastPotential

constructive_injectivity BasisTraceFamily

namespace BasisTraceFamily

variable {genus : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {energy allowance : Purelib.Integration.Path.IncrementArea.Coordinate} {counts : List Nat} {paths : List (List
    Purelib.Integration.Path.IncrementArea.Gaussian)}
  {first last firstPotential lastPotential : Purelib.Integration.Path.IncrementArea.Gaussian}

open Purelib.Integration.Budget in
open Purelib.Integration.Path in
/-- Connect the original ordered trace family into a homogeneous trace with its certified family loss. -/
@[expose] def connect : {counts : List Nat} → {paths : List (List IncrementArea.Gaussian)} →
    {first last firstPotential lastPotential : IncrementArea.Gaussian} →
    Homogeneous.FamilyConnection.BasisTraceFamily coefficients energy allowance counts paths first last firstPotential
      lastPotential →
    HomogeneousTraceConnection.HomogeneousTrace coefficients paths.flatten first last firstPotential lastPotential
      (Trace.Family.basisFamilyLoss counts energy allowance)
  | _, _, _, _, _, _, .nil first potential => HomogeneousTraceConnection.HomogeneousTrace.empty coefficients first
    potential
  | _, _, _, _, _, _, .cons head tail => head.append tail.connect

end BasisTraceFamily

namespace BasisFamilyAllowance

variable {genus : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {parentCount : Nat} {counts : List Nat} {target : Purelib.Integration.Path.IncrementArea.Coordinate} {paths : List
    (List Purelib.Integration.Path.IncrementArea.Gaussian)}
  {first last firstPotential lastPotential : Purelib.Integration.Path.IncrementArea.Gaussian}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Budget in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Connect the retained trace family under its original family allowance.

The exact family-length certificate pays the zero-energy common allowances against the target; the returned trace reuses
the joined summary, trace and corrected value. -/
@[expose] def connect (allocation : Trace.Family.BasisFamilyAllowance parentCount target)
    (family : Homogeneous.FamilyConnection.BasisTraceFamily coefficients 0
      (allocation.allowance + allocation.allowance + allocation.allowance + allocation.allowance)
      counts paths first last firstPotential lastPotential)
    (counted : counts.length = parentCount) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients paths.flatten first last firstPotential lastPotential
      target := by
  let joined := family.connect
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : IncrementArea.Coordinate)) _ (fun row
        => Basic.Canonical.normSq_nonneg (coefficients row)))
  have paid : Trace.Family.basisFamilyLoss counts 0
      (allocation.allowance + allocation.allowance + allocation.allowance + allocation.allowance) ≤ target := by
    rw [Trace.Family.basisFamilyLoss_common, counted, ← allocation.loss_eq]
    exact allocation.paid
  have lower := (Fraction.Order.Arithmetic.neg_le_neg_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid nonnegative)).trans joined.lower
  exact ⟨joined.summary, joined.total_eq, joined.trace, joined.trace_eq,
    joined.corrected, joined.corrected_eq, lower⟩

end BasisFamilyAllowance
end Purelib.Integration.Path.Homogeneous.FamilyConnection
