module
import Purelib.Data.List.OfFn.Basic

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Stability
public import Purelib.Data.Rat.List.Minimum
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table (CoefficientTable)
open Purelib.RootIsolation.Owner.Family.Basic (OwnerFamily)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Stability
open Purelib.Data.Gaussian

/-! ## Owner-family transport across one coefficient reading -/

/-- Per-owner safe coefficient targets for an arbitrary degree-sized local
family. -/
def ownerFamilyStabilityTargets
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) : List Fraction.Rational :=
  List.ofFn fun index : Fin table.degree =>
    table.stabilityTarget (family.owner index).box
      (family.owner index).clearance
end Purelib.RootIsolation.Progressive.Owner.Stability

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Stability
open Purelib.Data.Gaussian

/-- Compute one common positive coefficient-stability allowance by taking the finite minimum of all owner targets. -/
def ownerFamilyStabilityTarget
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) : Fraction.Rational :=
  Data.Rat.List.Minimum.positiveMinimum (ownerFamilyStabilityTargets table family)
end Purelib.RootIsolation.Progressive.Owner.Stability

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Stability
open Purelib.Data.Gaussian

/-- The common stability allowance is at most each original owner's boundary-stability target. -/
theorem ownerFamilyStabilityTarget_le
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree)
    (index : Fin table.degree) :
    ownerFamilyStabilityTarget table family ≤
      table.stabilityTarget (family.owner index).box
        (family.owner index).clearance := by
  apply Data.Rat.List.Minimum.positiveMinimum_le_of_mem
  rw [ownerFamilyStabilityTargets]
  exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

end Purelib.RootIsolation.Progressive.Owner.Stability

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Stability
open Purelib.Data.Gaussian

/-- Every retained per-owner stability target is strictly positive. -/
theorem ownerFamilyStabilityTargets_positive
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) :
    ∀ target ∈ ownerFamilyStabilityTargets table family, 0 < target := by
  intro target member
  rw [ownerFamilyStabilityTargets] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
  exact table.stabilityTarget_pos (family.owner index).box
    (family.owner index).clearance
end Purelib.RootIsolation.Progressive.Owner.Stability

end

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Progressive.Owner.Stability
open Purelib.Data.Gaussian

/-- The common finite-family coefficient-stability allowance is strictly positive. -/
theorem ownerFamilyStabilityTarget_pos
    (table : CoefficientTable)
    (family : OwnerFamily table.polynomial table.degree) :
    0 < ownerFamilyStabilityTarget table family :=
  Data.Rat.List.Minimum.positiveMinimum_pos _
    (ownerFamilyStabilityTargets_positive table family)
end Purelib.RootIsolation.Progressive.Owner.Stability

end
