module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

section
section
@[expose] public section

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

section Purelib.Riemann.Integration.LegendreFractionalWords

section FoldPreparations
end FoldPreparations
end Purelib.Riemann.Integration.LegendreFractionalWords

end

end

section
@[expose] public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Division

set_option genInjectivity false in
/-- A prepared equivalent presentation need not have the same process states or candidate predicate as the original
channel. Both presentations are retained, with their finite operational comparison. -/
structure Prepared (channel : Coherent.CoherentNamed)
  where
  /-- The prepared coherent denominator presentation. -/ denominator : Coherent.CoherentNamed
  /-- Uniform whole-ball apartness for the exact retained prepared denominator. -/ apart : Named.Apart denominator.name
  /-- The finite operational equivalence from the original channel to the retained denominator presentation. -/
    equivalent : Gaussian.Equivalence.NamedEquivalent channel.name denominator.name

constructive_injectivity Prepared

end Purelib.Approximation.Gaussian.Division

end

section
@[expose] public section

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

end

section
@[expose] public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

section Purelib.Riemann.Integration.LegendreFractionalAction

end Purelib.Riemann.Integration.LegendreFractionalAction

end
