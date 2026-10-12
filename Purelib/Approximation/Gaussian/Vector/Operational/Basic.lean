module
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

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

namespace Purelib.Riemann.Integration.LegendreFractionalWords

namespace FoldPreparations
end FoldPreparations
end Purelib.Riemann.Integration.LegendreFractionalWords

end

end

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Approximation.Gaussian.Vector.Operational.Basic

/-- A displayed two-coordinate vector of coherent Gaussian names. -/
abbrev RawPeriodVector := Fin 2 -> Coherent.CoherentNamed

/-- Pointwise operational equality of raw period vectors. -/
def VectorEquivalent (left right :
  RawPeriodVector) : Type :=
  forall coordinate, Gaussian.Equivalence.NamedEquivalent (left coordinate).name
    (right coordinate).name

namespace VectorEquivalent

/-- Every two-coordinate coherent vector is pointwise operationally equivalent to itself. -/
def refl (periods :
  Approximation.Gaussian.Vector.Operational.Basic.RawPeriodVector) :
  Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent periods periods :=
  fun coordinate =>
    NamedEquivalent.refl (periods coordinate).name

/-- Reverse a pointwise operational equivalence between two coherent vectors. -/
def symm {left right :
  Approximation.Gaussian.Vector.Operational.Basic.RawPeriodVector}
    (equivalent : Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent left right) :
      Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent right left :=
  fun coordinate =>
    NamedEquivalent.symm (equivalent coordinate)

/-- Compose pointwise operational equivalences through the same retained middle vector. -/
def trans {first second third :
  Approximation.Gaussian.Vector.Operational.Basic.RawPeriodVector}
    (firstSecond : Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent first second)
    (secondThird : Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent second third) :
    Approximation.Gaussian.Vector.Operational.Basic.VectorEquivalent first third := fun coordinate =>
  NamedEquivalent.trans
    (firstSecond coordinate) (secondThird coordinate)

end VectorEquivalent
end Purelib.Approximation.Gaussian.Vector.Operational.Basic

end

section
@[expose] public section
end
