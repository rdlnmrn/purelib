module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Provenance

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic

section
@[expose] public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Annotated

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option backward.match.sparseCases false in
/-- Negate the original numerical channel and propagate rational provenance when it is present. -/
def neg (input : Annotated)
  : Annotated :=
  { channel := CoherentNamed.neg input.channel
    provenance := match input.provenance with
      | some (.inl rational) => some (.inl (Rational.Arithmetic.negateRational rational))
      | _ => none }

set_option backward.match.sparseCases false in
/-- Add the original numerical channels and propagate supported rational or zero-identity provenance.

Unsupported combinations retain their actual sum channel with no provenance sidecar. -/
def add (left right :
  Annotated) : Annotated :=
  { channel := CoherentNamed.add left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.inl first), some (.inl second) => some (.inl (first.add second))
      | some (.inl first), other =>
          if zero : first.value = 0 then other.map fun p =>
            Provenance.transportProvenance p (Add.addLeftZero _ _ (Rational.Arithmetic.rationalZero first zero)) else
              none
      | other, some (.inl second) =>
          if zero : second.value = 0 then other.map fun p =>
            Provenance.transportProvenance p (Add.addRightZero _ _ (Rational.Arithmetic.rationalZero second zero)) else
              none
      | _, _ => none }

set_option backward.match.sparseCases false in
/-- Multiply the original numerical channels and propagate supported rational, zero and unit provenance.

Unsupported combinations retain their actual product channel with no provenance sidecar. -/
def mul (left right :
  Annotated) : Annotated :=
  { channel := CoherentNamed.mul left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.inl first), some (.inl second) => some (.inl (first.mul second))
      | some (.inl first), other =>
          if zero : first.value = 0 then some (.inl (RationalSidecar.zero
            (NamedEquivalent.trans
              (by simpa only [zero, CoherentNamed.mul,
                Coherence.exact] using Mul.mulLeftConstant left.channel right.channel first)
              (Mul.coherentMul_zero_left right.channel))))
          else if one : first.value = 1 then other.map fun p => Provenance.transportProvenance p
            (NamedEquivalent.trans
              (by simpa only [one, CoherentNamed.mul,
                Coherence.exact] using Mul.mulLeftConstant left.channel right.channel first)
              (Mul.coherentMul_one_left right.channel))
          else none
      | other, some (.inl second) =>
          if zero : second.value = 0 then some (.inl (RationalSidecar.zero
            (NamedEquivalent.trans
              (by
                  simpa only [zero, CoherentNamed.mul, Coherence.exact]
                    using Mul.mulRightConstant left.channel right.channel second)
              (Mul.coherentMul_zero_right left.channel))))
          else if one : second.value = 1 then other.map fun p => Provenance.transportProvenance p
            (NamedEquivalent.trans
              (by
                  simpa only [one, CoherentNamed.mul, Coherence.exact]
                    using Mul.mulRightConstant left.channel right.channel second)
              (Mul.coherentMul_one_right left.channel))
          else none
      | _, _ => none }

/-- The same compiled channel is shared by both occurrences. -/
def cancel (input :
  Annotated) : Annotated :=
  ⟨CoherentNamed.add input.channel
      (CoherentNamed.neg input.channel),
    some (.inl (RationalSidecar.addNeg input.channel))⟩

/-- A retained square equation recovers exact rational provenance for the square, even when no rational reading is
itself an exact root. -/
def square (input :
  Annotated) : Annotated :=
  { channel := CoherentNamed.mul input.channel input.channel
    provenance := match input.provenance with
      | some (.inl rational) => some (.inl (rational.mul rational))
      | some (.inr root) => some (.inl ⟨root.parameter, root.square⟩)
      | none => none }
end Purelib.Approximation.Gaussian.Acquisition.Annotated

end
