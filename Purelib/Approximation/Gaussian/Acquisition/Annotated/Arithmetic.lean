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
import Purelib.Data.Gaussian.Cast.Real
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

namespace Purelib.Approximation.Gaussian.Acquisition.Provenance

/-- Read the retained arbitrary-degree numerical construction from supported scalar or root provenance. -/
def algebraic? {channel : CoherentNamed} : Provenance channel → Option (Algebraic.Sidecar channel)
  | .rational reading => some (Algebraic.Sidecar.ofRational reading)
  | .polynomialRoot root => some (Algebraic.Sidecar.ofRoot root)
  | .algebraic sidecar => some sidecar
  | .squareRoot _ => none
  | .quadratic _ => none

end Purelib.Approximation.Gaussian.Acquisition.Provenance

namespace Purelib.Approximation.Gaussian.Acquisition.Annotated

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option backward.match.sparseCases false in
/-- Negate the original numerical channel and retain supported scalar, quadratic or general algebraic evidence. -/
def neg (input : Annotated)
  : Annotated :=
  { channel := CoherentNamed.neg input.channel
    provenance := match input.provenance with
      | some (.rational reading) => some (.rational (Rational.Arithmetic.negateRational reading))
      | some (.quadratic coordinates) => some (.quadratic coordinates.neg)
      | some provenance => match provenance.algebraic? with
          | some sidecar => some (.algebraic sidecar.neg)
          | none => none
      | none => none }

set_option backward.match.sparseCases false in
/-- Add the original numerical channels and propagate supported rational or zero-identity provenance.

Unsupported combinations retain their actual sum channel with no provenance
sidecar. Disabling general algebraic inference preserves the rational, quadratic
and zero rules while leaving a compound general-algebraic output unannotated
for exact coefficient normalization by its retaining compiler. -/
def add (left right :
  Annotated) (inferAlgebraic : Bool := true) : Annotated :=
  { channel := CoherentNamed.add left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.rational first), some (.rational second) => some (.rational (first.add second))
      | some (.rational first), other =>
          if zero : first.value = 0 then other.map fun p =>
            Provenance.transportProvenance p (Add.addLeftZero _ _ (Rational.Arithmetic.rationalZero first zero)) else
              match other with
              | some (.quadratic coordinates) =>
                  match Cast.inspectReal first.value with
                  | .real value same => some (.quadratic (coordinates.addScalarLeft first value same))
                  | .complex _ => none
              | some provenance => if inferAlgebraic then match provenance.algebraic? with
                  | some sidecar => some (.algebraic ((Algebraic.Sidecar.ofRational first).add sidecar))
                  | none => none
                else none
              | none => none
      | other, some (.rational second) =>
          if zero : second.value = 0 then other.map fun p =>
            Provenance.transportProvenance p (Add.addRightZero _ _ (Rational.Arithmetic.rationalZero second zero)) else
              match other with
              | some (.quadratic coordinates) =>
                  match Cast.inspectReal second.value with
                  | .real value same => some (.quadratic (coordinates.addScalarRight second value same))
                  | .complex _ => none
              | some provenance => if inferAlgebraic then match provenance.algebraic? with
                  | some sidecar => some (.algebraic (sidecar.add (Algebraic.Sidecar.ofRational second)))
                  | none => none
                else none
              | none => none
      | some first, some second =>
          if inferAlgebraic then match first.algebraic?, second.algebraic? with
          | some leftCache, some rightCache => some (.algebraic (leftCache.add rightCache))
          | _, _ => none
          else none
      | _, _ => none }

set_option backward.match.sparseCases false in
/-- Multiply the original numerical channels and propagate supported rational, zero and unit provenance.

Unsupported combinations retain their actual product channel with no provenance
sidecar. Disabling general algebraic inference preserves the rational, quadratic,
zero and unit rules while deferring compound general-algebraic construction. -/
def mul (left right :
  Annotated) (inferAlgebraic : Bool := true) : Annotated :=
  { channel := CoherentNamed.mul left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.rational first), some (.rational second) => some (.rational (first.mul second))
      | some (.rational first), other =>
          if zero : first.value = 0 then some (.rational (RationalSidecar.zero
            (NamedEquivalent.trans
              (by simpa only [zero, CoherentNamed.mul,
                Coherence.exact] using Mul.mulLeftConstant left.channel right.channel first)
              (Mul.coherentMul_zero_left right.channel))))
          else if one : first.value = 1 then other.map fun p => Provenance.transportProvenance p
            (NamedEquivalent.trans
              (by simpa only [one, CoherentNamed.mul,
                Coherence.exact] using Mul.mulLeftConstant left.channel right.channel first)
              (Mul.coherentMul_one_left right.channel))
          else match other with
            | some (.quadratic coordinates) =>
                match Cast.inspectReal first.value with
                | .real value same => some (.quadratic (coordinates.mulScalarLeft first value same))
                | .complex _ => none
            | some provenance => if inferAlgebraic then match provenance.algebraic? with
                | some sidecar => some (.algebraic ((Algebraic.Sidecar.ofRational first).mul sidecar))
                | none => none
              else none
            | none => none
      | other, some (.rational second) =>
          if zero : second.value = 0 then some (.rational (RationalSidecar.zero
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
          else match other with
            | some (.quadratic coordinates) =>
                match Cast.inspectReal second.value with
                | .real value same => some (.quadratic (coordinates.mulScalarRight second value same))
                | .complex _ => none
            | some provenance => if inferAlgebraic then match provenance.algebraic? with
                | some sidecar => some (.algebraic (sidecar.mul (Algebraic.Sidecar.ofRational second)))
                | none => none
              else none
            | none => none
      | some first, some second =>
          if inferAlgebraic then match first.algebraic?, second.algebraic? with
          | some leftCache, some rightCache => some (.algebraic (leftCache.mul rightCache))
          | _, _ => none
          else none
      | _, _ => none }

/-- The same compiled channel is shared by both occurrences. -/
def cancel (input :
  Annotated) : Annotated :=
  ⟨CoherentNamed.add input.channel
      (CoherentNamed.neg input.channel),
    some (.rational (RationalSidecar.addNeg input.channel))⟩

/-- A retained square equation recovers exact rational provenance for the square, even when no rational reading is
itself an exact root. General algebraic inference can be deferred while the
rational, supplied square and quadratic paths keep their original witnesses. -/
def square (input :
  Annotated) (inferAlgebraic : Bool := true) : Annotated :=
  { channel := CoherentNamed.mul input.channel input.channel
    provenance := match input.provenance with
      | some (.rational reading) => some (.rational (reading.mul reading))
      | some (.squareRoot root) => some (.rational ⟨root.parameter, root.square⟩)
      | some (.quadratic coordinates) => some (.quadratic coordinates.square)
      | some (.polynomialRoot root) => if inferAlgebraic then
          let sidecar := Algebraic.Sidecar.ofRoot root
          some (.algebraic (sidecar.mul sidecar))
        else none
      | some (.algebraic sidecar) => if inferAlgebraic then some (.algebraic (sidecar.mul sidecar)) else none
      | none => none }
end Purelib.Approximation.Gaussian.Acquisition.Annotated

end
