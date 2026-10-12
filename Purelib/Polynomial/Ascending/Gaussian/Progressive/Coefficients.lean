module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Coefficients

/-- Addition of low-to-high finite coefficient lists, retaining an unmatched
displayed tail exactly as the rational polynomial kernel does. -/
def addCoefficients : List
  Name.Coherent.CoherentNamed → List Name.Coherent.CoherentNamed →
    List Name.Coherent.CoherentNamed
  | [], right => right
  | left, [] => left
  | left :: leftTail, right :: rightTail =>
      CoherentNamed.add left right ::
        addCoefficients leftTail rightTail

/-- Multiply every displayed coefficient by one coherent scalar. -/
def scaleCoefficients (factor :
  Name.Coherent.CoherentNamed) (coefficients : List Name.Coherent.CoherentNamed) :
    List Name.Coherent.CoherentNamed :=
  coefficients.map (CoherentNamed.mul factor)

section
open Purelib.Polynomial
/-- Finite Cauchy multiplication of coherent coefficient channels. -/
def mulCoefficients : List
  Name.Coherent.CoherentNamed → List Name.Coherent.CoherentNamed →
    List Name.Coherent.CoherentNamed
  | [], _ => []
  | left :: leftTail, right =>
      addCoefficients
        (scaleCoefficients left right)
        (CoherentNamed.Coherence.exact 0 ::
          mulCoefficients leftTail right)

/-- Finite Horner composition of coherent coefficient tables. -/
def composeCoefficients : List
  Name.Coherent.CoherentNamed → List Name.Coherent.CoherentNamed →
    List Name.Coherent.CoherentNamed
  | [], _ => []
  | coefficient :: remaining, inner =>
      addCoefficients [coefficient]
        (mulCoefficients inner
          (composeCoefficients remaining inner))

end

/-- Represent the natural degree as an exact real-axis Gaussian coefficient channel. -/
def naturalChannel (degree : Nat) :
  Name.Coherent.CoherentNamed :=
  CoherentNamed.Coherence.exact ⟨(degree : Fraction.Rational), 0⟩

open Purelib.Polynomial in
/-- Formal differentiation of a finite coherent coefficient table. -/
def derivativeFrom : Nat → List
  Name.Coherent.CoherentNamed → List Name.Coherent.CoherentNamed
  | _, [] => []
  | degree, coefficient :: remaining =>
      CoherentNamed.mul
        (naturalChannel degree)
        coefficient ::
        derivativeFrom (degree + 1) remaining

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Coefficients

end
