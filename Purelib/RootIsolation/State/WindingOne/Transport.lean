module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.RootIsolation.State.WindingOne.Transport

/-- Reindex a finite winding-one state along exact polynomial and ambient-box
equalities.  All numerical data, including the four full ambient-line
clearances, are retained. -/
def castWindingOneState
    {leftPolynomial rightPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (state : WindingOneState
      leftPolynomial leftAmbient) :
    WindingOneState rightPolynomial rightAmbient := by
  subst rightPolynomial
  subst rightAmbient
  exact state

/-- Reindexing a winding-one state along polynomial and ambient equalities preserves its exact box. -/
@[simp] theorem castWindingOneState_box
    {leftPolynomial rightPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (state : WindingOneState
      leftPolynomial leftAmbient) :
    (castWindingOneState polynomialSame ambientSame state).box = state.box := by
  subst rightPolynomial
  subst rightAmbient
  rfl

end Purelib.RootIsolation.State.WindingOne.Transport

end
