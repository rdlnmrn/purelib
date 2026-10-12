module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Squarefree.Observation.Properties
public import Purelib.RootIsolation.Squarefree.Observation.Build
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.RootIsolation.Squarefree.Observation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RootIsolation.Squarefree.Observation.Certified

set_option genInjectivity false in
/-- Complete result for one squarefree side, with degree count, internal
separation, and atomic maximality retained as fields. -/
structure SquarefreeSideResult
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite) where
  /-- The exact finite observation of the retained squarefree side. -/ observation :
    Squarefree.Observation.Basic.SquarefreeObservation input
  /-- The observation's site count equals the original source polynomial's degree. -/ siteCount : observation.siteCount
    = source.natDegree
  /-- The sites of this exact retained observation are internally separated. -/ internalSeparation :
    observation.InternallySeparated
  /-- The retained observation satisfies its original atomic maximality contract. -/ atomicMaximality :
    observation.AtomicMaximality

constructive_injectivity SquarefreeSideResult

/-- Compute the original squarefree-side observation with its degree count, separation and atomic maximality
certificates. -/
@[expose] def proveSquarefreeSide
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Coprime.SquarefreeSide.SquarefreeSideInput source opposite) :
    SquarefreeSideResult input :=
  let observation := input.observe
  { observation := observation
    siteCount := observation.siteCount_eq_natDegree
    internalSeparation := observation.internallySeparated
    atomicMaximality := observation.atomicMaximality }
end Purelib.RootIsolation.Squarefree.Observation.Certified

end
