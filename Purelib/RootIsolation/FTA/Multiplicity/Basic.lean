module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
public import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Box-only general-polynomial isolation after squarefree preprocessing

This is the Paper-I general-polynomial layer.  It computes the exact
pairwise-coprime positive multiplicity basis and runs the standalone box
theorem once for every displayed basis factor.  No finite-name or cylinder
module is imported.
-/

namespace Purelib.RootIsolation.FTA.Multiplicity.Basic

set_option genInjectivity false in
/-- One pairwise-coprime squarefree basis factor and its box-only isolation. -/
structure BoxFactor where
  /-- The actual original squarefree multiplicity-basis entry. -/ entry :
    Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry
  /-- The original positive-degree isolation for this exact retained factor. -/ result :
    FTA.Positive.Basic.PositiveResult entry.part.polynomial

constructive_injectivity BoxFactor

namespace BoxFactor

/-- Read the original squarefree factor from the retained multiplicity entry. -/
@[expose] def factor (boxed :
  FTA.Multiplicity.Basic.BoxFactor) : Dense.Gaussian.Squarefree.Decomposition.Basic.Factor := boxed.entry.factor

/-- Read the original factor's retained positive multiplicity. -/
@[expose] def occurrenceCount (boxed :
  FTA.Multiplicity.Basic.BoxFactor) : Nat := boxed.entry.multiplicity

/-- The original boxed factor has strictly positive retained multiplicity. -/
theorem occurrenceCountPositive (boxed :
  FTA.Multiplicity.Basic.BoxFactor) :
    0 < boxed.occurrenceCount :=
  boxed.entry.multiplicityPositive

end BoxFactor

set_option genInjectivity false in
/-- Total box-only result for an arbitrary displayed polynomial. -/
inductive BoxResult (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original polynomial is identically zero. -/ | zero (certificate : p.isZero = true)
  /-- The original polynomial is nonzero and has degree zero. -/ | constant (nonzero : p.isZero = false) (degreeZero :
    p.natDegree = 0)
  /-- The original positive preprocessing retains a nonempty pairwise-coprime list of isolated squarefree basis factors.
  -/
  | positive
      (preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing p)
      (factors : List BoxFactor)
      (factorsNonempty : factors ≠ [])
      (factorsPairwiseCoprime : factors.Pairwise fun left right =>
        Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
          (Dense.Gaussian.Squarefree.Part.Factor.toPart left.factor)
          (Dense.Gaussian.Squarefree.Part.Factor.toPart right.factor))

constructive_injectivity BoxResult

end Purelib.RootIsolation.FTA.Multiplicity.Basic

end
