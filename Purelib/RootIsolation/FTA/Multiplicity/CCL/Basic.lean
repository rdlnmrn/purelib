module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
public import Purelib.RootIsolation.FTA.Positive.CCL.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

section

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

namespace Purelib.RootIsolation.FTA.Multiplicity.CCL.Basic

set_option genInjectivity false in
/-- One pairwise-coprime squarefree basis factor and its CCL-coupled isolation. -/
structure CCLFactor where
  /-- The original retained squarefree factor. -/ factor : Dense.Gaussian.Squarefree.Decomposition.Basic.Factor
  /-- The retained number of occurrences of this original factor. -/ occurrenceCount : Nat
  /-- The original CCL-coupled positive-degree isolation for this factor. -/ result :
    FTA.Positive.CCL.Basic.PositiveResult factor.polynomial

constructive_injectivity CCLFactor

set_option genInjectivity false in
/-- Total CCL-coupled result for an arbitrary displayed polynomial. -/
inductive CCLResult (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original polynomial is identically zero. -/ | zero (certificate : p.isZero = true)
  /-- The original polynomial is nonzero and has degree zero. -/ | constant (nonzero : p.isZero = false) (degreeZero :
    p.natDegree = 0)
  /-- The original positive preprocessing retains a nonempty pairwise-coprime list of CCL-coupled factor isolations. -/
    | positive
      (preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing p)
      (factors : List FTA.Multiplicity.CCL.Basic.CCLFactor)
      (factorsNonempty : factors ≠ [])
      (factorsPairwiseCoprime : factors.Pairwise fun left right =>
        Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
          (Dense.Gaussian.Squarefree.Part.Factor.toPart left.factor)
          (Dense.Gaussian.Squarefree.Part.Factor.toPart right.factor))

constructive_injectivity CCLResult

end Purelib.RootIsolation.FTA.Multiplicity.CCL.Basic

end

end
