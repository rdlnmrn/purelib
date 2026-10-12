module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Integration

section
@[expose] public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic

/-! ## Precisely indexed productive composition -/

set_option genInjectivity false in
/-- Lightweight dependent carrier for three preparation types. Keeping this carrier independent of fractional process
expressions prevents generated structure recursors from unfolding the complete action tree. -/
structure
  CompositionPreparationPayload
  (innerType : Type 1)
    (outerType : innerType -> Type 1) (combinedType : Type 1) where
  /-- The retained inner-action preparation. -/ inner : innerType
  /-- The retained outer-action preparation indexed by the exact inner preparation. -/ outer : outerType inner
  /-- The retained preparation for the combined action. -/ combined : combinedType

constructive_injectivity CompositionPreparationPayload

/-- Exact evidence needed to compare one combined quotient with the nested right-then-left productive action. None of
the three process indices is silently transported across operational equivalence. -/
def CompositionPreparation (left right
  : LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : Coherent.CoherentNamed) : Type 1 :=
  Approximation.Gaussian.FractionalAction.Integral.Composition.Basic.CompositionPreparationPayload
    (Division.Prepared.DenominatorPreparation (LegendreModularMonodromy.fractionalDenominator right tau))
    (fun inner => Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator left (LegendreModularMonodromy.fractionalLinear right tau inner)))
    (Division.Prepared.DenominatorPreparation
      (LegendreModularMonodromy.fractionalDenominator
        (Multiplication.mul left right) tau))

section CompositionPreparation

/-- Compute the right-hand fractional action using its retained inner denominator preparation. -/
def CompositionPreparation.innerOutput
  {left right : LinearAlgebra.Matrix.Basic.IntegralMatrix} {tau : Coherent.CoherentNamed}
    (preparation : Approximation.Gaussian.FractionalAction.Integral.Composition.Basic.CompositionPreparation left right
      tau) : Coherent.CoherentNamed :=
  LegendreModularMonodromy.fractionalLinear right tau preparation.inner

/-- Compute the left action on the exact prepared inner output using the retained dependent outer preparation. -/
def
  CompositionPreparation.nestedOutput
  {left right : LinearAlgebra.Matrix.Basic.IntegralMatrix} {tau : Coherent.CoherentNamed}
    (preparation : Approximation.Gaussian.FractionalAction.Integral.Composition.Basic.CompositionPreparation left right
      tau) : Coherent.CoherentNamed :=
  LegendreModularMonodromy.fractionalLinear left preparation.innerOutput preparation.outer

/-- Compute the combined matrix action using its retained combined denominator preparation. -/
def
  CompositionPreparation.combinedOutput
  {left right : LinearAlgebra.Matrix.Basic.IntegralMatrix} {tau : Coherent.CoherentNamed}
    (preparation : Approximation.Gaussian.FractionalAction.Integral.Composition.Basic.CompositionPreparation left right
      tau) : Coherent.CoherentNamed :=
  LegendreModularMonodromy.fractionalLinear (Multiplication.mul left right) tau
    preparation.combined

end CompositionPreparation
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic

end
