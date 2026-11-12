module
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.FTA.Positive.Build
public import Purelib.RootIsolation.Multiplicity.Observation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data.Rat.Fraction (Rational)

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

/-- Attach an original focused factor observation to its retained positive-degree result.

The exact linear branch derives the opposite polynomial's nonvanishing at
that same displayed root. The higher branch retains the complete supplied
box family and its degree bound without running another root producer.
-/
@[expose] def fromPositive
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries)
    (positive : FTA.Positive.Basic.PositiveResult context.focus.part.polynomial) :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context := by
  cases positive with
  | linear root degree =>
      have alternative := (input.focusOppositeCoprime context).eval_ne_zero root.point
      have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
        rcases alternative with focusNonzero | oppositeNonzero
        · exact (focusNonzero root.root).elim
        · exact oppositeNonzero
      exact .exact root degree oppositeAtRoot
  | higher boxes degree => exact .higher boxes degree

/-- Observe the retained positive multiplicity factor with the original positive-degree box construction.

Return its exact linear root with the opposite polynomial's nonvanishing proof, or its complete higher-degree box
family.
-/
@[expose] def observe
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries) (request : Option Rational := none) :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context :=
  fromPositive input context (FTA.Positive.Build.provePositive
    { squarefree := context.focus.part.squarefree
      degreePositive := context.focus.degreePositive } request)

/-- A retained original positive-degree result gives the same complete focused observation. -/
theorem fromPositive_eq_observe
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries)
    (positive : FTA.Positive.Basic.PositiveResult context.focus.part.polynomial)
    {request : Option Rational}
    (same : positive = FTA.Positive.Build.provePositive
      { squarefree := context.focus.part.squarefree, degreePositive := context.focus.degreePositive } request) :
    fromPositive input context positive = input.observe context request :=
  congrArg (fromPositive input context) same

/-- The absent event request preserves the complete original focused observation. -/
theorem observe_none
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries) :
    input.observe context none = fromPositive input context (FTA.Positive.Build.provePositive
      { squarefree := context.focus.part.squarefree, degreePositive := context.focus.degreePositive }) := rfl

/-- Shared original branches preserve the complete earlier exact or higher observation. -/
theorem observe_eq_original
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries) :
    input.observe context = (by
      let positive := FTA.Positive.Build.provePositive
        { squarefree := context.focus.part.squarefree, degreePositive := context.focus.degreePositive }
      cases positive with
      | linear root degree =>
          have alternative := (input.focusOppositeCoprime context).eval_ne_zero root.point
          have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
            rcases alternative with focusNonzero | oppositeNonzero
            · exact (focusNonzero root.root).elim
            · exact oppositeNonzero
          exact .exact root degree oppositeAtRoot
      | higher boxes degree => exact .higher boxes degree) := rfl

/-- A certified higher focused factor retains its same original input and complete requested box result. -/
theorem observe_higher
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (higher : 2 ≤ context.focus.part.polynomial.natDegree) (request : Option Rational := none) :
    input.observe context request =
      .higher (FTA.Squarefree.Build.BoxFTA.prove ⟨context.focus.part.squarefree, higher⟩ request) higher :=
  congrArg (input.fromPositive context) (FTA.Positive.Build.provePositive_eq_higher
    { squarefree := context.focus.part.squarefree, degreePositive := context.focus.degreePositive } higher request)

namespace FactorObservation

/-- Complete original Newton origins at every higher site of this exact observation.

Exact observations need no track. Each higher site preserves the original
focused factor, its canonical elimination and actual retained track, rather
than merely an equal scalar reading or box.
-/
@[expose] def NewtonOrigins
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries} :
    FactorObservation input context → Prop
  | .exact _ _ _ => True
  | .higher boxes degree =>
      ∀ index : Fin context.focus.part.polynomial.natDegree,
        Track.Newton.Build.Origin degree context.focus.part.squarefree
          (FTA.Squarefree.Input.mk context.focus.part.squarefree degree).elimination
          (boxes.isolation.trackAt index)

end FactorObservation

/-- The actual higher observation constructor retains the original Newton origin at each focused root index. -/
theorem observe_higher_track_origin
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (request : Option Rational) (boxes : FTA.Squarefree.BoxResult context.focus.part.polynomial)
    (degree : 2 ≤ context.focus.part.polynomial.natDegree)
    (same : input.observe context request = .higher boxes degree)
    (index : Fin context.focus.part.polynomial.natDegree) :
    Track.Newton.Build.Origin degree context.focus.part.squarefree
      (FTA.Squarefree.Input.mk context.focus.part.squarefree degree).elimination
      (boxes.isolation.trackAt index) := by
  have produced : input.observe context request = .higher
      (FTA.Squarefree.Build.BoxFTA.prove ⟨context.focus.part.squarefree, degree⟩ request) degree :=
    input.observe_higher context degree request
  have whole := produced.symm.trans same
  have boxesEq : FTA.Squarefree.Build.BoxFTA.prove ⟨context.focus.part.squarefree, degree⟩ request = boxes := by
    cases whole
    rfl
  rewrite [← boxesEq]
  exact FTA.Squarefree.Build.BoxFTA.prove_trackAt_origin ⟨context.focus.part.squarefree, degree⟩ request index

/-- The original focused observation carries exact Newton origins for every actual higher site. -/
theorem observe_newtonOrigins
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (request : Option Rational) : (input.observe context request).NewtonOrigins := by
  cases observed : input.observe context request with
  | exact => exact True.intro
  | higher boxes degree => exact input.observe_higher_track_origin context request boxes degree observed

end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
