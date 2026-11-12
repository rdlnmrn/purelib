module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Interpretation
public import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Provenance.Power

/-! # Algebraic interpretations of the original parameter-variation observations

Both original full-sheet square certificates supply their retained finite
power identities once. Five materialized two-entry banks interpret the
same ten already selected numerical observations on those exact sheets.
Each existing comparison retains the old actual arithmetic reading and
the independent new algebraic reading with its paid finite discrepancy.
No root or numerical coefficient observation is selected again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

open Purelib.Curves.Hyperelliptic.Differentials.OddPower

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation

variable {parameter increment point : Canonical}
variable {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
variable {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
variable {unit : Norm.Basic.normSq increment ≤ 1}
variable {jet : Sampling.SampledJet parameter increment point source target unit}

/-- The two original square identities and five materialized banks of actual arithmetic interpretations.

Every interpretation is indexed by its old numerical observation and the
same cached original source or target square certificate. Its denotation,
new observation and comparison retain their own original owners and requests.
-/
abbrev Interpretations (observations : Observations jet) : Type 2 :=
  (sourceIdentity : PowerIdentity source.value 2 ((Paths.polynomial parameter).eval point)) ×
  (targetIdentity : PowerIdentity target.value 2 ((Paths.polynomial (parameter + increment)).eval point)) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Observation.Reading.Interpretation (observations.sourceValue coordinate).original sourceIdentity) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Observation.Reading.Interpretation (observations.targetValue coordinate).original targetIdentity) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Observation.Reading.Interpretation (observations.sourceFirst coordinate).original sourceIdentity) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Observation.Reading.Interpretation (observations.targetFirst coordinate).original targetIdentity) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Observation.Reading.Interpretation (observations.sourceSecond coordinate).original sourceIdentity)

namespace Interpretations

variable {observations : Observations jet}

/-- Interpret all ten stored numerical observations, sharing the two original square certificates across their rows. -/
def build (observations : Observations jet) : Interpretations observations := by
  let sourceIdentity : PowerIdentity source.value 2 ((Paths.polynomial parameter).eval point) := by
    rewrite [Paths.polynomial_eval]
    exact PowerIdentity.ofSquare source.square
  let targetIdentity : PowerIdentity target.value 2 ((Paths.polynomial (parameter + increment)).eval point) := by
    rewrite [Paths.polynomial_eval]
    exact PowerIdentity.ofSquare target.square
  let sourceValue := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceValue coordinate).original.requestInterpretation sourceIdentity)
  let targetValue := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.targetValue coordinate).original.requestInterpretation targetIdentity)
  let sourceFirst := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceFirst coordinate).original.requestInterpretation sourceIdentity)
  let targetFirst := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.targetFirst coordinate).original.requestInterpretation targetIdentity)
  let sourceSecond := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceSecond coordinate).original.requestInterpretation sourceIdentity)
  exact ⟨sourceIdentity, targetIdentity, sourceValue, targetValue, sourceFirst, targetFirst, sourceSecond⟩

/-- Read the original source-sheet power identity shared by the value and both derivative banks. -/
@[expose] def sourceIdentity (retained : Interpretations observations) :
    PowerIdentity source.value 2 ((Paths.polynomial parameter).eval point) := retained.1

/-- Read the distinct original target-sheet identity shared by its value and first derivative banks. -/
@[expose] def targetIdentity (retained : Interpretations observations) :
    PowerIdentity target.value 2 ((Paths.polynomial (parameter + increment)).eval point) := retained.2.1

/-- Read the retained interpretation bank of the actual original source value observations. -/
@[expose] def sourceValue (retained : Interpretations observations) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Observation.Reading.Interpretation (observations.sourceValue coordinate).original
        retained.sourceIdentity) := retained.2.2.1

/-- Read the independent target value interpretations on the same original fixed spatial point. -/
@[expose] def targetValue (retained : Interpretations observations) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Observation.Reading.Interpretation (observations.targetValue coordinate).original
        retained.targetIdentity) := retained.2.2.2.1

/-- Read the original first derivative interpretations used as the value Taylor slopes. -/
@[expose] def sourceFirst (retained : Interpretations observations) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Observation.Reading.Interpretation (observations.sourceFirst coordinate).original
        retained.sourceIdentity) := retained.2.2.2.2.1

/-- Read the target first derivative interpretations retained by the first variation bank. -/
@[expose] def targetFirst (retained : Interpretations observations) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Observation.Reading.Interpretation (observations.targetFirst coordinate).original
        retained.targetIdentity) := retained.2.2.2.2.2.1

/-- Read the independent original second derivative interpretations used by the first Taylor slopes. -/
@[expose] def sourceSecond (retained : Interpretations observations) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Observation.Reading.Interpretation (observations.sourceSecond coordinate).original
        retained.sourceIdentity) := retained.2.2.2.2.2.2

end Interpretations

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

end
