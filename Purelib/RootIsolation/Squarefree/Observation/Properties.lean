module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.Squarefree.Observation.Basic
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.SquarefreeSide (SquarefreeSideInput)

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace Purelib.RootIsolation.Squarefree.Observation.Basic

namespace SquarefreeObservation

/-- Number of distinct squarefree sites represented by one side. -/
def siteCount
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite} :
    Squarefree.Observation.Basic.SquarefreeObservation input → Nat
  | .constant _ => 0
  | .exact _ _ _ => 1
  | .higher boxes _ => boxes.isolation.tracks.length

/-- The retained squarefree observation represents exactly the original polynomial's degree many sites. -/
theorem siteCount_eq_natDegree
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : Squarefree.Observation.Basic.SquarefreeObservation input) :
    observation.siteCount = source.natDegree := by
  cases observation with
  | constant degreeZero => exact degreeZero.symm
  | exact _ degreeOne _ => exact degreeOne.symm
  | higher boxes _ => exact boxes.isolation.tracks_length

/-- Pairwise separation within one squarefree side. -/
def InternallySeparated
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : Squarefree.Observation.Basic.SquarefreeObservation input) : Type :=
  match observation with
  | .constant _ => PUnit
  | .exact _ _ _ => PUnit
  | .higher boxes _ =>
      PLift (∀ left right : Fin source.natDegree, left ≠ right →
        (boxes.isolation.trackAt left).initial.box.Separated
          (boxes.isolation.trackAt right).initial.box)

/-- Read the original observation's internal separation certificate for its retained sites. -/
def internallySeparated
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : Squarefree.Observation.Basic.SquarefreeObservation input) :
    observation.InternallySeparated := by
  cases observation with
  | constant => exact PUnit.unit
  | exact => exact PUnit.unit
  | higher boxes => exact ⟨boxes.isolation.trackAt_pairwiseSeparated⟩

/-- Atomic completeness mirrors the general multiplicity result: constants
have no site, linear factors retain an exact rational evaluation, and every
alternative higher winding-one track receives a deterministic output owner. -/
def AtomicMaximality
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : Squarefree.Observation.Basic.SquarefreeObservation input) : Type :=
  match observation with
  | .constant _ => PUnit
  | .exact root _ _ => PLift (source.eval root.point = 0)
  | .higher boxes _ =>
      ∀ (track : Track.Basic.WindingOneTrack source
          (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox source)),
        track.initial.box.Refines boxes.isolation.support →
          Exact.Ownership.Basic.OwnerSelection boxes.isolation track

/-- Read the original observation's exact-root witness or deterministic higher-track ownership operation. -/
def atomicMaximality
    {source opposite : CoefficientPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : Squarefree.Observation.Basic.SquarefreeObservation input) :
    observation.AtomicMaximality := by
  cases observation with
  | constant => exact PUnit.unit
  | exact root => exact ⟨root.root⟩
  | higher boxes => exact boxes.ownership

end SquarefreeObservation
end Purelib.RootIsolation.Squarefree.Observation.Basic

end
