module

import Purelib.Approximation.Gaussian.Provenance.Power.Factorization
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Admission
meta import Purelib.Approximation.Gaussian.Provenance.Power.Factorization
meta import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
meta import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Admission
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Data.Rat.Fraction

/-!
# Finite sign selection at original split power equations

The same certificate selects exact readings at positive and negative exact
sources, and at both original isolated sheets of the rational-square
parameter four. Its returned observation retains both original summands and
the selected actual preparation.
-/

namespace TestPurelib.Approximation.Gaussian.PowerFactorization

open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Approximation.Gaussian.Provenance.Power
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation

example {generator : CoherentNamed} (candidate : Canonical) (nonzero : candidate ≠ 0)
    (identity : PowerIdentity generator 2 (candidate * candidate)) :
    let result := identity.rationalSquare candidate nonzero
    (result.2.val.value = candidate ∨ result.2.val.value = -candidate) ∧
      Nonempty (NamedEquivalent generator.name (Coherence.exact result.2.val.value).name) :=
  let result := identity.rationalSquare candidate nonzero
  ⟨result.2.property, ⟨result.2.val.equivalent⟩⟩

/-- Check the actual selected reading at an original exact signed source. -/
private meta def checkExact (value expected : Canonical)
    (equation : value * value = (2 : Canonical) * 2) : IO Unit := do
  have identity : PowerIdentity (Coherence.exact value) 2 ((2 : Canonical) * 2) := by
    have square := Exact.Arithmetic.exact_mul value value
    rewrite [equation] at square
    exact PowerIdentity.ofSquare square
  let result := identity.rationalSquare 2 (by decide +kernel)
  unless result.2.val.value = expected do
    throw (IO.userError "split power factorization selected the wrong original exact sign")
  unless result.1.observation.value = 4 ∧ result.1.observation.norm = 16 do
    throw (IO.userError "sign selection lost its actual comparison point or norm")
  unless result.1.observation.firstSource.nextIndex = result.1.observation.index + 1 ∧
      result.1.observation.secondSource.nextIndex = result.1.observation.index + 1 do
    throw (IO.userError "sign selection did not retain both original finite sampling states")

/-- Check both actual isolated owners and retain their distinct signed rational readings. -/
private meta def checkIsolated : IO Unit := do
  let mut values : List Canonical := []
  for sheet in ([0, 1] : List (Fin 2)) do
    let retained := SquareRootSidecar.isolated 4 sheet
    let checked := Realization.inspectRoot retained.2
    let certificate := checked.outcome.inspectRational
    match checked.outcome.rationalReading? certificate with
    | some reading => values := reading.value :: values
    | none => throw (IO.userError "the retained rational-square admission supplied no exact reading")
  unless values = [2, -2] ∨ values = [-2, 2] do
    throw (IO.userError "split power factorization did not distinguish the two original isolated sheets")

#eval checkExact 2 2 (by decide +kernel)
#eval checkExact (-2) (-2) (by decide +kernel)
#eval checkIsolated

end TestPurelib.Approximation.Gaussian.PowerFactorization
