module

import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Sidecar
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
import Purelib.Riemann.RootContinuation.SquareRootSidecar

/-!
# Unique coordinates and cached actual reciprocals at an admitted realization

The finite nonsquareness certificate for two realizes the original pair ring
at either supplied root sheet. Operational agreement identifies the original
coordinates, and the inverse package retains the entire original cached input
while comparing its actual numerical reciprocal with the interpreted inverse.
-/

namespace TestPurelib.Algebra.QuadraticPairRealization

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Division.Prepared
open Purelib.Riemann.RootContinuation

/-- Realize the original parameter-minus-two pair ring at an actual supplied generator equation. -/
private def realized (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) : Realization Rational :=
  Realization.rational 2 generator identity (Square.inspect 2) (by decide +kernel)

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    let sidecar := ((realized generator identity).retain (Pair.scalar 3)).sidecar
    (sidecar.scalarReading rfl).value = Cast.CoordinateTaylor.ofCoordinate 3 :=
  let sidecar := ((realized generator identity).retain (Pair.scalar 3)).sidecar
  sidecar.scalarReading_value rfl

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) :
    let sidecar := ((realized generator identity).retain value).sidecar
    (sidecar.compare sidecar).outcome = .equal rfl (sidecar.equivalent_of_coordinates sidecar rfl) :=
  let sidecar := ((realized generator identity).retain value).sidecar
  sidecar.compare_equal sidecar rfl

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    let first := ((realized generator identity).retain (⟨1, 1⟩ : Pair Rational (-2))).sidecar
    let second := ((realized generator identity).retain (⟨3, 2⟩ : Pair Rational (-2))).sidecar
    ∃ different : first.value ≠ second.value,
      (first.compare second).outcome =
        .unequal different (fun equivalent => different (first.coordinates_eq second equivalent)) := by
  dsimp only
  let first := ((realized generator identity).retain (⟨1, 1⟩ : Pair Rational (-2))).sidecar
  let second := ((realized generator identity).retain (⟨3, 2⟩ : Pair Rational (-2))).sidecar
  have different : first.value ≠ second.value := by
    change (⟨1, 1⟩ : Pair Rational (-2)) ≠ ⟨3, 2⟩
    decide +kernel
  exact ⟨different, first.compare_unequal second different⟩

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (first second : CoherentNamed)
    (left : Realization.Sidecar (realized generator identity) first)
    (right : Realization.Sidecar (realized generator identity) second) :
    Nonempty (NamedEquivalent first.name second.name) ↔ left.value = right.value := left.agreement_iff right

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (left right : Pair Rational (-2))
    (equivalent : NamedEquivalent ((realized generator identity).denote left).name
      ((realized generator identity).denote right).name) : left = right :=
  (realized generator identity).coordinates_eq left right equivalent

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) :
    let retained := (realized generator identity).retain value
    (Zero.IsZero retained.channel ↔ ¬ Equivalence.IsPrepared retained.channel) ∧
      (Equivalence.IsPrepared retained.channel ↔ ¬ Zero.IsZero retained.channel) :=
  let retained := (realized generator identity).retain value
  ⟨retained.decide.zero_iff_unpreparable, retained.decide.prepared_iff_nonzero⟩

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let retained := (realized generator identity).retain value
    let inverse := retained.inverse nonzero
    inverse.source = retained :=
  let retained := (realized generator identity).retain value
  (retained.inverse nonzero).source_eq

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let retained := (realized generator identity).retain value
    let inverse := retained.inverse nonzero
    NamedEquivalent inverse.output.name inverse.interpreted.name :=
  let retained := (realized generator identity).retain value
  (retained.inverse nonzero).equivalent

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) :
    let retained := (realized generator identity).retain value
    retained.sidecar.retained = retained := rfl

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) (original : CoherentNamed)
    (equivalent : NamedEquivalent original.name ((realized generator identity).denote value).name) :
    let retained := (realized generator identity).retain value
    let sidecar := retained.sidecar.transport equivalent
    sidecar.source = original :=
  let retained := (realized generator identity).retain value
  (retained.sidecar.transport equivalent).source_eq

/-- Either actual supplied root sheet retains the same coefficient uniqueness theorem. -/
private theorem uniqueFromSidecar (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = Cast.CoordinateTaylor.ofCoordinate 2) (left right : Pair Rational (-2)) :
    let identity := parameter_eq ▸ PowerIdentity.ofSquare sidecar.square
    NamedEquivalent ((realized generator identity).denote left).name
      ((realized generator identity).denote right).name → left = right :=
  let identity := parameter_eq ▸ PowerIdentity.ofSquare sidecar.square
  fun equivalent => (realized generator identity).coordinates_eq left right equivalent

example (sheet : Fin 2) (left right : Pair Rational (-2)) :
    let root := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    let identity := SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet ▸
      PowerIdentity.ofSquare root.2.square
    NamedEquivalent ((realized root.1 identity).denote left).name
      ((realized root.1 identity).denote right).name → left = right :=
  let root := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
  uniqueFromSidecar root.1 root.2 (SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet)
    left right

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    let realization := realized generator identity
    let left := (realization.retain (⟨1, 1⟩ : Pair Rational (-2))).sidecar
    let right := (realization.retain (⟨-1, 1⟩ : Pair Rational (-2))).sidecar
    (left.mul right).value = ⟨1, 0⟩ := by
  dsimp only
  rewrite [Realization.Sidecar.mul_value]
  change (⟨1, 1⟩ : Pair Rational (-2)) * ⟨-1, 1⟩ = ⟨1, 0⟩
  decide +kernel

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    ¬ Nonempty (NamedEquivalent
      ((realized generator identity).denote (⟨1, 0⟩ : Pair Rational (-2))).name
      ((realized generator identity).denote (⟨0, 1⟩ : Pair Rational (-2))).name) := by
  rintro ⟨equivalent⟩
  have equal := (realized generator identity).coordinates_eq _ _ equivalent
  have impossible : (1 : Rational) = 0 := congrArg Pair.re equal
  exact (by decide : (1 : Rational) ≠ 0) impossible

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2))
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let sidecar := ((realized generator identity).retain value).sidecar
    let reciprocal := sidecar.reciprocal nonzero
    reciprocal.output = reciprocal.prepared.quotient (Coherence.exact 1) :=
  let sidecar := ((realized generator identity).retain value).sidecar
  (sidecar.reciprocal nonzero).numerical_eq

end TestPurelib.Algebra.QuadraticPairRealization
