module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Comparison
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Admitted realizations of the original quadratic pair ring

A realization retains its actual scalar parameter, exact injective coefficient
map, original coherent generator and defining operational equation. Exclusion
of scalar roots of the negative parameter makes coordinate equality complete
and computes finite preparation for every nonzero original pair.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Gaussian

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Division

set_option genInjectivity false in
/-- An admitted operational realization of the original pair ring over an explicit scalar field. -/
structure Realization (K : Type) [ExplicitField K] where
  /-- The actual original pair square parameter. -/
  parameter : K
  /-- The exact Gaussian coefficient map. -/
  coefficient : K → Canonical
  /-- The map preserves the original zero coefficient. -/
  zero_eq : coefficient 0 = 0
  /-- The map preserves the original unit coefficient. -/
  one_eq : coefficient 1 = 1
  /-- The exact map identifies original scalars only when they are equal. -/
  injective : Function.Injective coefficient
  /-- The exact map preserves original scalar addition. -/
  add_eq : ∀ first second, coefficient (first + second) = coefficient first + coefficient second
  /-- The exact map preserves original scalar multiplication. -/
  mul_eq : ∀ first second, coefficient (first * second) = coefficient first * coefficient second
  /-- The exact map preserves original scalar subtraction. -/
  sub_eq : ∀ first second, coefficient (first - second) = coefficient first - coefficient second
  /-- The actual original coherent generator. -/
  generator : CoherentNamed
  /-- The degree-two invocation of the retained generator's operational power equation. -/
  identity : PowerIdentity generator 2 (-coefficient parameter)
  /-- Every scalar square differs from the negative original parameter. -/
  nonsquare : ∀ candidate : K, candidate * candidate ≠ -parameter

constructive_injectivity Realization

namespace Realization

variable {K : Type} [ExplicitField K] [DecidableEq K]

/-- Interpret an original pair using this same retained coefficient map and generator. -/
@[expose] def denote (realization : Realization K) (value : Pair K realization.parameter) : CoherentNamed :=
  Gaussian.denote realization.coefficient realization.generator value

/-- Operational agreement at this admitted realization identifies the original pair coordinates. -/
theorem coordinates_eq (realization : Realization K) (left right : Pair K realization.parameter)
    (equivalent : NamedEquivalent (realization.denote left).name (realization.denote right).name) : left = right :=
  denote_injective realization.coefficient realization.zero_eq realization.injective realization.add_eq
    realization.mul_eq realization.sub_eq realization.generator realization.identity realization.nonsquare left right
    equivalent

/-- Every nonzero original pair has nonzero scalar norm at the same admitted parameter. -/
theorem norm_ne_zero (realization : Realization K) {value : Pair K realization.parameter} (nonzero : value ≠ 0) :
    value.norm ≠ 0 := value.norm_ne_zero realization.nonsquare nonzero

/-- Every nonzero original pair has nonzero exact mapped norm. -/
theorem mapped_norm_ne_zero (realization : Realization K) {value : Pair K realization.parameter}
    (nonzero : value ≠ 0) : realization.coefficient value.norm ≠ 0 := by
  intro zero
  exact realization.norm_ne_zero nonzero (realization.injective (zero.trans realization.zero_eq.symm))

set_option genInjectivity false in
/-- A cached pair interpretation retaining the entire original realization, coordinates and numerical channel. -/
structure Denotation (realization : Realization K) (original : Pair K realization.parameter) where
  /-- The entire original realization as executable data. -/
  owner : Realization K
  /-- The retained realization is the original mathematical owner. -/
  owner_eq : owner = realization
  /-- The entire original pair in the original nominal pair ring. -/
  value : Pair K realization.parameter
  /-- The cached coordinates are the original input pair. -/
  value_eq : value = original
  /-- The actual cached interpreted coherent channel. -/
  channel : CoherentNamed
  /-- The cached channel interprets this exact original pair and realization. -/
  channel_eq : channel = realization.denote value

constructive_injectivity Denotation

/-- Cache one original pair interpretation without changing the realization or pair owner. -/
@[expose] def retain (realization : Realization K) (value : Pair K realization.parameter) :
    Denotation realization value :=
  ⟨realization, rfl, value, rfl, realization.denote value, rfl⟩

/-- Compute finite factor observations at the exact cached channel of a nonzero retained pair. -/
@[noinline, nospecialize] def Denotation.observe {realization : Realization K}
    {original : Pair K realization.parameter} (retained : Denotation realization original)
    (nonzero : retained.value ≠ 0) :
    Prepared.Factor.Observation retained.channel (realization.denote retained.value.conjugate)
      (realization.coefficient retained.value.norm) := by
  have identity : NamedEquivalent
      (CoherentNamed.mul retained.channel (realization.denote retained.value.conjugate)).name
      (Coherence.exact (realization.coefficient retained.value.norm)).name := by
    rewrite [retained.channel_eq]
    exact denote_norm realization.coefficient realization.zero_eq realization.add_eq realization.mul_eq
      realization.sub_eq realization.generator realization.identity retained.value
  exact Prepared.Factor.observe retained.channel (realization.denote retained.value.conjugate)
    (realization.coefficient retained.value.norm) (realization.mapped_norm_ne_zero nonzero) identity

/-- Decide exact zero or finite preparation while consuming the actual cached pair channel. -/
@[noinline, nospecialize] def Denotation.decide {realization : Realization K}
    {original : Pair K realization.parameter} (retained : Denotation realization original) :
    Prepared.Decision retained.channel :=
  if zero : retained.value = 0 then .excluded (by
      rewrite [retained.channel_eq, zero]
      exact denote_zero realization.coefficient realization.zero_eq realization.generator)
  else .prepared (retained.observe zero).prepare

set_option genInjectivity false in
/-- Cached inverse coordinates and actual numerical division at an original retained nonzero pair channel. -/
structure Inverse {realization : Realization K} {original : Pair K realization.parameter}
    (retained : Denotation realization original) where
  /-- The entire original retained input as executable data. -/
  source : Denotation realization original
  /-- The input is the original cached denotation. -/
  source_eq : source = retained
  /-- The cached original pair's explicit inverse coordinates. -/
  value : Pair K realization.parameter
  /-- The inverse coordinates use the original nominal pair operation. -/
  value_eq : value = retained.value.inverse
  /-- The actual cached interpretation of these inverse coordinates. -/
  interpreted : CoherentNamed
  /-- The interpretation uses this same original realization and cached inverse. -/
  interpreted_eq : interpreted = realization.denote value
  /-- The cached norm-factor observation at the exact retained original input channel. -/
  observation : Prepared.Factor.Observation retained.channel (realization.denote retained.value.conjugate)
    (realization.coefficient retained.value.norm)
  /-- The actual cached denominator preparation. -/
  prepared : Prepared retained.channel
  /-- The denominator preparation consumes this same retained factor observation. -/
  prepared_eq : prepared = observation.prepare
  /-- The actual cached coherent reciprocal program. -/
  output : CoherentNamed
  /-- The reciprocal uses the exact cached prepared denominator. -/
  output_eq : output = prepared.quotient (Coherence.exact 1)
  /-- The actual numerical reciprocal agrees with the same cached interpreted inverse. -/
  equivalent : NamedEquivalent output.name interpreted.name

constructive_injectivity Inverse

/-- Cache explicit inverse coordinates, finite factor preparation and actual division at the retained input channel. -/
@[noinline, nospecialize] def Denotation.inverse {realization : Realization K}
    {original : Pair K realization.parameter} (retained : Denotation realization original)
    (nonzero : retained.value ≠ 0) : Inverse retained := by
  let value := retained.value.inverse
  let interpreted := realization.denote value
  let observation := retained.observe nonzero
  let prepared := observation.prepare
  let output := prepared.quotient (Coherence.exact 1)
  have product : NamedEquivalent (CoherentNamed.mul retained.channel interpreted).name (Coherence.exact 1).name := by
    rewrite [retained.channel_eq]
    exact denote_inverse realization.coefficient realization.zero_eq realization.one_eq realization.add_eq
      realization.mul_eq realization.sub_eq realization.generator realization.identity retained.value
      (realization.norm_ne_zero nonzero)
  exact
    { source := retained
      source_eq := rfl
      value := value
      value_eq := rfl
      interpreted := interpreted
      interpreted_eq := rfl
      observation := observation
      prepared := prepared
      prepared_eq := rfl
      output := output
      output_eq := rfl
      equivalent := prepared.reciprocal_equivalent_of_product interpreted product }

end Realization

end Purelib.Algebra.Quadratic.Pair.Gaussian

end
