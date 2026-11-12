module

public import Purelib.Polynomial.Multivariate.Gaussian.PowerCoordinates.Real
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Rational
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Arithmetic.Add
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Degree-two power coordinates in the original pair ring

The general bounded-power cache specializes to degree two. Its actual rational
coefficients determine the original pair's constant and generator coordinates,
with operational agreement at the same selected original channel. This
readback neither supplies nonsquareness nor identifies independent generators.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Terms

/-- Read one bounded degree-two power coefficient as the original pair's scalar or generator coordinate. -/
@[expose] def pairEntry (parameter coefficient : Rational) (exponent : Fin 2) : Pair Rational parameter :=
  Fin.cases (Pair.scalar coefficient)
    (fun tail => Fin.cases (⟨0, coefficient⟩ : Pair Rational parameter) (fun impossible => Fin.elim0 impossible) tail)
    exponent

/-- One original bounded power compares to its coordinate in the original pair ring. -/
def denote_pairEntry (generator : CoherentNamed) (parameter coefficient : Rational) (exponent : Fin 2) :
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate coefficient))
        (Power.namedPower generator exponent.val)).name
      (Pair.Gaussian.denoteRational generator (pairEntry parameter coefficient exponent)).name := by
  refine Fin.cases ?_ (fun tail => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) tail) exponent
  · exact NamedEquivalent.trans
      (Mul.coherentMul_one_right (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate coefficient)))
      (NamedEquivalent.symm (Pair.Gaussian.denoteRational_scalar generator coefficient))
  · let linear := CoherentNamed.mul (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate coefficient)) generator
    exact NamedEquivalent.trans
      (Product.Congruence.coherentMul_respects (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate coefficient))
        (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate coefficient)) (Power.namedPower generator 1) generator
        (NamedEquivalent.refl _) (Power.namedPower_one generator))
      (NamedEquivalent.symm (Add.coherentAdd_zero_left linear))

/-- Collect the actual bounded power coefficients using the original pair addition operation. -/
@[expose] def pairPowers (parameter : Rational) : List (Fin 2 × Rational) → Pair Rational parameter
  | [] => 0
  | first :: remaining => pairEntry parameter first.2 first.1 + pairPowers parameter remaining

/-- The retained ordered rational powers compare to their collected coordinates at the same original generator. -/
def denote_pairPowers (generator : CoherentNamed) (parameter : Rational) : (entries : List (Fin 2 × Rational)) →
    NamedEquivalent
      (denotePowers generator (entries.map (fun entry => (entry.1, Cast.CoordinateTaylor.ofCoordinate entry.2)))).name
      (Pair.Gaussian.denoteRational generator (pairPowers parameter entries)).name
  | [] => NamedEquivalent.symm
      (Pair.Gaussian.denote_zero Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero generator)
  | first :: remaining => by
      let originalHead := CoherentNamed.mul (Coherence.exact (Cast.CoordinateTaylor.ofCoordinate first.2))
        (Power.namedPower generator first.1.val)
      let pairedHead := Pair.Gaussian.denoteRational generator (pairEntry parameter first.2 first.1)
      let originalTail :=
        denotePowers generator (remaining.map (fun entry => (entry.1, Cast.CoordinateTaylor.ofCoordinate entry.2)))
      let pairedTail := Pair.Gaussian.denoteRational generator (pairPowers parameter remaining)
      have headComparison : NamedEquivalent originalHead.name pairedHead.name :=
        denote_pairEntry generator parameter first.2 first.1
      have tailComparison : NamedEquivalent originalTail.name pairedTail.name :=
        denote_pairPowers generator parameter remaining
      exact NamedEquivalent.trans
        (Sum.Congruence.coherentAdd_respects originalHead pairedHead originalTail pairedTail
          headComparison tailComparison)
        (Pair.Gaussian.denoteRational_add generator
          (pairEntry parameter first.2 first.1) (pairPowers parameter remaining))

end Terms

namespace Sparse.PowerCoordinates.RationalCoordinates

/-- Read a cached degree-two rational coordinate list as the original pair with the supplied parameter. -/
@[expose] def toPair {arity : Nat} {polynomial : Sparse Basic.Canonical arity} {index : Fin arity}
    {coordinates : PowerCoordinates polynomial index 2} (rational : RationalCoordinates coordinates)
    (parameter : Rational) : Pair Rational parameter := Terms.pairPowers parameter rational.entries

/-- Original polynomial interpretation agrees with the same cached degree-two pair coordinates. -/
def equivalentPair {arity : Nat} {polynomial : Sparse Basic.Canonical arity} {index : Fin arity}
    {coordinates : PowerCoordinates polynomial index 2} (rational : RationalCoordinates coordinates)
    (parameter : Rational) (environment : Fin arity → CoherentNamed) :
    NamedEquivalent (polynomial.denote environment).name
      (Pair.Gaussian.denoteRational (environment index) (rational.toPair parameter)).name :=
  NamedEquivalent.trans (rational.equivalent environment)
    (Terms.denote_pairPowers (environment index) parameter rational.entries)

end Sparse.PowerCoordinates.RationalCoordinates

namespace Gaussian.Normalized

set_option genInjectivity false in
/-- A cached pair interpretation or all formal power/coefficient conditions preventing that readback. -/
inductive PairOutcome {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (generator : CoherentNamed)
    (index : Fin arity) (parameter : Rational) where
  /-- Retain the two actual coordinate caches, computed pair, normal channel and original-channel comparison. -/
  | pair (powers : Sparse.PowerCoordinates normalized.form index 2)
      (rational : Sparse.PowerCoordinates.RationalCoordinates powers)
      (value : Pair Rational (-parameter)) (value_eq : value = rational.toPair (-parameter))
      (channel : CoherentNamed) (channel_eq : channel = Pair.Gaussian.denoteRational generator value)
      (equivalent : NamedEquivalent original.name channel.name)
  /-- Retain every original term inspection and prove that the requested degree-two support is incomplete. -/
  | powers (view : Terms.PowerView index 2 normalized.form.terms) (incomplete : ¬ view.Complete)
  /-- Retain the original power cache and every exact coefficient inspection that prevents a real readback. -/
  | coefficients (powers : Sparse.PowerCoordinates normalized.form index 2)
      (view : Cast.RealListView powers.entries) (incomplete : ¬ view.Complete)

constructive_injectivity PairOutcome

set_option genInjectivity false in
/-- A pair inspection retaining its actual source normalization, requested index, original generator and parameter. -/
structure PairCheck {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Gaussian.Normalized bindings original)
    (requestedIndex : Fin arity) (requestedParameter : Rational) where
  /-- The same actual cached source normalization used by the procedure. -/
  source : Gaussian.Normalized bindings original
  /-- The retained source is the entire original input normalization. -/
  source_eq : source = normalized
  /-- The actual selected original variable position. -/
  index : Fin arity
  /-- The retained position is the requested original index. -/
  index_eq : index = requestedIndex
  /-- The original coherent generator read at this actual source index. -/
  generator : CoherentNamed
  /-- The retained generator is exactly the selected original binding channel. -/
  generator_eq : generator = bindings index
  /-- The retained rational square parameter used for the original pair's negative parameter convention. -/
  parameter : Rational
  /-- The parameter is the one supplied by the caller. -/
  parameter_eq : parameter = requestedParameter
  /-- The cached successful pair or all unresolved conditions at these same retained inputs. -/
  outcome : PairOutcome source generator index parameter

constructive_injectivity PairCheck

/-- Transport the retained outcome to its original source, requested index, generator and parameter. -/
def PairCheck.result {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {normalized : Gaussian.Normalized bindings original} {index : Fin arity} {parameter : Rational}
    (check : PairCheck normalized index parameter) : PairOutcome normalized (bindings index) index parameter := by
  rcases check with ⟨source, source_eq, actualIndex, index_eq, generator, generator_eq,
    actualParameter, parameter_eq, outcome⟩
  cases source_eq
  cases index_eq
  cases generator_eq
  cases parameter_eq
  exact outcome

/-- Read the actual cached pair value, leaving both kinds of unresolved inspection without a pair reading. -/
@[expose] def PairCheck.value? {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    {normalized : Gaussian.Normalized bindings original} {index : Fin arity} {parameter : Rational}
    (check : PairCheck normalized index parameter) : Option (Pair Rational (-check.parameter)) :=
  match check.outcome with
  | .pair _ _ value _ _ _ _ => some value
  | .powers _ _ => none
  | .coefficients _ _ _ => none

/-- Read just the formal coefficient result of the same two retained inspection procedures. -/
@[expose] def pairValue {arity : Nat} (polynomial : Sparse Basic.Canonical arity)
    (index : Fin arity) (parameter : Rational) : Option (Pair Rational (-parameter)) :=
  match (polynomial.inspectPowers index 2).outcome with
  | .unresolved _ _ => none
  | .coordinates powers =>
      match powers.inspectReal with
      | .unresolved _ _ => none
      | .real rational => some (rational.toPair (-parameter))

/-- Inspect cached degree-two support and exact real coefficients without rerunning the source normalizer. -/
@[expose] def inspectPair {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (parameter : Rational) :
    PairCheck normalized index parameter :=
  let generator := bindings index
  let powerCheck := normalized.form.inspectPowers index 2
  let outcome := match powerCheck.outcome with
    | .unresolved view incomplete => PairOutcome.powers view incomplete
    | .coordinates powers =>
        match powers.inspectReal with
        | .unresolved view incomplete => PairOutcome.coefficients powers view incomplete
        | .real rational =>
            let value := rational.toPair (-parameter)
            let channel := Pair.Gaussian.denoteRational generator value
            let equivalent := NamedEquivalent.trans normalized.toForm (rational.equivalentPair (-parameter) bindings)
            PairOutcome.pair powers rational value rfl channel rfl equivalent
  ⟨normalized, rfl, index, rfl, generator, rfl, parameter, rfl, outcome⟩

/-- The pair-value projection consumes the same retained coefficient inspections.

The readback keeps numerical comparison certificates opaque. -/
theorem inspectPair_value {arity : Nat} {bindings : Fin arity → CoherentNamed} {original : CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (parameter : Rational) :
    (normalized.inspectPair index parameter).value? = pairValue normalized.form index parameter := by
  unfold inspectPair PairCheck.value? pairValue
  dsimp only
  cases selected : (normalized.form.inspectPowers index 2).outcome with
  | unresolved view incomplete =>
      rfl
  | coordinates powers =>
      dsimp only
      cases realSelected : powers.inspectReal with
      | unresolved view incomplete =>
          rfl
      | real rational =>
          rfl

end Gaussian.Normalized

end Purelib.Polynomial.Multivariate

end
