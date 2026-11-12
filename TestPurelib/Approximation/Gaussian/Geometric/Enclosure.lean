module

import Purelib.System.IO
import Purelib.Approximation.Gaussian.Geometric.Enclosure
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison

namespace TestPurelib.Approximation.Gaussian.Geometric.Enclosure

open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Geometric.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

/-- Every paired prefix retains the exact original named power channel. -/
example (input : CoherentNamed) (source : GeometricApproximation)
    (same : NamedEquivalent input.name source.toApproximation.toNamed) (exponent : Nat) :
    (Comparison.PowerRealization.build input source same exponent).channel = Power.namedPower input exponent :=
  (Comparison.PowerRealization.build input source same exponent).channel_eq

/-- Every paired prefix retains the complete original geometric power program. -/
example (input : CoherentNamed) (source : GeometricApproximation)
    (same : NamedEquivalent input.name source.toApproximation.toNamed) (exponent : Nat) :
    (Comparison.PowerRealization.build input source same exponent).source = source.pow exponent :=
  (Comparison.PowerRealization.build input source same exponent).source_eq

/-- Cached target product comparison consumes the supplied program and its actual pointwise readings. -/
example (first second : CoherentNamed) (left right target : GeometricApproximation)
    (firstEq : NamedEquivalent first.name left.toApproximation.toNamed)
    (secondEq : NamedEquivalent second.name right.toApproximation.toNamed)
    (samples : ∀ index, target.sample index = left.sample index * right.sample index) :
    NamedEquivalent (CoherentNamed.mul first second).name target.toApproximation.toNamed :=
  Comparison.mul_agreesWith first second left right target firstEq secondEq samples

/-- Exact common enclosures contain the original displayed reading at every index. -/
example (value : Canonical) (index : Nat) : (Enclosure.exact value).ball.Contains value := by
  have inside := (Enclosure.exact value).contains index
  rewrite [Enclosure.exact_sample] at inside
  exact inside

/-- Negated common enclosures contain the negative of every original finite reading. -/
example {channel : CoherentNamed} (original : Enclosure channel) (index : Nat) :
    original.neg.ball.Contains (-original.source.sample index) := by
  have inside := original.neg.contains index
  rewrite [Enclosure.neg_sample] at inside
  exact inside

/-- Ordered common sums contain both original readings at their unchanged common index. -/
example {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.add right).ball.Contains (left.source.sample index + right.source.sample index) := by
  have inside := (left.add right).contains index
  rewrite [Enclosure.add_sample] at inside
  exact inside

/-- Ordered common differences retain the original readings at their unchanged common index. -/
example {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.sub right).ball.Contains (left.source.sample index - right.source.sample index) := by
  have inside := (left.sub right).contains index
  rewrite [Enclosure.sub_sample] at inside
  exact inside

/-- Common products contain both original readings at their unchanged common index. -/
example {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second) (index : Nat) :
    (left.mul right).ball.Contains (left.source.sample index * right.source.sample index) := by
  have inside := (left.mul right).contains index
  rewrite [Enclosure.mul_sample] at inside
  exact inside

/-- Every finite natural power contains the power of the same original finite reading. -/
example {channel : CoherentNamed} (original : Enclosure channel) (exponent index : Nat) :
    (original.pow exponent).ball.Contains (original.source.sample index ^ exponent) := by
  have inside := (original.pow exponent).contains index
  rewrite [Enclosure.pow_sample] at inside
  exact inside

/-- Common conjugate enclosures contain conjugates of the same original readings. -/
example {channel : CoherentNamed} (original : Enclosure channel) (index : Nat) :
    original.conj.ball.Contains (original.source.sample index).conj := by
  have inside := original.conj.contains index
  rewrite [Enclosure.conj_sample] at inside
  exact inside

/-- Exact channel transport retains the complete original source and ball records. -/
example {first second : CoherentNamed} (original : Enclosure first) (same : first = second) :
    (original.cast same).source = original.source ∧ (original.cast same).ball = original.ball :=
  ⟨original.cast_source same, original.cast_ball same⟩

/-- Operational channel transport retains the complete original source and ball records. -/
example {first second : CoherentNamed} (original : Enclosure first)
    (equivalent : NamedEquivalent first.name second.name) :
    (original.transport equivalent).source = original.source ∧
      (original.transport equivalent).ball = original.ball :=
  ⟨original.transport_source equivalent, original.transport_ball equivalent⟩

/-- Check original nonreal arithmetic, a zero power and actual original operational comparison payment. -/
public def check : IO Unit := do
  let first : Canonical := ⟨3, 4⟩
  let second : Canonical := ⟨2, -1⟩
  let left := Enclosure.exact first
  let right := Enclosure.exact second
  let sum := left.add right
  let difference := left.sub right
  let product := left.mul right
  let conjugated := left.conj
  let cube := left.pow 3
  let unit := left.pow 0
  let prefixes := Comparison.PowerRealization.build (CoherentNamed.Coherence.exact first)
    left.source left.equivalent 3
  match prefixes with
  | .succ previous _ _ result _ _ =>
      unless result.sample 7 == (⟨-117, 44⟩ : Canonical) &&
          previous.source.sample 7 == (⟨-7, 24⟩ : Canonical) do
        throw (IO.userError "A retained power prefix changed its original observation")
      match previous with
      | .succ initial _ _ _ _ _ =>
          unless initial.source.sample 7 == first do
            throw (IO.userError "A retained first power prefix replaced its original input")
          match initial with
          | .succ zero _ _ _ _ _ =>
              unless zero.source.sample 7 == 1 do
                throw (IO.userError "A retained zero power prefix changed its exact unit")
  unless left.neg.source.sample 7 == (⟨-3, -4⟩ : Canonical) &&
      sum.source.sample 7 == (⟨5, 3⟩ : Canonical) &&
      difference.source.sample 7 == (⟨1, 5⟩ : Canonical) &&
      product.source.sample 7 == (⟨10, 5⟩ : Canonical) &&
      conjugated.source.sample 7 == (⟨3, -4⟩ : Canonical) &&
      cube.source.sample 7 == (⟨-117, 44⟩ : Canonical) && unit.source.sample 7 == 1 do
    throw (IO.userError "An original geometric enclosure arithmetic reading changed")
  unless sum.ball.Contains (sum.source.sample 7) && product.ball.Contains (product.source.sample 7) &&
      cube.ball.Contains (cube.source.sample 7) && unit.ball.radiusSq == 0 do
    throw (IO.userError "An original arithmetic sample left its retained common enclosure")
  let compared := product.equivalent.compare 3 7 (1 / 16 : Rational) (by decide +kernel)
  unless 3 ≤ compared.leftIndex && 7 ≤ compared.rightIndex do
    throw (IO.userError "An original operational comparison changed its two starting indices")
  let unchanged := left.cast rfl
  let transported := left.transport (NamedEquivalent.refl (CoherentNamed.Coherence.exact first).name)
  unless unchanged.ball == left.ball && transported.ball == left.ball &&
      transported.source.sample 7 == left.source.sample 7 do
    throw (IO.userError "Enclosure channel transport failed to retain original cached data")
  Purelib.System.IO.println s!"Original geometric enclosures: comparison {compared.leftIndex}/{compared.rightIndex}"

end TestPurelib.Approximation.Gaussian.Geometric.Enclosure
