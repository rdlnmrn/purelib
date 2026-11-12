module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction.Polynomial
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Power
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal
public import Purelib.Approximation.Gaussian.Equivalence.Zero
public import Purelib.Approximation.Gaussian.Division.Prepared.Product
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compilation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Evaluation
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Polynomial.Multivariate.Gaussian.Inverse
import Purelib.Data.Vector.Dependent
import Init.Core
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact checked constructions and retained Sidecar materialization

The actual numerical channels and original child tree are retained independently
of generic eliminants. A selected-generator reciprocal consumes the original
coordinate, Euclidean, unit-product and numerical preparation caches. Named
materialization returns the original Completed with its actual stored Sidecar
and an equation binding that output to the retained construction.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Data.Vector (DependentVector)

variable {arity : Nat}

namespace Construction

/-- One original power inspection retained only when its actual child Sidecar already exists. -/
abbrev PowerCache (channel : CoherentNamed) (exponent : Nat) :=
  (sidecar : Algebraic.Sidecar channel) ×
    {reading : Option (PowerReading sidecar exponent) // reading = PowerReading.inspect sidecar exponent}

/-- Materialize a displayed power through its actual already retained inspection. -/
@[expose] def powerSidecar {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (exponent : Nat)
    (reading : Option (PowerReading sidecar exponent)) : Algebraic.Sidecar (Power.namedPower channel exponent) :=
  match exponent, reading with
  | 0, _ => sidecar.pow 0
  | _ + 1, some certificate => Algebraic.Sidecar.ofRational certificate.reading
  | exponent + 1, none => sidecar.pow (exponent + 1)

/-- Zero power retains the same actual parent even when its exact scalar inspection succeeded. -/
theorem powerSidecar_zero {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (reading : Option (PowerReading sidecar 0)) : powerSidecar sidecar 0 reading = sidecar.pow 0 := rfl

/-- Positive powers preserve the complete original scalar-inspection and generic fallback branches. -/
theorem powerSidecar_succ {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) (exponent : Nat)
    (reading : Option (PowerReading sidecar (exponent + 1))) :
    powerSidecar sidecar (exponent + 1) reading =
      (match reading with
      | some certificate => Algebraic.Sidecar.ofRational certificate.reading
      | none => sidecar.pow (exponent + 1)) := by
  cases reading <;> rfl

end Construction

set_option genInjectivity false in
/-- The actual original construction tree, retaining exact operations and available materialized caches. -/
inductive Construction (environment : Fin arity → Annotated) : Expr arity → CoherentNamed → Type 1 where
  /-- Retain the original compiler/certificate and its optional once computed selected-generator check. -/
  | base {expression} (cached : Base.Cached environment expression) (certificate : Base.Certificate cached)
      (checked : Construction.BaseCache cached certificate) :
      Construction environment (.base expression) cached.channel
  /-- Retain the original child and any actual already materialized child Sidecar. -/
  | neg {input channel} (child : Construction environment input channel)
      (sidecar : Option (Algebraic.Sidecar channel))
      (polynomial : Construction.PolynomialCache environment (CoherentNamed.neg channel)) :
      Construction environment (.neg input) (CoherentNamed.neg channel)
  /-- Retain the original ordered children, actual materializations and any demanded cached-sum attempt. -/
  | add {left right first second} (leftChild : Construction environment left first)
      (leftSidecar : Option (Algebraic.Sidecar first)) (rightChild : Construction environment right second)
      (rightSidecar : Option (Algebraic.Sidecar second))
      (polynomial : Construction.PolynomialCache environment (CoherentNamed.add first second))
      (sum : Option (Prepared.Sum.Attempt first second)) :
      Construction environment (.add left right) (CoherentNamed.add first second)
  /-- Retain the original subtraction and the same ordered child caches. -/
  | sub {left right first second} (leftChild : Construction environment left first)
      (leftSidecar : Option (Algebraic.Sidecar first)) (rightChild : Construction environment right second)
      (rightSidecar : Option (Algebraic.Sidecar second))
      (polynomial : Construction.PolynomialCache environment (CoherentNamed.add first (CoherentNamed.neg second))) :
      Construction environment (.sub left right) (CoherentNamed.add first (CoherentNamed.neg second))
  /-- Retain the original product and the same ordered child caches. -/
  | mul {left right first second} (leftChild : Construction environment left first)
      (leftSidecar : Option (Algebraic.Sidecar first)) (rightChild : Construction environment right second)
      (rightSidecar : Option (Algebraic.Sidecar second))
      (polynomial : Construction.PolynomialCache environment (CoherentNamed.mul first second)) :
      Construction environment (.mul left right) (CoherentNamed.mul first second)
  /-- Retain the original natural-power child and any once inspected existing Sidecar. -/
  | pow {input channel} (child : Construction environment input channel) (exponent : Nat)
      (cached : Option (Construction.PowerCache channel exponent))
      (polynomial : Construction.PolynomialCache environment (Power.namedPower channel exponent)) :
      Construction environment (.pow input exponent) (Power.namedPower channel exponent)
  /-- Retain the original conjugate and any actual already materialized child Sidecar. -/
  | conj {input channel} (child : Construction environment input channel)
      (sidecar : Option (Algebraic.Sidecar channel))
      (polynomial : Construction.PolynomialCache environment (CoherentNamed.conj channel)) :
      Construction environment (.conj input) (CoherentNamed.conj channel)
  /-- Retain the actual materialized denominator and its original reciprocal residual cache/result. -/
  | inverse {input channel} (child : Construction environment input channel) (sidecar : Algebraic.Sidecar channel)
      (prepared : Prepared channel) (cache : Residual.Reciprocal sidecar.residual prepared)
      (result : Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
      (result_eq : result = sidecar.reciprocalFromCache cache) :
      Construction environment (.inverse input) (prepared.quotient (CoherentNamed.Coherence.exact 1))
  /-- Retain the exact original coordinate/unit/preparation cache without constructing a composite Sidecar. -/
  | inverseGenerator {input channel} (child : Construction environment input channel)
      (sidecar : Option (Algebraic.Sidecar channel)) (cache : Construction.GeneratorInverse channel)
      (retained : Construction.GeneratorInverse.Caches environment cache) :
      Construction environment (.inverse input) cache.output

constructive_injectivity Construction

namespace Construction

variable {environment : Fin arity → Annotated}

/-- Complete checked constructions respect operational comparisons of their original input atoms.

Both retained construction trees keep their own ordered children and actual
denominator preparations. Scalar congruences compare every supported node,
including either reciprocal implementation, without materializing Sidecars
or recomputing exact arithmetic and preparation caches.
-/
def namedEquivalent {other : Fin arity → Annotated} {expression : Expr arity}
    {firstChannel secondChannel : CoherentNamed}
    (first : Construction environment expression firstChannel) (second : Construction other expression secondChannel)
    (atoms : ∀ index, NamedEquivalent (environment index).channel.name (other index).channel.name) :
    NamedEquivalent firstChannel.name secondChannel.name :=
  match first, second with
  | .base cached _ _, .base otherCached _ _ =>
      cached.compiled.namedEquivalent otherCached.compiled atoms
  | .neg child _ _, .neg other _ _ =>
      Additive.coherentNeg_respects _ _ (namedEquivalent child other atoms)
  | .add first _ second _ _ _, .add otherFirst _ otherSecond _ _ _ =>
      Sum.Congruence.coherentAdd_respects _ _ _ _
        (namedEquivalent first otherFirst atoms) (namedEquivalent second otherSecond atoms)
  | .sub first _ second _ _, .sub otherFirst _ otherSecond _ _ =>
      Sum.Congruence.coherentAdd_respects _ _ _ _ (namedEquivalent first otherFirst atoms)
        (Additive.coherentNeg_respects _ _ (namedEquivalent second otherSecond atoms))
  | .mul first _ second _ _, .mul otherFirst _ otherSecond _ _ =>
      Product.Congruence.coherentMul_respects _ _ _ _
        (namedEquivalent first otherFirst atoms) (namedEquivalent second otherSecond atoms)
  | .pow _ 0 _ _, .pow _ _ _ _ => NamedEquivalent.refl _
  | .pow child (exponent + 1) _ _, .pow other _ _ _ =>
      Power.namedPower_respects _ _ (namedEquivalent child other atoms) (exponent + 1)
  | .conj child _ _, .conj other _ _ =>
      CoherentNamed.conj_respects (namedEquivalent child other atoms)
  | .inverse child _ prepared _ _ _, .inverse other _ otherPrepared _ _ _ =>
      prepared.quotient_respects_equivalent otherPrepared (namedEquivalent child other atoms) (NamedEquivalent.refl _)
  | .inverse child _ prepared _ _ _, .inverseGenerator other _ otherCache _ =>
      NamedEquivalent.transport rfl (congrArg CoherentNamed.name otherCache.2.2.2.output_eq.symm)
        (prepared.quotient_respects_equivalent otherCache.prepared
          (namedEquivalent child other atoms) (NamedEquivalent.refl _))
  | .inverseGenerator child _ cache _, .inverse other _ otherPrepared _ _ _ =>
      NamedEquivalent.transport (congrArg CoherentNamed.name cache.2.2.2.output_eq.symm) rfl
        (cache.prepared.quotient_respects_equivalent otherPrepared
          (namedEquivalent child other atoms) (NamedEquivalent.refl _))
  | .inverseGenerator child _ cache _, .inverseGenerator other _ otherCache _ =>
      NamedEquivalent.transport
        (congrArg CoherentNamed.name cache.2.2.2.output_eq.symm)
        (congrArg CoherentNamed.name otherCache.2.2.2.output_eq.symm)
        (cache.prepared.quotient_respects_equivalent otherCache.prepared
          (namedEquivalent child other atoms) (NamedEquivalent.refl _))
termination_by structural first

/-- Materialize the original construction, consuming actual cached child Sidecars when present.

This is the shared full interpreter. Each absent child is materialized once;
the caller stores the returned result in Completed. Exact reciprocal nodes
use their retained numerical preparation and pay reciprocal-residual work only
at this explicit boundary.
-/
@[expose] def buildSidecar : {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → Algebraic.Sidecar channel
  | _, _, .base _ certificate _ => certificate.buildSidecar
  | _, _, .neg child cached _ =>
      let sidecar := match cached with | some sidecar => sidecar | none => child.buildSidecar
      sidecar.neg
  | _, _, .add first firstCache second secondCache _ _ =>
      let left := match firstCache with | some sidecar => sidecar | none => first.buildSidecar
      let right := match secondCache with | some sidecar => sidecar | none => second.buildSidecar
      left.add right
  | _, _, .sub first firstCache second secondCache _ =>
      let left := match firstCache with | some sidecar => sidecar | none => first.buildSidecar
      let right := match secondCache with | some sidecar => sidecar | none => second.buildSidecar
      left.sub right
  | _, _, .mul first firstCache second secondCache _ =>
      let left := match firstCache with | some sidecar => sidecar | none => first.buildSidecar
      let right := match secondCache with | some sidecar => sidecar | none => second.buildSidecar
      left.mul right
  | _, _, .pow child exponent cached _ => match cached with
    | some retained => powerSidecar retained.1 exponent retained.2.val
    | none =>
        let sidecar := child.buildSidecar
        powerSidecar sidecar exponent (PowerReading.inspect sidecar exponent)
  | _, _, .conj child cached _ =>
      let sidecar := match cached with | some sidecar => sidecar | none => child.buildSidecar
      sidecar.conj
  | _, _, .inverse _ _ _ _ result _ => result
  | _, _, .inverseGenerator child cached inverseCache _ =>
      let sidecar := match cached with | some sidecar => sidecar | none => child.buildSidecar
      let certificate := inverseCache.2.2.2
      let reciprocal := Residual.Reciprocal.ofPrepared sidecar.residual certificate.prepared
      show Algebraic.Sidecar certificate.output from
        certificate.output_eq.symm ▸ sidecar.reciprocalFromCache reciprocal

/-- Read an existing original polynomial view without traversing or evaluating the construction again. -/
@[expose] def polynomial : {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → Option (Polynomial environment channel)
  | _, _, .base _ _ cached => cached.2.polynomial
  | _, _, .neg _ _ cached | _, _, .add _ _ _ _ cached _ | _, _, .sub _ _ _ _ cached
      | _, _, .mul _ _ _ _ cached | _, _, .pow _ _ _ cached | _, _, .conj _ _ cached => cached.polynomial
  | _, _, .inverseGenerator _ _ _ cached => cached.polynomial.polynomial
  | _, _, .inverse _ _ _ _ _ _ => none

/-- An optional actual child cache agrees with this same original child's complete construction. -/
@[expose] def CacheMatches {expression : Expr arity} {channel : CoherentNamed}
    (child : Construction environment expression channel) (cached : Option (Algebraic.Sidecar channel)) : Prop :=
  ∀ sidecar, cached = some sidecar → sidecar = child.buildSidecar

/-- Every available child materialization belongs to its actual original retained construction. -/
@[expose] def CacheCoherent : {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → Prop
  | _, _, .base _ _ retained => retained.Matches
  | _, _, .neg child cached polynomialCache => child.CacheCoherent ∧ child.CacheMatches cached ∧
      polynomialCache.polynomial = child.polynomial.map Polynomial.neg
  | _, _, .conj child cached polynomialCache => child.CacheCoherent ∧ child.CacheMatches cached ∧
      polynomialCache.polynomial = child.polynomial.map Polynomial.conj
  | _, _, .add first firstCache second secondCache polynomialCache _ =>
      first.CacheCoherent ∧ first.CacheMatches firstCache ∧ second.CacheCoherent ∧ second.CacheMatches secondCache ∧
      polynomialCache.polynomial = Polynomial.combine Polynomial.add first.polynomial second.polynomial
  | _, _, .sub first firstCache second secondCache polynomialCache =>
      first.CacheCoherent ∧ first.CacheMatches firstCache ∧ second.CacheCoherent ∧ second.CacheMatches secondCache ∧
      polynomialCache.polynomial = Polynomial.combine Polynomial.sub first.polynomial second.polynomial
  | _, _, .mul first firstCache second secondCache polynomialCache =>
      first.CacheCoherent ∧ first.CacheMatches firstCache ∧ second.CacheCoherent ∧ second.CacheMatches secondCache ∧
      polynomialCache.polynomial = Polynomial.combine Polynomial.mul first.polynomial second.polynomial
  | _, _, .pow child exponent cached polynomialCache => child.CacheCoherent ∧
      (∀ retained, cached = some retained → retained.1 = child.buildSidecar) ∧
      polynomialCache.polynomial = child.polynomial.map (fun input => input.pow exponent)
  | _, _, .inverse child sidecar _ _ _ _ => child.CacheCoherent ∧ sidecar = child.buildSidecar
  | _, _, .inverseGenerator child cached _ retained => child.CacheCoherent ∧ child.CacheMatches cached ∧
      retained.Matches

/-- Reading an actual optional child cache gives that same original child's complete materialization. -/
theorem cachedSidecar_eq {expression : Expr arity} {channel : CoherentNamed}
    (child : Construction environment expression channel) (cached : Option (Algebraic.Sidecar channel))
    (origin : child.CacheMatches cached) :
    (fun actual : Option (Algebraic.Sidecar channel) =>
      match actual with | some sidecar => sidecar | none => child.buildSidecar) cached = child.buildSidecar := by
  cases cached with
  | none => rfl
  | some sidecar => exact origin sidecar rfl

/-- Read whether this exact original construction already retains its demanded inverse request and complete result. -/
@[expose] def inverseChecked : {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → Bool
  | _, _, .base _ _ cached => cached.1.isSome
  | _, _, .neg _ _ cached | _, _, .add _ _ _ _ cached _ | _, _, .sub _ _ _ _ cached
      | _, _, .mul _ _ _ _ cached | _, _, .pow _ _ _ cached | _, _, .conj _ _ cached => cached.hasInverseCheck
  | _, _, .inverseGenerator _ _ _ cached => cached.polynomial.hasInverseCheck
  | _, _, .inverse _ _ _ _ _ _ => false

/-- A retained sum attempt changes none of the original polynomial, full materialization or inverse-check readers. -/
theorem add_sum_readback {left right : Expr arity} {first second : CoherentNamed}
    (firstChild : Construction environment left first) (firstStored : Option (Algebraic.Sidecar first))
    (secondChild : Construction environment right second) (secondStored : Option (Algebraic.Sidecar second))
    (polynomial : PolynomialCache environment (CoherentNamed.add first second))
    (attempt : Option (Prepared.Sum.Attempt first second)) :
    ((Construction.add firstChild firstStored secondChild secondStored polynomial attempt).polynomial,
      (Construction.add firstChild firstStored secondChild secondStored polynomial attempt).buildSidecar,
      (Construction.add firstChild firstStored secondChild secondStored polynomial attempt).inverseChecked) =
    ((Construction.add firstChild firstStored secondChild secondStored polynomial none).polynomial,
      (Construction.add firstChild firstStored secondChild secondStored polynomial none).buildSidecar,
      (Construction.add firstChild firstStored secondChild secondStored polynomial none).inverseChecked) := rfl

/-- Read only already retained reciprocal observations through the actual original conjugation history.

No absent receipt is demanded here. Unsupported construction nodes supply no
source view; a later denominator request keeps the original fallback.
-/
@[expose] def cachedSource : {expression : Expr arity} → {channel : CoherentNamed} →
    Construction environment expression channel → Option (Prepared.Sum.Source channel)
  | _, _, .inverseGenerator _ _ _ retained => retained.cachedSource
  | _, _, .conj child _ _ => child.cachedSource.map Prepared.Sum.Source.conj
  | _, _, _ => none

/-- Refine demanded structural denominator caches while preserving the original construction and numerical output.

An existing inverse check is inspected first. Otherwise actual reciprocal
receipts supply product, power, conjugation and checked cached-sum preparations; unsupported
nodes keep the original default request. No Sidecar is materialized here.
-/
@[expose] def prepareDenominator {expression : Expr arity} {channel : CoherentNamed}
    (original : Construction environment expression channel) (coherent : original.CacheCoherent) :
    {retained : Construction environment expression channel // retained.CacheCoherent ∧
      retained.polynomial = original.polynomial ∧ retained.buildSidecar = original.buildSidecar} ×
      Option (Prepared channel) :=
  if original.inverseChecked then ⟨⟨original, coherent, rfl, rfl⟩, none⟩
  else
    match original, coherent with
    | .inverseGenerator child stored inverseCache actual, coherent =>
        let demanded := actual.demandReciprocal
        ⟨⟨.inverseGenerator child stored inverseCache demanded.1,
          ⟨coherent.1, coherent.2.1, actual.demandReciprocal_matches coherent.2.2⟩, rfl, rfl⟩,
          some demanded.2⟩
    | .add (first := firstChannel) (second := secondChannel)
        first firstStored second secondStored polynomialCache sum, coherent =>
        match sum with
        | some attempt =>
            ⟨⟨.add first firstStored second secondStored polynomialCache (some attempt), coherent, rfl, rfl⟩,
              attempt.prepared⟩
        | none => by
            let left := prepareDenominator first coherent.1
            let right := prepareDenominator second coherent.2.2.1
            have leftMatches : left.1.val.CacheMatches firstStored := by
              intro sidecar selected
              exact (coherent.2.1 sidecar selected).trans left.1.property.2.2.symm
            have rightMatches : right.1.val.CacheMatches secondStored := by
              intro sidecar selected
              exact (coherent.2.2.2.1 sidecar selected).trans right.1.property.2.2.symm
            have polynomial : polynomialCache.polynomial =
                Polynomial.combine Polynomial.add left.1.val.polynomial right.1.val.polynomial :=
              coherent.2.2.2.2.trans (congrArg₂ (Polynomial.combine Polynomial.add)
                left.1.property.2.1.symm right.1.property.2.1.symm)
            have leftValue := (cachedSidecar_eq left.1.val firstStored leftMatches).trans
              (left.1.property.2.2.trans (cachedSidecar_eq first firstStored coherent.2.1).symm)
            have rightValue := (cachedSidecar_eq right.1.val secondStored rightMatches).trans
              (right.1.property.2.2.trans (cachedSidecar_eq second secondStored coherent.2.2.2.1).symm)
            let attempt := match left.1.val.cachedSource, right.1.val.cachedSource with
              | some left, some right => some (Prepared.Sum.inspect (left, right))
              | none, _ | _, none => none
            have output :
                (Construction.add left.1.val firstStored right.1.val secondStored
                  polynomialCache attempt).buildSidecar =
                  (Construction.add first firstStored second secondStored polynomialCache none).buildSidecar :=
              congrArg₂ (fun (left : Algebraic.Sidecar firstChannel) (right : Algebraic.Sidecar secondChannel) =>
                left.add right) leftValue rightValue
            exact ⟨⟨.add left.1.val firstStored right.1.val secondStored polynomialCache attempt,
              ⟨left.1.property.1, leftMatches, right.1.property.1, rightMatches, polynomial⟩, rfl, output⟩,
              attempt.bind Prepared.Sum.Attempt.prepared⟩
    | .mul (first := firstChannel) (second := secondChannel)
        first firstStored second secondStored polynomialCache, coherent => by
        let left := prepareDenominator first coherent.1
        let right := prepareDenominator second coherent.2.2.1
        have leftMatches : left.1.val.CacheMatches firstStored := by
          intro sidecar selected
          exact (coherent.2.1 sidecar selected).trans left.1.property.2.2.symm
        have rightMatches : right.1.val.CacheMatches secondStored := by
          intro sidecar selected
          exact (coherent.2.2.2.1 sidecar selected).trans right.1.property.2.2.symm
        have polynomial : polynomialCache.polynomial =
            Polynomial.combine Polynomial.mul left.1.val.polynomial right.1.val.polynomial :=
          coherent.2.2.2.2.trans (congrArg₂ (Polynomial.combine Polynomial.mul)
            left.1.property.2.1.symm right.1.property.2.1.symm)
        have leftValue := (cachedSidecar_eq left.1.val firstStored leftMatches).trans
          (left.1.property.2.2.trans (cachedSidecar_eq first firstStored coherent.2.1).symm)
        have rightValue := (cachedSidecar_eq right.1.val secondStored rightMatches).trans
          (right.1.property.2.2.trans (cachedSidecar_eq second secondStored coherent.2.2.2.1).symm)
        have output :
            (Construction.mul left.1.val firstStored right.1.val secondStored polynomialCache).buildSidecar =
              (Construction.mul first firstStored second secondStored polynomialCache).buildSidecar := by
          exact congrArg₂ (fun (left : Algebraic.Sidecar firstChannel) (right : Algebraic.Sidecar secondChannel) =>
            left.mul right) leftValue rightValue
        let prepared := match left.2, right.2 with
          | some left, some right => some (left.mul right)
          | none, _ | _, none => none
        exact ⟨⟨.mul left.1.val firstStored right.1.val secondStored polynomialCache,
          ⟨left.1.property.1, leftMatches, right.1.property.1, rightMatches, polynomial⟩, rfl, output⟩,
          prepared⟩
    | .pow (channel := inputChannel) child exponent stored polynomialCache, coherent => by
        let retained := prepareDenominator child coherent.1
        have cached : ∀ actual, stored = some actual → actual.1 = retained.1.val.buildSidecar := by
          intro actual selected
          exact (coherent.2.1 actual selected).trans retained.1.property.2.2.symm
        have polynomial : polynomialCache.polynomial =
            retained.1.val.polynomial.map (fun input => input.pow exponent) :=
          coherent.2.2.trans (congrArg (fun value => value.map (fun input => input.pow exponent))
            retained.1.property.2.1.symm)
        have output : (Construction.pow retained.1.val exponent stored polynomialCache).buildSidecar =
            (Construction.pow child exponent stored polynomialCache).buildSidecar := by
          cases stored with
          | some actual => rfl
          | none =>
              exact congrArg (fun sidecar : Algebraic.Sidecar inputChannel =>
                powerSidecar sidecar exponent (PowerReading.inspect sidecar exponent)) retained.1.property.2.2
        exact ⟨⟨.pow retained.1.val exponent stored polynomialCache,
          ⟨retained.1.property.1, cached, polynomial⟩, rfl, output⟩,
          retained.2.map (fun prepared => prepared.pow exponent)⟩
    | .conj (channel := inputChannel) child stored polynomialCache, coherent => by
        let retained := prepareDenominator child coherent.1
        have cached : retained.1.val.CacheMatches stored := by
          intro sidecar selected
          exact (coherent.2.1 sidecar selected).trans retained.1.property.2.2.symm
        have polynomial : polynomialCache.polynomial = retained.1.val.polynomial.map Polynomial.conj :=
          coherent.2.2.trans (congrArg (fun value => value.map Polynomial.conj) retained.1.property.2.1.symm)
        have value := (cachedSidecar_eq retained.1.val stored cached).trans
          (retained.1.property.2.2.trans (cachedSidecar_eq child stored coherent.2.1).symm)
        have output : (Construction.conj retained.1.val stored polynomialCache).buildSidecar =
            (Construction.conj child stored polynomialCache).buildSidecar :=
          congrArg (fun sidecar : Algebraic.Sidecar inputChannel => sidecar.conj) value
        exact ⟨⟨.conj retained.1.val stored polynomialCache,
          ⟨retained.1.property.1, cached, polynomial⟩, rfl, output⟩, retained.2.map Prepared.conj⟩
    | original, coherent => ⟨⟨original, coherent, rfl, rfl⟩, none⟩
termination_by structural original

/-- A stored guard returns the whole original construction before any structural child-preparation traversal. -/
theorem prepareDenominator_checked {expression : Expr arity} {channel : CoherentNamed}
    (original : Construction environment expression channel) (coherent : original.CacheCoherent)
    (checked : original.inverseChecked = true) :
    original.prepareDenominator coherent = (⟨original, coherent, rfl, rfl⟩, none) := by
  unfold prepareDenominator
  rewrite [checked]
  rfl

/-- A stored sum attempt returns the complete original node and its same success or failed-test result.

This branch runs only when no inverse guard is already retained. Neither child
is traversed, and an inconclusive sum attempt is retained just like a success.
-/
theorem prepareDenominator_add_cached {left right : Expr arity} {first second : CoherentNamed}
    (firstChild : Construction environment left first) (firstStored : Option (Algebraic.Sidecar first))
    (secondChild : Construction environment right second) (secondStored : Option (Algebraic.Sidecar second))
    (polynomial : PolynomialCache environment (CoherentNamed.add first second))
    (attempt : Prepared.Sum.Attempt first second)
    (coherent :
      (Construction.add firstChild firstStored secondChild secondStored polynomial (some attempt)).CacheCoherent)
    (unchecked :
      (Construction.add firstChild firstStored secondChild secondStored polynomial (some attempt)).inverseChecked =
        false) :
    (Construction.add firstChild firstStored secondChild secondStored polynomial (some attempt)).prepareDenominator
        coherent =
      (⟨Construction.add firstChild firstStored secondChild secondStored polynomial (some attempt),
        coherent, rfl, rfl⟩, attempt.prepared) := by
  unfold prepareDenominator
  rewrite [unchecked]
  rfl

/-- Prepare a missing original base polynomial at its actual source,
retaining the same channel and full materialization.

Other nodes already store their mathematical operation's polynomial output.
This request does not traverse or reinterpret the checked grammar. A base
normalization consumes its original retained compilation only when demanded.
-/
@[expose] def preparePolynomial {expression : Expr arity} {channel : CoherentNamed}
    (original : Construction environment expression channel) (coherent : original.CacheCoherent) :
    {retained : Construction environment expression channel //
      retained.CacheCoherent ∧ retained.buildSidecar = original.buildSidecar} :=
  match original, coherent with
  | .base cached certificate actual, coherent =>
      let polynomial := actual.preparePolynomial coherent
      ⟨.base cached certificate (actual.1, polynomial.val), Or.inr polynomial.property, rfl⟩
  | .inverseGenerator child cached inverseCache actual, coherent =>
      let polynomial := actual.preparePolynomial coherent.2.2
      ⟨.inverseGenerator child cached inverseCache (actual.withPolynomial polynomial.val),
        ⟨coherent.1, coherent.2.1, Or.inr polynomial.property⟩, rfl⟩
  | original, coherent => ⟨original, coherent, rfl⟩

/-- An exact completion view retains its actual channel/tree and any already stored full output.

The subtype binds all optional child caches and the optional output cache to
actual construction equalities. It is a view of the original owners, not a new
completion record, and it performs no generic Sidecar computation.
-/
abbrev Result (environment : Fin arity → Annotated) (expression : Expr arity) :=
  (channel : CoherentNamed) × (construction : Construction environment expression channel) ×
    {cached : Option (Algebraic.Sidecar channel) // construction.CacheCoherent ∧ construction.CacheMatches cached}

end Construction

set_option genInjectivity false in
/-- A full checked-expression materialization retaining its actual stored Sidecar and original construction equality. -/
structure Completed (environment : Fin arity → Annotated) (expression : Expr arity) where
  /-- The actual original numerical output channel. -/
  channel : CoherentNamed
  /-- The same original retained child/construction/preparation tree. -/
  construction : Construction environment expression channel
  /-- The stored complete algebraic residual of this same output. -/
  sidecar : Algebraic.Sidecar channel
  /-- All retained child Sidecars belong to their actual original constructions. -/
  cache_coherent : construction.CacheCoherent
  /-- The stored output is this original construction's actual materialization. -/
  sidecar_eq : sidecar = construction.buildSidecar

constructive_injectivity Completed

namespace Construction.Result

variable {environment : Fin arity → Annotated}

/-- Read the actual retained numerical channel, without reconstructing it from an erased index. -/
@[expose] def channel {expression : Expr arity} (result : Result environment expression) : CoherentNamed := result.1

/-- Read the actual original checked construction. -/
@[expose] def construction {expression : Expr arity} (result : Result environment expression) :
    Construction environment expression result.channel := result.2.1

/-- Read the actual optional stored full output, without materializing an absent cache. -/
@[expose] def cached {expression : Expr arity} (result : Result environment expression) :
    Option (Algebraic.Sidecar result.channel) := result.2.2.val

/-- Compare the actual original result channels without demanding either optional full materialization.

A dependent spine stores one delayed comparison at each original atom index.
Only used atoms force their comparisons, and repeated occurrences consume
the same retained comparison rather than constructing it again.
-/
def namedEquivalent {other : Fin arity → Annotated} {expression : Expr arity}
    (first : Result environment expression) (second : Result other expression)
    (atoms : ∀ index, NamedEquivalent (environment index).channel.name (other index).channel.name) :
    NamedEquivalent first.channel.name second.channel.name :=
  let comparisons := DependentVector.ofFn (fun index : Fin arity => Thunk.mk fun _ => atoms index)
  Construction.namedEquivalent first.construction second.construction (fun index => (comparisons.get index).get)

/-- Every original child cache agrees with its actual retained construction. -/
theorem coherent {expression : Expr arity} (result : Result environment expression) :
    result.construction.CacheCoherent :=
  result.2.2.property.1

/-- An actual stored output belongs to this same retained construction. -/
theorem cacheMatches {expression : Expr arity} (result : Result environment expression) :
    result.construction.CacheMatches result.cached := result.2.2.property.2

/-- Request this same construction's original polynomial cache without materializing a generic Sidecar. -/
@[expose] def preparePolynomial {expression : Expr arity} (child : Result environment expression) :
    Result environment expression :=
  let retained := child.construction.preparePolynomial child.coherent
  ⟨child.channel, retained.val, ⟨child.cached, retained.property.1, fun sidecar selected =>
    (child.cacheMatches sidecar selected).trans retained.property.2.symm⟩⟩

/-- A polynomial request preserves the complete actual numerical owner. -/
theorem preparePolynomial_channel {expression : Expr arity} (child : Result environment expression) :
    child.preparePolynomial.channel = child.channel := rfl

/-- A polynomial request retains the complete actual optional full materialization cache. -/
theorem preparePolynomial_cached {expression : Expr arity} (child : Result environment expression) :
    child.preparePolynomial.cached = child.cached := rfl

/-- Demand only actual structural denominator preparations, retaining the original result and full output cache. -/
@[expose] def prepareDenominator {expression : Expr arity} (child : Result environment expression) :
    (retained : Result environment expression) × Option (Prepared retained.channel) :=
  let actual := child.construction.prepareDenominator child.coherent
  let retained : Result environment expression :=
    ⟨child.channel, actual.1.val, ⟨child.cached, actual.1.property.1, fun sidecar selected =>
      (child.cacheMatches sidecar selected).trans actual.1.property.2.2.symm⟩⟩
  ⟨retained, actual.2⟩

/-- A structural denominator request retains the exact original numerical output channel. -/
theorem prepareDenominator_channel {expression : Expr arity} (child : Result environment expression) :
    child.prepareDenominator.1.channel = child.channel := rfl

/-- A structural denominator request retains the same actual optional full Sidecar cache. -/
theorem prepareDenominator_cached {expression : Expr arity} (child : Result environment expression) :
    child.prepareDenominator.1.cached = child.cached := rfl

/-- A stored guard retains the complete original Result and skips all ignored preparation recipes. -/
theorem prepareDenominator_checked {expression : Expr arity} (child : Result environment expression)
    (checked : child.construction.inverseChecked = true) : child.prepareDenominator = ⟨child, none⟩ := by
  rcases child with ⟨channel, construction, sidecar, coherent, cacheOrigin⟩
  let retain := fun actual :
      {retained : Construction environment expression channel // retained.CacheCoherent ∧
        retained.polynomial = construction.polynomial ∧ retained.buildSidecar = construction.buildSidecar} ×
        Option (Prepared channel) =>
    let retained : Result environment expression :=
      ⟨channel, actual.1.val, ⟨sidecar, actual.1.property.1, fun value selected =>
        (cacheOrigin value selected).trans actual.1.property.2.2.symm⟩⟩
    (⟨retained, actual.2⟩ : (retained : Result environment expression) × Option (Prepared retained.channel))
  exact congrArg retain (Construction.prepareDenominator_checked construction coherent checked)

/-- Retain an exact original base certificate while deferring any absent generic Sidecar. -/
@[expose] def ofBaseCertificate {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (certificate : Base.Certificate cached) : Result environment (.base expression) :=
  let polynomial := PolynomialCache.ofPolynomial none
  ⟨cached.channel, .base cached certificate (none, polynomial),
    ⟨certificate.cached, Or.inl rfl,
      fun result selected => certificate.cached_eq result selected⟩⟩

/-- Retain complete original admissions at their actual bounded compiler without forcing generic elimination. -/
@[expose] def base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (admissions : Base.Admissions cached.compiled.bindings) : Result environment (.base expression) :=
  ofBaseCertificate cached (cached.certificate admissions)

/-- Materialize one exact result and return the original Completed with its actual stored output. -/
@[expose] def materialize {expression : Expr arity} (result : Result environment expression) :
    Completed environment expression :=
  let retained : {sidecar : Algebraic.Sidecar result.channel // sidecar = result.construction.buildSidecar} :=
    match selected : result.cached with
    | some sidecar => ⟨sidecar, result.cacheMatches sidecar selected⟩
    | none => ⟨result.construction.buildSidecar, rfl⟩
  ⟨result.channel, result.construction, retained.val, result.coherent, retained.property⟩

/-- Negate the same actual child channel and retain its original optional materialization. -/
@[expose] def neg {expression : Expr arity} (child : Result environment expression) :
    Result environment (.neg expression) :=
  let child := child.preparePolynomial
  let polynomial := PolynomialCache.ofPolynomial (child.construction.polynomial.map Polynomial.neg)
  ⟨CoherentNamed.neg child.channel, .neg child.construction child.cached polynomial,
    ⟨none, ⟨child.coherent, child.cacheMatches, PolynomialCache.ofPolynomial_polynomial _⟩,
      fun _ impossible => by cases impossible⟩⟩

/-- Add the same original ordered channels while retaining both existing materialization caches. -/
@[expose] def add {left right : Expr arity} (first : Result environment left) (second : Result environment right) :
    Result environment (.add left right) :=
  let first := first.preparePolynomial
  let second := second.preparePolynomial
  let polynomial := PolynomialCache.ofPolynomial
    (Polynomial.combine Polynomial.add first.construction.polynomial second.construction.polynomial)
  ⟨CoherentNamed.add first.channel second.channel,
    .add first.construction first.cached second.construction second.cached polynomial none,
    ⟨none, ⟨first.coherent, first.cacheMatches, second.coherent, second.cacheMatches,
      PolynomialCache.ofPolynomial_polynomial _⟩, fun _ impossible => by cases impossible⟩⟩

/-- Subtract the same original ordered channels while retaining both existing materialization caches. -/
@[expose] def sub {left right : Expr arity} (first : Result environment left) (second : Result environment right) :
    Result environment (.sub left right) :=
  let first := first.preparePolynomial
  let second := second.preparePolynomial
  let polynomial := PolynomialCache.ofPolynomial
    (Polynomial.combine Polynomial.sub first.construction.polynomial second.construction.polynomial)
  ⟨CoherentNamed.add first.channel (CoherentNamed.neg second.channel),
    .sub first.construction first.cached second.construction second.cached polynomial,
    ⟨none, ⟨first.coherent, first.cacheMatches, second.coherent, second.cacheMatches,
      PolynomialCache.ofPolynomial_polynomial _⟩, fun _ impossible => by cases impossible⟩⟩

/-- Multiply the same original ordered channels while retaining both existing materialization caches. -/
@[expose] def mul {left right : Expr arity} (first : Result environment left) (second : Result environment right) :
    Result environment (.mul left right) :=
  let first := first.preparePolynomial
  let second := second.preparePolynomial
  let polynomial := PolynomialCache.ofPolynomial
    (Polynomial.combine Polynomial.mul first.construction.polynomial second.construction.polynomial)
  ⟨CoherentNamed.mul first.channel second.channel,
    .mul first.construction first.cached second.construction second.cached polynomial,
    ⟨none, ⟨first.coherent, first.cacheMatches, second.coherent, second.cacheMatches,
      PolynomialCache.ofPolynomial_polynomial _⟩, fun _ impossible => by cases impossible⟩⟩

/-- Retain the original finite power and inspect an already stored child Sidecar once, without materializing an
absent one. -/
@[expose] def pow {expression : Expr arity} (child : Result environment expression) (exponent : Nat) :
    Result environment (.pow expression exponent) := by
  let child := child.preparePolynomial
  let cached : Option (PowerCache child.channel exponent) := match child.cached with
    | some sidecar => some ⟨sidecar, ⟨PowerReading.inspect sidecar exponent, rfl⟩⟩
    | none => none
  have cacheMatches : ∀ retained, cached = some retained → retained.1 = child.construction.buildSidecar := by
    intro retained same
    dsimp only [cached] at same
    cases selected : child.cached with
    | none => rewrite [selected] at same; cases same
    | some sidecar =>
        rewrite [selected] at same
        cases Option.some.inj same
        exact child.cacheMatches sidecar selected
  let polynomial := PolynomialCache.ofPolynomial
    (child.construction.polynomial.map (fun input => input.pow exponent))
  exact ⟨Power.namedPower child.channel exponent, .pow child.construction exponent cached polynomial,
    ⟨none, ⟨child.coherent, cacheMatches, PolynomialCache.ofPolynomial_polynomial _⟩,
      fun _ impossible => by cases impossible⟩⟩

/-- Conjugate the same original channel while retaining its actual optional materialization. -/
@[expose] def conj {expression : Expr arity} (child : Result environment expression) :
    Result environment (.conj expression) :=
  let child := child.preparePolynomial
  let polynomial := PolynomialCache.ofPolynomial (child.construction.polynomial.map Polynomial.conj)
  ⟨CoherentNamed.conj child.channel, .conj child.construction child.cached polynomial,
    ⟨none, ⟨child.coherent, child.cacheMatches, PolynomialCache.ofPolynomial_polynomial _⟩,
      fun _ impossible => by cases impossible⟩⟩

/-- Store an actual materialized reciprocal, preserving its original child, preparation, residual cache and result. -/
@[expose] def ofReciprocal {expression : Expr arity} (child : Completed environment expression)
    (prepared : Prepared child.channel) (cache : Residual.Reciprocal child.sidecar.residual prepared)
    (result : Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
    (resultEq : result = child.sidecar.reciprocalFromCache cache) : Result environment (.inverse expression) :=
  ⟨prepared.quotient (CoherentNamed.Coherence.exact 1),
    .inverse child.construction child.sidecar prepared cache result resultEq,
    ⟨some result, ⟨child.cache_coherent, child.sidecar_eq⟩,
      fun _ selected => Option.some.inj selected.symm⟩⟩

/-- Complete an exact reciprocal from this same retained original generator certificate. -/
@[expose] def inverseGenerator {expression : Expr arity} (child : Result environment expression)
    (cache : GeneratorInverse child.channel) (source : Option (GeneratorInverse.Source environment cache) := none) :
    Result environment (.inverse expression) :=
  let polynomial := PolynomialCache.ofPolynomial none
  ⟨cache.output, .inverseGenerator child.construction child.cached cache ⟨none, source, polynomial⟩,
    ⟨none, ⟨child.coherent, child.cacheMatches, Or.inl rfl⟩,
      fun _ impossible => by cases impossible⟩⟩

/-- Check an available exact polynomial once and retain its actual original ordered generator attempts.

Base nodes retain their original certificate/check parent. Arithmetic and prior
inverse nodes consume their same stored normalization and original admission
table. Inconclusive exact attempts preserve their caches for the existing total
materialization fallback; no new generator is inferred from a composite output.
-/
@[expose] def checkInverse {expression : Expr arity} (child : Result environment expression)
    (supplied : Option (Prepared child.channel) := none) :
    (retained : Result environment expression) × Option (GeneratorInverse.Selected environment retained.channel) :=
  match expression, child, supplied with
  | _, ⟨_, .base cached certificate old, sidecar⟩, supplied =>
      let checked := match old.1 with
        | some result => result
        | none => ⟨supplied, ⟨certificate.inverseCheck supplied, rfl⟩⟩
      let retained : Result environment (.base _) :=
        ⟨cached.channel, .base cached certificate (some checked, old.2), sidecar⟩
      let inverseCache : Option (GeneratorInverse.Selected environment retained.channel) :=
        match checked.2.val with
        | none => none
        | some result =>
            match selected : result.2.val.2 with
            | none => none
            | some inverseCertificate =>
                some ⟨⟨cached.compiled.bindings.length, Basic.Binding.channels cached.compiled.bindings,
                  result.1.polynomial, inverseCertificate⟩,
                  ⟨Polynomial.ofOriginal cached.compiled.bindings certificate.generatorSlots result.1.polynomial,
                    ⟨inverseCertificate, rfl, (certificate.get_generatorSlots inverseCertificate.index).trans
                      (result.1.polynomial.inverseCheck_generator certificate.generator
                        result.2 inverseCertificate selected)⟩⟩⟩
      ⟨retained, inverseCache⟩
  | _, ⟨_, .neg original stored polynomialCache, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .neg original stored checked.1,
        ⟨retained.val, ⟨coherent.1, coherent.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2⟩,
          retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .conj original stored polynomialCache, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .conj original stored checked.1,
        ⟨retained.val, ⟨coherent.1, coherent.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2⟩,
          retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .add first firstStored second secondStored polynomialCache sum, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .add first firstStored second secondStored checked.1 sum,
        ⟨retained.val, ⟨coherent.1, coherent.2.1, coherent.2.2.1, coherent.2.2.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2.2.2⟩, retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .sub first firstStored second secondStored polynomialCache, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .sub first firstStored second secondStored checked.1,
        ⟨retained.val, ⟨coherent.1, coherent.2.1, coherent.2.2.1, coherent.2.2.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2.2.2⟩, retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .mul first firstStored second secondStored polynomialCache, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .mul first firstStored second secondStored checked.1,
        ⟨retained.val, ⟨coherent.1, coherent.2.1, coherent.2.2.1, coherent.2.2.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2.2.2⟩, retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .pow original exponent stored polynomialCache, retained⟩, supplied =>
      let checked := polynomialCache.checkInverse supplied
      let coherent := retained.property.1
      ⟨⟨_, .pow original exponent stored checked.1,
        ⟨retained.val, ⟨coherent.1, coherent.2.1,
          (polynomialCache.checkInverse_polynomial supplied).trans coherent.2.2⟩,
          retained.property.2⟩⟩, checked.2⟩
  | _, ⟨_, .inverseGenerator original stored inverseCache actual, retained⟩, supplied =>
      let coherent := retained.property.1
      let prepared := actual.preparePolynomial coherent.2.2
      let checked := prepared.val.checkInverse supplied
      ⟨⟨_, .inverseGenerator original stored inverseCache (actual.withPolynomial checked.1),
        ⟨retained.val, ⟨coherent.1, coherent.2.1,
          Or.inr ((prepared.val.checkInverse_polynomial supplied).trans prepared.property)⟩,
          retained.property.2⟩⟩, checked.2⟩
  | _, retained, _ => ⟨retained, none⟩

end Construction.Result

namespace Completed

variable {environment : Fin arity → Annotated}

/-- View this actual full result as an exact construction with its stored Sidecar, preserving the same cache. -/
@[expose] def toResult {expression : Expr arity} (completed : Completed environment expression) :
    Construction.Result environment expression :=
  ⟨completed.channel, completed.construction,
    ⟨some completed.sidecar, completed.cache_coherent, fun _ selected =>
      (Option.some.inj selected.symm).trans completed.sidecar_eq⟩⟩

/-- Compare complete original checked outputs while preserving their distinct construction and preparation caches. -/
def namedEquivalent {other : Fin arity → Annotated} {expression : Expr arity}
    (first : Completed environment expression) (second : Completed other expression)
    (atoms : ∀ index, NamedEquivalent (environment index).channel.name (other index).channel.name) :
    NamedEquivalent first.channel.name second.channel.name :=
  first.toResult.namedEquivalent second.toResult atoms

/-- Complete and materialize an original base from its exact original finite admissions. -/
@[expose] def base {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (admissions : Base.Admissions cached.compiled.bindings) : Completed environment (.base expression) :=
  (Construction.Result.base cached admissions).materialize

/-- Materialize an actual original output, normalized or supported certificate at its unchanged channel. -/
@[expose] def ofBaseCertificate {expression : Basic.Expr arity} (cached : Base.Cached environment expression)
    (certificate : Base.Certificate cached) : Completed environment (.base expression) :=
  (Construction.Result.ofBaseCertificate cached certificate).materialize

/-- Negate this same completed original child through the shared exact construction. -/
@[expose] def neg {expression : Expr arity} (child : Completed environment expression) :
    Completed environment (.neg expression) :=
  child.toResult.neg.materialize

/-- Add the same original ordered completed children through the shared exact construction. -/
@[expose] def add {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    Completed environment (.add left right) := (first.toResult.add second.toResult).materialize

/-- Subtract the same original ordered completed children through the shared exact construction. -/
@[expose] def sub {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    Completed environment (.sub left right) := (first.toResult.sub second.toResult).materialize

/-- Multiply the same original ordered completed children through the shared exact construction. -/
@[expose] def mul {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    Completed environment (.mul left right) := (first.toResult.mul second.toResult).materialize

/-- Materialize the same original finite power, retaining the once inspected actual child Sidecar. -/
@[expose] def pow {expression : Expr arity} (child : Completed environment expression) (exponent : Nat) :
    Completed environment (.pow expression exponent) := (child.toResult.pow exponent).materialize

/-- The original power construction retains the same child, actual Sidecar and inspected reading. -/
theorem pow_construction {expression : Expr arity} (child : Completed environment expression) (exponent : Nat) :
    (child.pow exponent).construction = .pow child.toResult.preparePolynomial.construction exponent
      (some ⟨child.sidecar, ⟨PowerReading.inspect child.sidecar exponent, rfl⟩⟩)
      (Construction.PolynomialCache.ofPolynomial
        (child.toResult.preparePolynomial.construction.polynomial.map (fun input => input.pow exponent))) := rfl

/-- A successful original inspection retains the zero-power parent or its positive-power scalar result. -/
theorem pow_sidecar_of_reading {expression : Expr arity} (child : Completed environment expression)
    (exponent : Nat) (reading : PowerReading child.sidecar exponent)
    (computed : PowerReading.inspect child.sidecar exponent = some reading) :
    (child.pow exponent).sidecar =
      (match exponent, reading with
      | 0, _ => child.sidecar.pow 0
      | _ + 1, certificate => Algebraic.Sidecar.ofRational certificate.reading) := by
  change Construction.powerSidecar child.sidecar exponent (PowerReading.inspect child.sidecar exponent) = _
  rewrite [computed]
  cases exponent <;> rfl

/-- The actual completed zero power retains its same stored original Sidecar and complete child cache. -/
theorem pow_zero_sidecar {expression : Expr arity} (child : Completed environment expression) :
    (child.pow 0).sidecar = child.sidecar.pow 0 := rfl

/-- Conjugate this same completed original child through the shared exact construction. -/
@[expose] def conj {expression : Expr arity} (child : Completed environment expression) :
    Completed environment (.conj expression) :=
  child.toResult.conj.materialize

/-- Retain an already materialized original reciprocal using its same cached preparation and residual. -/
@[expose] def inverse {expression : Expr arity} (child : Completed environment expression)
    (prepared : Prepared child.channel) (cache : Residual.Reciprocal child.sidecar.residual prepared)
    (result : Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
    (resultEq : result = child.sidecar.reciprocalFromCache cache) : Completed environment (.inverse expression) :=
  (Construction.Result.ofReciprocal child prepared cache result resultEq).materialize

/-- Full negation retains the complete original numerical Sidecar operation. -/
theorem neg_sidecar {expression : Expr arity} (child : Completed environment expression) :
    child.neg.sidecar = child.sidecar.neg := rfl

/-- Full addition retains the complete original ordered numerical Sidecar operation. -/
theorem add_sidecar {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    (first.add second).sidecar = first.sidecar.add second.sidecar := rfl

/-- Full subtraction retains the complete original ordered numerical Sidecar operation. -/
theorem sub_sidecar {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    (first.sub second).sidecar = first.sidecar.sub second.sidecar := rfl

/-- Full multiplication retains the complete original ordered numerical Sidecar operation. -/
theorem mul_sidecar {left right : Expr arity} (first : Completed environment left) (second :
    Completed environment right) :
    (first.mul second).sidecar = first.sidecar.mul second.sidecar := rfl

/-- Full conjugation retains the complete original Sidecar and sample-cache operation. -/
theorem conj_sidecar {expression : Expr arity} (child : Completed environment expression) :
    child.conj.sidecar = child.sidecar.conj := rfl

/-- Full reciprocal completion stores the exact original already computed reciprocal result. -/
theorem inverse_sidecar {expression : Expr arity} (child : Completed environment expression)
    (prepared : Prepared child.channel) (cache : Residual.Reciprocal child.sidecar.residual prepared)
    (result : Algebraic.Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
    (resultEq : result = child.sidecar.reciprocalFromCache cache) :
    (child.inverse prepared cache result resultEq).sidecar = result := rfl

/-- Attach this actual stored full Sidecar to the unchanged numerical output for production acquisition. -/
@[expose] def annotation {expression : Expr arity} (completed : Completed environment expression) : Annotated :=
  Annotated.algebraic completed.sidecar

end Completed

namespace Construction.Result

variable {environment : Fin arity → Annotated}

/-- Checking an exact generator preserves the actual original numerical output channel. -/
theorem checkInverse_channel {expression : Expr arity} (child : Result environment expression)
    (supplied : Option (Prepared child.channel) := none) :
    (child.checkInverse supplied).1.channel = child.channel := by
  rcases child with ⟨channel, construction, cached⟩
  cases construction <;> rfl

/-- A stored inverse guard preserves the whole Result and complete guard output for every proposed new request. -/
theorem checkInverse_cached {expression : Expr arity} (child : Result environment expression)
    (supplied : Option (Prepared child.channel)) (existing : child.construction.inverseChecked = true) :
    (child.checkInverse supplied).1 = child ∧ child.checkInverse supplied = child.checkInverse none := by
  rcases child with ⟨channel, construction, stored⟩
  cases construction with
  | base cached certificate retained =>
      rcases retained with ⟨checked, polynomial⟩
      cases checked with
      | none => cases existing
      | some checked => exact ⟨rfl, rfl⟩
  | neg original cached polynomial | conj original cached polynomial =>
      rcases polynomial with ⟨input, checked⟩
      cases input with
      | none => cases existing
      | some input =>
          cases checked with
          | none => cases existing
          | some checked => exact ⟨rfl, rfl⟩
  | add first firstCached second secondCached polynomial sum
      | sub first firstCached second secondCached polynomial
      | mul first firstCached second secondCached polynomial =>
      rcases polynomial with ⟨input, checked⟩
      cases input with
      | none => cases existing
      | some input =>
          cases checked with
          | none => cases existing
          | some checked => exact ⟨rfl, rfl⟩
  | pow original exponent cached polynomial =>
      rcases polynomial with ⟨input, checked⟩
      cases input with
      | none => cases existing
      | some input =>
          cases checked with
          | none => cases existing
          | some checked => exact ⟨rfl, rfl⟩
  | inverseGenerator original cached inverseCache retained =>
      rcases retained with ⟨reciprocal, source, polynomial⟩
      rcases polynomial with ⟨input, checked⟩
      cases input with
      | none => cases existing
      | some input =>
          cases checked with
          | none => cases existing
          | some checked => exact ⟨rfl, rfl⟩
  | inverse _ _ _ _ _ _ => cases existing

/-- Repeating a stored guard retains the whole original Result before another proposed request is consumed. -/
theorem checkInverse_retained {expression : Expr arity} (child : Result environment expression)
    (supplied : Option (Prepared child.channel)) (existing : child.construction.inverseChecked = true) :
    (child.checkInverse supplied).1 = child := (child.checkInverse_cached supplied existing).1

/-- Explicit full materialization preserves the actual original numerical channel. -/
theorem materialize_channel {expression : Expr arity} (child : Result environment expression) :
    child.materialize.channel = child.channel := (rfl)

/-- Explicit full materialization preserves the entire original construction, including its attempt caches. -/
theorem materialize_construction {expression : Expr arity} (child : Result environment expression) :
    HEq child.materialize.construction child.construction := (HEq.rfl)

/-- Resolve an original inverse guard using its retained exact generator certificate or one retained full fallback.

Coordinate or nonconstant-GCD inconclusivity invokes the original total Sidecar
procedure. The fallback stores its actual materialization in the original child
view. It does not classify a nonconstant gcd as selected-generator vanishing.
-/
@[expose] def inverseAttempt {expression : Expr arity} (child : Result environment expression) :
    Except ((retained : Result environment expression) × ZeroIdentity retained.channel)
      (Result environment (.inverse expression)) :=
  let known := child.prepareDenominator
  let checked := known.1.checkInverse known.2
  let retained := checked.1
  match checked.2 with
  | some checkedInverse => .ok (retained.inverseGenerator checkedInverse.cache (some checkedInverse.source))
  | none =>
      let materialized := retained.materialize
      match materialized.sidecar.inverse with
      | .ready prepared cache result computed => .ok (ofReciprocal materialized prepared cache result computed)
      | .obstructed zero => .error ⟨materialized.toResult, zero⟩

/-- An actual completed sidecar and its retained original classification for this same decision.

This is an exact dependent view of the existing Result, Sidecar and Resolved
owners. It exists only when the original decision branch materialized that
Sidecar; direct generator/preparation branches carry no synthetic classification.
-/
@[expose] def Resolution {expression : Expr arity} (retained : Result environment expression)
    (decision : Prepared.Decision retained.channel) : Type 2 :=
  Σ completed : { value : Completed environment expression // value.toResult = retained },
    { resolved : Algebraic.Sidecar.Resolved completed.val.sidecar //
      resolved = completed.val.sidecar.resolve ∧ decision =
        (congrArg (fun result : Result environment expression => result.channel) completed.property ▸
          resolved.decision) }

namespace Resolution

/-- The actual complete materialization retained by this same original decision branch. -/
@[expose] def completed {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    Completed environment expression := resolution.1.val

/-- The retained complete materialization projects to the same original exact result. -/
theorem completed_eq {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    resolution.completed.toResult = retained := resolution.1.property

/-- The actual once-computed classification on that same retained materialization. -/
@[expose] def resolved {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    Algebraic.Sidecar.Resolved resolution.completed.sidecar := resolution.2.val

/-- The stored classification was computed by the original resolver on the retained sidecar. -/
theorem resolved_eq {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    resolution.resolved = resolution.completed.sidecar.resolve := resolution.2.property.1

/-- The same whole-result equality identifies the original materialized channel. -/
theorem channel_eq {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    resolution.completed.channel = retained.channel :=
  congrArg (fun result : Result environment expression => result.channel) resolution.completed_eq

/-- The stored original decision is the readback of that same retained classification. -/
theorem decision_eq {expression : Expr arity} {retained : Result environment expression}
    {decision : Prepared.Decision retained.channel} (resolution : Resolution retained decision) :
    decision = (resolution.channel_eq ▸ resolution.resolved.decision) := resolution.2.property.2

end Resolution

/-- Compute the original exact branch once and retain its actual optional full classification.

Generator and prepared-cache branches keep their complete original result and
payment. Only the original materialization fallback constructs a Sidecar
resolution, then stores that same value beside its once read decision.
-/
@[expose] def resolve {expression : Expr arity} (child : Result environment expression) :
    Σ result : (retained : Result environment expression) × Prepared.Decision retained.channel,
      Option (Resolution result.1 result.2) :=
  match expression, child with
  | _, ⟨_, .inverseGenerator (input := input) original stored inverseCache actual, retained⟩ =>
      let demanded := actual.demandReciprocal
      let result : Result environment (.inverse input) :=
        ⟨inverseCache.output, .inverseGenerator original stored inverseCache demanded.1, retained⟩
      ⟨⟨result, .prepared demanded.2⟩, none⟩
  | _, original =>
      let known := original.prepareDenominator
      let checked := known.1.checkInverse known.2
      let retained := checked.1
      match checked.2 with
      | some checkedInverse => ⟨⟨retained, .prepared checkedInverse.cache.prepared⟩, none⟩
      | none =>
          let materialized := retained.materialize
          let resolved := materialized.sidecar.resolve
          let decision := resolved.decision
          ⟨⟨materialized.toResult, decision⟩, some ⟨⟨materialized, rfl⟩, ⟨resolved, rfl, rfl⟩⟩⟩

/-- Project the same original exact result and decision from their once computed retained branch. -/
@[expose] def decide {expression : Expr arity} (child : Result environment expression) :
    (retained : Result environment expression) × Prepared.Decision retained.channel := child.resolve.1

/-- A retained reciprocal decision consumes its same actual preparation receipt without another head or factor scan. -/
theorem decide_inverseGenerator_cached {expression : Expr arity} {channel : CoherentNamed}
    (original : Construction environment expression channel) (stored : Option (Algebraic.Sidecar channel))
    (inverseCache : GeneratorInverse channel) (receipt : GeneratorInverse.Reciprocal inverseCache)
    (actual : GeneratorInverse.Caches environment inverseCache)
    (selected : actual.reciprocal = some receipt)
    (retained : {cached : Option (Algebraic.Sidecar inverseCache.output) //
      (Construction.inverseGenerator original stored inverseCache actual).CacheCoherent ∧
      (Construction.inverseGenerator original stored inverseCache actual).CacheMatches cached}) :
    decide (⟨inverseCache.output, .inverseGenerator original stored inverseCache actual, retained⟩ :
      Result environment (.inverse expression)) =
      ⟨⟨inverseCache.output, .inverseGenerator original stored inverseCache
          (actual.withReciprocal (some receipt)), retained⟩, .prepared receipt.val.prepared⟩ := by
  unfold decide resolve GeneratorInverse.Caches.demandReciprocal
  dsimp only
  rewrite [selected]
  rfl

/-- Exact decision requests preserve the actual original output owner across both exact and materialized routes. -/
theorem decide_channel {expression : Expr arity} (child : Result environment expression) :
    child.decide.1.channel = child.channel := by
  rcases child with ⟨channel, construction, cached⟩
  cases construction with
  | inverseGenerator _ _ _ _ => rfl
  | base _ _ _ | neg _ _ _ | add _ _ _ _ _ _ | sub _ _ _ _ _ | mul _ _ _ _ _
      | pow _ _ _ _ | conj _ _ _ | inverse _ _ _ _ _ _ =>
      unfold decide resolve
      dsimp only
      split
      · exact (checkInverse_channel _ _).trans (prepareDenominator_channel _)
      · exact (materialize_channel _).trans
          ((checkInverse_channel _ _).trans (prepareDenominator_channel _))

end Construction.Result
end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
end
