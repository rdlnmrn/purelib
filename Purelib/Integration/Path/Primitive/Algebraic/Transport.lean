module

public import Purelib.Integration.Path.Primitive.Algebraic
public import Purelib.Integration.Path.Primitive
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive endpoint transport through original chart maps

The original map ownership and selected-root transport are retained. Exact
scalar checks use both cached divided coefficient readings and the map's
actual factor. Agreement is derived by Gaussian arithmetic at the original
selected generators, without identifying unlike quadratic parameters.
-/

public section

namespace Purelib.Integration.Path.Primitive.Algebraic.Endpoint

open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Algebra.Quadratic.Pair

variable {Chart : Type} {sheets : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}

/-- A fixed original chart-owned endpoint type retaining its source polynomial and selected-root operation. -/
abbrev OriginalEndpoint := Endpoint Chart sheets polynomialAt rootAt

local notation "EndpointType" => OriginalEndpoint (Chart := Chart) (sheets := sheets)
  (polynomialAt := polynomialAt) (rootAt := rootAt)

set_option genInjectivity false in
/-- Cached endpoint coefficient checks through an original chart-map owner.

The original owner relation binds both endpoints to that map. Its branch
certificate transports their actual selected generators, and the cached
coefficient differences retain both original primitive denotations. -/
structure TransportAttempt {Map : Type*} (belongs : Map → EndpointType → EndpointType → Prop)
    (factorAt : Map → Canonical) (owner : Map) (source target : EndpointType) where
  /-- The actual original chart-map owner retained as executable data. -/
  map : Map
  /-- The retained map is the original owner. -/
  map_eq : map = owner
  /-- Both original endpoints belong to this actual map. -/
  ownership : belongs owner source target
  /-- The actual source endpoint with its cached primitive readback. -/
  retainedSource : EndpointType
  /-- The cached source is the original source endpoint. -/
  retainedSource_eq : retainedSource = source
  /-- The actual target endpoint with its cached primitive readback. -/
  retainedTarget : EndpointType
  /-- The cached target is the original target endpoint. -/
  retainedTarget_eq : retainedTarget = target
  /-- The cached scalar generator factor computed by the original map. -/
  factor : Canonical
  /-- The cached factor belongs to the actual original map operation. -/
  factor_eq : factor = factorAt owner
  /-- The original selected source root is this factor times the original selected target root. -/
  root_equivalent : NamedEquivalent source.root.1.name
    (CoherentNamed.mul (Coherence.exact factor) target.root.1).name
  /-- The cached real coefficient difference. -/
  realDifference : Canonical
  /-- The real difference uses the two actual retained divided coefficient readings. -/
  realDifference_eq : realDifference = source.denotation.value.re - target.denotation.value.re
  /-- The cached generator coefficient difference after the original map's factor. -/
  imaginaryDifference : Canonical
  /-- The imaginary difference uses the actual original coefficient readings and map factor. -/
  imaginaryDifference_eq : imaginaryDifference =
    source.denotation.value.im * factor - target.denotation.value.im

constructive_injectivity TransportAttempt

/-- Compute both primitive coefficient differences once while retaining the original map and root transport. -/
@[expose] def prepareTransport {Map : Type*} (belongs : Map → EndpointType → EndpointType → Prop)
    (factorAt : Map → Canonical) (owner : Map) (source target : EndpointType)
    (ownership : belongs owner source target)
    (roots : NamedEquivalent source.root.1.name
      (CoherentNamed.mul (Coherence.exact (factorAt owner)) target.root.1).name) :
    TransportAttempt belongs factorAt owner source target :=
  let factor := factorAt owner
  ⟨owner, rfl, ownership, source, rfl, target, rfl, factor, rfl, roots,
    source.denotation.value.re - target.denotation.value.re, rfl,
    source.denotation.value.im * factor - target.denotation.value.im, rfl⟩

set_option genInjectivity false in
/-- An established primitive endpoint correspondence through its actual original chart map. -/
structure Transport {Map : Type*} {belongs : Map → EndpointType → EndpointType → Prop}
    {factorAt : Map → Canonical} {owner : Map} {source target : EndpointType}
    (attempt : TransportAttempt belongs factorAt owner source target) : Type where
  /-- The retained real coefficient difference vanishes. -/
  realZero : attempt.realDifference = 0
  /-- The retained mapped generator coefficient difference vanishes. -/
  imaginaryZero : attempt.imaginaryDifference = 0

constructive_injectivity Transport

set_option genInjectivity false in
/-- A proved endpoint correspondence or the identified obstruction to its actual scalar coefficient checks.

A failed coefficient check makes no assertion of selected-sheet inequality:
that converse would need additional independence evidence. -/
inductive TransportAttempt.Outcome {Map : Type*} {belongs : Map → EndpointType → EndpointType → Prop}
    {factorAt : Map → Canonical} {owner : Map} {source target : EndpointType}
    (attempt : TransportAttempt belongs factorAt owner source target) where
  /-- The original chart map's cached coefficient checks both pass. -/
  | transported (certificate : Transport attempt)
  /-- The original real coefficient difference does not vanish. -/
  | realObstructed (nonzero : attempt.realDifference ≠ 0)
  /-- The real difference vanishes and the mapped generator coefficient does not. -/
  | imaginaryObstructed (realZero : attempt.realDifference = 0) (nonzero : attempt.imaginaryDifference ≠ 0)

constructive_injectivity TransportAttempt.Outcome

/-- Decide the actual cached coefficient conditions without recomputing the original map or endpoint readings. -/
@[expose] def TransportAttempt.check {Map : Type*} {belongs : Map → EndpointType → EndpointType → Prop}
    {factorAt : Map → Canonical} {owner : Map} {source target : EndpointType}
    (attempt : TransportAttempt belongs factorAt owner source target) : attempt.Outcome :=
  if realZero : attempt.realDifference = 0 then
    if imaginaryZero : attempt.imaginaryDifference = 0 then .transported ⟨realZero, imaginaryZero⟩
    else .imaginaryObstructed realZero imaginaryZero
  else .realObstructed realZero

/-- A zero exact scalar difference identifies its two original readings. -/
private theorem eq_of_difference_zero (left right : Canonical) (zero : left - right = 0) : left = right := by
  calc
    left = (left - right) + right := by ring1
    _ = right := by rewrite [zero, zero_add]; rfl

/-- The checked chart transport realizes equality of the two original primitive endpoint channels.

The proof uses the original selected-root branch certificate and both cached
coefficient readings. No common parameter ring or independent root is formed. -/
@[noinline, nospecialize] def Transport.equivalent {Map : Type*}
    {belongs : Map → EndpointType → EndpointType → Prop} {factorAt : Map → Canonical}
    {owner : Map} {source target : EndpointType} {attempt : TransportAttempt belongs factorAt owner source target}
    (certificate : Transport attempt) : NamedEquivalent source.channel.name target.channel.name := by
  have realZero := certificate.realZero
  rewrite [attempt.realDifference_eq] at realZero
  have real := eq_of_difference_zero _ _ realZero
  have imaginaryZero := certificate.imaginaryZero
  rewrite [attempt.imaginaryDifference_eq] at imaginaryZero
  have imaginary := eq_of_difference_zero _ _ imaginaryZero
  have mapped := Product.Congruence.coherentMul_respects
    (Coherence.exact source.denotation.value.im) (Coherence.exact source.denotation.value.im)
    source.root.1 (CoherentNamed.mul (Coherence.exact attempt.factor) target.root.1)
    (NamedEquivalent.refl _) attempt.root_equivalent
  have associated := NamedEquivalent.symm (Product.Laws.coherentMul_assoc
    (Coherence.exact source.denotation.value.im) (Coherence.exact attempt.factor) target.root.1)
  have factorProduct := Product.Congruence.coherentMul_respects
    (CoherentNamed.mul (Coherence.exact source.denotation.value.im) (Coherence.exact attempt.factor))
    (Coherence.exact (source.denotation.value.im * attempt.factor)) target.root.1 target.root.1
    (Exact.Arithmetic.exact_mul source.denotation.value.im attempt.factor) (NamedEquivalent.refl _)
  rewrite [imaginary] at factorProduct
  have linear := NamedEquivalent.trans mapped (NamedEquivalent.trans associated factorProduct)
  have comparison := Sum.Congruence.coherentAdd_respects
    (Coherence.exact source.denotation.value.re) (Coherence.exact target.denotation.value.re)
    (CoherentNamed.mul (Coherence.exact source.denotation.value.im) source.root.1)
    (CoherentNamed.mul (Coherence.exact target.denotation.value.im) target.root.1)
    (by rewrite [real]; exact NamedEquivalent.refl _) linear
  change NamedEquivalent source.denotation.channel.name target.denotation.channel.name
  rewrite [source.denotation.channel_eq, target.denotation.channel_eq]
  exact comparison

/-- Join actual original primitive paths through a checked transport of their retained endpoint presentations. -/
@[noinline, nospecialize] def Transport.overlap {Map : Type*}
    {belongs : Map → EndpointType → EndpointType → Prop} {factorAt : Map → Canonical}
    {owner : Map} {source target : EndpointType} {attempt : TransportAttempt belongs factorAt owner source target}
    (certificate : Transport attempt) {start finish : CoherentNamed}
    (head : PrimitiveEdge start source.channel) (tail : PrimitivePath target.channel finish) :
    PrimitivePath start finish :=
  PrimitivePath.overlap head tail certificate.equivalent

/-- Close an actual original primitive path through the checked transport of its two original endpoint owners.

Both endpoints and every original integration program remain retained. The
closure comes from the original chart map and checked coefficient transport,
not from equality of the base coordinates or sheet labels alone. -/
@[noinline, nospecialize] def Transport.closed {Map : Type*}
    {belongs : Map → EndpointType → EndpointType → Prop} {factorAt : Map → Canonical}
    {owner : Map} {source target : EndpointType} {attempt : TransportAttempt belongs factorAt owner source target}
    (certificate : Transport attempt) (path : PrimitivePath target.channel source.channel) : ClosedPrimitiveBoundary :=
  ⟨target.channel, source.channel, path, certificate.equivalent⟩

end Purelib.Integration.Path.Primitive.Algebraic.Endpoint

end
