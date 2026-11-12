module

public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
public import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection

public import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
public import Purelib.Riemann.RootContinuation.CoherentRoot.SamplePrefix
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
public import Purelib.Polynomial.Approximation.Gaussian.Arithmetic
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
public import Purelib.Approximation.Gaussian.Provenance.Rational.Division
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Origin
import Purelib.Approximation.Gaussian.Arithmetic.Mul
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Conjugation
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Negation
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Reciprocal
public import Purelib.Polynomial.Approximation.Gaussian.Residual.SamplePrefix
public import Purelib.Polynomial.Approximation.Gaussian.Residual.QuadraticSum
public import Purelib.Approximation.Gaussian.Geometric.Preparation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained finite algebraic constructions on original channels

Each construction keeps its original scalar or root inputs. Its numerical
certificate is indexed by that construction and retains the actual arithmetic
caches consumed at every node, so subsequent operations reuse their input data.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Algebraic

open Purelib.Polynomial
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Substitution
open Purelib.Polynomial.Approximation.Gaussian renaming Residual -> PolynomialResidual
open Purelib.Polynomial.Approximation.Gaussian.Localization (Preparation)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation

set_option genInjectivity false in
/-- A finite construction retaining its actual scalar or root inputs and original numerical operations. -/
inductive Origin : CoherentNamed → Type 1 where
  /-- Retain the original scalar reading and its operational comparison. -/
  | rational {channel : CoherentNamed} (reading : RationalSidecar channel) : Origin channel
  /-- Retain the complete original root owner, multiplicity and numerical cache. -/
  | root {channel : CoherentNamed} (sidecar : PolynomialRoot.Sidecar channel) : Origin channel
  /-- Retain the original root owner and actual cache restart on the unchanged original channel. -/
  | recondition {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
      {track : CoherentRoot.WindingOneTrack polynomial ambient} {start : Nat}
      (original : CoherentRoot.CertifiedName track) (input : FTA.Squarefree.Input polynomial)
      (prepared : CoherentRoot.Reconditioning original start) : Origin original.value
  /-- Retain both original sub-constructions at their unchanged arithmetic output channel. -/
  | arithmetic {first second : CoherentNamed} (operation : Operation) (left : Origin first) (right : Origin second) :
      Origin (PolynomialArithmetic.channel operation first second)
  /-- Retain the original input owner at the unchanged exact constant-one zero-power channel. -/
  | powZero {channel : CoherentNamed} (original : Origin channel) : Origin (CoherentNamed.Coherence.exact 1)
  /-- Retain the actual original child at its intrinsic stateful negation channel. -/
  | neg {channel : CoherentNamed} (original : Origin channel) : Origin (CoherentNamed.neg channel)
  /-- Retain the original construction at its actual conjugated numerical channel. -/
  | conj {channel : CoherentNamed} (original : Origin channel) : Origin (CoherentNamed.conj channel)
  /-- Retain the original construction and actual successful denominator preparation at its reciprocal output. -/
  | reciprocal {channel : CoherentNamed} (original : Origin channel) (prepared : Division.Prepared channel) :
      Origin (prepared.quotient (CoherentNamed.Coherence.exact 1))
  /-- Retain a construction at an explicitly compared original channel. -/
  | transport {first second : CoherentNamed} (original : Origin first)
      (equivalent : NamedEquivalent second.name first.name) :
      Origin second

constructive_injectivity Origin

set_option genInjectivity false in
/-- Actual numerical certificates and arithmetic caches indexed by their original finite construction.

Arithmetic nodes consume both retained child residual records. Transport keeps
the same sample program and bound, and root nodes consume the same owner cache.
-/
inductive Cached : {channel : CoherentNamed} → Origin channel →
    (polynomial : CoefficientPolynomial) → PolynomialResidual polynomial channel → Type 1 where
  /-- An original scalar reading supplies its degree-one exact residual on the same channel. -/
  | rational {channel : CoherentNamed} (reading : RationalSidecar channel) : Cached (.rational reading) _
      ((PolynomialResidual.exact reading.value).transport reading.equivalent)
  /-- An original root uses its same stored numerical certificate. -/
  | root {channel : CoherentNamed} (sidecar : PolynomialRoot.Sidecar channel) : Cached (.root sidecar)
      sidecar.residualCertificate.1 sidecar.residualCertificate.2
  /-- Use the same actual restarted residual while retaining its original owner and restart certificate. -/
  | recondition {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
      {track : CoherentRoot.WindingOneTrack polynomial ambient} {start : Nat}
      (original : CoherentRoot.CertifiedName track) (input : FTA.Squarefree.Input polynomial)
      (prepared : CoherentRoot.Reconditioning original start) :
      Cached (.recondition original input prepared) polynomial (prepared.residualCertificate input)
  /-- An arithmetic cache consumes the actual retained residuals of both original children. -/
  | arithmetic {first second : CoherentNamed} {left : Origin first} {right : Origin second}
      {firstPolynomial secondPolynomial} {firstResidual : PolynomialResidual firstPolynomial first}
      {secondResidual : PolynomialResidual secondPolynomial second}
      (operation : Operation) (leftCache : Cached left firstPolynomial firstResidual)
      (rightCache : Cached right secondPolynomial secondResidual)
      (result : PolynomialArithmetic operation firstResidual secondResidual) :
      Cached (.arithmetic operation left right) result.polynomial result.residualCertificate
  /-- Zero power keeps the same original child cache and the original constant-one residual program. -/
  | powZero {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (child : Cached original polynomial residual) :
      Cached (.powZero original) _
        ((PolynomialResidual.exact 1).transport (RationalSidecar.exact 1).equivalent)
  /-- The original quadratic sum retains both child caches and its computed quartic numerical evidence. -/
  | quadraticSum {first second : CoherentNamed} {left : Origin first} {right : Origin second}
      {firstPolynomial secondPolynomial} {firstResidual : PolynomialResidual firstPolynomial first}
      {secondResidual : PolynomialResidual secondPolynomial second} (firstParameter secondParameter :
        Rational)
      (leftCache : Cached left firstPolynomial firstResidual)
      (rightCache : Cached right secondPolynomial secondResidual)
      (first_eq : firstPolynomial = Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩)
      (second_eq : secondPolynomial =
        Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩)
      (result : PolynomialResidual.QuadraticSum (first_eq ▸ firstResidual) (second_eq ▸ secondResidual)) :
      Cached (.arithmetic .add left right) (PolynomialResidual.QuadraticSum.polynomial firstParameter secondParameter)
        result.residualCertificate
  /-- Negation consumes the same original child cache through degree-preserving negative-argument substitution. -/
  | neg {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (cache : Cached original polynomial residual) :
      Cached (.neg original) (Negation.negateVariable polynomial) residual.neg
  /-- Conjugation consumes the same original child cache and residual sample program. -/
  | conj {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (cache : Cached original polynomial residual) :
      Cached (.conj original) (Purelib.Polynomial.Dense.Gaussian.Conjugation.conjugate polynomial) residual.conj
  /-- Reciprocal preparation consumes the original child residual and same stored paid inverse cache. -/
  | reciprocal {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (cache : Cached original polynomial residual)
      (prepared : Division.Prepared channel) (result : PolynomialResidual.Reciprocal residual prepared) :
      Cached (.reciprocal original prepared) result.annihilator result.residualCertificate
  /-- Transport consumes the same retained original cache and explicit channel comparison. -/
  | transport {first second : CoherentNamed} {original : Origin first} {polynomial}
      {residual : PolynomialResidual polynomial first} (cache : Cached original polynomial residual)
      (equivalent : NamedEquivalent second.name first.name) :
      Cached (.transport original equivalent) polynomial (residual.transport equivalent)

  /-- Saved observations consume the same original construction cache at its unchanged polynomial and channel. -/
  | samples {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (child : Cached original polynomial residual)
      (observations : Sequence.SamplePrefix residual.source.toApproximation) :
      Cached original polynomial (residual.withSamples observations)

  /-- Saved original root observations retain the original child cache and every actual restored root-state entry. -/
  | rootSamples {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (child : Cached original polynomial residual)
      {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
      {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient}
      (root : CoherentRoot.CertifiedName track) (entries : List (CoherentRoot.StateCache.Entry track))
      (same : ∀ index, root.approximation.sample index = residual.source.sample index) :
      Cached original polynomial (residual.withSamples (root.samplesFor residual.source.toApproximation same entries))

  /-- Retain one computed result localization and the same stored root descriptor on the unchanged operation channel. -/
  | selected {channel : CoherentNamed} {original : Origin channel} {polynomial}
      {residual : PolynomialResidual polynomial channel} (child : Cached original polynomial residual)
      (preparation : Preparation polynomial residual.source)
      (selection : Preparation.Selection preparation) (selection_eq : selection = preparation.select)
      (root : PolynomialRoot.Sidecar channel) (root_eq : root = PolynomialRoot.Sidecar.ofSelection
        residual preparation selection)
      (inspection : Option (PolynomialRoot.Sidecar.PointInspection root) := none) :
      Cached original root.residualCertificate.1 root.residualCertificate.2

  /-- A paid original-root restart preserves the original child cache and its explicitly selected geometric schedule. -/
  | reconditioned {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
      {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient} {start : Nat}
      (root : CoherentRoot.CertifiedName track) {original : Origin root.value} {polynomial}
      {residual : PolynomialResidual polynomial root.value} (child : Cached original polynomial residual)
      (input : FTA.Squarefree.Input sourcePolynomial) (prepared : CoherentRoot.Reconditioning root start)
      (same : sourcePolynomial = polynomial) :
      Cached original polynomial (same ▸ prepared.scheduledResidual input)

constructive_injectivity Cached

set_option genInjectivity false in
/-- One original algebraic construction with its actual retained polynomial, residual program and cache witnesses. -/
structure Sidecar (channel : CoherentNamed) where
  /-- The original finite construction and its retained input owners. -/
  origin : Origin channel
  /-- The numerical annihilating polynomial computed for this same construction. -/
  polynomial : CoefficientPolynomial
  /-- The actual retained quantitative residual program on the original channel. -/
  residual : PolynomialResidual polynomial channel
  /-- The numerical certificate consumes the retained caches of this original construction. -/
  cached : Cached origin polynomial residual

constructive_injectivity Sidecar

/-- Read an already retained original root sidecar through cache-preserving wrappers.

A root returns its entire supplied owner, source index and numerical cache.
Channel transport uses the original root-sidecar transport; saved observation
wrappers keep the same root view. Other constructions remain unclassified
rather than synthesizing a root owner from their coefficient polynomial.
-/
@[expose] def Cached.root? {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual) :
    Option (PolynomialRoot.Sidecar channel) :=
  match cached with
  | .root original => some original
  | .selected _ _ _ _ selectedRoot _ _ => some selectedRoot
  | .transport child equivalent => (child.root?).map (fun original => original.transport equivalent)
  | .samples child _ => child.root?
  | .rootSamples child _ _ _ => child.root?
  | .reconditioned _ child _ _ _ => child.root?
  | .rational _ | .powZero _ | .recondition _ _ _ | .arithmetic _ _ _ _ | .quadraticSum _ _ _ _ _ _ _ |
    .neg _ | .conj _ | .reciprocal _ _ _ => none

/-- The intrinsic root view is the complete original supplied root sidecar. -/
theorem Cached.root?_root {channel : CoherentNamed} (original : PolynomialRoot.Sidecar channel) :
    (Cached.root original).root? = some original := rfl

/-- Saving original scalar observations preserves the same complete intrinsic root view. -/
theorem Cached.root?_samples {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual)
    (observations : Sequence.SamplePrefix residual.source.toApproximation) :
    (Cached.samples cached observations).root? = cached.root? := rfl

/-- Read a computed result selection while preserving the original isolated and admitted root routes. -/
@[expose] def Cached.selectedRoot? {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual) :
    Option (PolynomialRoot.Sidecar channel) :=
  match cached.root? with
  | some retained => match retained.owner with
      | .selected _ _ _ => some retained
      | .isolated _ _ | .admitted _ | .realized _ => none
  | none => none

/-- Read scalar evidence through the actual retained arithmetic and paid reciprocal child caches.

A zero multiplication operand is read through its retained child cache and
original multiplication laws; the other child is preserved. Each success
concerns the unchanged original channel. A reciprocal consumes
the same original preparation and derives coefficient nonzero from that
certificate; no repeated root localization or replacement inverse is used.
-/
@[expose] def Cached.scalar? {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual) :
    Option (RationalSidecar channel) :=
  match cached with
  | .rational reading => some reading
  | .powZero _ => some (RationalSidecar.exact 1)
  | .root sidecar => match sidecar.scalar? with
      | some reading => some reading
      | none => sidecar.residualCertificate.2.scalar?
  | .recondition _ input prepared => (prepared.residualCertificate input).scalar?
  | .selected child _ _ _ selectedRoot _ inspection =>
      match child.scalar? with
      | some reading => some reading
      | none => match inspection with
          | none => selectedRoot.scalar?
          | some retained => match selectedRoot.scalar? with
              | some reading => some reading
              | none => retained.reading
  | .arithmetic (first := firstChannel) (second := secondChannel) operation left right result =>
      match left.scalar?, right.scalar? with
      | some first, some second => match operation with
          | .add => some (first.add second)
          | .mul => some (first.mul second)
      | some first, none => match operation with
          | .add => result.residualCertificate.scalar?
          | .mul => if zero : first.value = 0 then
              some (RationalSidecar.zero
                (NamedEquivalent.trans
                  (by simpa only [zero, PolynomialArithmetic.channel, CoherentNamed.mul, CoherentNamed.Coherence.exact]
                    using Arithmetic.Mul.mulLeftConstant firstChannel secondChannel first)
                  (Arithmetic.Mul.coherentMul_zero_left secondChannel)))
            else result.residualCertificate.scalar?
      | none, some second => match operation with
          | .add => result.residualCertificate.scalar?
          | .mul => if zero : second.value = 0 then
              some (RationalSidecar.zero
                (NamedEquivalent.trans
                  (by simpa only [zero, PolynomialArithmetic.channel, CoherentNamed.mul, CoherentNamed.Coherence.exact]
                    using Arithmetic.Mul.mulRightConstant firstChannel secondChannel second)
                  (Arithmetic.Mul.coherentMul_zero_right firstChannel)))
            else result.residualCertificate.scalar?
      | none, none => result.residualCertificate.scalar?
  | .quadraticSum _ _ left right _ _ result =>
      match left.scalar?, right.scalar? with
      | some first, some second => some (first.add second)
      | _, _ => result.residualCertificate.scalar?
  | .neg child => match child.scalar? with
      | none => none
      | some reading => some (Rational.Arithmetic.negateRational reading)
  | .conj child => match child.scalar? with
      | none => none
      | some reading => some ⟨Purelib.Data.Gaussian.Basic.Canonical.conj reading.value,
          (CoherentNamed.conj_respects reading.equivalent).trans (CoherentNamed.conj_exact reading.value)⟩
  | .reciprocal child prepared _ => match child.scalar? with
      | none => none
      | some reading =>
          have nonzero : reading.value ≠ 0 := fun zero =>
            Division.Obstruction.Zero.ZeroIdentity.incompatible_prepared
              (Rational.Arithmetic.rationalZero reading zero) prepared
          some (reading.reciprocal prepared nonzero)
  | .transport child equivalent => match child.scalar? with
      | none => none
      | some reading => some ⟨reading.value, equivalent.trans reading.equivalent⟩
  | .samples child _ => child.scalar?
  | .rootSamples child _ _ _ => child.scalar?
  | .reconditioned _ child _ _ _ => child.scalar?

namespace Cached

/-- Conjugation preserves the absence of a retained scalar reading. -/
theorem scalar?_conj_of_none {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (child : Cached origin polynomial residual)
    (missing : child.scalar? = none) : (Cached.conj child).scalar? = none := by
  change (match child.scalar? with
    | none => none
    | some reading => some ⟨Purelib.Data.Gaussian.Basic.Canonical.conj reading.value,
        (CoherentNamed.conj_respects reading.equivalent).trans
          (CoherentNamed.conj_exact reading.value)⟩) =
    (none : Option (RationalSidecar (CoherentNamed.conj channel)))
  rewrite [missing]
  rfl

/-- Demand exact candidate inspection only at an existing original selected cache.

A stored inspection returns before child traversal or reconstruction. Existing
scalar and linear readings keep precedence; only an unclassified selected
root executes the actual original point-inspection procedure. Transparent
cache wrappers retain their original fields and the same stored Root Sidecar.
-/
def inspectExact {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual) (start : Nat) :
    Cached origin polynomial residual :=
  match cached with
  | .selected child preparation selection selectionComputed retainedRoot rootComputed inspection =>
      let selectedCache := Cached.selected child preparation selection selectionComputed retainedRoot rootComputed
        inspection
      match inspection with
      | some _ => selectedCache
      | none => match child.scalar? with
          | some _ => selectedCache
          | none => match retainedRoot.scalar? with
              | some _ => selectedCache
              | none => .selected child preparation selection selectionComputed retainedRoot rootComputed
                  (some (PolynomialRoot.Sidecar.PointInspection.build retainedRoot start))
  | .transport child equivalent => .transport (child.inspectExact start) equivalent
  | .samples child observations => .samples (child.inspectExact start) observations
  | .rootSamples child retainedRoot entries same => .rootSamples (child.inspectExact start) retainedRoot entries same
  | .reconditioned retainedRoot child input prepared same =>
      .reconditioned retainedRoot (child.inspectExact start) input prepared same
  | .rational reading => .rational reading
  | .powZero child => .powZero child
  | .root sidecar => .root sidecar
  | .recondition original input prepared => .recondition original input prepared
  | .arithmetic operation left right result => .arithmetic operation left right result
  | .quadraticSum first second left right first_eq second_eq result =>
      .quadraticSum first second left right first_eq second_eq result
  | .neg child => .neg child
  | .conj child => .conj child
  | .reciprocal child prepared result => .reciprocal child prepared result

/-- An already retained inspection preserves the complete selected cache before any child or candidate work. -/
theorem inspectExact_retained {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (child : Cached origin polynomial residual)
    (preparation : Preparation polynomial residual.source) (selection : Preparation.Selection preparation)
    (selectionComputed : selection = preparation.select) (root : PolynomialRoot.Sidecar channel)
    (rootComputed : root = PolynomialRoot.Sidecar.ofSelection residual preparation selection)
    (inspection : PolynomialRoot.Sidecar.PointInspection root) (start : Nat) :
    (Cached.selected child preparation selection selectionComputed root rootComputed (some inspection)).inspectExact
        start = Cached.selected child preparation selection selectionComputed root rootComputed (some inspection) := by
  unfold inspectExact
  rfl

/-- An absent selected inspection preserves the complete old scalar-readback procedure. -/
theorem scalar?_selected_none {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (child : Cached origin polynomial residual)
    (preparation : Preparation polynomial residual.source) (selection : Preparation.Selection preparation)
    (selectionComputed : selection = preparation.select) (root : PolynomialRoot.Sidecar channel)
    (rootComputed : root = PolynomialRoot.Sidecar.ofSelection residual preparation selection) :
    (Cached.selected child preparation selection selectionComputed root rootComputed none).scalar? =
      (match child.scalar? with | some reading => some reading | none => root.scalar?) := by
  change (match child.scalar? with | some reading => some reading | none => root.scalar?) = _
  rfl

/-- Only the literal retained point-inspection result supplies a new exact reading after both original readers fail. -/
theorem scalar?_selected_inspection {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (child : Cached origin polynomial residual)
    (preparation : Preparation polynomial residual.source) (selection : Preparation.Selection preparation)
    (selectionComputed : selection = preparation.select) (root : PolynomialRoot.Sidecar channel)
    (rootComputed : root = PolynomialRoot.Sidecar.ofSelection residual preparation selection)
    (inspection : PolynomialRoot.Sidecar.PointInspection root)
    (noChild : child.scalar? = none) (noRoot : root.scalar? = none) :
    (Cached.selected child preparation selection selectionComputed root rootComputed (some inspection)).scalar? =
      inspection.reading := by
  change (match child.scalar? with
    | some reading => some reading
    | none => match root.scalar? with | some reading => some reading | none => inspection.reading) = _
  rewrite [noChild, noRoot]
  rfl

/-- A first demand with no existing scalar evidence stores exactly the actual original inspection result once. -/
theorem inspectExact_selected {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (child : Cached origin polynomial residual)
    (preparation : Preparation polynomial residual.source) (selection : Preparation.Selection preparation)
    (selectionComputed : selection = preparation.select) (root : PolynomialRoot.Sidecar channel)
    (rootComputed : root = PolynomialRoot.Sidecar.ofSelection residual preparation selection)
    (start : Nat) (noChild : child.scalar? = none) (noRoot : root.scalar? = none) :
    (Cached.selected child preparation selection selectionComputed root rootComputed none).inspectExact start =
      Cached.selected child preparation selection selectionComputed root rootComputed
        (some (PolynomialRoot.Sidecar.PointInspection.build root start)) := by
  unfold Cached.inspectExact
  rewrite [noChild, noRoot]
  rfl

/-- Exact candidate inspection preserves the same entire original Root Sidecar at every supported cache wrapper. -/
theorem root?_inspectExact {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual) (start : Nat) :
    (cached.inspectExact start).root? = cached.root? := by
  induction cached with
  | rational _ => rfl
  | powZero _ _ => rfl
  | root _ => rfl
  | recondition _ _ _ => rfl
  | arithmetic _ _ _ _ _ _ => rfl
  | quadraticSum _ _ _ _ _ _ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ => rfl
  | reciprocal _ _ _ _ => rfl
  | selected child _ _ _ root _ inspection _ =>
      cases inspection with
      | some _ => rfl
      | none =>
          unfold inspectExact
          cases child.scalar? with
          | some _ => rfl
          | none => cases root.scalar? <;> rfl
  | transport child equivalent previous =>
      change (child.inspectExact start).root?.map (fun original => original.transport equivalent) = _
      rewrite [previous]
      rfl
  | reconditioned root child input prepared same previous => exact previous
  | samples child observations previous => exact previous
  | rootSamples child root entries same previous => exact previous

/-- Repeated demands retain the complete first cache, including its original start and failed point attempts. -/
theorem inspectExact_idempotent {channel : CoherentNamed} {origin : Origin channel} {polynomial}
    {residual : PolynomialResidual polynomial channel} (cached : Cached origin polynomial residual)
    (first second : Nat) : (cached.inspectExact first).inspectExact second = cached.inspectExact first := by
  induction cached with
  | rational _ => rfl
  | powZero _ _ => rfl
  | root _ => rfl
  | recondition _ _ _ => rfl
  | arithmetic _ _ _ _ _ _ => rfl
  | quadraticSum _ _ _ _ _ _ _ _ _ => rfl
  | neg _ _ => rfl
  | conj _ _ => rfl
  | reciprocal _ _ _ _ => rfl
  | selected child preparation selection computed retainedRoot rootComputed inspection _ =>
      cases inspection with
      | some _ => rfl
      | none =>
          cases childRead : child.scalar? with
          | some _ =>
              have unchanged (index : Nat) :
                  (Cached.selected child preparation selection computed retainedRoot rootComputed none).inspectExact
                    index = Cached.selected child preparation selection computed retainedRoot rootComputed none := by
                unfold inspectExact
                rewrite [childRead]
                rfl
              rewrite [unchanged first, unchanged second]
              rfl
          | none =>
              cases rootRead : retainedRoot.scalar? with
              | some _ =>
                  have unchanged (index : Nat) :
                      (Cached.selected child preparation selection computed retainedRoot rootComputed none).inspectExact
                        index = Cached.selected child preparation selection computed retainedRoot rootComputed none :=
                    by
                    unfold inspectExact
                    rewrite [childRead, rootRead]
                    rfl
                  rewrite [unchanged first, unchanged second]
                  rfl
              | none =>
                  rewrite [inspectExact_selected child preparation selection computed retainedRoot rootComputed first
                    childRead rootRead]
                  exact inspectExact_retained child preparation selection computed retainedRoot rootComputed _ second
  | transport child equivalent previous =>
      change Cached.transport ((child.inspectExact first).inspectExact second) equivalent = _
      exact congrArg (fun retained => Cached.transport retained equivalent) previous
  | samples child observations previous =>
      change Cached.samples ((child.inspectExact first).inspectExact second) observations = _
      exact congrArg (fun retained => Cached.samples retained observations) previous
  | rootSamples child root entries same previous =>
      change Cached.rootSamples ((child.inspectExact first).inspectExact second) root entries same = _
      exact congrArg (fun retained => Cached.rootSamples retained root entries same) previous
  | reconditioned root child input prepared same previous =>
      change Cached.reconditioned root ((child.inspectExact first).inspectExact second) input prepared same = _
      exact congrArg (fun retained => Cached.reconditioned root retained input prepared same) previous

end Cached

namespace Sidecar

/-- Attach an original scalar reading and its exact numerical residual once. -/
@[expose] def ofRational {channel : CoherentNamed} (reading : RationalSidecar channel) : Sidecar channel :=
  ⟨.rational reading, _, (PolynomialResidual.exact reading.value).transport reading.equivalent, .rational reading⟩

/-- Attach an original root sidecar using its same retained owner residual. -/
@[expose] def ofRoot {channel : CoherentNamed} (sidecar : PolynomialRoot.Sidecar channel) : Sidecar channel :=
  let numerical := sidecar.residualCertificate
  ⟨.root sidecar, numerical.1, numerical.2, .root sidecar⟩

/-- Root sidecars retain the same original owner's displayed numerical polynomial. -/
theorem ofRoot_polynomial {channel : CoherentNamed} (sidecar : PolynomialRoot.Sidecar channel) :
    (ofRoot sidecar).polynomial = sidecar.residualCertificate.1 := rfl

/-- Root sidecars read the same actual original owner cache in every numerical residual sample. -/
theorem ofRoot_sample {channel : CoherentNamed} (sidecar : PolynomialRoot.Sidecar channel) (index : Nat) :
    (ofRoot sidecar).residual.source.sample index = sidecar.residualCertificate.2.source.sample index := rfl

/-- Optionally inspect the same existing selected cache without changing any original owner or numerical field.

An absent request returns the complete supplied Sidecar. A present request
retains the actual original point-inspection result only where a selected
cache already exists; no decomposition or root selection is constructed here.
-/
@[expose] def inspectExact {channel : CoherentNamed} (original : Sidecar channel)
    (request : Option Nat := none) : Sidecar channel :=
  match request with
  | none => original
  | some start => ⟨original.origin, original.polynomial, original.residual, original.cached.inspectExact start⟩

/-- An absent exact-inspection request preserves the complete original Sidecar and all its caches. -/
theorem inspectExact_none {channel : CoherentNamed} (original : Sidecar channel) :
    original.inspectExact none = original := rfl

/-- Exact inspection preserves the entire original construction and ordered input parents. -/
theorem inspectExact_origin {channel : CoherentNamed} (original : Sidecar channel) (request : Option Nat) :
    (original.inspectExact request).origin = original.origin := by cases request <;> rfl

/-- Exact inspection preserves the original complete numerical polynomial and residual object. -/
theorem inspectExact_numerical {channel : CoherentNamed} (original : Sidecar channel) (request : Option Nat) :
    (original.inspectExact request).polynomial = original.polynomial ∧
      HEq (original.inspectExact request).residual original.residual := by
  cases request <;> exact ⟨rfl, HEq.rfl⟩

/-- Exact inspection retains the same complete original selected Root Sidecar and its parent identities. -/
theorem inspectExact_root {channel : CoherentNamed} (original : Sidecar channel) (request : Option Nat) :
    (original.inspectExact request).cached.root? = original.cached.root? := by
  cases request with
  | none => rfl
  | some start => exact Cached.root?_inspectExact original.cached start

/-- Repeated inspection retains the first complete Sidecar and its original candidate and point data. -/
theorem inspectExact_idempotent {channel : CoherentNamed} (original : Sidecar channel) (first second : Nat) :
    (original.inspectExact (some first)).inspectExact (some second) =
      original.inspectExact (some first) := by
  cases original with
  | mk origin polynomial residual cached =>
      change Sidecar.mk origin polynomial residual ((cached.inspectExact first).inspectExact second) = _
      exact congrArg (fun retained => Sidecar.mk origin polynomial residual retained)
        (Cached.inspectExact_idempotent cached first second)

/-- Consume a retained result selection while preserving the complete original construction and all its input caches.

The actual output channel stays unchanged. The new numerical factor residual
reads the same stored selected root cache; the complete original annihilator,
residual and ordered input parents remain in the retained child. The supplied
selection equation links this one selection to its actual finite producer.
-/
@[expose] def withSelection {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select)
    (exactStart : Option Nat := none) : Sidecar channel :=
  let root := PolynomialRoot.Sidecar.ofSelection original.residual preparation selection
  let numerical := root.residualCertificate
  let selected : Sidecar channel := ⟨original.origin, numerical.1, numerical.2,
    .selected original.cached preparation selection selectionComputed root rfl none⟩
  selected.inspectExact exactStart

/-- An absent candidate demand preserves the complete original selected Sidecar construction and cache. -/
theorem withSelection_none {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select) :
    original.withSelection preparation selection selectionComputed none =
      (let root := PolynomialRoot.Sidecar.ofSelection original.residual preparation selection
       let numerical := root.residualCertificate
       ⟨original.origin, numerical.1, numerical.2,
         .selected original.cached preparation selection selectionComputed root rfl none⟩) := rfl

/-- Result selection preserves the complete original construction and ordered original input parents. -/
theorem withSelection_origin {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select) :
    (original.withSelection preparation selection selectionComputed).origin = original.origin := rfl

/-- The selected result exposes the same complete stored root descriptor, with its full original annihilator. -/
theorem withSelection_root {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select) :
    (original.withSelection preparation selection selectionComputed).cached.root? =
      some (PolynomialRoot.Sidecar.ofSelection original.residual preparation selection) := rfl

/-- The computed result-selection view returns the same complete stored root descriptor. -/
theorem withSelection_selectedRoot {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select) :
    (original.withSelection preparation selection selectionComputed).cached.selectedRoot? =
      some (PolynomialRoot.Sidecar.ofSelection original.residual preparation selection) := rfl

/-- Result selection preserves an exact reading already retained by the original construction cache. -/
theorem withSelection_scalar {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select)
    (reading : RationalSidecar channel) (retained : original.cached.scalar? = some reading) :
    (original.withSelection preparation selection selectionComputed).cached.scalar? = some reading := by
  change (match original.cached.scalar? with
    | some saved => some saved
    | none => _) = some reading
  rewrite [retained]
  rfl

/-- Compute and retain result identification once when no original root or exact scalar evidence is already present.

The original residual supplies its own finite localization bounds and stable
selection. Existing scalar and root evidence return the unchanged sidecar.
The selected result keeps the full original construction, so mixed-root
arithmetic and conjugation never replace their actual input owners.
-/
@[expose] def identify {channel : CoherentNamed} (original : Sidecar channel)
    (exactStart : Option Nat := none) : Sidecar channel :=
  let identified := match original.cached.root? with
    | some _ => original
    | none => match original.cached.scalar? with
        | some _ => original
        | none =>
            let preparation := original.residual.prepareLocalization
            let selection := preparation.select
            original.withSelection preparation selection rfl
  identified.inspectExact exactStart

/-- An absent exact-candidate demand preserves the complete previous result-identification procedure. -/
theorem identify_none {channel : CoherentNamed} (original : Sidecar channel) :
    original.identify none =
      (match original.cached.root? with
      | some _ => original
      | none => match original.cached.scalar? with
          | some _ => original
          | none =>
              let preparation := original.residual.prepareLocalization
              let selection := preparation.select
              original.withSelection preparation selection rfl) := rfl

/-- A retained original root makes identification preserve the same complete sidecar without another localization. -/
theorem identify_of_root {channel : CoherentNamed} (original : Sidecar channel)
    (root : PolynomialRoot.Sidecar channel) (retained : original.cached.root? = some root) :
    original.identify = original := by
  unfold identify
  rewrite [retained]
  rfl

/-- A stored computed selection makes repeated identification preserve the same complete sidecar and all its caches. -/
theorem identify_withSelection {channel : CoherentNamed} (original : Sidecar channel)
    (preparation : Preparation original.polynomial original.residual.source)
    (selection : Preparation.Selection preparation) (selectionComputed : selection = preparation.select) :
    (original.withSelection preparation selection selectionComputed).identify =
      original.withSelection preparation selection selectionComputed :=
  identify_of_root _ (PolynomialRoot.Sidecar.ofSelection original.residual preparation selection)
    (withSelection_root original preparation selection selectionComputed)

/-- Identification preserves the complete original construction and ordered original input parents. -/
theorem identify_origin {channel : CoherentNamed} (original : Sidecar channel) :
    original.identify.origin = original.origin := by
  unfold identify
  cases original.cached.root? with
  | some root => rfl
  | none =>
      cases original.cached.scalar? with
      | some reading => rfl
      | none => rfl

/-- Attach the original root owner and actual restarted samples on the unchanged original numerical channel.

The retained restart reuses its paid original cache state. Its exact residual
certificate supplies the same original polynomial and actual restarted sample
program; subsequent construction nodes retain this origin rather than replacing
it with the restarted root owner.
-/
@[expose] def ofReconditioning {polynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {start : Nat}
    (original : CoherentRoot.CertifiedName track) (input : FTA.Squarefree.Input polynomial)
    (prepared : CoherentRoot.Reconditioning original start) : Sidecar original.value :=
  ⟨.recondition original input prepared, polynomial, prepared.residualCertificate input,
    .recondition original input prepared⟩

/-- Compute one arithmetic node using both original stored numerical residuals. -/
@[expose] def arithmetic {first second : CoherentNamed} (operation : Operation)
    (left : Sidecar first) (right : Sidecar second) :
    Sidecar (PolynomialArithmetic.channel operation first second) :=
  let result := PolynomialArithmetic.ofResiduals operation left.residual right.residual
  ⟨.arithmetic operation left.origin right.origin, result.polynomial, result.residualCertificate,
    .arithmetic operation left.cached right.cached result⟩

/-- Generic arithmetic reads the operation on both same retained input residual samples. -/
theorem arithmetic_sample {first second : CoherentNamed} (operation : Operation)
    (left : Sidecar first) (right : Sidecar second) (index : Nat) :
    (left.arithmetic operation right).residual.source.sample index =
      operation.value (left.residual.source.sample index) (right.residual.source.sample index) := by
  change (PolynomialArithmetic.ofResiduals operation left.residual right.residual).result.sample index = _
  let result := PolynomialArithmetic.ofResiduals operation left.residual right.residual
  have reading := result.result_sample index
  rewrite [result.first_eq, result.second_eq] at reading
  exact reading

/-- Retain both original quadratic child caches and compute their quartic residual on the unchanged sum channel. -/
@[expose] def quadraticSum {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstParameter secondParameter : Rational)
    (first_eq : left.polynomial = Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩)
    (second_eq : right.polynomial =
      Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) :
    Sidecar (CoherentNamed.add first second) :=
  let result := PolynomialResidual.QuadraticSum.ofResiduals (first_eq ▸ left.residual) (second_eq ▸ right.residual)
  ⟨.arithmetic .add left.origin right.origin, _, result.residualCertificate,
    .quadraticSum firstParameter secondParameter left.cached right.cached first_eq second_eq result⟩

/-- A specialized quadratic sum reads both original child residual samples at the same index. -/
theorem quadraticSum_sample {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (firstParameter secondParameter : Rational)
    (first_eq : left.polynomial = Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩)
    (second_eq : right.polynomial =
      Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩) (index : Nat) :
    (left.quadraticSum right firstParameter secondParameter first_eq second_eq).residual.source.sample index =
      left.residual.source.sample index + right.residual.source.sample index := by
  unfold quadraticSum
  let result := PolynomialResidual.QuadraticSum.ofResiduals (first_eq ▸ left.residual) (second_eq ▸ right.residual)
  have reading := result.residualCertificate_sample index
  rewrite [result.first_eq, result.second_eq] at reading
  exact reading.trans (congrArg₂ (· + ·)
    (congrArg (fun source => source.sample index)
      (PolynomialResidual.cast_polynomial_source first_eq left.residual))
    (congrArg (fun source => source.sample index)
      (PolynomialResidual.cast_polynomial_source second_eq right.residual)))

/-- Recognize two actual real pure-quadratic coefficient tables and retain the same original sum inputs.

Every test concerns the original cached polynomials. A mismatch returns no
specialized certificate; the complete generic arithmetic route remains available.
-/
@[expose] def quadraticSum? {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Option (Sidecar (CoherentNamed.add first second)) :=
  if left.polynomial.natDegree = 2 ∧ right.polynomial.natDegree = 2 then
    let firstParameter := (-left.polynomial.eval 0).re
    let secondParameter := (-right.polynomial.eval 0).re
    if first_eq : left.polynomial =
        Power.Gaussian.rootPolynomial ⟨firstParameter, 0⟩ ⟨2, by decide⟩ then
      if second_eq : right.polynomial =
          Power.Gaussian.rootPolynomial ⟨secondParameter, 0⟩ ⟨2, by decide⟩ then
        some (left.quadraticSum right firstParameter secondParameter first_eq second_eq)
      else none
    else none
  else none

/-- Every recognized quadratic-sum candidate reads the same original child samples. -/
theorem quadraticSum?_sample {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (result : Sidecar (CoherentNamed.add first second)) (same : left.quadraticSum? right = some result)
    (index : Nat) : result.residual.source.sample index =
      left.residual.source.sample index + right.residual.source.sample index := by
  unfold quadraticSum? at same
  split at same
  · dsimp only at same
    split at same
    · split at same
      · have identity := Option.some.inj same
        rewrite [← identity]
        exact quadraticSum_sample left right _ _ _ _ index
      · cases same
    · cases same
  · cases same

/-- Add the original channels using their retained quadratic-sum certificate or complete generic arithmetic cache. -/
@[expose] def add {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Sidecar (CoherentNamed.add first second) :=
  match left.quadraticSum? right with
  | some result => result
  | none => left.arithmetic .add right

/-- Addition preserves original child samples through its actual specialized or generic dispatch. -/
theorem add_sample {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second)
    (index : Nat) : (left.add right).residual.source.sample index =
      left.residual.source.sample index + right.residual.source.sample index := by
  unfold add
  split
  · rename_i result same
    exact quadraticSum?_sample left right result same index
  · exact arithmetic_sample .add left right index

/-- Multiply the original channels using the actual stored residuals of both finite constructions. -/
@[expose] def mul {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Sidecar (CoherentNamed.mul first second) := left.arithmetic .mul right

/-- Transport the original construction and same numerical sample cache along its supplied comparison. -/
@[expose] def transport {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : NamedEquivalent second.name first.name) : Sidecar second :=
  ⟨.transport sidecar.origin equivalent, sidecar.polynomial, sidecar.residual.transport equivalent,
    .transport sidecar.cached equivalent⟩

/-- Channel transport reads the same original residual sample at every unchanged primitive index. -/
theorem transport_sample {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : NamedEquivalent second.name first.name) (index : Nat) :
    (sidecar.transport equivalent).residual.source.sample index = sidecar.residual.source.sample index := by
  change (sidecar.residual.transport equivalent).source.sample index = _
  rewrite [PolynomialResidual.transport_source]
  rfl

/-- Consume checked saved observations while retaining the complete original construction and its child cache. -/
@[expose] def withSamples {channel : CoherentNamed} (sidecar : Sidecar channel)
    (observations : Sequence.SamplePrefix sidecar.residual.source.toApproximation) : Sidecar channel :=
  ⟨sidecar.origin, sidecar.polynomial, sidecar.residual.withSamples observations,
    .samples sidecar.cached observations⟩

/-- Consume exact saved root states while retaining the original sidecar, child cache and restored state entries. -/
@[expose] def withRootSamples {channel : CoherentNamed} (sidecar : Sidecar channel)
    {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient}
    (root : CoherentRoot.CertifiedName track) (entries : List (CoherentRoot.StateCache.Entry track))
    (same : ∀ index, root.approximation.sample index = sidecar.residual.source.sample index) : Sidecar channel :=
  ⟨sidecar.origin, sidecar.polynomial,
    sidecar.residual.withSamples (root.samplesFor sidecar.residual.source.toApproximation same entries),
    .rootSamples sidecar.cached root entries same⟩

/-- Saved root-state lookup retains the exact original finite construction. -/
theorem withRootSamples_origin {channel : CoherentNamed} (sidecar : Sidecar channel)
    {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient}
    (root : CoherentRoot.CertifiedName track) (entries : List (CoherentRoot.StateCache.Entry track))
    (same : ∀ index, root.approximation.sample index = sidecar.residual.source.sample index) :
    (sidecar.withRootSamples root entries same).origin = sidecar.origin := rfl

/-- Saved root-state lookup retains the original child cache, root owner and every actual restored state. -/
theorem withRootSamples_cached {channel : CoherentNamed} (sidecar : Sidecar channel)
    {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient}
    (root : CoherentRoot.CertifiedName track) (entries : List (CoherentRoot.StateCache.Entry track))
    (same : ∀ index, root.approximation.sample index = sidecar.residual.source.sample index) :
    (sidecar.withRootSamples root entries same).cached = Cached.rootSamples sidecar.cached root entries same := rfl

/-- Every saved root-state observation is the same original sidecar's scalar reading at its unchanged index. -/
theorem withRootSamples_sample {channel : CoherentNamed} (sidecar : Sidecar channel)
    {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient}
    (root : CoherentRoot.CertifiedName track) (entries : List (CoherentRoot.StateCache.Entry track))
    (same : ∀ index, root.approximation.sample index = sidecar.residual.source.sample index) (index : Nat) :
    (sidecar.withRootSamples root entries same).residual.source.sample index = sidecar.residual.source.sample index :=
  sidecar.residual.withSamples_sample _ index

/-- Retain an original sidecar and its actual paid restart through an explicit computed geometric comparison.

The input channel and original construction remain unchanged. The actual
restart supplies the new numerical source, and the original child cache and
zero-to-positive-index payment remain in the retained construction cache.
-/
@[expose] def withReconditioning {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient} {start : Nat}
    (root : CoherentRoot.CertifiedName track) (sidecar : Sidecar root.value)
    (input : FTA.Squarefree.Input sourcePolynomial) (prepared : CoherentRoot.Reconditioning root start)
    (same : sourcePolynomial = sidecar.polynomial) : Sidecar root.value :=
  ⟨sidecar.origin, sidecar.polynomial, same ▸ prepared.scheduledResidual input,
    .reconditioned root sidecar.cached input prepared same⟩

/-- Paid reconditioning reads the actual restarted program at the same primitive sample index. -/
theorem withReconditioning_sample {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient} {start : Nat}
    (root : CoherentRoot.CertifiedName track) (sidecar : Sidecar root.value)
    (input : FTA.Squarefree.Input sourcePolynomial) (prepared : CoherentRoot.Reconditioning root start)
    (same : sourcePolynomial = sidecar.polynomial) (index : Nat) :
    (withReconditioning root sidecar input prepared same).residual.source.sample index =
      prepared.root.approximation.sample index := by
  change (same ▸ prepared.scheduledResidual input :
    PolynomialResidual sidecar.polynomial root.value).source.sample index = _
  rewrite [PolynomialResidual.cast_polynomial_source same (prepared.scheduledResidual input)]
  change (prepared.root.residualCertificate.transport (prepared.scheduledEquivalent input)).source.sample index = _
  rewrite [PolynomialResidual.transport_source]
  rfl

/-- Paid reconditioning preserves the original finite construction and its input ownership. -/
theorem withReconditioning_origin {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient} {start : Nat}
    (root : CoherentRoot.CertifiedName track) (sidecar : Sidecar root.value)
    (input : FTA.Squarefree.Input sourcePolynomial) (prepared : CoherentRoot.Reconditioning root start)
    (same : sourcePolynomial = sidecar.polynomial) :
    (withReconditioning root sidecar input prepared same).origin = sidecar.origin := rfl

/-- Paid reconditioning keeps the original child cache, root and actual payment with the selected schedule. -/
theorem withReconditioning_cached {sourcePolynomial : CoefficientPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack sourcePolynomial ambient} {start : Nat}
    (root : CoherentRoot.CertifiedName track) (sidecar : Sidecar root.value)
    (input : FTA.Squarefree.Input sourcePolynomial) (prepared : CoherentRoot.Reconditioning root start)
    (same : sourcePolynomial = sidecar.polynomial) :
    (withReconditioning root sidecar input prepared same).cached =
      Cached.reconditioned root sidecar.cached input prepared same := rfl

/-- Saved observation lookup retains the exact original finite construction. -/
theorem withSamples_origin {channel : CoherentNamed} (sidecar : Sidecar channel)
    (observations : Sequence.SamplePrefix sidecar.residual.source.toApproximation) :
    (sidecar.withSamples observations).origin = sidecar.origin := rfl

/-- Saved observation lookup retains the original child cache and actual observation table. -/
theorem withSamples_cached {channel : CoherentNamed} (sidecar : Sidecar channel)
    (observations : Sequence.SamplePrefix sidecar.residual.source.toApproximation) :
    (sidecar.withSamples observations).cached = Cached.samples sidecar.cached observations := rfl

/-- Every saved algebraic observation has the same original scalar readback at its unchanged index. -/
theorem withSamples_sample {channel : CoherentNamed} (sidecar : Sidecar channel)
    (observations : Sequence.SamplePrefix sidecar.residual.source.toApproximation) (index : Nat) :
    (sidecar.withSamples observations).residual.source.sample index = sidecar.residual.source.sample index :=
  sidecar.residual.withSamples_sample observations index

/-- Negate the original stateful channel using its same child cache and negative-argument polynomial substitution.

The numerical program negates the actual original samples at their unchanged
indices. Its polynomial preserves the original degree and residual scale;
the unary construction retains the complete original child owner and cache.
-/
@[expose] def neg {channel : CoherentNamed} (sidecar : Sidecar channel) : Sidecar (CoherentNamed.neg channel) :=
  ⟨.neg sidecar.origin, _, sidecar.residual.neg, .neg sidecar.cached⟩

/-- Negation retains the exact original unary construction owner. -/
theorem neg_origin {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.neg.origin = .neg sidecar.origin := rfl

/-- Negation substitutes the negative argument into the same original coefficient polynomial. -/
theorem neg_polynomial {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.neg.polynomial = Negation.negateVariable sidecar.polynomial := rfl

/-- The unary cache retains the same complete original child cache. -/
theorem neg_cached {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.neg.cached = Cached.neg sidecar.cached := rfl

/-- Negation preserves the original finite polynomial degree. -/
theorem neg_degree {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.neg.polynomial.natDegree = sidecar.polynomial.natDegree :=
  Negation.natDegree sidecar.polynomial

/-- Negation reads the negative of the same retained original indexed numerical sample. -/
theorem neg_sample {channel : CoherentNamed} (sidecar : Sidecar channel) (index : Nat) :
    sidecar.neg.residual.source.sample index = -sidecar.residual.source.sample index := rfl

/-- Negation retains the same original quantitative polynomial error scale. -/
theorem neg_scale {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.neg.residual.scale = sidecar.residual.scale := rfl

/-- Subtract original channels using the actual retained negative-input and sum caches. -/
@[expose] def sub {first second : CoherentNamed} (left : Sidecar first) (right : Sidecar second) :
    Sidecar (CoherentNamed.add first (CoherentNamed.neg second)) := left.add right.neg

/-- Compute natural powers, retaining the original input and every actual intermediate arithmetic cache. -/
@[expose] def pow {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (exponent : Nat) → Sidecar (Name.Coherent.Power.namedPower channel exponent)
  | 0 =>
      ⟨.powZero sidecar.origin, _,
        (PolynomialResidual.exact 1).transport (RationalSidecar.exact 1).equivalent, .powZero sidecar.cached⟩
  | exponent + 1 => (sidecar.pow exponent).mul sidecar

/-- Zero power retains the exact original input owner at its same constant-one output channel. -/
theorem pow_zero_origin {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).origin = .powZero sidecar.origin := rfl

/-- Zero power retains the same complete original child cache without evaluating its sample program. -/
theorem pow_zero_cached {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).cached = Cached.powZero sidecar.cached := rfl

/-- Zero power keeps the original rational-one annihilating polynomial exactly. -/
theorem pow_zero_polynomial {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).polynomial = (ofRational (RationalSidecar.exact 1)).polynomial := rfl

/-- Zero power keeps the complete original constant-one quantitative residual exactly. -/
theorem pow_zero_residual {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).residual = (ofRational (RationalSidecar.exact 1)).residual := rfl

/-- Every zero-power sample is the same exact constant one at its unchanged index. -/
theorem pow_zero_sample {channel : CoherentNamed} (sidecar : Sidecar channel) (index : Nat) :
    (sidecar.pow 0).residual.source.sample index = 1 := by
  change ((PolynomialResidual.exact 1).transport (RationalSidecar.exact 1).equivalent).source.sample index = 1
  rewrite [PolynomialResidual.transport_source]
  exact PolynomialResidual.exact_sample 1 index

/-- A positive power retains the same recursive arithmetic operation and both actual intermediate child caches. -/
theorem pow_succ {channel : CoherentNamed} (sidecar : Sidecar channel) (exponent : Nat) :
    sidecar.pow (exponent + 1) = (sidecar.pow exponent).mul sidecar := rfl

/-- Conjugate the original construction using its same numerical cache and transformed coefficient polynomial. -/
@[expose] def conj {channel : CoherentNamed} (sidecar : Sidecar channel) : Sidecar (CoherentNamed.conj channel) :=
  let residual := sidecar.residual.conj
  ⟨.conj sidecar.origin, _, residual, .conj sidecar.cached⟩

/-- Conjugation retains the original coefficient table with its exact coefficientwise conjugation. -/
theorem conj_polynomial {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.conj.polynomial = Dense.Gaussian.Conjugation.conjugate sidecar.polynomial := rfl

/-- Conjugation retains the complete actual original child cache. -/
theorem conj_cached {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.conj.cached = Cached.conj sidecar.cached := rfl

/-- Conjugation reads the conjugate of the same retained original numerical sample at every index. -/
theorem conj_sample {channel : CoherentNamed} (sidecar : Sidecar channel) (index : Nat) :
    sidecar.conj.residual.source.sample index = Data.Gaussian.Basic.conj (sidecar.residual.source.sample index) :=
  PolynomialResidual.conj_sample sidecar.residual index

/-- Conjugation retains the same original quantitative residual scale. -/
theorem conj_scale {channel : CoherentNamed} (sidecar : Sidecar channel) :
    sidecar.conj.residual.scale = sidecar.residual.scale := rfl

/-- Retain one already computed reciprocal cache of the exact original numerical residual and successful preparation. -/
@[expose] def reciprocalFromCache {channel : CoherentNamed} (sidecar : Sidecar channel)
    {prepared : Division.Prepared channel} (cache : PolynomialResidual.Reciprocal sidecar.residual prepared) :
    Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)) :=
  ⟨.reciprocal sidecar.origin prepared, cache.annihilator, cache.residualCertificate,
    .reciprocal sidecar.cached prepared cache⟩

/-- Every retained construction satisfies its computed polynomial on the unchanged original channel. -/
def equation {channel : CoherentNamed} (sidecar : Sidecar channel) :
    NamedEquivalent (Horner.polynomialEval sidecar.polynomial channel).name
      (CoherentNamed.Coherence.exact 0).name := sidecar.residual.equation

/-- Read exact scalar evidence through the same retained construction or its checked linear residual.

Arithmetic, conjugation, transport and paid reciprocals consume the actual
original child certificates. The reader preserves every construction/cache;
other inputs retain their unclassified quantitative algebraic evidence.
-/
@[expose] def scalar? {channel : CoherentNamed} (sidecar : Sidecar channel) : Option (RationalSidecar channel) :=
  sidecar.cached.scalar?

/-- The retained zero-power child yields the exact original constant-one scalar reading without inspecting the child. -/
theorem pow_zero_scalar {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).scalar? = some (RationalSidecar.exact 1) := by
  unfold scalar?
  change (Cached.powZero sidecar.cached).scalar? = some (RationalSidecar.exact 1)
  unfold Cached.scalar?
  rfl

/-- Cache one actual original geometric initial observation and its sufficient preparation outcome. -/
@[expose] def inspectInitial {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Geometric.Preparation.Observation sidecar.residual.source channel sidecar.residual.equivalent :=
  Geometric.Preparation.inspectInitial sidecar.residual.source channel sidecar.residual.equivalent

set_option genInjectivity false in
/-- The actual retained scalar, original numerical observation or completed coefficient decision construction.

Coefficient outcomes retain the same original residual, ordered decomposition,
observation and exact zero occurrence. Inconclusive observations consume and
retain complete localization on that same decomposition.
-/
inductive Resolved {channel : CoherentNamed} (sidecar : Sidecar channel) : Type 2 where
  /-- The actual exact reading decides the same original channel. -/
  | scalar (reading : RationalSidecar channel) (readback : sidecar.scalar? = some reading)
  /-- The same stored selected Root Sidecar and its once read decision precede a fresh numerical attempt. -/
  | selected (root : PolynomialRoot.Sidecar channel) (retained : sidecar.cached.selectedRoot? = some root)
      (decision : Division.Prepared.Decision channel) (computed : decision = root.decide)
  /-- The retained original numerical observation has this same prepared outcome. -/
  | geometric (initial : PolynomialResidual.Origin.Initial sidecar.residual)
      (separated : Geometric.Preparation.Separated initial.ball) (result : Division.Prepared channel)
      (result_eq : result = Geometric.Preparation.fromBall sidecar.residual.source channel sidecar.residual.equivalent
        initial.state initial.ball initial.readback separated)
      (computed : initial.outcome = .prepared separated result result_eq)
  /-- The actual coefficient inspection and its complete outcome retain all same original caches. -/
  | coefficient (inspection : PolynomialResidual.Origin.Inspection sidecar.residual)
      (completion : PolynomialResidual.Origin.Completion inspection)

constructive_injectivity Resolved

/-- Read the original-channel decision from its same retained construction and caches. -/
@[expose] def Resolved.decision {channel : CoherentNamed} {sidecar : Sidecar channel}
    (resolved : Resolved sidecar) : Division.Prepared.Decision channel :=
  match resolved with
  | .scalar reading _ => reading.decide
  | .selected _ _ decision _ => decision
  | .geometric _ _ result _ _ => .prepared result
  | .coefficient _ completion => completion.decision

/-- Resolve the cached original observation using an early coefficient certificate before complete localization. -/
@[expose] def resolveInitial {channel : CoherentNamed} (sidecar : Sidecar channel)
    (initial : Geometric.Preparation.Observation sidecar.residual.source channel sidecar.residual.equivalent) :
    Resolved sidecar :=
  match computed : initial.outcome with
  | .prepared separated result resultEq => .geometric initial separated result resultEq computed
  | .inconclusive _ =>
      let inspection := PolynomialResidual.Origin.inspect sidecar.residual initial
      .coefficient inspection inspection.complete

/-- Decide from the same retained original observation and its actual completed coefficient construction. -/
@[expose] def decideInitial {channel : CoherentNamed} (sidecar : Sidecar channel)
    (initial : Geometric.Preparation.Observation sidecar.residual.source channel sidecar.residual.equivalent) :
    Division.Prepared.Decision channel := (sidecar.resolveInitial initial).decision

/-- Retain the actual exact reading or original observation with every cache consumed by its complete decision. -/
@[expose] def resolve {channel : CoherentNamed} (sidecar : Sidecar channel) : Resolved sidecar :=
  match readback : sidecar.scalar? with
  | some reading => .scalar reading readback
  | none => match retained : sidecar.cached.selectedRoot? with
      | some root => let decision := root.decide; .selected root retained decision rfl
      | none => sidecar.resolveInitial sidecar.inspectInitial

/-- Decide the original channel using exact readings, computed result selection or its existing numerical fallback.

A computed result selection consumes its same owner decision and selected
occurrence. Other inputs retain the original initial numerical attempt and
complete coefficient-derived fallback. Exact scalar evidence keeps priority.
Every success concerns the unchanged original channel.
-/
@[expose] def decide {channel : CoherentNamed} (sidecar : Sidecar channel) : Division.Prepared.Decision channel :=
  sidecar.resolve.decision

/-- An exact scalar reading supplies the same original scalar decision before any geometric or root procedure. -/
theorem decide_of_scalar {channel : CoherentNamed} (sidecar : Sidecar channel) (reading : RationalSidecar channel)
    (retained : sidecar.scalar? = some reading) : sidecar.decide = reading.decide := by
  unfold decide resolve
  split
  · rename_i actual observed
    change actual.decide = reading.decide
    cases Option.some.inj (observed.symm.trans retained)
    rfl
  · rename_i missing
    cases (missing.symm.trans retained)

/-- A computed retained result supplies its same decision without another decomposition or result selection. -/
theorem decide_of_selectedRoot {channel : CoherentNamed} (sidecar : Sidecar channel)
    (root : PolynomialRoot.Sidecar channel) (noScalar : sidecar.scalar? = none)
    (retained : sidecar.cached.selectedRoot? = some root) : sidecar.decide = root.decide := by
  unfold decide resolve
  split
  · rename_i actual observed
    cases (noScalar.symm.trans observed)
  · split
    · rename_i actual observed
      change actual.decide = root.decide
      cases Option.some.inj (observed.symm.trans retained)
      rfl
    · rename_i missing
      cases (missing.symm.trans retained)

/-- Absence of a result selection retains scalar-first dispatch to the same completed fallback. -/
theorem decide_without_selection {channel : CoherentNamed} (sidecar : Sidecar channel)
    (noRoot : sidecar.cached.selectedRoot? = none) : sidecar.decide =
      match sidecar.scalar? with
      | some reading => reading.decide
      | none => sidecar.decideInitial sidecar.inspectInitial := by
  unfold decide resolve
  split
  · rename_i reading observed
    change reading.decide = match sidecar.scalar? with
      | some actual => actual.decide
      | none => sidecar.decideInitial sidecar.inspectInitial
    rewrite [observed]
    rfl
  · rename_i noScalar
    split
    · rename_i actual observed
      cases (noRoot.symm.trans observed)
    · change sidecar.decideInitial sidecar.inspectInitial = match sidecar.scalar? with
        | some reading => reading.decide
        | none => sidecar.decideInitial sidecar.inspectInitial
      rewrite [noScalar]
      rfl

/-- An unclassified cache retains its existing geometric attempt and complete localization fallback. -/
theorem decide_of_unclassified {channel : CoherentNamed} (sidecar : Sidecar channel)
    (noScalar : sidecar.scalar? = none) (noRoot : sidecar.cached.selectedRoot? = none) :
    sidecar.decide = sidecar.decideInitial sidecar.inspectInitial := by
  rewrite [decide_without_selection sidecar noRoot, noScalar]
  rfl

/-- Zero power keeps the complete original rational-one division decision without inspecting its retained child. -/
theorem pow_zero_decide {channel : CoherentNamed} (sidecar : Sidecar channel) :
    (sidecar.pow 0).decide = (ofRational (RationalSidecar.exact 1)).decide := by
  change (RationalSidecar.exact 1).decide = (RationalSidecar.exact 1).decide
  rfl

/-- Successful cached numerical separation returns exactly that same retained original-channel preparation. -/
theorem decideInitial_prepared {channel : CoherentNamed} (sidecar : Sidecar channel)
    (initial : Geometric.Preparation.Observation sidecar.residual.source channel sidecar.residual.equivalent)
    (separated : Geometric.Preparation.Separated initial.ball) (result : Division.Prepared channel)
    (resultEq : result = Geometric.Preparation.fromBall sidecar.residual.source channel sidecar.residual.equivalent
      initial.state initial.ball initial.readback separated)
    (outcome : initial.outcome = .prepared separated result resultEq) :
    sidecar.decideInitial initial = .prepared result := by
  cases initial with
  | mk state stateEq ball readback observed =>
      cases observed with
      | prepared actualSeparated actualResult actualResultEq => cases outcome; rfl
      | inconclusive actualFailed => cases outcome

/-- Failed numerical separation consumes the retained coefficient inspection and its exact complete fallback. -/
theorem decideInitial_inconclusive {channel : CoherentNamed} (sidecar : Sidecar channel)
    (initial : Geometric.Preparation.Observation sidecar.residual.source channel sidecar.residual.equivalent)
    (failed : ¬ Geometric.Preparation.Separated initial.ball)
    (outcome : initial.outcome = .inconclusive failed) :
    sidecar.decideInitial initial =
      (PolynomialResidual.Origin.inspect sidecar.residual initial).complete.decision := by
  cases initial with
  | mk state stateEq ball readback observed =>
      cases observed with
      | prepared actualSeparated actualResult actualResultEq => cases outcome
      | inconclusive actualFailed => cases outcome; rfl

set_option genInjectivity false in
/-- A computed reciprocal of the original algebraic construction or its exact zero obstruction.

Success retains the actual denominator presentation and inverse cache.
Obstruction identifies operational zero of the same original input channel.
-/
inductive Inverse {channel : CoherentNamed} (sidecar : Sidecar channel) : Type 1 where
  /-- Retain the actual successful preparation, inverse numerical cache and resulting finite construction. -/
  | ready (prepared : Division.Prepared channel) (cache : PolynomialResidual.Reciprocal sidecar.residual prepared)
      (result : Sidecar (prepared.quotient (CoherentNamed.Coherence.exact 1)))
      (result_eq : result = sidecar.reciprocalFromCache cache)
  /-- Retain exact operational zero of the original input, which prevents a productive reciprocal. -/
  | obstructed (zero : Equivalence.Zero.ZeroIdentity channel)

constructive_injectivity Inverse

/-- Decide the original input and compute its checked reciprocal with no caller-supplied exclusion floor. -/
@[expose] def inverse {channel : CoherentNamed} (sidecar : Sidecar channel) : Inverse sidecar :=
  match sidecar.decide with
  | .excluded zero => .obstructed zero
  | .prepared prepared =>
      let cache := PolynomialResidual.Reciprocal.ofPrepared sidecar.residual prepared
      .ready prepared cache (sidecar.reciprocalFromCache cache) rfl

end Sidecar

end Purelib.Approximation.Gaussian.Provenance.Algebraic

end
