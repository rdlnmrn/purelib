module
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Quadratic
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Exact
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Root
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Riemann.RootContinuation.SquareRootSidecar
meta import Purelib.Elab.ConstructiveInjectivity
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib.Approximation.Gaussian.Provenance

section
@[expose] public section

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance and
admitted irrational quadratic coordinates construct and transport all-row
providers. One retained root admission selects that provider or exact rational
readings for zero and rational-square parameters. An isolated polynomial root
whose original box misses the real axis supplies a provider through that same
root view; otherwise its failed inspection is retained. Missing provenance is explicit.
The word client consumes rational readings through ordered domain inspection
and sends unresolved inference to its signed numerical acquisition.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Process.Imaginary (Separation)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)
open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Approximation.Gaussian.Provenance.Quadratic (Sidecar)
open Purelib.Riemann.RootContinuation

/-- Construct an all-matrix preparation provider from nonreal rational provenance.

The exact rational sidecar supplies imaginary separation, and its operational equivalence transports the resulting
provider to the original coherent channel. -/
def rationalProvider {channel :
  Coherent.CoherentNamed} (sidecar : Rational.Basic.RationalSidecar channel)
    (nonreal : sidecar.value.im ≠ 0) : Preparation.Basic.Provider channel :=
  Equivalence.transportProvider (Separated.provider
    (Exact.exactSeparation sidecar.value nonreal)) sidecar.equivalent

/-- Prepare every requested integer row from the original admitted irrational coordinate cache. -/
def quadraticProvider {channel : CoherentNamed} (sidecar : Sidecar channel)
    (irrational : sidecar.evidence.value.im ≠ 0) : Provider channel :=
  Preparation.Quadratic.provider sidecar.evidence (fun value => sidecar.admission.coefficient_eq value) irrational

/-- Construct a provider from the same admitted original generator and its cached realization. -/
def admissionProvider {channel : CoherentNamed} {root : SquareRootSidecar.Sidecar channel}
    (admission : Realization.Admission channel root) : Provider channel := by
  have original : NamedEquivalent channel.name admission.realization.generator.name := by
    rewrite [admission.realization_generator]
    exact NamedEquivalent.refl _
  let input := (Realization.Sidecar.generator admission.realization).transport original
  have irrational : input.value.im ≠ 0 := by
    change ((Realization.Sidecar.generator admission.realization).transport original).value.im ≠ 0
    rewrite [Realization.Sidecar.transport_value, Realization.Sidecar.generator_value]
    change (1 : Rational) ≠ 0
    decide +kernel
  exact Preparation.Quadratic.provider input (fun value => admission.coefficient_eq value) irrational

/-- Inspect a supplied root once and construct an all-row provider for its admitted original generator. -/
def rootProvider {channel : CoherentNamed} (sidecar : SquareRootSidecar.Sidecar channel) : Option (Provider channel) :=
  match (Realization.inspectRoot sidecar).outcome with
  | .admitted admission => some (admissionProvider admission)
  | .nonreal _ => none
  | .zero _ _ _ _ => none
  | .nonpositive _ _ _ _ => none
  | .square _ _ _ _ _ _ => none

/-- A zero-parameter root declines the all-row provider and retains its exact rational inspection route. -/
theorem rootProvider_zero {channel : CoherentNamed} (sidecar : SquareRootSidecar.Sidecar channel)
    (zero : sidecar.parameter = 0) : rootProvider sidecar = none := by
  obtain ⟨evidence, selected, _⟩ := Realization.inspectRoot_zero sidecar zero
  unfold rootProvider
  rewrite [selected]
  rfl

/-- Every supplied positive nonsquare real rational root produces a provider at its exact original channel. -/
theorem rootProvider_admitted {channel : CoherentNamed} (sidecar : SquareRootSidecar.Sidecar channel)
    (parameter : Rational) (same : sidecar.parameter = Data.Gaussian.Cast.CoordinateTaylor.ofCoordinate parameter)
    (positive : 0 < parameter) (missing : (Data.Rat.Fraction.Square.inspect parameter).root? = none) :
    (rootProvider sidecar).isSome = true := by
  obtain ⟨admission, accepted, _⟩ := Realization.inspectRoot_positive sidecar parameter same positive missing
  unfold rootProvider
  rewrite [accepted]
  rfl

/-- The original root coefficient is outside the admitted real nonnegative parameter fragment. -/
def outsideFragment {channel : CoherentNamed} {root : SquareRootSidecar.Sidecar channel} :
    Realization.AdmissionOutcome channel root → Prop
  | .nonreal _ => True
  | .nonpositive _ _ _ _ => True
  | _ => False

/-- The original root view and the result of checking its initial imaginary interval.

Missing-view and crossing outcomes retain the exact failed lookup or both
failed endpoint tests. Successful outcomes retain the same root view and its
actual operational link to the supplied channel. -/
def RootInspection {channel : CoherentNamed} (root : PolynomialRoot.Sidecar channel) : Type 1 :=
  PLift (root.view? = none) ⊕
    (Σ view : { value : CoherentRoot.CertifiedName.View channel // root.view? = some value },
      Separation.RootBox view.val.track)

/-- Read the original root view once and check its same initial track box. -/
@[noinline, nospecialize] def inspectRoot {channel : CoherentNamed} (root : PolynomialRoot.Sidecar channel) :
    RootInspection root :=
  match found : root.view? with
  | none => .inl ⟨found⟩
  | some view => .inr ⟨⟨view, found⟩, Separation.inspectRootBox view.track⟩

/-- The inspections which leave the original root's imaginary gap unresolved. -/
def RootInspection.unresolved {channel : CoherentNamed} {root : PolynomialRoot.Sidecar channel} :
    RootInspection root → Prop
  | .inl _ | .inr ⟨_, .crossing ..⟩ => True
  | .inr ⟨_, .above ..⟩ | .inr ⟨_, .below ..⟩ => False

/-- The complete unresolved root inspection, tied to the actual cached checker result. -/
def RootFailure {channel : CoherentNamed} (root : PolynomialRoot.Sidecar channel) : Type 1 :=
  { inspection : RootInspection root // inspection = inspectRoot root ∧ inspection.unresolved }

/-- Derive an all-row provider from an original root view, or retain the unresolved actual inspection.

Positive and negative initial boxes supply unsigned separation at the same
original root state. The existing operational link transports its provider to
the original input channel without rebuilding its root or numerical cache. -/
@[noinline, nospecialize] def inspectedRootProvider {channel : CoherentNamed}
    (root : PolynomialRoot.Sidecar channel) : Provider channel ⊕ RootFailure root :=
  match inspected : inspectRoot root with
  | .inr ⟨view, .above positive⟩ =>
      .inl (Equivalence.transportProvider (Separated.provider (Separation.ofRootAbove view.val.root positive))
        view.val.equivalent)
  | .inr ⟨view, .below _ negative⟩ =>
      .inl (Equivalence.transportProvider (Separated.provider (Separation.ofRootBelow view.val.root negative))
        view.val.equivalent)
  | .inl missing => .inr ⟨.inl missing, inspected.symm, True.intro⟩
  | .inr ⟨view, .crossing notAbove notBelow⟩ =>
      .inr ⟨.inr ⟨view, .crossing notAbove notBelow⟩, inspected.symm, True.intro⟩

set_option genInjectivity false in
/-- The actual missing or unsupported condition retained by finite provider inference.

Polynomial-root evidence without an exact scalar reading retains that same
original owner and the unresolved root inspection. It does not assert that a
requested row is zero or that a provider is impossible.
-/
inductive Unresolved {channel : CoherentNamed}
    (source : Option (Approximation.Gaussian.Acquisition.Provenance channel)) : Type 1 where
  /-- The original source supplies no finite provenance. -/
  | missing (selected : source = none)
  /-- The original square-root parameter fails one retained admission condition. -/
  | squareRoot (root : SquareRootSidecar.Sidecar channel)
      (selected : source = some (.squareRoot root))
      (outcome : Realization.AdmissionOutcome channel root) (outside : outsideFragment outcome)
  /-- A general root lacks a scalar and its retained track inspection cannot certify imaginary separation. -/
  | polynomialRoot (root : PolynomialRoot.Sidecar channel)
      (selected : source = some (.polynomialRoot root)) (missing : root.scalar? = none) (reason : RootFailure root)
  /-- A retained algebraic construction has no scalar reading or stored root owner. -/
  | algebraic (sidecar : Algebraic.Sidecar channel)
      (selected : source = some (.algebraic sidecar)) (missing : sidecar.scalar? = none)
      (noRoot : sidecar.cached.root? = none)
  /-- The actual cached algebraic root cannot yet certify imaginary separation. -/
  | algebraicRoot (sidecar : Algebraic.Sidecar channel)
      (selected : source = some (.algebraic sidecar)) (missing : sidecar.scalar? = none)
      (root : PolynomialRoot.Sidecar channel) (found : sidecar.cached.root? = some root) (reason : RootFailure root)

constructive_injectivity Unresolved

set_option genInjectivity false in
/-- A shallow carrier for successful provider or scalar evidence and retained unresolved inspection data. -/
inductive InferencePayload.{u, v, w}
    (providerType : Type u) (rationalType : Type v) (unresolvedType : Type w) where
  /-- Successful preparation of every original invertible matrix request. -/
  | provider (evidence : providerType)
  /-- Successful exact evidence for ordered denominator inspection. -/
  | rational (evidence : rationalType)
  /-- Actual missing or unsupported source evidence. -/
  | unresolved (evidence : unresolvedType)

constructive_injectivity InferencePayload

/-- Inferred matrix or scalar evidence at the same actual input and original provenance. -/
def Inference {channel : CoherentNamed} (source : Option (Approximation.Gaussian.Acquisition.Provenance channel)) :=
  InferencePayload (Provider channel) (RationalSidecar channel) (Unresolved source)

/-- Inspect the original provenance once, sharing root admission between its provider and signed rational routes. -/
@[noinline, nospecialize] def infer {channel : CoherentNamed}
    (source : Option (Approximation.Gaussian.Acquisition.Provenance channel)) : Inference source :=
  match source with
  | none => .unresolved (.missing rfl)
  | some (.rational reading) => if nonreal : reading.value.im ≠ 0
      then .provider (rationalProvider reading nonreal) else .rational reading
  | some (.quadratic coordinates) => if zero : coordinates.evidence.value.im = 0
      then .rational (coordinates.scalarReading zero) else .provider (quadraticProvider coordinates zero)
  | some (.squareRoot root) =>
      let checked := Realization.inspectRoot root
      match checked.outcome, checked.outcome.inspectRational with
      | .admitted admission, _ => .provider (admissionProvider admission)
      | .zero _ _ _ reading, _ => .rational reading
      | .square _ _ _ _ _ _, certificate => .rational certificate.2.val
      | .nonreal imaginary, _ => .unresolved (.squareRoot root rfl (.nonreal imaginary) True.intro)
      | .nonpositive parameter same nonzero notPositive, _ =>
           .unresolved (.squareRoot root rfl (.nonpositive parameter same nonzero notPositive) True.intro)

  | some (.polynomialRoot root) =>
      match selected : root.scalar? with
      | some reading => if nonreal : reading.value.im ≠ 0
          then .provider (rationalProvider reading nonreal) else .rational reading
      | none => match inspectedRootProvider root with
          | .inl provider => .provider provider
          | .inr reason => .unresolved (.polynomialRoot root rfl selected reason)
  | some (.algebraic sidecar) =>
      match selected : sidecar.scalar? with
      | some reading => if nonreal : reading.value.im ≠ 0
          then .provider (rationalProvider reading nonreal) else .rational reading
      | none => match found : sidecar.cached.root? with
          | none => .unresolved (.algebraic sidecar rfl selected found)
          | some root => match inspectedRootProvider root with
              | .inl provider => .provider provider
              | .inr reason => .unresolved (.algebraicRoot sidecar rfl selected root found reason)

/-- An algebraic scalar reading with zero imaginary part supplies the same original rational evidence. -/
theorem infer_algebraic_real {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (reading : RationalSidecar channel) (selected : sidecar.scalar? = some reading) (real : reading.value.im = 0) :
    infer (some (.algebraic sidecar)) = .rational reading := by
  unfold infer
  dsimp only
  split
  · rename_i actual observed
    cases Option.some.inj (observed.symm.trans selected)
    rewrite [dif_neg (fun nonreal => nonreal real)]
    rfl
  · rename_i observed
    cases observed.symm.trans selected

/-- A nonreal algebraic scalar reading supplies the existing provider at its same original channel. -/
theorem infer_algebraic_nonreal {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (reading : RationalSidecar channel) (selected : sidecar.scalar? = some reading) (nonreal : reading.value.im ≠ 0) :
    infer (some (.algebraic sidecar)) = .provider (rationalProvider reading nonreal) := by
  unfold infer
  dsimp only
  split
  · rename_i actual observed
    cases Option.some.inj (observed.symm.trans selected)
    rewrite [dif_pos nonreal]
    rfl
  · rename_i observed
    cases observed.symm.trans selected

/-- Missing algebraic scalar and root evidence retains the same sidecar and both failed readings. -/
theorem infer_algebraic_unresolved {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (missing : sidecar.scalar? = none) (noRoot : sidecar.cached.root? = none) :
    infer (some (.algebraic sidecar)) = .unresolved (.algebraic sidecar rfl missing noRoot) := by
  unfold infer
  dsimp only
  split
  · rename_i actual observed
    cases observed.symm.trans missing
  · split
    · rfl
    · rename_i actual observed
      cases observed.symm.trans noRoot

/-- An inspected cached root provider is returned at the same original algebraic channel. -/
theorem infer_algebraic_rootProvider {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (missing : sidecar.scalar? = none) (root : PolynomialRoot.Sidecar channel)
    (found : sidecar.cached.root? = some root) (provider : Provider channel)
    (prepared : inspectedRootProvider root = .inl provider) :
    infer (some (.algebraic sidecar)) = .provider provider := by
  unfold infer
  dsimp only
  split
  · rename_i actual observed
    cases observed.symm.trans missing
  · split
    · rename_i observed
      cases observed.symm.trans found
    · rename_i actual observed
      cases Option.some.inj (observed.symm.trans found)
      rewrite [prepared]
      rfl

/-- An inspected cached root's unresolved result retains the exact sidecar, root and failed inspection. -/
theorem infer_algebraic_rootUnresolved {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (missing : sidecar.scalar? = none) (root : PolynomialRoot.Sidecar channel)
    (found : sidecar.cached.root? = some root) (reason : RootFailure root)
    (unresolved : inspectedRootProvider root = .inr reason) :
    infer (some (.algebraic sidecar)) = .unresolved (.algebraicRoot sidecar rfl missing root found reason) := by
  unfold infer
  dsimp only
  split
  · rename_i actual observed
    cases observed.symm.trans missing
  · split
    · rename_i observed
      cases observed.symm.trans found
    · rename_i actual observed
      cases Option.some.inj (observed.symm.trans found)
      rewrite [unresolved]
      rfl

/-- Zero-parameter root inference returns exact evidence at the same original input. -/
theorem infer_zero_root {channel : CoherentNamed} (root : SquareRootSidecar.Sidecar channel)
    (zero : root.parameter = 0) :
    ∃ reading, infer (some (.squareRoot root)) = .rational reading := by
  obtain ⟨reading, selected, _⟩ := Realization.inspectRoot_zero root zero
  unfold infer
  dsimp only
  rewrite [selected]
  exact ⟨reading, rfl⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance

end
