module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Normalization
public import Purelib.Polynomial.Multivariate.Gaussian.PowerReduction
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Power
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained generator reduction of original acquisition expressions

The supplied equation belongs to an actual bounded position in the original
binding cache. Coefficient reduction retains the same original compilation,
bindings and support; exact provenance still enriches that original channel.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated Provenance)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Multivariate
open Purelib.Riemann.RootContinuation.SquareRootSidecar (Sidecar)
open Purelib.Approximation.Gaussian.Provenance

namespace Binding

set_option genInjectivity false in
/-- A supplied power equation, retained composite or polynomial-root evidence, or proved absence of provenance. -/
inductive PowerEvidence {arity : Nat} {environment : Fin arity → Annotated} (binding : Binding environment) where
  /-- Retain the degree, coefficient and power equation at this exact original channel. -/
  | known (degree : Nat) (positive : 0 < degree) (parameter : Canonical)
      (identity : PowerIdentity binding.channel degree parameter)
  /-- The original annotation supplies no power relation; this asserts no numerical obstruction. -/
  | absent (provenance_eq : binding.annotation.provenance = none)
  /-- Supplied composite coordinates do not assert a pure-power equation for their original channel. -/
  | composite (sidecar : Quadratic.Sidecar binding.channel)
      (provenance_eq : binding.annotation.provenance = some (.quadratic sidecar))
  /-- A general polynomial equation does not assert a pure-power equation at its original root channel. -/
  | polynomialRoot (sidecar : PolynomialRoot.Sidecar binding.channel)
      (provenance_eq : binding.annotation.provenance = some (.polynomialRoot sidecar))
  /-- A retained algebraic construction supplies a general equation rather than a pure-power relation. -/
  | algebraic (sidecar : Algebraic.Sidecar binding.channel)
      (provenance_eq : binding.annotation.provenance = some (.algebraic sidecar))

constructive_injectivity PowerEvidence

/-- Read retained scalar/root equations or check the same cached algebraic polynomial for a pure-power relation.

The general polynomial check consumes its actual retained residual certificate.
Only a structural coefficient identity yields a power equation; other
algebraic polynomials retain their original general evidence.
-/
@[expose] def powerEvidence {arity : Nat} {environment : Fin arity → Annotated}
    (binding : Binding environment) : PowerEvidence binding :=
  match selected : binding.annotation.provenance with
  | none => .absent selected
  | some (.rational reading) => .known 1 (by decide) reading.value
      (NamedEquivalent.trans (Power.namedPower_one binding.channel) reading.equivalent)
  | some (.squareRoot root) => .known 2 (by decide) root.parameter (PowerIdentity.ofSquare root.square)
  | some (.quadratic coordinates) => .composite coordinates selected
  | some (.polynomialRoot root) =>
      let numerical := root.residualCertificate
      match numerical.2.inspectPower with
      | .recognized _ identity => .known numerical.1.natDegree numerical.2.degreePositive
          (-numerical.1.eval 0) identity
      | .other _ => .polynomialRoot root selected
  | some (.algebraic sidecar) =>
      match sidecar.residual.inspectPower with
      | .recognized _ identity => .known sidecar.polynomial.natDegree sidecar.residual.degreePositive
          (-sidecar.polynomial.eval 0) identity
      | .other _ => .algebraic sidecar selected

/-- A retained general root's checked numerical polynomial supplies its original-channel power equation.

The supplied equality concerns the actual cached polynomial readback, including
factor reduction when the original source has repeated multiplicity. The
original annotation and mathematical root owner remain retained.
-/
theorem powerEvidence_polynomialRoot {arity : Nat} {environment : Fin arity → Annotated}
    (binding : Binding environment) (sidecar : PolynomialRoot.Sidecar binding.channel)
    (selected : binding.annotation.provenance = some (.polynomialRoot sidecar))
    (same : sidecar.residualCertificate.1 = Polynomial.Power.Gaussian.rootPolynomial
      (-sidecar.residualCertificate.1.eval 0)
      ⟨sidecar.residualCertificate.1.natDegree, sidecar.residualCertificate.2.degreePositive⟩) :
    binding.powerEvidence = .known sidecar.residualCertificate.1.natDegree
      sidecar.residualCertificate.2.degreePositive (-sidecar.residualCertificate.1.eval 0)
      (sidecar.residualCertificate.2.powerIdentity (-sidecar.residualCertificate.1.eval 0)
        ⟨sidecar.residualCertificate.1.natDegree, sidecar.residualCertificate.2.degreePositive⟩ same) := by
  change PolynomialRoot.Sidecar binding.annotation.channel at sidecar
  unfold powerEvidence
  split
  · rename_i none_eq
    cases none_eq.symm.trans selected
  · rename_i reading reading_eq
    cases Option.some.inj (reading_eq.symm.trans selected)
  · rename_i root root_eq
    cases Option.some.inj (root_eq.symm.trans selected)
  · rename_i coordinates coordinates_eq
    cases Option.some.inj (coordinates_eq.symm.trans selected)
  · rename_i root root_eq
    have sameRoot : root = sidecar := Provenance.polynomialRoot.inj (Option.some.inj (root_eq.symm.trans selected))
    cases sameRoot
    dsimp only
    rewrite [sidecar.residualCertificate.2.inspectPower_recognized same]
    rfl
  · rename_i original original_eq
    cases Option.some.inj (original_eq.symm.trans selected)

/-- The actual supplied root annotation selects its original degree-two relation and coefficient. -/
theorem powerEvidence_root {arity : Nat} {environment : Fin arity → Annotated}
    (binding : Binding environment) (sidecar : Sidecar binding.channel)
    (selected : binding.annotation.provenance = some (.squareRoot sidecar)) :
    binding.powerEvidence = .known 2 (by decide) sidecar.parameter (PowerIdentity.ofSquare sidecar.square) := by
  unfold powerEvidence
  split
  · rename_i none_eq
    cases none_eq.symm.trans selected
  · rename_i rational rational_eq
    have impossible := Option.some.inj (rational_eq.symm.trans selected)
    cases impossible
  · rename_i root root_eq
    have same : root = sidecar := Provenance.squareRoot.inj (Option.some.inj (root_eq.symm.trans selected))
    cases same
    rfl
  · rename_i algebraic algebraic_eq
    have impossible := Option.some.inj (algebraic_eq.symm.trans selected)
    cases impossible
  · rename_i root root_eq
    cases Option.some.inj (root_eq.symm.trans selected)
  · rename_i sidecar sidecar_eq
    cases Option.some.inj (sidecar_eq.symm.trans selected)

/-- Absence of supplied annotation provenance selects the retained absence certificate. -/
theorem powerEvidence_absent {arity : Nat} {environment : Fin arity → Annotated}
    (binding : Binding environment) (selected : binding.annotation.provenance = none) :
    binding.powerEvidence = .absent selected := by
  unfold powerEvidence
  split
  · rfl
  · rename_i rational rational_eq
    cases rational_eq.symm.trans selected
  · rename_i root root_eq
    cases root_eq.symm.trans selected
  · rename_i algebraic algebraic_eq
    cases algebraic_eq.symm.trans selected
  · rename_i root root_eq
    cases root_eq.symm.trans selected
  · rename_i sidecar sidecar_eq
    cases sidecar_eq.symm.trans selected

/-- Apply supplied power equations in a bounded original binding prefix to the same cached polynomial. -/
@[expose] def reducePowers {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) {original : CoherentNamed}
    (polynomial : Gaussian.Normalized (channels bindings) original) :
    (count : Nat) → count ≤ bindings.length → Gaussian.Normalized (channels bindings) original
  | 0, _ => polynomial
  | count + 1, bound =>
      let previous := reducePowers bindings polynomial count (Nat.le_of_succ_le bound)
      let index : Fin bindings.length := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩
      match (read bindings index).powerEvidence with
      | .known degree _ parameter identity => previous.reduceAt index degree parameter identity
      | .absent _ => previous
      | .composite _ _ => previous
      | .polynomialRoot _ _ => previous
      | .algebraic _ _ => previous

/-- An original prefix with no supplied provenance retains the complete cached polynomial literally. -/
theorem reducePowers_absent {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) {original : CoherentNamed}
    (polynomial : Gaussian.Normalized (channels bindings) original)
    (absent : ∀ index : Fin bindings.length, (read bindings index).annotation.provenance = none)
    (count : Nat) (bound : count ≤ bindings.length) : reducePowers bindings polynomial count bound = polynomial := by
  induction count with
  | zero => rfl
  | succ count ih =>
      unfold reducePowers
      dsimp only
      let index : Fin bindings.length := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩
      rewrite [powerEvidence_absent (read bindings index) (absent index)]
      exact ih (Nat.le_of_succ_le bound)

/-- A selected original annotation equation determines the next cached coefficient form. -/
theorem reducePowers_known_form {arity : Nat} {environment : Fin arity → Annotated}
    (bindings : List (Binding environment)) {original : CoherentNamed}
    (polynomial : Gaussian.Normalized (channels bindings) original) (count : Nat)
    (bound : count + 1 ≤ bindings.length) (degree : Nat) (positive : 0 < degree) (parameter : Canonical)
    (identity : PowerIdentity (channels bindings ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩)
      degree parameter)
    (selected : (read bindings ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩).powerEvidence =
      .known degree positive parameter identity) :
    (reducePowers bindings polynomial (count + 1) bound).form =
      (reducePowers bindings polynomial count (Nat.le_of_succ_le bound)).form.reduceAt
        ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩ degree parameter := by
  conv_lhs => unfold reducePowers
  dsimp only
  rewrite [selected]
  dsimp only
  exact Gaussian.Normalized.reduceAt_form
    (reducePowers bindings polynomial count (Nat.le_of_succ_le bound))
    ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩ degree parameter identity

end Binding

namespace Normalized

/-- Reduce an actual cached expression form at a supplied original generator equation. -/
@[expose] def reduceAt {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length)
    (degree : Nat) (parameter : Canonical)
    (relation : PowerIdentity (Binding.channels normalized.bindings index) degree parameter) :
    Normalized environment expression :=
  { compiled := normalized.compiled
    bindings := normalized.bindings
    inspections := normalized.inspections
    supported := normalized.supported
    polynomial := normalized.polynomial.reduceAt index degree parameter relation }

/-- Retained generator reduction preserves the literal original compilation. -/
theorem reduceAt_compiled {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length)
    (degree : Nat) (parameter : Canonical)
    (relation : PowerIdentity (Binding.channels normalized.bindings index) degree parameter) :
    (normalized.reduceAt index degree parameter relation).compiled = normalized.compiled := rfl

/-- Retained generator reduction keeps the same actual original leaf annotations and owners. -/
theorem reduceAt_bindings {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length)
    (degree : Nat) (parameter : Canonical)
    (relation : PowerIdentity (Binding.channels normalized.bindings index) degree parameter) :
    (normalized.reduceAt index degree parameter relation).bindings = normalized.bindings := rfl

/-- Reduce at the selected actual annotation's supplied relation, keeping the cached input if none is present. -/
@[expose] def reduceRetainedAt {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length) :
    Normalized environment expression :=
  let polynomial := match (Binding.read normalized.bindings index).powerEvidence with
    | .known degree _ parameter identity => normalized.polynomial.reduceAt index degree parameter identity
    | .absent _ => normalized.polynomial
    | .composite _ _ => normalized.polynomial
    | .polynomialRoot _ _ => normalized.polynomial
    | .algebraic _ _ => normalized.polynomial
  ⟨normalized.compiled, normalized.bindings, normalized.inspections, normalized.supported, polynomial⟩

/-- Reduction from a supplied root annotation uses its actual coefficient at the selected original position. -/
theorem reduceRetainedAt_root_form {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length)
    (sidecar : Sidecar (Binding.channels normalized.bindings index))
    (selected : (Binding.read normalized.bindings index).annotation.provenance = some (.squareRoot sidecar)) :
    (normalized.reduceRetainedAt index).polynomial.form =
      normalized.polynomial.form.reduceAt index 2 sidecar.parameter := by
  unfold reduceRetainedAt
  rewrite [Binding.powerEvidence_root (Binding.read normalized.bindings index) sidecar selected]
  rfl

/-- An annotation without supplied provenance retains the complete cached normalization literally. -/
theorem reduceRetainedAt_absent {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length)
    (selected : (Binding.read normalized.bindings index).annotation.provenance = none) :
    normalized.reduceRetainedAt index = normalized := by
  unfold reduceRetainedAt
  rewrite [Binding.powerEvidence_absent (Binding.read normalized.bindings index) selected]
  rfl

/-- Every selected retained-evidence reduction preserves the original compilation exactly. -/
theorem reduceRetainedAt_compiled {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length) :
    (normalized.reduceRetainedAt index).compiled = normalized.compiled := rfl

/-- Every selected retained-evidence reduction retains the actual original leaf owners. -/
theorem reduceRetainedAt_bindings {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) (index : Fin normalized.bindings.length) :
    (normalized.reduceRetainedAt index).bindings = normalized.bindings := rfl

/-- Apply actual supplied relations once across the original finite binding cache. -/
@[expose] def reduceRetained {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) : Normalized environment expression :=
  { compiled := normalized.compiled
    bindings := normalized.bindings
    inspections := normalized.inspections
    supported := normalized.supported
    polynomial := Binding.reducePowers normalized.bindings normalized.polynomial
      normalized.bindings.length (Nat.le_refl _) }

/-- Complete retained-equation reduction keeps the original compilation literally. -/
theorem reduceRetained_compiled {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) : normalized.reduceRetained.compiled = normalized.compiled := rfl

/-- Complete retained-equation reduction keeps every original indexed leaf owner. -/
theorem reduceRetained_bindings {arity : Nat} {environment : Fin arity → Annotated} {expression : Expr arity}
    (normalized : Normalized environment expression) : normalized.reduceRetained.bindings = normalized.bindings := rfl

end Normalized

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
