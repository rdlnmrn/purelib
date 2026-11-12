module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Polynomial.Approximation.Gaussian.Residual.Reality
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Reality of original cached power-polynomial root tracks -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

open Purelib.Polynomial
open Purelib.Polynomial.Approximation.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- Every later actual root-cache sample stays in its same retained earlier-state box. -/
theorem sample_state_inside {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (floor index : Nat)
    (order : floor ≤ index) : (root.stateAt floor).box.Contains (root.approximation.sample index) := by
  rewrite [root.stateAt_eq, root.approximation_eq, approximation_sample]
  exact (state_refines_of_le track order).contains (state track index).box.contains_anchor

/-- A checked original cubic polynomial and positive actual cached-box gap retain the same root-tail reality region. -/
@[expose] def cubicRegion {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat)
    (same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩)
    (nonnegative : 0 ≤ (root.stateAt floor).box.xLower)
    (positive : 0 < Power.Gaussian.Reality.cubicGap (root.stateAt floor).box) :
    Residual.CubicRegion root.residualCertificate parameter floor (root.stateAt floor).box :=
  ⟨same, nonnegative, positive, fun index order => root.sample_state_inside floor index order⟩

/-- The original cached cubic root is operationally its conjugate when its actual region has positive cubic gap. -/
def cubicReal {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat)
    (same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩)
    (nonnegative : 0 ≤ (root.stateAt floor).box.xLower)
    (positive : 0 < Power.Gaussian.Reality.cubicGap (root.stateAt floor).box) :
    Equivalence.NamedEquivalent root.value.name (Name.Coherent.CoherentNamed.conj root.value).name :=
  (root.cubicRegion parameter floor same nonnegative positive).real

set_option genInjectivity false in
/-- The exact polynomial and current original box explain a finite cubic reality check. -/
inductive CubicOutcome {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (parameter : Rational) (floor : Nat) (box : Box) where
  /-- The original retained polynomial has different displayed coefficients. -/
  | polynomialMismatch (different : polynomial ≠ Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩)
  /-- This same retained box does not have the required nonnegative real-coordinate lower endpoint. -/
  | negativeReal (failed : ¬ 0 ≤ box.xLower)
  /-- The computed gap is not positive at this actual finite root-cache stage. -/
  | unresolvedGap (failed : ¬ 0 < Power.Gaussian.Reality.cubicGap box)
  /-- The same original polynomial residual and retained box certify the actual channel's reality. -/
  | ready (region : Residual.CubicRegion root.residualCertificate parameter floor box)

constructive_injectivity CubicOutcome

set_option genInjectivity false in
/-- One once read original root-state box and its typed current-stage reality outcome. -/
structure CubicAttempt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (parameter : Rational) (floor : Nat) where
  /-- The actual box read from the original retained root cache at the requested stage. -/
  box : Box
  /-- The stored box is the same original cache read. -/
  box_eq : box = (root.stateAt floor).box
  /-- The finite check retains its actual failed condition or the successful original-tail region certificate. -/
  outcome : CubicOutcome root parameter floor box

constructive_injectivity CubicAttempt

/-- Inspect the original polynomial and cached box once, preserving every finite reality stopping condition.

A nonpositive current gap is a finite unresolved region condition. It
establishes no global impossibility and leaves the original numerical cache
available for a later retained-stage attempt.
-/
@[expose] def inspectCubic {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat) :
    CubicAttempt root parameter floor :=
  let box := (root.stateAt floor).box
  let outcome := if same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩ then
      if nonnegative : 0 ≤ box.xLower then
        if positive : 0 < Power.Gaussian.Reality.cubicGap box then
          CubicOutcome.ready (root.cubicRegion parameter floor same nonnegative positive)
        else .unresolvedGap positive
      else .negativeReal nonnegative
    else .polynomialMismatch same
  ⟨box, rfl, outcome⟩

/-- A checked original quadratic and positive actual cached-box gap retain the same root-tail reality region. -/
@[expose] def quadraticRegion {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat)
    (same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩)
    (nonnegative : 0 ≤ (root.stateAt floor).box.xLower)
    (positive : 0 < Power.Gaussian.Reality.quadraticGap (root.stateAt floor).box) :
    Residual.QuadraticRegion root.residualCertificate parameter floor (root.stateAt floor).box :=
  ⟨same, nonnegative, positive, fun index order => root.sample_state_inside floor index order⟩

/-- The original cached quadratic root is operationally its conjugate on its same positive-gap region. -/
def quadraticReal {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat)
    (same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩)
    (nonnegative : 0 ≤ (root.stateAt floor).box.xLower)
    (positive : 0 < Power.Gaussian.Reality.quadraticGap (root.stateAt floor).box) :
    Equivalence.NamedEquivalent root.value.name (Name.Coherent.CoherentNamed.conj root.value).name :=
  (root.quadraticRegion parameter floor same nonnegative positive).real

set_option genInjectivity false in
/-- The exact polynomial and current original box explain a finite quadratic reality check. -/
inductive QuadraticOutcome {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (parameter : Rational) (floor : Nat) (box : Box) where
  /-- The original retained polynomial has different displayed coefficients. -/
  | polynomialMismatch (different : polynomial ≠ Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩)
  /-- This same retained box does not have the required nonnegative real-coordinate lower endpoint. -/
  | negativeReal (failed : ¬ 0 ≤ box.xLower)
  /-- The computed gap is not positive at this actual finite root-cache stage. -/
  | unresolvedGap (failed : ¬ 0 < Power.Gaussian.Reality.quadraticGap box)
  /-- The same original polynomial residual and retained box certify the actual channel's reality. -/
  | ready (region : Residual.QuadraticRegion root.residualCertificate parameter floor box)

constructive_injectivity QuadraticOutcome

set_option genInjectivity false in
/-- One once read original root-state box and its typed current-stage reality outcome. -/
structure QuadraticAttempt {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (parameter : Rational) (floor : Nat) where
  /-- The actual box read from the original retained root cache at the requested stage. -/
  box : Box
  /-- The stored box is the same original cache read. -/
  box_eq : box = (root.stateAt floor).box
  /-- The finite check retains its actual failed condition or the successful original-tail region certificate. -/
  outcome : QuadraticOutcome root parameter floor box

constructive_injectivity QuadraticAttempt

/-- Inspect the original polynomial and cached box once, preserving every finite reality stopping condition.

A nonpositive current gap is a finite unresolved region condition. It
establishes no global impossibility and leaves the original numerical cache
available for a later retained-stage attempt.
-/
@[expose] def inspectQuadratic {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (parameter : Rational) (floor : Nat) :
    QuadraticAttempt root parameter floor :=
  let box := (root.stateAt floor).box
  let outcome := if same : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩ then
      if nonnegative : 0 ≤ box.xLower then
        if positive : 0 < Power.Gaussian.Reality.quadraticGap box then
          QuadraticOutcome.ready (root.quadraticRegion parameter floor same nonnegative positive)
        else .unresolvedGap positive
      else .negativeReal nonnegative
    else .polynomialMismatch same
  ⟨box, rfl, outcome⟩

end Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

end
