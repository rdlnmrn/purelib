module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
public import Purelib.Approximation.Gaussian.Division.Prepared.Product
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Apart.Exact
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

/-! # Root certificates on retained arithmetic processes

An original square comparison and its existing division preparation produce
a full root certificate on the actual cached prepared presentation. Product
and exact-factor square comparisons use the complete original factor
certificates. The operational link retains the original arithmetic input as
well as the prepared root; no winding owner or replacement root is selected.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Certificate

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- Certify the square of an original arithmetic input on its identical supplied prepared presentation. -/
def ofPrepared {parameter : Canonical} (value : CoherentNamed)
    (square : NamedEquivalent (value.mul value).name (Named.exact parameter))
    (prepared : Division.Prepared value) : Certificate parameter :=
  { value := prepared.denominator
    apart := prepared.apart
    square := (Product.Congruence.coherentMul_respects
      prepared.denominator value prepared.denominator value
      prepared.equivalent.symm prepared.equivalent.symm).trans square }

/-- The full arithmetic root certificate uses the exact supplied denominator cache. -/
theorem ofPrepared_value {parameter : Canonical} (value : CoherentNamed)
    (square : NamedEquivalent (value.mul value).name (Named.exact parameter))
    (prepared : Division.Prepared value) : (ofPrepared value square prepared).value = prepared.denominator := by
  unfold ofPrepared
  rfl

/-- The full arithmetic certificate retains the exact supplied whole-ball apartness certificate. -/
theorem ofPrepared_apart {parameter : Canonical} (value : CoherentNamed)
    (square : NamedEquivalent (value.mul value).name (Named.exact parameter))
    (prepared : Division.Prepared value) :
    Eq.mp (congrArg (fun retained : CoherentNamed => Named.Apart retained.name)
      (ofPrepared_value value square prepared)) (ofPrepared value square prepared).apart = prepared.apart := by
  unfold ofPrepared
  rfl

/-- The original arithmetic input agrees operationally with its full prepared root certificate. -/
def ofPrepared_agrees {parameter : Canonical} (value : CoherentNamed)
    (square : NamedEquivalent (value.mul value).name (Named.exact parameter))
    (prepared : Division.Prepared value) : NamedEquivalent value.name (ofPrepared value square prepared).value.name :=
  NamedEquivalent.transport rfl
    (congrArg (fun retained : CoherentNamed => retained.name) (ofPrepared_value value square prepared)).symm
    prepared.equivalent

/-- The original product of two retained root channels squares to the product of their exact radicands. -/
def productSquare {first last : Canonical} (left : Certificate first) (right : Certificate last)
    (value : CoherentNamed) (retained : value = left.value.mul right.value) :
    NamedEquivalent (value.mul value).name (Named.exact (first * last)) := by
  have factors := (Product.Laws.coherentMul_squares_interchange left.value right.value).symm.trans
    ((Product.Congruence.coherentMul_respects (left.value.mul left.value) (Coherence.exact first)
      (right.value.mul right.value) (Coherence.exact last) left.square right.square).trans
        (Name.Coherent.Exact.Arithmetic.exact_mul first last))
  exact NamedEquivalent.transport
    (congrArg (fun original : CoherentNamed => (original.mul original).name) retained).symm rfl factors

/-- Certify an actual retained product on the exact supplied prepared cache, keeping both factor certificates. -/
def ofProduct {first last : Canonical} (left : Certificate first) (right : Certificate last)
    (value : CoherentNamed) (retained : value = left.value.mul right.value)
    (prepared : Division.Prepared value) : Certificate (first * last) :=
  ofPrepared value (productSquare left right value retained) prepared

/-- The displayed exact nonzero root has its original exact process and square comparison. -/
def exact (root : Canonical) (nonzero : root ≠ 0) : Certificate (root ^ 2) :=
  { value := Coherence.exact root
    apart := Name.Apart.Exact.exactApart root nonzero
    square := NamedEquivalent.transport rfl
      (congrArg Named.exact (show root * root = root ^ 2 by ring1))
      (Name.Coherent.Exact.Arithmetic.exact_mul root root) }

/-- The exact-root arithmetic certificate retains the original exact coherent name. -/
theorem exact_value (root : Canonical) (nonzero : root ≠ 0) :
    (exact root nonzero).value = Coherence.exact root := by
  unfold exact
  rfl

/-- The retained root process has a strictly positive original center bound. -/
theorem centerBound_positive {parameter : Canonical} (root : Certificate parameter) :
    0 < root.value.name.process.centerBound := by
  have centerInside : (root.value.name.process.ball root.value.name.state).Contains
      (root.value.name.process.ball root.value.name.state).center := by
    change Norm.Basic.normSq (_ - _) ≤ _
    rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
    exact (root.value.name.process.ball root.value.name.state).radiusSq_nonneg
  exact root.apart.certificate.positive.trans_le
    ((root.apart.certificate.lower root.value.name.state centerInside).trans
      (root.value.name.process.center_bounded root.value.name.state))

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Certificate
