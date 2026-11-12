module

import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Polynomial.Winding.Box.Basic

/-! # Actual signed unit-root readings on the original Legendre collision patches -/

namespace TestPurelib.Curves.Legendre.UnitRoot

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

/-- Intrinsic patch admission constructs a retained original root track and its operational square identity. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) :
    let retained := Degeneration.UnitRoot.owner site point inside
    SquareRootProvenance.SquareIdentity (CertifiedSquareRoot.rawRoot retained.track)
      ((Degeneration.unitPolynomial site).eval point) := by
  intro retained
  exact CertifiedSquareRoot.rawRoot_square retained.track

/-- The same retained original channel can be prepared for division without a supplied root or sample inequality. -/
private def prepare (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) :
    let retained := Degeneration.UnitRoot.owner site point inside
    Approximation.Gaussian.Division.Prepared (CertifiedSquareRoot.rawRoot retained.track) :=
  let retained := Degeneration.UnitRoot.owner site point inside
  SquareRootProvenance.prepared_of_square (CertifiedSquareRoot.rawRoot_square retained.track) retained.parameterNonzero

/-- Every state of the constructed track retains original cofactor winding one and the signed reference box. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) (index : Nat) :
    let retained := Degeneration.UnitRoot.owner site point inside
    Polynomial.Winding.Box.Basic.quadrupledBoxWinding
      (SquareRootContinuationChain.Owner.rootPolynomial ((Degeneration.unitPolynomial site).eval point))
      (CoherentRoot.state retained.track index).box = 4 ∧
      (CoherentRoot.state retained.track index).box.Refines (Degeneration.UnitRoot.box site) := by
  intro retained
  exact ⟨CoherentRoot.state_winding retained.track index,
    Degeneration.UnitRoot.owner_state_refines_box site point inside index⟩

/-- All actual sample indices share the same original signed box and uniform nonzero quadrance. -/
example (site : Fin 2) (point : Canonical) (inside : (Degeneration.spatialBox site).Contains point) (index : Nat) :
    let retained := Degeneration.UnitRoot.owner site point inside
    (Degeneration.UnitRoot.box site).Contains ((CertifiedSquareRoot.approximation retained.track).sample index) ∧
      (1 / 4 : Rat.Fraction.Rational) ≤
        Gaussian.Norm.Basic.normSq ((CertifiedSquareRoot.approximation retained.track).sample index) := by
  intro retained
  exact ⟨Degeneration.UnitRoot.sample_contains_box site point inside index,
    Degeneration.UnitRoot.sample_lower site point inside index⟩

/-- The boundary corner pays the maximal half-quadrance perturbation at the zero collision. -/
example : Gaussian.Norm.Basic.normSq (Degeneration.UnitRoot.seed 0 ^ 2 -
    (Degeneration.unitPolynomial 0).eval (⟨1 / 2, 1 / 2⟩ : Canonical)) = 1 / 2 := by
  rewrite [Degeneration.UnitRoot.displacement, Gaussian.Norm.Basic.normSq_neg]
  decide +kernel

/-- The same maximal perturbation is paid at the one collision, using its original cofactor. -/
example : Gaussian.Norm.Basic.normSq (Degeneration.UnitRoot.seed 1 ^ 2 -
    (Degeneration.unitPolynomial 1).eval (⟨3 / 2, 1 / 2⟩ : Canonical)) = 1 / 2 := by
  rewrite [Degeneration.UnitRoot.displacement, Gaussian.Norm.Basic.normSq_neg]
  decide +kernel

end TestPurelib.Curves.Legendre.UnitRoot
