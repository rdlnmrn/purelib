module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Localization
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Point
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Localization.Preparation

open Purelib
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

/-- A constant original source reading lies in the original selected root's initial box.

If a finite box test excludes that reading, its positive coordinate gap pays
one original operational comparison. The same original cached root sample
lies in the box and has smaller squared distance, contradicting that gap.
No original state or comparison producer is executed outside the proof. -/
theorem Selection.initial_contains_of_constant {polynomial : GaussianPolynomial}
    {input : FTA.Squarefree.Input polynomial} {original : Geometric.GeometricApproximation}
    {preparation : Preparation input original} (selection : Selection preparation) (point : Canonical)
    (constant : ∀ index, preparation.source.sample index = point) :
    (preparation.boxes.isolation.tracks.get selection.anchor.nearby.owner).initial.box.Contains point := by
  by_cases contains :
      (preparation.boxes.isolation.tracks.get selection.anchor.nearby.owner).initial.box.Contains point
  · exact contains
  · let separation := Geometry.Rational.Box.Point.separationCertificateOfNotContains
      (preparation.boxes.isolation.tracks.get selection.anchor.nearby.owner).initial.box point contains
    have positive := Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct separation.positive 2
    let comparison := selection.equivalent.symm.compare 0 0 (separation.gap ^ 2) positive
    have close := comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
    change Data.Gaussian.Norm.Basic.normSq
      (selection.root.approximation.sample comparison.leftIndex - original.sample comparison.rightIndex) <
        separation.gap ^ 2 at close
    have sourceEq := congrArg (fun source : Geometric.GeometricApproximation =>
      source.sample comparison.rightIndex) preparation.source_eq
    have sourceConstant := sourceEq.symm.trans (constant comparison.rightIndex)
    rewrite [sourceConstant] at close
    have lower := separation.lower (selection.root.sample_initial_inside comparison.leftIndex)
      (Geometry.Rational.Box.Point.pointBox_contains point)
    exact (not_lt_of_ge lower close).elim

/-- Identify the exact original selected owner from an original initial box containing a constant source reading.

The selected root's original box contains the same source point by its paid
operational comparison. Positive separation of distinct original owner boxes
identifies the supplied original index. Selection is used only in the equality
certificate; the runtime result retains the supplied finite index unchanged. -/
@[expose] def ownerFromInitialBox {polynomial : GaussianPolynomial}
    {input : FTA.Squarefree.Input polynomial} {original : Geometric.GeometricApproximation}
    (preparation : Preparation input original) (point : Canonical)
    (constant : ∀ index, preparation.source.sample index = point)
    (index : Fin preparation.boxes.isolation.tracks.length)
    (inside : (preparation.boxes.isolation.tracks.get index).initial.box.Contains point) :
    { owner : Fin preparation.boxes.isolation.tracks.length // owner = preparation.select.anchor.nearby.owner } :=
  ⟨index, by
    by_cases same : index = preparation.select.anchor.nearby.owner
    · exact same
    · have selectedInside := preparation.select.initial_contains_of_constant point constant
      have separated := preparation.boxes.isolation.tracks_get_separated index
        preparation.select.anchor.nearby.owner same
      rcases separated with left | right | bottom | top
      · exact (not_lt_of_ge (selectedInside.1.trans inside.2.1) left).elim
      · exact (not_lt_of_ge (inside.1.trans selectedInside.2.1) right).elim
      · exact (not_lt_of_ge (selectedInside.2.2.1.trans inside.2.2.2) bottom).elim
      · exact (not_lt_of_ge (inside.2.2.1.trans selectedInside.2.2.2) top).elim⟩

end Purelib.Riemann.RootContinuation.CoherentRoot.Localization.Preparation
