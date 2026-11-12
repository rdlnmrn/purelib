module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Geometry.Rational.Box.Square.Centered.Separation.Distance
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Division.Cancellation

/-! # Agreement at identical original parameter endpoints

Two independently retained source lifts may describe the same exact base and
normalized ordinate. Their actual admitted parameter steps retain both original
signed Seed windows and root certificates. A positive sum floor on all original
samples proves agreement without identifying or rebuilding either owner.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter increment : Canonical} {firstDirection lastDirection : UnitVertex}
variable {firstUnit : Owner ((unitPolynomial site).eval (sourcePoint site parameter firstDirection).base)}
variable {lastUnit : Owner ((unitPolynomial site).eval (sourcePoint site parameter lastDirection).base)}
variable {firstSource : Lift (sourcePoint site parameter firstDirection) firstUnit}
variable {lastSource : Lift (sourcePoint site parameter lastDirection) lastUnit}

namespace Anchor

/-- An actual full-source comparison and equal normalized ordinates compare the two original cofactor caches.

Both retained source products agree with their original Lift.value channels.
The independently retained Seed certificates agree with the exact source
ordinate. Product congruence and commutation put the same original first Seed
on the left of both products; its actual apartness pays cancellation. No new
original Reading, cofactor owner or desired target comparison is supplied.
-/
def unit_agrees_of_source_eq (first : Anchor firstSource) (last : Anchor lastSource)
    (full_agrees : NamedEquivalent firstSource.value.name lastSource.value.name)
    (ordinate_eq : (sourcePoint site parameter firstDirection).ordinate =
      (sourcePoint site parameter lastDirection).ordinate) :
    NamedEquivalent firstSource.unitRoot.value.name lastSource.unitRoot.value.name := by
  let firstSeed := first.seed.certificate.value
  let lastSeed := last.seed.certificate.value
  have seeds : NamedEquivalent firstSeed.name lastSeed.name :=
    (NamedEquivalent.transport rfl (congrArg Named.exact ordinate_eq) first.seed.agrees_exact).trans
      last.seed.agrees_exact.symm
  have products : NamedEquivalent (firstSource.unitRoot.value.mul firstSeed).name
      (lastSource.unitRoot.value.mul lastSeed).name :=
    first.source_agrees.trans (full_agrees.trans last.source_agrees.symm)
  have shifted := Congruence.coherentMul_respects
    lastSource.unitRoot.value lastSource.unitRoot.value lastSeed firstSeed (NamedEquivalent.refl _) seeds.symm
  have common := (Laws.coherentMul_comm firstSeed firstSource.unitRoot.value).trans
    (products.trans (shifted.trans (Laws.coherentMul_comm lastSource.unitRoot.value firstSeed)))
  exact Division.Cancellation.coherentMul_cancel_left firstSeed firstSource.unitRoot.value lastSource.unitRoot.value
    first.seed.certificate.apart common

end Anchor

namespace Step

/-- Identical exact source coordinates give operational agreement of the two retained normalized target roots.

The original target candidates remain in their respective signed source
windows. The exact ordinate equality pays their center displacement; the
same-radicand square identities and positive sum floor then invoke the general
comparison procedure with both original consumer indices preserved.
-/
def root_agrees_of_source_eq (first : Anchor firstSource) (last : Anchor lastSource)
    (firstStep : Step first increment) (lastStep : Step last increment)
    (base_eq : (sourcePoint site parameter firstDirection).base =
      (sourcePoint site parameter lastDirection).base)
    (ordinate_eq : (sourcePoint site parameter firstDirection).ordinate =
      (sourcePoint site parameter lastDirection).ordinate) :
    NamedEquivalent firstStep.root.value.name lastStep.root.value.name := by
  have radicand_eq : radicand site parameter firstDirection increment =
      radicand site parameter lastDirection increment := by
    unfold radicand branchFactor
    rewrite [base_eq, ordinate_eq]
    rfl
  have lastSquare : SquareRootProvenance.SquareIdentity lastStep.root.value
      (radicand site parameter firstDirection increment) := by
    rewrite [radicand_eq]
    exact lastStep.root.square
  have near : Norm.Basic.normSq
      ((sourcePoint site parameter lastDirection).ordinate -
        (sourcePoint site parameter firstDirection).ordinate) ≤
      first.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256 := by
    have difference_eq : (sourcePoint site parameter lastDirection).ordinate -
        (sourcePoint site parameter firstDirection).ordinate = 0 := by
      rewrite [ordinate_eq, Basic.sub_self]
      rfl
    rewrite [difference_eq, show Norm.Basic.normSq (0 : Canonical) = 0 by decide +kernel]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel)
  apply SquareRootProvenance.equivalent_of_sum_lower firstStep.root.square lastSquare
    (first.seed.separation.radius ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct first.seed.separation.positive 2)
  intro leftIndex rightIndex
  have firstPossible := Process.Sampling.witnessAt_possible
    firstStep.root.value.name.process firstStep.root.value.name.state leftIndex
  have lastPossible := Process.Sampling.witnessAt_possible
    lastStep.root.value.name.process lastStep.root.value.name.state rightIndex
  have firstContained := firstStep.target_candidate_inside firstPossible
  have lastContained := lastStep.target_candidate_inside lastPossible
  have paid := first.seed.separation.near_sum_normSq_lower last.seed.separation near firstContained lastContained
  rewrite [Norm.Basic.normSq_eq_canonical] at paid
  exact paid

/-- Equal exact source coordinates and an original cofactor comparison give agreement of the full target cubic channels.

Both products use their own retained source cofactor and admitted normalized
root caches. The generic product comparison preserves the supplied cofactor
processes and the internally derived normalized-root comparison.
-/
def value_agrees_of_source_eq (first : Anchor firstSource) (last : Anchor lastSource)
    (firstStep : Step first increment) (lastStep : Step last increment)
    (base_eq : (sourcePoint site parameter firstDirection).base =
      (sourcePoint site parameter lastDirection).base)
    (ordinate_eq : (sourcePoint site parameter firstDirection).ordinate =
      (sourcePoint site parameter lastDirection).ordinate)
    (unit_agrees : NamedEquivalent firstSource.unitRoot.value.name lastSource.unitRoot.value.name) :
    NamedEquivalent firstStep.value.name lastStep.value.name := by
  have compared := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    firstSource.unitRoot.value lastSource.unitRoot.value firstStep.root.value lastStep.root.value
    unit_agrees (root_agrees_of_source_eq first last firstStep lastStep base_eq ordinate_eq)
  exact NamedEquivalent.transport
    (congrArg (fun value : Name.Coherent.CoherentNamed => value.name) firstStep.value_eq.symm)
    (congrArg (fun value : Name.Coherent.CoherentNamed => value.name) lastStep.value_eq.symm) compared

end Step

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter

end
