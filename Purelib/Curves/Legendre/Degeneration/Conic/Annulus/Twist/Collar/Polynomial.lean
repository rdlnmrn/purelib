module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Cofactor
public import Purelib.Curves.Legendre.Degeneration.Polynomial
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Data.Fin

/-! # The original cubic at a retained named collar base

The original centered-base factory and the supplied signed cofactor lift
compare the new ordinate square with the original Legendre Horner program.
The original named base and ordinate remain distinct retained channels; no
exact Gaussian point or new root-equivalence owner is introduced.
-/

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    {profile : Profile channels bound} {time : Fraction.Rational}
    {rotated : Sweep channels bound profile time} (actual : Reconstruction rotated)

/-- The original whole base factory removes the same midpoint and recovers its retained abscissa channel. -/
private def translated_base :
    NamedEquivalent (actual.2.1.val.add (Coherence.exact (center site parameter)).neg).name actual.1.val.name := by
  let bindings : Fin 2 → CoherentNamed :=
    Data.Fin.cases actual.1.val (fun _ => Coherence.exact (center site parameter))
  let x := Normalized.atom bindings 0
  let origin := Normalized.atom bindings 1
  let base := (origin.add x).transport actual.2.1.property.symm
  let translated := base.sub origin
  have baseForm : base.form = (origin.add x).form :=
    Normalized.transport_form (origin.add x) actual.2.1.property.symm
  have forms : translated.form.terms = x.form.terms := by
    dsimp only [translated]
    rewrite [Normalized.sub_form, baseForm]
    dsimp only [origin, x]
    simp only [Normalized.add_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  exact translated.compare x forms

public section

/-- The actual re-lifted ordinate square agrees with a GIVEN original Horner output on the same named base.

Every centered factor is obtained from the supplied reconstruction's whole
factories. The cofactor root and factorized square are the supplied lift's
cached values. The supplied source, phase, cofactor-root and Horner caches
remain unchanged. Normalization constructs auxiliary arithmetic channels and
their finite operational comparisons.
-/
def polynomial_agrees (base : Enclosure actual.2.1.val)
    (contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value)
    (lifted : Lift actual base contained)
    (evaluated : { value : CoherentNamed //
      value = Horner.polynomialEval (Paths.polynomial parameter) actual.2.1.val }) :
    NamedEquivalent (lifted.2.2.1.val.mul lifted.2.2.1.val).name evaluated.val.name := by
  let centered := actual.2.1.val.add (Coherence.exact (center site parameter)).neg
  let cofactor := actual.2.1.val.add (Coherence.exact (-(remainingValue site)))
  have shifted : NamedEquivalent centered.name actual.1.val.name := translated_base actual
  have squares := Product.Congruence.coherentMul_respects
    centered actual.1.val centered actual.1.val shifted shifted
  have cores := Sum.Congruence.coherentAdd_respects
    (centered.mul centered) (actual.1.val.mul actual.1.val)
    (Coherence.exact (smoothing site parameter)).neg (Coherence.exact (smoothing site parameter)).neg
    squares (NamedEquivalent.refl _)
  have cofactorRead : NamedEquivalent cofactor.name actual.2.2.2.1.val.name :=
    NamedEquivalent.transport rfl (congrArg CoherentNamed.name actual.2.2.2.1.property.symm)
      (NamedEquivalent.refl cofactor.name)
  have factors := Product.Congruence.coherentMul_respects
    ((centered.mul centered).add (Coherence.exact (smoothing site parameter)).neg)
    ((actual.1.val.mul actual.1.val).add (Coherence.exact (smoothing site parameter)).neg)
    cofactor actual.2.2.2.1.val cores cofactorRead
  have original := polynomialEval_centered site parameter actual.2.1.val evaluated
  exact lifted.2.2.2.trans (original.trans factors).symm

/-- Evaluate the original cubic once on the retained base, keeping its output, factory, and derived square law. -/
def evaluate (base : Enclosure actual.2.1.val)
    (contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value)
    (lifted : Lift actual base contained) :
    (evaluated : { value : CoherentNamed //
      value = Horner.polynomialEval (Paths.polynomial parameter) actual.2.1.val }) ×
      NamedEquivalent (lifted.2.2.1.val.mul lifted.2.2.1.val).name evaluated.val.name := by
  let evaluated := Horner.polynomialEval (Paths.polynomial parameter) actual.2.1.val
  let cached : { value : CoherentNamed //
      value = Horner.polynomialEval (Paths.polynomial parameter) actual.2.1.val } := ⟨evaluated, rfl⟩
  let compared := polynomial_agrees actual base contained lifted cached
  exact ⟨cached, compared⟩

end

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction
