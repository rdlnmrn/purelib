module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Comparison
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Coherent.Additive
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Named coordinate reconstruction of the retained collar sweep

The actual rotated plus/minus names determine a named base, normalized
ordinate and affine cofactor. Their conic relation follows from the same
retained smoothing-product comparison. These names are not exact Gaussian
points, and the new affine cofactor still needs a signed root continuation.
-/

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep

/-- Half-sum and half-difference programs satisfy the same named conic relation as their original product. -/
private def quadratic (plus minus : CoherentNamed) (smoothing : Canonical)
    (product : NamedEquivalent (plus.mul minus).name (Named.exact smoothing)) :
    NamedEquivalent
      (((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus.neg)).mul
        ((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus.neg))).name
      ((((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus)).mul
        ((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus))).add
        (Coherence.exact smoothing).neg).name := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases plus (fun _ => minus)
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let half := Normalized.constant bindings (1 / 2)
  let abscissa := half.mul (a.add b)
  let ordinate := half.mul (a.sub b)
  let left := ordinate.mul ordinate
  let right := (abscissa.mul abscissa).sub (a.mul b)
  have forms : left.form.terms = right.form.terms := by
    dsimp only [left, right, abscissa, ordinate, half, a, b]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.sub_form,
      Normalized.constant_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  have identity := left.compare right forms
  have replace := Sum.Congruence.coherentAdd_respects
    (((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus)).mul
      ((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus)))
    (((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus)).mul
      ((Coherence.exact (1 / 2 : Canonical)).mul (plus.add minus)))
    (plus.mul minus).neg (Coherence.exact smoothing).neg (NamedEquivalent.refl _)
    (Coherent.Additive.coherentNeg_respects _ _ product)
  exact identity.trans replace

public section

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    {profile : Profile channels bound} {time : Fraction.Rational}

/-- Actual named reconstruction retains four arithmetic caches and their original conic-product comparison. -/
@[expose] def Reconstruction (rotated : Sweep channels bound profile time) : Type _ :=
  (abscissa : { value : CoherentNamed // value = (Coherence.exact (1 / 2 : Canonical)).mul
    (rotated.2.1.val.add rotated.2.2.1.val) }) ×
  (base : { value : CoherentNamed // value = (Coherence.exact (center site parameter)).add abscissa.val }) ×
  (ordinate : { value : CoherentNamed // value = (Coherence.exact (1 / 2 : Canonical)).mul
    (rotated.2.1.val.add rotated.2.2.1.val.neg) }) ×
  (_ : { value : CoherentNamed // value = base.val.add (Coherence.exact (-(remainingValue site))) }) ×
    NamedEquivalent (ordinate.val.mul ordinate.val).name
      ((abscissa.val.mul abscissa.val).add (Coherence.exact (smoothing site parameter)).neg).name

/-- Reconstruct the named base, normalized ordinate and affine cofactor once from the SAME retained sweep. -/
def reconstruct (rotated : Sweep channels bound profile time) : Reconstruction rotated := by
  let abscissa := (Coherence.exact (1 / 2 : Canonical)).mul
    (rotated.2.1.val.add rotated.2.2.1.val)
  let base := (Coherence.exact (center site parameter)).add abscissa
  let ordinate := (Coherence.exact (1 / 2 : Canonical)).mul
    (rotated.2.1.val.add rotated.2.2.1.val.neg)
  let cofactor := base.add (Coherence.exact (-(remainingValue site)))
  let compared := quadratic rotated.2.1.val rotated.2.2.1.val (smoothing site parameter) rotated.2.2.2
  exact ⟨⟨abscissa, rfl⟩, ⟨base, rfl⟩, ⟨ordinate, rfl⟩, ⟨cofactor, rfl⟩, compared⟩

/-- The actual time-zero forward rotated channel agrees with the original plus channel. -/
def plus_zero (rotated : Sweep channels bound profile 0) :
    NamedEquivalent rotated.2.1.val.name channels.plus.name := by
  have unchanged := Product.Congruence.coherentMul_respects
    channels.plus channels.plus rotated.1.val.2.val.1 (Coherence.exact 1) (NamedEquivalent.refl _)
    (Collar.PhaseNames.forward_zero (height := profile.1.val) (clipped := profile.2) rotated.1.val)
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name rotated.2.1.property.symm) rfl
      (unchanged.trans (Arithmetic.Mul.coherentMul_one_right channels.plus))

/-- The actual time-zero backward rotated channel agrees with the original minus channel. -/
def minus_zero (rotated : Sweep channels bound profile 0) :
    NamedEquivalent rotated.2.2.1.val.name channels.minus.name := by
  have unchanged := Product.Congruence.coherentMul_respects
    channels.minus channels.minus rotated.1.val.2.val.2.1 (Coherence.exact 1) (NamedEquivalent.refl _)
    (Collar.PhaseNames.backward_zero (height := profile.1.val) (clipped := profile.2) rotated.1.val)
  exact NamedEquivalent.transport
    (congrArg CoherentNamed.name rotated.2.2.1.property.symm) rfl
      (unchanged.trans (Arithmetic.Mul.coherentMul_one_right channels.minus))

namespace Reconstruction

variable {rotated : Sweep channels bound profile 0} (actual : Reconstruction rotated)

/-- The SAME reconstructed named base at zero time agrees operationally with the original exact base. -/
def base_zero : NamedEquivalent actual.2.1.val.name (Named.exact point) := by
  have sum := Sum.Congruence.coherentAdd_respects
    rotated.2.1.val channels.plus rotated.2.2.1.val channels.minus
    (plus_zero rotated) (minus_zero rotated)
  have scaled := Product.Congruence.coherentMul_respects
    (Coherence.exact (1 / 2 : Canonical)) (Coherence.exact (1 / 2 : Canonical))
    (rotated.2.1.val.add rotated.2.2.1.val) (channels.plus.add channels.minus)
    (NamedEquivalent.refl _) sum
  have centered : NamedEquivalent actual.1.val.name
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus)).name :=
    NamedEquivalent.transport (congrArg CoherentNamed.name actual.1.property.symm) rfl scaled
  have shifted := Sum.Congruence.coherentAdd_respects
    (Coherence.exact (center site parameter)) (Coherence.exact (center site parameter))
    actual.1.val ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus))
    (NamedEquivalent.refl _) centered
  have original := NamedEquivalent.transport rfl
    (congrArg CoherentNamed.name (CoordinateChannels.readPoint_eq channels).symm) shifted
  exact (NamedEquivalent.transport
    (congrArg CoherentNamed.name actual.2.1.property.symm) rfl original).trans
      (CoordinateChannels.readPoint_agrees channels)

/-- The SAME zero-time normalized ordinate recovers the original signed channel with its retained cofactor root. -/
def source_zero :
    NamedEquivalent (channels.unitRoot.value.mul actual.2.2.1.val).name source.name := by
  have negative := Coherent.Additive.coherentNeg_respects _ _ (minus_zero rotated)
  have difference := Sum.Congruence.coherentAdd_respects
    rotated.2.1.val channels.plus rotated.2.2.1.val.neg channels.minus.neg (plus_zero rotated) negative
  have scaled := Product.Congruence.coherentMul_respects
    (Coherence.exact (1 / 2 : Canonical)) (Coherence.exact (1 / 2 : Canonical))
    (rotated.2.1.val.add rotated.2.2.1.val.neg) (channels.plus.add channels.minus.neg)
    (NamedEquivalent.refl _) difference
  have centered : NamedEquivalent actual.2.2.1.val.name
      ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg)).name :=
    NamedEquivalent.transport (congrArg CoherentNamed.name actual.2.2.1.property.symm) rfl scaled
  have restored := Product.Congruence.coherentMul_respects
    channels.unitRoot.value channels.unitRoot.value actual.2.2.1.val
    ((Coherence.exact (1 / 2 : Canonical)).mul (channels.plus.add channels.minus.neg))
    (NamedEquivalent.refl _) centered
  exact (NamedEquivalent.transport rfl
    (congrArg CoherentNamed.name (CoordinateChannels.readOrdinate_eq channels).symm) restored).trans
      (CoordinateChannels.readOrdinate_agrees channels)

/-- The SAME new named cofactor at zero time agrees with the original affine cofactor evaluation. -/
def cofactor_zero : NamedEquivalent actual.2.2.2.1.val.name
    (Named.exact ((unitPolynomial site).eval point)) := by
  have shifted := Sum.Congruence.coherentAdd_respects
    actual.2.1.val (Coherence.exact point) (Coherence.exact (-(remainingValue site)))
    (Coherence.exact (-(remainingValue site)))
    (base_zero (channels := channels) (profile := profile) (rotated := rotated) actual) (NamedEquivalent.refl _)
  have replace := NamedEquivalent.transport
    (congrArg CoherentNamed.name actual.2.2.2.1.property.symm) rfl shifted
  have scalar : point + -(remainingValue site) = (unitPolynomial site).eval point := by
    rewrite [unitPolynomial, Polynomial.Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    ring1
  exact replace.trans (NamedEquivalent.transport rfl (congrArg Named.exact scalar)
    (Name.Coherent.Exact.Arithmetic.exact_add _ _))

end Reconstruction

end

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep
