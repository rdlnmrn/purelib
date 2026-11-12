module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Preparation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Radial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field

/-! # Collar chart admission from the actual conic annulus

Both original conic coordinates obey the same radial outer bound. Their
exact half-sum therefore pays the original collar's centered-coordinate
test. The actual meridian transport preserves this bound at every rational
time. A given cubic lift and named sweep retain their owners and feed the
original native-tail, arithmetic-enclosure and cofactor-lift constructor.
No named base is converted to an exact Gaussian point or rooted mesh.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The actual regular annulus pays the centered-coordinate test for its recovered original cubic base.

The conic product derives the second radial bound from the first. The
same two coordinates and their exact half-sum give the fixed chart bound;
neither a cofactor root nor a new Point is acquired by this proof.
-/
theorem coordinate_bound {site : Fin 2} {parameter : Canonical} (point : Point site parameter)
    (regular : parameter ≠ criticalValue site) (inside : Contains site parameter point.plus) :
    Norm.Basic.normSq (coordinate site parameter point.base) ≤ (1 / 64 : Fraction.Rational) := by
  have partnerBound := (partner_contains regular inside).2
  have minusBound : Norm.Basic.normSq point.minus ≤ outerRadiusSq :=
    (congrArg Norm.Basic.normSq (point.minus_eq_div (coordinate_ne_zero regular inside))).trans_le partnerBound
  have bounded := point.abscissa_normSq_le outerRadiusSq inside.2 minusBound
  exact (congrArg Norm.Basic.normSq point.coordinate_base).trans_le
    (bounded.trans_eq (by decide +kernel : outerRadiusSq = (1 / 64 : Fraction.Rational)))

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Every actual meridian time retains chart admission at the transported conic Point's own fibre and base.

Regularity and annulus admission are transported by their original laws.
The centered-coordinate bound is then derived on that exact target Point;
no endpoint return or phase-additivity identity is used.
-/
theorem transport_coordinate_bound {site : Fin 2} {parameter : Canonical}
    (time : Fraction.Rational) (point : Point site parameter) (regular : parameter ≠ criticalValue site)
    (inside : Contains site parameter point.plus) :
    Norm.Basic.normSq
      (coordinate site (parameterAt site parameter time) (transport time point).base) ≤
        (1 / 64 : Fraction.Rational) :=
  Annulus.coordinate_bound (transport time point) (regular_at regular time) (transport_contains time point inside)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

namespace Purelib.Curves.Legendre.Degeneration.Conic.Lift

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Legendre.Degeneration.CoordinateChannels (Profile Sweep)
open Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep (Reconstruction)

variable {site : Fin 2} {parameter : Canonical} {point : Point site parameter}
variable {unit : Owner ((unitPolynomial site).eval point.base)} (original : Lift point unit)
variable {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
variable {profile : Profile original.coordinates bound} {time : Fraction.Rational}
variable {rotated : Sweep original.coordinates bound profile time} (actual : Reconstruction rotated)

/-- The retained raw profile has the exact radial value of its original conic coordinate.

The original signed plus-channel comparison supplies the finite floors.
The actual profile and its arithmetic sample factory are consumed unchanged;
no raw-height boundary certificate or new sampler is supplied by the caller.
-/
def profile_height : Equivalent profile.1.val.toApproximation
    (Sequence.Constant.constantApproximation
      (⟨Annulus.Twist.radialParameter site parameter point.plus, 0⟩ : Canonical)) := by
  have compared := CoordinateChannels.Profile.raw_to_exact (channels := original.coordinates) (bound := bound)
    profile point.plus original.plus_agrees
  rewrite [Annulus.Twist.Collar.range_lower, Annulus.Twist.Collar.range_width] at compared
  exact compared

/-- The actual forward sweep channel agrees with the exact original conic rotation coordinate at the same time. -/
def plus_at (inside : Annulus.Contains site parameter point.plus) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    NamedEquivalent rotated.2.1.val.name
      (Named.exact (point.plus * (Annulus.Twist.phase
        (time * Annulus.Twist.radialParameter site parameter point.plus)).value)) := by
  have forward := Annulus.Twist.Collar.PhaseNames.forward_boundary
    (height := profile.1.val) (clipped := profile.2) (time := time) rotated.1.val timeInside
    (Annulus.Twist.radialParameter site parameter point.plus)
    (Annulus.Twist.radialParameter_inside (site := site) (parameter := parameter) (coordinate := point.plus)
      bound inside)
    (original.profile_height (bound := bound) (profile := profile))
  have product := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    original.coordinates.plus (Coherence.exact point.plus) rotated.1.val.2.val.1
    (Coherence.exact (Annulus.Twist.phase (time * Annulus.Twist.radialParameter site parameter point.plus)).value)
    original.plus_agrees forward
  exact NamedEquivalent.transport (congrArg CoherentNamed.name rotated.2.1.property.symm) rfl
    (product.trans (Name.Coherent.Exact.Arithmetic.exact_mul point.plus
      (Annulus.Twist.phase (time * Annulus.Twist.radialParameter site parameter point.plus)).value))

/-- The actual backward sweep channel agrees with the same exact rotation's conjugate coordinate. -/
def minus_at (inside : Annulus.Contains site parameter point.plus) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    NamedEquivalent rotated.2.2.1.val.name
      (Named.exact (point.minus * (Annulus.Twist.phase
        (time * Annulus.Twist.radialParameter site parameter point.plus)).value.conj)) := by
  have backward := Annulus.Twist.Collar.PhaseNames.backward_boundary
    (height := profile.1.val) (clipped := profile.2) (time := time) rotated.1.val timeInside
    (Annulus.Twist.radialParameter site parameter point.plus)
    (Annulus.Twist.radialParameter_inside (site := site) (parameter := parameter) (coordinate := point.plus)
      bound inside)
    (original.profile_height (bound := bound) (profile := profile))
  have product := Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    original.coordinates.minus (Coherence.exact point.minus) rotated.1.val.2.val.2.1
    (Coherence.exact
      ((Annulus.Twist.phase (time * Annulus.Twist.radialParameter site parameter point.plus)).value.conj))
    original.minus_agrees backward
  exact NamedEquivalent.transport (congrArg CoherentNamed.name rotated.2.2.1.property.symm) rfl
    (product.trans (Name.Coherent.Exact.Arithmetic.exact_mul point.minus
      ((Annulus.Twist.phase (time * Annulus.Twist.radialParameter site parameter point.plus)).value.conj)))

/-- The completed actual forward sweep agrees with the independently defined annular twist on the given conic Point. -/
def plus_twist (rotated : Sweep original.coordinates bound profile 1)
    (inside : Annulus.Contains site parameter point.plus) :
    NamedEquivalent rotated.2.1.val.name (Named.exact (Annulus.annularTwist point).plus) := by
  have compared := original.plus_at (bound := bound) (profile := profile) (time := 1) (rotated := rotated) inside
    ⟨by decide +kernel, Fraction.Order.Basic.le_refl 1⟩
  have phaseSame := congrArg (fun position : Fraction.Rational => (Annulus.Twist.phase position).value)
    (Fraction.Field.one_mul (Annulus.Twist.radialParameter site parameter point.plus))
  have coordinate := (congrArg (fun phase : Canonical => point.plus * phase) phaseSame).trans
    (Annulus.annularTwist_plus point).symm
  exact NamedEquivalent.transport rfl (congrArg Named.exact coordinate) compared

/-- The completed actual backward sweep agrees with the same independently defined annular twist's minus coordinate. -/
def minus_twist (rotated : Sweep original.coordinates bound profile 1)
    (inside : Annulus.Contains site parameter point.plus) :
    NamedEquivalent rotated.2.2.1.val.name (Named.exact (Annulus.annularTwist point).minus) := by
  have compared := original.minus_at (bound := bound) (profile := profile) (time := 1) (rotated := rotated) inside
    ⟨by decide +kernel, Fraction.Order.Basic.le_refl 1⟩
  have phaseSame := congrArg (fun position : Fraction.Rational => (Annulus.Twist.phase position).value)
    (Fraction.Field.one_mul (Annulus.Twist.radialParameter site parameter point.plus))
  have coordinate := (congrArg (fun phase : Canonical => point.minus * phase.conj) phaseSame).trans
    (Annulus.annularTwist_minus point).symm
  exact NamedEquivalent.transport rfl (congrArg Named.exact coordinate) compared

/-- Prepare the given original named collar reconstruction using chart admission derived from its exact annulus input.

The original cubic lift, profile, paired phase and reconstruction are given
unchanged. One exact coordinate/coefficient pair feeds the original native
tail, arithmetic enclosure and signed cofactor lift. Every admitted sweep
time is supported; this supplies no spatial-parameter mesh or root-owner
incidence certificate for the changed named base.
-/
def prepareCollarAt (regular : parameter ≠ criticalValue site)
    (inside : Annulus.Contains site parameter point.plus) (floor : Nat) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    Reconstruction.Prepared actual
      ⟨coordinate site parameter point.base, rfl⟩
      ⟨(coordinate site parameter point.base) ^ 2 - smoothing site parameter, rfl⟩
      floor timeInside (Annulus.coordinate_bound point regular inside) :=
  let coordinateCache : {value : Canonical // value = coordinate site parameter point.base} :=
    ⟨coordinate site parameter point.base, rfl⟩
  let parameterCache : {value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter} :=
    ⟨coordinateCache.val ^ 2 - smoothing site parameter, rfl⟩
  Reconstruction.prepareAt actual coordinateCache parameterCache floor timeInside
    (Annulus.coordinate_bound point regular inside)

end Purelib.Curves.Legendre.Degeneration.Conic.Lift

end
