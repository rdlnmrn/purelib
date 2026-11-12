module

public import Purelib.Curves.Legendre.Degeneration.Coordinates
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Variation
public import Purelib.Approximation.Gaussian.Geometric.Clipping
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Rat.Interval.Unit.Clamp
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Constant
import Purelib.Data.Gaussian.Components.Projection
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Finite intrinsic collar profiles on actual named conic channels

The original named plus-channel sampler supplies the squared-radius stream.
Its equal-index arithmetic computes the original annulus height, and finite
unit clipping plus the actual phase variation constructs a productive unit
phase. Rotation consumes the SAME original plus/minus names and preserves
the original smoothing product. No exact Gaussian Point is manufactured.
-/

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

/-- Squared real-coordinate displacement is bounded by the SAME Gaussian displacement. -/
private theorem real_difference_le (first last : Canonical) :
    (first.re - last.re) ^ 2 ≤ Norm.Basic.normSq (first - last) := by
  have actual := Components.Projection.normSq_realPart_le (first - last)
  have scalar : Norm.Basic.normSq (Components.Projection.realPart (first - last)) =
      (first.re - last.re) ^ 2 := by
    change (first.re - last.re) ^ 2 + (0 : Fraction.Rational) ^ 2 = _
    ring1
  exact scalar.symm.trans_le actual

public section

/-- Evaluate the ACTUAL rational phase on clipped real samples, with derived geometric density64. -/
def phaseOfReal (source : GeometricApproximation) : GeometricApproximation where
  sample := fun index => (Twist.phase (Interval.Unit.clamp (source.sample index).re)).value
  errorScale := 64 * source.errorScale
  errorScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have phaseBound := Twist.phase_distance_le
      (Interval.Unit.clamp (source.sample later).re) (Interval.Unit.clamp (source.sample earlier).re)
      (Interval.Unit.clamp_inside _) (Interval.Unit.clamp_inside _)
    have clipping := Interval.Unit.clamp_distance_le (source.sample earlier).re (source.sample later).re
    have projection : ((source.sample earlier).re - (source.sample later).re) ^ 2 ≤
        Norm.Basic.normSq (source.sample later - source.sample earlier) :=
      (show ((source.sample earlier).re - (source.sample later).re) ^ 2 =
        ((source.sample later).re - (source.sample earlier).re) ^ 2 by ring1).trans_le
          (real_difference_le _ _)
    exact (phaseBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (clipping.trans (projection.trans (source.later_close order))) (by decide +kernel))).trans_eq (by
        rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
        ring1)
  centerBound := 1
  centerBound_nonneg := by decide +kernel
  sample_bounded := fun index => (Twist.phase (Interval.Unit.clamp (source.sample index).re)).unit.le

/-- Every actual finite phase sample has exact unit quadrance. -/
theorem phaseOfReal_unit (source : GeometricApproximation) (index : Nat) :
    Norm.Basic.normSq ((phaseOfReal source).sample index) = 1 :=
  (Twist.phase (Interval.Unit.clamp (source.sample index).re)).unit

/-- The original annulus interval retains both squared radii and the actual strict-width proof. -/
def range (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) : Interval :=
  ⟨innerRadiusSq site parameter, outerRadiusSq, (Twist.proper site parameter bound).le⟩

/-- The retained collar interval starts at the same original squared inner radius. -/
theorem range_lower (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    (range site parameter bound).lower = innerRadiusSq site parameter := by
  unfold range
  rfl

/-- The retained collar width is the same original squared-radius difference. -/
theorem range_width (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    (range site parameter bound).width = outerRadiusSq - innerRadiusSq site parameter := by
  unfold range Interval.width
  rfl

/-- The SAME retained original annulus interval has a strictly positive width. -/
theorem range_width_positive (site : Fin 2) (parameter : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    0 < (range site parameter bound).width :=
  Fraction.Order.Arithmetic.sub_pos_direct (Twist.proper site parameter bound)

/-- Compute the actual equal-index squared-radius height on one retained rational interval. -/
def radial (range : Interval) (source : GeometricApproximation) : GeometricApproximation :=
  let squared := source.mul source.conj
  let translated := squared.sub (GeometricApproximation.exact ⟨range.lower, 0⟩)
  translated.mul (GeometricApproximation.exact ⟨range.width⁻¹, 0⟩)

/-- Each height sample is the original squared-radius sample normalized by the SAME retained interval width. -/
theorem radial_sample (range : Interval) (source : GeometricApproximation) (index : Nat) :
    ((radial range source).sample index).re =
      (Norm.Basic.normSq (source.sample index) - range.lower) / range.width := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct]
  unfold radial
  rewrite [GeometricApproximation.mul_sample, GeometricApproximation.sub_sample,
    GeometricApproximation.mul_sample, GeometricApproximation.conj_sample,
    GeometricApproximation.exact_sample, GeometricApproximation.exact_sample]
  change (((source.sample index).re * (source.sample index).re -
    (source.sample index).im * (-(source.sample index).im) - range.lower) * range.width⁻¹ -
      ((source.sample index).re * (-(source.sample index).im) +
        (source.sample index).im * (source.sample index).re - 0) * 0) = _
  unfold Norm.Basic.normSq
  ring1

/-- Every actual raw height sample is the real normalized quadrance of its same original coordinate sample. -/
theorem radial_sample_eq (range : Interval) (source : GeometricApproximation) (index : Nat) :
    (radial range source).sample index =
      (⟨(Norm.Basic.normSq (source.sample index) - range.lower) / range.width, 0⟩ : Canonical) := by
  apply Basic.ext
  · exact radial_sample range source index
  · unfold radial
    rewrite [GeometricApproximation.mul_sample, GeometricApproximation.sub_sample,
      GeometricApproximation.mul_sample, GeometricApproximation.conj_sample,
      GeometricApproximation.exact_sample, GeometricApproximation.exact_sample]
    change ((source.sample index).re * (source.sample index).re -
      (source.sample index).im * (-(source.sample index).im) - range.lower) * 0 +
        ((source.sample index).re * (-(source.sample index).im) +
          (source.sample index).im * (source.sample index).re - 0) * range.width⁻¹ = 0
    ring1

/-- Scale the SAME retained clipped height by the actual sweep time before phase evaluation. -/
def phase {height : GeometricApproximation}
    (clipped : { value : GeometricApproximation // value = height.clipReal })
    (time : Fraction.Rational) : GeometricApproximation :=
  phaseOfReal (clipped.val.mul (GeometricApproximation.exact ⟨time, 0⟩))

/-- At every admitted sweep time, clipping precedes multiplication in the ACTUAL phase sample formula. -/
theorem phase_sample {height : GeometricApproximation}
    (clipped : { value : GeometricApproximation // value = height.clipReal })
    (time : Fraction.Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) (index : Nat) :
    (phase (height := height) clipped time).sample index =
      (Twist.phase (time * Interval.Unit.clamp (height.sample index).re)).value := by
  have pointEq : clipped.val.sample index =
      (⟨Interval.Unit.clamp (height.sample index).re, 0⟩ : Canonical) :=
    (congrArg (fun value : GeometricApproximation => value.sample index) clipped.property).trans
      (GeometricApproximation.clipReal_sample height index)
  have heightInside := Interval.Unit.clamp_inside (height.sample index).re
  have scaledInside : 0 ≤ time * Interval.Unit.clamp (height.sample index).re ∧
      time * Interval.Unit.clamp (height.sample index).re ≤ 1 :=
    ⟨Fraction.Order.Arithmetic.mul_nonneg_direct timeInside.1 heightInside.1,
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct timeInside.2 heightInside.1).trans_eq
        (Fraction.Field.one_mul _)).trans heightInside.2⟩
  change (Twist.phase (Interval.Unit.clamp
    ((clipped.val.mul (GeometricApproximation.exact ⟨time, 0⟩)).sample index).re)).value = _
  rewrite [GeometricApproximation.mul_sample, GeometricApproximation.exact_sample, pointEq]
  change (Twist.phase (Interval.Unit.clamp
    (Interval.Unit.clamp (height.sample index).re * time - 0 * 0))).value = _
  have same : Interval.Unit.clamp (height.sample index).re * time - 0 * 0 =
      time * Interval.Unit.clamp (height.sample index).re := by ring1
  rewrite [same, Interval.Unit.clamp_eq scaledInside]
  rfl

/-- Two actual named phase channels retain their original operational unit-product comparison. -/
@[expose] def UnitPair : Type _ :=
  (forward : CoherentNamed) × (backward : CoherentNamed) ×
    NamedEquivalent (forward.mul backward).name (Named.exact 1)

/-- A phase cache and its two actual arithmetic names retain the complete original factories. -/
@[expose] def PhaseNames {height : GeometricApproximation}
    (clipped : { value : GeometricApproximation // value = height.clipReal })
    (time : Fraction.Rational) : Type _ :=
  (cached : { value : GeometricApproximation // value = phase (height := height) clipped time }) ×
  { pair : UnitPair //
    pair.1 = CoherentNamed.ofApproximation cached.val.toApproximation ∧
    pair.2.1 = CoherentNamed.ofApproximation cached.val.conj.toApproximation }

/-- Construct one actual unit phase and its inverse names from the SAME retained height before numerical requests. -/
def phaseNames {height : GeometricApproximation}
    (clipped : { value : GeometricApproximation // value = height.clipReal })
    (time : Fraction.Rational) : PhaseNames (height := height) clipped time := by
  let cached := phase (height := height) clipped time
  let inverse := cached.conj
  let forward := CoherentNamed.ofApproximation cached.toApproximation
  let backward := CoherentNamed.ofApproximation inverse.toApproximation
  have unit : ∀ index, Norm.Basic.normSq (cached.sample index) = 1 :=
    phaseOfReal_unit (clipped.val.mul (GeometricApproximation.exact ⟨time, 0⟩))
  have compared : NamedEquivalent (forward.mul backward).name (Named.exact 1) :=
    (Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise cached.toApproximation
      inverse.toApproximation (Sequence.Constant.constantApproximation 1) (by
        intro index
        change (1 : Canonical) = cached.sample index * (cached.sample index).conj
        have product := Basic.Canonical.mul_conj (cached.sample index)
        rewrite [← Norm.Basic.normSq_eq_canonical, unit index] at product
        exact product.symm)).trans (Sequence.Name.Exact.exact_toConstantNamed 1).symm
  exact ⟨⟨cached, rfl⟩, ⟨⟨forward, backward, compared⟩, rfl, rfl⟩⟩

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

public section

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    (channels : CoordinateChannels site parameter point source unit)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))

/-- The intrinsic collar profile retains both actual squared-radius and clipped-height streams before time. -/
@[expose] def Profile : Type _ :=
  (raw : { height : GeometricApproximation // height = Collar.radial (Collar.range site parameter bound)
    (GeometricApproximation.ofNamed channels.plus.name) }) ×
  { clipped : GeometricApproximation // clipped = raw.val.clipReal }

/-- Prepare the original radius profile and its clipped height once, before selecting sweep times or accuracy. -/
def profile : Profile channels bound :=
  let raw := Collar.radial (Collar.range site parameter bound)
    (GeometricApproximation.ofNamed channels.plus.name)
  let clipped := raw.clipReal
  ⟨⟨raw, rfl⟩, ⟨clipped, rfl⟩⟩

/-- The actual rotated plus/minus programs retain one phase cache and the original smoothing-product relation. -/
@[expose] def Sweep (profile : Profile channels bound) (time : Fraction.Rational) : Type _ :=
  (phases : { value : Collar.PhaseNames (height := profile.1.val) profile.2 time //
    value = Collar.phaseNames (height := profile.1.val) profile.2 time }) ×
  (plus : { value : CoherentNamed // value = channels.plus.mul phases.val.2.val.1 }) ×
  (minus : { value : CoherentNamed // value = channels.minus.mul phases.val.2.val.2.1 }) ×
    NamedEquivalent (plus.val.mul minus.val).name (Named.exact (smoothing site parameter))

/-- Rotate the GIVEN actual named conic channels on the SAME intrinsic collar profile.

The two actual phase names are built once and their operational unit law
pays product preservation. The source/root/cofactor programs are consumed
unchanged. This does not convert their base into an exact Gaussian Point or
assert a rooted mesh incidence, cubic re-lift or signed cut correction.
-/
def sweep (profile : Profile channels bound) (time : Fraction.Rational) : Sweep channels bound profile time := by
  let phases := Collar.phaseNames (height := profile.1.val) profile.2 time
  let forward := phases.2.val.1
  let backward := phases.2.val.2.1
  let plus := channels.plus.mul forward
  let minus := channels.minus.mul backward
  have cancel : NamedEquivalent (forward.mul backward).name (Named.exact 1) := phases.2.val.2.2
  have product : NamedEquivalent (plus.mul minus).name (Named.exact (smoothing site parameter)) :=
    (Name.Coherent.Arithmetic.Product.Laws.coherentMul_interchange
      channels.plus forward channels.minus backward).trans
      ((Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
        (channels.plus.mul channels.minus) (Coherence.exact (smoothing site parameter))
        (forward.mul backward) (Coherence.exact 1) channels.product cancel).trans
        (NamedEquivalent.transport rfl
          (congrArg Named.exact (Data.Gaussian.Basic.mul_one (smoothing site parameter)))
          (Name.Coherent.Exact.Arithmetic.exact_mul (smoothing site parameter) 1)))
  exact ⟨⟨phases, rfl⟩, ⟨plus, rfl⟩, ⟨minus, rfl⟩, product⟩

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels

end
