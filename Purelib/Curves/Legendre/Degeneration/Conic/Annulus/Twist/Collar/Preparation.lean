module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Cofactor
public import Purelib.Riemann.RootContinuation.SquareRootProvenance.Tail
import Purelib.Data.Gaussian.Norm.Parallelogram
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial
import Purelib.Data.Rat.Interval.Unit.Clamp
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Acquired original-channel enclosures for a retained collar base

A finite check of the original exact centered coordinate pays one actual
normalized-ordinate tail. Original arithmetic factories and the GIVEN paired
phase cache construct the retained base program. Its derived common ball
lies in the original collision patch and feeds the existing cofactor re-lift.
-/

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation Enclosure)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist

public section

open Purelib.Data.Rat.Fraction

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.PhaseNames

variable {height : GeometricApproximation}
    {clipped : { value : GeometricApproximation // value = height.clipReal }}
    {time : Fraction.Rational} (names : PhaseNames (height := height) clipped time)

/-- Every actual retained phase-program sample has unit quadrance at an admitted time. -/
theorem sample_unit (inside : 0 ≤ time ∧ time ≤ 1) (index : Nat) :
    Norm.Basic.normSq (names.1.val.sample index) = 1 :=
  (congrArg Norm.Basic.normSq ((congrArg (fun value : GeometricApproximation => value.sample index)
    names.1.property).trans (phase_sample (height := height) clipped time inside index))).trans
      (Twist.phase (time * Interval.Unit.clamp (height.sample index).re)).unit

/-- Enclose the GIVEN forward name by its SAME retained phase program and exact unit sample law. -/
def forwardEnclosure (inside : 0 ≤ time ∧ time ≤ 1) : Enclosure names.2.val.1 where
  source := names.1.val
  equivalent := NamedEquivalent.transport (congrArg CoherentNamed.name names.2.property.1.symm) rfl
    (NamedEquivalent.refl _)
  ball := { center := 0, radiusSq := 1, radiusSq_nonneg := by decide +kernel }
  contains := fun index => by
    change Norm.Basic.normSq (names.1.val.sample index - 0) ≤ 1
    rewrite [Basic.sub_zero]
    exact (names.sample_unit inside index).le

/-- Enclose the GIVEN backward name by conjugation of the SAME retained phase program. -/
def backwardEnclosure (inside : 0 ≤ time ∧ time ≤ 1) : Enclosure names.2.val.2.1 where
  source := names.1.val.conj
  equivalent := NamedEquivalent.transport (congrArg CoherentNamed.name names.2.property.2.symm) rfl
    (NamedEquivalent.refl _)
  ball := { center := 0, radiusSq := 1, radiusSq_nonneg := by decide +kernel }
  contains := fun index => by
    change Norm.Basic.normSq (names.1.val.conj.sample index - 0) ≤ 1
    have sampleEq := GeometricApproximation.conj_sample names.1.val index
    have scalar : Norm.Basic.normSq (names.1.val.conj.sample index - 0) =
        Norm.Basic.normSq (names.1.val.sample index) :=
      (congrArg Norm.Basic.normSq (Basic.sub_zero _)).trans
        ((congrArg Norm.Basic.normSq sampleEq).trans (Norm.Basic.normSq_conj _))
    exact scalar.trans_le (names.sample_unit inside index).le

/-- The forward enclosure retains the complete original cached phase program. -/
theorem forwardEnclosure_source (inside : 0 ≤ time ∧ time ≤ 1) :
    (names.forwardEnclosure inside).source = names.1.val := by
  unfold forwardEnclosure
  rfl

/-- The backward enclosure retains the actual conjugate of that SAME original phase program. -/
theorem backwardEnclosure_source (inside : 0 ≤ time ∧ time ≤ 1) :
    (names.backwardEnclosure inside).source = names.1.val.conj := by
  unfold backwardEnclosure
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.PhaseNames

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

/-- The original small centered-coordinate check derives the fixed normalized-ordinate coefficient bound. -/
theorem square_parameter_bound (site : Fin 2) (parameter abscissa : Canonical)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (coordinateBound : Norm.Basic.normSq abscissa ≤ (1 / 64 : Fraction.Rational)) :
    Norm.Basic.normSq (abscissa ^ 2 - smoothing site parameter) ≤ (1 / 1024 : Fraction.Rational) := by
  have gapBound := Radial.halfGap_bound site parameter bound
  have coordinatePower := Order.Arithmetic.pow_le_pow_direct
    (Norm.Basic.normSq_nonneg abscissa) coordinateBound 2
  have gapPower := Order.Arithmetic.pow_le_pow_direct
    (Norm.Basic.normSq_nonneg (halfGap site parameter)) gapBound 2
  have first : Norm.Basic.normSq (abscissa ^ 2) ≤ (1 / 4096 : Fraction.Rational) :=
    (Norm.Power.normSq_pow abscissa 2).trans_le
      (coordinatePower.trans_eq (by
        change (1 / ((64 : Nat) : Fraction.Rational)) ^ 2 = 1 / ((4096 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 64, Fraction.Cast.natCast_eq_fromInt 4096]
        decide +kernel))
  have last : Norm.Basic.normSq (smoothing site parameter) ≤ (1 / 65536 : Fraction.Rational) :=
    (Norm.Power.normSq_pow (halfGap site parameter) 2).trans_le
      (gapPower.trans_eq (by
        change (1 / ((256 : Nat) : Fraction.Rational)) ^ 2 = 1 / ((65536 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 256, Fraction.Cast.natCast_eq_fromInt 65536]
        decide +kernel))
  have combined := (Norm.Bounds.normSq_sub_le_two (abscissa ^ 2) (smoothing site parameter)).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct first last) (by decide +kernel))
  have scalar : 2 * ((1 / 4096 : Fraction.Rational) + 1 / 65536) ≤ (1 / 1024 : Fraction.Rational) :=
    by
      change 2 * (1 / ((4096 : Nat) : Fraction.Rational) + 1 / ((65536 : Nat) : Fraction.Rational)) ≤
        1 / ((1024 : Nat) : Fraction.Rational)
      rewrite [Fraction.Cast.natCast_eq_fromInt 4096, Fraction.Cast.natCast_eq_fromInt 65536,
        Fraction.Cast.natCast_eq_fromInt 1024]
      decide +kernel
  exact combined.trans scalar

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}

/-- Reindex the SAME original normalized-ordinate square comparison at its cached exact coefficient. -/
def squareAt (channels : CoordinateChannels site parameter point source unit)
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter }) :
    SquareRootProvenance.SquareIdentity channels.ordinate parameterCache.val := by
  have scalar := parameterCache.property.trans
    (congrArg (fun value : Canonical => value ^ 2 - smoothing site parameter) coordinateCache.property)
  exact NamedEquivalent.transport rfl (congrArg Named.exact scalar.symm) channels.square

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    {profile : Profile channels bound} {time : Fraction.Rational}
    {rotated : Sweep channels bound profile time} (actual : Reconstruction rotated)

/-- One actual arithmetic enclosure retains its exact paired phase and ordinate sample formula. -/
@[expose] def Arithmetic
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (normal : Enclosure channels.ordinate) : Type _ :=
  { value : Enclosure actual.2.1.val // ∀ index, value.source.sample index =
    center site parameter + (1 / 2 : Canonical) *
      ((coordinateCache.val + normal.source.sample index) * rotated.1.val.1.val.sample index +
        (coordinateCache.val - normal.source.sample index) * Basic.conj (rotated.1.val.1.val.sample index)) }

/-- Assemble the SAME retained named base with one normalized tail and the GIVEN original paired phase cache. -/
def arithmetic
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (normal : Enclosure channels.ordinate) (inside : 0 ≤ time ∧ time ≤ 1) :
    Arithmetic actual coordinateCache normal := by
  let exactCoordinate := Enclosure.exact coordinateCache.val
  let negative := normal.neg
  have plusEq : (Coherence.exact coordinateCache.val).add channels.ordinate = channels.plus :=
    (congrArg (fun value : Canonical => (Coherence.exact value).add channels.ordinate)
      coordinateCache.property).trans channels.plus_eq.symm
  have minusEq : (Coherence.exact coordinateCache.val).add channels.ordinate.neg = channels.minus :=
    (congrArg (fun value : Canonical => (Coherence.exact value).add channels.ordinate.neg)
      coordinateCache.property).trans channels.minus_eq.symm
  let plus := (exactCoordinate.add normal).cast plusEq
  let minus := (exactCoordinate.add negative).cast minusEq
  let forward := Collar.PhaseNames.forwardEnclosure (height := profile.1.val) (clipped := profile.2) (time := time)
    rotated.1.val inside
  let backward := Collar.PhaseNames.backwardEnclosure (height := profile.1.val) (clipped := profile.2) (time := time)
    rotated.1.val inside
  let left := (plus.mul forward).cast rotated.2.1.property.symm
  let right := (minus.mul backward).cast rotated.2.2.1.property.symm
  let sum := left.add right
  let half := Enclosure.exact (1 / 2 : Canonical)
  let centered := (half.mul sum).cast actual.1.property.symm
  let origin := Enclosure.exact (center site parameter)
  let result := (origin.add centered).cast actual.2.1.property.symm
  refine ⟨result, ?_⟩
  intro index
  have exactRead := Enclosure.exact_sample coordinateCache.val index
  have negativeRead := Enclosure.neg_sample normal index
  have plusRead : plus.source.sample index = coordinateCache.val + normal.source.sample index :=
    (Enclosure.cast_sample (exactCoordinate.add normal) plusEq index).trans
      ((Enclosure.add_sample exactCoordinate normal index).trans
        (congrArg (fun value : Canonical => value + normal.source.sample index) exactRead))
  have minusRead : minus.source.sample index = coordinateCache.val - normal.source.sample index :=
    (Enclosure.cast_sample (exactCoordinate.add negative) minusEq index).trans
      ((Enclosure.add_sample exactCoordinate negative index).trans
        ((congrArg₂ (fun first last : Canonical => first + last) exactRead negativeRead).trans
          (Basic.sub_eq_add_neg _ _).symm))
  have forwardRead : forward.source.sample index = rotated.1.val.1.val.sample index :=
    congrArg (fun value : GeometricApproximation => value.sample index)
      (Collar.PhaseNames.forwardEnclosure_source (height := profile.1.val) (clipped := profile.2) (time := time)
        rotated.1.val inside)
  have backwardRead : backward.source.sample index = Basic.conj (rotated.1.val.1.val.sample index) :=
    (congrArg (fun value : GeometricApproximation => value.sample index)
      (Collar.PhaseNames.backwardEnclosure_source (height := profile.1.val) (clipped := profile.2) (time := time)
        rotated.1.val inside)).trans (GeometricApproximation.conj_sample rotated.1.val.1.val index)
  have leftRead := (Enclosure.cast_sample (plus.mul forward) rotated.2.1.property.symm index).trans
    ((Enclosure.mul_sample plus forward index).trans
      (congrArg₂ (fun first last : Canonical => first * last) plusRead forwardRead))
  have rightRead := (Enclosure.cast_sample (minus.mul backward) rotated.2.2.1.property.symm index).trans
    ((Enclosure.mul_sample minus backward index).trans
      (congrArg₂ (fun first last : Canonical => first * last) minusRead backwardRead))
  have sumRead := (Enclosure.add_sample left right index).trans
    (congrArg₂ (fun first last : Canonical => first + last) leftRead rightRead)
  have centeredRead := (Enclosure.cast_sample (half.mul sum) actual.1.property.symm index).trans
    ((Enclosure.mul_sample half sum index).trans
      (congrArg₂ (fun first last : Canonical => first * last) (Enclosure.exact_sample _ index) sumRead))
  exact (Enclosure.cast_sample (origin.add centered) actual.2.1.property.symm index).trans
    ((Enclosure.add_sample origin centered index).trans
      (congrArg₂ (fun first last : Canonical => first + last) (Enclosure.exact_sample _ index) centeredRead))

include bound in
/-- The SAME normalized tail and paired phase give the actual base program radius twenty-one over128. -/
theorem arithmetic_radius
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter })
    (floor : Nat)
    (normal : SquareRootProvenance.Tail channels.ordinate parameterCache.val
      (channels.squareAt coordinateCache parameterCache) floor (1 / 16) (by decide +kernel))
    (made : Arithmetic actual coordinateCache normal.enclosure)
    (coordinateBound : Norm.Basic.normSq coordinateCache.val ≤ (1 / 64 : Fraction.Rational))
    (inside : 0 ≤ time ∧ time ≤ 1) (index : Nat) :
    Norm.Basic.normSq (made.val.source.sample index - criticalValue site) ≤ (21 / 128 : Fraction.Rational) := by
  have normalInside := normal.enclosure.contains index
  have normalBall := normal.2.2.property.2
  have normalized : Norm.Basic.normSq (normal.enclosure.source.sample index) ≤ (1 / 16 : Fraction.Rational) := by
    have actualBall := Eq.mp (congrArg (fun value : Ball =>
      value.Contains (normal.enclosure.source.sample index)) normalBall) normalInside
    change Norm.Basic.normSq (normal.enclosure.source.sample index - 0) ≤ _ at actualBall
    exact (congrArg Norm.Basic.normSq (Basic.sub_zero _)).symm.trans_le actualBall
  have unit := Collar.PhaseNames.sample_unit (height := profile.1.val) (clipped := profile.2) (time := time)
    rotated.1.val inside index
  have paired := Norm.Parallelogram.rotated_half_sum_le coordinateCache.val
    (normal.enclosure.source.sample index) (rotated.1.val.1.val.sample index) unit
  have bounded := paired.trans
    (Order.Arithmetic.add_le_add_direct coordinateBound normalized)
  have centered : Norm.Basic.normSq ((1 / 2 : Canonical) *
      ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
        (coordinateCache.val - normal.enclosure.source.sample index) *
          Basic.conj (rotated.1.val.1.val.sample index))) ≤ (5 / 64 : Fraction.Rational) :=
    bounded.trans_eq (by decide +kernel)
  have midpoint : center site parameter - criticalValue site = halfGap site parameter := by
    have sourceEq := (center_sub_halfGap site parameter).trans (criticalValue_eq_branchPoint site parameter).symm
    rewrite [← sourceEq]
    ring1
  have displacement : made.val.source.sample index - criticalValue site = halfGap site parameter +
      (1 / 2 : Canonical) *
        ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
          (coordinateCache.val - normal.enclosure.source.sample index) *
            Basic.conj (rotated.1.val.1.val.sample index)) := by
    have read := congrArg (fun value : Canonical => value - criticalValue site) (made.property index)
    exact read.trans ((show center site parameter + (1 / 2 : Canonical) *
      ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
        (coordinateCache.val - normal.enclosure.source.sample index) *
          Basic.conj (rotated.1.val.1.val.sample index)) - criticalValue site =
      (center site parameter - criticalValue site) + (1 / 2 : Canonical) *
        ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
          (coordinateCache.val - normal.enclosure.source.sample index) *
            Basic.conj (rotated.1.val.1.val.sample index)) by ring1).trans
      (congrArg (fun value : Canonical => value + (1 / 2 : Canonical) *
        ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
          (coordinateCache.val - normal.enclosure.source.sample index) *
            Basic.conj (rotated.1.val.1.val.sample index))) midpoint))
  have radius := (Norm.Bounds.normSq_add_le_two (halfGap site parameter)
    ((1 / 2 : Canonical) *
      ((coordinateCache.val + normal.enclosure.source.sample index) * rotated.1.val.1.val.sample index +
        (coordinateCache.val - normal.enclosure.source.sample index) *
          Basic.conj (rotated.1.val.1.val.sample index)))).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct
        (Radial.halfGap_bound site parameter bound) centered) (by decide +kernel))
  exact (congrArg Norm.Basic.normSq displacement).trans_le (radius.trans_eq (by decide +kernel))

/-- A tightened base enclosure retains its same sample program and comparison with a proved collision-centered ball. -/
@[expose] def Tight (program : Enclosure actual.2.1.val) : Type _ :=
  { value : Enclosure actual.2.1.val // value.source = program.source ∧
    value.ball = { center := criticalValue site, radiusSq := 21 / 128, radiusSq_nonneg := by decide +kernel } ∧
    HEq value.equivalent program.equivalent }

/-- Tighten only the common ball after deriving the actual program's radius from its acquired original tail. -/
def tighten
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter })
    (floor : Nat)
    (normal : SquareRootProvenance.Tail channels.ordinate parameterCache.val
      (channels.squareAt coordinateCache parameterCache) floor (1 / 16) (by decide +kernel))
    (made : Arithmetic actual coordinateCache normal.enclosure)
    (coordinateBound : Norm.Basic.normSq coordinateCache.val ≤ (1 / 64 : Fraction.Rational))
    (inside : 0 ≤ time ∧ time ≤ 1) : Tight actual made.val :=
  ⟨{ source := made.val.source
     equivalent := made.val.equivalent
     ball := { center := criticalValue site, radiusSq := 21 / 128, radiusSq_nonneg := by decide +kernel }
     contains := arithmetic_radius actual coordinateCache parameterCache floor normal made coordinateBound inside },
    rfl, rfl, HEq.rfl⟩

/-- Every point of the actual tightened common ball lies in the original spatial patch. -/
theorem contained (program : Enclosure actual.2.1.val) (tight : Tight actual program)
    (value : Canonical) (inside : tight.val.ball.Contains value) : (spatialBox site).Contains value := by
  have actualBall := Eq.mp (congrArg (fun ball : Ball => ball.Contains value) tight.property.2.1) inside
  change Norm.Basic.normSq (value - criticalValue site) ≤ (21 / 128 : Fraction.Rational) at actualBall
  have distance : Norm.Basic.normSq (value - criticalValue site) ≤ ((1 / 2 : Fraction.Rational) ^ 2) :=
    actualBall.trans (by decide +kernel)
  have result := Geometry.Rational.Box.Square.Centered.centeredBox_contains_of_normSq_sub_le
    (center := criticalValue site) (value := value) (radius := (1 / 2 : Fraction.Rational))
    (by decide +kernel) distance
  change (spatialBox site).Contains value at result
  exact result

include bound in
/-- The cached exact coefficient and original chart check pay the SAME fixed native-tail request. -/
theorem parameter_bound
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter })
    (coordinateBound : Norm.Basic.normSq coordinateCache.val ≤ (1 / 64 : Fraction.Rational)) :
    Norm.Basic.normSq parameterCache.val ≤ SquareRootProvenance.tailRequest (1 / 16) :=
  (congrArg Norm.Basic.normSq parameterCache.property).trans_le
    ((Collar.square_parameter_bound site parameter coordinateCache.val bound coordinateBound).trans_eq
      (by unfold SquareRootProvenance.tailRequest; decide +kernel))

/-- One accepted chart check retains its actual native tail, arithmetic program, tight enclosure and cofactor lift. -/
@[expose] def Prepared
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter })
    (floor : Nat) (inside : 0 ≤ time ∧ time ≤ 1)
    (coordinateBound : Norm.Basic.normSq coordinateCache.val ≤ (1 / 64 : Fraction.Rational)) : Type _ :=
  (normal : { value : SquareRootProvenance.Tail channels.ordinate parameterCache.val
      (channels.squareAt coordinateCache parameterCache) floor (1 / 16) (by decide +kernel) //
    value = SquareRootProvenance.encloseAt channels.ordinate parameterCache.val
      (channels.squareAt coordinateCache parameterCache) floor (1 / 16) (by decide +kernel)
      (parameter_bound (site := site) (parameter := parameter) (point := point) (bound := bound)
        coordinateCache parameterCache coordinateBound) }) ×
  (made : { value : Arithmetic actual coordinateCache normal.val.enclosure //
    value = arithmetic actual coordinateCache normal.val.enclosure inside }) ×
  (tight : Tight actual made.val.val) ×
  { value : Lift actual tight.val (contained actual made.val.val tight) //
    value = lift actual tight.val (contained actual made.val.val tight) }

/-- Execute one original ordinate-tail selection, the paired base arithmetic and one actual cofactor lift. -/
def prepareAt
    (coordinateCache : { value : Canonical // value = coordinate site parameter point })
    (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter })
    (floor : Nat) (inside : 0 ≤ time ∧ time ≤ 1)
    (coordinateBound : Norm.Basic.normSq coordinateCache.val ≤ (1 / 64 : Fraction.Rational)) :
    Prepared actual coordinateCache parameterCache floor inside coordinateBound := by
  let normal := SquareRootProvenance.encloseAt channels.ordinate parameterCache.val
    (channels.squareAt coordinateCache parameterCache) floor (1 / 16) (by decide +kernel)
    (parameter_bound (site := site) (parameter := parameter) (point := point) (bound := bound)
        coordinateCache parameterCache coordinateBound)
  let made := arithmetic actual coordinateCache normal.enclosure inside
  let tight := tighten actual coordinateCache parameterCache floor normal made coordinateBound inside
  let lifted := lift actual tight.val (contained actual made.val tight)
  exact ⟨⟨normal, rfl⟩, ⟨made, rfl⟩, tight, ⟨lifted, rfl⟩⟩

/-- Actual coefficient caches and a typed unresolved chart check precede new tail and root acquisition. -/
@[expose] def Attempt (floor : Nat) (inside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  (coordinateCache : { value : Canonical // value = coordinate site parameter point }) ×
  (parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter }) ×
  (norm : { value : Fraction.Rational // value = Norm.Basic.normSq coordinateCache.val }) ×
    Except (PLift (¬ norm.val ≤ (1 / 64 : Fraction.Rational)))
      ((accepted : PLift (norm.val ≤ (1 / 64 : Fraction.Rational))) ×
        Prepared actual coordinateCache parameterCache floor inside (norm.property.symm.trans_le accepted.down))

/-- Check the exact centered coordinate, retaining current inconclusivity or the SAME successful construction. -/
def prepare (floor : Nat) (inside : 0 ≤ time ∧ time ≤ 1) : Attempt actual floor inside := by
  let coordinateValue := coordinate site parameter point
  let coordinateCache : { value : Canonical // value = coordinate site parameter point } := ⟨coordinateValue, rfl⟩
  let parameterValue := coordinateValue ^ 2 - smoothing site parameter
  let parameterCache : { value : Canonical // value = coordinateCache.val ^ 2 - smoothing site parameter } :=
    ⟨parameterValue, rfl⟩
  let normValue := Norm.Basic.normSq coordinateValue
  let normCache : { value : Fraction.Rational // value = Norm.Basic.normSq coordinateCache.val } := ⟨normValue, rfl⟩
  if accepted : normValue ≤ (1 / 64 : Fraction.Rational) then
    let completed := prepareAt actual coordinateCache parameterCache floor inside
      (normCache.property.symm.trans_le accepted)
    exact ⟨coordinateCache, parameterCache, normCache, .ok ⟨⟨accepted⟩, completed⟩⟩
  else
    exact ⟨coordinateCache, parameterCache, normCache, .error ⟨accepted⟩⟩

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction

end
