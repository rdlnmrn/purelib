module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Tangent
public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Integral
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Data.List.DependentProduct
public import Purelib.Geometry.Gaussian.UnitCircle.Quarter
public import Purelib.Integration.Program.Gaussian.Concatenation.Uniform
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Tactic.Ring
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Reciprocal
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance

/-!
# Logarithmic integration on the original rational circle

The original curve cache supplies each actual point and its original
scaled tangent. The shared logarithmic-tangent cells retain those exact
quotient readings while reusing the same finite polynomial integration.
-/

public section

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Integral

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.List (DependentProduct)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Ascending
open Purelib.RationalFunctions.Curve.Canonical
open Purelib.Polynomial.Ascending.Gaussian

/-- Integrate the actual logarithmic tangent of the supplied original circle cache.

The actual original rational curve is retained outside every stage and
observation lambda. Each shared cell reads that same curve's point and its
same-base tangent at both original endpoint parameters. Exact pointwise
cancellation derives the original polynomial and movement bounds.
-/
@[expose] def program (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base } := ⟨circle base, rfl⟩) : RefinementProgram :=
  let integrand := fun time => logarithmicVelocity base time curve
  have integrand_eq : ∀ time, integrand time = Stereographic.Tangent.logarithmicVelocity time :=
    fun time => logarithmicVelocity_eq base nonzero time curve
  let models := fun index => Stereographic.Integral.model index integrand integrand_eq
  Stereographic.Integral.program.withModels models (fun _ => rfl)
    (fun index => Stereographic.Integral.program.modelAllowance_le index)

/-- Each actual circle stage retains the complete shared model with both original point-and-tangent observations. -/
theorem program_model (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base }) (index : Nat) :
    (program base nonzero curve).model index =
      Stereographic.Integral.model index (fun time => logarithmicVelocity base time curve)
        (fun time => logarithmicVelocity_eq base nonzero time curve) := rfl

/-- The actual logarithmic curve programme preserves the original quarter programme's center bound. -/
theorem program_centerBound (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base }) :
    (program base nonzero curve).centerBound = Stereographic.Integral.program.centerBound := (rfl)

/-- The actual supplied circle's program has the same original finite polynomial integral samples. -/
theorem program_sample (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base }) (index : Nat) :
    ((program base nonzero curve).model index).integralSample =
      (Stereographic.Integral.program.model index).integralSample := by
  rw [program_model, Stereographic.Integral.model_integralSample index
    (fun time => logarithmicVelocity base time curve)
    (fun time => logarithmicVelocity_eq base nonzero time curve)]
  exact (Stereographic.Integral.model_integralSample index).symm

/-- The actual supplied circle's program keeps the same retained finite aggregate allowances. -/
theorem program_allowance (base : Canonical) (nonzero : base ≠ 0)
    (curve : { value : RationalCurve // value = circle base }) (index : Nat) :
    ((program base nonzero curve).model index).aggregateAllowance =
      (Stereographic.Integral.program.model index).aggregateAllowance := by
  rw [program_model, Stereographic.Integral.model_aggregateAllowance index
    (fun time => logarithmicVelocity base time curve)
    (fun time => logarithmicVelocity_eq base nonzero time curve)]
  exact (Stereographic.Integral.model_aggregateAllowance index).symm

/-- The four original circuit quarters in their positive traversal order. -/
@[expose] def quarters : List Quarter.UnitCircuitQuarter := [.first, .second, .third, .fourth]

/-- The actual original base of the selected quarter on a centered circuit. -/
@[expose] def quarterBase (base : Canonical) (quarter : Quarter.UnitCircuitQuarter) : Canonical :=
  base * Quarter.unitCircuitMultiplier quarter

/-- Multiplication by an original unit circuit multiplier preserves a supplied nonzero base. -/
theorem quarterBase_ne_zero (base : Canonical) (nonzero : base ≠ 0) (quarter : Quarter.UnitCircuitQuarter) :
    quarterBase base quarter ≠ 0 := by
  apply Basic.Canonical.mul_ne_zero nonzero
  intro zero
  have normZero := congrArg Norm.Basic.normSq zero
  rw [Quarter.unitCircuitMultiplier_unit, Norm.Basic.normSq_zero] at normZero
  exact (by decide +kernel : (1 : Fraction.Rational) ≠ 0) normZero

/-- Each original quarter base retains the exact squared norm of its original circuit base. -/
theorem quarterBase_normSq (base : Canonical) (quarter : Quarter.UnitCircuitQuarter) :
    Norm.Basic.normSq (quarterBase base quarter) = Norm.Basic.normSq base := by
  rewrite [quarterBase, Norm.Basic.normSq_mul, Quarter.unitCircuitMultiplier_unit]
  ring1

/-- One original quarter curve and the actual program constructed from that same supplied curve cache. -/
abbrev QuarterData (base : Canonical) (nonzero : base ≠ 0) (quarter : Quarter.UnitCircuitQuarter) :=
  (curve : { value : RationalCurve // value = circle (quarterBase base quarter) }) ×
    { value : RefinementProgram //
      value = program (quarterBase base quarter) (quarterBase_ne_zero base nonzero quarter) curve }

/-- Materialize the actual original curve once and its exact logarithmic integration program once. -/
@[expose] def QuarterData.build (base : Canonical) (nonzero : base ≠ 0) (quarter : Quarter.UnitCircuitQuarter) :
    QuarterData base nonzero quarter :=
  let actualBase := quarterBase base quarter
  let curve : { value : RationalCurve // value = circle actualBase } := ⟨circle actualBase, rfl⟩
  let actual := program actualBase (quarterBase_ne_zero base nonzero quarter) curve
  ⟨curve, ⟨actual, rfl⟩⟩

/-- Each retained original quarter program has one original cell at every finite refinement stage. -/
theorem QuarterData.cells_length {base : Canonical} {nonzero : base ≠ 0} {quarter : Quarter.UnitCircuitQuarter}
    (entry : QuarterData base nonzero quarter) (index : Nat) :
    (entry.2.val.model index).cells.length = 1 := by
  rw [entry.2.property, program_model]
  rfl

/-- Every retained quarter program reads the same original logarithmic integral sample. -/
theorem QuarterData.sample {base : Canonical} {nonzero : base ≠ 0} {quarter : Quarter.UnitCircuitQuarter}
    (entry : QuarterData base nonzero quarter) (index : Nat) :
    (entry.2.val.model index).integralSample = (Stereographic.Integral.program.model index).integralSample := by
  rw [entry.2.property]
  exact program_sample _ _ _ index

/-- Each actual retained quarter program has the original logarithmic movement scale. -/
theorem QuarterData.errorScale {base : Canonical} {nonzero : base ≠ 0} {quarter : Quarter.UnitCircuitQuarter}
    (entry : QuarterData base nonzero quarter) : entry.2.val.errorScale = 1 / 16 := by
  rw [entry.2.property]
  rfl

/-- The same retained quarter programme has the original fixed common center bound. -/
theorem QuarterData.centerBound {base : Canonical} {nonzero : base ≠ 0} {quarter : Quarter.UnitCircuitQuarter}
    (entry : QuarterData base nonzero quarter) : entry.2.val.centerBound = 18 :=
  (congrArg (fun value : RefinementProgram => value.centerBound) entry.2.property).trans
    (program_centerBound (quarterBase base quarter) (quarterBase_ne_zero base nonzero quarter) entry.1)

/-- The ordered original curve/program caches at all four bounded original quarter occurrences. -/
abbrev Entries (base : Canonical) (nonzero : base ≠ 0) :=
  DependentProduct quarters (fun index => QuarterData base nonzero (quarters[index.val]'index.isLt))

/-- Materialize each original quarter's actual curve and same-cache program exactly once. -/
@[expose] def Entries.build (base : Canonical) (nonzero : base ≠ 0) : Entries base nonzero :=
  DependentProduct.ofFn quarters (fun index => QuarterData.build base nonzero (quarters[index.val]'index.isLt))

/-- Read the exact retained curve/program pair at the supplied bounded original quarter occurrence. -/
@[expose] def Entries.get {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (index : Fin quarters.length) : QuarterData base nonzero (quarters[index.val]'index.isLt) :=
  DependentProduct.get quarters entries index

/-- Lookup of the materialized table returns the complete actual original quarter cache. -/
theorem Entries.get_build (base : Canonical) (nonzero : base ≠ 0) (index : Fin quarters.length) :
    (Entries.build base nonzero).get index = QuarterData.build base nonzero (quarters[index.val]'index.isLt) :=
  DependentProduct.get_ofFn quarters _ index

/-- The stored curve at its original quarter occurrence starts at that same quarter's actual base. -/
theorem Entries.start {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (index : Fin quarters.length) :
    (entries.get index).1.val.point 0 = quarterBase base (quarters[index.val]'index.isLt) := by
  rw [(entries.get index).1.property, point_eq_base_mul, Stereographic.unitQuarterPoint_zero]
  exact Basic.mul_one _

/-- The stored curve at its original quarter occurrence finishes at its actual next quarter-turn point. -/
theorem Entries.finish {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero)
    (index : Fin quarters.length) :
    (entries.get index).1.val.point 1 =
      quarterBase base (quarters[index.val]'index.isLt) * (⟨0, 1⟩ : Canonical) := by
  rw [(entries.get index).1.property, point_eq_base_mul, Stereographic.unitQuarterPoint_one]

/-- Successive stored original quarter curves have exactly the same physical endpoint. -/
theorem Entries.join {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero) (index : Fin 3) :
    (entries.get index.castSucc).1.val.point 1 = (entries.get index.succ).1.val.point 0 := by
  rw [entries.finish, entries.start, quarterBase, quarterBase, Basic.mul_assoc]
  apply congrArg (fun value => base * value)
  refine Fin.cases ?_
    (fun tail => Fin.cases ?_ (fun last => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) last) tail) index <;>
    decide +kernel

/-- The last retained original curve closes at the first retained curve's original starting point. -/
theorem Entries.closed {base : Canonical} {nonzero : base ≠ 0} (entries : Entries base nonzero) :
    (entries.get ⟨3, by decide +kernel⟩).1.val.point 1 = (entries.get ⟨0, by decide +kernel⟩).1.val.point 0 := by
  rw [entries.finish, entries.start, quarterBase, quarterBase, Basic.mul_assoc]
  exact congrArg (fun value => base * value) (by decide +kernel)

/-- Concatenate the four actual retained quarter programs in their original source order.

Both halves consume the supplied table entries directly. Their equal cell
counts derive the original concatenation allowance internally; the final
concatenation retains the four actual original cells and observations.
-/
@[expose] def Entries.concatenate {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) : RefinementProgram :=
  let first := (entries.get ⟨0, by decide +kernel⟩).2.val
  let second := (entries.get ⟨1, by decide +kernel⟩).2.val
  let third := (entries.get ⟨2, by decide +kernel⟩).2.val
  let fourth := (entries.get ⟨3, by decide +kernel⟩).2.val
  let earlier := first.concatOfEqualCounts second
    (fun index => ((entries.get ⟨0, by decide +kernel⟩).cells_length index).trans
      ((entries.get ⟨1, by decide +kernel⟩).cells_length index).symm)
  let later := third.concatOfEqualCounts fourth
    (fun index => ((entries.get ⟨2, by decide +kernel⟩).cells_length index).trans
      ((entries.get ⟨3, by decide +kernel⟩).cells_length index).symm)
  earlier.concatOfEqualCounts later (by
    intro index
    change ((first.model index).cells ++ (second.model index).cells).length =
      ((third.model index).cells ++ (fourth.model index).cells).length
    rw [List.length_append, List.length_append, (entries.get ⟨0, by decide +kernel⟩).cells_length,
      (entries.get ⟨1, by decide +kernel⟩).cells_length, (entries.get ⟨2, by decide +kernel⟩).cells_length,
      (entries.get ⟨3, by decide +kernel⟩).cells_length])

/-- The concatenated circuit retains the exact original quarter cells in their original grouped order. -/
theorem Entries.concatenate_model {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (index : Nat) :
    (entries.concatenate.model index) =
      (((entries.get ⟨0, by decide +kernel⟩).2.val.model index).concat
        ((entries.get ⟨1, by decide +kernel⟩).2.val.model index)).concat
          (((entries.get ⟨2, by decide +kernel⟩).2.val.model index).concat
            ((entries.get ⟨3, by decide +kernel⟩).2.val.model index)) := rfl

/-- The actual circuit sample is the sum of the four original retained logarithmic quarter samples. -/
theorem Entries.concatenate_sample {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (index : Nat) :
    (entries.concatenate.model index).integralSample =
      ((Stereographic.Integral.program.model index).integralSample +
        (Stereographic.Integral.program.model index).integralSample) +
      ((Stereographic.Integral.program.model index).integralSample +
        (Stereographic.Integral.program.model index).integralSample) := by
  rw [entries.concatenate_model, PathModel.integralSample_concat, PathModel.integralSample_concat,
    PathModel.integralSample_concat, QuarterData.sample, QuarterData.sample, QuarterData.sample, QuarterData.sample]

/-- Balanced concatenation has the exact movement scale derived from the four retained quarter programs. -/
theorem Entries.concatenate_errorScale {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) : entries.concatenate.errorScale = 1 := by
  change 2 * (2 * ((entries.get ⟨0, by decide +kernel⟩).2.val.errorScale +
    (entries.get ⟨1, by decide +kernel⟩).2.val.errorScale) +
      2 * ((entries.get ⟨2, by decide +kernel⟩).2.val.errorScale +
        (entries.get ⟨3, by decide +kernel⟩).2.val.errorScale)) = 1
  rw [QuarterData.errorScale, QuarterData.errorScale, QuarterData.errorScale, QuarterData.errorScale]
  decide +kernel

/-- The actual balanced four-quarter concatenation preserves its original fixed sample center bound. -/
theorem Entries.concatenate_centerBound {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) : entries.concatenate.centerBound = 288 := by
  change 2 * (2 * ((entries.get ⟨0, by decide⟩).2.val.centerBound +
    (entries.get ⟨1, by decide⟩).2.val.centerBound) +
      2 * ((entries.get ⟨2, by decide⟩).2.val.centerBound +
        (entries.get ⟨3, by decide⟩).2.val.centerBound)) = 288
  rewrite [QuarterData.centerBound, QuarterData.centerBound, QuarterData.centerBound, QuarterData.centerBound]
  ring1

/-- The original ordered quarter caches together with their exact materialized concatenation. -/
abbrev Circuit (base : Canonical) (nonzero : base ≠ 0) :=
  (entries : Entries base nonzero) × { value : RefinementProgram // value = entries.concatenate }

/-- Retain the four actual original quarter caches once and their exact concatenated program once. -/
@[expose] def circuit (base : Canonical) (nonzero : base ≠ 0) : Circuit base nonzero :=
  let entries := Entries.build base nonzero
  let actual := entries.concatenate
  ⟨entries, ⟨actual, rfl⟩⟩

/-- The actual coherent CCL presentation of the same retained closed circuit program. -/
@[expose] def Circuit.channel {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    CoherentNamed :=
  Preparation.sampledChannel cached.2.val.geometric

/-- Each actual retained circuit sample reads the four original quarter samples in the same balanced order. -/
theorem Circuit.sample {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) (index : Nat) :
    (cached.2.val.model index).integralSample =
      ((Stereographic.Integral.program.model index).integralSample +
        (Stereographic.Integral.program.model index).integralSample) +
      ((Stereographic.Integral.program.model index).integralSample +
        (Stereographic.Integral.program.model index).integralSample) :=
  (congrArg (fun value : RefinementProgram => (value.model index).integralSample) cached.2.property).trans
    (Entries.concatenate_sample cached.1 index)

/-- The actual four-quarter circuit retains its original geometric error scale. -/
theorem Circuit.errorScale {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    cached.2.val.errorScale = 1 :=
  (congrArg (fun value : RefinementProgram => value.errorScale) cached.2.property).trans
    (Entries.concatenate_errorScale cached.1)

/-- The actual logarithmic channel keeps its original base-independent common center bound. -/
theorem Circuit.centerBound {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    cached.channel.name.process.centerBound = 288 := by
  change cached.2.val.centerBound = 288
  exact (congrArg (fun value : RefinementProgram => value.centerBound) cached.2.property).trans
    (Entries.concatenate_centerBound cached.1)

/-- The actual circuit's sample quadrance is sixteen times its original retained quarter sample quadrance. -/
theorem Circuit.sample_normSq {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) (index : Nat) :
    Norm.Basic.normSq (cached.2.val.model index).integralSample =
      16 * Norm.Basic.normSq (Stereographic.Integral.program.model index).integralSample := by
  rewrite [Circuit.sample]
  unfold Norm.Basic.normSq
  simp only [Basic.add_re, Basic.add_im]
  ring1

/-- The same actual first circuit observation is quantitatively separated from zero.

The four retained samples add in their original order. Their quadrance is
sixteen times the quarter sample's quadrance, while the exact concatenation
movement scale is one; the original quarter's paid separation therefore
supplies this actual whole-loop ball's separation directly.
-/
theorem Circuit.initial_separated {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    let state := Refinement.State.initial cached.channel
    2 * (cached.channel.name.process.ball state.source).radiusSq <
      Norm.Basic.normSq (cached.channel.name.process.ball state.source).center := by
  change 2 * Geometric.Basic.quarterRadius cached.2.val.errorScale 0 <
    Norm.Basic.normSq (cached.2.val.model 0).integralSample
  rw [Circuit.errorScale, Circuit.sample_normSq]
  have quarter := Stereographic.Integral.initial_separated
  change 2 * Geometric.Basic.quarterRadius (1 / 16) 0 <
    Norm.Basic.normSq (Stereographic.Integral.program.model 0).integralSample at quarter
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide +kernel : (0 : Fraction.Rational) < 16) quarter
  rw [show (16 : Fraction.Rational) *
    (2 * Geometric.Basic.quarterRadius (1 / 16) 0) =
      2 * Geometric.Basic.quarterRadius 1 0 by decide +kernel] at paid
  exact paid

/-- Prepare the actual closed-loop logarithmic integral from its same retained first observation.

The source is the concatenation of the four stored original quarter programs;
the denominator evidence reads that source's actual first ball exactly once.
No formal winding value or independently selected channel replaces it.
-/
@[expose] def Circuit.prepared {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    Prepared cached.channel :=
  let source := cached.2.val.geometric
  let state := Refinement.State.initial cached.channel
  let ball := cached.channel.name.process.ball state.source
  Preparation.fromBall source cached.channel
    (NamedEquivalent.refl cached.channel.name) state ball rfl
      cached.initial_separated

/-- The actual prepared logarithmic denominator retains the same fixed center bound as its original circuit. -/
theorem Circuit.prepared_centerBound {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    cached.prepared.denominator.name.process.centerBound = 288 := by
  have actual := Preparation.fromBall_centerBound cached.2.val.geometric cached.channel
    (NamedEquivalent.refl _) (Refinement.State.initial cached.channel)
    (cached.channel.name.process.ball (Refinement.State.initial cached.channel).source) rfl cached.initial_separated
  exact actual.trans (Circuit.centerBound cached)

/-- The original logarithmic circle's lower floor is computed from the original fixed quarter's first observation. -/
def logarithmicLower : Fraction.Rational :=
  (16 * Norm.Basic.normSq (Stereographic.Integral.program.model 0).integralSample / 2 - 1) / 8

/-- The same actual prepared logarithmic denominator retains the fixed original finite lower floor. -/
theorem Circuit.prepared_lowerSq {base : Canonical} {nonzero : base ≠ 0} (cached : Circuit base nonzero) :
    cached.prepared.apart.certificate.lowerSq = logarithmicLower := by
  have actual := Preparation.fromBall_lowerSq cached.2.val.geometric cached.channel
    (NamedEquivalent.refl _) (Refinement.State.initial cached.channel)
    (cached.channel.name.process.ball (Refinement.State.initial cached.channel).source) rfl cached.initial_separated
  change cached.prepared.apart.certificate.lowerSq =
    (Norm.Basic.normSq (cached.2.val.model 0).integralSample / 2 -
      Geometric.Basic.quarterRadius cached.2.val.errorScale 0) / 8 at actual
  rewrite [Circuit.sample_normSq, Circuit.errorScale] at actual
  exact actual

/-- The computed original logarithmic lower floor is positive by the same actual original prepared integral. -/
theorem logarithmicLower_positive : 0 < logarithmicLower := by
  let actual := circuit (1 : Canonical) (by decide)
  exact actual.prepared_lowerSq ▸ actual.prepared.apart.certificate.positive

/-- The actual supplied original circuit curve avoids zero at every displayed parameter. -/
theorem Entries.point_ne_zero {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (index : Fin quarters.length) (time : Fraction.Rational) :
    (entries.get index).1.val.point time ≠ 0 := by
  rw [(entries.get index).1.property]
  exact Circle.point_ne_zero _ (quarterBase_ne_zero base nonzero _) time

/-- Read a primitive's exact endpoint increment on the actual stored original quarter curve.

The source and finish use the same retained curve, at its original
parameters zero and one. No independently rebuilt circle supplies a point.
-/
@[expose] def Entries.primitiveIncrement {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (primitive : Canonical → Canonical) (index : Fin quarters.length) : Canonical :=
  let curve := (entries.get index).1.val
  let start := curve.point 0
  let finish := curve.point 1
  primitive finish - primitive start

/-- The exact primitive increments of the four actual original joined curves cancel at their physical endpoints.

The three original joins and original closure identify consecutive scalar
readings while keeping each supplied curve. This finite cancellation needs
no analytic or operational integral assertion about the primitive.
-/
theorem Entries.primitive_closed {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (primitive : Canonical → Canonical) :
    (entries.primitiveIncrement primitive ⟨0, by decide +kernel⟩ +
      entries.primitiveIncrement primitive ⟨1, by decide +kernel⟩) +
    (entries.primitiveIncrement primitive ⟨2, by decide +kernel⟩ +
      entries.primitiveIncrement primitive ⟨3, by decide +kernel⟩) = 0 := by
  dsimp only [primitiveIncrement]
  have first : (entries.get ⟨0, by decide +kernel⟩).1.val.point 1 =
      (entries.get ⟨1, by decide +kernel⟩).1.val.point 0 := entries.join ⟨0, by decide +kernel⟩
  have second : (entries.get ⟨1, by decide +kernel⟩).1.val.point 1 =
      (entries.get ⟨2, by decide +kernel⟩).1.val.point 0 := entries.join ⟨1, by decide +kernel⟩
  have third : (entries.get ⟨2, by decide +kernel⟩).1.val.point 1 =
      (entries.get ⟨3, by decide +kernel⟩).1.val.point 0 := entries.join ⟨2, by decide +kernel⟩
  rw [first, second, third, entries.closed]
  ring1

/-- The same retained reciprocal primitive reads the original nonlogarithmic coefficient on each actual stored curve. -/
theorem Entries.reciprocalPrimitive_coefficient {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order)
    (index : Fin quarters.length) (time : Fraction.Rational) :
    retained.derivativeValue ((entries.get index).1.val.point time) =
      Evaluation.eval ⟨source.coefficients.take order⟩ ((entries.get index).1.val.point time) *
        (((entries.get index).1.val.point time) ^ (order + 1))⁻¹ :=
  retained.derivativeValue_eq _ (entries.point_ne_zero index time)

/-- The same cached nonlogarithmic primitive factors its difference along two actual stored-quarter points. -/
theorem Entries.reciprocalPrimitive_difference {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) {source : CoefficientPolynomial} {order : Nat}
    (primitive : Antiderivative.ReciprocalPrimitive source order) (index : Fin quarters.length)
    (first second : Fraction.Rational) :
    primitive.value ((entries.get index).1.val.point first) -
      primitive.value ((entries.get index).1.val.point second) =
      ((entries.get index).1.val.point first - (entries.get index).1.val.point second) *
        primitive.kernel ((entries.get index).1.val.point first) ((entries.get index).1.val.point second) :=
  primitive.sub_factor _ _ (entries.point_ne_zero index first) (entries.point_ne_zero index second)

/-- The actual stored quarter's nonlogarithmic primitive increment is its original finite inverse-endpoint integral. -/
theorem Entries.reciprocalPrimitive_increment {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order) (index : Fin quarters.length) :
    entries.primitiveIncrement retained.value index =
      -Gaussian.Integral.definiteIntegral retained.1.val
        ((entries.get index).1.val.point 0)⁻¹ ((entries.get index).1.val.point 1)⁻¹ :=
  retained.increment _ _

/-- The four original inverse-endpoint polynomial integrals cancel for the same retained nonlogarithmic primitive.

This is finite primitive boundary cancellation on the actual stored curves.
It does not identify a Laurent pullback program with its endpoint difference.
-/
theorem Entries.reciprocalPrimitive_closed {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) {source : CoefficientPolynomial} {order : Nat}
    (retained : Antiderivative.ReciprocalPrimitive source order) :
    (-Gaussian.Integral.definiteIntegral retained.1.val
      ((entries.get ⟨0, by decide +kernel⟩).1.val.point 0)⁻¹
      ((entries.get ⟨0, by decide +kernel⟩).1.val.point 1)⁻¹ +
      -Gaussian.Integral.definiteIntegral retained.1.val
        ((entries.get ⟨1, by decide +kernel⟩).1.val.point 0)⁻¹
        ((entries.get ⟨1, by decide +kernel⟩).1.val.point 1)⁻¹) +
    (-Gaussian.Integral.definiteIntegral retained.1.val
      ((entries.get ⟨2, by decide +kernel⟩).1.val.point 0)⁻¹
      ((entries.get ⟨2, by decide +kernel⟩).1.val.point 1)⁻¹ +
      -Gaussian.Integral.definiteIntegral retained.1.val
        ((entries.get ⟨3, by decide +kernel⟩).1.val.point 0)⁻¹
        ((entries.get ⟨3, by decide +kernel⟩).1.val.point 1)⁻¹) = 0 := by
  rw [← entries.reciprocalPrimitive_increment retained ⟨0, by decide +kernel⟩,
    ← entries.reciprocalPrimitive_increment retained ⟨1, by decide +kernel⟩,
    ← entries.reciprocalPrimitive_increment retained ⟨2, by decide +kernel⟩,
    ← entries.reciprocalPrimitive_increment retained ⟨3, by decide +kernel⟩]
  exact entries.primitive_closed retained.value

/-- The original finite polynomial primitive integral also cancels around the same four actual stored curves. -/
theorem Entries.polynomialPrimitive_closed {base : Canonical} {nonzero : base ≠ 0}
    (entries : Entries base nonzero) (source : CoefficientPolynomial) :
    (Gaussian.Integral.definiteIntegral source
      ((entries.get ⟨0, by decide +kernel⟩).1.val.point 0) ((entries.get ⟨0, by decide +kernel⟩).1.val.point 1) +
      Gaussian.Integral.definiteIntegral source
        ((entries.get ⟨1, by decide +kernel⟩).1.val.point 0) ((entries.get ⟨1, by decide +kernel⟩).1.val.point 1)) +
    (Gaussian.Integral.definiteIntegral source
      ((entries.get ⟨2, by decide +kernel⟩).1.val.point 0) ((entries.get ⟨2, by decide +kernel⟩).1.val.point 1) +
      Gaussian.Integral.definiteIntegral source
        ((entries.get ⟨3, by decide +kernel⟩).1.val.point 0)
          ((entries.get ⟨3, by decide +kernel⟩).1.val.point 1)) = 0 :=
  entries.primitive_closed (Evaluation.eval (Antiderivative.antiderivative source))

end Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
