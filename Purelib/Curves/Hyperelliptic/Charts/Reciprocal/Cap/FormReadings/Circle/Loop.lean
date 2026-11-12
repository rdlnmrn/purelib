module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Program
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral
public import Purelib.Integration.CertifiedProgram.Arithmetic
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent.Program
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence

/-! # The actual four-quarter total-form integration programme on the retained cap model -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.List (DependentProduct)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Integration
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical} {nonzero : base ≠ 0}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {data : Polynomials differential} {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}

/-- The original unit-interval starting endpoint of each actual retained quarter programme. -/
def start : Endpoint := ⟨0, by decide +kernel⟩

/-- The original unit-interval finishing endpoint of each actual retained quarter programme. -/
def finish : Endpoint := ⟨1, by decide +kernel⟩

/-- The original retained starting endpoint is the complete canonical zero endpoint. -/
theorem start_eq : start = ⟨0, by decide +kernel⟩ :=
  (rfl)

/-- The original retained finishing endpoint is the complete canonical unit endpoint. -/
theorem finish_eq : finish = ⟨1, by decide +kernel⟩ :=
  (rfl)

/-- One original total-form programme at the exact supplied original quarter curve and shared polynomial caches.

The original quarter curve is a correctness-bearing parent. Its original
base, nonzero guard, unit/collar bounds, common numerical derivative
bounds and unchanged whole coefficient caches index the original Program.
-/
@[expose] def QuarterProgram (cached : data.Bounds base)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (quarter : Quarter.UnitCircuitQuarter) (entry : Integral.QuarterData base nonzero quarter)
    (edges : DyadicEdges 0 start finish) :=
  Circle.Program (differential := differential) (cap := cap)
    (base := Integral.quarterBase base quarter)
    (unitBound := (Integral.quarterBase_normSq base quarter).trans_le unitBound)
    (collarBound := (Integral.quarterBase_normSq base quarter).trans_le collarBound)
    (actual := entry.1) (cached.onQuarter quarter)
    (Integral.quarterBase_ne_zero base nonzero quarter) bounds start finish edges

/-- The actual original four quarter programmes retain their supplied curve-bank parent and shared setup caches.

The original dependent product preserves all four ordered occurrences.
Every entry is the original whole quarter Program, including its same
coarse reading bank, budget and retained certified stage producer.
-/
@[expose] def Programs (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) :=
  DependentProduct Integral.quarters fun index =>
    QuarterProgram (unitBound := unitBound) (collarBound := collarBound) cached bounds
      (Integral.quarters[index.val]'index.isLt) (entries.get index) edges

/-- Build the four actual original total-form programmes, sharing the supplied whole polynomial and numerical setup.

The original dependent traversal passes each retained quarter curve once
to the original programme builder. Exact box transport reuses the same
whole Horner-cache pair; the supplied coarse edge cache and common root
bounds remain outside that traversal and all later-stage lambdas.
-/
def programs (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish := ⟨dyadicEdges 0 start finish, rfl⟩) :
    Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges :=
  DependentProduct.map Integral.quarters entries
    (fun index entry => QuarterProgram (unitBound := unitBound) (collarBound := collarBound) cached bounds
      (Integral.quarters[index.val]'index.isLt) entry edges)
    (fun index entry => Circle.program (differential := differential) (cap := cap)
      (base := Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
      (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
      (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
      (actual := entry.1) (cached.onQuarter _) (Integral.quarterBase_ne_zero base nonzero _)
      pairs degreeBound bounds start finish edges)

namespace Programs

variable {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
  {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
  {edges : DyadicEdges 0 start finish}

/-- Read the complete actual total-form programme at its original supplied quarter occurrence. -/
@[expose] def get (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :
    QuarterProgram (unitBound := unitBound) (collarBound := collarBound) cached bounds
      (Integral.quarters[index.val]'index.isLt) (entries.get index) edges :=
  DependentProduct.get Integral.quarters stored index

/-- Reading a built quarter returns the complete original producer at that same supplied curve and occurrence. -/
theorem get_programs (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) (index : Fin Integral.quarters.length) :
    (programs (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges).get index =
      Circle.program (differential := differential) (cap := cap)
        (base := Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
        (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
        (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
        (actual := (entries.get index).1) (cached.onQuarter _) (Integral.quarterBase_ne_zero base nonzero _)
        pairs degreeBound bounds start finish edges := by
  unfold get programs
  exact DependentProduct.get_map Integral.quarters entries _ _ index

/-- Every built quarter retains the exact requested source dyadic index in its actual certified stage. -/
theorem get_programs_stage_index (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) (quarter : Fin Integral.quarters.length) (index : Nat) :
    ((((programs (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges).get quarter).2.2.stage index).model).1 = index := by
  have whole := get_programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached pairs degreeBound bounds edges quarter
  have projected := congrArg (fun value => ((value.2.2.stage index).model).1) whole
  exact projected.trans (Circle.program_stage_index
    (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
    (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
    (actual := (entries.get quarter).1) (cached.onQuarter _)
    (Integral.quarterBase_ne_zero base nonzero _) pairs degreeBound bounds start finish edges index)

/-- The original sampling operations at one retained quarter and its same saved budget. -/
@[expose] def operations (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) (index : Fin Integral.quarters.length) :=
  Circle.operations (differential := differential) (cap := cap)
    (base := Integral.quarterBase base (Integral.quarters[index.val]'index.isLt))
    (unitBound := (Integral.quarterBase_normSq base _).trans_le unitBound)
    (collarBound := (Integral.quarterBase_normSq base _).trans_le collarBound)
    (actual := (entries.get index).1) start finish (stored.get index).2.1.val

/-- The exact balanced sum operations on the four same supplied original quarter budgets. -/
@[expose] def sumOperations (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) :=
  ((stored.operations ⟨0, by decide +kernel⟩).add (stored.operations ⟨1, by decide +kernel⟩)).add
    ((stored.operations ⟨2, by decide +kernel⟩).add (stored.operations ⟨3, by decide +kernel⟩))

/-- The balanced coherent sum retains the four actual original quarter output channels. -/
def channels (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) :=
  ((stored.get ⟨0, by decide +kernel⟩).2.2.output.add
    (stored.get ⟨1, by decide +kernel⟩).2.2.output).add
  ((stored.get ⟨2, by decide +kernel⟩).2.2.output.add
    (stored.get ⟨3, by decide +kernel⟩).2.2.output)

/-- The complete channel sum keeps the four actual supplied original quarter output channels in balanced order. -/
theorem channels_eq (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) :
    stored.channels =
      ((stored.get ⟨0, by decide +kernel⟩).2.2.output.add
        (stored.get ⟨1, by decide +kernel⟩).2.2.output).add
      ((stored.get ⟨2, by decide +kernel⟩).2.2.output.add
        (stored.get ⟨3, by decide +kernel⟩).2.2.output) := by
  unfold channels
  rfl

/-- A retained original total-form loop programme with its actual four-input output comparison. -/
@[expose] def Result (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) :=
  (produced : CertifiedProgram.Program stored.sumOperations) ×
    NamedEquivalent stored.channels.name produced.output.name

/-- Sum the four supplied certified programmes and retain their actual output comparison in original quarter order.

Each new stage keeps the literal two existing child caches, recursively
retaining all four original quarter caches. The same three produced sum
programmes feed their output comparisons; none is reconstructed by a
comparison handler. No Laurent or physical integral identity is assumed.
-/
def concatenate (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) : stored.Result := by
  let first := (stored.get ⟨0, by decide +kernel⟩).2.2
  let second := (stored.get ⟨1, by decide +kernel⟩).2.2
  let third := (stored.get ⟨2, by decide +kernel⟩).2.2
  let fourth := (stored.get ⟨3, by decide +kernel⟩).2.2
  exact first.addFour second third fourth

/-- The complete produced loop programme is the literal balanced addition of the four supplied original programmes. -/
theorem concatenate_program (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) :
    stored.concatenate.1 =
      (((stored.get ⟨0, by decide +kernel⟩).2.2.add (stored.get ⟨1, by decide +kernel⟩).2.2).add
        ((stored.get ⟨2, by decide +kernel⟩).2.2.add (stored.get ⟨3, by decide +kernel⟩).2.2)) := by
  unfold concatenate
  exact CertifiedProgram.Program.addFour_program _ _ _ _

/-- Each loop stage is the literal balanced pair of all four selected original whole caches. -/
theorem concatenate_stage (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) (index : Nat) :
    stored.concatenate.1.stage index =
      ((((stored.get ⟨0, by decide +kernel⟩).2.2.stage index).add
        ((stored.get ⟨1, by decide +kernel⟩).2.2.stage index)).add
      (((stored.get ⟨2, by decide +kernel⟩).2.2.stage index).add
        ((stored.get ⟨3, by decide +kernel⟩).2.2.stage index))) := by
  let first := (stored.get ⟨0, by decide +kernel⟩).2.2
  let second := (stored.get ⟨1, by decide +kernel⟩).2.2
  let third := (stored.get ⟨2, by decide +kernel⟩).2.2
  let fourth := (stored.get ⟨3, by decide +kernel⟩).2.2
  have outer := (first.add second).add_stage (third.add fourth) index
  have inner := congrArg₂ CertifiedProgram.CachedModel.add
    (first.add_stage second index) (third.add_stage fourth index)
  exact (congrArg (fun value => value.stage index) (concatenate_program stored)).trans (outer.trans inner)

/-- The actual closed-form loop sample adds the four saved source samples in their retained balanced order. -/
theorem concatenate_sample (stored : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges) (index : Nat) :
    (stored.concatenate.1.stage index).sample =
      (((stored.get ⟨0, by decide +kernel⟩).2.2.stage index).sample +
        ((stored.get ⟨1, by decide +kernel⟩).2.2.stage index).sample) +
      (((stored.get ⟨2, by decide +kernel⟩).2.2.stage index).sample +
        ((stored.get ⟨3, by decide +kernel⟩).2.2.stage index).sample) := by
  let first := (stored.get ⟨0, by decide +kernel⟩).2.2
  let second := (stored.get ⟨1, by decide +kernel⟩).2.2
  let third := (stored.get ⟨2, by decide +kernel⟩).2.2
  let fourth := (stored.get ⟨3, by decide +kernel⟩).2.2
  have outer := (first.add second).add_sample (third.add fourth) index
  have inner := congrArg₂ (fun first last : Canonical => first + last)
    (first.add_sample second index) (third.add_sample fourth index)
  exact (congrArg (fun value => (value.stage index).sample) (concatenate_program stored)).trans (outer.trans inner)

section Logarithmic

variable {circuit : Integral.Circuit base nonzero}
  (stored : Programs (unitBound := unitBound) (collarBound := collarBound) circuit.1 cached bounds edges)
  (logarithmic : { value :
    (program : CertifiedProgram.Program (Integral.Logarithmic.operations circuit)) ×
      NamedEquivalent circuit.channel.name program.output.name // value = Integral.Logarithmic.program circuit })
  (source : { value : stored.Result // value = stored.concatenate })

/-- Select the literal total-form caches at the same actual depths retained by the supplied logarithmic programme.

The supplied whole loop result is consumed directly. Its saved comparison
composes with the original stage-selection comparison; no source sum or
quarter builder is rerun. The logarithmic programme remains its actual
original producer, rather than an assumed or silently equal mesh.
-/
def selectLogarithmic : stored.Result :=
  let actual := source.val.1
  let selected := actual.selectStages (ParameterPrimitives.Program.depth logarithmic)
    (ParameterPrimitives.Program.depth_ge logarithmic)
  ⟨selected, source.val.2.trans
    (actual.selectedStages_output_equivalent (ParameterPrimitives.Program.depth logarithmic)
      (ParameterPrimitives.Program.depth_ge logarithmic) ⟨selected, rfl⟩)⟩

/-- The complete selected programme is the original stage-selection operation on the supplied whole loop result. -/
theorem selectLogarithmic_program :
    (selectLogarithmic stored logarithmic source).1 =
      source.val.1.selectStages (ParameterPrimitives.Program.depth logarithmic)
        (ParameterPrimitives.Program.depth_ge logarithmic) := by
  unfold selectLogarithmic
  rfl

/-- The selected whole stage is the same supplied original total-form cache at the actual saved logarithmic depth. -/
theorem selectLogarithmic_stage (index : Nat) :
    ((selectLogarithmic stored logarithmic source).1.stage index) =
      source.val.1.stage (ParameterPrimitives.Program.depth logarithmic index) := by
  unfold selectLogarithmic
  exact CertifiedProgram.Program.selectStages_stage _ _ _ index

end Logarithmic

end Programs

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop

end
