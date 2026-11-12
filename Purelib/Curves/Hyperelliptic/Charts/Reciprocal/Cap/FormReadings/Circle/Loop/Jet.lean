module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Jet.Program
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence

/-! # Four-quarter expansions of the same retained total-form programme -/

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
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical} {nonzero : base ≠ 0}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {data : Polynomials differential} {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {retained : jet.Principal data.1.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}

/-- The original local expansion result on the same supplied quarter curve and its actual total-form programme. -/
@[expose] def PreparedQuarter (cached : data.Bounds base)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (quarter : Quarter.UnitCircuitQuarter) (entry : Integral.QuarterData base nonzero quarter)
    (edges : DyadicEdges 0 start finish)
    (source : QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds quarter entry edges) :=
  Readings.Jets.Preparation (source := source.2.2) (origin := origin) (jet := jet) (remainder := remainder)
    (polynomial := data.1) (retained := retained) (primitive := primitive)

/-- The four original expansion preparations keep their exact supplied source programmes and curve-bank parents. -/
@[expose] def Expansions {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges) :=
  DependentProduct Integral.quarters fun index =>
    PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.get index)

/-- The exact original finite-expansion model keeps its same supplied source and quarter parents. -/
@[expose] def ExpandedModel {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :=
  Readings.Jets.Model (stored.get index).2.2 origin jet remainder data.1 retained primitive

/-- Sampling operations retain the original source programme and its same finite expansion parents at a quarter. -/
@[expose] def expandedOperations {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :
    CertifiedProgram.ModelOperations (ExpandedModel (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored index) :=
  Readings.Jets.operations (source := (stored.get index).2.2) (origin := origin) (jet := jet)
    (remainder := remainder) (polynomial := data.1) (retained := retained) (primitive := primitive)

/-- An actual expanded programme retains its same source programme and actual output comparison.

Each entry is the original preparation handler's complete result. The
dependent product preserves the four original quarter occurrences and
their supplied source and curve parents.
-/
@[expose] def ExpandedQuarter {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges)
    (index : Fin Integral.quarters.length) :=
  (produced : CertifiedProgram.Program (expandedOperations (origin := origin) (jet := jet)
    (remainder := remainder) (retained := retained) (primitive := primitive) stored index)) ×
    NamedEquivalent (stored.get index).2.2.output.name produced.output.name

/-- The original dependent product retains four complete expansion results at their same supplied source occurrences. -/
@[expose] def Expanded {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges) :=
  DependentProduct Integral.quarters fun index =>
    ExpandedQuarter (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored index

namespace Programs

/-- The supplied whole source bank retains the original four-quarter producer and its exact input caches. -/
@[expose] def Built (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) :=
  { value : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges //
    value = programs entries cached pairs degreeBound bounds edges }

namespace Built

/-- Every actual retained programme stage has its original requested dyadic index from the same supplied producer. -/
theorem stage_index {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
    {pairs : differential.denominatorPairs = 0} {degreeBound : differential.numerator.natDegree ≤ 2 * genus}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges) (index : Fin Integral.quarters.length) (depth : Nat) :
    (((stored.val.get index).2.2.stage depth).model).1 = depth := by
  have whole := congrArg (fun bank : Programs (unitBound := unitBound) (collarBound := collarBound)
    entries cached bounds edges => bank.get index) stored.property
  exact (congrArg (fun value => ((value.2.2.stage depth).model).1) whole).trans
    (get_programs_stage_index entries cached pairs degreeBound bounds edges index depth)

end Built

section Expansion

variable (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
  (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
  (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
  (edges : DyadicEdges 0 start finish)
  (stored : Built (unitBound := unitBound) (collarBound := collarBound)
    entries cached pairs degreeBound bounds edges)
  (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
  (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)

section

attribute [local irreducible] QuarterProgram

/-- Transport the same whole supplied source programme to the equal supplied quarter-curve parent. -/
private def moveQuarter (index : Fin Integral.quarters.length)
    (entry : Integral.QuarterData base nonzero (Integral.quarters[index.val]'index.isLt))
    (same : entry = entries.get index)
    (source : QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges) :
    QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) entry edges :=
  Eq.mp (congrArg (fun value : Integral.QuarterData base nonzero (Integral.quarters[index.val]'index.isLt) =>
    QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) value edges) same.symm) source

end

/-- The equal supplied source programme has the same original requested stage index at its actual curve parent. -/
private theorem moved_index (index : Fin Integral.quarters.length)
    (entry : Integral.QuarterData base nonzero (Integral.quarters[index.val]'index.isLt))
    (same : entry = entries.get index)
    (source : QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges)
    (sourceSame : source = stored.val.get index) (depth : Nat) :
    (((moveQuarter entries cached bounds edges index entry same source).2.2.stage depth).model).1 = depth := by
  cases same
  exact (congrArg (fun value => ((value.2.2.stage depth).model).1) sourceSame).trans
    (stored.stage_index index depth)

/-- The exact moved result type returns to its original supplied whole source programme and curve occurrence. -/
private theorem prepared_type (index : Fin Integral.quarters.length)
    (entry : Integral.QuarterData base nonzero (Integral.quarters[index.val]'index.isLt))
    (same : entry = entries.get index)
    (source : QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges)
    (sourceSame : source = stored.val.get index) :
    PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) entry edges
        (moveQuarter entries cached bounds edges index entry same source) =
    PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.val.get index) := by
  cases same
  cases sourceSame
  rfl

/-- Prepare one actual supplied quarter through the common retained numerical handler and exact source transport. -/
private def expandQuarter (index : Fin Integral.quarters.length)
    (entry : Integral.QuarterData base nonzero (Integral.quarters[index.val]'index.isLt))
    (supplied : QuarterProgram (unitBound := unitBound) (collarBound := collarBound)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges)
    (entryOrigin : entry = entries.get index) (sourceOrigin : supplied = stored.val.get index) :
    PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.val.get index) :=
  let source := moveQuarter entries cached bounds edges index entry entryOrigin supplied
  let produced := Readings.Jets.prepare (source := source.2.2) (origin := origin) (jet := jet)
    (remainder := remainder) (polynomial := data.1) (retained := retained) (primitive := primitive)
    (Integral.quarterBase_ne_zero base nonzero _) pairs degreeBound
    (moved_index entries cached pairs degreeBound bounds edges stored index entry entryOrigin supplied sourceOrigin)
    root bounds jetBounds anchor setup
  Eq.mp (prepared_type entries cached pairs degreeBound bounds edges stored index entry entryOrigin
    supplied sourceOrigin) produced

/-- Prepare the four actual original expansions using one supplied numerical square and factor handler.

The structural paired traversal consumes each supplied curve and whole
programme once. Exact origin equations derive its actual stage-index law
and transport only the dependent result type. The supplied numerical setup
is retained outside all quarter and stage lambdas; no source programme,
curve or factor-setup producer is rerun by the traversal.
-/
def expand : Expansions (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored.val :=
  DependentProduct.zipWith Integral.quarters entries stored.val
    (fun index => PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.val.get index))
    (expandQuarter entries cached pairs degreeBound bounds edges stored jetBounds anchor setup)

/-- Reading a built expansion returns the complete original preparation at that same original source and curve. -/
theorem get_expand (index : Fin Integral.quarters.length) :
    DependentProduct.get Integral.quarters
      (expand entries cached pairs degreeBound bounds edges stored jetBounds anchor setup) index =
    Readings.Jets.prepare (source := (stored.val.get index).2.2) (origin := origin) (jet := jet)
      (remainder := remainder) (polynomial := data.1) (retained := retained) (primitive := primitive)
      (Integral.quarterBase_ne_zero base nonzero _) pairs degreeBound
      (stored.stage_index index) root bounds jetBounds anchor setup := by
  unfold expand
  rewrite [DependentProduct.get_zipWith]
  unfold expandQuarter moveQuarter
  rfl

/-- Every actual quarter retains the same complete supplied positive numerical radius. -/
theorem get_expand_radius (index : Fin Integral.quarters.length) :
    (DependentProduct.get Integral.quarters
      (expand (origin := origin) (jet := jet) (remainder := remainder)
        (retained := retained) (primitive := primitive)
        entries cached pairs degreeBound bounds edges stored jetBounds anchor setup) index).1 = setup.val.1 :=
  (congrArg (fun value : PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
      (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
      cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.val.get index) =>
      value.1)
    (get_expand entries cached pairs degreeBound bounds edges stored jetBounds anchor setup index)).trans
      (Readings.Jets.prepare_radius (source := (stored.val.get index).2.2)
        (origin := origin) (jet := jet) (remainder := remainder) (polynomial := data.1)
        (retained := retained) (primitive := primitive) (Integral.quarterBase_ne_zero base nonzero _)
        pairs degreeBound (stored.stage_index index) root bounds jetBounds anchor setup)

/-- Construct one actual factor setup and the four expansions retaining that same complete supplied setup.

The numerical producer runs once before the paired traversal. Its result
is retained with its exact original producer identity; the returned whole
bank retains its same expansion producer and original curve/source inputs.
-/
def prepareExpansions :
    (saved : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor) ×
      { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
          (retained := retained) (primitive := primitive) stored.val //
        value = expand entries cached pairs degreeBound bounds edges stored jetBounds anchor saved } :=
  let actual := RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor
  let saved : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor := ⟨actual, rfl⟩
  let expanded := expand entries cached pairs degreeBound bounds edges stored jetBounds anchor saved
  ⟨saved, ⟨expanded, rfl⟩⟩

/-- Realize each supplied preparation once using its same retained common numerical radius.

The exact whole preparation-bank identity supplies each positive radius
readback. Quarter rotation preserves the original base quadrance, so the
single displayed radius bound pays every actual handler. Four bounded
lookups happen during materialization, outside all stage and observation
lambdas; the original setup and source producers are not rerun.
-/
def realize
    (prepared : { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
        (retained := retained) (primitive := primitive) stored.val //
      value = expand entries cached pairs degreeBound bounds edges stored jetBounds anchor setup })
    (near : Norm.Basic.normSq base ≤ setup.val.1.val ^ 2) :
    Expanded (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored.val :=
  DependentProduct.ofFn Integral.quarters fun index =>
    let actual := DependentProduct.get Integral.quarters prepared.val index
    have same : actual.1 = setup.val.1 :=
      (congrArg (fun bank : Expansions (origin := origin) (jet := jet) (remainder := remainder)
          (retained := retained) (primitive := primitive) stored.val =>
        (DependentProduct.get Integral.quarters bank index).1) prepared.property).trans
          (get_expand_radius entries cached pairs degreeBound bounds edges stored jetBounds anchor setup index)
    have quadrance := Integral.quarterBase_normSq base (Integral.quarters[index.val]'index.isLt)
    have paid := quadrance.trans_le
      (near.trans_eq (congrArg (fun radius : { value : Fraction.Rational // 0 < value } => radius.val ^ 2)
        same).symm)
    actual.2 paid

/-- Every realized quarter retains the requested actual source index through its same whole preparation cache.

The supplied complete preparation bank is linked to its original producer.
That equality transports the original prepare stage-index law; the actual
radius handler and original dependent-product lookup retain the same
programme and source-cache parents.
-/
theorem realize_stage_index
    (prepared : { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
        (retained := retained) (primitive := primitive) stored.val //
      value = expand entries cached pairs degreeBound bounds edges stored jetBounds anchor setup })
    (near : Norm.Basic.normSq base ≤ setup.val.1.val ^ 2)
    (index : Fin Integral.quarters.length) (depth : Nat) :
    ((DependentProduct.get Integral.quarters
      (realize entries cached pairs degreeBound bounds edges stored jetBounds anchor setup prepared near)
      index).1.stage depth).model.1 = depth := by
  let actual := DependentProduct.get Integral.quarters prepared.val index
  let Indexed := fun (value : PreparedQuarter (unitBound := unitBound) (collarBound := collarBound)
    (origin := origin) (jet := jet) (remainder := remainder) (retained := retained) (primitive := primitive)
    cached bounds (Integral.quarters[index.val]'index.isLt) (entries.get index) edges (stored.val.get index)) =>
    ∀ paid current, ((value.2 paid).1.stage current).model.1 = current
  have whole := (congrArg (fun bank : Expansions (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored.val =>
    DependentProduct.get Integral.quarters bank index) prepared.property).trans
      (get_expand entries cached pairs degreeBound bounds edges stored jetBounds anchor setup index)
  have canonical : Indexed actual := Eq.mp (congrArg Indexed whole.symm)
    (Readings.Jets.prepare_stage_index (source := (stored.val.get index).2.2)
      (origin := origin) (jet := jet) (remainder := remainder) (polynomial := data.1)
      (retained := retained) (primitive := primitive) (Integral.quarterBase_ne_zero base nonzero _)
      pairs degreeBound (stored.stage_index index) root bounds jetBounds anchor setup)
  unfold realize
  rewrite [DependentProduct.get_ofFn]
  exact canonical _ depth

end Expansion

end Programs

namespace Expanded

variable {entries : Integral.Entries base nonzero} {cached : data.Bounds base}
  {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
  {edges : DyadicEdges 0 start finish}
  {stored : Programs (unitBound := unitBound) (collarBound := collarBound) entries cached bounds edges}

/-- Read the complete saved expansion result at its same original supplied source and quarter occurrence. -/
@[expose] def get (expanded : Expanded (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored) (index : Fin Integral.quarters.length) :
    ExpandedQuarter (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored index :=
  DependentProduct.get Integral.quarters expanded index

/-- The actual balanced sum operations keep all four expanded source-indexed model families. -/
@[expose] def sumOperations :=
  ((expandedOperations (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored ⟨0, by decide +kernel⟩).add
    (expandedOperations (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored ⟨1, by decide +kernel⟩)).add
  ((expandedOperations (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored ⟨2, by decide +kernel⟩).add
    (expandedOperations (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored ⟨3, by decide +kernel⟩))

/-- A whole expanded loop result retains its actual supplied original total-form loop as comparison source. -/
@[expose] def Result (source : { value : stored.Result // value = stored.concatenate }) :=
  (produced : CertifiedProgram.Program (sumOperations (stored := stored) (origin := origin) (jet := jet)
    (remainder := remainder) (retained := retained) (primitive := primitive))) ×
      NamedEquivalent source.val.1.output.name produced.output.name

section

attribute [local irreducible] expandedOperations ExpandedModel

/-- Concatenate the actual four expansions and compare their output to the same supplied original loop result.

The source loop's saved comparison is composed with the four actual
handler comparisons and the new balanced sum's saved comparison. The
original loop producer, source programmes, zero procedures and factor
setup are not rerun. This compares the complete operational total-form
and finite-expansion programmes; it does not discard their error channels.
-/
def concatenate (expanded : Expanded (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored)
    (source : { value : stored.Result // value = stored.concatenate }) :
    Result (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) source := by
  let first := get expanded ⟨0, by decide +kernel⟩
  let second := get expanded ⟨1, by decide +kernel⟩
  let third := get expanded ⟨2, by decide +kernel⟩
  let fourth := get expanded ⟨3, by decide +kernel⟩
  let produced := first.1.addFour second.1 third.1 fourth.1
  let earlier := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (stored.get ⟨0, by decide +kernel⟩).2.2.output first.1.output
    (stored.get ⟨1, by decide +kernel⟩).2.2.output second.1.output first.2 second.2
  let later := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    (stored.get ⟨2, by decide +kernel⟩).2.2.output third.1.output
    (stored.get ⟨3, by decide +kernel⟩).2.2.output fourth.1.output third.2 fourth.2
  let compared := Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
    ((stored.get ⟨0, by decide +kernel⟩).2.2.output.add (stored.get ⟨1, by decide +kernel⟩).2.2.output)
    (first.1.output.add second.1.output)
    ((stored.get ⟨2, by decide +kernel⟩).2.2.output.add (stored.get ⟨3, by decide +kernel⟩).2.2.output)
    (third.1.output.add fourth.1.output) earlier later
  let names := congrArg (fun value : Name.Coherent.CoherentNamed => value.name) (Programs.channels_eq stored)
  let comparedChannels := NamedEquivalent.transport names.symm rfl (compared.trans produced.2)
  exact ⟨produced.1, source.val.2.symm.trans comparedChannels⟩

/-- The complete expanded loop programme is the literal balanced addition of the four supplied expanded programmes. -/
theorem concatenate_program (expanded : Expanded (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive) stored)
    (source : { value : stored.Result // value = stored.concatenate }) :
    (concatenate expanded source).1 =
      (((get expanded ⟨0, by decide +kernel⟩).1.add (get expanded ⟨1, by decide +kernel⟩).1).add
        ((get expanded ⟨2, by decide +kernel⟩).1.add (get expanded ⟨3, by decide +kernel⟩).1)) := by
  unfold concatenate
  exact CertifiedProgram.Program.addFour_program _ _ _ _

end

end Expanded

namespace Programs

/-- Prepare the actual expanded closed-loop programme on one computed common numerical square.

The original source aggregate is supplied whole. One factor setup and
one preparation bank are retained before the radius handler. A paid base
quadrance realizes the four same source-indexed expansion programmes and
concatenates their saved comparisons with that original source aggregate.
No integral vanishing or physical residue claim is an input or conclusion.
-/
def prepareLoop (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (source : { value : stored.val.Result // value = stored.val.concatenate } :=
      ⟨stored.val.concatenate, rfl⟩) :
    (radius : { value : Fraction.Rational // 0 < value }) ×
      (Norm.Basic.normSq base ≤ radius.val ^ 2 →
        Expanded.Result (origin := origin) (jet := jet) (remainder := remainder)
          (retained := retained) (primitive := primitive) source) :=
  let prepared := prepareExpansions (origin := origin) (jet := jet) (remainder := remainder)
    (retained := retained) (primitive := primitive)
    entries cached pairs degreeBound bounds edges stored jetBounds anchor
  ⟨prepared.1.val.1, fun near =>
    let expanded := realize entries cached pairs degreeBound bounds edges stored jetBounds anchor
      prepared.1 prepared.2 near
    Expanded.concatenate expanded source⟩

/-- The complete positive radius is the same original common numerical setup's retained radius. -/
theorem prepareLoop_radius (entries : Integral.Entries base nonzero) (cached : data.Bounds base)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      entries cached pairs degreeBound bounds edges)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (source : { value : stored.val.Result // value = stored.val.concatenate }) :
    (prepareLoop (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive)
      entries cached pairs degreeBound bounds edges stored jetBounds anchor source).1 =
        (RootCoordinates.prepareJetFactors origin jet root bounds jetBounds anchor).1 := by
  unfold prepareLoop prepareExpansions
  rfl

end Programs

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop

end
