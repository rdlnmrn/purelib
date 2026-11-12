module

import Purelib.System.IO.Reference

import Purelib.System.IO
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Codec

public import Purelib.Data.List.DependentProduct
public import scripts.checkpoint.InitialExtraction
public import scripts.checkpoint.CoherentRootSamples
import scripts.checkpoint.RawSubdivision
public import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Admission
import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Build
import Purelib.RootIsolation.FTA.Positive.Build
import Purelib.RootIsolation.Multiplicity.Family.Build
import Purelib.RootIsolation.Multiplicity.Observation.Build
import Purelib.Polynomial.Dense.Gaussian.Unit
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Build
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Persistent
import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.System.FilePath

/-!
# Original multiplicity and CCL results from checked saved isolation

The original preprocessing and cancellation select the same finite factors
and branches. Higher factors reuse complete checked coefficient-selected
isolation; exact linear factors retain their original formula. Complete
readbacks identify the original families, quotient result and CCL attachment.

Enabled retained results also carry the actual elimination certificates in
products indexed by the same ordered contexts on both sides. Admission and
state-prefix replay consume those entries at their original indices. Disabled
retention returns the complete original result and checkpoint action.
-/

open Purelib.Data.Rat.Fraction (Rational)

public section

namespace MultiplicityCheckpoint

open Purelib.RootIsolation.Multiplicity
open Purelib.RationalFunctions.ArgumentPrinciple
open Purelib.Data.List (DependentProduct)

open Purelib
open Purelib.Data (Json)
open Purelib.Data.Json (toJson)
open IntegrationCheckpoint (fractionData gaussianData)
open Purelib.Polynomial
open Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open CoherentRoot (CertifiedName)
open Purelib.Approximation.Gaussian
open Purelib.RationalFunctions
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)

/-- An optional retained-data view of the same complete original execution result.

The disabled index is exactly the original result subtype. The enabled index
adds actual cached data beside that result, without changing its nominal owner.
-/
abbrev Retained (enabled : Bool) {α : Type} (cache : α → Type) (expected : α) :=
  if enabled then {result : (Σ value, cache value) // result.1 = expected}
  else {result : α // result = expected}

namespace Retained

variable {α : Type} {cache : α → Type} {expected : α}

/-- Read the complete original result from either exact retained-data view. -/
@[expose] def value (enabled : Bool) (saved : Retained enabled cache expected) : α :=
  match enabled with
  | false => saved.val
  | true => saved.val.1

/-- Both retained-data views identify the same complete original constructor. -/
theorem same (enabled : Bool) (saved : Retained enabled cache expected) :
    value enabled saved = expected := by
  cases enabled with
  | false => exact saved.property
  | true => exact saved.property

/-- Read the supplied cached data only from the enabled exact result view. -/
def data (enabled : Bool) (saved : Retained enabled cache expected)
    (active : enabled = true) : cache (value enabled saved) := by
  cases active
  exact saved.val.2

/-- Package an original result, forcing additional retained data only when enabled. -/
@[expose] def pack (enabled : Bool) (result : α) (same : result = expected)
    (cached : Unit → enabled = true → cache result) : Retained enabled cache expected :=
  match enabled with
  | false => ⟨result, same⟩
  | true => ⟨⟨result, cached () rfl⟩, same⟩

end Retained

namespace Eliminations

/-- Exact original elimination data retained beside one positive-degree result. -/
@[expose] def positive {polynomial : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput polynomial) :
    FTA.Positive.Basic.PositiveResult polynomial → Type
  | .linear _ _ => PUnit
  | .higher _ degree =>
      {value : AxisEliminationCertificate polynomial
        (FTA.Squarefree.Input.mk input.squarefree degree).eliminationDegree //
        value = (FTA.Squarefree.Input.mk input.squarefree degree).elimination}

/-- Exact original elimination data at the same focused multiplicity observation. -/
@[expose] def observation {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries} :
    PositiveSideInput.FactorObservation input context → Type
  | .exact _ _ _ => PUnit
  | .higher _ degree =>
      {value : AxisEliminationCertificate context.focus.part.polynomial
        (FTA.Squarefree.Input.mk context.focus.part.squarefree degree).eliminationDegree //
        value = (FTA.Squarefree.Input.mk context.focus.part.squarefree degree).elimination}

/-- Retain the same positive-result cache when attaching its original focused observation. -/
def ofPositive {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (result : FTA.Positive.Basic.PositiveResult context.focus.part.polynomial) :
    positive ⟨context.focus.part.squarefree, context.focus.degreePositive⟩ result →
      observation (input.fromPositive context result) := by
  cases result with
  | linear => exact fun _ => PUnit.unit
  | higher => exact fun cached => cached

/-- Actual certificate entries at each original ordered observation occurrence. -/
abbrev observations {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {contexts : List (Context.Basic.PositiveContext input.entries)}
    (saved : PositiveSideInput.Observations input contexts) :=
  DependentProduct contexts (fun index => observation (DependentProduct.get contexts saved index))

/-- Actual certificate entries at each original retained family occurrence. -/
abbrev family {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    (saved : PositiveSideInput.PositiveFamily input) :=
  DependentProduct input.contexts (fun index => observation (saved.observationAt index))

/-- Retained elimination entries for the same original constant or positive side. -/
@[expose] def side {source opposite : CoefficientPolynomial} :
    Multiplicity.Side.Basic.SideResult source opposite → Type
  | .constant _ _ _ => PUnit
  | .positive _ saved => family saved

/-- Both actual elimination banks of the same original reduced quotient result. -/
@[expose] def quotient {numerator denominator : CoefficientPolynomial} :
    ArgumentPrinciple.General.Result numerator denominator → Type
  | .zeroNumerator _ _ => PUnit
  | .nonzero result => side result.numeratorSites × side result.denominatorSites

/-- Both actual elimination banks of the same original CCL attachment. -/
@[expose] def ccl {numerator denominator : CoefficientPolynomial} :
    CCL.Basic.Result numerator denominator → Type
  | .zeroNumerator _ _ => PUnit
  | .nonzero result => side result.rfap.numeratorSites × side result.rfap.denominatorSites

/-- Retain both original banks when attaching CCL data to the same quotient result. -/
def ofQuotient {numerator denominator : CoefficientPolynomial}
    (result : ArgumentPrinciple.General.Result numerator denominator) :
    quotient result → ccl (CCL.Build.fromResult result) := by
  cases result with
  | zeroNumerator => exact fun _ => PUnit.unit
  | nonzero => exact fun cached => cached

end Eliminations

/-- Restore the complete original positive-degree root result using the same retained squarefree input.

Degree one keeps the original exact formula. Higher degrees consume their
same complete coefficient-selected isolation, original ordered seed attempts,
raw subdivision and band checkpoints. Every return proves full result equality.
-/
@[expose] def positive {polynomial : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput polynomial)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain (Eliminations.positive input) (FTA.Positive.Build.provePositive input request)) := do
  if higher : 2 ≤ polynomial.natDegree then
    let retainedInput : FTA.Squarefree.Input polynomial := ⟨input.squarefree, higher⟩
    let elimination := retainedInput.elimination
    let saved ← InitialExtractionCheckpoint.separatedLargeSquareWithElimination retainedInput elimination rfl
      columns winding control directory request
    let cached : Option {value : AxisEliminationCertificate polynomial retainedInput.eliminationDegree //
        value = retainedInput.elimination} := if retain then some ⟨elimination, rfl⟩ else none
    let boxes := FTA.Squarefree.Build.BoxFTA.fromIsolation retainedInput saved.val cached
    let value := FTA.Positive.Basic.PositiveResult.higher boxes higher
    have same : value = FTA.Positive.Build.provePositive input request :=
      (congrArg (fun boxes => FTA.Positive.Basic.PositiveResult.higher boxes higher)
        (FTA.Squarefree.Build.BoxFTA.fromIsolation_cached_eq_default retainedInput saved.val cached)).trans
          (FTA.Positive.Build.fromIsolation_eq_provePositive input higher saved.val
            (request := request) saved.property)
    return Retained.pack retain value same (fun _ _ => ⟨elimination, rfl⟩)
  else
    let same : polynomial.natDegree = 1 :=
      Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge higher))
        (Nat.succ_le_of_lt input.degreePositive)
    return Retained.pack retain (FTA.Positive.Build.fromDegree input 1 same request)
      (FTA.Positive.Build.fromDegree_eq_provePositive input 1 same request) (fun _ _ => PUnit.unit)

/-- Attach an original focused multiplicity observation to the same restored positive-degree result.

The source decomposition, focused occurrence, multiplicity and opposite
cofactor remain those of the supplied input. The stored higher box family
or exact linear root is passed directly into the original observation constructor.
-/
@[expose] def observation {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.observation (input.observe context request)) := do
  let saved ← positive ⟨context.focus.part.squarefree, context.focus.degreePositive⟩
    columns winding control directory request retain
  let value := Retained.value retain saved
  return Retained.pack retain (input.fromPositive context value)
    (input.fromPositive_eq_observe context value (request := request) (Retained.same retain saved))
    (fun _ active => Eliminations.ofPositive input context value (Retained.data retain saved active))

/-- Restore every original focused observation once in its original structural order.

Each directory records that same context's complete isolation. The structural
tail retains the original remaining contexts, and the return identifies the
entire observation cache rather than only its individual lookups.
-/
@[expose] def observations {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    (contexts : List (Context.Basic.PositiveContext input.entries)) → (index : Nat) →
    (request : Option Rational := none) → (retain : Bool := false) →
    IO (Retained retain Eliminations.observations
      (PositiveSideInput.Observations.ofContexts input contexts request))
  | [], _, _, retain => pure (Retained.pack retain PUnit.unit rfl (fun _ _ => PUnit.unit))
  | context :: contexts, index, request, retain => do
      let first ← observation input context columns winding control
        (Purelib.System.FilePath.join directory (System.FilePath.mk s!"context-{index}")) request retain
      let tail ← observations input columns winding control directory contexts (index + 1) request retain
      let firstValue := Retained.value retain first
      let tailValue := Retained.value retain tail
      return Retained.pack retain (firstValue, tailValue)
        ((congrArg (fun head => (head, tailValue))
          (Retained.same retain first)).trans
          (congrArg (fun remaining => (input.observe context request, remaining))
            (Retained.same retain tail)))
        (fun _ active => (Retained.data retain first active, Retained.data retain tail active))

/-- Assemble the complete original multiplicity family from its restored original ordered observations. -/
@[expose] def family {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.family (input.buildFamily request)) := do
  let saved ← observations input columns winding control directory input.contexts 0 request retain
  let value := Retained.value retain saved
  return Retained.pack retain (input.fromObservations value)
    (input.fromObservations_eq_buildFamily value (request := request) (Retained.same retain saved))
    (fun _ active => Retained.data retain saved active)

/-- Restore the original constant or positive side using its shared original preprocessing branch.

The positive callback retains the same preprocessing and executable Bézout
certificate. Its actual restored family is attached once, preserving the
complete original side result and all source multiplicities.
-/
@[expose] def side (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source) (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.side
      (Multiplicity.Side.Build.buildSide source opposite sourceNormalized
        sourceNonzero oppositeNonzero coprime request)) :=
  Multiplicity.Side.Build.withInput source opposite sourceNormalized sourceNonzero oppositeNonzero coprime
    (fun degreeZero same => pure (Retained.pack retain
      (.constant sourceNonzero degreeZero oppositeNonzero)
      (Multiplicity.Side.Build.buildSide_eq_constant source opposite sourceNormalized sourceNonzero
        oppositeNonzero coprime degreeZero same request).symm (fun _ _ => PUnit.unit)))
    (fun input same coprimeSame => do
      let saved ← family input columns winding control directory request retain
      let value := Retained.value retain saved
      return Retained.pack retain (.positive input value)
        ((congrArg (Multiplicity.Side.Basic.SideResult.positive input) (Retained.same retain saved)).trans
          (Multiplicity.Side.Build.buildSide_eq_positive source opposite sourceNormalized sourceNonzero
            oppositeNonzero coprime input same coprimeSame request).symm)
        (fun _ active => Retained.data retain saved active))

/-- Restore the complete original reduced quotient result from both same retained multiplicity sides.

The shared original zero test and cancellation run once. Both actual side
results are passed into the original certificate constructor, and its complete
readback retains the original reduction, degree balances and separation.
-/
@[expose] def quotient (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.quotient
      (ArgumentPrinciple.General.prove numerator denominator denominatorNonzero request)) :=
  ArgumentPrinciple.General.withInput numerator denominator denominatorNonzero
    (fun numeratorZero => pure (Retained.pack retain (.zeroNumerator numeratorZero denominatorNonzero)
      (ArgumentPrinciple.General.prove_eq_zero numerator denominator denominatorNonzero numeratorZero request).symm
      (fun _ _ => PUnit.unit)))
    (fun numeratorNonzero input same => do
      let numeratorSites ← side input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.reduction.numeratorReduced_normalized input.numeratorReducedNonzero input.denominatorReducedNonzero
        (Reduction.Basic.ReducedPair.coprime input.reduction) columns winding control
        (Purelib.System.FilePath.join directory "numerator") request retain
      let denominatorSites ← side input.reduction.denominatorReduced input.reduction.numeratorReduced
        input.reduction.denominatorReduced_normalized input.denominatorReducedNonzero input.numeratorReducedNonzero
        (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
          (Reduction.Basic.ReducedPair.coprime input.reduction))
        columns winding control (Purelib.System.FilePath.join directory "denominator") request retain
      let numeratorValue := Retained.value retain numeratorSites
      let denominatorValue := Retained.value retain denominatorSites
      return Retained.pack retain
        (.nonzero (ArgumentPrinciple.General.NonzeroResult.fromSides input numeratorValue denominatorValue))
        (ArgumentPrinciple.General.prove_eq_nonzero numerator denominator denominatorNonzero numeratorNonzero
          input same (request := request) numeratorValue (Retained.same retain numeratorSites)
          denominatorValue (Retained.same retain denominatorSites)).symm
        (fun _ active => (Retained.data retain numeratorSites active, Retained.data retain denominatorSites active)))

/-- Attach original CCL data to the same restored complete original quotient result. -/
@[expose] def ccl (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.ccl
      (CCL.Build.prove numerator denominator denominatorNonzero request)) := do
  let saved ← quotient numerator denominator denominatorNonzero columns winding control directory request retain
  let value := Retained.value retain saved
  return Retained.pack retain (CCL.Build.fromResult value)
    (CCL.Build.fromResult_eq_prove numerator denominator denominatorNonzero value
      (request := request) (Retained.same retain saved))
    (fun _ active => Eliminations.ofQuotient value (Retained.data retain saved active))

/-- Restore the complete original coefficient-first polynomial CCL source, including every original multiplicity site.

The polynomial-facing `p / 1` constructor keeps its original cancellation,
complete factor families and indexed CCL attachments. Its full equality
identifies the same original polynomial-source result.
-/
@[expose] def polynomial (source : CoefficientPolynomial)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) (retain : Bool := false) :
    IO (Retained retain Eliminations.ccl (CCL.Polynomial.Build.isolate source request)) := do
  match request with
  | none => pure ()
  | some width =>
      InitialExtractionCheckpoint.retainSturmRequest control directory "multiplicity-request.json"
        (Json.mkObj
          [("format", toJson "ccl-multiplicity-isolation-request-v1"),
           ("factory", toJson "canonical-five-then-real-axis-event"),
           ("polynomial", toJson (source.coeffs.map gaussianData)),
           ("eventWidth", toJson (fractionData width))])
  ccl source Dense.Gaussian.Unit.unitDenominator Dense.Gaussian.Unit.unitDenominator_isZero
    columns winding control directory request retain

/-- The absent event request preserves the whole original polynomial checkpoint action. -/
theorem polynomial_none (source : CoefficientPolynomial)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    polynomial source columns winding control directory none =
      ccl source Dense.Gaussian.Unit.unitDenominator Dense.Gaussian.Unit.unitDenominator_isZero
        columns winding control directory := rfl

/-- Restore exact original states at one retained observation and its actual dependent site index.

The original attachment identity and complete Newton origin determine the
same track consumed by root-prefix replay. Exact observations have no root
states and preserve their original unit cache view.
-/
@[expose] def observationStates {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (count : Nat) (cached : Option (Eliminations.observation observation) := none) :
    IO (Observation.CCL.Admission.StateCache observation data index) := by
  cases observation with
  | exact => exact pure PUnit.unit
  | higher boxes degree =>
      let retainedInput : FTA.Squarefree.Input context.focus.part.polynomial :=
        ⟨context.focus.part.squarefree, degree⟩
      let track := data.boxes.isolation.trackAt index
      have canonical : ∀ current epsilon positive, track.refine current epsilon positive =
          Track.Newton.Refinement.refineState retainedInput.degreeAtLeastTwo retainedInput.squarefree
            retainedInput.elimination current epsilon positive := by
        cases dataEq
        exact Track.Newton.Build.Origin.refine (origins index)
      exact RawSubdivisionCheckpoint.rootPrefix retainedInput
        (RootRefinementCheckpoint.ClearanceLoader.separated columns _
          retainedInput.nonzero retainedInput.degreePositive)
        columns winding directory track canonical count cached

/-- Restore exact original root-state entries for one actual admitted side index.

The supplied provenance is the complete original Newton constructor at that
same index. The attachment identity retains precisely the original numerical
boxes. The same observation restorer consumes its existing context and index.
-/
@[expose] def admissionStates {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side) (count : Nat)
    (cached : Option (Eliminations.side side) := none) :
    IO (Side.CCL.Admission.StateCache side data index) := by
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      exact observationStates (family.observationAt index.1)
        (data index.1) (origins index.1) (congrArg (fun current => current index.1) dataEq)
        columns winding directory index.2 count
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- Retain an admitted observation's completed state entries behind its same original root-view reader.

Exact evidence has no numerical states. A higher admission retains its actual
realization and attachment index. One shared reader starts with the supplied
completed prefix and restores only missing successors through the original
Newton law and the same retained elimination certificate.
-/
def withObservationStateReaders {α : Type} {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (admission : Observation.CCL.Admission observation data index)
    (initial : Observation.CCL.Admission.StateCache observation data index)
    (use : ((view : CertifiedName.View admission.channel) → admission.view? = some view →
      (stage : Nat) → IO (CoherentRootCheckpoint.State view.root stage)) → IO α)
    (cached : Option (Eliminations.observation observation) := none) : IO α := by
  rcases admission with ⟨channel, equivalent, evidence, equation⟩
  cases observation with
  | exact root degree oppositeAtRoot =>
      cases evidence with
      | exact _ _ _ _ _ _ _ =>
          exact use (fun _ found _ => by cases found)
  | higher boxes degree =>
      cases evidence with
      | higher _ _ _ index realization channelEq => exact do
          let retainedInput : FTA.Squarefree.Input context.focus.part.polynomial :=
            ⟨context.focus.part.squarefree, degree⟩
          let track := data.boxes.isolation.trackAt index
          have canonical : ∀ current epsilon positive, track.refine current epsilon positive =
              Track.Newton.Refinement.refineState retainedInput.degreeAtLeastTwo retainedInput.squarefree
                retainedInput.elimination current epsilon positive := by
            cases dataEq
            exact Track.Newton.Build.Origin.refine (origins index)
          let root := realization.root
          let retained : Thunk (FTA.Squarefree.Input.Elimination retainedInput) := Thunk.mk fun _ =>
            match cached with
            | none => FTA.Squarefree.Input.Elimination.ofInput retainedInput
            | some saved => FTA.Squarefree.Input.Elimination.ofCertificate retainedInput saved.val saved.property
          let states ← CoherentRootCheckpoint.stateReader (track := track) root
            (CoherentRootCheckpoint.readStateWith (track := track) root
              (CoherentRootCheckpoint.nextState (track := track) root retainedInput retained
                canonical columns winding directory)) initial
          use (fun view found stage => by
            have same := Option.some.inj found
            cases same
            exact states stage)

/-- Retain the same admitted side site's view reader at its original context and bounded index.

The selected observation consumes the exact supplied completed-state bank.
Its future reads preserve the original side attachment, Newton origin,
numerical controls and retained elimination cell.
-/
def withAdmissionStateReaders {α : Type} {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side)
    (admission : Side.CCL.Admission side data index)
    (initial : Side.CCL.Admission.StateCache side data index)
    (use : ((view : CertifiedName.View (Side.CCL.Admission.channel admission)) →
      Side.CCL.Admission.view? admission = some view →
      (stage : Nat) → IO (CoherentRootCheckpoint.State view.root stage)) → IO α)
    (cached : Option (Eliminations.side side) := none) : IO α := by
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      exact withObservationStateReaders (family.observationAt index.1)
        (data index.1) (origins index.1) (congrArg (fun current => current index.1) dataEq)
        columns winding directory index.2 admission initial use
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- Restore and consume exact original state entries in the same indexed polynomial admission.

The actual original result and complete attachment remain the parents of the
returned admission. The callback also receives that exact completed state
bank. The whole default equation proves cache consumption leaves the original
channel, source equation and every admission field identical.
-/
@[expose] def polynomialAdmission {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (origins : (CCL.Basic.Result.nonzero result).NewtonOrigins)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) (count : Nat)
    (consume : (value : CCL.Polynomial.Admission result index) →
      value = CCL.Polynomial.Admission.ofResult result index →
      Side.CCL.Admission.StateCache result.rfap.numeratorSites result.numeratorCCL index → IO Unit)
    (cached : Option (Eliminations.ccl (.nonzero result)) := none) : IO Unit := do
  let cached ← admissionStates result.rfap.numeratorSites result.numeratorCCL
    origins.1.1 origins.2.1 columns winding directory index count (cached.map Prod.fst)
  consume (CCL.Polynomial.Admission.ofResult result index (some cached))
    (CCL.Polynomial.Admission.ofResult_cached_eq_default result index (some cached)) cached

section

open Purelib.RootIsolation.Multiplicity.CCL.Polynomial
open Purelib.Data.CCL.Transducer (Machine)

/-- Prepare exact original numerical replies for one persistent observation request.

The action owns this same observation and site. One retained elimination cell
serves every demanded higher refinement. Ordered request directories retain
their exact current-state/radius headers; callers use a distinct directory for
each joint request and recreate this reader to resume that same request.
-/
def observationHandler {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (cached : Option (Eliminations.observation observation) := none) :
    IO (Observation.CCL.Numerical.Handler IO observation data index) := by
  cases dataEq
  cases observation with
  | exact => exact pure (fun _ _ _ => pure ⟨(), rfl⟩)
  | higher boxes degree =>
      let retainedInput : FTA.Squarefree.Input context.focus.part.polynomial :=
        ⟨context.focus.part.squarefree, degree⟩
      let retained : Thunk (Eliminations.observation (.higher boxes degree)) :=
        ⟨fun _ => match cached with | none => ⟨retainedInput.elimination, rfl⟩ | some value => value⟩
      let track := boxes.isolation.trackAt index
      exact do
        let ordinal ← System.IO.mkRef 0
        pure (fun current epsilon positive => do
          let step ← System.IO.Ref.get ordinal
          let saved := retained.get
          let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns _
            retainedInput.nonzero retainedInput.degreePositive
          let savedLoader := RootRefinementCheckpoint.ClearanceLoader.cast saved.property.symm loader
          let reply ← RawSubdivisionCheckpoint.refineTrack retainedInput saved.val saved.property savedLoader
            columns winding (Purelib.System.FilePath.join directory s!"request-{step}") track
            (Track.Newton.Build.Origin.refine (origins index)) current epsilon positive
          ordinal.set (step + 1)
          pure reply)

/-- Prepare the numerical action at the same original reduced-side site and retained elimination entry. -/
def admissionHandler {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side)
    (cached : Option (Eliminations.side side) := none) :
    IO (Side.CCL.Persistent.NumericalHandler IO side data index) := by
  cases dataEq
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      exact observationHandler (family.observationAt index.1)
        (Observation.CCL.Basic.observationCCL (family.observationAt index.1))
        (origins index.1) rfl columns winding directory index.2
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- Execute the complete original root request through exact saved numerical actions and its retained cursor history.

The actual result, attachment and dependent root index remain fixed. The
reader is scoped to this joint request, so a retry recreates its ordered
source path and reloads completed original refinements. Successful consecutive
requests consume their actual returned root state and history in distinct
request directories, reusing the same supplied coefficient cache.
-/
def polynomialRequest {α : Type} {initial : Machine.Snapshot} {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (origins : (CCL.Basic.Result.nonzero result).NewtonOrigins)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result)
    (current : Persistent.NonzeroResult.RootState result index) (history : Machine.History initial)
    (cursorEq : history.current.machine = Persistent.NonzeroResult.rootMachine result index current)
    (sourceEq : history.current.source =
      Side.CCL.Persistent.sourceProcess result.rfap.numeratorSites result.numeratorCCL index)
    (epsilon : Rational) (positive : 0 < epsilon) (count : Nat)
    (consume : (next : Persistent.NonzeroResult.RootState result index) →
      next = Persistent.NonzeroResult.rootRequest result index current epsilon positive count →
      (retained : Machine.History initial) →
        retained.current.machine = Persistent.NonzeroResult.rootMachine result index next →
        retained.current.source =
          Side.CCL.Persistent.sourceProcess result.rfap.numeratorSites result.numeratorCCL index → IO α)
    (cached : Option (Eliminations.ccl (.nonzero result)) := none) : IO α := do
  let execute ← admissionHandler result.rfap.numeratorSites result.numeratorCCL origins.1.1 origins.2.1
    columns winding directory index (cached.map Prod.fst)
  Persistent.NonzeroResult.withRootRequest result index execute current history cursorEq sourceEq epsilon positive count
    consume

end

/-- Restore exact productive-name observations at the retained attachment and dependent site index.

Higher observations consume the original Newton trajectory and actual
elimination cache. Exact observations need no numerical refinement. The
returned finite table is indexed by the original complete arithmetic name.
-/
def observationSamples {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (count : Nat) (cached : Option (Eliminations.observation observation) := none) :
    IO (Sequence.SamplePrefix (Name.Sampling.approximation
      (Observation.CCL.Name.observationArithmeticName observation data index))) := by
  cases dataEq
  cases observation with
  | exact => exact pure (Sequence.SamplePrefix.ofEntries _ [])
  | higher boxes degree =>
      let retainedInput : FTA.Squarefree.Input context.focus.part.polynomial :=
        ⟨context.focus.part.squarefree, degree⟩
      let track := boxes.isolation.trackAt index
      exact RawSubdivisionCheckpoint.samplingPrefix retainedInput
        (RootRefinementCheckpoint.ClearanceLoader.separated columns _
          retainedInput.nonzero retainedInput.degreePositive)
        columns winding directory track
        (Track.Newton.Build.Origin.refine (origins index)) count cached

/-- Restore observations of the original productive name at its same ordered side-site index. -/
def admissionSamples {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side) (count : Nat)
    (cached : Option (Eliminations.side side) := none) :
    IO (Sequence.SamplePrefix (Name.Sampling.approximation
      (Side.CCL.Name.sideArithmeticName side data index))) := by
  cases dataEq
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      exact observationSamples (family.observationAt index.1)
        (Observation.CCL.Basic.observationCCL (family.observationAt index.1))
        (origins index.1) rfl columns winding directory index.2 count
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- Restore a finite checked observation table of one original polynomial root-stream name.

The actual result, attachment, dependent root index and complete Newton
origin determine the source. Supplied coefficient-producer elimination
entries are selected at their original context index and consumed directly.
-/
def polynomialSamples {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (origins : (CCL.Basic.Result.nonzero result).NewtonOrigins)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) (count : Nat)
    (cached : Option (Eliminations.ccl (.nonzero result)) := none) :
    IO (Sequence.SamplePrefix (Name.Sampling.approximation
      (CCL.Polynomial.Name.NonzeroResult.rootName result index))) :=
  admissionSamples result.rfap.numeratorSites result.numeratorCCL origins.1.1 origins.2.1
    columns winding directory index count (cached.map Prod.fst)

/-- Exact original elimination data preserves the complete observation-sampling checkpoint action. -/
theorem observationSamples_cached_eq_default {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (count : Nat) (cached : Option (Eliminations.observation observation)) :
    observationSamples observation data origins dataEq columns winding directory index count cached =
      observationSamples observation data origins dataEq columns winding directory index count := by
  cases dataEq
  cases observation with
  | exact => exact (rfl)
  | higher boxes degree =>
      exact RawSubdivisionCheckpoint.samplingPrefix_cached_eq_default _ _ _ _ _ _ _ _ cached

/-- Ordered retained elimination entries preserve the complete side-sampling checkpoint action. -/
theorem admissionSamples_cached_eq_default {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side) (count : Nat)
    (cached : Option (Eliminations.side side)) :
    admissionSamples side data origins dataEq columns winding directory index count cached =
      admissionSamples side data origins dataEq columns winding directory index count := by
  cases dataEq
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      unfold admissionSamples
      exact observationSamples_cached_eq_default (family.observationAt index.1)
        (Observation.CCL.Basic.observationCCL (family.observationAt index.1))
        (origins index.1) rfl columns winding directory index.2 count
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- The original coefficient-producer cache preserves the complete polynomial-sampling checkpoint action. -/
theorem polynomialSamples_cached_eq_default {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (origins : (CCL.Basic.Result.nonzero result).NewtonOrigins)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) (count : Nat)
    (cached : Option (Eliminations.ccl (.nonzero result))) :
    polynomialSamples result origins columns winding directory index count cached =
      polynomialSamples result origins columns winding directory index count := by
  unfold polynomialSamples
  exact admissionSamples_cached_eq_default _ _ _ _ _ _ _ _ _ _

/-- Supplied elimination data preserves the complete original observation-state action. -/
theorem observationStates_cached_eq_default {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite} {context : Context.Basic.PositiveContext input.entries}
    (observation : PositiveSideInput.FactorObservation input context)
    (data : Observation.CCL.Basic.ObservationCCL observation)
    (origins : observation.NewtonOrigins)
    (dataEq : data = Observation.CCL.Basic.observationCCL observation)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Observation.Index.ObservationIndex observation)
    (count : Nat) (cached : Option (Eliminations.observation observation)) :
    observationStates observation data origins dataEq columns winding directory index count cached =
      observationStates observation data origins dataEq columns winding directory index count := by
  cases dataEq
  cases observation with
  | exact => exact (rfl)
  | higher boxes degree =>
      exact RawSubdivisionCheckpoint.rootPrefix_cached_eq_default _ _ _ _ _ _ _ _ cached

/-- Supplied ordered certificates preserve the complete original side-state action. -/
theorem admissionStates_cached_eq_default {source opposite : CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (data : Side.CCL.Basic.SideCCL side)
    (origins : side.NewtonOrigins) (dataEq : data = Side.CCL.Basic.sideCCL side)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (index : Multiplicity.Side.Index.SideIndex side) (count : Nat)
    (cached : Option (Eliminations.side side)) :
    admissionStates side data origins dataEq columns winding directory index count cached =
      admissionStates side data origins dataEq columns winding directory index count := by
  cases dataEq
  cases side with
  | constant => exact nomatch index
  | positive input family =>
      unfold admissionStates
      exact observationStates_cached_eq_default (family.observationAt index.1)
        (Observation.CCL.Basic.observationCCL (family.observationAt index.1))
        (origins index.1) rfl columns winding directory index.2 count
        (cached.map (fun entries => DependentProduct.get input.contexts entries index.1))

/-- Supplied producer certificates preserve the complete original admission-consumer action. -/
theorem polynomialAdmission_cached_eq_default {polynomial : CoefficientPolynomial}
    (result : CCL.Polynomial.Basic.NonzeroResult polynomial)
    (origins : (CCL.Basic.Result.nonzero result).NewtonOrigins)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath)
    (index : CCL.Polynomial.Index.NonzeroResult.RootIndex result) (count : Nat)
    (consume : (value : CCL.Polynomial.Admission result index) →
      value = CCL.Polynomial.Admission.ofResult result index →
      Side.CCL.Admission.StateCache result.rfap.numeratorSites result.numeratorCCL index → IO Unit)
    (cached : Option (Eliminations.ccl (.nonzero result))) :
    polynomialAdmission result origins columns winding directory index count consume cached =
      polynomialAdmission result origins columns winding directory index count consume := by
  unfold polynomialAdmission
  rewrite [admissionStates_cached_eq_default]
  exact (rfl)

/-- Disabling retained output preserves the complete previous positive checkpoint action. -/
theorem positive_default {polynomial : CoefficientPolynomial}
    (input : FTA.Positive.Input.PositiveInput polynomial)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    positive input columns winding control directory request false =
      (do
        if higher : 2 ≤ polynomial.natDegree then
          let retainedInput : FTA.Squarefree.Input polynomial := ⟨input.squarefree, higher⟩
          let elimination := retainedInput.elimination
          let saved ← InitialExtractionCheckpoint.separatedLargeSquareWithElimination retainedInput elimination rfl
            columns winding control directory request
          return ⟨.higher (FTA.Squarefree.Build.BoxFTA.fromIsolation ⟨input.squarefree, higher⟩ saved.val) higher,
            FTA.Positive.Build.fromIsolation_eq_provePositive input higher saved.val
              (request := request) saved.property⟩
        else
          let same : polynomial.natDegree = 1 :=
            Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge higher))
              (Nat.succ_le_of_lt input.degreePositive)
          return ⟨FTA.Positive.Build.fromDegree input 1 same request,
            FTA.Positive.Build.fromDegree_eq_provePositive input 1 same request⟩) := (rfl)

/-- Disabling retained output preserves the complete previous observation checkpoint action. -/
theorem observation_default {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite) (context : Context.Basic.PositiveContext input.entries)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    observation input context columns winding control directory request false =
      (do
        let saved ← positive ⟨context.focus.part.squarefree, context.focus.degreePositive⟩
          columns winding control directory request
        return ⟨input.fromPositive context saved.val,
          input.fromPositive_eq_observe context saved.val (request := request) saved.property⟩) := (rfl)

/-- Disabling retained output preserves the complete previous ordered-observation action. -/
theorem observations_default {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (contexts : List (Context.Basic.PositiveContext input.entries)) (index : Nat)
    (request : Option Rational := none) :
    observations input columns winding control directory contexts index request false =
      (match contexts with
       | [] => pure ⟨PUnit.unit, rfl⟩
       | context :: contexts => do
           let first ← observation input context columns winding control
             (Purelib.System.FilePath.join directory (System.FilePath.mk s!"context-{index}")) request
           let tail ← observations input columns winding control directory contexts (index + 1) request
           return ⟨(first.val, tail.val),
             (congrArg (fun head => (head, tail.val)) first.property).trans
               (congrArg (fun remaining => (input.observe context request, remaining)) tail.property)⟩) := by
  cases contexts with
  | nil => exact (rfl)
  | cons => exact (rfl)

/-- Disabling retained output preserves the complete previous family checkpoint action. -/
theorem family_default {source opposite : CoefficientPolynomial}
    (input : PositiveSideInput source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    family input columns winding control directory request false =
      (do
        let saved ← observations input columns winding control directory input.contexts 0 request
        return ⟨input.fromObservations saved.val,
          input.fromObservations_eq_buildFamily saved.val (request := request) saved.property⟩) := (rfl)

/-- Disabling retained output preserves the complete previous side checkpoint action. -/
theorem side_default (source opposite : CoefficientPolynomial)
    (sourceNormalized : source.normalize = source) (sourceNonzero : source.isZero = false)
    (oppositeNonzero : opposite.isZero = false)
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    side source opposite sourceNormalized sourceNonzero oppositeNonzero coprime
      columns winding control directory request false =
      (Multiplicity.Side.Build.withInput source opposite sourceNormalized sourceNonzero oppositeNonzero coprime
          (fun degreeZero same => pure ⟨.constant sourceNonzero degreeZero oppositeNonzero,
            (Multiplicity.Side.Build.buildSide_eq_constant source opposite sourceNormalized sourceNonzero
              oppositeNonzero coprime degreeZero same request).symm⟩)
          (fun input same coprimeSame => do
            let saved ← family input columns winding control directory request
            return ⟨.positive input saved.val,
              (congrArg (Multiplicity.Side.Basic.SideResult.positive input) saved.property).trans
                (Multiplicity.Side.Build.buildSide_eq_positive source opposite sourceNormalized sourceNonzero
                  oppositeNonzero coprime input same coprimeSame request).symm⟩)) := (rfl)

/-- Disabling retained output preserves the complete previous quotient checkpoint action. -/
theorem quotient_default (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    quotient numerator denominator denominatorNonzero columns winding control directory request false =
      (ArgumentPrinciple.General.withInput numerator denominator denominatorNonzero
          (fun numeratorZero => pure ⟨.zeroNumerator numeratorZero denominatorNonzero,
            (ArgumentPrinciple.General.prove_eq_zero numerator denominator denominatorNonzero
              numeratorZero request).symm⟩)
          (fun numeratorNonzero input same => do
            let numeratorSites ← side input.reduction.numeratorReduced input.reduction.denominatorReduced
              input.reduction.numeratorReduced_normalized input.numeratorReducedNonzero input.denominatorReducedNonzero
              (Reduction.Basic.ReducedPair.coprime input.reduction) columns winding control
              (Purelib.System.FilePath.join directory "numerator") request
            let denominatorSites ← side input.reduction.denominatorReduced input.reduction.numeratorReduced
              input.reduction.denominatorReduced_normalized
              input.denominatorReducedNonzero input.numeratorReducedNonzero
              (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
                (Reduction.Basic.ReducedPair.coprime input.reduction))
              columns winding control (Purelib.System.FilePath.join directory "denominator") request
            return ⟨.nonzero
              (ArgumentPrinciple.General.NonzeroResult.fromSides input numeratorSites.val denominatorSites.val),
              (ArgumentPrinciple.General.prove_eq_nonzero numerator denominator denominatorNonzero numeratorNonzero
                input same (request := request) numeratorSites.val numeratorSites.property
                denominatorSites.val denominatorSites.property).symm⟩)) := (rfl)

/-- Disabling retained output preserves the complete previous ccl checkpoint action. -/
theorem ccl_default (numerator denominator : CoefficientPolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    ccl numerator denominator denominatorNonzero columns winding control directory request false =
      (do
        let saved ← quotient numerator denominator denominatorNonzero columns winding control directory request
        return ⟨CCL.Build.fromResult saved.val,
          CCL.Build.fromResult_eq_prove numerator denominator denominatorNonzero saved.val
            (request := request) saved.property⟩) := (rfl)

/-- Disabling retained output preserves the complete previous polynomial checkpoint action. -/
theorem polynomial_default (source : CoefficientPolynomial)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (request : Option Rational := none) :
    polynomial source columns winding control directory request false =
      (do
        match request with
        | none => pure ()
        | some width =>
            InitialExtractionCheckpoint.retainSturmRequest control directory "multiplicity-request.json"
              (Json.mkObj
                [("format", toJson "ccl-multiplicity-isolation-request-v1"),
                 ("factory", toJson "canonical-five-then-real-axis-event"),
                 ("polynomial", toJson (source.coeffs.map gaussianData)),
                 ("eventWidth", toJson (fractionData width))])
        ccl source Dense.Gaussian.Unit.unitDenominator Dense.Gaussian.Unit.unitDenominator_isZero
          columns winding control directory request) := (rfl)

end MultiplicityCheckpoint
