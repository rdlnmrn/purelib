module

import Purelib.System.IO.Reference

public import scripts.checkpoint.CoherentRootSamples
import scripts.checkpoint.InitialExtraction
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Separation
import Init.System.IO
import Purelib.RootIsolation.FTA.Squarefree.Preparation
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Approximation.Gaussian.Residual.Localization
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Riemann.RootContinuation.CoherentRoot.Localization
public import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.RootIsolation.Exact.Ownership.Replay
import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.RootIsolation.Newton.Restart.Seed.Track
public import Purelib.RootIsolation.Track.Newton.Canonical
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.System.FilePath
import Purelib.System.IO
meta import Purelib.Elab.ConstructiveInjectivity
-- This comparison API retains both complete original algebraic input owners.
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Union

/-! # Saved original localization and selected-root comparison requests -/

public section

namespace RootSelectionCheckpoint

open Purelib
open Purelib.RootIsolation
open Purelib.RootIsolation.Residual
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.Riemann.RootContinuation.CoherentRoot.Localization
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.RootIsolation.Newton.Restart
open Purelib.System.FilePath (join)

variable {polynomial : GaussianPolynomial} {input : FTA.Squarefree.Input polynomial}
  {source : Geometric.GeometricApproximation}

/-- The authentic coverage request whose particular source sample is localized. -/
abbrev Request (preparation : Preparation input source) (current : Nat) (target : Rational) :=
  Sequence.Selection.Coverage.Request preparation.coverage current target

/-- Error-preserving state for the actual retained root-family cache.

The original owner-indexed entries accompany successful results and original
loader failures, so both payments and the final reading share completed work. -/
abbrev Execution (preparation : Preparation input source) :=
  System.IO.StateExecution (CoherentRoot.StateCache.FamilyEntries preparation.boxes.isolation.tracks)

/-- Original-state readers indexed by the actual retained family owner and requested state index. -/
abbrev RootStates (preparation : Preparation input source) :=
  (owner : Fin preparation.boxes.isolation.tracks.length) → (index : Nat) →
    Execution preparation (CoherentRootCheckpoint.State (preparation.roots.get owner) index)

/-- The original anchored seed requested by one retained localization payment. -/
abbrev OriginalSeed (preparation : Preparation input source) {current : Nat} {target : Rational}
    (_request : Request preparation current target) :=
  Seed input.squarefree input.elimination
    (Global.Assignment.largeSquareProtectedAmbient input.degreePositive)

/-- The complete original assignment requested by a retained coverage sample. -/
abbrev Assigned (preparation : Preparation input source) {current : Nat} {target : Rational}
    (request : Request preparation current target) :=
  Global.Assignment.AssignedResult input (preparation.source.sample request.index)
    (Preparation.localizationRadius target) preparation.boxes.isolation

set_option genInjectivity false in
/-- An actual seed, its eight checked lines, and the original complete state and track. -/
structure SeedCache (preparation : Preparation input source) {current : Nat} {target : Rational}
    (request : Request preparation current target) where
  /-- The original sample's anchored seed, before any line construction. -/
  seed : OriginalSeed preparation request
  /-- This seed is the original localization request's seed. -/
  seed_eq : seed = Global.Assignment.insideSeed input input.elimination
    (preparation.source.sample request.index) (preparation.request_inside request)
    (Preparation.localizationRadius_positive target) (preparation.request_residualSmall request)
  /-- The exact original selected band used by all eight retained lines. -/
  band : Geometry.Rational.Box.Band.Basic.BandBox
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter polynomial seed.source) seed.radius
  /-- The supplied band is the actual seed's original band. -/
  band_eq : band = seed.band
  /-- Four original columns supply both current and ambient sides. -/
  lines : Newton.Band.Prepare.Lines input.elimination
    (Global.Assignment.largeSquareProtectedAmbient input.degreePositive).box
    (RootRadius.Box.largeSquareBox polynomial)
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter polynomial seed.source) seed.radiusPositive
  /-- The original winding-one state assembled from those actual retained lines. -/
  state : WindingOneState polynomial (RootRadius.Box.largeSquareBox polynomial)
  /-- The supplied state retains the complete original seed result. -/
  state_eq : state = seed.state input.degreeAtLeastTwo
  /-- The original track assembled from the supplied state. -/
  track : WindingOneTrack polynomial (RootRadius.Box.largeSquareBox polynomial)
  /-- The actual track retains the complete original seed track. -/
  track_eq : track = seed.track input.degreeAtLeastTwo

constructive_injectivity SeedCache

set_option genInjectivity false in
/-- A complete assignment and owner-side paid request retained before reading its nearby result. -/
structure Nearby (preparation : Preparation input source) {current : Nat} {target : Rational}
    (request : Request preparation current target) where
  /-- The actual restored seed, line, state and track operands. -/
  seed : SeedCache preparation request
  /-- The original complete assigned result on the same finite isolation. -/
  assigned : Assigned preparation request
  /-- The assignment is the original localization on these exact operands. -/
  assigned_eq : assigned = Global.Assignment.assignInsideUsing input preparation.boxes preparation.support
    (preparation.source.sample request.index) (preparation.request_inside request)
    (Preparation.localizationRadius_positive target) (preparation.request_residualSmall request)
  /-- The actual selected owner's original paid refinement. -/
  paid : Refinement (preparation.roots.get assigned.owner.owner) (max 0 1)
  /-- The owner payment retains all three literal quarter allocations. -/
  paid_eq : paid = Refinement.ofTarget (preparation.roots.get assigned.owner.owner) (max 0 1)
    (((target / 4) / 4) / 4)
    (Field.div_pos_direct (Field.div_pos_direct
      (Field.div_pos_direct request.positive (by decide)) (by decide)) (by decide))
  /-- The complete original nearby record returned from the retained payment. -/
  value : Sequence.Selection.Nearby preparation.candidates (preparation.source.sample request.index) target
  /-- The retained value is the exact localization of the original request. -/
  value_eq : value = request.locate

constructive_injectivity Nearby

set_option genInjectivity false in
/-- The original stable selection, with the complete retained anchor payment. -/
structure Anchor (preparation : Preparation input source) where
  /-- The exact initial source coverage request at one sixteenth of the original gap. -/
  request : Request preparation 0 (preparation.separated.gap / 16)
  /-- The actual seed, assignment and candidate payment used by this anchor. -/
  nearby : Nearby preparation request
  /-- The original complete fixed selection constructed from that same nearby record. -/
  selection : Preparation.Selection preparation
  /-- The retained selection is the original default fixed-root selection. -/
  selection_eq : selection = preparation.select

constructive_injectivity Anchor

set_option genInjectivity false in
/-- A particular independent-start comparison and both of its original localization payments. -/
structure Compared (preparation : Preparation input source) (left right : Nat) (target : Rational) where
  /-- The actual original preparation, including its complete source and root family. -/
  original : Preparation input source
  /-- The retained physical parent is the preparation used by this comparison. -/
  original_eq : original = preparation
  /-- The retained original anchor and its whole selection identity. -/
  anchor : Anchor preparation
  /-- The actual subsequent source request, preserving the original starts and allocations. -/
  request : Request preparation (max left anchor.selection.anchor.index)
    (min (preparation.separated.gap / 16) (target / 8))
  /-- The actual second localization and selected candidate payment. -/
  nearby : Nearby preparation request
  /-- The complete original independent-start comparison. -/
  value : Equivalence.Comparison source.toApproximation anchor.selection.root.approximation left right target
  /-- The retained value is this original selected-channel comparison request. -/
  value_eq : ∀ positive : 0 < target, value = anchor.selection.equivalent.compare left right target positive

constructive_injectivity Compared

set_option genInjectivity false in
/-- One exact saved subrequest, including all completed operands before its unmet frontier. -/
inductive Work (preparation : Preparation input source) : Type 1 where
  /-- Four original paired columns must supply the actual seed's eight lines. -/
  | seedLines {current target} (request : Request preparation current target)
      (seed : OriginalSeed preparation request)
      (band : Geometry.Rational.Box.Band.Basic.BandBox
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter polynomial seed.source) seed.radius)
      (sameBand : band = seed.band)
  /-- The actual localized track must be refined at this isolation's original assignment radius. -/
  | assignment {current target} (request : Request preparation current target)
      (seed : SeedCache preparation request)
      (radius : { value : Rational // value = Exact.Ownership.Radius.assignmentRadius polynomial
        (RootRadius.Box.largeSquareBox polynomial) preparation.boxes.isolation })
  /-- The selected original candidate must pay its original nearby-comparison request. -/
  | owner {current target} (request : Request preparation current target)
      (seed : SeedCache preparation request) (assigned : Assigned preparation request)
      (diagnosticDirectory : System.FilePath)
  /-- A subsequent comparison keeps the complete already restored anchor and earlier payments. -/
  | comparison (anchor : Anchor preparation) (pending : Work preparation)
  /-- The actual returned right index requires its original selected root's checked cache state. -/
  | reading {left right target} (comparison : Compared preparation left right target)

constructive_injectivity Work

set_option genInjectivity false in
/-- An unfulfilled saved request with its original preparation, exact operands and loader failure.

Absent and rejected saved artifacts both leave this request unresolved. The
retained loader error distinguishes their execution failures; neither branch
asserts invalidity of the polynomial or a mathematical obstruction.
-/
structure Stopped (preparation : Preparation input source) where
  /-- Retain the actual original preparation, including its complete root family. -/
  original : Preparation input source
  /-- The physical parent is the same preparation used by the pending request. -/
  original_eq : original = preparation
  /-- The exact numerical subrequest that could not be restored. -/
  work : Work preparation
  /-- The numerical request directory; owner work separately retains its diagnostic directory. -/
  directory : System.FilePath
  /-- The original checkpoint loader's failure, without reclassification as a theorem. -/
  cause : IO.Error

constructive_injectivity Stopped

/-- Capture one existing loader result without changing its absence or rejection behavior. -/
private def capture {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]
    {α : Type} (action : m α) : m (Except IO.Error α) := do
  try return .ok (← action)
  catch error => return .error error

set_option genInjectivity false in
/-- An unresolved original complete-isolation request, before any localization or selected-root payment. -/
structure IsolationStopped (input : FTA.Squarefree.Input polynomial) where
  /-- The actual original coefficient input, including its finite squarefree data. -/
  original : FTA.Squarefree.Input polynomial
  /-- The retained parent is the original requested input. -/
  original_eq : original = input
  /-- The original complete-isolation request directory. -/
  directory : System.FilePath
  /-- The original saved loader's absence or rejection reason. -/
  cause : IO.Error

constructive_injectivity IsolationStopped

/-- Restore the original coefficient isolation with one unchanged checkpoint-production policy. -/
def isolation (input : FTA.Squarefree.Input polynomial) (savedOnly : Bool) (directory : System.FilePath) :
    IO (Except (IsolationStopped input)
      { value : Exact.Basic.Output polynomial (RootRadius.Box.largeSquareBox polynomial)
        polynomial.natDegree // value = input.isolation }) := do
  let result ← capture <| InitialExtractionCheckpoint.separatedLargeSquare input
    { savedOnly := savedOnly } { savedOnly := savedOnly }
    (← RootRefinementCheckpoint.Control.create savedOnly) directory
  match result with
  | .ok saved => return .ok saved
  | .error error => return .error ⟨input, rfl, directory, error⟩

/-- Read the original unresolved numerical phase without classifying it as mathematical invalidity. -/
def Work.phase {preparation : Preparation input source} : Work preparation → String
  | .seedLines .. => "original localization seed's eight lines"
  | .assignment .. => "original assignment-radius owner refinement"
  | .owner .. => "original selected-candidate nearby payment"
  | .comparison _ pending => "particular comparison: " ++ pending.phase
  | .reading .. => "actual returned-index original root sample"

/-- Restore one original coverage localization with separate preparation and root-payment policies.

The seed's four paired columns and assignment-radius refinement may produce
their distinct original requests. The selected candidate's paid refinement
consumes its supplied original family reader. Numerical prefix and per-payment
diagnostics have distinct directories. The continuation receives the complete
retained nearby record or the first typed pending request with earlier operands.
-/
def nearby {α : Type} (preparation : Preparation input source)
    (boxes_eq : preparation.boxes = FTA.Squarefree.Build.BoxFTA.fromIsolation input preparation.boxes.isolation)
    (states : RootStates preparation) (prefixDirectory : System.FilePath)
    {current : Nat} {target : Rational} (request : Request preparation current target)
    (preparationSavedOnly : Bool) (directory rootDirectory : System.FilePath)
    (use : Except (Stopped preparation) (Nearby preparation request) → Execution preparation α) :
    Execution preparation α := do
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
  let winding : WindingCheckpoint.Control IO := { savedOnly := preparationSavedOnly }
  let sample := preparation.source.sample request.index
  let seed := Global.Assignment.insideSeed input input.elimination sample
    (preparation.request_inside request) (Preparation.localizationRadius_positive target)
    (preparation.request_residualSmall request)
  let band := seed.band
  let restored ← capture <| RawSubdivisionCheckpoint.bandLinesFromBand polynomial input.nonzero input.degreePositive
    input.elimination rfl rfl columns (join directory "seed-band")
    (Global.Assignment.largeSquareProtectedAmbient input.degreePositive).box
    (RootRadius.Box.largeSquareBox polynomial)
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter polynomial seed.source) seed.radiusPositive band rfl
  match restored with
  | .error error =>
      use (.error ⟨preparation, rfl, .seedLines request seed band rfl, join directory "seed-band", error⟩)
  | .ok lines =>
      let state := seed.stateFromLines input.degreeAtLeastTwo band rfl lines
      have state_eq := seed.stateFromLines_eq input.degreeAtLeastTwo band rfl lines
      let track := seed.trackFromState input.degreeAtLeastTwo state state_eq
      have track_eq := seed.trackFromState_eq input.degreeAtLeastTwo state state_eq
      let cached : SeedCache preparation request := ⟨seed, rfl, band, rfl, lines, state, state_eq, track, track_eq⟩
      let radius := Exact.Ownership.Radius.assignmentRadius polynomial
        (RootRadius.Box.largeSquareBox polynomial) preparation.boxes.isolation
      have radiusPositive := Exact.Ownership.Radius.assignmentRadius_pos polynomial
        (RootRadius.Box.largeSquareBox polynomial) preparation.boxes.isolation
      let loader := RootRefinementCheckpoint.ClearanceLoader.separated columns polynomial input.nonzero
        input.degreePositive
      let restored ← capture <| RawSubdivisionCheckpoint.refine input input.elimination rfl loader columns winding
        (join directory "assignment") state radius radiusPositive
      match restored with
      | .error error =>
          use (.error ⟨preparation, rfl, .assignment request cached ⟨radius, rfl⟩,
            join directory "assignment", error⟩)
      | .ok saved =>
          have trackCanonical : Track.Newton.Canonical input.degreeAtLeastTwo input.squarefree
              input.elimination track := by
            have original : Track.Newton.Canonical input.degreeAtLeastTwo input.squarefree input.elimination
                (seed.track input.degreeAtLeastTwo) := by
              intro current epsilon positive
              rfl
            exact (congrArg (fun track => Track.Newton.Canonical input.degreeAtLeastTwo input.squarefree
              input.elimination track) track_eq).mpr original
          have initial_eq := seed.trackFromState_initial input.degreeAtLeastTwo state state_eq
          let refined : Exact.Ownership.Replay.Refined preparation.boxes.isolation track :=
            ⟨saved.val, saved.property.trans ((trackCanonical state radius radiusPositive).symm.trans
              (congrArg (fun state => track.refine state radius radiusPositive) initial_eq.symm))⟩
          have supported := preparation.support.symm ▸ track.initial.refinesAmbient
          let owner := Exact.Ownership.Replay.restore input.degreeAtLeastTwo input.squarefree input.elimination
            preparation.boxes.isolation track supported refined
          have ownership : ∀ (track : WindingOneTrack polynomial
              (RootRadius.Box.largeSquareBox polynomial))
              (supported : track.initial.box.Refines preparation.boxes.isolation.support),
              preparation.boxes.ownership track supported = Exact.Ownership.Prepare.selectOutputOwner
                input.degreeAtLeastTwo input.squarefree input.elimination preparation.boxes.isolation
                  track supported := by
            let Claim := fun boxes : FTA.Squarefree.BoxResult polynomial =>
              ∀ (track : WindingOneTrack polynomial (RootRadius.Box.largeSquareBox polynomial))
                (supported : track.initial.box.Refines boxes.isolation.support),
                boxes.ownership track supported = Exact.Ownership.Prepare.selectOutputOwner
                  input.degreeAtLeastTwo input.squarefree input.elimination boxes.isolation track supported
            have original : Claim (FTA.Squarefree.Build.BoxFTA.fromIsolation input preparation.boxes.isolation) := by
              intro track supported
              rfl
            exact (congrArg Claim boxes_eq.symm).mp original
          have owner_eq : owner = preparation.boxes.ownership track supported :=
            (Exact.Ownership.Replay.restore_eq input.degreeAtLeastTwo input.squarefree input.elimination
              preparation.boxes.isolation track supported refined).trans (ownership track supported).symm
          let assigned := Global.Assignment.assignInsideFromCaches input input.elimination preparation.boxes
            preparation.support sample (preparation.request_inside request)
            (Preparation.localizationRadius_positive target)
            (preparation.request_residualSmall request) seed rfl state state_eq track track_eq owner owner_eq
          have assigned_eq := Global.Assignment.assignInsideFromCaches_eq_using input preparation.boxes
            preparation.support sample (preparation.request_inside request)
            (Preparation.localizationRadius_positive target)
            (preparation.request_residualSmall request) seed rfl state state_eq track track_eq owner owner_eq
          let root := preparation.roots.get assigned.owner.owner
          have positive := Field.div_pos_direct
            (Field.div_pos_direct
              (Field.div_pos_direct request.positive (by decide)) (by decide)) (by decide)
          let paid ← capture <| CoherentRootCheckpoint.ofTargetWithStates root
            (states assigned.owner.owner) rootDirectory
            (max 0 1) (((target / 4) / 4) / 4) positive
          match paid with
          | .error error =>
              use (.error ⟨preparation, rfl, .owner request cached assigned rootDirectory, prefixDirectory, error⟩)
          | .ok paid =>
              let value := Assignment.nearbyFromOwnerPaid input preparation.boxes.isolation preparation.roots sample
                request.positive (Preparation.localizationRadius_small request.positive) assigned paid.val paid.property
              have value_eq := Assignment.nearbyFromOwnerPaid_eq input preparation.boxes.isolation
                preparation.roots sample
                request.positive (Preparation.localizationRadius_small request.positive) assigned paid.val paid.property
              have original : value = request.locate := value_eq.trans
                ((congrArg (fun assigned => Assignment.nearby input preparation.boxes.isolation preparation.roots sample
                  request.positive (Preparation.localizationRadius_small request.positive) assigned) assigned_eq).trans
                  (preparation.request_locate_eq request).symm)
              use (.ok ⟨cached, assigned, assigned_eq, paid.val, paid.property, value, original⟩)

set_option genInjectivity false in
/-- A checked original sample at the actual returned comparison index, retaining all original parents. -/
structure Observed (preparation : Preparation input source) (left right : Nat) (target : Rational) where
  /-- Retain the physical original preparation and its complete root family. -/
  original : Preparation input source
  /-- The physical retained parent is the original preparation used by this observation. -/
  original_eq : original = preparation
  /-- Both actual localizations, the stable selection and this original particular comparison. -/
  comparison : Compared preparation left right target
  /-- The checked original root state at the comparison's actual returned right index. -/
  state : CoherentRootCheckpoint.State comparison.anchor.selection.root comparison.value.rightIndex
  /-- The actual anchor read from that same retained state. -/
  reading : Data.Gaussian.Basic.Canonical
  /-- The original sample is exactly this reading at the actual returned right index. -/
  reading_eq : reading = comparison.anchor.selection.root.approximation.sample comparison.value.rightIndex

constructive_injectivity Observed

/-- Restore the full original selection and comparison without accessing a final sample store.

Anchor and particular-comparison localization have separate numerical request
directories. Preparation policy controls only their seed-band and assignment
requests; both candidate-owner payments consume the same supplied original
family readers. The complete comparison retains the preparation and payments.
-/
def compare {α : Type} (preparation : Preparation input source)
    (boxes_eq : preparation.boxes = FTA.Squarefree.Build.BoxFTA.fromIsolation input preparation.boxes.isolation)
    (states : RootStates preparation) (prefixDirectory : System.FilePath)
    (left right : Nat) (target : Rational) (positive : 0 < target)
    (preparationSavedOnly : Bool) (directory : System.FilePath)
    (use : Except (Stopped preparation) (Compared preparation left right target) → Execution preparation α) :
    Execution preparation α := do
  have anchorPositive := Field.div_pos_direct preparation.separated.positive
    (by decide : (0 : Rational) < 16)
  let request := preparation.coverage.request 0 (preparation.separated.gap / 16) anchorPositive
  nearby preparation boxes_eq states prefixDirectory request preparationSavedOnly (join directory "anchor")
    (join directory "anchor/owner") fun result => do
    match result with
    | .error missing => use (.error missing)
    | .ok first =>
        let originalAnchor := Sequence.Selection.Anchor.ofNearby preparation.source.toApproximation
          preparation.separated preparation.coverage request ⟨first.value, first.value_eq⟩
        let selection : Preparation.Selection preparation := ⟨originalAnchor⟩
        have selection_eq : selection = preparation.select :=
          (congrArg Preparation.Selection.mk (Sequence.Selection.Anchor.ofNearby_eq
            preparation.source.toApproximation preparation.separated preparation.coverage request
              ⟨first.value, first.value_eq⟩)).trans preparation.select_eq.symm
        let anchor : Anchor preparation := ⟨request, first, selection, selection_eq⟩
        have requestPositive := Data.Rat.Fraction.Order.Basic.lt_min anchorPositive
          (Field.div_pos_direct positive (by decide : (0 : Rational) < 8))
        let request := preparation.coverage.request (max left selection.anchor.index)
          (min (preparation.separated.gap / 16) (target / 8)) requestPositive
        nearby preparation boxes_eq states prefixDirectory request preparationSavedOnly (join directory "comparison")
          (join directory "comparison/owner")
          fun result => do
            match result with
            | .error missing => use (.error { missing with work := .comparison anchor missing.work })
            | .ok second =>
                let value := selection.compareFromNearby left right target positive request
                  ⟨second.value, second.value_eq⟩
                have value_eq : ∀ positive : 0 < target,
                    value = selection.equivalent.compare left right target positive := by
                  intro positive
                  exact selection.compareFromNearby_eq left right target positive request
                    ⟨second.value, second.value_eq⟩
                use (.ok ⟨preparation, rfl, anchor, request, second, value, value_eq⟩)

/-- Restore the full original comparison and returned-index sample through supplied original-state readers.

Every preparation loader is saved-only. Both root payments and the final sample
consume the same supplied original family readers; their I/O policy belongs to
the caller. The sample uses the actual returned index; failure retains the
complete comparison.
-/
def observe {α : Type} (preparation : Preparation input source)
    (boxes_eq : preparation.boxes = FTA.Squarefree.Build.BoxFTA.fromIsolation input preparation.boxes.isolation)
    (states : RootStates preparation) (prefixDirectory : System.FilePath)
    (left right : Nat) (target : Rational) (positive : 0 < target)
    (directory : System.FilePath)
    (use : Except (Stopped preparation) (Observed preparation left right target) → Execution preparation α) :
    Execution preparation α := do
  compare preparation boxes_eq states prefixDirectory left right target positive true directory fun result => do
    match result with
    | .error missing => use (.error missing)
    | .ok comparison =>
        let selection := comparison.anchor.selection
        let restored ← capture <| states selection.anchor.nearby.owner comparison.value.rightIndex
        match restored with
        | .error error => use (.error ⟨preparation, rfl, .reading comparison, prefixDirectory, error⟩)
        | .ok state =>
            let reading := state.val.box.anchor
            have reading_eq : reading = selection.root.approximation.sample comparison.value.rightIndex := by
              have anchor := congrArg (fun state => state.box.anchor)
                (state.property.trans (selection.root.stateAt_eq comparison.value.rightIndex))
              have sample := congrArg (fun approximation : Sequence.ApproximationData =>
                approximation.sample comparison.value.rightIndex) selection.root.approximation_eq
              exact anchor.trans (sample.trans (CoherentRoot.approximation_sample _ _)).symm
            use (.ok ⟨preparation, rfl, comparison, state, reading, reading_eq⟩)

namespace Multiplicity

open Purelib.Polynomial.Approximation.Gaussian.Localization
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
  (PositiveEntry positiveEntries unitValue CoprimePairs)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.RootIsolation.Residual.Multiplicity (Factor Family)
open Purelib.Approximation.Rational.SquareRoot.Radius
open CoherentRoot.Multiplicity (Realization)
open CoherentRoot.Multiplicity renaming Family -> RootFamily
open Purelib.Data.List (DependentProduct)

/-- The existing exact-state entry container belonging to one original factor. -/
private def FactorEntries {entry : PositiveEntry} : Factor entry → Type
  | .linear .. => Unit
  | .higher _ preparation => StateCache.FamilyEntries preparation.boxes.isolation.tracks

/-- Retain each actual original root's initial entry in its existing owner-indexed container. -/
private def initialFactorEntries {entry : PositiveEntry} {factor : Factor entry}
    (roots : Realization factor) : FactorEntries factor :=
  match factor, roots with
  | .linear .., .linear .. => ()
  | .higher .., .higher family => StateCache.FamilyEntries.initial family

/-- A product of the existing factor caches at the original bounded factor occurrences. -/
private abbrev StateEntries {entries : List PositiveEntry} (factors : Family entries) :=
  DependentProduct entries (fun index => FactorEntries (factors.get index))

/-- Initialize the actual head-factor cache and literal retained tail without rebuilding root realizations.

Recursion consumes the retained head realization and its original tail. Each
stored cell keeps the same bounded factor occurrence and original track family.
-/
private def initialEntries : {entries : List PositiveEntry} → {factors : Family entries} →
    (roots : RootFamily factors) → StateEntries factors
  | [], .nil, .nil => PUnit.unit
  | _ :: _, .cons _ _, .cons roots remaining => (initialFactorEntries roots, initialEntries remaining)

/-- Read this original factor's states through its existing cache accessors and prepared-axis policy.

The factor's defining equality authenticates its retained prepared family and
original refinement policy. Cache writes carry that same entry container with
only the requested owner's cell replaced.
-/
private def factorStateReaders {entry : PositiveEntry} (factor : Factor entry)
    (original : factor = Factor.ofEntry entry) (roots : Realization factor)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (readFactor : IO (FactorEntries factor))
    (writeFactor : FactorEntries factor → IO Unit) : Realization.StateReaders IO roots := by
  cases factor with
  | linear degree data inverse inverseEq =>
      cases roots with
      | linear value valueEq geometric geometricEq => exact PUnit.unit
  | higher degree preparation =>
      cases roots with
      | higher roots => exact fun owner index => do
          let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, degree⟩
          have preparationEq := Factor.higher_preparation_eq entry degree preparation original
          let track := preparation.boxes.isolation.tracks.get owner
          let root := roots.get owner
          have origin := preparation.track_origin preparationEq track
            (List.get_mem preparation.boxes.isolation.tracks owner)
          have canonical : ∀ current epsilon positive, track.refine current epsilon positive =
              Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
                (preparation.axis.certificate input.nonzero input.degreePositive) current epsilon positive := by
            intro current epsilon positive
            exact (origin.refine current epsilon positive).trans
              (congrArg (fun certificate => Track.Newton.Refinement.refineState input.degreeAtLeastTwo
                input.squarefree certificate current epsilon positive) preparation.elimination_eq)
          let readEntries : IO (List (StateCache.Entry track)) := do
            return (← readFactor).get owner
          let writeEntries : List (StateCache.Entry track) → IO Unit := fun values => do
            let retained ← readFactor
            writeFactor (retained.set owner values)
          CoherentRootCheckpoint.readPreparedState root input preparation.axis canonical columns winding
            (join directory s!"owner-{owner.val}") readEntries writeEntries index

/-- Share one actual retained entry bank across all original factor and root state readers.

The existing dependent occurrence product stores each factor's existing
owner-indexed entry container. Reads and updates preserve their original
bounded indices and every other cell. All table entries and later owner
payments can consume these same readers, including after a loader failure.
-/
def stateReaders {entries : List PositiveEntry} {factors : Family entries} (roots : RootFamily factors)
    (original : ∀ index, factors.get index = Factor.ofEntry (entries.get index))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : IO (RootFamily.StateReaders IO roots) := do
  let retained ← System.IO.mkRef (initialEntries roots)
  return fun index =>
    let factor := factors.get index
    let readFactor : IO (FactorEntries factor) := do
      return DependentProduct.get entries (← System.IO.Ref.get retained) index
    let writeFactor : FactorEntries factor → IO Unit := fun values => do
      System.IO.Ref.modify retained fun bank => DependentProduct.replace entries bank index values
    factorStateReaders factor (original index) (roots.get index) columns winding
      (join directory s!"factor-{index.val}") readFactor writeFactor

/-- Restore one original factor preparation without changing its exact linear or nonlinear branch.

Linear entries keep the original coefficient constructor. Nonlinear entries
restore their own complete prepared-axis family through the existing column
and winding stores, with equality to the original factor constructor. -/
def factor (entry : PositiveEntry)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    IO {value : Factor entry // value = Factor.ofEntry entry} := do
  if degree : entry.part.polynomial.natDegree = 1 then
    return ⟨Factor.ofEntry entry, rfl⟩
  else
    have higher : 2 ≤ entry.part.polynomial.natDegree := by
      have positive := entry.degreePositive
      omega0
    let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, higher⟩
    let saved ← InitialExtractionCheckpoint.preparedFamily input columns winding control directory
    return ⟨.higher higher saved.val,
      (congrArg (Factor.higher higher) saved.property).trans (Factor.ofEntry_higher entry higher).symm⟩

/-- Restore the same ordered original factor spine, retaining each complete head and tail cache.

Each factor has its own numerical request directory. Extending or retrying the
family consumes the completed column and winding checkpoints of earlier
entries rather than invoking their original isolation producers again. -/
def factors (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    (entries : List PositiveEntry) → (index : Nat) →
      IO {value : Family entries // value = Family.ofEntries entries}
  | [], _ => pure ⟨.nil, Family.ofEntries_nil.symm⟩
  | entry :: tail, index => do
      let head ← factor entry columns winding control (join directory s!"factor-{index}")
      let remaining ← factors columns winding control directory tail (index + 1)
      let result := Family.cons head.val remaining.val
      have same : result = Family.cons (Factor.ofEntry entry) (Family.ofEntries tail) :=
        congrArg₂ Residual.Multiplicity.Family.cons head.property remaining.property
      return ⟨result, same.trans (Family.ofEntries_cons entry tail).symm⟩

/-- Prepare the actual original residual source using restored factor families and their original coherent roots.

Coefficient decomposition is computed by its shared library owner once. The
retained ordered factors supply the complete original preparation, preserving
its source, residual scale, root programs, multiplicities and owner identities. -/
def prepare {α : Type} {polynomial : GaussianPolynomial} {channel : Name.Coherent.CoherentNamed}
    (residual : Polynomial.Approximation.Gaussian.Residual polynomial channel)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : {value : Preparation polynomial residual.source // value = residual.prepareLocalization} → IO α) :
    IO α := do
  let decomposition := Preparation.decompose polynomial residual.degreePositive
  let basis := decomposition.multiplicityBasis
  let entries := positiveEntries basis.entries
  let saved ← factors columns winding control directory entries 0
  let unit := normSq (unitValue basis.entries)
  let retained := Residual.Multiplicity.Preparation.ofFamily decomposition entries rfl saved.val unit rfl
  have retainedEq : retained = Residual.Multiplicity.Preparation.ofDecomposition decomposition :=
    Residual.Multiplicity.Preparation.ofFamily_eq_ofDecomposition decomposition entries rfl
      saved.val unit rfl saved.property
  let result := Preparation.ofFactors polynomial decomposition residual.source residual.scale
    residual.scale_nonnegative residual.bound retained
  use ⟨result, Preparation.ofFactors_eq_ofResidual polynomial residual.degreePositive decomposition rfl
    residual.source residual.scale residual.scale_nonnegative residual.bound retained retainedEq⟩

/-- Restore the complete original prepared-family inside assignment from its actual saved numerical work.

The original anchored seed retains its sample and requested radius. Four
paired columns supply its eight lines; its same track is refined at the
original partition ownership radius. The exact original deterministic owner
and all assignment fields are retained on the original isolation family. -/
def assignment {polynomial : GaussianPolynomial} (input : FTA.Squarefree.Input polynomial)
    (preparation : FTA.Squarefree.Preparation input)
    (same : preparation = FTA.Squarefree.Preparation.ofInput input)
    (sample : Data.Gaussian.Basic.Canonical)
    (inside : (RootRadius.Box.largeSquareBox polynomial).Contains sample)
    {epsilon : Rational} (positive : 0 < epsilon)
    (small : Data.Gaussian.Norm.Basic.normSq (polynomial.eval sample) <
      Global.Assignment.insideResidualTarget input epsilon)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) :
    IO {value : Global.Assignment.AssignedResult input sample epsilon preparation.boxes.isolation //
      value = Global.Assignment.assignInsideWithElimination input preparation.elimination preparation.boxes
        preparation.support sample inside positive small} := do
  let elimination := preparation.axis.certificate input.nonzero input.degreePositive
  let seed := Global.Assignment.insideSeed input elimination sample inside positive small
  let band := seed.band
  let lines ← RawSubdivisionCheckpoint.bandLinesPrepared polynomial preparation.axis input.nonzero input.degreePositive
    columns (join directory "seed-band")
    (Global.Assignment.largeSquareProtectedAmbient input.degreePositive).box
    (RootRadius.Box.largeSquareBox polynomial)
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter polynomial seed.source) seed.radiusPositive band rfl
  let state := seed.stateFromLines input.degreeAtLeastTwo band rfl lines
  have stateEq := seed.stateFromLines_eq input.degreeAtLeastTwo band rfl lines
  let track := seed.trackFromState input.degreeAtLeastTwo state stateEq
  have trackEq := seed.trackFromState_eq input.degreeAtLeastTwo state stateEq
  have initialEq := seed.trackFromState_initial input.degreeAtLeastTwo state stateEq
  let radius := Exact.Ownership.Radius.assignmentRadius polynomial
    (RootRadius.Box.largeSquareBox polynomial) preparation.boxes.isolation
  have radiusPositive := Exact.Ownership.Radius.assignmentRadius_pos polynomial
    (RootRadius.Box.largeSquareBox polynomial) preparation.boxes.isolation
  let saved ← RawSubdivisionCheckpoint.refinePrepared input preparation.axis columns winding
    (join directory "assignment") state radius radiusPositive
  have canonical : track.refine state radius radiusPositive =
      Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree elimination
        state radius radiusPositive :=
    (congrArg (fun track => track.refine state radius radiusPositive) trackEq).trans (by rfl)
  let refined : Exact.Ownership.Replay.Refined preparation.boxes.isolation track :=
    ⟨saved.val, saved.property.trans (canonical.symm.trans
      (congrArg (fun current => track.refine current radius radiusPositive) initialEq.symm))⟩
  have supported := preparation.support.symm ▸ track.initial.refinesAmbient
  let owner := Exact.Ownership.Replay.restore input.degreeAtLeastTwo input.squarefree elimination
    preparation.boxes.isolation track supported refined
  have ownership : preparation.boxes.ownership track supported =
      Exact.Ownership.Prepare.selectOutputOwner input.degreeAtLeastTwo input.squarefree elimination
        preparation.boxes.isolation track supported :=
    (preparation.ownership_eq same track supported).trans
      (congrArg (fun certificate => Exact.Ownership.Prepare.selectOutputOwner input.degreeAtLeastTwo input.squarefree
        certificate preparation.boxes.isolation track supported) preparation.elimination_eq)
  have ownerEq : owner = preparation.boxes.ownership track supported :=
    (Exact.Ownership.Replay.restore_eq input.degreeAtLeastTwo input.squarefree elimination
      preparation.boxes.isolation track supported refined).trans ownership.symm
  let value := Global.Assignment.assignInsideFromCaches input elimination preparation.boxes preparation.support
    sample inside positive small seed rfl state stateEq track trackEq owner ownerEq
  return ⟨value,
    (Global.Assignment.assignInsideFromCaches_eq input elimination preparation.boxes preparation.support
      sample inside positive small seed rfl state stateEq track trackEq owner ownerEq).trans
      (congrArg (fun certificate => Global.Assignment.assignInsideWithElimination input certificate
        preparation.boxes preparation.support sample inside positive small) preparation.elimination_eq.symm)⟩

/-- Restore the actual original selected factor's locator through its prepared assignment checkpoints.

The exact linear branch keeps its original scalar proof. A higher branch
retains the original complete preparation and consumes the restored original
inside assignment, without running an uncheckpointed root locator. -/
def localizeFactor {entry : PositiveEntry} (factor : Factor entry) (original : factor = Factor.ofEntry entry)
    (sample : Data.Gaussian.Basic.Canonical) {epsilon : Rational} (positive : 0 < epsilon)
    (small : normSq (entry.part.polynomial.eval sample) < factor.threshold epsilon)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) :
    IO {value : Factor.Localized factor sample epsilon // value = factor.localize sample positive small} := by
  cases factor with
  | linear degree data inverse inverseEq => exact pure ⟨_, rfl⟩
  | higher degree preparation => exact do
      have preparationEq := Factor.higher_preparation_eq entry degree preparation original
      have inside := Factor.higher_contains degree preparation sample small
      let saved ← assignment ⟨entry.part.squarefree, degree⟩ preparation preparationEq sample inside positive
        (small.trans_le (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)) columns winding directory
      return ⟨.higher saved.val, (congrArg Factor.Localized.higher saved.property).trans
        (Factor.localize_higher_eq degree preparation sample positive small inside).symm⟩

/-- Restore the original nearby reading of one retained factor's coherent roots using its actual owner payment.

The selected root retains its same original track, prepared refinement policy,
maximum-one starting floor and three quarter allocations. Its retained state
reader consumes completed predecessors and returns the entire original
nearby certificate, including the actual owner and paid sample index. A
supplied shared reader retains the same state bank used by other requests. -/
def nearbyFactor {entry : PositiveEntry} (factor : Factor entry) (original : factor = Factor.ofEntry entry)
    (roots : CoherentRoot.Multiplicity.Realization factor) (sample : Data.Gaussian.Basic.Canonical)
    {epsilon target : Rational} (positive : 0 < target) (small : epsilon ^ 2 < target / 128)
    (localized : Factor.Localized factor sample epsilon)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (states : Option (Realization.StateReaders IO roots) := none) :
    IO {value : Sequence.Selection.Nearby roots.approximation sample target //
      value = roots.nearby sample positive small localized} := by
  cases factor with
  | linear degree data inverse inverseEq => exact pure ⟨_, rfl⟩
  | higher degree preparation =>
      cases roots with
      | higher roots =>
          cases localized with
          | higher assigned => exact do
              let input : FTA.Squarefree.Input entry.part.polynomial := ⟨entry.part.squarefree, degree⟩
              have preparationEq := Factor.higher_preparation_eq entry degree preparation original
              let track := preparation.boxes.isolation.tracks.get assigned.owner.owner
              let root := roots.get assigned.owner.owner
              have origin := preparation.track_origin preparationEq track
                (List.get_mem preparation.boxes.isolation.tracks assigned.owner.owner)
              have canonical : ∀ current epsilon positive, track.refine current epsilon positive =
                  Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree
                    (preparation.axis.certificate input.nonzero input.degreePositive) current epsilon positive := by
                intro current epsilon positive
                exact (origin.refine current epsilon positive).trans
                  (congrArg (fun certificate => Track.Newton.Refinement.refineState input.degreeAtLeastTwo
                    input.squarefree certificate current epsilon positive) preparation.elimination_eq)
              let states ← match states with
                | some shared => pure (shared assigned.owner.owner)
                | none =>
                    CoherentRootCheckpoint.preparedStateReader root input preparation.axis canonical
                      columns winding (join directory s!"owner-{assigned.owner.owner.val}")
              have targetPositive := Field.div_pos_direct
                (Field.div_pos_direct (Field.div_pos_direct positive (by decide)) (by decide)) (by decide)
              let paid ← CoherentRootCheckpoint.ofTargetWithStates root states (join directory "owner-payment")
                (max 0 1) (((target / 4) / 4) / 4) targetPositive
              let value := Assignment.nearbyFromOwnerPaid input preparation.boxes.isolation roots sample
                positive small assigned paid.val paid.property
              return ⟨value,
                (Assignment.nearbyFromOwnerPaid_eq input preparation.boxes.isolation roots sample
                  positive small assigned paid.val paid.property).trans
                  (CoherentRoot.Multiplicity.Realization.nearby_higher_eq (entry := entry)
                    roots sample positive small assigned).symm⟩

/-- Restore one complete original multiplicity coverage locator from an authenticated source observation.

The same original finite factor scan is computed once. Its selected factor,
complete prepared assignment, actual owner payment and family embedding are
retained, with equality to the original requested locator and no replacement
root, changed radius or altered starting floor. An optional shared state bank
supplies the same selected owner's original refinement states. -/
def nearbyPrepared {polynomial : GaussianPolynomial} {channel : Name.Coherent.CoherentNamed}
    (residual : Polynomial.Approximation.Gaussian.Residual polynomial channel)
    (preparation : Preparation polynomial residual.source) (original : preparation = residual.prepareLocalization)
    {current : Nat} {target : Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target)
    (samples : (index : Nat) → IO {value : Data.Gaussian.Basic.Canonical //
      value = preparation.source.sample index})
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) (states : Option (RootFamily.StateReaders IO preparation.roots) := none) :
    IO {value : Sequence.Selection.Nearby preparation.roots.candidates
      (preparation.source.sample request.index) target // value = request.locate} := do
  let sample ← samples request.index
  let epsilon := Dyadic.Geometric.dyadicSquareRadius (target / 128)
  have epsilonPositive := Dyadic.Geometric.dyadicSquareRadius_positive (target / 128)
  have radiusSmall := Dyadic.Geometric.dyadicSquareRadius_sq_lt
    (Field.div_pos_direct request.positive
      (Purelib.Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide)))
  have small : normSq (polynomial.normalize.eval sample.val) < preparation.factors.threshold epsilon := by
    rewrite [sample.property]
    exact preparation.request_residualSmall request
  let selected := preparation.factors.selectFactor sample.val epsilonPositive small
  let factor := preparation.factors.factors.get selected.index
  have factorEq := Preparation.factor_eq_ofResidual polynomial residual.degreePositive residual.source residual.scale
    residual.scale_nonnegative residual.bound preparation original selected.index
  let localized ← localizeFactor factor factorEq sample.val epsilonPositive
    (selected.residualSmall.trans_le (preparation.factors.factors.threshold_le_get selected.index epsilon))
    columns winding (join directory s!"factor-{selected.index.val}")
  let complete := preparation.factors.localizeFromFactor sample.val epsilonPositive small selected rfl
    localized.val localized.property
  let nearby ← nearbyFactor factor factorEq (preparation.roots.get selected.index) sample.val request.positive
    radiusSmall localized.val columns winding (join directory s!"factor-{selected.index.val}")
    (states.map (fun readers => readers selected.index))
  let embedded := CoherentRoot.Multiplicity.Family.nearbyFromFactor preparation.roots selected.index sample.val
    request.positive radiusSmall localized.val nearby.val nearby.property
  have completeEq := congrArg (fun result : Residual.Multiplicity.Preparation.Localization
      preparation.factors sample.val epsilon =>
    preparation.roots.nearby result.selected.index sample.val request.positive radiusSmall result.localized)
      complete.property
  return preparation.nearbyFromLocalized request sample embedded.val (embedded.property.trans completeEq)

/-- Read one authenticated source scalar and retain its complete original multiplicity locator result.

The supplied reader keeps its own numerical policy and failure state. It is
called once at the request's actual primitive index; the original preparation
and candidate family are consumed directly. -/
def nearby {m : Type → Type} [Monad m] {polynomial : GaussianPolynomial}
    {original : Geometric.GeometricApproximation} (preparation : Preparation polynomial original)
    {current : Nat} {target : Rational}
    (request : Sequence.Selection.Coverage.Request preparation.coverage current target)
    (samples : (index : Nat) → m { value : Data.Gaussian.Basic.Canonical //
      value = preparation.source.sample index }) :
    m { value : Sequence.Selection.Nearby preparation.roots.candidates
      (preparation.source.sample request.index) target // value = request.locate } := do
  let sample ← samples request.index
  return preparation.nearbyFromSample request sample

/-- Complete the original stable multiplicity selection through an authenticated nearby reader.

The original factor certificates and root-pair bank are retained across the
read. Supplied complete caches are consumed directly; defaults compute each
cache once. The returned certificate identifies the complete default
selection, including its unchanged zero start and gap allocation. -/
def select {m : Type → Type} [Monad m] {α : Type} {polynomial : GaussianPolynomial}
    {original : Geometric.GeometricApproximation} (preparation : Preparation polynomial original)
    (readNearby : {current : Nat} → {target : Rational} →
      (request : Sequence.Selection.Coverage.Request preparation.coverage current target) →
      m { value : Sequence.Selection.Nearby preparation.roots.candidates
        (preparation.source.sample request.index) target // value = request.locate })
    (use : { value : Preparation.Selection preparation // value = preparation.select } → m α)
    (factorPairs : {value : CoprimePairs preparation.factors.entries // value = preparation.factorPairs} :=
      ⟨preparation.factorPairs, rfl⟩)
    (rootPairs : {value : Sequence.Selection.Pairs preparation.roots.candidates //
      value = preparation.roots.pairs factorPairs.val} := ⟨preparation.roots.pairs factorPairs.val, rfl⟩) : m α := do
  let target := rootPairs.val.separated.gap / 16
  have positive := Field.div_pos_direct rootPairs.val.separated.positive (by decide : (0 : Rational) < 16)
  let request := preparation.coverage.request 0 target positive
  let nearby ← readNearby request
  use (Preparation.Selection.ofNearby preparation factorPairs rootPairs request nearby)

end Multiplicity

section SidecarComparison

open Purelib.Approximation.Gaussian.Provenance.Algebraic
open Sidecar.Compared (RootInput Intrinsic)
open Purelib.Polynomial.Dense.Gaussian.Squarefree (Union)

/-- Restore the complete original algebraic comparison from its same root views and supplied state banks.

The shared ordered input inspection selects intrinsic replay or the unchanged
full-difference fallback. Intrinsic replay retains both original owners and
all three request bits; its actual preparation feeds the original decision,
comparison and deferred materialization. Reader failures skip later work and
the final callback. Only a nonlinear partition fallback invokes elimination.
-/
def compareSidecars {α : Type} {first second : Name.Coherent.CoherentNamed}
    (left : Sidecar first) (right : Sidecar second) (firstStart secondStart : Nat)
    (readers : (inputs : RootInput left × RootInput right) →
      IO (((index : Nat) → IO (CoherentRootCheckpoint.State inputs.1.view.root index)) ×
        ((index : Nat) → IO (CoherentRootCheckpoint.State inputs.2.view.root index))))
    (elimination : (inputs : RootInput left × RootInput right) →
      (algebra : Union inputs.1.view.polynomial inputs.2.view.polynomial) →
      (degree : 2 ≤ algebra.polynomial.natDegree) →
      IO (FTA.Squarefree.Input.Elimination (FTA.Squarefree.Input.mk algebra.squarefree degree)))
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (inspectInitial inspectLocal inspectBound : Bool)
    (use : {value : Sidecar.Compared left right firstStart secondStart //
      value = left.compare right firstStart secondStart inspectInitial inspectLocal inspectBound} → IO α) : IO α := do
  match found : Sidecar.Compared.rootInputs? left right with
  | none =>
      let result := Sidecar.Compared.fallback left right firstStart secondStart inspectBound
      have original : result =
          left.compare right firstStart secondStart inspectInitial inspectLocal inspectBound := by
        unfold Sidecar.compare
        rewrite [found]
        rfl
      use ⟨result, original⟩
  | some inputs =>
      let states ← readers inputs
      CoherentRootCheckpoint.withPreparedComparison inputs.1.view.input inputs.2.view.input
        inputs.1.view.root inputs.2.view.root firstStart secondStart
        (fun algebra degree => do elimination inputs algebra degree)
        columns winding control directory states.1 states.2 inspectInitial inspectLocal fun prepared => do
        have actual : prepared.val = CommonSource.prepareComparison inputs.1.view.input inputs.2.view.input
            inputs.1.view.root inputs.2.view.root firstStart secondStart
            prepared.val.inspectInitial prepared.val.inspectLocal := by
          rcases prepared with ⟨prepared, same⟩
          cases same
          rfl
        let intrinsic : Intrinsic left right firstStart secondStart :=
          ⟨inputs.1, inputs.2, ⟨prepared.val, actual⟩⟩
        let result := Sidecar.Compared.ofIntrinsic left right firstStart secondStart intrinsic inspectBound
        have original : result =
            left.compare right firstStart secondStart inspectInitial inspectLocal inspectBound := by
          have initialSame : prepared.val.inspectInitial = inspectInitial :=
            congrArg (fun value => value.inspectInitial) prepared.property
          have localSame : prepared.val.inspectLocal = inspectLocal :=
            congrArg (fun value => value.inspectLocal) prepared.property
          have same := Sidecar.compare_of_intrinsic left right firstStart secondStart intrinsic inspectBound
          change left.compare right firstStart secondStart prepared.val.inspectInitial prepared.val.inspectLocal
            inspectBound = result at same
          rewrite [initialSame, localSame] at same
          exact same.symm
        use ⟨result, original⟩

end SidecarComparison

end RootSelectionCheckpoint
