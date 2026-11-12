module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
public import Purelib.RootIsolation.Owner.Bridge.Interpolation
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.Data.Rat.Fraction
public import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
public import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
public import Purelib.RootIsolation.Track.Newton.Build
public import Purelib.RootIsolation.Track.Accelerated
public import Purelib.RootIsolation.Subdivision.WindingOne
import Purelib.Riemann.RootContinuation.CoherentRoot.Comparison
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Coprime.Bounds.Protection
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation
open Purelib.RootIsolation.FTA.Squarefree (Input)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Owner.Local.Basic (LocalOwner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)

namespace InteriorStep

/-- A rational parameter of one original Rouché piece lies in its closed unit interval. -/
abbrev Inside (time : Rational) := 0 ≤ time ∧ time ≤ 1

/-- The original zero endpoint lies in the closed parameter interval. -/
theorem zero_inside : Inside 0 := by constructor <;> decide

/-- The original unit endpoint lies in the closed parameter interval. -/
theorem one_inside : Inside 1 := by constructor <;> decide

/-- Actual nonlinear regularity inputs for every coefficient reading of one retained original bridge. -/
abbrev Inputs {left right : GaussianPolynomial} (bridge : OwnerBridge left right) :=
  (time : Rational) → Inside time → FTA.Squarefree.Input (bridge.connection.polynomialAt time)

/-- The actual shrinking program initialized by the retained bridge owner and its supplied regularity input. -/
@[expose] def trackAt {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (time : Rational) (inside : Inside time) :=
  (bridge.ownerAt time inside).track (inputs time inside).degreeAtLeastTwo (inputs time inside).squarefree

/-- The exact original shrinking-track type at one retained bridge parameter. -/
abbrev Track {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (time : Rational) (inside : Inside time) :=
  WindingOneTrack (bridge.connection.polynomialAt time) (bridge.ownerAt time inside).box

set_option genInjectivity false in
/-- One prepared point retains its actual original input, complete track and root cache together.

The input and whole track have defining equalities to the original bridge's
pointwise program. Consumers use these retained fields and do not reconstruct
the track already used by the root-cache producer.
-/
structure Cached {left right : GaussianPolynomial} (bridge : OwnerBridge left right) (inputs : Inputs bridge)
    (time : Rational) (inside : Inside time) where
  /-- The actual original coefficient reading is retained with its literal interpolation readback. -/
  polynomial : { value : GaussianPolynomial // value = bridge.connection.polynomialAt time }
  /-- The complete actual original regularity input at this parameter. -/
  input : FTA.Squarefree.Input polynomial.val
  /-- The cached input is the original family's actual parameter input. -/
  input_eq : input = polynomial.property.symm ▸ inputs time inside
  /-- The actual elimination certificate is retained for both original and subsequent numerical programs. -/
  elimination : Input.Elimination input
  /-- The complete original point owner is retained, including its actual box, clearance and winding. -/
  owner : { value : LocalOwner polynomial.val // value = polynomial.property.symm ▸ bridge.ownerAt time inside }
  /-- The complete actual original shrinking track, with its whole pointwise-program readback. -/
  track : { value : WindingOneTrack polynomial.val owner.val.box //
    value = owner.val.track input.degreeAtLeastTwo input.squarefree }
  /-- The complete original certified root cache on this exact retained track. -/
  root : CertifiedName track.val

constructive_injectivity Cached

namespace Cached

/-- Retain already prepared original input, track and root data without invoking their producers. -/
@[expose] def ofRoot {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time}
    (polynomial : GaussianPolynomial) (polynomial_eq : polynomial = bridge.connection.polynomialAt time)
    (input : FTA.Squarefree.Input polynomial) (input_eq : input = polynomial_eq.symm ▸ inputs time inside)
    (owner : LocalOwner polynomial) (owner_eq : owner = polynomial_eq.symm ▸ bridge.ownerAt time inside)
    (track : WindingOneTrack polynomial owner.box)
    (track_eq : track = owner.track input.degreeAtLeastTwo input.squarefree)
    (root : CertifiedName track)
    (elimination : Input.Elimination input) : Cached bridge inputs time inside :=
  ⟨⟨polynomial, polynomial_eq⟩, input, input_eq, elimination,
    ⟨owner, owner_eq⟩, ⟨track, track_eq⟩, root⟩

/-- Build the exact original point program from its genuine parameter input and retained bridge.

Each requested parameter computes its coefficient reading, actual owner and
whole track once, then retains the certified root on that same track. No
replacement root or input polynomial is selected by an equation alone.
-/
@[expose] def build {left right : GaussianPolynomial} (bridge : OwnerBridge left right) (inputs : Inputs bridge)
    (time : Rational) (inside : Inside time) : Cached bridge inputs time inside :=
  let polynomial := bridge.connection.polynomialAt time
  let input := inputs time inside
  let owner := bridge.ownerAt time inside
  let elimination := Input.Elimination.ofInput input
  let track := Track.Newton.Build.ofInitial input.degreeAtLeastTwo input.squarefree
    elimination.certificate owner.initialState
  have sameTrack : track = owner.track input.degreeAtLeastTwo input.squarefree := by
    rcases elimination with ⟨degree, degreeEq, certificate, same⟩
    cases degreeEq
    cases same
    rfl
  let root := certifiedName track input.degreePositive
  ofRoot polynomial rfl input rfl owner rfl track sameTrack root elimination

/-- Build the identical original point cache using supplied input and elimination caches.

The input, owner and complete canonical track are unchanged. Both supplied
values enter the original track constructor directly, avoiding a second input
or elimination construction before a new program can use the same caches.
-/
@[expose] def buildWithElimination {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside })
    (elimination : Input.Elimination input.val) : Cached bridge inputs time inside :=
  let polynomial := bridge.connection.polynomialAt time
  let owner := bridge.ownerAt time inside
  let track := Track.Newton.Build.ofInitial input.val.degreeAtLeastTwo input.val.squarefree
    elimination.certificate owner.initialState
  have sameTrack : track = owner.track input.val.degreeAtLeastTwo input.val.squarefree := by
    rcases elimination with ⟨degree, degreeEq, certificate, same⟩
    cases degreeEq
    cases same
    rfl
  let root := certifiedName track input.val.degreePositive
  ofRoot polynomial rfl input.val input.property owner rfl track sameTrack root elimination

/-- Supplying the checked caches preserves the complete original point record. -/
theorem buildWithElimination_eq {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside })
    (elimination : Input.Elimination input.val) :
    buildWithElimination bridge inputs time inside input elimination = build bridge inputs time inside := by
  rcases input with ⟨input, sameInput⟩
  cases sameInput
  rewrite [Input.Elimination.eq_of_input elimination (Input.Elimination.ofInput (inputs time inside))]
  rfl

/-- Reindex the original input family along two literal endpoint coefficient equalities. -/
private def inputsFromPolynomials {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) :
    Inputs (bridge.cast first.property.symm second.property.symm) := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  exact inputs

/-- Restore a complete already computed point cache to its original coefficient and input indices. -/
private def restorePolynomials {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time)
    (value : Cached (bridge.cast first.property.symm second.property.symm)
      (inputsFromPolynomials bridge inputs first second) time inside) : Cached bridge inputs time inside := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  exact value

/-- Build the same original point program using retained literal endpoint coefficient readings.

The two whole coefficient equalities transport the original bridge indices.
Its actual owner and numerical program remain unchanged, while consuming the
retained coefficient records avoids materializing their enclosing frame data.
-/
def buildFromPolynomials {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right })
    (time : Rational) (inside : Inside time) : Cached bridge inputs time inside :=
  let actualBridge := bridge.cast first.property.symm second.property.symm
  let actualInputs := inputsFromPolynomials bridge inputs first second
  let value := build actualBridge actualInputs time inside
  restorePolynomials bridge inputs first second time inside value

/-- Reindex the retained input along literal endpoint coefficient readings. -/
private def inputFromPolynomials {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside }) :
    { value : FTA.Squarefree.Input
      ((bridge.cast first.property.symm second.property.symm).connection.polynomialAt time) //
      value = inputsFromPolynomials bridge inputs first second time inside } := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  exact input

/-- Reindex the same retained elimination certificate along literal endpoint readings. -/
private def eliminationFromPolynomials {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside })
    (elimination : Input.Elimination input.val) :
    Input.Elimination (inputFromPolynomials bridge inputs first second time inside input).val := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  exact elimination

/-- Reuse literal coefficients and both supplied caches in the original point constructor. -/
def buildFromPolynomialsWithElimination {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside })
    (elimination : Input.Elimination input.val) : Cached bridge inputs time inside :=
  let actualBridge := bridge.cast first.property.symm second.property.symm
  let actualInputs := inputsFromPolynomials bridge inputs first second
  let actualInput := inputFromPolynomials bridge inputs first second time inside input
  let actualElimination := eliminationFromPolynomials bridge inputs first second time inside input elimination
  let value := buildWithElimination actualBridge actualInputs time inside actualInput actualElimination
  restorePolynomials bridge inputs first second time inside value

/-- Literal coefficient and elimination reuse preserves the complete original point cache. -/
theorem buildFromPolynomialsWithElimination_eq {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time)
    (input : { value : FTA.Squarefree.Input (bridge.connection.polynomialAt time) // value = inputs time inside })
    (elimination : Input.Elimination input.val) :
    buildFromPolynomialsWithElimination bridge inputs first second time inside input elimination =
      build bridge inputs time inside := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  exact buildWithElimination_eq bridge inputs time inside input elimination

/-- Retained coefficient readings preserve the complete original point cache and every numerical field. -/
theorem buildFromPolynomials_eq {left right : GaussianPolynomial} (bridge : OwnerBridge left right)
    (inputs : Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : Inside time) :
    buildFromPolynomials bridge inputs first second time inside = build bridge inputs time inside := by
  rcases first with ⟨first, firstEq⟩
  rcases second with ⟨second, secondEq⟩
  cases firstEq
  cases secondEq
  rfl

/-- Read the same retained original root cache at the exact original pointwise track index. -/
@[expose] def original {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) :
    CertifiedName (trackAt bridge inputs time inside) := by
  cases cached with
  | mk polynomial input inputEq elimination owner track root =>
      rcases polynomial with ⟨polynomial, samePolynomial⟩
      cases samePolynomial
      cases inputEq
      rcases owner with ⟨owner, sameOwner⟩
      cases sameOwner
      rcases track with ⟨track, sameTrack⟩
      cases sameTrack
      exact root

/-- Every retained root sample lies in the same complete original bridge box. -/
theorem sample_inside {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) (stage : Nat) :
    bridge.box.Contains (cached.root.approximation.sample stage) := by
  cases cached with
  | mk polynomial input inputEq elimination owner track root =>
      rcases polynomial with ⟨polynomial, samePolynomial⟩
      cases samePolynomial
      rcases owner with ⟨owner, sameOwner⟩
      cases sameOwner
      exact (congrArg (fun box => box.Contains (root.approximation.sample stage))
        (bridge.ownerAt_box time inside)).mp (root.sample_inside stage)

/-- The retained point owner has the exact original selected bridge box after polynomial reindexing. -/
theorem owner_box {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) :
    cached.owner.val.box = bridge.box := by
  cases cached with
  | mk polynomial input inputEq elimination owner track root =>
      rcases polynomial with ⟨polynomial, samePolynomial⟩
      cases samePolynomial
      rcases owner with ⟨owner, sameOwner⟩
      cases sameOwner
      exact bridge.ownerAt_box time inside

/-- The retained point program starts at the exact selected original bridge box. -/
theorem initial_box {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) :
    cached.track.val.initial.box = bridge.box := by
  cases cached with
  | mk polynomial input inputEq elimination owner track root =>
      rcases polynomial with ⟨polynomial, samePolynomial⟩
      cases samePolynomial
      rcases owner with ⟨owner, sameOwner⟩
      cases sameOwner
      rcases track with ⟨track, sameTrack⟩
      cases sameTrack
      change (bridge.ownerAt time inside).box = bridge.box
      exact bridge.ownerAt_box time inside

/-- The positive factor-protection request uses the retained point polynomial and its original ambient owner. -/
def protectionRequest {left right : GaussianPolynomial} {bridge : OwnerBridge left right}
    {inputs : Inputs bridge} {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) :
    { targetSq : Rational // 0 < targetSq } :=
  let coprime := Coprime.Operations.CoprimeCertificate.constantRight cached.input.nonzero
  let radius := Coprime.Bounds.Protection.protectionRadius coprime cached.owner.val.box
  ⟨radius ^ 2, Purelib.Data.Rat.Fraction.Order.Arithmetic.pow_pos_direct
    (Coprime.Bounds.Protection.protectionRadius_pos coprime cached.owner.val.box) 2⟩

/-- Compute the endpoint protection index from the initial scale without reading a positive root state. -/
def protectionIndex {left right : GaussianPolynomial} {bridge : OwnerBridge left right}
    {inputs : Inputs bridge} {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) :
    Nat :=
  let request := cached.protectionRequest
  cached.root.approximation.refineIndex 0 request.val request.property

set_option genInjectivity false in
/-- A retained point owner and an actual same-initial numerical program compared with it.

The original complete cache and its canonical-track readback remain intact.
The numerical track may differ, but starts at the same box and retains one
actual certified root used by both geometric and algebraic consumers.
-/
structure Program {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside) where
  /-- The complete original parent is physically retained. -/
  original : Cached bridge inputs time inside
  /-- The retained parent is the exact supplied cache. -/
  original_eq : original = cached
  /-- The actual numerical track keeps the original polynomial and ambient owner. -/
  track : WindingOneTrack cached.polynomial.val cached.owner.val.box
  /-- The numerical track starts at the exact original initial box. -/
  initial_box : track.initial.box = cached.track.val.initial.box
  /-- The one actual root cache used for numerical and polynomial readings. -/
  root : CertifiedName track
  /-- The computed original-to-numerical coherent-channel comparison. -/
  comparison : NamedEquivalent cached.root.value.name root.value.name

constructive_injectivity Program

namespace Program

variable {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time}

/-- Retain the original numerical cache itself without an additional state payment. -/
@[expose] def ofOriginal (cached : Cached bridge inputs time inside) : Program cached :=
  ⟨cached, rfl, cached.track.val, rfl, cached.root, NamedEquivalent.refl _⟩

/-- Attach an actual same-initial root and compute its comparison using only the new positive state.

The comparison retains both original root owners. Its common strictly nested
restart is paid from the supplied second program; no positive state of the
original canonical program is required merely to construct the comparison.
-/
@[expose] def ofRoot (cached : Cached bridge inputs time inside)
    (track : WindingOneTrack cached.polynomial.val cached.owner.val.box)
    (initial : track.initial.box = cached.track.val.initial.box) (root : CertifiedName track) : Program cached :=
  let comparison := cached.root.equivalent_initial cached.input root initial.symm
  ⟨cached, rfl, track, initial, root, comparison⟩

/-- Attach the exact loaded numerical root and its already computed original-channel comparison.

The complete original point parent remains unchanged. The supplied finite
refinement cache is consumed through the loaded root's actual track, while
its existing comparison is transported along the whole original-root
readback. No elimination or second comparison is constructed here.
-/
@[expose] def ofInitial (cached : Cached bridge inputs time inside)
    (prepared : Accelerated.Initial cached.input cached.track.val) (same : prepared.original = cached.root) :
    Program cached :=
  let comparison := (congrArg (fun original : CertifiedName cached.track.val =>
    NamedEquivalent original.value.name prepared.root.value.name) same).mp prepared.comparison
  ⟨cached, rfl, prepared.numericalTrack,
    congrArg (fun state => state.box) prepared.initial_eq, prepared.root, comparison⟩

/-- Loaded program attachment keeps the identical supplied numerical root and its finite refinement cache. -/
theorem ofInitial_root (cached : Cached bridge inputs time inside)
    (prepared : Accelerated.Initial cached.input cached.track.val) (same : prepared.original = cached.root) :
    (ofInitial cached prepared same).root = prepared.root := rfl

/-- Same-initial programs compute the same requested index without reading a positive root state. -/
theorem refineIndex_eq {cached : Cached bridge inputs time inside} (program : Program cached)
    (start : Nat) (targetSq : Rational) (positive : 0 < targetSq) :
    program.root.approximation.refineIndex start targetSq positive =
      cached.root.approximation.refineIndex start targetSq positive := by
  rewrite [program.root.approximation_eq, cached.root.approximation_eq]
  change Purelib.Approximation.Rational.Geometric.Search.firstQuarterBelow (scale program.track) start targetSq =
    Purelib.Approximation.Rational.Geometric.Search.firstQuarterBelow (scale cached.track.val) start targetSq
  exact congrArg (fun value =>
    Purelib.Approximation.Rational.Geometric.Search.firstQuarterBelow value start targetSq)
    (congrArg (fun box => box.diagonalSq) program.initial_box)

/-- The checked dyadic shortcut track and total fallback share one retained elimination certificate. -/
@[expose] def acceleratedTrack (cached : Cached bridge inputs time inside) :
    WindingOneTrack cached.polynomial.val cached.owner.val.box :=
  let clearances := AxisClearances.canonical cached.elimination.certificate
  let fallback := Subdivision.WindingOne.ofInitial cached.input cached.elimination.certificate
    cached.track.val.initial clearances
  Track.Accelerated.fromDyadic cached.elimination.certificate fallback clearances

/-- The underlying accelerated track retains the identical original initial state. -/
theorem acceleratedTrack_initial (cached : Cached bridge inputs time inside) :
    (acceleratedTrack cached).initial = cached.track.val.initial := by
  unfold acceleratedTrack
  exact (Track.Accelerated.fromDyadic_initial cached.elimination.certificate
    (Subdivision.WindingOne.ofInitial cached.input cached.elimination.certificate cached.track.val.initial
      (AxisClearances.canonical cached.elimination.certificate))
    (AxisClearances.canonical cached.elimination.certificate)).trans
      (Subdivision.WindingOne.ofInitial_initial cached.input cached.elimination.certificate cached.track.val.initial
        (AxisClearances.canonical cached.elimination.certificate))

/-- Install checked dyadic shortcuts and total subdivision from the same original initial state.

The original cache supplies its actual retained elimination certificate to
both programs. The new root and its same-initial comparison are constructed
once, without recomputing elimination or paying an old positive-index state.
-/
@[expose] def accelerate (cached : Cached bridge inputs time inside) : Program cached :=
  let track := acceleratedTrack cached
  let root := certifiedName track cached.root.degreePositive
  ofRoot cached track (congrArg (fun state => state.box) (acceleratedTrack_initial cached)) root

/-- Original-program attachment preserves the identical complete root cache. -/
theorem ofOriginal_root (cached : Cached bridge inputs time inside) :
    (ofOriginal cached).root = cached.root := rfl

/-- Same-initial attachment retains the complete supplied numerical root. -/
theorem ofRoot_root (cached : Cached bridge inputs time inside)
    (track : WindingOneTrack cached.polynomial.val cached.owner.val.box)
    (initial : track.initial.box = cached.track.val.initial.box) (root : CertifiedName track) :
    (ofRoot cached track initial root).root = root := rfl

/-- The actual comparison is computed from the two retained inputs and their same-initial witness. -/
theorem ofRoot_comparison (cached : Cached bridge inputs time inside)
    (track : WindingOneTrack cached.polynomial.val cached.owner.val.box)
    (initial : track.initial.box = cached.track.val.initial.box) (root : CertifiedName track) :
    (ofRoot cached track initial root).comparison =
      cached.root.equivalent_initial cached.input root initial.symm := rfl

/-- The program retains the same complete supplied accelerated track. -/
theorem accelerate_track (cached : Cached bridge inputs time inside) :
    (accelerate cached).track = acceleratedTrack cached := rfl

/-- The accelerated program keeps the full original initial state, including its line certificates. -/
theorem accelerate_initial (cached : Cached bridge inputs time inside) :
    (accelerate cached).track.initial = cached.track.val.initial :=
  (congrArg (fun track : WindingOneTrack cached.polynomial.val cached.owner.val.box => track.initial)
    (accelerate_track cached)).trans (acceleratedTrack_initial cached)

/-- Every actual numerical sample remains in the same original selected bridge box. -/
theorem sample_inside {cached : Cached bridge inputs time inside} (program : Program cached) (stage : Nat) :
    bridge.box.Contains (program.root.approximation.sample stage) := by
  exact (congrArg (fun box => box.Contains (program.root.approximation.sample stage)) cached.owner_box).mp
    (program.root.sample_inside stage)

end Program

end Cached

/-- Actual complete point caches for the original bridge's pointwise shrinking programs. -/
abbrev Caches {left right : GaussianPolynomial} (bridge : OwnerBridge left right) (inputs : Inputs bridge) :=
  (time : Rational) → (inside : Inside time) → Cached bridge inputs time inside

end InteriorStep

set_option genInjectivity false in
/-- Prepared interior root programs and genuine same-parameter handoffs for one original trace step.

The selected bridge is cached with its complete original-selector equality.
Actual regularity inputs and root-state caches are supplied at rational interior
parameters. The two endpoint comparisons concern the original source and target
cache separately; they do not identify values at different parameters.
-/
structure InteriorStep {start middle : ChamberFrame} (step : ChamberOverlap start middle)
    (index : start.Index) (originalSource : Root start index)
    (originalTarget : Root middle (step.matching.forward index)) where
  /-- The complete retained original source root cache. -/
  source : Root start index
  /-- The source cache is exactly the original supplied source. -/
  source_eq : source = originalSource
  /-- The complete retained original target root cache. -/
  target : Root middle (step.matching.forward index)
  /-- The target cache is exactly the original supplied target. -/
  target_eq : target = originalTarget
  /-- The actual selected original bridge, cached instead of re-running its selector at each parameter. -/
  bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index }
  /-- Genuine supplied interior regularity for this exact retained bridge. -/
  inputs : InteriorStep.Inputs bridge.val
  /-- The actual certified root caches of this same bridge's pointwise shrinking programs. -/
  caches : InteriorStep.Caches bridge.val inputs
  /-- The zero-parameter cache agrees with the exact original source cache at that same parameter. -/
  left : NamedEquivalent (caches 0 InteriorStep.zero_inside).root.value.name source.certificate.value.name
  /-- The unit-parameter cache agrees with the exact original target cache at that same parameter. -/
  right : NamedEquivalent (caches 1 InteriorStep.one_inside).root.value.name target.certificate.value.name
  /-- The configured numerical programs retain those same original caches; legacy construction uses identity. -/
  programs : (time : Rational) → (inside : InteriorStep.Inside time) →
    InteriorStep.Cached.Program (caches time inside) :=
      fun time inside => InteriorStep.Cached.Program.ofOriginal (caches time inside)

constructive_injectivity InteriorStep

namespace InteriorStep

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
variable {originalSource : Root start index} {originalTarget : Root middle (step.matching.forward index)}

/-- Retain the exact supplied bridge, original endpoint caches, interior inputs and genuine handoff comparisons. -/
@[expose] def ofCaches (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (left : NamedEquivalent (caches 0 zero_inside).root.value.name source.certificate.value.name)
    (right : NamedEquivalent (caches 1 one_inside).root.value.name target.certificate.value.name) :
    InteriorStep step index source target :=
  ⟨source, rfl, target, rfl, bridge, inputs, caches, left, right,
    fun time inside => Cached.Program.ofOriginal (caches time inside)⟩

/-- Every retained root sample lies in the same complete original bridge box. -/
theorem sample_inside (piece : InteriorStep step index originalSource originalTarget)
    (time : Rational) (inside : Inside time) (stage : Nat) :
    piece.bridge.val.box.Contains ((piece.caches time inside).root.approximation.sample stage) :=
  (piece.caches time inside).sample_inside stage

/-- The cached bridge box is exactly the original selected step's box. -/
theorem bridge_box (piece : InteriorStep step index originalSource originalTarget) :
    piece.bridge.val.box = (step.bridge index).box :=
  congrArg OwnerBridge.box piece.bridge.property

/-- The retained zero-parameter handoff consumes the complete original source root cache. -/
def leftEquivalent (piece : InteriorStep step index originalSource originalTarget) :
    NamedEquivalent (piece.caches 0 zero_inside).root.value.name originalSource.certificate.value.name := by
  have same := congrArg (fun root : Root start index => root.certificate.value.name) piece.source_eq
  exact same ▸ piece.left

/-- The retained unit-parameter handoff consumes the complete original target root cache. -/
def rightEquivalent (piece : InteriorStep step index originalSource originalTarget) :
    NamedEquivalent (piece.caches 1 one_inside).root.value.name originalTarget.certificate.value.name := by
  have same := congrArg (fun root : Root middle (step.matching.forward index) => root.certificate.value.name)
    piece.target_eq
  exact same ▸ piece.right

/-- Compute one retained point root's protected region on its exact endpoint polynomial. -/
private def endpointRegion {left right : GaussianPolynomial} {bridge : OwnerBridge left right} {inputs : Inputs bridge}
    {time : Rational} {inside : Inside time} (cached : Cached bridge inputs time inside)
    (program : Cached.Program cached) (frame : ChamberFrame) (same : cached.polynomial.val = frame.polynomial) :
    FactorRegion program.root frame.polynomial (DensePolynomial.constant 1) 0 :=
  FactorRegion.ofRoot program.root frame.polynomial (DensePolynomial.constant 1) frame.input.nonzero (by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    rewrite [DensePolynomial.eval_constant, mul_one, ← same]
    rfl) (Coprime.Operations.CoprimeCertificate.constantRight cached.input.nonzero) 0

/-- An original protected point state retains every supplied containment of its original initial box. -/
private theorem region_refines {left right : GaussianPolynomial} {bridge : OwnerBridge left right}
    {inputs : Inputs bridge} {time : Rational} {inside : Inside time}
    (cached : Cached bridge inputs time inside) (program : Cached.Program cached)
    {frame : ChamberFrame} {index : frame.Index}
    (root : Root frame index) (region : FactorRegion program.root frame.polynomial (DensePolynomial.constant 1) 0)
    (nested : cached.track.val.initial.box.Refines root.track.initial.box) :
    region.current.box.Refines root.track.initial.box := by
  have original := state_refines_of_le program.track (Nat.zero_le region.index)
  rewrite [← program.root.stateAt_eq region.index, ← region.current_eq] at original
  have actual : program.track.initial.box.Refines root.track.initial.box :=
    (congrArg (fun box => box.Refines root.track.initial.box) program.initial_box).mpr nested
  exact original.trans actual

set_option genInjectivity false in
/-- Actual endpoint caches and computed same-parameter handoffs for one original interior family.

The original family remains retained. Its two endpoint calls are executed once,
and their actual cached values and protected factor regions supply comparisons
with the distinct original source and target roots. The endpoint-aware view
returns those same entries without invoking the original family again.
-/
structure Handoffs {start middle : ChamberFrame} (step : ChamberOverlap start middle) (index : start.Index)
    (originalSource : Root start index) (originalTarget : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs) where
  /-- The complete actual original source cache is retained. -/
  source : Root start index
  /-- The source is exactly the originally supplied cache. -/
  source_eq : source = originalSource
  /-- The complete actual original selected target cache is retained. -/
  target : Root middle (step.matching.forward index)
  /-- The target is exactly the originally supplied cache. -/
  target_eq : target = originalTarget
  /-- The complete original pointwise family remains available away from the endpoints. -/
  original : Caches bridge.val inputs
  /-- The retained family is the unchanged original callback. -/
  original_eq : original = caches
  /-- The actual original zero-parameter cache is retained once. -/
  initial : { value : Cached bridge.val inputs 0 zero_inside // value = original 0 zero_inside }
  /-- The actual original unit-parameter cache is retained once. -/
  terminal : { value : Cached bridge.val inputs 1 one_inside // value = original 1 one_inside }
  /-- Nonendpoint parameters construct a pure program on their actual retained original cache. -/
  prepareProgram : (time : Rational) → (inside : Inside time) →
    (cached : Cached bridge.val inputs time inside) → Cached.Program cached
  /-- The once constructed actual zero-parameter numerical program. -/
  initialProgram : Cached.Program initial.val
  /-- The once constructed actual unit-parameter numerical program. -/
  terminalProgram : Cached.Program terminal.val
  /-- The computed protection region consumes the same retained zero-parameter root and original source polynomial. -/
  leftRegion : FactorRegion initialProgram.root start.polynomial (DensePolynomial.constant 1) 0
  /-- The actual protected initial state lies in the original source program's initial owner. -/
  left_nested : leftRegion.current.box.Refines source.track.initial.box
  /-- The computed protection region consumes the same retained unit-parameter root and original target polynomial. -/
  rightRegion : FactorRegion terminalProgram.root middle.polynomial (DensePolynomial.constant 1) 0
  /-- The actual protected terminal state lies in the original selected target program's initial owner. -/
  right_nested : rightRegion.current.box.Refines target.track.initial.box
  /-- The actual original-cache-to-source comparison, computed through this retained protection region. -/
  left : NamedEquivalent initial.val.root.value.name source.certificate.value.name
  /-- The actual original-cache-to-target comparison, computed through this retained protection region. -/
  right : NamedEquivalent terminal.val.root.value.name target.certificate.value.name

constructive_injectivity Handoffs

namespace Handoffs

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
variable {source : Root start index} {target : Root middle (step.matching.forward index)}
variable {bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index }}
variable {inputs : Inputs bridge.val} {original : Caches bridge.val inputs}

/-- Retain actual prepared endpoint parents and programs before computing their protection regions.

Both endpoint parents have whole readbacks to the original family. Protection
uses their supplied numerical roots, which remain the same stored programs
used by later geometry and algebraic sidecars. Only other parameters invoke
the pure program constructor; no equality to that constructor is required for
a prepared endpoint cache or program.
-/
def ofEndpoints (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    Handoffs step index source target bridge inputs caches :=
  let first := initial.val
  let last := terminal.val
  let leftRegion := endpointRegion first initialProgram start
    (first.polynomial.property.trans bridge.val.connection.at_zero)
  let rightRegion := endpointRegion last terminalProgram middle
    (last.polynomial.property.trans bridge.val.connection.at_one)
  have leftNested : first.track.val.initial.box.Refines source.track.initial.box := by
    rewrite [first.initial_box, source.initial_box]
    have nested := step.bridge_refines_left index
    rewrite [← bridge.property] at nested
    exact nested
  have rightNested : last.track.val.initial.box.Refines target.track.initial.box := by
    rewrite [last.initial_box, target.initial_box]
    have nested := step.bridge_refines_right index
    rewrite [← bridge.property] at nested
    exact nested
  { source := source
    source_eq := rfl
    target := target
    target_eq := rfl
    original := caches
    original_eq := rfl
    initial := initial
    terminal := terminal
    prepareProgram := prepareProgram
    initialProgram := initialProgram
    terminalProgram := terminalProgram
    leftRegion := leftRegion
    left_nested := region_refines first initialProgram source leftRegion leftNested
    rightRegion := rightRegion
    right_nested := region_refines last terminalProgram target rightRegion rightNested
    left := initialProgram.comparison.trans
      (leftRegion.equivalent start.input source.certificate
        (region_refines first initialProgram source leftRegion leftNested)).symm
    right := terminalProgram.comparison.trans
      (rightRegion.equivalent middle.input target.certificate
        (region_refines last terminalProgram target rightRegion rightNested)).symm }

/-- The supplied initial parent is retained as the identical complete cache and readback. -/
theorem ofEndpoints_initial (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).initial.val = initial.val := (rfl)

/-- The supplied terminal parent is retained as the identical complete cache and readback. -/
theorem ofEndpoints_terminal (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).terminal.val = terminal.val := (rfl)

/-- The initial protection root is the identical complete supplied numerical program. -/
theorem ofEndpoints_initialProgram (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    HEq (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).initialProgram initialProgram := HEq.rfl

/-- The terminal protection root is the identical complete supplied numerical program. -/
theorem ofEndpoints_terminalProgram (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    HEq (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).terminalProgram terminalProgram := HEq.rfl

/-- The actual initial protection consumes exactly the cheaply computed original-index request. -/
theorem ofEndpoints_left_index (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).leftRegion.index = initial.val.protectionIndex := by
  change initialProgram.root.approximation.refineIndex 0 initial.val.protectionRequest.val
    initial.val.protectionRequest.property =
      initial.val.root.approximation.refineIndex 0 initial.val.protectionRequest.val
        initial.val.protectionRequest.property
  exact initialProgram.refineIndex_eq 0 _ _

/-- The actual terminal protection consumes exactly its cheaply computed original-index request. -/
theorem ofEndpoints_right_index (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (initial : { value : Cached bridge.val inputs 0 zero_inside // value = caches 0 zero_inside })
    (terminal : { value : Cached bridge.val inputs 1 one_inside // value = caches 1 one_inside })
    (initialProgram : Cached.Program initial.val) (terminalProgram : Cached.Program terminal.val)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    (ofEndpoints source target bridge inputs caches initial terminal initialProgram terminalProgram
      prepareProgram).rightRegion.index = terminal.val.protectionIndex := by
  change terminalProgram.root.approximation.refineIndex 0 terminal.val.protectionRequest.val
    terminal.val.protectionRequest.property =
      terminal.val.root.approximation.refineIndex 0 terminal.val.protectionRequest.val
        terminal.val.protectionRequest.property
  exact terminalProgram.refineIndex_eq 0 _ _

/-- Construct each pure endpoint program once and retain it through the prepared-endpoint constructor. -/
def ofPrograms (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs)
    (prepareProgram : (time : Rational) → (inside : Inside time) →
      (cached : Cached bridge.val inputs time inside) → Cached.Program cached) :
    Handoffs step index source target bridge inputs caches :=
  let initial := caches 0 zero_inside
  let terminal := caches 1 one_inside
  let initialProgram := prepareProgram 0 zero_inside initial
  let terminalProgram := prepareProgram 1 one_inside terminal
  ofEndpoints source target bridge inputs caches ⟨initial, rfl⟩ ⟨terminal, rfl⟩
    initialProgram terminalProgram prepareProgram

/-- Preserve the original canonical endpoint protection and direct comparison schedules.

The identity programs retain exactly the original caches. The two comparisons
remain the direct original factor-region comparisons, without an extra
reflexive composition changing their requested index schedules.
-/
def ofCaches (source : Root start index) (target : Root middle (step.matching.forward index))
    (bridge : { bridge : OwnerBridge start.polynomial middle.polynomial // bridge = step.bridge index })
    (inputs : Inputs bridge.val) (caches : Caches bridge.val inputs) :
    Handoffs step index source target bridge inputs caches :=
  let initial := caches 0 zero_inside
  let terminal := caches 1 one_inside
  let initialProgram := Cached.Program.ofOriginal initial
  let terminalProgram := Cached.Program.ofOriginal terminal
  let leftRegion := endpointRegion initial initialProgram start
    (initial.polynomial.property.trans bridge.val.connection.at_zero)
  let rightRegion := endpointRegion terminal terminalProgram middle
    (terminal.polynomial.property.trans bridge.val.connection.at_one)
  have leftNested : initial.track.val.initial.box.Refines source.track.initial.box := by
    rewrite [initial.initial_box, source.initial_box]
    have nested := step.bridge_refines_left index
    rewrite [← bridge.property] at nested
    exact nested
  have rightNested : terminal.track.val.initial.box.Refines target.track.initial.box := by
    rewrite [terminal.initial_box, target.initial_box]
    have nested := step.bridge_refines_right index
    rewrite [← bridge.property] at nested
    exact nested
  { source := source
    source_eq := rfl
    target := target
    target_eq := rfl
    original := caches
    original_eq := rfl
    initial := ⟨initial, rfl⟩
    terminal := ⟨terminal, rfl⟩
    prepareProgram := fun _ _ cached => Cached.Program.ofOriginal cached
    initialProgram := initialProgram
    terminalProgram := terminalProgram
    leftRegion := leftRegion
    left_nested := region_refines initial initialProgram source leftRegion leftNested
    rightRegion := rightRegion
    right_nested := region_refines terminal terminalProgram target rightRegion rightNested
    left := (leftRegion.equivalent start.input source.certificate
      (region_refines initial initialProgram source leftRegion leftNested)).symm
    right := (rightRegion.equivalent middle.input target.certificate
      (region_refines terminal terminalProgram target rightRegion rightNested)).symm }

/-- Read the retained endpoint entries directly and invoke the original family only at other parameters. -/
@[expose] def caches (handoffs : Handoffs step index source target bridge inputs original) : Caches bridge.val inputs :=
  fun time inside =>
    if zero : time = 0 then by
      subst time
      exact handoffs.initial.val
    else if one : time = 1 then by
      subst time
      exact handoffs.terminal.val
    else handoffs.original time inside

/-- The endpoint-aware family consumes the identical complete retained initial cache. -/
theorem caches_zero (handoffs : Handoffs step index source target bridge inputs original) :
    handoffs.caches 0 zero_inside = handoffs.initial.val := by
  rw [caches, dif_pos rfl]

/-- The endpoint-aware family consumes the identical complete retained terminal cache. -/
theorem caches_one (handoffs : Handoffs step index source target bridge inputs original) :
    handoffs.caches 1 one_inside = handoffs.terminal.val := by
  rw [caches, dif_neg (by decide), dif_pos rfl]

/-- Every parameter view retains the complete original point cache without equating family functions. -/
theorem caches_eq (handoffs : Handoffs step index source target bridge inputs original)
    (time : Rational) (inside : Inside time) : handoffs.caches time inside = original time inside := by
  unfold caches
  split
  · rename_i zero
    subst time
    exact handoffs.initial.property.trans
      (congrArg (fun family : Caches bridge.val inputs => family 0 zero_inside) handoffs.original_eq)
  · split
    · rename_i one
      subst time
      exact handoffs.terminal.property.trans
        (congrArg (fun family : Caches bridge.val inputs => family 1 one_inside) handoffs.original_eq)
    · exact congrArg (fun family : Caches bridge.val inputs => family time inside) handoffs.original_eq

/-- Read the same retained endpoint programs and prepare other points from one actual cache each. -/
@[expose] def programs (handoffs : Handoffs step index source target bridge inputs original)
    (time : Rational) (inside : Inside time) : Cached.Program (handoffs.caches time inside) := by
  unfold caches
  split
  · rename_i zero
    subst time
    exact handoffs.initialProgram
  · split
    · rename_i one
      subst time
      exact handoffs.terminalProgram
    · exact handoffs.prepareProgram time inside (handoffs.original time inside)

/-- The configured zero endpoint returns the same complete retained numerical program. -/
theorem programs_zero (handoffs : Handoffs step index source target bridge inputs original) :
    handoffs.programs 0 zero_inside = handoffs.caches_zero.symm ▸ handoffs.initialProgram := rfl

/-- The configured unit endpoint returns the same complete retained numerical program. -/
theorem programs_one (handoffs : Handoffs step index source target bridge inputs original) :
    handoffs.programs 1 one_inside = handoffs.caches_one.symm ▸ handoffs.terminalProgram := rfl

/-- Build the genuine original step from retained point caches and their computed same-parameter comparisons.

Each comparison consumes its retained protection region and both actual root
programs. The source and target remain distinct original occurrences, with
separate polynomial and ambient indices throughout.
-/
@[expose] def interior (handoffs : Handoffs step index source target bridge inputs original) :
    InteriorStep step index source target where
  source := handoffs.source
  source_eq := handoffs.source_eq
  target := handoffs.target
  target_eq := handoffs.target_eq
  bridge := bridge
  inputs := inputs
  caches := fun time inside => handoffs.caches time inside
  left := by
    rewrite [handoffs.caches_zero]
    exact handoffs.left
  right := by
    rewrite [handoffs.caches_one]
    exact handoffs.right
  programs := handoffs.programs

end Handoffs

end InteriorStep

namespace Trace

set_option genInjectivity false in
/-- Genuine prepared interior families along the exact original numerical trace.

Every cons retains the original trace itself, the exact selected source/target
caches and bridge, and its original tail. No interior regularity, endpoint
handoff or geometrical root selection is manufactured by this certificate.
-/
inductive Interior : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → Trace path index source → Type 2
  /-- The empty original trace retains its original root without an interior piece. -/
  | nil {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
      Interior (source := root) (Trace.nil root)
  /-- Retain one actual original trace cons, its genuine interior evidence and its exact remaining family. -/
  | cons {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
      {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
      {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
      (original : Trace (.cons step remaining) index source)
      (original_eq : original = Trace.cons (source := source) target rest)
      (piece : InteriorStep step index source target) (tail : Interior rest) :
      Interior (source := source) (Trace.cons (source := source) target rest)

constructive_injectivity Interior

namespace Interior

/-- The original step data needed to prepare one actual trace constructor.

A nonempty trace consumes its exact retained target and tail. Its callback
supplies one actual point family and the prepared remaining trace; an empty
trace needs no additional numerical data.
-/
abbrev Preparation {start finish : ChamberFrame} (path : ChamberPath start finish)
    (index : start.Index) (source : Root start index) : Type 2 :=
  match path with
  | .nil _ => ULift.{2} Unit
  | .cons step remaining =>
      (target : Root _ (step.matching.forward index)) →
      (rest : Trace remaining (step.matching.forward index) target) →
        InteriorStep step index source target × Interior rest

/-- Prepare a trace constructor using its actual retained frame, overlap, root and tail fields. -/
@[expose] def prepare {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    Preparation path index source → Interior trace :=
  Trace.casesOn (motive := fun {_ _} path index source trace => Preparation path index source → Interior trace)
    trace
    (fun {_ _} root _ => .nil root)
    (fun {_ _ _ _ _ _ _} target rest callback =>
      let prepared := callback target rest
      .cons (Trace.cons target rest) rfl prepared.1 prepared.2)

/-- Prepare an actual original nonempty trace by consuming its retained target and tail directly. -/
@[expose] def prepareCons {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    (trace : Trace (.cons step remaining) index source)
    (callback : (target : Root middle (step.matching.forward index)) →
      (rest : Trace remaining (step.matching.forward index) target) →
        InteriorStep step index source target × Interior rest) : Interior trace :=
  prepare trace callback

/-- Consume an actual trace cons before preparing its piece, retaining its exact assembly operation.

The result may be an effectful action. The supplied target and tail are the
original stored fields; the continuation combines prepared evidence without
putting a higher-universe interior certificate inside a state or IO result.
-/
def withCons {Result : Sort u} {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    (trace : Trace (.cons step remaining) index source)
    (use : (target : Root middle (step.matching.forward index)) →
      (rest : Trace remaining (step.matching.forward index) target) →
      (InteriorStep step index source target → Interior rest → Interior trace) → Result) : Result := by
  cases trace with
  | cons target rest => exact use target rest (fun piece tail => .cons (.cons target rest) rfl piece tail)

/-- Prepare the exact original empty trace without replacing its retained source root. -/
@[expose] def prepareNil {frame : ChamberFrame} {index : frame.Index} {source : Root frame index}
    (trace : Trace (.nil frame) index source) : Interior trace :=
  prepare trace ⟨()⟩

/-- Read the complete actual original trace retained by the prepared family. -/
@[expose] def original : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    Interior trace → Trace path index source
  | _, _, _, _, _, _, .nil root => .nil root
  | _, _, _, _, _, _, .cons original _ _ _ => original

/-- Every prepared family retains exactly its original supplied trace. -/
theorem original_eq : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    (interior : Interior trace) → interior.original = trace
  | _, _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, _, .cons _ same _ _ => same

/-- Read the complete original starting root cache without building another root program. -/
@[expose] def source : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    Interior trace → Root start index
  | _, _, _, _, _, _, .nil root => root
  | _, _, _, _, _, _, .cons _ _ piece _ => piece.source

/-- Every prepared family retains exactly the supplied original starting root cache. -/
theorem source_eq : {start finish : ChamberFrame} → {path : ChamberPath start finish} →
    {index : start.Index} → {source : Root start index} → {trace : Trace path index source} →
    (interior : Interior trace) → interior.source = source
  | _, _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, _, .cons _ _ piece _ => piece.source_eq

/-- Extend the exact remaining family with the actual original step and its genuine prepared interior evidence. -/
@[expose] def ofStep {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
    (piece : InteriorStep step index source target) (tail : Interior rest) :
    Interior (source := source) (Trace.cons (source := source) target rest) :=
  .cons (Trace.cons (source := source) target rest) rfl piece tail

/-- Read the actual first original piece without rebuilding its bridge or pointwise caches. -/
@[expose] def first {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target} :
    Interior (Trace.cons (source := source) target rest) → InteriorStep step index source target
  | .cons _ _ piece _ => piece

/-- Read the actual remaining original family without discarding any later unresolved occurrence. -/
@[expose] def remaining {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {path : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace path (step.matching.forward index) target} :
    Interior (Trace.cons (source := source) target rest) → Interior rest
  | .cons _ _ _ tail => tail

/-- Reading the first piece of a prepared extension retains that complete actual supplied piece. -/
theorem ofStep_first {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
    (piece : InteriorStep step index source target) (tail : Interior rest) :
    (ofStep piece tail).first = piece := rfl

/-- Reading the tail of a prepared extension retains the complete actual supplied remaining family. -/
theorem ofStep_remaining {start middle finish : ChamberFrame} {step : ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    {target : Root middle (step.matching.forward index)} {rest : Trace remaining (step.matching.forward index) target}
    (piece : InteriorStep step index source target) (tail : Interior rest) :
    (ofStep piece tail).remaining = tail := rfl

end Interior

set_option genInjectivity false in
/-- The exact original trace and starting cache whose supplied interior family is absent.

The absence equation concerns the actual offered prepared family. It establishes
no singularity or pole and preserves the original numerical caches for retry.
-/
structure InteriorRequest {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source)
    (offered : Option (Interior trace)) where
  /-- The complete original trace retained for a later retry. -/
  original : Trace path index source
  /-- The retained trace is exactly the original input. -/
  original_eq : original = trace
  /-- The complete original starting cache retained for a later retry. -/
  initial : Root start index
  /-- The retained starting cache is exactly the original input. -/
  initial_eq : initial = source
  /-- This attempt has no supplied interior family for the same original trace. -/
  unavailable : offered = none

constructive_injectivity InteriorRequest

set_option genInjectivity false in
/-- An actual supplied interior family or the exact finite request for its absent original contract. -/
inductive InteriorOutcome {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source)
    (offered : Option (Interior trace)) : Type 2
  /-- Retain the actual supplied family and its offered-data readback. -/
  | prepared (interior : Interior trace) (offered_eq : offered = some interior)
  /-- Retain the original trace/cache and its exact absent-family equation. -/
  | requested (request : InteriorRequest trace offered)

constructive_injectivity InteriorOutcome

/-- Consume genuine prepared interior evidence or retain the exact original missing-family request. -/
@[expose] def acquireInterior {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    (offered : Option (Interior trace)) → InteriorOutcome trace offered
  | some interior => .prepared interior rfl
  | none => .requested ⟨trace, rfl, source, rfl, rfl⟩

/-- Retry a missing-family request with genuine evidence for its retained original trace. -/
@[expose] def InteriorRequest.resume {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    {offered : Option (Interior trace)} (request : InteriorRequest trace offered)
    (interior : Interior request.original) : Interior trace :=
  request.original_eq ▸ interior

end Trace

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

end
