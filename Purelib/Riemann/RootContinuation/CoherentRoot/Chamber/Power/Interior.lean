module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power
public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Interior
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Interpolation
public import Purelib.RootIsolation.Progressive.Power.Unit.Move.Overlap.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap.Preparation
public import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap.Preparation
import Purelib.RootIsolation.Power.Isolation
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap
import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Overlap
import Purelib.RootIsolation.Owner.Bridge.Interpolation
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Genuine pointwise root families on the original three-overlap unit-power path -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power.Interior

open Purelib.RootIsolation.Progressive.Power.Unit.Rebase
open Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Overlap
open Purelib.Polynomial.Power.Gaussian (rootPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.RootIsolation.Owner.Bridge.Basic (OwnerBridge)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.FTA.Squarefree (Input)

variable {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
variable (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
variable (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)

/-- The exact original robust source frame of the unit-power move. -/
abbrev Source := Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo

/-- The original same-index transport overlap is the first occurrence of the path. -/
abbrev Move := Unit.Move.Overlap.unitMoveOverlap sourceUnit targetUnit degree degreeTwo small

/-- The original transported-to-isolated owner matching is the second occurrence of the path. -/
abbrev Rebase := Unit.Rebase.Overlap.unitRebaseOverlap sourceUnit targetUnit degree degreeTwo small

/-- The original isolation-to-robust owner rebase is the third occurrence of the path. -/
abbrev Robust := Unit.Frame.Overlap.isolationRobustOverlap
  (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo

/-- The actual matched index at the first intermediate original occurrence. -/
abbrev movedIndex (index : (Source sourceUnit degree degreeTwo).Index) :=
  (Move sourceUnit targetUnit degree degreeTwo small).matching.forward index

/-- The actual selected index at the second intermediate original occurrence. -/
abbrev selectedIndex (index : (Source sourceUnit degree degreeTwo).Index) :=
  (Rebase sourceUnit targetUnit degree degreeTwo small).matching.forward
    (movedIndex sourceUnit targetUnit degree degreeTwo small index)

set_option genInjectivity false in
/-- The three actual original selected bridge records, retained with their complete selector readbacks.

Each bridge belongs to its original overlap and bounded source occurrence.
Consumers use these cached values directly; the canonical selectors and their
underlying numerical refinements need not run again during family assembly.
-/
structure Bridges (index : (Source sourceUnit degree degreeTwo).Index) where
  /-- The retained original first same-index Rouché transport bridge. -/
  move : { value : OwnerBridge
      (Source sourceUnit degree degreeTwo).polynomial
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial //
    value = (Move sourceUnit targetUnit degree degreeTwo small).bridge index }
  /-- The retained original bridge to the independently selected target isolation owner. -/
  rebase : { value : OwnerBridge
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial //
    value = (Rebase sourceUnit targetUnit degree degreeTwo small).bridge
      (movedIndex sourceUnit targetUnit degree degreeTwo small index) }
  /-- The retained original bridge from that isolation occurrence to its robust target owner. -/
  robust : { value : OwnerBridge
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial
      (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).polynomial //
    value = (Robust targetUnit degree degreeTwo).bridge
      (selectedIndex sourceUnit targetUnit degree degreeTwo small index) }

constructive_injectivity Bridges

namespace Bridges

/-- Read the exact ordered selected boxes from the three retained original bridges.

The whole-list certificate identifies the original path selectors at their
original bounded occurrences. Execution reads only these cached bridge fields.
-/
def boxes {index : (Source sourceUnit degree degreeTwo).Index}
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index) :
    { value : List Purelib.Geometry.Rational.Box //
      value = (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small).bridgeBoxes index } :=
  ⟨[bridges.move.val.box, bridges.rebase.val.box, bridges.robust.val.box], by
    change [bridges.move.val.box, bridges.rebase.val.box, bridges.robust.val.box] =
      [((Move sourceUnit targetUnit degree degreeTwo small).bridge index).box,
       ((Rebase sourceUnit targetUnit degree degreeTwo small).bridge
         (movedIndex sourceUnit targetUnit degree degreeTwo small index)).box,
       ((Robust targetUnit degree degreeTwo).bridge
         (selectedIndex sourceUnit targetUnit degree degreeTwo small index)).box]
    rewrite [bridges.move.property, bridges.rebase.property, bridges.robust.property]
    rfl⟩

set_option genInjectivity false in
/-- The actual source owner, complete matching and selected robust source used by the original three bridges.

The matching retains its actual assignment-radius state and selected bounded
occurrence. The last source uses that same occurrence, so the bridge cache
needs neither a second selector nor a canonical source refinement.
-/
structure Caches (index : (Source sourceUnit degree degreeTwo).Index) where
  /-- The exact saved original robust source owner. -/
  source : Owner.Local.Preparation.Prepared ((Source sourceUnit degree degreeTwo).owner index)
  /-- The exact complete original owner assignment, including its retained refinement. -/
  selection : Matching.Preparation.Selection sourceUnit targetUnit degree degreeTwo small
    (movedIndex sourceUnit targetUnit degree degreeTwo small index)
  /-- The saved original robust source at the actual selected target occurrence. -/
  targetSource : Power.Unit.Source.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeTwo
    (Fin.cast (Frame.Basic.chamberFrame_degree (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
      (Matching.Preparation.selected selection))

constructive_injectivity Caches

/-- Build all three exact selected bridge records from their actual retained original parents. -/
def fromCaches {index : (Source sourceUnit degree degreeTwo).Index}
    (caches : Caches sourceUnit targetUnit degree degreeTwo small index) :
    Bridges sourceUnit targetUnit degree degreeTwo small index :=
  let first := Unit.Move.Overlap.Preparation.fromSource sourceUnit targetUnit degree degreeTwo small index caches.source
  let second := Preparation.fromSelection caches.selection
  let selected := Matching.Preparation.selected caches.selection
  let third := Unit.Frame.Overlap.Preparation.fromSource (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeTwo selected caches.targetSource
  { move := first
    rebase := second
    robust := ⟨third.val, third.property.trans (congrArg
      (Unit.Frame.Overlap.isolationRobustBridge (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo)
      (Matching.Preparation.selected_eq caches.selection))⟩ }

/-- The move bridge consumes the actual saved source owner's box. -/
theorem fromCaches_move_box {index : (Source sourceUnit degree degreeTwo).Index}
    (caches : Caches sourceUnit targetUnit degree degreeTwo small index) :
    (fromCaches sourceUnit targetUnit degree degreeTwo small caches).move.val.box = caches.source.owner.box :=
  Unit.Move.Overlap.Preparation.fromSource_box sourceUnit targetUnit degree degreeTwo small index caches.source

/-- The rebase bridge consumes the matching's actual saved assignment-radius state. -/
theorem fromCaches_rebase_box {index : (Source sourceUnit degree degreeTwo).Index}
    (caches : Caches sourceUnit targetUnit degree degreeTwo small index) :
    (fromCaches sourceUnit targetUnit degree degreeTwo small caches).rebase.val.box =
      caches.selection.val.refined.box :=
  Preparation.fromSelection_box caches.selection

/-- The final bridge consumes the exact saved robust source at the selected target occurrence. -/
theorem fromCaches_robust_box {index : (Source sourceUnit degree degreeTwo).Index}
    (caches : Caches sourceUnit targetUnit degree degreeTwo small index) :
    (fromCaches sourceUnit targetUnit degree degreeTwo small caches).robust.val.box = caches.targetSource.val.box :=
  Unit.Frame.Overlap.Preparation.fromSource_box _ _ _ _ _ caches.targetSource

end Bridges

/-- The second original bridge reads the same target power polynomial at every rational parameter. -/
private theorem rebase_polynomialAt
    (index : (Source sourceUnit degree degreeTwo).Index) (time : Rational) :
    ((Rebase sourceUnit targetUnit degree degreeTwo small).bridge
      (movedIndex sourceUnit targetUnit degree degreeTwo small index)).connection.polynomialAt time =
      rootPolynomial target degree := by
  change (Unit.Rebase.Overlap.unitRebaseBridge sourceUnit targetUnit degree degreeTwo small _).connection.polynomialAt
    time = _
  unfold Unit.Rebase.Overlap.unitRebaseBridge
  rw [OwnerBridge.cast_polynomialAt]
  rfl

/-- The third original bridge reads the same target power polynomial at every rational parameter. -/
private theorem robust_polynomialAt
    (index : (Source sourceUnit degree degreeTwo).Index) (time : Rational) :
    ((Robust targetUnit degree degreeTwo).bridge
      (selectedIndex sourceUnit targetUnit degree degreeTwo small index)).connection.polynomialAt time =
      rootPolynomial target degree := by
  change (Unit.Frame.Overlap.isolationRobustBridge (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo
    _).connection.polynomialAt time = _
  unfold Unit.Frame.Overlap.isolationRobustBridge
  rw [OwnerBridge.cast_polynomialAt]
  rfl

/-- Genuine regularity inputs consume the actual first bridge's complete coefficient readback. -/
private def moveInputs {index : (Source sourceUnit degree degreeTwo).Index}
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index) : InteriorStep.Inputs bridges.move.val := by
  intro time inside
  rw [bridges.move.property]
  exact Unit.Move.Interpolation.unitMoveBridge_input sourceUnit targetUnit degree degreeTwo small index time inside

/-- Genuine regularity inputs consume the actual same-polynomial second bridge. -/
private def rebaseInputs {index : (Source sourceUnit degree degreeTwo).Index}
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index) :
    InteriorStep.Inputs bridges.rebase.val := by
  intro time _
  rw [bridges.rebase.property, rebase_polynomialAt]
  exact Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo

/-- Genuine regularity inputs consume the actual same-polynomial third bridge. -/
private def robustInputs {index : (Source sourceUnit degree degreeTwo).Index}
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index) :
    InteriorStep.Inputs bridges.robust.val := by
  intro time _
  rw [bridges.robust.property, robust_polynomialAt]
  exact Power.Isolation.isolationInput (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo

/-- Assemble genuine all-rational-parameter families on the exact supplied original three-overlap trace.

Every original source, intermediate and endpoint cache remains in its original
cons. Each selected cached bridge supplies its own actual pointwise owner,
track and certified root, including the constant-polynomial rebases. Retained
handoffs compute endpoint relations and reuse their original point caches.
-/
def ofTrace {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index) : Trace.Interior trace :=
  let sourcePolynomial := rootPolynomial source degree
  let targetPolynomial := rootPolynomial target degree
  let sourceReading : { value : GaussianPolynomial // value = (Source sourceUnit degree degreeTwo).polynomial } :=
    ⟨sourcePolynomial, (Unit.Frame.robustChamberFrame_polynomial
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo).symm⟩
  let movedReading : { value : GaussianPolynomial // value =
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial } :=
    ⟨targetPolynomial, (Unit.Move.Frame.unitTransportedFrame_polynomial
      sourceUnit targetUnit degree degreeTwo small).symm⟩
  let selectedReading : { value : GaussianPolynomial // value =
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial } :=
    ⟨targetPolynomial, (Frame.Basic.chamberFrame_polynomial
      (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).symm⟩
  let robustReading : { value : GaussianPolynomial // value =
      (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).polynomial } :=
    ⟨targetPolynomial, (Unit.Frame.robustChamberFrame_polynomial
      (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).symm⟩
  Trace.Interior.prepareCons trace fun moved rest =>
    let firstInputs := moveInputs sourceUnit targetUnit degree degreeTwo small bridges
    let first := InteriorStep.Handoffs.ofCaches original moved bridges.move firstInputs
      (fun time inside => InteriorStep.Cached.buildFromPolynomials bridges.move.val firstInputs
        sourceReading movedReading time inside)
    ⟨first.interior, Trace.Interior.prepareCons rest fun selected rest =>
      let secondInputs := rebaseInputs sourceUnit targetUnit degree degreeTwo small bridges
      let second := InteriorStep.Handoffs.ofCaches moved selected bridges.rebase secondInputs
        (fun time inside => InteriorStep.Cached.buildFromPolynomials bridges.rebase.val secondInputs
          movedReading selectedReading time inside)
      ⟨second.interior, Trace.Interior.prepareCons rest fun robust rest =>
        let thirdInputs := robustInputs sourceUnit targetUnit degree degreeTwo small bridges
        let third := InteriorStep.Handoffs.ofCaches selected robust bridges.robust thirdInputs
          (fun time inside => InteriorStep.Cached.buildFromPolynomials bridges.robust.val thirdInputs
            selectedReading robustReading time inside)
        ⟨third.interior, Trace.Interior.prepareNil rest⟩⟩⟩

set_option genInjectivity false in
/-- A retained original trace, bridge parents and genuine all-parameter interior construction.

Both the cached bridge computation and the actual interior family carry their
whole original defining equations. Retaining the input caches keeps the full
matching refinement and robust source beside their derived bridge records.
-/
structure Prepared {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original) where
  /-- The exact original complete numerical trace is physically retained. -/
  original : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original
  /-- The retained trace is this same original parent. -/
  original_eq : original = trace
  /-- The actual saved parents of all three selected bridge records. -/
  caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index
  /-- The actual once-computed original selected bridge records. -/
  bridges : Bridges sourceUnit targetUnit degree degreeTwo small index
  /-- The bridges consume those same complete retained parents. -/
  bridges_eq : bridges = Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small caches
  /-- The genuine point family and same-parameter handoffs on the retained original trace. -/
  interior : Trace.Interior original
  /-- The family is the actual original finite assembly on the retained bridges. -/
  computed : interior = ofTrace sourceUnit targetUnit degree degreeTwo small original bridges

constructive_injectivity Prepared

/-- Attach the actual once-built original bridge records and their retained source caches to the same trace. -/
def prepareWithBridges {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index)
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index)
    (computed : bridges = Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small caches) :
    Prepared sourceUnit targetUnit degree degreeTwo small trace :=
  let interior := ofTrace sourceUnit targetUnit degree degreeTwo small trace bridges
  ⟨trace, rfl, caches, bridges, computed, interior, rfl⟩

/-- Attach cached original bridges and genuine interior families to the same actual numerical trace. -/
def prepare {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index) :
    Prepared sourceUnit targetUnit degree degreeTwo small trace :=
  let bridges := Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small caches
  prepareWithBridges sourceUnit targetUnit degree degreeTwo small trace caches bridges rfl

/-- Consuming exact supplied original bridges preserves the complete original attachment result. -/
theorem prepareWithBridges_eq {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index)
    (bridges : Bridges sourceUnit targetUnit degree degreeTwo small index)
    (computed : bridges = Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small caches) :
    prepareWithBridges sourceUnit targetUnit degree degreeTwo small trace caches bridges computed =
      prepare sourceUnit targetUnit degree degreeTwo small trace caches := by
  cases computed
  rfl

/-- Attachment physically retains the actual complete original bridge parents. -/
private theorem prepare_caches_readback {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index) :
    (prepare sourceUnit targetUnit degree degreeTwo small trace caches).caches = caches := rfl

/-- Read the complete unchanged bridge parents from the actual retained attachment. -/
theorem prepare_caches {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Bridges.Caches sourceUnit targetUnit degree degreeTwo small index) :
    (prepare sourceUnit targetUnit degree degreeTwo small trace caches).caches = caches :=
  prepare_caches_readback sourceUnit targetUnit degree degreeTwo small trace caches

/-- Reindex a retained elimination cache to an equal constant coefficient reading. -/
private def constantElimination {polynomial actual : GaussianPolynomial} (same : actual = polynomial)
    (input : Input polynomial) (elimination : Input.Elimination input) :
    Input.Elimination (same.symm ▸ input) := by
  cases same
  exact elimination

/-- Prepare all six actual endpoint programs before protection on the assignment-based three-overlap trace.

The first bridge retains the original coefficient move and its time-dependent
regularity input. The two rebases retain their actual supplied states and the
same cached target input on a constant polynomial. Every point and both
endpoint handoffs use the existing complete root-cache construction; no old
bridge or path equality is asserted for the new middle occurrence.
-/
def withAssignmentPrograms {Result : Sort u} {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (trace : Trace (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index original)
    (sourceOwner : Owner.Local.Preparation.Prepared ((Source sourceUnit degree degreeTwo).owner index))
    (targetSource : Power.Unit.Source.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit)
      targetUnit degree degreeTwo
      (Fin.cast (Frame.Basic.chamberFrame_degree (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
        assignment.selected))
    (prepare : (occurrence : Fin 3) → (endpoint : Fin 2) →
      {left right : GaussianPolynomial} → {bridge : OwnerBridge left right} → {inputs : InteriorStep.Inputs bridge} →
      {time : Rational} → {inside : InteriorStep.Inside time} →
      (cached : InteriorStep.Cached bridge inputs time inside) →
      (InteriorStep.Cached.Program cached → Result) → Result)
    (use : Trace.Interior trace → Result) : Result := by
  rcases targetFrame with ⟨frame, frameEq, isolation, isolationEq, input, inputEq, certificate, certificateEq⟩
  let elimination := Input.Elimination.ofCertificate input certificate certificateEq
  cases frameEq
  let firstBridge := Unit.Move.Overlap.Preparation.fromSource sourceUnit targetUnit degree degreeTwo small
    index sourceOwner
  let actualRebase := Preparation.overlapFromAssignment assignment
  have movedEq : movedIndex sourceUnit targetUnit degree degreeTwo small index =
      Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index :=
    Purelib.Data.Fin.Bijection.cast_forward _ index
  have selectedEq : actualRebase.matching.forward (movedIndex sourceUnit targetUnit degree degreeTwo small index) =
      assignment.selected :=
    (congrArg actualRebase.matching.forward movedEq).trans
      (Preparation.overlapFromAssignment_forward assignment)
  let secondBridge : { value : OwnerBridge
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial //
    value = actualRebase.bridge (movedIndex sourceUnit targetUnit degree degreeTwo small index) } :=
    ⟨Preparation.fromAssignment assignment,
      (Preparation.overlapFromAssignment_bridge assignment).symm.trans
        (congrArg actualRebase.bridge movedEq.symm)⟩
  let robustBridge := Unit.Frame.Overlap.Preparation.fromSource (nonzero_of_normSq_eq_one targetUnit)
    targetUnit degree degreeTwo assignment.selected targetSource
  let thirdBridge : { value : OwnerBridge
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial
      (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).polynomial //
    value = (Robust targetUnit degree degreeTwo).bridge
      (actualRebase.matching.forward (movedIndex sourceUnit targetUnit degree degreeTwo small index)) } :=
    ⟨robustBridge.val, robustBridge.property.trans
      (congrArg (Unit.Frame.Overlap.isolationRobustBridge (nonzero_of_normSq_eq_one targetUnit)
        targetUnit degree degreeTwo) selectedEq.symm)⟩
  let firstInputs : InteriorStep.Inputs firstBridge.val := by
    intro time inside
    rewrite [firstBridge.property]
    exact Unit.Move.Interpolation.unitMoveBridge_input sourceUnit targetUnit degree degreeTwo small index time inside
  let secondInputs : InteriorStep.Inputs secondBridge.val := fun time _ =>
    (Preparation.fromAssignment_polynomialAt assignment time).symm ▸ input
  let thirdInputs : InteriorStep.Inputs thirdBridge.val := fun time _ =>
    (Unit.Frame.Overlap.Preparation.fromSource_polynomialAt (nonzero_of_normSq_eq_one targetUnit)
      targetUnit degree degreeTwo assignment.selected targetSource time).symm ▸ input
  let sourcePolynomial := rootPolynomial source degree
  let targetPolynomial := rootPolynomial target degree
  let sourceReading : { value : GaussianPolynomial // value = (Source sourceUnit degree degreeTwo).polynomial } :=
    ⟨sourcePolynomial, (Unit.Frame.robustChamberFrame_polynomial
      (nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeTwo).symm⟩
  let movedReading : { value : GaussianPolynomial // value =
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).polynomial } :=
    ⟨targetPolynomial, (Unit.Move.Frame.unitTransportedFrame_polynomial
      sourceUnit targetUnit degree degreeTwo small).symm⟩
  let selectedReading : { value : GaussianPolynomial // value =
      (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).polynomial } :=
    ⟨targetPolynomial, (Frame.Basic.chamberFrame_polynomial
      (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo).symm⟩
  let robustReading : { value : GaussianPolynomial // value =
      (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).polynomial } :=
    ⟨targetPolynomial, (Unit.Frame.robustChamberFrame_polynomial
      (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo).symm⟩
  exact Trace.Interior.withCons trace fun moved rest firstCons =>
    Trace.Interior.withCons rest fun selected rest secondCons =>
      Trace.Interior.withCons rest fun robust rest thirdCons =>
        let firstCaches := fun time inside => InteriorStep.Cached.buildFromPolynomials firstBridge.val firstInputs
          sourceReading movedReading time inside
        let secondCaches := fun time inside =>
          InteriorStep.Cached.buildFromPolynomialsWithElimination secondBridge.val secondInputs
            movedReading selectedReading time inside ⟨secondInputs time inside, rfl⟩
            (constantElimination
              (Preparation.fromAssignment_polynomialAt assignment time)
              input elimination)
        let thirdCaches := fun time inside =>
          InteriorStep.Cached.buildFromPolynomialsWithElimination thirdBridge.val thirdInputs
            selectedReading robustReading time inside ⟨thirdInputs time inside, rfl⟩
            (constantElimination
              (Unit.Frame.Overlap.Preparation.fromSource_polynomialAt (nonzero_of_normSq_eq_one targetUnit)
                targetUnit degree degreeTwo assignment.selected targetSource time)
              input elimination)
        let firstInitial := firstCaches 0 InteriorStep.zero_inside
        let firstTerminal := firstCaches 1 InteriorStep.one_inside
        let secondInitial := secondCaches 0 InteriorStep.zero_inside
        let secondTerminal := secondCaches 1 InteriorStep.one_inside
        let thirdInitial := thirdCaches 0 InteriorStep.zero_inside
        let thirdTerminal := thirdCaches 1 InteriorStep.one_inside
        prepare ⟨0, by decide⟩ ⟨0, by decide⟩ firstInitial fun firstInitialProgram =>
          prepare ⟨0, by decide⟩ ⟨1, by decide⟩ firstTerminal fun firstTerminalProgram =>
            prepare ⟨1, by decide⟩ ⟨0, by decide⟩ secondInitial fun secondInitialProgram =>
              prepare ⟨1, by decide⟩ ⟨1, by decide⟩ secondTerminal fun secondTerminalProgram =>
                prepare ⟨2, by decide⟩ ⟨0, by decide⟩ thirdInitial fun thirdInitialProgram =>
                  prepare ⟨2, by decide⟩ ⟨1, by decide⟩ thirdTerminal fun thirdTerminalProgram =>
                    let first := InteriorStep.Handoffs.ofEndpoints original moved firstBridge firstInputs firstCaches
                      ⟨firstInitial, rfl⟩ ⟨firstTerminal, rfl⟩ firstInitialProgram firstTerminalProgram
                      (fun _ _ cached => InteriorStep.Cached.Program.accelerate cached)
                    let second := InteriorStep.Handoffs.ofEndpoints moved selected secondBridge secondInputs
                      secondCaches
                      ⟨secondInitial, rfl⟩ ⟨secondTerminal, rfl⟩ secondInitialProgram secondTerminalProgram
                      (fun _ _ cached => InteriorStep.Cached.Program.accelerate cached)
                    let third := InteriorStep.Handoffs.ofEndpoints selected robust thirdBridge thirdInputs thirdCaches
                      ⟨thirdInitial, rfl⟩ ⟨thirdTerminal, rfl⟩ thirdInitialProgram thirdTerminalProgram
                      (fun _ _ cached => InteriorStep.Cached.Program.accelerate cached)
                    use (firstCons first.interior (secondCons second.interior
                      (thirdCons third.interior (Trace.Interior.prepareNil rest))))

/-- Assemble pure dyadic endpoint programs on the same actual three-overlap assignment trace.

Each actual parent and endpoint program is retained once. All six programs
are prepared before protection; arbitrary other rational parameters keep the
same pure dyadic construction.
-/
def fromAssignment {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (trace : Trace (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index original)
    (sourceOwner : Owner.Local.Preparation.Prepared ((Source sourceUnit degree degreeTwo).owner index))
    (targetSource : Power.Unit.Source.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit)
      targetUnit degree degreeTwo
      (Fin.cast (Frame.Basic.chamberFrame_degree (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
        assignment.selected)) : Trace.Interior trace :=
  withAssignmentPrograms sourceUnit targetUnit degree degreeTwo small targetFrame assignment trace
    sourceOwner targetSource
    (fun _ _ {_ _ _ _ _ _} cached use => use (InteriorStep.Cached.Program.accelerate cached))
    (fun result => result)

/-- Actual assignment-family assembly retains the complete supplied numerical trace. -/
theorem fromAssignment_original {index : (Source sourceUnit degree degreeTwo).Index}
    {original : Root (Source sourceUnit degree degreeTwo) index}
    (targetFrame : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
    (assignment : Matching.Preparation.Assignment sourceUnit targetUnit degree degreeTwo small
      (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index))
    (trace : Trace (Unit.Move.Path.Preparation.fromAssignment sourceUnit targetUnit degree degreeTwo small index
      targetFrame assignment) index original)
    (sourceOwner : Owner.Local.Preparation.Prepared ((Source sourceUnit degree degreeTwo).owner index))
    (targetSource : Power.Unit.Source.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit)
      targetUnit degree degreeTwo
      (Fin.cast (Frame.Basic.chamberFrame_degree (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo)
        assignment.selected)) :
    (fromAssignment sourceUnit targetUnit degree degreeTwo small targetFrame assignment trace
      sourceOwner targetSource).original = trace :=
  Trace.Interior.original_eq _

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power.Interior

end
