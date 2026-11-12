module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Interior
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Admission
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
public import Purelib.Geometry.Rational.Box.Outside.Preparation
import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.RootIsolation.Owner.Local.Track
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Context
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator

open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Approximation

set_option genInjectivity false in
/-- The literal root denominator or the ordered constant-one-plus-root denominator. -/
inductive Kind where
  /-- The original root atom itself is the denominator. -/
  | root
  /-- Exact one is the first child and the original root is the second child. -/
  | oneAddRoot

constructive_injectivity Kind

namespace Kind

/-- The original checked syntax retains the literal atom or its ordered addition to exact one. -/
@[expose] def expression (kind : Kind) {arity : Nat} (index : Fin arity) : Checked.Expr arity :=
  match kind with
  | .root => Checked.Expr.atom index
  | .oneAddRoot => .add (Checked.Expr.rational 1) (Checked.Expr.atom index)

/-- The corresponding rational pole point in the original root's box. -/
@[expose] def pole : Kind → Canonical
  | .root => 0
  | .oneAddRoot => -1

/-- Complete the original ordered denominator using the same actual completed root child. -/
@[expose] def complete (kind : Kind) {arity : Nat} {environment : Fin arity → Annotated}
    {index : Fin arity} (root : Checked.Completed environment (.atom index)) :
    Checked.Completed environment (kind.expression index) :=
  match kind with
  | .root => root
  | .oneAddRoot => (Checked.Completed.rational environment 1).add root

/-- The actual geometric sample program follows the same literal or ordered affine denominator. -/
@[expose] def samples (kind : Kind) (root : GeometricApproximation) : GeometricApproximation :=
  match kind with
  | .root => root
  | .oneAddRoot => (GeometricApproximation.exact 1).add root

/-- Compare the original denominator to its actual retained target with the original same-index readings. -/
def agreesWith (kind : Kind) {arity : Nat} {environment : Fin arity → Annotated} {index : Fin arity}
    (root : Checked.Completed environment (.atom index)) (source target : GeometricApproximation)
    (equivalent : NamedEquivalent root.channel.name source.toApproximation.toNamed)
    (sample_eq : ∀ stage, target.sample stage = (kind.samples source).sample stage) :
    NamedEquivalent (kind.complete root).channel.name target.toApproximation.toNamed := by
  cases kind with
  | root =>
      exact equivalent.trans ((Sequence.Equivalence.approximationEquivalentOfSamplesEq
        source.toApproximation target.toApproximation (fun stage => (sample_eq stage).symm)).toNamed)
  | oneAddRoot =>
      let one := GeometricApproximation.exact 1
      exact Geometric.Coherent.Comparison.add_agreesWith (CoherentNamed.Coherence.exact 1) root.channel
        one source target (Geometric.Coherent.Comparison.exact_agreesWith 1 one (fun _ => rfl)) equivalent
        sample_eq

/-- The retained original coherent denominator agrees with its actual geometric sample program. -/
def agrees (kind : Kind) {arity : Nat} {environment : Fin arity → Annotated} {index : Fin arity}
    (root : Checked.Completed environment (.atom index)) (source : GeometricApproximation)
    (equivalent : NamedEquivalent root.channel.name source.toApproximation.toNamed) :
    NamedEquivalent (kind.complete root).channel.name (kind.samples source).toApproximation.toNamed :=
  kind.agreesWith root source (kind.samples source) equivalent (fun _ => rfl)

/-- The displayed affine denominator has exactly the quadrance of displacement from its rational pole. -/
theorem sample_norm (kind : Kind) (source : GeometricApproximation) (index : Nat) :
    Basic.normSq ((kind.samples source).sample index) = Basic.normSq (source.sample index - kind.pole) := by
  cases kind with
  | root =>
      change Basic.normSq (source.sample index) = Basic.normSq (source.sample index - 0)
      rewrite [Purelib.Data.Gaussian.Basic.sub_zero]
      rfl
  | oneAddRoot =>
      change Basic.normSq (1 + source.sample index) = Basic.normSq (source.sample index - -1)
      have scalar : source.sample index - -1 = 1 + source.sample index := by ring1
      rewrite [scalar]
      rfl

end Kind

variable {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
variable {originalSource : Root start index} {originalTarget : Root middle (step.matching.forward index)}

set_option genInjectivity false in
/-- One original point owner, its actual numerical program and that same root's polynomial sidecar.

The original complete cache remains the provenance parent. A possibly distinct
same-initial program is compared with it; both geometric and algebraic readings
consume that one retained numerical root at the same parameter.
-/
structure Point (piece : InteriorStep step index originalSource originalTarget) (time : Rational)
    (inside : Inside time) where
  /-- The complete original input/track/root bundle is retained with its whole family-cache readback. -/
  cache : { value : Cached piece.bridge.val piece.inputs time inside // value = piece.caches time inside }
  /-- The actual numerical program retains and compares this same original parent cache. -/
  program : Cached.Program cache.val
  /-- The once built sidecar consumes the same actual numerical root and original regularity input. -/
  sidecar : PolynomialRoot.Sidecar program.root.value
  /-- The sidecar is the isolated-root constructor on those exact retained inputs. -/
  sidecar_eq : sidecar = PolynomialRoot.Sidecar.ofIsolated program.root cache.val.input.toPositive

constructive_injectivity Point

/-- Retain an actual point program and build its polynomial sidecar from that same numerical root. -/
@[expose] def Point.ofProgram {piece : InteriorStep step index originalSource originalTarget} {time : Rational}
    {inside : Inside time}
    (cache : { value : Cached piece.bridge.val piece.inputs time inside // value = piece.caches time inside })
    (program : Cached.Program cache.val) : Point piece time inside :=
  let sidecar := PolynomialRoot.Sidecar.ofIsolated program.root cache.val.input.toPositive
  ⟨cache, program, sidecar, rfl⟩

/-- Retain the original interior root and polynomial input without an additional numerical payment. -/
@[expose] def pointAt (piece : InteriorStep step index originalSource originalTarget) (time : Rational)
    (inside : Inside time) : Point piece time inside :=
  let cache := piece.caches time inside
  Point.ofProgram ⟨cache, rfl⟩ (Cached.Program.ofOriginal cache)

/-- Build a point from its configured program without rerunning its original cache or program constructor.

The configured program retains its exact canonical parent. Endpoint-aware
families return their already paid numerical programs, so the sidecar and
geometric sampler share the same root used by endpoint protection.
-/
@[expose] def pointFromProgram (piece : InteriorStep step index originalSource originalTarget) (time : Rational)
    (inside : Inside time) : Point piece time inside :=
  let program := piece.programs time inside
  Point.ofProgram ⟨program.original, program.original_eq⟩
    ((congrArg (fun cache : Cached piece.bridge.val piece.inputs time inside => Cached.Program cache)
      program.original_eq).mpr program)

namespace Point

variable {piece : InteriorStep step index originalSource originalTarget} {time : Rational} {inside : Inside time}

/-- Read the actual numerical root used by both geometry and the retained polynomial sidecar. -/
abbrev root (point : Point piece time inside) := point.program.root

/-- Read the actual numerical track from that same retained point program. -/
abbrev track (point : Point piece time inside) := point.program.track

/-- Read the original regularity input from the same retained point-cache owner. -/
abbrev input (point : Point piece time inside) := point.cache.val.input

/-- Read the retained original root cache at its original complete track index. -/
@[expose] def originalRoot (point : Point piece time inside) :
    CertifiedName (trackAt piece.bridge.val piece.inputs time inside) := point.cache.val.original

/-- The cached original-track view is exactly the supplied family's actual root cache. -/
theorem originalRoot_eq (point : Point piece time inside) :
    point.originalRoot = (piece.caches time inside).original :=
  congrArg Cached.original point.cache.property

/-- The original-to-actual comparison retains both channels of this same point owner. -/
abbrev comparison (point : Point piece time inside) := point.program.comparison

/-- Attach checked acceleration using the retained original elimination cache and no old positive payment. -/
@[expose] def accelerate (point : Point piece time inside) : Point piece time inside :=
  ofProgram point.cache (Cached.Program.accelerate point.cache.val)

/-- Canonical point construction retains the identical original root cache. -/
theorem pointAt_root (piece : InteriorStep step index originalSource originalTarget) (time : Rational)
    (inside : Inside time) : (pointAt piece time inside).root = (piece.caches time inside).root := rfl

/-- Supplied point programs keep exactly the same numerical root in the point and sidecar indices. -/
theorem ofProgram_root
    (cache : { value : Cached piece.bridge.val piece.inputs time inside // value = piece.caches time inside })
    (program : Cached.Program cache.val) : (ofProgram cache program).root = program.root := rfl

/-- Configured construction reads the same numerical root as the retained family program. -/
theorem pointFromProgram_value (piece : InteriorStep step index originalSource originalTarget) (time : Rational)
    (inside : Inside time) :
    (pointFromProgram piece time inside).root.value = (piece.programs time inside).root.value := by
  have readback (program : Cached.Program (piece.caches time inside)) :
      (ofProgram ⟨program.original, program.original_eq⟩
        ((congrArg (fun cache : Cached piece.bridge.val piece.inputs time inside => Cached.Program cache)
          program.original_eq).mpr program)).root.value = program.root.value := by
    rcases program with ⟨original, same, track, initial, root, comparison⟩
    cases same
    rfl
  exact readback (piece.programs time inside)

/-- The bounded environment contains the same actual numerical root annotation. -/
@[expose] def environment (point : Point piece time inside) : Fin 1 → Annotated :=
  fun _ => Annotated.polynomialRoot point.sidecar

/-- The literal original atom occupies its actual bounded singleton position. -/
abbrev atomIndex : Fin 1 := ⟨0, by decide⟩

/-- The original atom is completed from the retained root sidecar, without re-isolation. -/
@[expose] def atom (point : Point piece time inside) : Checked.Completed point.environment (.atom atomIndex) :=
  Checked.Completed.atom point.environment atomIndex (Algebraic.Sidecar.ofRoot point.sidecar)

/-- Complete the literal or ordered affine denominator from this same actual root cache. -/
@[expose] def completed (point : Point piece time inside) (kind : Kind) :
    Checked.Completed point.environment (kind.expression atomIndex) := kind.complete point.atom

/-- The original completed atom keeps the unchanged actual interior root channel. -/
theorem atom_channel (point : Point piece time inside) : point.atom.channel = point.root.value := rfl

/-- Every displayed original root sample lies in this same retained bridge box. -/
theorem sample_inside (point : Point piece time inside) (stage : Nat) :
    piece.bridge.val.box.Contains (point.root.geometric.sample stage) := point.program.sample_inside stage

/-- The actual original denominator channel agrees with the geometric interpretation of its ordered syntax. -/
def agrees (point : Point piece time inside) (kind : Kind) :
    NamedEquivalent (point.completed kind).channel.name
      (kind.samples point.root.geometric).toApproximation.toNamed :=
  let geometric := point.root.geometric
  let target := kind.samples geometric
  kind.agreesWith point.atom geometric target
    (point.root.geometric_agreesWith geometric (fun _ => rfl)) (fun _ => rfl)

/-- Box exclusion computes an all-index denominator lower quadrance at every actual retained parameter. -/
theorem lower (point : Point piece time inside) (kind : Kind)
    (clearance : Box.OutsideSide.Prepared piece.bridge.val.box kind.pole) (stage : Nat) :
    clearance.margin ≤ Basic.normSq ((kind.samples point.root.geometric).sample stage) := by
  rewrite [kind.sample_norm]
  exact clearance.lower (point.sample_inside stage)

/-- Prepare the literal root or ordered one-plus-root reciprocal from the original box's computed margin.

The actual geometric observation is paid from its original initial state. The
unchanged original completed denominator and its exact residual supply the
reciprocal cache; the enclosure is used only to derive its positive sample bound.
-/
@[expose] def prepare (point : Point piece time inside) (kind : Kind)
    (clearance : Box.OutsideSide.Prepared piece.bridge.val.box kind.pole) :
    Checked.Geometric.Inverse (point.completed kind) :=
  let root := point.atom
  let geometric := point.root.geometric
  let source := kind.samples geometric
  let child := kind.complete root
  let equivalent := kind.agreesWith root geometric source
    (point.root.geometric_agreesWith geometric (fun _ => rfl)) (fun _ => rfl)
  Checked.Geometric.fromLower child source equivalent
    (Refinement.State.initial (Geometric.Preparation.sampledChannel source))
    clearance.margin clearance.positive (point.lower kind clearance)

end Point

/-- Inspect the rational pole against the actual original bridge box and retain the computed coordinate margin. -/
@[expose] def inspect (piece : InteriorStep step index originalSource originalTarget) (kind : Kind) :
    Box.PointExclusion piece.bridge.val.box kind.pole := Box.inspectPoint piece.bridge.val.box kind.pole

set_option genInjectivity false in
/-- The once computed spatial inspection of one original bridge and denominator syntax.

The retained result comes from the same original finite membership test.
Pointwise reciprocal consumers share this result and its computed margin.
-/
structure Inspection (piece : InteriorStep step index originalSource originalTarget) (kind : Kind) where
  /-- The complete original piece, including both handoffs and all parameter caches. -/
  original : InteriorStep step index originalSource originalTarget
  /-- The retained family is exactly this original input piece. -/
  original_eq : original = piece
  /-- The once computed sufficient spatial exclusion or finite inconclusivity. -/
  result : Box.PointExclusion piece.bridge.val.box kind.pole
  /-- The result is exactly this same original box inspection. -/
  result_eq : result = inspect piece kind

constructive_injectivity Inspection

/-- Inspect and retain one original bridge's whole-parameter sufficient denominator condition once. -/
@[expose] def inspectPiece (piece : InteriorStep step index originalSource originalTarget) (kind : Kind) :
    Inspection piece kind := ⟨piece, rfl, inspect piece kind, rfl⟩

set_option genInjectivity false in
/-- An actual same-parameter reciprocal preparation or the retained unresolved original denominator.

The inconclusive branch retains the original point/root cache and completed
denominator alongside the failed sufficient box condition. It proves no pole.
-/
inductive PointOutcome {piece : InteriorStep step index originalSource originalTarget} {time : Rational}
    {inside : Inside time} (point : Point piece time inside) (kind : Kind) where
  /-- The actual completed original reciprocal retains its paid observation and residual cache. -/
  | prepared (original : Point piece time inside) (original_eq : original = point)
      (inverse : Checked.Geometric.Inverse (point.completed kind))
  /-- Retain the original child and exact spatial condition left unresolved by this finite inspection. -/
  | inconclusive (original : Point piece time inside) (original_eq : original = point)
      (child : Checked.Completed point.environment (kind.expression Point.atomIndex))
      (child_eq : child = point.completed kind) (inside : piece.bridge.val.box.Contains kind.pole)

constructive_injectivity PointOutcome

/-- Consume the retained inspection without re-running its original coordinate comparisons. -/
@[expose] def Inspection.prepare {piece : InteriorStep step index originalSource originalTarget} {kind : Kind}
    (inspection : Inspection piece kind) {time : Rational} {inside : Inside time}
    (point : Point piece time inside) : PointOutcome point kind :=
  match inspection.result with
  | .apart clearance => .prepared point rfl (point.prepare kind clearance)
  | .inconclusive inside => .inconclusive point rfl (point.completed kind) rfl inside

set_option genInjectivity false in
/-- An exact operational pole at a retained original parameter and denominator occurrence.

The actual completed child and its zero identity establish the obstruction.
Containment of a rational point in the bridge box alone never constructs it.
-/
structure Pole {piece : InteriorStep step index originalSource originalTarget} {time : Rational}
    {inside : Inside time} (point : Point piece time inside) (kind : Kind) where
  /-- The actual original completed denominator is retained for the obstruction. -/
  child : Checked.Completed point.environment (kind.expression Point.atomIndex)
  /-- This is the same original denominator constructed from the actual root. -/
  child_eq : child = point.completed kind
  /-- The original denominator channel has an exact operational identity to zero. -/
  zero : Equivalence.Zero.ZeroIdentity child.channel

constructive_injectivity Pole

/-- Consume the retained exact original zero denominator as the existing checked reciprocal obstruction. -/
@[expose] def Pole.invalid {piece : InteriorStep step index originalSource originalTarget} {time : Rational}
    {inside : Inside time} {point : Point piece time inside} {kind : Kind} (pole : Pole point kind) :
    Checked.Invalid point.environment (.inverse (kind.expression Point.atomIndex)) :=
  .inverse pole.child.toResult pole.zero

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.InteriorStep.Denominator

end
