module
import TestPurelib.Approximation.Gaussian.MultiplicityAdmission
import scripts.checkpoint.CoherentRoot
import scripts.checkpoint.CoherentRootSamples
import scripts.checkpoint.InitialExtraction
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Rebase.Matching.Preparation
import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.System.FilePath

public import Purelib.Data.Nat.Positive
public import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning.Arithmetic
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Arithmetic
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Preparation
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Algebraic
import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning.Algebraic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.RootContinuation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Track.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
import Purelib.RootIsolation.Power.Unit.Circuit.Point
import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision
public import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
import Purelib.System.IO
import Init.System.IO
import Init.System.IOError
meta import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
meta import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Arithmetic
meta import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
meta import Purelib.RootIsolation.Progressive.Power.Unit.Move.Path
meta import Purelib.RootIsolation.Progressive.Power.Unit.Vertex
meta import Purelib.RootIsolation.Power.Unit.Circuit.Vertex
meta import Purelib.RootIsolation.Power.Unit.Circuit.Point
meta import Purelib.RootIsolation.Power.Unit.Circuit.Subdivision

/-!
# Prepared arbitrary-degree branch transport and numerical restart clients

The concrete path changes the parameter of Z³-w along one certified circuit
move. Generic clients retain original occurrence indices, actual endpoint
caches and arithmetic comparisons without a squarefree result assumption.
-/

namespace TestPurelib.Riemann.RootReconditioning

open Purelib.Riemann.RootContinuation
open TestPurelib.Approximation.Gaussian
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> NumericalArithmetic
open Purelib.Riemann.RootContinuation.CoherentRoot
open Purelib.Geometry.Gaussian
open Purelib.RootIsolation.Power.Unit

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (root : CoherentRoot.CertifiedName track) (input : FTA.Squarefree.Input polynomial)
    (start : Nat) (target : CoherentRoot.Coordinate) (positive : 0 < target) :
    Equivalence.NamedEquivalent root.value.name
      (CoherentRoot.Reconditioning.ofTarget root start target positive).root.value.name :=
  (CoherentRoot.Reconditioning.ofTarget root start target positive).namedEquivalent input

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (root : CoherentRoot.CertifiedName track) (start : Nat)
    (target : CoherentRoot.Coordinate) (positive : 0 < target) :
    (CoherentRoot.Reconditioning.ofTarget root start target positive).root.approximation.sample 0 =
      (root.stateAt (CoherentRoot.Reconditioning.ofTarget root start target positive).paid.index).box.anchor :=
  (CoherentRoot.Reconditioning.ofTarget root start target positive).first_sample

example {start middle finish : ChamberFrame} (left : ChamberPath start middle)
    (right : ChamberPath middle finish) (index : start.Index) (source : CoherentRoot.Chamber.Root start index)
    (first : Chamber.Trace left index source)
    (second : Chamber.Trace right (left.finalIndex index) first.endpoint) :
    Chamber.Trace (left.append right) index source := first.append second

example {start finish : ChamberFrame} (path : ChamberPath start finish) (index : start.Index) :
    path.reverse.finalIndex (path.finalIndex index) = index :=
  Chamber.Trace.endpointIndex_reverse path index

example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : CoherentRoot.Chamber.Root start index} (trace : Chamber.Trace path index source) :
    (Chamber.Trace.Reversal.ofTrace trace).returned = source :=
  Chamber.Trace.Reversal.ofTrace_returned_eq trace

example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : CoherentRoot.Chamber.Root start index} (trace : Chamber.Trace path index source)
    (stage : Nat) :
    (Chamber.Trace.Reversal.ofTrace trace).returned.certificate.approximation.sample stage =
      source.certificate.approximation.sample stage :=
  congrArg (fun root => root.certificate.approximation.sample stage)
    (Chamber.Trace.Reversal.ofTrace_returned_eq trace)

example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : CoherentRoot.Chamber.Root start index} (trace : Chamber.Trace path index source) :
    Equivalence.NamedEquivalent source.certificate.value.name
      (Chamber.Trace.Reversal.ofTrace trace).returned.certificate.value.name :=
  Chamber.Trace.Reversal.ofTrace_namedEquivalent trace

example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : CoherentRoot.Chamber.Root start index} {trace : Chamber.Trace path index source}
    (reversal : Chamber.Trace.Reversal trace) :
    Equivalence.NamedEquivalent source.certificate.value.name reversal.returned.certificate.value.name :=
  reversal.namedEquivalent

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {original : CoherentRoot.CertifiedName track}
    {start : Nat} (prepared : CoherentRoot.Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) (index : Nat) :
    (prepared.algebraic input).residual.source.sample index = prepared.root.approximation.sample index :=
  prepared.algebraic_sample input index

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {original : CoherentRoot.CertifiedName track}
    {start : Nat} (prepared : CoherentRoot.Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) :
    ((prepared.algebraic input).mul (prepared.algebraic input)).origin =
      .arithmetic .mul (.recondition original input prepared) (.recondition original input prepared) := rfl

example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : CoherentRoot.Chamber.Root start index} (trace : Chamber.Trace path index source)
    (stage : Nat) :
    (Chamber.Trace.Algebraic.ofTrace trace).endpoint.residual.source.sample stage =
      trace.endpoint.certificate.approximation.sample stage :=
  (Chamber.Trace.Algebraic.ofTrace trace).endpoint_sample stage

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {original : CoherentRoot.CertifiedName track}
    {start : Nat} (prepared : CoherentRoot.Reconditioning original start)
    (input : FTA.Squarefree.Input polynomial) :
    (Acquisition.Annotated.ofReconditioning prepared input).provenance =
      some (.algebraic (prepared.algebraic input)) := rfl

section

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Approximation.Gaussian.Provenance

/-- Completed expressions compare the original root channels with their actual retained restarts.

Each input retains its own polynomial, cache and paid restart. Only the
original root squarefreeness is supplied; an arithmetic result may have
repeated roots or collapse to zero.
-/
example {arity : Nat} {polynomials : Fin arity → GaussianPolynomial} {ambients : Fin arity → Box}
    {tracks : (index : Fin arity) → WindingOneTrack (polynomials index) (ambients index)}
    {originals : (index : Fin arity) → CertifiedName (tracks index)} {starts : Fin arity → Nat}
    (restarts : (index : Fin arity) → Reconditioning (originals index) (starts index))
    (inputs : (index : Fin arity) → FTA.Squarefree.Input (polynomials index))
    {expression : Expr arity}
    (first : Completed
      (fun index => Annotated.polynomialRoot
        (PolynomialRoot.Sidecar.ofIsolated (originals index) (inputs index).toPositive)) expression)
    (second : Completed
      (fun index => Annotated.polynomialRoot
        (PolynomialRoot.Sidecar.ofIsolated (restarts index).root (inputs index).toPositive)) expression) :
    Equivalence.NamedEquivalent first.channel.name second.channel.name :=
  Annotated.compareReconditionedExpression restarts inputs first second

/-- Completed endpoint expressions compare at the same original occurrences on independent caches.

Every atom keeps its own path and selected owner. Powers, conjugation and
checked reciprocals retain the two actual preparation caches.
-/
example {arity : Nat} {starts finishes : Fin arity → ChamberFrame}
    {paths : (index : Fin arity) → ChamberPath (starts index) (finishes index)}
    {indices : (index : Fin arity) → (starts index).Index}
    {sources : (index : Fin arity) → Chamber.Root (starts index) (indices index)}
    {traces : (index : Fin arity) → Chamber.Trace (paths index) (indices index) (sources index)}
    (evidence : (index : Fin arity) → Chamber.Trace.Algebraic (traces index))
    (others : (index : Fin arity) → Chamber.Root (finishes index) ((paths index).finalIndex (indices index)))
    {expression : Expr arity}
    (first : Construction.Result (fun index => Annotated.ofTraceEndpoint (evidence index)) expression)
    (second : Construction.Result (fun index => Annotated.ofChamberRoot (others index)) expression) :
    Equivalence.NamedEquivalent first.channel.name second.channel.name :=
  Annotated.compareTraceEndpointExpression evidence others first second

end

section

open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Progressive.Power.Unit

variable {source target : Canonical}
    (sourceUnit : Gaussian.Norm.Basic.normSq source = 1)
    (targetUnit : Gaussian.Norm.Basic.normSq target = 1)
    (degree : Nat.Positive.RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : Fin (Power.Gaussian.Progressive.Coefficients.coefficientTable target degree).degree)
    (prepared : Owner.Local.Preparation.Prepared
      ((Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner index))

example :
    (Move.Track.Preparation.rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).val =
      Unit.Move.Track.unitTransportedRawState sourceUnit targetUnit degree degreeTwo small
        (Unit.Move.Track.unitMoveSourceDegreeIndex sourceUnit targetUnit degree degreeTwo index) :=
  (Move.Track.Preparation.rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).property

example :
    (Move.Track.Preparation.rawFromFrame sourceUnit targetUnit degree degreeTwo small index prepared).val.box =
      prepared.owner.box :=
  Move.Track.Preparation.rawFromFrame_box sourceUnit targetUnit degree degreeTwo small index prepared

example :
    (Move.Track.Preparation.rawFromFrame
      sourceUnit targetUnit degree degreeTwo small index prepared).val.clearance.bound =
      prepared.owner.clearance.bound :=
  Move.Track.Preparation.rawFromFrame_bound sourceUnit targetUnit degree degreeTwo small index prepared

end

section

variable (rootDegree : Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ rootDegree.value)

/-- The actual first vertex of the coefficient-computed rational circuit subdivision. -/
public def sourceVertex : UnitVertex := Power.Unit.Circuit.Vertex.unitCircuitVertex .first rootDegree degreeAtLeastTwo 0

/-- The distinct next vertex of that same retained rational circuit subdivision. -/
public def targetVertex : UnitVertex := Power.Unit.Circuit.Vertex.unitCircuitVertex .first rootDegree degreeAtLeastTwo 1

/-- The original consecutive circuit vertices satisfy the retained unit-move budget. -/
public theorem smallMove : Power.Unit.Move.Budget.UnitMoveSmall
    (sourceVertex rootDegree degreeAtLeastTwo).unit (targetVertex rootDegree degreeAtLeastTwo).unit
    rootDegree degreeAtLeastTwo :=
  ⟨Circuit.Point.unitCircuitSubdivision_small .first rootDegree degreeAtLeastTwo 0,
    (Circuit.Point.unitCircuitSubdivision_liftMargin .first rootDegree degreeAtLeastTwo 0).le⟩

/-- The original complete source frame for the same degree-generic parameter family. -/
def sourceFrame : ChamberFrame := (sourceVertex rootDegree degreeAtLeastTwo).frame rootDegree degreeAtLeastTwo

/-- The original complete target frame at the actual next parameter. -/
def targetFrame : ChamberFrame := (targetVertex rootDegree degreeAtLeastTwo).frame rootDegree degreeAtLeastTwo

/-- The existing three-overlap prepared move for the same power-polynomial family. -/
def cubicPath : ChamberPath (sourceFrame rootDegree degreeAtLeastTwo) (targetFrame rootDegree degreeAtLeastTwo) :=
  Progressive.Power.Unit.Move.Path.unitSmallMovePath (sourceVertex rootDegree degreeAtLeastTwo).unit (targetVertex
      rootDegree degreeAtLeastTwo).unit rootDegree degreeAtLeastTwo
    ⟨Circuit.Point.unitCircuitSubdivision_small .first rootDegree degreeAtLeastTwo 0,
      (Circuit.Point.unitCircuitSubdivision_liftMargin .first rootDegree degreeAtLeastTwo 0).le⟩

/-- The displayed initial parameter of this cubic continuation is exactly one. -/
theorem source_parameter : (sourceVertex rootDegree degreeAtLeastTwo).value = 1 := by
  change UnitCircle.Quarter.unitCircuitMultiplier .first *
    UnitCircle.Stereographic.unitQuarterPoint
      (Circuit.Subdivision.unitCircuitParameter rootDegree degreeAtLeastTwo 0) = 1
  rewrite [Circuit.Subdivision.unitCircuitParameter_zero]
  exact (by decide : (1 : Canonical) *
    UnitCircle.Stereographic.unitQuarterPoint 0 = 1)

/-- The next parameter has strictly positive imaginary coordinate, so this path is nonstationary. -/
theorem target_parameter_im_positive : 0 < (targetVertex rootDegree degreeAtLeastTwo).value.im := by
  change 0 < (UnitCircle.Quarter.unitCircuitMultiplier .first *
    UnitCircle.Stereographic.unitQuarterPoint
      (Circuit.Subdivision.unitCircuitParameter rootDegree degreeAtLeastTwo 1)).im
  change 0 < ((1 : Canonical) *
    UnitCircle.Stereographic.unitQuarterPoint
      (Circuit.Subdivision.unitCircuitParameter rootDegree degreeAtLeastTwo 1)).im
  rewrite [Gaussian.Basic.one_mul, UnitCircle.Stereographic.unitQuarterPoint_im]
  let parameter := Circuit.Subdivision.unitCircuitParameter rootDegree degreeAtLeastTwo 1
  have parameterPositive : 0 < parameter := by
    change 0 < Circuit.Subdivision.unitCircuitParameter rootDegree degreeAtLeastTwo 1
    rewrite [Circuit.Subdivision.unitCircuitParameter_eq]
    exact Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (Circuit.Subdivision.unitCircuitStepCount_pos
        rootDegree degreeAtLeastTwo))
  have scalarPositive : 0 < parameter ^ 2 + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter) (by decide)
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) parameterPositive)
    (Fraction.Order.Field.inv_pos_direct scalarPositive)

/-- The original source and target parameters differ, independently of a root-sheet selection. -/
theorem parameters_differ : (sourceVertex rootDegree degreeAtLeastTwo).value ≠ (targetVertex rootDegree
    degreeAtLeastTwo).value := by
  intro same
  have sameIm := congrArg (fun value : Canonical => value.im) same
  rewrite [(source_parameter rootDegree degreeAtLeastTwo)] at sameIm
  have positive := (target_parameter_im_positive rootDegree degreeAtLeastTwo)
  rewrite [← sameIm] at positive
  exact (lt_irrefl 0) positive

/-- One original rootDegree-bounded source occurrence, without an asserted real-branch choice. -/
def sourceIndex : (sourceFrame rootDegree degreeAtLeastTwo).Index :=
  ⟨0, (by decide : 0 < 2).trans_le (sourceFrame rootDegree degreeAtLeastTwo).chamber.degreeAtLeastTwo⟩

/-- The original source owner with its own actual numerical root cache. -/
def sourceRoot : CoherentRoot.Chamber.Root (sourceFrame rootDegree degreeAtLeastTwo) (sourceIndex rootDegree
    degreeAtLeastTwo) :=
  CoherentRoot.Chamber.Root.ofOwner (sourceFrame rootDegree degreeAtLeastTwo) (sourceIndex rootDegree
      degreeAtLeastTwo)

/-- Retain the actual cubic path and numerical caches at every selected original occurrence. -/
def cubicTrace : Chamber.Trace (cubicPath rootDegree degreeAtLeastTwo) (sourceIndex rootDegree
    degreeAtLeastTwo) (sourceRoot rootDegree degreeAtLeastTwo) :=
  Chamber.Trace.build (cubicPath rootDegree degreeAtLeastTwo) (sourceIndex rootDegree degreeAtLeastTwo)
      (sourceRoot rootDegree degreeAtLeastTwo)

example (owners : Chamber.Trace.Owners
    (cubicPath rootDegree degreeAtLeastTwo) (sourceIndex rootDegree degreeAtLeastTwo)) :
    Chamber.Trace.ofPreparedOwners (sourceRoot rootDegree degreeAtLeastTwo) owners =
      cubicTrace rootDegree degreeAtLeastTwo :=
  Chamber.Trace.ofPreparedOwners_eq (sourceRoot rootDegree degreeAtLeastTwo) owners

/-- Restart the existing original cubic cache from its own first paid refined state. -/
def cubicRestart : CoherentRoot.Reconditioning (sourceRoot rootDegree degreeAtLeastTwo).certificate 0 :=
  CoherentRoot.Reconditioning.ofTarget (sourceRoot rootDegree degreeAtLeastTwo).certificate 0 1 (by decide)

example : Equivalence.NamedEquivalent (sourceRoot rootDegree degreeAtLeastTwo).certificate.value.name (cubicRestart
    rootDegree degreeAtLeastTwo).root.value.name :=
  (cubicRestart rootDegree degreeAtLeastTwo).namedEquivalent ((sourceFrame rootDegree degreeAtLeastTwo).input)

/-- Arithmetic before and after the nonstationary path retains two occurrences of that same original cubic branch. -/
def continuedProduct : Chamber.Arithmetic .mul (cubicTrace rootDegree degreeAtLeastTwo) (cubicTrace
    rootDegree degreeAtLeastTwo) :=
  Chamber.Arithmetic.ofTraces .mul (cubicTrace rootDegree degreeAtLeastTwo) (cubicTrace rootDegree
      degreeAtLeastTwo)

example : Equivalence.NamedEquivalent
    (NumericalArithmetic.channel .mul
      (cubicTrace rootDegree degreeAtLeastTwo).endpoint.certificate.value (cubicTrace rootDegree
          degreeAtLeastTwo).endpoint.certificate.value).name
    (continuedProduct rootDegree degreeAtLeastTwo).endpoint.result.toApproximation.toNamed := (continuedProduct
        rootDegree degreeAtLeastTwo).endpointEquivalent

example (independent : CoherentRoot.Chamber.Root (targetFrame rootDegree degreeAtLeastTwo) ((cubicPath rootDegree
    degreeAtLeastTwo).finalIndex (sourceIndex rootDegree degreeAtLeastTwo)))
    (arithmetic : CoherentRoot.Arithmetic .mul independent.certificate independent.certificate) :
    Equivalence.NamedEquivalent (continuedProduct rootDegree degreeAtLeastTwo).endpoint.result.toApproximation.toNamed
      arithmetic.result.toApproximation.toNamed :=
  (continuedProduct rootDegree degreeAtLeastTwo).compareEndpoint independent independent arithmetic

example {start finish : ChamberFrame} {index : start.Index} (root : CoherentRoot.Chamber.Root start index) :
    CoherentRoot.Chamber.StepOutcome finish root none := CoherentRoot.Chamber.acquireStep finish root none

example (prepared : Chamber.Arithmetic.EndpointPreparation (continuedProduct rootDegree
    degreeAtLeastTwo)) :
    Division.Prepared.Decision (NumericalArithmetic.channel .mul
      (cubicTrace rootDegree degreeAtLeastTwo).endpoint.certificate.value (cubicTrace rootDegree
          degreeAtLeastTwo).endpoint.certificate.value) := prepared.decide

/-- A distinct original source occurrence of the same degree-generic chamber. -/
def secondIndex : (sourceFrame rootDegree degreeAtLeastTwo).Index :=
  ⟨1, (by decide : 1 < 2).trans_le (sourceFrame rootDegree degreeAtLeastTwo).chamber.degreeAtLeastTwo⟩

/-- The distinct second branch retains its own original numerical owner cache. -/
def secondRoot : CoherentRoot.Chamber.Root (sourceFrame rootDegree degreeAtLeastTwo) (secondIndex rootDegree
    degreeAtLeastTwo) :=
  CoherentRoot.Chamber.Root.ofOwner (sourceFrame rootDegree degreeAtLeastTwo) (secondIndex rootDegree
      degreeAtLeastTwo)

/-- The actual same prepared coefficient path carries the second original occurrence separately. -/
def secondTrace : Chamber.Trace (cubicPath rootDegree degreeAtLeastTwo) (secondIndex rootDegree
    degreeAtLeastTwo) (secondRoot rootDegree degreeAtLeastTwo) :=
  Chamber.Trace.build (cubicPath rootDegree degreeAtLeastTwo) (secondIndex rootDegree degreeAtLeastTwo)
      (secondRoot rootDegree degreeAtLeastTwo)

/-- Ordered continued input pairs may give the same product without merging their original branch witnesses. -/
def orderedProduct : Chamber.Arithmetic .mul (cubicTrace rootDegree degreeAtLeastTwo) (secondTrace
    rootDegree degreeAtLeastTwo) :=
  Chamber.Arithmetic.ofTraces .mul (cubicTrace rootDegree degreeAtLeastTwo) (secondTrace rootDegree
      degreeAtLeastTwo)

/-- The reversed product retains the same two original occurrences in the opposite order. -/
def reversedProduct : Chamber.Arithmetic .mul (secondTrace rootDegree degreeAtLeastTwo) (cubicTrace
    rootDegree degreeAtLeastTwo) :=
  Chamber.Arithmetic.ofTraces .mul (secondTrace rootDegree degreeAtLeastTwo) (cubicTrace rootDegree
      degreeAtLeastTwo)

example : (sourceIndex rootDegree degreeAtLeastTwo) ≠ (secondIndex rootDegree degreeAtLeastTwo) := by
  intro same
  have equal := congrArg Fin.val same
  exact (by decide : (0 : Nat) ≠ 1) equal

example : Equivalence.NamedEquivalent (orderedProduct rootDegree
    degreeAtLeastTwo).endpoint.result.toApproximation.toNamed
    (reversedProduct rootDegree degreeAtLeastTwo).endpoint.result.toApproximation.toNamed :=
  (orderedProduct rootDegree degreeAtLeastTwo).productReverseEquivalent (reversedProduct rootDegree degreeAtLeastTwo)

/-- Emit one actual native regression stage before its finite computation. -/
private def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a scalar observation after its actual execution progress message. -/
@[noinline] private def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Execute actual numerical cache reuse on the nonstationary cubic path and its original restarted branch. -/
@[noinline] public def checkCubicCaches (operational : Bool := false) : IO Unit := do
  report "cubic-continuation: preparing original nonstationary parameter vertices"
  let firstVertex := sourceVertex rootDegree degreeAtLeastTwo
  let lastVertex := targetVertex rootDegree degreeAtLeastTwo
  unless firstVertex.value ≠ lastVertex.value do
    throw (IO.userError "cubic continuation lost its original nonstationary parameters")
  report "cubic-continuation: preparing the original source and target frames"
  let firstFrame := firstVertex.frame rootDegree degreeAtLeastTwo
  let lastFrame := lastVertex.frame rootDegree degreeAtLeastTwo
  report "cubic-continuation: preparing the original three-overlap path"
  let path : ChamberPath firstFrame lastFrame :=
    Progressive.Power.Unit.Move.Path.unitSmallMovePath firstVertex.unit lastVertex.unit rootDegree degreeAtLeastTwo
      ⟨Circuit.Point.unitCircuitSubdivision_small .first rootDegree degreeAtLeastTwo 0,
        (Circuit.Point.unitCircuitSubdivision_liftMargin .first rootDegree degreeAtLeastTwo 0).le⟩
  let steps ← evaluate fun _ => path.stepCount
  unless steps = 3 do
    throw (IO.userError "cubic continuation lost its original three-overlap step")
  let index : firstFrame.Index := ⟨0, (by decide : 0 < 2).trans_le firstFrame.chamber.degreeAtLeastTwo⟩
  let originalRoot := CoherentRoot.Chamber.Root.ofOwner firstFrame index
  report "cubic-continuation: reading original selected endpoint cache"
  let trace := Chamber.Trace.build path index originalRoot
  let endpoint := trace.endpoint
  let reading ← evaluate fun _ => endpoint.certificate.approximation.sample 0
  unless (lastFrame.owner (path.finalIndex index)).box.Contains reading do
    throw (IO.userError "continued cubic reading lost its original selected endpoint owner")
  report "cubic-continuation: reusing original paid cubic cache state"
  let restart := CoherentRoot.Reconditioning.ofTarget originalRoot.certificate 0 1 (by decide)
  let restarted ← evaluate fun _ => restart.root.approximation.sample 0
  let original := originalRoot.certificate.stateAt restart.paid.index
  unless restarted = original.box.anchor ∧ restart.paid.index ≥ 1 do
    throw (IO.userError "cubic reconditioning failed to reuse the actual paid original cache state")
  report "cubic-continuation: checking actual retained endpoint arithmetic"
  let product := Chamber.Arithmetic.ofTraces .mul trace trace
  unless product.endpoint.result.sample 0 = reading * reading do
    throw (IO.userError "continued arithmetic replaced its two retained original endpoint occurrences")
  report "cubic-continuation: reading actual production algebraic cache attachments"
  let restartedSidecar := restart.algebraic firstFrame.input
  let restartedReading ← evaluate fun _ => restartedSidecar.residual.source.sample 0
  unless restartedReading = restarted do
    throw (IO.userError "production reconditioning sidecar replaced the actual restarted sample program")
  let continuedSidecar := Chamber.Trace.Algebraic.ofTrace trace
  let continuedReading ← evaluate fun _ => continuedSidecar.endpoint.residual.source.sample 0
  unless continuedReading = reading do
    throw (IO.userError "production continuation sidecar replaced the actual retained endpoint cache")
  match operational with
  | true => do
    report "cubic-continuation: paying original before/after restart arithmetic"
    let before := CoherentRoot.Arithmetic.ofRoots .mul originalRoot.certificate originalRoot.certificate
    let after := CoherentRoot.Reconditioning.Arithmetic.ofRestarts before restart restart
    MultiplicityAdmission.checkAgreement
      (after.resultEquivalent firstFrame.input firstFrame.input) 1 2 ⟨1, by decide⟩
    report "cubic-continuation: retaining the distinct second original continued branch"
    let otherIndex : firstFrame.Index := ⟨1, (by decide : 1 < 2).trans_le firstFrame.chamber.degreeAtLeastTwo⟩
    unless index.val = 0 ∧ otherIndex.val = 1 ∧ path.finalIndex index ≠ path.finalIndex otherIndex do
      throw (IO.userError "continued coincident products lost their distinct original branch indices")
    let otherRoot := CoherentRoot.Chamber.Root.ofOwner firstFrame otherIndex
    let otherTrace := CoherentRoot.Chamber.Trace.build path otherIndex otherRoot
    let forward := Chamber.Arithmetic.ofTraces .mul trace otherTrace
    let backward := Chamber.Arithmetic.ofTraces .mul otherTrace trace
    report "cubic-continuation: paying coincident products with both original branch traces retained"
    MultiplicityAdmission.checkAgreement
      (forward.productReverseEquivalent backward) 2 3 ⟨1, by decide⟩
    report "cubic-continuation: restart arithmetic and distinct-branch coincident products paid"
  | false =>
    report "cubic-continuation: original path, branch, restart and arithmetic checked"

end

open Purelib.RootIsolation.Progressive.Power
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.System.FilePath (join)

/-- Pay the original independent target and robust endpoint through their actual saved numerical states.

The retained target frame supplies its complete isolation and elimination cache.
The endpoint keeps its own owner and certified channel; the existing indexed
comparison requests starts one and two at unit tolerance on those same inputs. -/
private def checkIndependentEndpoint {parameter : Canonical} (nonzeroTarget : parameter ≠ 0)
    (unit : Gaussian.Norm.Basic.normSq parameter = 1) (degree : Nat.Positive.RootDegree)
    (degreeTwo : 2 ≤ degree.value) (frame : Frame.Preparation.Prepared nonzeroTarget degree degreeTwo)
    (index : Fin degree.value) (robust : Unit.Owner.Preparation.Prepared nonzeroTarget unit degree degreeTwo index)
    {endpointIndex : (Unit.Frame.robustChamberFrame nonzeroTarget unit degree degreeTwo).Index}
    (endpoint : Chamber.Root (Unit.Frame.robustChamberFrame nonzeroTarget unit degree degreeTwo) endpointIndex)
    (sameIndex : Fin.cast (Unit.Frame.robustChamberFrame_degree nonzeroTarget unit degree degreeTwo)
      endpointIndex = index)
    (endpointSame : endpoint = Chamber.Root.ofOwner _ endpointIndex)
    (columns : ClearanceCheckpoint.Control IO) (winding : WindingCheckpoint.Control IO)
    (directory : System.FilePath) : IO Unit := do
  let targetRoot := certifiedName (frame.track index).val frame.input.degreePositive
  let equivalent : Equivalence.NamedEquivalent targetRoot.value.name endpoint.certificate.value.name :=
    Chamber.Power.robustEndpointEquivalent nonzeroTarget unit degree degreeTwo
      frame index targetRoot rfl robust endpoint sameIndex
  let request := equivalent.compare 1 2 1 (by decide)
  let targetElimination := Thunk.mk fun _ => FTA.Squarefree.Input.Elimination.ofCertificate
    frame.input frame.elimination frame.elimination_eq
  report "cubic-continuation: restoring original named independent-target payments"
  let targetSamples ← CoherentRootCheckpoint.namedSamples targetRoot frame.input targetElimination
    (by
      intro current epsilon positive
      change (frame.isolation.trackAt _).refine current epsilon positive = _
      rewrite [frame.isolation_eq, ← frame.input_eq]
      exact frame.input.isolation_trackAt_refine none _ current epsilon positive)
    columns winding (join directory "endpoint-identification/independent-target") [request.leftIndex]
  let targetEliminations :
      (input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial parameter degree)) →
        FTA.Squarefree.Input.Elimination input :=
    fun input => (FTA.Squarefree.Input.eq_of_polynomial frame.input input) ▸ targetElimination.get
  let endpointEliminations :=
    (congrArg (fun polynomial : CoherentRoot.GaussianPolynomial =>
      (input : FTA.Squarefree.Input polynomial) → FTA.Squarefree.Input.Elimination input)
      (Unit.Frame.robustChamberFrame_polynomial nonzeroTarget unit degree degreeTwo).symm) ▸
      targetEliminations
  let endpointInput := (Unit.Frame.robustChamberFrame nonzeroTarget unit degree degreeTwo).input
  let endpointElimination := Thunk.mk fun _ => endpointEliminations endpointInput
  report "cubic-continuation: restoring original named robust-endpoint payments"
  let endpointSamples ← CoherentRootCheckpoint.namedSamples endpoint.certificate endpointInput
    endpointElimination (Chamber.Root.refine_eq endpoint endpointSame) columns winding
    (join directory "endpoint-identification/trace-endpoint") [request.rightIndex]
  MultiplicityAdmission.checkAgreement
    (first := targetRoot.value.name) (second := endpoint.certificate.value.name) equivalent 1 2 ⟨1, by decide⟩
    (some targetSamples) (some endpointSamples) ⟨request, rfl⟩
  report "cubic-continuation: independent target and actual assignment trace endpoint paid from original saved states"

/-- Restore the nonstationary cubic trace and pay its original independent endpoint comparison.

The original parameter-one occurrence, next circuit vertex, three overlaps,
raw-owner assignment and robust target cache retain their existing numerical
stores. The named comparison keeps starts one and two and unit tolerance;
saved-only mode reports missing work through the original readers. -/
public def checkPreparedCubicEndpoint (directory : System.FilePath) (savedOnly : Bool := false)
    (inputDigest : Option (String → IO String) := none) : IO Unit := do
  let degree : Nat.Positive.RootDegree := ⟨3, by decide⟩
  have degreeTwo : 2 ≤ degree.value := by decide
  let source := sourceVertex degree degreeTwo
  let target := targetVertex degree degreeTwo
  unless source.value ≠ target.value do
    throw (IO.userError "prepared cubic continuation lost its original nonstationary parameters")
  let small := smallMove degree degreeTwo
  let nonzeroSource := nonzero_of_normSq_eq_one source.unit
  let nonzeroTarget := nonzero_of_normSq_eq_one target.unit
  let sourceFrame := Unit.Frame.robustChamberFrame nonzeroSource source.unit degree degreeTwo
  let sourceIndex : sourceFrame.Index := ⟨0, (by decide : 0 < 2).trans_le sourceFrame.chamber.degreeAtLeastTwo⟩
  let sourceDegreeIndex := Fin.cast
    (Unit.Frame.robustChamberFrame_degree nonzeroSource source.unit degree degreeTwo) sourceIndex
  let columns : ClearanceCheckpoint.Control IO := { savedOnly := savedOnly }
  let winding : WindingCheckpoint.Control IO := { savedOnly := savedOnly, inputDigest := inputDigest }
  report "cubic-continuation: reusing the original completed source owner"
  let sourceState ← CoherentRootCheckpoint.Power.source nonzeroSource source.unit degree degreeTwo sourceDegreeIndex
    { savedOnly := true } { savedOnly := true, inputDigest := inputDigest } directory
  let originalOwner := Unit.Owner.Preparation.fromSource
    nonzeroSource source.unit degree degreeTwo sourceDegreeIndex sourceState
  let sourcePrepared := Unit.Frame.Preparation.fromOwner nonzeroSource source.unit degree degreeTwo
    sourceIndex originalOwner
  let originalRoot := Chamber.Root.ofPreparedOwner sourceFrame sourceIndex sourcePrepared
  let movedIndex := Fin.cast (Unit.Move.Frame.unitMoveCountEq
    source.unit target.unit degree degreeTwo) sourceIndex
  let movedOwner := Unit.Move.Frame.Preparation.fromSource source.unit target.unit degree degreeTwo
    small sourceIndex sourcePrepared
  report "cubic-continuation: preparing the original target partition"
  InitialExtractionCheckpoint.withPowerFrame nonzeroTarget degree degreeTwo columns winding { savedOnly := savedOnly }
      (join directory "target-family") fun targetFrame => do
    report "cubic-continuation: restoring original transported raw-owner assignment"
    let assignment ← CoherentRootCheckpoint.Power.assignment source.unit target.unit degree degreeTwo small
      movedIndex targetFrame movedOwner columns winding savedOnly
      (join directory "matching-raw-owner-v1")
    let selected := assignment.selected
    let targetDegreeIndex := Fin.cast
      (Frame.Basic.chamberFrame_degree nonzeroTarget degree degreeTwo) selected
    let robustIndex := Fin.cast (Unit.Frame.Overlap.isolationRobustCountEq
      nonzeroTarget target.unit degree degreeTwo) selected
    report "cubic-continuation: restoring the original selected robust target owner"
    let robust ← CoherentRootCheckpoint.Power.ownerFromFrame nonzeroTarget target.unit degree degreeTwo
      targetDegreeIndex targetFrame columns winding
      (join directory "target-robust-source")
    let robustAtIndex : Unit.Owner.Preparation.Prepared nonzeroTarget target.unit degree degreeTwo
        (Fin.cast (Unit.Frame.robustChamberFrame_degree
          nonzeroTarget target.unit degree degreeTwo) robustIndex) := by
      have same : targetDegreeIndex = Fin.cast (Unit.Frame.robustChamberFrame_degree
          nonzeroTarget target.unit degree degreeTwo) robustIndex := by
        apply Fin.ext
        rfl
      exact same ▸ robust
    let robustOwner := Unit.Frame.Preparation.fromOwner nonzeroTarget target.unit degree degreeTwo
      robustIndex robustAtIndex
    let targetIndex : targetFrame.frame.Index :=
      Fin.cast (congrArg ChamberFrame.degree targetFrame.frame_eq.symm) selected
    let targetOwner : Owner.Local.Preparation.Prepared (targetFrame.frame.owner targetIndex) :=
      ⟨targetFrame.frame.owner targetIndex, rfl⟩
    let path := Unit.Move.Path.Preparation.fromAssignment source.unit target.unit degree degreeTwo
      small sourceIndex targetFrame assignment
    let trace : Chamber.Trace path sourceIndex originalRoot :=
      Chamber.Power.fromAssignment source.unit target.unit degree degreeTwo small sourceIndex originalRoot
        movedOwner targetFrame assignment targetOwner robustOwner
    let reading := trace.endpoint.certificate.approximation.sample 0
    unless trace.endpoint.track.initial.box.Contains reading ∧ path.stepCount = 3 do
      throw (IO.userError "prepared continuation lost its original endpoint owner or overlap occurrences")
    let product := Chamber.Arithmetic.ofTraces .mul trace trace
    unless product.endpoint.result.sample 0 = reading * reading do
      throw (IO.userError "prepared continuation replaced its repeated original endpoint occurrences")
    let attached := Chamber.Trace.Algebraic.ofTrace trace
    unless attached.endpoint.residual.source.sample 0 = reading do
      throw (IO.userError "prepared continuation attachment replaced the actual endpoint cache")
    have endpointIndex : Fin.cast (Unit.Frame.robustChamberFrame_degree
        nonzeroTarget target.unit degree degreeTwo) (path.finalIndex sourceIndex) = targetDegreeIndex := by
      change Fin.cast _ ((Unit.Move.Path.Preparation.fromAssignment source.unit target.unit
        degree degreeTwo small sourceIndex targetFrame assignment).finalIndex sourceIndex) = _
      rewrite [Unit.Move.Path.Preparation.fromAssignment_finalIndex]
      apply Fin.ext
      rfl
    have endpointSame : trace.endpoint = Chamber.Root.ofOwner _ (path.finalIndex sourceIndex) := by
      change (Chamber.Power.fromAssignment source.unit target.unit degree degreeTwo small sourceIndex
        originalRoot movedOwner targetFrame assignment targetOwner robustOwner).endpoint = _
      rewrite [Chamber.Power.fromAssignment_eq]
      rfl
    checkIndependentEndpoint nonzeroTarget target.unit degree degreeTwo targetFrame targetDegreeIndex robust
      trace.endpoint endpointIndex endpointSame columns winding directory

end TestPurelib.Riemann.RootReconditioning
