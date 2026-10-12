module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.List.Control
public import Purelib.Data.Int.Decimal
public import Purelib.Data.Range
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic

public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Geometry.Rational.Box.Refinement
import Init.Data.Int.Basic
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.Range Purelib.Data.List

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.Data.Rat

open Purelib.Data.Rat.Bounds

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Polynomial.Clearance.Box.Line.Elimination

open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Derivative

open Purelib.Polynomial.Elimination.Axis

open Purelib.Polynomial.Power.Gaussian

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.RootIsolation

open Purelib.RootIsolation.Newton.Search

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

open Purelib.RootIsolation.State

section
public section

/-!
Minimal native root-refinement diagnostic, independent of the generated
period module tree.  The displayed radicand and root box are taken from the
first generated B cell.  Every box premise is checked at runtime; this is a
numerical bottleneck test, not a substitute for running the actual period.
Run under an explicit SIGKILL timeout and systemd memory bound.

`quotient ROOT_BITS` additionally exercises the ordinary division-ready root
and exact-one quotient at squared target `4^(-ROOT_BITS)`.  It separates
initialization, refinement, witness selection and ball construction without
loading any generated certificate bank.  It is a root/quotient microbenchmark,
not a prepared-path or period replay test.

`phases STEP_COUNT` separates each accepted checked-Newton refinement into
rounded-centre preparation, band selection, winding and clearance construction.
It retains the checked state between steps and preserves the ordinary finite
proposal order.  It deliberately measures the generic clearance baseline and
does not run a fallback after rejected proposals.

`compare STEP_COUNT` compares the generic and direct quadratic clearances on
the same accepted boxes, alternating timing order.  Both routes run the shared
exact checker; every accepted box is compared and the retained state is the
direct result.  This is not an end-to-end period benchmark.
-/

namespace QuadraticRefinementHarness

/-- The exact Gaussian parameter with real part seventeen eighths and imaginary part minus two. -/
@[expose] def parameter : Data.Gaussian.Basic.Canonical := ⟨17 / 8, -2⟩

/-- The displayed dyadic-centered rational box used as the initial quadratic-root request. -/
@[expose] def initialBox : Rational.Box :=
  let center : Data.Gaussian.Basic.Canonical :=
    ⟨Fraction.Cast.fromInt 1745966715789 /
        Fraction.Cast.fromInt 1099511627776,
      Fraction.Cast.fromInt (-692410576148) /
        Fraction.Cast.fromInt 1099511627776⟩
  Affine.centeredSquare center (1 / 16) (by decide)

/-- Check box shape, all four boundary determinants and winding before constructing the retained quadratic-root owner.
-/
@[expose] def owner? (_token : Unit) : Option (SquareRootContinuationChain.Owner parameter) :=
  let box := initialBox
  if proper : box.xLower < box.xUpper ∧ box.yLower < box.yUpper then
    if left : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0 then
      if right : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0 then
        if bottom : QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0 then
          if top : QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0 then
            if winding : Winding.Box.Basic.quadrupledBoxWinding
                (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) box = 4 then
              some (ExactQuadraticOwnerClearance.directOwnerOfBox
                parameter (by decide) box proper left right bottom top winding)
            else none
          else none
        else none
      else none
    else none
  else none

/-- Print and flush one root-refinement diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining the timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α :=
  pure (work ())

/-- The actual generic coefficient process, isolated from path construction and summation. Timing barriers keep the pure
work inside its measured IO interval; the requested radius is checked on the resulting ball. -/
@[expose] def quotient (bits : Nat) : IO Unit := do
  report "quadratic quotient: checking displayed first-B root box"
  let start ← IO.monoMsNow
  let some owner ← evaluate fun _ => owner? ()
    | throw (IO.userError "initial root box rejected")
  let target := Geometric.Basic.quarterRadius 1 bits
  have positive : 0 < target :=
    Geometric.Basic.quarterRadius_pos (by decide) bits
  let coefficient :=
    let root := owner.certificate owner.parameterNonzero
    CoherentNamed.div
      (Coherence.exact 1) root.value root.apart
  let initial ← evaluate fun _ => coefficient.name.state
  let initialized ← IO.monoMsNow
  report s!"quadratic quotient: box check and initialization={initialized - start} ms; target bits={bits}"
  let state ← evaluate fun _ => coefficient.name.process.refine initial target positive
  let refined ← IO.monoMsNow
  report s!"quadratic quotient: refinement={refined - initialized} ms"
  let sample ← evaluate fun _ => (coefficient.name.process.witness state).val
  let sampled ← IO.monoMsNow
  report
    s!"quadratic quotient: witness={sampled - refined} ms; denominator bits=({sample.re.den.log2}, \
      {sample.im.den.log2})"
  let ball ← evaluate fun _ => coefficient.name.process.ball state
  unless ball.radiusSq < target do
    throw (IO.userError "quotient ball exceeds its requested squared radius")
  let finish ← IO.monoMsNow
  report s!"quadratic quotient: checked ball={finish - sampled} ms; total={finish - start} ms"

/-- Small exact regressions for empty caches, retained entries, repeated lookups, and requests beyond the displayed
cache. No large index is needed to exercise the uncached fallback. -/
@[expose] def cache : IO Unit := do
  let some owner ← evaluate fun _ => owner? ()
    | throw (IO.userError "initial root box rejected")
  for (count, index) in [(0, 0), (0, 2), (4, 0), (4, 3), (2, 3)] do
    let entries := StateCache.buildPrefix count
      (StateCache.first owner.track)
    let observed ← evaluate fun _ =>
      StateCache.read owner.track index entries
    let repeated ← evaluate fun _ =>
      StateCache.read owner.track index entries
    let expected ← evaluate fun _ => CoherentRoot.state owner.track index
    let coordinates := fun (box : Rational.Box) =>
      (box.xLower, box.xUpper, box.yLower, box.yUpper)
    unless coordinates observed.box = coordinates expected.box ∧
        coordinates repeated.box = coordinates expected.box ∧
        observed.clearance.bound = expected.clearance.bound do
      throw (IO.userError "finite cache changed a canonical root state")
    report s!"quadratic cache: {count} entries, requested index {index}; exact and repeated reads passed"

/-- Report the six ordered rounded Newton proposals and their exact box checks.

Each report records positivity, strict containment, target accuracy and winding; rejected proposals establish no global
impossibility. -/
@[expose] def diagnose {ambient : Rational.Box}
    (current : WindingOne.Basic.WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) ambient)
    (epsilon : Fraction.Rational) : IO Unit := do
  let elimination := QuadraticAxisElimination.quadraticAxisElimination parameter
  let polynomial := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo
  let mut proposal : Data.Gaussian.Basic.Canonical :=
    ⟨(current.box.xLower + current.box.xUpper) / 2,
      (current.box.yLower + current.box.yUpper) / 2⟩
  for index in [:6] do
    let center := Gaussian.Grid.Box.roundedCenter current.box epsilon (2 * index) proposal
    let margin := min (center.re - current.box.xLower)
      (min (current.box.xUpper - center.re)
        (min (center.im - current.box.yLower) (current.box.yUpper - center.im)))
    let radius := min (epsilon / 8) (margin / 4)
    if positive : 0 < radius then
      let band := Band.selectedBand elimination center radius positive
      report
        s!"proposal {index}: radius={radius.num}/{radius.den}; strict={decide (band.box.StrictInterior current.box)}, \
          accurate={decide (band.box.diagonalSq ≤ epsilon ^ 2)}, \
          winding={Purelib.Polynomial.Winding.Box.Basic.quadrupledBoxWinding polynomial band.box}"
    else report s!"proposal {index}: nonpositive radius={radius.num}/{radius.den}"
    proposal := Data.Gaussian.Basic.value (Newton.Basic.newtonCenter polynomial center)

/-- Diagnostic version of the exact candidate checks, returning their actual certified state. Winding is retained with
its specification equality so the timing and construction do not evaluate it twice. -/
@[expose] def phasedCenter {ambient : Rational.Box}
    (current : Raw.RawWindingState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) ambient)
    (epsilon : Fraction.Rational) (center : Data.Gaussian.Basic.Canonical) :
    IO (Option (RootIsolation.Refinement current epsilon)) := do
  let polynomial := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo
  let elimination := QuadraticAxisElimination.quadraticAxisElimination parameter
  let margin := min (center.re - current.box.xLower)
    (min (current.box.xUpper - center.re)
      (min (center.im - current.box.yLower) (current.box.yUpper - center.im)))
  let radius := min (epsilon / 8) (margin / 4)
  if positive : 0 < radius then
    let start ← IO.monoMsNow
    let bandData ← evaluate fun _ =>
      (⟨Band.selectedBand elimination center radius positive, rfl⟩ :
        { value : Band.Basic.BandBox center radius //
          value = Band.selectedBand elimination center radius positive })
    let band := bandData.val
    have bandEq : band = Band.selectedBand elimination center radius positive := bandData.property
    let selected ← IO.monoMsNow
    report s!"phases: band={selected - start} ms"
    if strict : band.box.StrictInterior current.box then
      if accurate : band.box.diagonalSq ≤ epsilon ^ 2 then
        let winding ← evaluate fun _ =>
          (⟨Winding.Box.Basic.quadrupledBoxWinding polynomial band.box, rfl⟩ :
            { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding polynomial band.box })
        let checked ← IO.monoMsNow
        report s!"phases: winding={checked - selected} ms; value={winding.val}"
        if accepted : winding.val = 4 then
          let refined ← evaluate fun _ =>
            let nested := (Geometry.Rational.Box.Refinement.StrictInterior.refines strict).trans current.refinesAmbient
            let left : Line.Basic.VerticalLineClearance polynomial ambient band.box.xLower := by
              simpa only [bandEq] using Band.selectedBandLeftClearance elimination ambient center positive
            let right : Line.Basic.VerticalLineClearance polynomial ambient band.box.xUpper := by
              simpa only [bandEq] using Band.selectedBandRightClearance elimination ambient center positive
            let bottom : Line.Basic.HorizontalLineClearance polynomial ambient band.box.yLower := by
              simpa only [bandEq] using Band.selectedBandBottomClearance elimination ambient center positive
            let top : Line.Basic.HorizontalLineClearance polynomial ambient band.box.yUpper := by
              simpa only [bandEq] using Band.selectedBandTopClearance elimination ambient center positive
            ({ state :=
                { box := band.box
                  refinesAmbient := nested
                  proper := band.proper positive
                  clearance := Lines.boundaryOfLines (left.restrict nested)
                    (right.restrict nested) (bottom.restrict nested) (top.restrict nested)
                  rawWindingFour := winding.property.symm.trans accepted
                  ambientLeftClearance := left
                  ambientRightClearance := right
                  ambientBottomClearance := bottom
                  ambientTopClearance := top }
               strict := strict
               accurate := accurate } : RootIsolation.Refinement current epsilon)
          let cleared ← IO.monoMsNow
          report s!"phases: clearances={cleared - checked} ms; accepted total={cleared - start} ms"
          return some refined
  return none

/-- Time the ordered checked Newton stages while retaining each accepted root state.

The finite six-proposal search stops on rejection or a zero derivative and preserves the original rounding and update
order. -/
@[expose] def phases (count : Nat) : IO Unit := do
  let some owner ← evaluate fun _ => owner? ()
    | throw (IO.userError "initial root box rejected")
  let polynomial := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo
  let mut current := owner.track.initial
  for index in [:count] do
    let epsilon := AccuracyRadius.accuracyRadius (CoherentRoot.stepTarget owner.track index)
    report s!"phases: root step {index + 1}"
    let mut proposal : Data.Gaussian.Basic.Canonical :=
      ⟨(current.box.xLower + current.box.xUpper) / 2, (current.box.yLower + current.box.yUpper) / 2⟩
    let mut found := false
    for attempt in [:6] do
      let start ← IO.monoMsNow
      let center ← evaluate fun _ => Gaussian.Grid.Box.roundedCenter current.box epsilon (2 * attempt) proposal
      let rounded ← IO.monoMsNow
      report s!"phases: proposal {attempt + 1}; rounding={rounded - start} ms"
      match ← phasedCenter current.raw epsilon center with
      | some accepted =>
          current := accepted.state
          found := true
          break
      | none =>
          if Data.Gaussian.Basic.value (Evaluation.derivativeEval polynomial center) = 0 then
            break
          let beforeNewton ← IO.monoMsNow
          proposal ← evaluate fun _ => Data.Gaussian.Basic.value (Newton.Basic.newtonCenter polynomial center)
          let afterNewton ← IO.monoMsNow
          report s!"phases: Newton update={afterNewton - beforeNewton} ms"
    unless found do throw (IO.userError "phased checked proposals rejected; total fallback not run")

/-- Compare both certified constructors on identical requests. The generic route is retained only as an explicit
diagnostic baseline. -/
@[expose] def compare (count : Nat) : IO Unit := do
  let some owner ← evaluate fun _ => owner? ()
    | throw (IO.userError "initial root box rejected")
  let elimination := QuadraticAxisElimination.quadraticAxisElimination parameter
  let direct := Owner.quadraticAxisClearances parameter
  let generic := AxisClearances.canonical elimination
  let mut current := owner.track.initial
  let mut genericTotal := 0
  let mut directTotal := 0
  for index in [:count] do
    let epsilon := AccuracyRadius.accuracyRadius (CoherentRoot.stepTarget owner.track index)
    let measure := fun clearances => do
      let start ← IO.monoMsNow
      let some accepted ← evaluate fun _ =>
          Attempt.attempt elimination current.raw epsilon clearances
        | throw (IO.userError "checked proposals rejected; total fallback not run")
      let finish ← IO.monoMsNow
      pure (accepted, finish - start)
    let ((baseline, genericMs), (optimized, directMs)) ←
      if index % 2 = 0 then do
        let baseline ← measure generic
        let optimized ← measure direct
        pure (baseline, optimized)
      else do
        let optimized ← measure direct
        let baseline ← measure generic
        pure (baseline, optimized)
    let coordinates := fun (box : Rational.Box) =>
      (box.xLower, box.xUpper, box.yLower, box.yUpper)
    unless coordinates baseline.state.box = coordinates optimized.state.box do
      throw (IO.userError "clearance strategy changed the selected box")
    genericTotal := genericTotal + genericMs
    directTotal := directTotal + directMs
    current := optimized.state
    report s!"compare: step {index + 1}; generic={genericMs} ms, direct={directMs} ms; exact same box"
  report s!"compare: totals generic={genericTotal} ms, direct={directTotal} ms"

/-- Time the original shared refiner or its finite checked shortcut from the retained root owner.

The shortcut branch reports its failed proposals and stops without invoking an unrelated fallback. -/
@[expose] def trial (count : Nat) (shared : Bool) : IO Unit := do
  report "quadratic: checking displayed first-B root box"
  let some owner := owner? () | throw (IO.userError "initial root box rejected")
  let owner := if shared then
      Owner.ofState owner.parameterNonzero
        owner.track.initial
    else owner
  let elimination := QuadraticAxisElimination.quadraticAxisElimination parameter
  let mut current := owner.track.initial
  for index in [:count] do
    let epsilon := AccuracyRadius.accuracyRadius
      (CoherentRoot.stepTarget owner.track index)
    report s!"quadratic: requesting step {index + 1}, epsilon denominator bits={epsilon.den.log2}"
    let start ← IO.monoMsNow
    if shared then
      current := owner.track.refine current epsilon
        (AccuracyRadius.accuracyRadius_pos
          (CoherentRoot.stepTarget_positive owner.track index))
    else
      let some accepted := Attempt.attempt elimination current.raw epsilon
        | do
          diagnose current epsilon
          throw (IO.userError "checked shortcut rejected; fallback intentionally not run")
      current := accepted.state
    report
      s!"quadratic: accepted; box denominator bits={current.box.xLower.den.log2}, clearance denominator \
        bits={current.clearance.bound.den.log2}"
    let finish ← IO.monoMsNow
    report s!"quadratic: step {index + 1} completed in {finish - start} ms"

/-- Exercise the public transported owner, including zero displacement and a distinct nearby radicand. Report the
checked shortcut separately so a slow total fallback is not mistaken for a successful proposal. -/
@[expose] def transport : IO Unit := do
  let some owner := owner? () | throw (IO.userError "initial root box rejected")
  let delta := Geometric.dyadicSquareRadius
    owner.track.initial.clearance.bound / 2
  for target in [parameter, parameter + (⟨delta, 0⟩ : Data.Gaussian.Basic.Canonical)] do
    if nonzero : target ≠ 0 then
      if small : Data.Gaussian.Norm.Basic.normSq (parameter - target) <
          owner.track.initial.clearance.bound then
        let start ← IO.monoMsNow
        let raw := SquareRootContinuation.transportedRawState
          owner.track.initial small
        let checked := Attempt.attempt
          (QuadraticAxisElimination.quadraticAxisElimination target)
          raw 1
          (Owner.quadraticAxisClearances target)
        report s!"quadratic transport: unchanged={decide (target = parameter)}; shortcut accepted={checked.isSome}"
        let transported := owner.advance nonzero small
        report
          s!"quadratic transport: public owner diagonal denominator \
            bits={transported.track.initial.box.diagonalSq.den.log2}; \
            strict={decide (transported.track.initial.box.StrictInterior owner.track.initial.box)}"
        let epsilon := 1 / Fraction.Cast.fromInt 1024
        let refined := transported.track.refine transported.track.initial epsilon
          (by decide)
        report s!"quadratic transport: next refinement accurate={decide (refined.box.diagonalSq ≤ epsilon ^ 2)}"
        let finish ← IO.monoMsNow
        report s!"quadratic transport: completed in {finish - start} ms"
      else throw (IO.userError "nearby move failed its exact clearance check")
    else throw (IO.userError "nearby radicand vanished")

end QuadraticRefinementHarness

/-- Parse the requested cache, quotient, transport or finite-refinement diagnostic mode. -/
@[expose] def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["cache"] => QuadraticRefinementHarness.cache
  | ["quotient", bits] =>
      match Purelib.Data.String.toNat? bits with
      | some bits => QuadraticRefinementHarness.quotient bits
      | none => throw (IO.userError "root bits must be a natural number")
  | ["transport"] => QuadraticRefinementHarness.transport
  | ["phases", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => QuadraticRefinementHarness.phases count
      | none => throw (IO.userError "step count must be a natural number")
  | ["compare", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => QuadraticRefinementHarness.compare count
      | none => throw (IO.userError "step count must be a natural number")
  | [count] =>
      match Purelib.Data.String.toNat? count with
      | some count => QuadraticRefinementHarness.trial count false
      | none => throw (IO.userError "count must be a natural number")
  | ["shared", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => QuadraticRefinementHarness.trial count true
      | none => throw (IO.userError "count must be a natural number")
  | _ => throw (IO.userError
    "usage: quadratic_refinement_harness [shared] STEP_COUNT | phases STEP_COUNT | compare STEP_COUNT | transport | \
      quotient ROOT_BITS | cache")

end
