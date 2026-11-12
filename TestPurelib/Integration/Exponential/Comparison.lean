module

import Purelib.System.IO
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
meta import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Comparison.Observation
import Purelib.Tactic.OperationalEquivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Integration.Exponential.Comparison
meta import Purelib.Integration.Exponential.Comparison
meta import Purelib.Integration.Exponential.Integrand
meta import Purelib.Integration.Exponential.Program
meta import Purelib.Integration.Program.Gaussian.Cached.Scale
meta import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Integration.Exponential.Geometry.Policy
meta import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Exponential.Integrand
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Geometry.Policy
import Purelib.Integration.Program.Gaussian.Cached.Scale
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Integration.Exponential.Selection
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Schedule.PositiveStride

namespace TestPurelib.Integration.Exponential.Comparison

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic (BitLaw)
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Comparison
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- The original integrand has two independently retained coefficient occurrences. -/
def leftIntegrand : Integrand := .add (.scale 2 .exponential) (.scale 3 .exponential)

/-- The second construction uses its own single computed coefficient. -/
def rightIntegrand : Integrand := .scale 5 .exponential

/-- Exact finite Gaussian arithmetic checks the normalized integrand identity. -/
theorem coefficients : leftIntegrand.coefficient = rightIntegrand.coefficient := by decide

/-- The first policy keeps its original fixed subdivision request. -/
def leftPolicy := Geometry.Policy.fixedCuts [1 / 2]

/-- The second policy retains a distinct alternating subdivision procedure. -/
def rightPolicy : Geometry.Policy := .alternating (.uniform 0 1) (Geometry.Policy.fixedCuts [1 / 3, 2 / 3])

/-- The first positive-stride schedule starts beyond zero and advances by two. -/
def leftSchedule : Schedule.PositiveStride := ⟨2, 1⟩

/-- The second schedule keeps a different start and stride. -/
def rightSchedule : Schedule.PositiveStride := ⟨1, 2⟩

/-- Construct the original left caches and scale their actual models at extra observation depth one. -/
def left := Realization.ofPolicy leftIntegrand leftPolicy leftSchedule 1

/-- Construct the independent right caches at its own extra observation depth. -/
def right := Realization.ofPolicy rightIntegrand rightPolicy rightSchedule 3

/-- Independently scheduled normalized integrands yield a comparison of their actual retained outputs. -/
def outputsCompare : NamedEquivalent left.output.name right.output.name := left.outputsEquivalent right coefficients

/-- The checked frontend lifts the actual integration comparison through its original arithmetic channels. -/
example : NamedEquivalent
    (CoherentNamed.add left.output
      (CoherentNamed.Coherence.exact 1)).name
    (CoherentNamed.add right.output
      (CoherentNamed.Coherence.exact 1)).name := by
  ccl_equiv [outputsCompare]

/-- All later original samples have the internally derived coefficient budget. -/
theorem laterSamples (common first second : Nat) (firstOrder : common ≤ first) (secondOrder : common ≤ second) :
    Norm.Basic.normSq ((left.integral.stage first).sample - (right.integral.stage second).sample) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius
        (Realization.comparisonScale leftIntegrand.coefficient) common :=
  left.samples_bound right coefficients common first second firstOrder secondOrder

/-- The original finite source integral keeps the Horner boundary subtraction by one. -/
theorem retainedBoundary (index : Nat) : (left.integral.stage index).sample =
    leftIntegrand.coefficient *
      (Purelib.Approximation.Gaussian.Exponential.Horner.Sample.sample 1
        ((Selection.selection leftPolicy leftSchedule index).depth + 1) - 1) := left.sample index

/-- Normalization preserves all original integrand evaluations, independently of the supplied reading. -/
theorem originalIntegrands (reading : Basic.Canonical) :
    leftIntegrand.evaluate reading = rightIntegrand.evaluate reading :=
  Integrand.evaluate_eq_of_coefficients coefficients reading

/-- Exact cancellation normalizes to zero without assuming any separation of original exponential readings. -/
theorem cancellation : (Integrand.add .exponential (.neg .exponential)).coefficient = 0 := by decide

/-- A finite request keeps the exact original left cache selected by its computed comparison. -/
theorem observationCache (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    (left.observe right coefficients firstStart secondStart target positive).leftCache =
      left.integral.stage
        (left.observe right coefficients firstStart secondStart target positive).comparison.leftIndex :=
  (left.observe right coefficients firstStart secondStart target positive).leftCache_eq

/-- Execute a finite comparison with different policies, source starts and observation schedules. -/
public def check : IO Unit := do
  let retainedLeft := left
  let retainedRight := right
  let observation := retainedLeft.observe retainedRight coefficients 3 7 (1 / 16) (by decide)
  unless observation.comparison.leftIndex ≥ 3 && observation.comparison.rightIndex ≥ 7 do
    throw (IO.userError "The comparison discarded an original requested starting stage")
  unless Norm.Basic.normSq (observation.leftCache.sample - observation.rightCache.sample) < (1 / 16) do
    throw (IO.userError "The retained original integration samples failed the requested bound")
  unless observation.leftCache.sample =
      (retainedLeft.integral.stage observation.comparison.leftIndex).sample do
    throw (IO.userError "The left retained cache failed its original-program readback")
  unless observation.rightCache.sample =
      (retainedRight.integral.stage observation.comparison.rightIndex).sample do
    throw (IO.userError "The right retained cache failed its original-program readback")
  let leftCursor := (ChannelCursor.initial retainedLeft.output).request 1 (by decide) 1
  let rightCursor := (ChannelCursor.initial retainedRight.output).request 1 (by decide) 2
  let scheduled := ChannelCursor.compareSchedules leftCursor rightCursor
    (BitLaw.ofEquivalent (retainedLeft.outputsEquivalent retainedRight coefficients))
    [⟨1 / 4, by decide, 1⟩, ⟨1 / 16, by decide, 1⟩] [⟨1 / 8, by decide, 3⟩]
  unless scheduled.sourceLeft.cursor.machine.emitted.length = 1 &&
      scheduled.sourceRight.cursor.machine.emitted.length = 2 &&
      scheduled.outputLeft.cursor.machine.emitted.length = 3 &&
      scheduled.outputRight.cursor.machine.emitted.length = 5 do
    throw (IO.userError "Exponential comparison discarded original prefixes or independent schedules")
  let sampled := scheduled.observe 3 7 (1 / 16) (by decide)
  unless sampled.comparison.leftIndex ≥ 3 && sampled.comparison.rightIndex ≥ 7 && sampled.residual < (1 / 16) do
    throw (IO.userError "Exponential cursor comparison failed its actual retained sample payment")
  Purelib.System.IO.println
    "Exponential integration cursors: prefixes 1/2 -> 3/5, sample starts 3/7 and caches retained"
  Purelib.System.IO.println
    (s!"Exponential integrand comparison passed at original stages {observation.comparison.leftIndex}/" ++
    s!"{observation.comparison.rightIndex}; original policies, coefficients and caches retained")

end TestPurelib.Integration.Exponential.Comparison
