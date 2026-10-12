module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks
public import Purelib.Integration.Path.IncrementRestoration
import Mathlib.Tactic.Ring.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Energy of the literal restored cap blocks

The boundary potential includes the chart-to-retained-endpoint edge. This
keeps the actual restored path, including its merged incoming correction,
while accounting for every source and endpoint detour.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Integration.Path.IncrementArea (Summary traceArea)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {depth : Nat} {target energyTarget joining : Normalization.InverseRootPolynomial.Coordinate}

set_option genInjectivity false in
/-- An original cap energy block with retained source detours, restored endpoints and radial boundary potentials.

All source, chart and endpoint discrepancy bounds refer to the actual cached path and values. -/
structure RestoredEnergyBlock (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index
  box)
    (depth : Nat) (target energyTarget joining : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original cached chart energy block at the retained common depth. -/ raw :
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks.EnergyBlock sample depth target energyTarget
  /-- The original initial source primitive reading. -/ firstSource : Normalization.InverseRootPolynomial.Gaussian
  /-- The original final source primitive reading. -/ lastSource : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained restored initial endpoint value. -/ firstValue : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained restored final endpoint value. -/ lastValue : Normalization.InverseRootPolynomial.Gaussian
  /-- The original initial source and restored value satisfy the joining squared-norm allowance. -/ first_source :
    Data.Gaussian.Norm.Basic.normSq (firstSource - firstValue) ≤ joining
  /-- The original final restored value and source satisfy the joining squared-norm allowance. -/ last_source :
    Data.Gaussian.Norm.Basic.normSq (lastValue - lastSource) ≤ joining
  /-- The original initial chart-to-source discrepancy is at most four times the target. -/ first_chart :
    Data.Gaussian.Norm.Basic.normSq (raw.firstValue - firstSource) ≤ 4 * target
  /-- The original final source-to-chart discrepancy is at most four times the target. -/ last_chart :
    Data.Gaussian.Norm.Basic.normSq (lastSource - raw.lastValue) ≤ 4 * target
  /-- The original initial chart-to-restored endpoint discrepancy satisfies the target. -/ first_offset :
    Data.Gaussian.Norm.Basic.normSq (raw.firstValue - firstValue) ≤ target
  /-- The original final chart-to-restored endpoint discrepancy satisfies the target. -/ last_offset :
    Data.Gaussian.Norm.Basic.normSq (raw.lastValue - lastValue) ≤ target
  /-- The retained initial chart-to-endpoint squared discrepancy is at most one. -/ first_small :
    Data.Gaussian.Norm.Basic.normSq (raw.firstValue - firstValue) ≤ 1
  /-- The retained final chart-to-endpoint squared discrepancy is at most one. -/ last_small :
    Data.Gaussian.Norm.Basic.normSq (raw.lastValue - lastValue) ≤ 1
  /-- The retained original initial radial potential including its endpoint correction. -/ firstPotential :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained original final radial potential including its endpoint correction. -/ lastPotential :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The stored initial potential equals the exact original radial and chart-to-restored endpoint expression. -/
    first_potential : firstPotential = Path.IncrementRestoration.potential raw.firstRadial raw.firstValue firstValue
  /-- The stored final potential equals the exact original radial and chart-to-restored endpoint expression. -/
    last_potential : lastPotential = Path.IncrementRestoration.potential raw.lastRadial raw.lastValue lastValue
  /-- The cached original chart path summary including both actual source detours. -/ core : Path.IncrementArea.Summary
    ((raw.firstValue - firstSource) :: (raw.path ++ [lastSource - raw.lastValue]))

constructive_injectivity RestoredEnergyBlock

namespace RestoredEnergyBlock

/-- Read the actual restored original increment path, including its incoming source correction and final retained
endpoint correction. -/
@[expose] def path (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth
  target energyTarget joining) (previous : Normalization.InverseRootPolynomial.Gaussian) : List Gaussian :=
  (block.firstSource - previous) :: (((block.raw.firstValue - block.firstSource) ::
    (block.raw.path ++ [block.lastSource - block.raw.lastValue])) ++ [block.lastValue - block.lastSource])

/-- Build the finite summary of the exact original restored path using the cached core summary. -/
@[expose] def summary (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  depth target energyTarget joining) (previous : Normalization.InverseRootPolynomial.Gaussian) :
  Path.IncrementArea.Summary (block.path previous) :=
  Path.IncrementAreaReplacement.bracket block.core (block.firstSource - previous) (block.lastValue - block.lastSource)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock in
/-- The complete original restored path totals to its retained last value minus the supplied previous value. -/
theorem total (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth target
  energyTarget joining) (previous : Normalization.InverseRootPolynomial.Gaussian) :
    (block.summary previous).total = block.lastValue - previous := by
  have coreTotal : block.core.total = block.lastSource - block.firstSource := by
    rw [block.core.total_eq]
    change block.raw.firstValue - block.firstSource + Data.Gaussian.Norm.Sum.Basic.gaussianSum (block.raw.path ++
      [block.lastSource - block.raw.lastValue]) = _
    rw [Path.IncrementArea.sum_append, ← block.raw.summary.total_eq, block.raw.total_eq]
    change _ + (_ + (_ + 0)) = _
    ring1
  rw [summary, Path.IncrementAreaReplacement.bracket_total, coreTotal]
  ring1

/-- Read the original potential discrepancy and ribbon area at the incoming retained endpoint join. -/
@[expose] def joinError (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  depth target energyTarget joining) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) :
  Gaussian :=
  block.firstPotential - previousPotential - Path.BoundaryRibbon.area previous block.firstValue

/-- Combine the original raw energy error and source detour with the exact retained incoming-join discrepancy. -/
@[expose] def localError (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  depth target energyTarget joining) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) :
  Gaussian :=
  block.raw.error + Path.IncrementRestoration.detour block.raw.firstValue block.raw.lastValue block.firstSource
    block.lastSource block.firstValue block.lastValue previous -
    block.joinError previous previousPotential

/-- The original energy-minus-restored-boundary expression equals the retained local error exactly. -/
theorem discrepancy (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth
  target energyTarget joining) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) :
    block.raw.energy - (-Path.IncrementArea.traceArea previous (block.path previous) + block.lastPotential -
      previousPotential) =
      block.localError previous previousPotential := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.path, block.last_potential,
    Path.IncrementRestoration.restored_discrepancy block.raw.summary
    block.raw.firstValue block.raw.lastValue block.firstSource block.lastSource block.firstValue block.lastValue
      previous
    block.raw.firstRadial block.raw.lastRadial previousPotential block.raw.energy block.raw.total_eq]
  rw [Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.localError, block.raw.error_eq,
    Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.joinError, block.first_potential]

/-- The original restored local error is bounded by 1024 times the sum of its target and joining allowance. -/
theorem local_bound (block : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth
  target energyTarget joining) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian)
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    (gap : Data.Gaussian.Norm.Basic.normSq (block.firstValue - previous) ≤ joining)
    (joined : Data.Gaussian.Norm.Basic.normSq (block.joinError previous previousPotential) ≤ 80 * target + 2 *
      joining) :
    Data.Gaussian.Norm.Basic.normSq (block.localError previous previousPotential) ≤ 1024 * (target + joining) :=
  Path.IncrementRestoration.combined_bound targetNonnegative joinNonnegative block.raw.bounded
    (Path.IncrementRestoration.detour_bound targetNonnegative joinSmall block.first_source block.last_source
      block.first_chart block.last_chart gap) joined

/-- The original ordered block joins satisfy their retained endpoint-gap and boundary-potential bounds. -/
@[expose] def JoinsBounded : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  depth target energyTarget joining) → Normalization.InverseRootPolynomial.Gaussian →
  Normalization.InverseRootPolynomial.Gaussian → Prop
  | [], _, _ => True
  | head :: tail, previous, previousPotential => Data.Gaussian.Norm.Basic.normSq (head.firstValue - previous) ≤
    joining ∧
      Data.Gaussian.Norm.Basic.normSq (head.joinError previous previousPotential) ≤ 80 * target + 2 * joining ∧
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.JoinsBounded tail
        head.lastValue head.lastPotential

/-- Read the original first retained value and potential, using zero for an empty block list. -/
@[expose] def initial : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth
  target energyTarget joining) → Normalization.InverseRootPolynomial.Gaussian ×
  Normalization.InverseRootPolynomial.Gaussian
  | [] => (0, 0)
  | head :: _ => (head.firstValue, head.firstPotential)

/-- Read every original restored path while carrying its predecessor's exact retained terminal value. -/
@[expose] def paths : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth
  target energyTarget joining) → Normalization.InverseRootPolynomial.Gaussian → List (List
  Normalization.InverseRootPolynomial.Gaussian)
  | [], _ => []
  | head :: tail, previous => head.path previous ::
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.paths tail
    head.lastValue

/-- Read the original last retained endpoint value, preserving the supplied value for an empty list. -/
@[expose] def terminalValue : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  depth target energyTarget joining) → Normalization.InverseRootPolynomial.Gaussian →
  Normalization.InverseRootPolynomial.Gaussian
  | [], previous => previous
  | head :: tail, _ =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalValue tail
    head.lastValue

/-- Read the original last retained radial potential, preserving the supplied potential for an empty list. -/
@[expose] def terminalPotential : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock
  sample depth target energyTarget joining) → Normalization.InverseRootPolynomial.Gaussian →
  Normalization.InverseRootPolynomial.Gaussian
  | [], previous => previous
  | head :: tail, _ =>
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential tail
    head.lastPotential

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock in
set_option genInjectivity false in
/-- The complete original restored block connection with exact total, trace, energy and paid local-error list. -/
structure Connection (blocks : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock
  sample depth target energyTarget joining)) (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian)
  where
  /-- The finite summary of the complete original restored path concatenation. -/ summary : Path.IncrementArea.Summary
    (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.paths blocks previous).flatten
  /-- The retained complete path total is the original terminal value minus its supplied initial value. -/ total_eq :
    summary.total = Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalValue blocks
    previous - previous
  /-- The retained signed trace area of the complete original restored path. -/ trace :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The cached trace equals the exact complete original increment trace at its supplied initial value. -/ trace_eq :
    trace = Path.IncrementArea.traceArea previous
    (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.paths blocks previous).flatten
  /-- The retained sum of all actual original block energies. -/ energy : Normalization.InverseRootPolynomial.Gaussian
  /-- The stored energy equals the finite sum of the exact retained original raw energies. -/ energy_eq : energy =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map (fun block => block.raw.energy))
  /-- The retained imaginary energy divided by four is bounded below by minus the original block count times the energy
    target. -/ lower : -((blocks.length : Normalization.InverseRootPolynomial.Coordinate) * energyTarget) ≤ energy.im /
    4
  /-- The ordered retained original local energy-boundary errors. -/ errors : List
    Normalization.InverseRootPolynomial.Gaussian
  /-- There is exactly one retained original local error for each block. -/ count_eq : errors.length = blocks.length
  /-- The full original energy-minus-boundary potential expression equals the sum of the retained local errors. -/
    discrepancy : energy - (-trace +
    Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential blocks
    previousPotential - previousPotential) = Data.Gaussian.Norm.Sum.Basic.gaussianSum errors
  /-- Every original retained local error satisfies the same 1024-scaled target-plus-joining allowance. -/ bounded : ∀
    error ∈ errors, Data.Gaussian.Norm.Basic.normSq error ≤ 1024 * (target + joining)

constructive_injectivity Connection

namespace Connection

/-- Combine the original restored blocks recursively, retaining actual predecessor values, radial potentials and every
paid local error. -/
@[expose] def build (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1) :
    (blocks : List (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample depth target
      energyTarget joining)) → (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) →
    Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.JoinsBounded blocks previous
      previousPotential → Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.Connection
      blocks previous previousPotential
  | [], previous, previousPotential, _ => by
      refine ⟨Summary.build [], ?_, 0, rfl, 0, rfl, ?_, [], rfl, ?_, ?_⟩
      · change (0 : Normalization.InverseRootPolynomial.Gaussian) = previous - previous; ring1
      · change -((0 : Normalization.InverseRootPolynomial.Coordinate) * energyTarget) ≤ 0 / 4
        rw [show -((0 : Normalization.InverseRootPolynomial.Coordinate) * energyTarget) = 0 by ring1]; decide
      · change (0 : Normalization.InverseRootPolynomial.Gaussian) - (-0 + previousPotential - previousPotential) = 0;
          ring1
      · intro _ member; exact False.elim (List.not_mem_nil member)
  | head :: tail, previous, previousPotential, joins => by
      let rest :=
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.Connection.build
        targetNonnegative joinNonnegative joinSmall tail head.lastValue head.lastPotential joins.2.2
      let summary := (head.summary previous).append rest.summary
      let headTrace := (head.summary previous).area + Path.BoundaryRibbon.area previous (head.summary previous).total
      have headTraceEq : headTrace = Path.IncrementArea.traceArea previous (head.path previous) := by
        rw [Path.IncrementArea.traceArea_eq, ← (head.summary previous).area_eq, ← (head.summary previous).total_eq]
      refine ⟨summary, ?_, headTrace + rest.trace, ?_, head.raw.energy + rest.energy, ?_, ?_,
        head.localError previous previousPotential :: rest.errors, congrArg Nat.succ rest.count_eq, ?_, ?_⟩
      · change (head.summary previous).total + rest.summary.total =
          terminalValue tail head.lastValue
          - previous
        rw [head.total, rest.total_eq]; ring1
      · change _ = Path.IncrementArea.traceArea previous (head.path previous ++
          (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.paths tail
          head.lastValue).flatten)
        rw [Path.IncrementArea.traceArea_append, ← (head.summary previous).total_eq, head.total,
          show previous + (head.lastValue - previous) = head.lastValue by ring1, ← headTraceEq, ← rest.trace_eq]
      · change head.raw.energy + rest.energy = head.raw.energy + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun
          block => block.raw.energy))
        rw [rest.energy_eq]
      · have bound := Fraction.Order.Arithmetic.add_le_add_direct head.raw.lower rest.lower
        simp only [List.length_cons, Nat.cast_succ, Gaussian.Basic.add_im]
        exact (by ring1 : -(((tail.length : Normalization.InverseRootPolynomial.Coordinate) + 1) * energyTarget) =
          -energyTarget + -((tail.length : Normalization.InverseRootPolynomial.Coordinate) * energyTarget)).trans_le
          (bound.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))
      · change head.raw.energy + rest.energy - (-(headTrace + rest.trace) +
          Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential tail
          head.lastPotential - previousPotential) =
          head.localError previous previousPotential + Data.Gaussian.Norm.Sum.Basic.gaussianSum rest.errors
        rw [← head.discrepancy, ← rest.discrepancy, ← headTraceEq]
        ring1
      · intro error member
        rcases Data.List.Membership.mem_cons.mp member with equal | member
        · subst error; exact head.local_bound previous previousPotential targetNonnegative joinNonnegative joinSmall
            joins.1 joins.2.1
        · exact rest.bounded error member

variable {blocks : List (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock
  sample depth target energyTarget joining)} {previous previousPotential : Normalization.InverseRootPolynomial.Gaussian}

/-- The complete original energy-boundary discrepancy is bounded by the block count squared times the retained local
allowance. -/
theorem boundary_error (connection :
  Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.Connection blocks previous
  previousPotential) :
    Data.Gaussian.Norm.Basic.normSq (connection.energy - (-connection.trace +
      Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential blocks
      previousPotential - previousPotential)) ≤
      (blocks.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (1024 * (target + joining)) := by
  rw [connection.discrepancy]
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le connection.errors _ connection.bounded
  rw [connection.count_eq] at estimate
  exact estimate.trans_eq (by ring1)

end Connection
end RestoredEnergyBlock
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
