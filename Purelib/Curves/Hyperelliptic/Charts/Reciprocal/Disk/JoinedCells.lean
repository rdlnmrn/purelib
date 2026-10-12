module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization

/-!
# Complete cap paths with explicit retained-reading junctions

Each corrected block keeps the complete fine path. The concatenated summary
includes all internal and inter-block areas, and its total telescopes to the
actual final reading minus the supplied initial reading.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank Budget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells (CorrectedCell)

variable {genus count index depth readingIndex floor : Nat} {curve :
  HyperellipticCurve genus}
  {differential : Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace JoinedCells.ComparedCell

/-- The original retained cap-cell total satisfies the parent's stage-independent slope and comparison ceiling. -/
theorem cap_uniform_bound {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell data edge}
    {comparison : ArcSamples.Data regular cell} (compared : ParentCells.ComparedCell comparison source capSample depth)
    (budget : ParentBank.Budget data) (bounded : comparison.scale ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ 2 * (budget.slope + budget.scale) := by
  have widthNonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct cell.ordered.le
  have widthLe : edge.right.parameter - edge.left.parameter ≤ 1 := by
    simpa only [(show (1 : InverseRootPolynomial.Coordinate) - 0 = 1 from by decide), -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.sub_le_sub_direct edge.right.inside.2 edge.left.inside.1
  have squareLe : (edge.right.parameter - edge.left.parameter) ^ 2 ≤ 1 := by
    simpa only [pow_two, Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.mul_le_mul_direct widthLe widthLe widthNonnegative (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
  have scaleLe := Geometric.Basic.quarterRadius_le_scale budget.nonnegative index
  calc
    _ ≤ 2 * (budget.slope + Geometric.Basic.quarterRadius budget.scale index) *
        (edge.right.parameter - edge.left.parameter) ^ 2 := ComparedCell.cap_bound compared budget bounded
    _ ≤ 2 * (budget.slope + budget.scale) * 1 := Fraction.Order.Arithmetic.mul_le_mul_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl scaleLe) (by decide))
      squareLe (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg budget.slope_nonnegative budget.nonnegative))
    _ = _ := Fraction.Field.mul_one_direct _

end JoinedCells.ComparedCell

namespace JoinedCells

variable {tolerance : Coordinate}

-- Preserve the original JoinedCells.JoinedCells nominal path.
/-- Read the original full cap paths with their actual endpoint and incoming-junction corrections attached. -/
@[expose] def correctedPairs : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {owners : ParentOwners.Owners bank} →
    (requests : ParentEndpoints.EndpointRequests (tolerance / 4) floor owners) → (cells : ParentPaths.ComparedCells
      source capSample depth bank) →
    EndpointRequests.EvaluationData (readingIndex := readingIndex) requests cells → InverseRootPolynomial.Gaussian →
      List (List InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, _, .nil, .nil, _, _ => []
  | _, _, _, .cons _ rest, .cons cell cells, readings, previous =>
      ((cell.sample.firstValue - readings.1.firstValue + (readings.1.firstValue - previous)) ::
        (cell.capPath ++ [readings.1.lastValue - cell.sample.lastValue]), cell.capPath) ::
          correctedPairs rest cells
            readings.2 readings.1.lastValue

end JoinedCells

-- Preserve the original JoinedCells.JoinedCells nominal path.
set_option genInjectivity false in
/-- A cached complete cap path with the original endpoint-reading connectors retained.

Every corrected block keeps its full fine path; the summary includes all internal and cross terms and telescopes to the
actual final reading minus the supplied initial value. -/
structure JoinedCells {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges} {owners : ParentOwners.Owners bank}
    {tolerance : InverseRootPolynomial.Coordinate} (requests : ParentEndpoints.EndpointRequests (tolerance / 4) floor
      owners)
    (cells : ParentPaths.ComparedCells source capSample depth bank)
    (readings : EndpointRequests.EvaluationData (readingIndex := readingIndex) requests cells)
    (previous : InverseRootPolynomial.Gaussian) (bound : InverseRootPolynomial.Coordinate) where
  /-- The cached corrected and original cap-path pairs in retained cell order. -/ pairs : List (List
    InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The pairs are exactly the original paths with their actual retained endpoint corrections. -/ pairs_eq : pairs =
    JoinedCells.correctedPairs requests cells readings previous
  /-- The cached pair count equals the original covered-edge count. -/ length_eq : pairs.length = edges.length
  /-- The uncorrected projection preserves exactly the original complete cap path. -/ original_paths : (pairs.map
    Prod.snd).flatten = (cells.pairs.map Prod.snd).flatten
  /-- The cached corrected path summary including original internal excursions and block cross terms. -/ summary :
    IncrementArea.Summary (pairs.map Prod.fst).flatten
  /-- The cached actual final endpoint reading of the original cell bank. -/ lastValue : InverseRootPolynomial.Gaussian
  /-- The final value is exactly the readback of the original retained endpoint evaluations. -/ lastValue_eq : lastValue
    = EndpointRequests.lastValue requests cells readings previous
  /-- The corrected path total is the actual original final reading minus the supplied incoming value. -/ total_eq :
    summary.total = lastValue - previous
  /-- Each actual corrected block retains paid area and total discrepancies and both original magnitude bounds. -/
    estimates : ∀ pair ∈ pairs,
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤ 24 *
      tolerance * bound + 16 * tolerance ^ 2 ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ tolerance ∧
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 * (bound +
      tolerance) ∧ Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 *
      (bound + tolerance)

constructive_injectivity JoinedCells

namespace JoinedCells

variable {tolerance : Coordinate}

-- Preserve the original JoinedCells.JoinedCells nominal path.
/-- Reuse the original compared cells and endpoint readings, then cache each corrected block and its aggregate path
summary. -/
@[expose] def build (budget : ParentBank.Budget data) (nonnegative : 0 ≤ tolerance) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
      {owners : ParentOwners.Owners bank} →
    (requests : ParentEndpoints.EndpointRequests (tolerance / 4) floor owners) → (cells : ParentPaths.ComparedCells
      source capSample depth bank) →
    (readings : EndpointRequests.EvaluationData (readingIndex := readingIndex) requests cells) → (previous :
      InverseRootPolynomial.Gaussian) →
    bank.Bounded budget.scale → EndpointRequests.GapsSmall requests cells readings previous (tolerance / 4) →
    JoinedCells requests cells readings previous (2 *
      (budget.slope + budget.scale))
  | _, _, _, .nil, .nil, _, previous, _, _ =>
      ⟨[], rfl, rfl, rfl, IncrementArea.Summary.build [], previous, rfl, (Data.Gaussian.Basic.sub_self previous).symm,
        fun _ member => False.elim (List.not_mem_nil member)⟩
  | _, _, _, .cons request rest, .cons cell cells, readings, previous, bounded, small => by
      let corrected := CorrectedCell.build cell readings.1 (readings.1.firstValue - previous)
      let tail := build budget nonnegative
        rest cells readings.2 readings.1.lastValue bounded.2 small.2
      let path := corrected.first :: (cell.capPath ++ [corrected.last])
      have headBound := Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCells.ComparedCell.cap_uniform_bound cell
        budget bounded.1
      have originalBound : Data.Gaussian.Norm.Basic.normSq cell.capSummary.total ≤ 2 * (2 * (budget.slope +
        budget.scale) + tolerance) := by
        have boundNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
          (add_nonneg budget.slope_nonnegative budget.nonnegative)
        exact headBound.trans ((le_add_of_nonneg_right nonnegative).trans (by
          simpa only [_root_.one_mul, -eq_self, -iff_self] using
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
                decide : (1 : InverseRootPolynomial.Coordinate) ≤ 2)
              (add_nonneg boundNonnegative nonnegative)))
      refine ⟨(path, cell.capPath) :: tail.pairs, ?_, congrArg Nat.succ tail.length_eq, ?_,
        corrected.summary.append tail.summary, tail.lastValue, tail.lastValue_eq, ?_, ?_⟩
      · rw [tail.pairs_eq]; rfl
      · change cell.capPath ++ (tail.pairs.map Prod.snd).flatten = cell.capPath ++ (cells.pairs.map Prod.snd).flatten
        rw [tail.original_paths]
      · change corrected.summary.total + tail.summary.total = _
        rw [corrected.total, tail.total_eq, readings.1.increment_eq]
        ring1
      · intro pair member
        rcases Data.List.Membership.mem_cons.mp member with same | member
        · subst pair
          have areaLe := corrected.area_error nonnegative small.1 headBound
          have totalLe := corrected.total_error small.1
          have correctedBound := corrected.total_bound small.1 headBound
          rw [corrected.summary.area_eq, cell.capSummary.area_eq] at areaLe
          rw [corrected.summary.total_eq] at totalLe correctedBound
          rw [cell.capSummary.total_eq] at totalLe
          rw [cell.capSummary.total_eq] at originalBound
          exact ⟨areaLe, totalLe, correctedBound, originalBound⟩
        · exact tail.estimates pair member

end JoinedCells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
