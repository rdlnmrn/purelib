module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.Word.Parents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Data.List.OfFn.Basic
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Riemann.Integration.RectangularSharedPrimitives

/-! # The same retained fragment endpoint values and closed gap word

Each original endpoint view is read at both literal slots. Whole leaf
identities relate those caches to the same assigned lifted source, so the
ordered increment list agrees before any routing comparison. The actual
closing gap and every stationary/repeated role remain in the given word.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
  (RegularPrimitiveFragment RegularPrimitiveFragments RegularPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Integration.RectangularSharedPrimitives
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {frames : RootFrames base.bank.grid} {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
    {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
    {domains : FaceDomainBank frames base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
    {target tolerance : Rational} {points : List Canonical} {index : Nat} {numerator : CoefficientPolynomial}
    {budgets : FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : FaceSharedMeshes budgets numerics)

namespace FragmentSheets

variable {parent : CenteredEdge curve source} {partition : AxisPartition 0 1 (axes.parameters parent)}
    {request : LocalRequest parent count target}

/-- Read a pair's actual assigned bank at its two literal physical endpoints. -/
private def pairValue {interval : Interval}
    (pair : OccurrencePair (axes := axes) (partition := partition) (domains := domains)
      (request := request) interval) : Canonical :=
  SharedPrimitiveValues.atPoint (BankReadings.meshReadings pair.2 shared).readings pair.1.located.last -
    SharedPrimitiveValues.atPoint (BankReadings.meshReadings pair.2 shared).readings pair.1.located.first

/-- Both cached endpoint slots retain those exact assigned-bank values. -/
private theorem occurrence_value {interval : Interval}
    {fragment : RegularPrimitiveFragment axes parent partition interval}
    {assigned : SheetEntry fragment domains request} (kept : Occurrence shared assigned) :
    kept.terminal - kept.initial = pairValue shared ⟨fragment, assigned⟩ :=
  congrArg₂ (· - ·) (EndpointReadings.value_eq_old_atPoint kept.view 1)
    (EndpointReadings.value_eq_old_atPoint kept.view 0)

/-- The complete stored leaf pair supplies the same actual bounded assigned entry. -/
private theorem leaf_value {intervals : List Interval}
    {fragments : RegularPrimitiveFragments axes parent partition intervals}
    (entries : FragmentSheets domains request fragments) {position : Fin intervals.length}
    (leaf : Leaf shared entries position) :
    leaf.occurrence.terminal - leaf.occurrence.initial = pairValue shared (entries.at position) :=
  (occurrence_value shared leaf.occurrence).trans (congrArg (pairValue shared) leaf.pair_eq)

/-- The original finite endpoint table agrees with the given actual lifted-source spine. -/
private theorem source_table {intervals : List Interval}
    {fragments : RegularPrimitiveFragments axes parent partition intervals}
    {entries : FragmentSheets domains request fragments}
    (sources : LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries.LiftedSources mesh entries) :
    sources.values shared = List.ofFn (fun position : Fin intervals.length =>
      pairValue shared (entries.at position)) := by
  induction sources with
  | nil => rfl
  | @cons interval intervals head tail entry entries first remaining following =>
      have step : List.ofFn (fun position : Fin (interval :: intervals).length =>
          pairValue shared ((FragmentSheets.cons entry entries).at position)) =
          pairValue shared ⟨head, entry⟩ :: List.ofFn (fun position : Fin intervals.length =>
            pairValue shared (entries.at position)) :=
        (Data.List.OfFn.Basic.ofFn_succ (function := fun position : Fin (interval :: intervals).length =>
          pairValue shared ((FragmentSheets.cons entry entries).at position))).trans (congrArg₂ List.cons
          (congrArg (pairValue shared) (FragmentSheets.at_zero entry entries))
          (Data.List.OfFn.Basic.ofFn_congr fun position =>
            congrArg (pairValue shared) (FragmentSheets.at_succ entry entries position)))
      have headValue :=
        LiftedReadings.ClearGrid.RegularPrimitiveFragment.SheetEntry.LiftedSource.value_eq first shared
      exact (congrArg₂ List.cons headValue following).trans step.symm

namespace Word

variable {fragments : RegularPrimitiveFragments axes parent partition partition.intervals}
    {entries : FragmentSheets domains request fragments}
    {included : ∀ value ∈ PointBanks.RegularPrimitiveFragments.SheetEntries.points entries, value ∈ points}
    (kept : Word shared entries included)

/-- Every original cached fragment increment is the SAME lifted partial-endpoint reading, in literal order.

The proof uses both endpoint view slots, complete stored leaf identities
and the original finite table. It executes no Finish, query, lookup,
primitive or source producer and does not identify independent root Owners.
-/
theorem increments_eq_lifted
    (sources : LiftedReadings.ClearGrid.RegularPrimitiveFragments.SheetEntries.LiftedSources mesh entries) :
    kept.increments = sources.values shared := by
  have cached : kept.increments = List.ofFn (fun position : Fin partition.intervals.length =>
      pairValue shared (entries.at position)) :=
    Data.List.OfFn.Basic.ofFn_congr fun position =>
      leaf_value shared entries (leafAt shared entries kept.leaves position)
  exact cached.trans (source_table shared sources).symm

end Word

end FragmentSheets

namespace SplitSheets

/-- The original parent product reads the same ordered source fragments, retaining each actual whole parent block. -/
private theorem blocks_values {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
    (sources : LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries.LiftedSources mesh entries)
    (bank : Blocks shared entries) : increments shared entries bank = sources.values shared := by
  induction sources with
  | nil => rfl
  | cons first remaining following =>
      exact congrArg₂ List.append
        (FragmentSheets.Word.increments_eq_lifted shared bank.1.word first) (following bank.2)

namespace Closed

variable {parents : List (CenteredEdge curve source)} {splits : PrimitiveSplits axes parents}
    {fragments : RegularPrimitiveSplits (base := base) axes splits}
    {requests : RequestedParents count target parents} {entries : SplitSheets domains fragments requests}
    {point : LiftedPoint 2} {root : Named}
    {geometry : CenteredPathChain parents (start := point) (finish := point)} {roots : RootChain parents root root}
    {included : ∀ value ∈ PointBanks.RegularPrimitiveSplits.SheetEntries.points entries, value ∈ points}
    (kept : Closed shared entries geometry roots included)

/-- The whole original closed-word increment list is the literal same supplied lifted-source value list.

The unified cached Blocks reader forwards the original bank. A wholly
empty word uses its actual empty product and root comparison; no Point or
nonempty witness is fabricated. Every original fragment occurrence remains.
-/
theorem increments_eq_lifted
    (sources : LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries.LiftedSources mesh entries) :
    Closed.increments shared entries geometry roots kept = sources.values shared :=
  (Closed.increments_blocks shared entries geometry roots kept).symm.trans
    (blocks_values shared sources (Closed.blocks shared entries geometry roots kept))

/-- The actual ordered source readings equal the SAME complete outgoing-gap sum, including literal closing.

Only the given word's existing signed telescope is composed. Individual
jumps and primitive offsets remain unchanged and need not vanish.
-/
theorem lifted_sum_eq_gaps
    (sources : LiftedReadings.ClearGrid.RegularPrimitiveSplits.SheetEntries.LiftedSources mesh entries) :
    gaussianSum (sources.values shared) = gaussianSum (Closed.gaps shared entries geometry roots kept) :=
  (congrArg gaussianSum (Closed.increments_eq_lifted shared kept sources).symm).trans
    (Closed.telescope shared entries geometry roots kept)

end Closed

end SplitSheets

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
