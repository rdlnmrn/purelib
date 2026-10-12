module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceParameters
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSourceParameters
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.Dyadic.SourceListResampling
open Purelib.Topology.Polygon

/-! Complete reversed source runs reuse all original fragment increments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries (SourceEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData sourceValues
  sourceDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (fragmentSourcePath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns (ResampledSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

/-- A physical source run descending within one retained parent. Explicit step inequalities also admit constant
junctions irrespective of their direction tag. -/
inductive ReverseSourceFragmentChain (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine) (width :
  InverseRootPolynomial.Coordinate) :
    List (PairedFragmentBlocks.OwnedFragment evaluated data otherData) → InverseRootPolynomial.Coordinate →
      InverseRootPolynomial.Coordinate → Prop
  /-- The empty descending source chain starts and finishes at the same retained parameter. -/ | nil (point :
    InverseRootPolynomial.Coordinate) :
    ReverseSourceFragmentChain entry
    width [] point point
  /-- Extend the original descending chain by a fragment with the identical source entry, adjacent terminal parameter
    and bounded descending steps. -/ | cons (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData)
      {rest : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)} {last :
        InverseRootPolynomial.Coordinate}
      (same : fragment.entry = entry)
      (descending : ∀ edge : Fin fragment.count, fragment.parameters edge.succ ≤ fragment.parameters edge.castSucc)
      (steps : ∀ edge : Fin fragment.count,
        fragment.parameters edge.castSucc - fragment.parameters edge.succ ≤ width)
      (tail : ReverseSourceFragmentChain
        entry width rest (fragment.parameters (Fin.last fragment.count)) last) :
      ReverseSourceFragmentChain entry
        width (fragment :: rest) (fragment.parameters 0) last

/-- Concatenate reversed original fragment parameters in reverse fragment order. -/
@[expose] def reverseSourceFragmentParameters : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData) →
  List InverseRootPolynomial.Coordinate
  | [] => []
  | fragment :: rest =>
    reverseSourceFragmentParameters rest
    ++ OwnedFragment.reversedSourceParameters fragment

namespace ReverseSourceFragmentChain
variable {entry : SourceEntry plan
  sample otherSample fine} {width first last : Coordinate}
  {fragments : List (OwnedFragment
    evaluated data otherData)}

/-- Reversing the retained descending fragment chain gives an ascending parameter chain between its original endpoints.
-/
theorem parameters_chain (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.ReverseSourceFragmentChain entry width
  fragments first last) :
    SourceResampling.Chain last
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.reverseSourceFragmentParameters fragments)
      first := by
  induction chain with
  | nil point => exact .nil point
  | cons fragment same descending steps tail ih =>
    exact Chain.append ih (OwnedFragment.reversed_source_chain fragment descending)

/-- Every reversed original source parameter step retains the common descending width bound. -/
theorem parameter_widths (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.ReverseSourceFragmentChain entry width
  fragments first last) :
    SourceResampling.widths last
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.reverseSourceFragmentParameters fragments)
      width := by
  induction chain with
  | nil point => trivial
  | cons fragment same descending steps tail ih =>
    apply SourceListResampling.widths_append ih
    rw [Chain.terminal_eq (tail.parameters_chain)]
    exact OwnedFragment.reversed_source_widths fragment width steps

/-- Reverse the cached source path as a whole. Group boundaries and stationary junctions remain in the exact parameter
and increment readbacks. -/
theorem source_readback (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.ReverseSourceFragmentChain entry width
  fragments first last) :
    PairedAreaReversal.reverseIncrements (FragmentFamilies.fragmentSourcePath fragments) =
      SourceListResampling.increments (PairedFragmentValues.sourceValues entry) last
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.reverseSourceFragmentParameters
        fragments) := by
  induction chain with
  | nil point => rfl
  | @cons fragment rest last same descending steps tail ih =>
    change PairedAreaReversal.reverseIncrements (CenteredPathIncrements.Sample.increments fragment.source ++
      FragmentFamilies.fragmentSourcePath rest) =
      SourceListResampling.increments (PairedFragmentValues.sourceValues entry) last
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.reverseSourceFragmentParameters rest ++
          OwnedFragment.reversedSourceParameters fragment)
    rw [PairedAreaReversal.reverseIncrements_append, SourceListResampling.increments_append, Chain.terminal_eq
      (tail.parameters_chain), ih]
    have read := (OwnedFragment.reversed_source_increments fragment).trans
      (congrArg (fun chosen : PairedFragmentQueries.SourceEntry plan sample otherSample fine =>
        SourceListResampling.increments (PairedFragmentValues.sourceValues chosen)
          (fragment.parameters (Fin.last fragment.count))
          (OwnedFragment.reversedSourceParameters fragment)) same)
    exact congrArg (fun values =>
      SourceListResampling.increments (PairedFragmentValues.sourceValues entry) last
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.reverseSourceFragmentParameters rest) ++
        values) read

end ReverseSourceFragmentChain

/-- Feed a complete descending physical run into the existing ascending resampling estimate using reversed cached
increments and the same source owner. -/
@[expose] def ResampledSourceRun.ofReverseFragments (entry : PairedFragmentQueries.SourceEntry plan sample otherSample
  fine)
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) (width :
      InverseRootPolynomial.Coordinate)
    (chain : ReverseSourceFragmentChain entry
      width fragments 1 0) :
    ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine :=
  { entry := entry
    parameters := reverseSourceFragmentParameters
      fragments
    width := width
    actual := PairedAreaReversal.reverseIncrements (FragmentFamilies.fragmentSourcePath fragments)
    actual_eq := chain.source_readback
    chain := chain.parameters_chain
    steps := chain.parameter_widths }

/-- The physical descending run approximates the negative reference area. The error budget is the same finite resampling
budget used for forward runs. -/
theorem ReverseSourceFragmentChain.conjugate_error
    {entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine}
    {fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)} {width :
      InverseRootPolynomial.Coordinate}
    (chain : ReverseSourceFragmentChain entry
      width fragments 1 0) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
      ((FragmentFamilies.fragmentSourcePath fragments).map ConjugateIncrementComparison.conjugateFirst) +
      PairedIncrementArea.area (entry.pair.1.map ConjugateIncrementComparison.conjugateFirst)) ≤
      16 * (PairedFragmentValues.sourceDensity entry)^2 * (max width ((1 / 2 :
        InverseRootPolynomial.Coordinate)^(plan.parents.depth + fine)))^2 := by
  have bound :=
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns.ResampledSourceRun.ofReverseFragments entry
    fragments width chain).accurate
  change Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
    ((PairedAreaReversal.reverseIncrements (FragmentFamilies.fragmentSourcePath fragments)).map
      ConjugateIncrementComparison.conjugateFirst) -
    PairedIncrementArea.area (entry.pair.1.map ConjugateIncrementComparison.conjugateFirst)) ≤ _ at bound
  rw [PairedAreaReversal.conjugate_area_reverseIncrements] at bound
  have negative (a b : InverseRootPolynomial.Gaussian) : -a - b = -(a + b) := by ring1
  rw [negative, Data.Gaussian.Norm.Basic.normSq_neg] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseFragmentRuns
