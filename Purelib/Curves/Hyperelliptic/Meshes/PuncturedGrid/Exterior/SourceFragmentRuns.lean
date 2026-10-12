module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Init.Data.Fin.Basic
import Init.Data.List.OfFn
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.SourceListResampling

@[expose] public section

/-! Read a complete source parent from its actual retained owned fragments.
The construction reuses their increments and preserves zero-length junctions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries (SourceEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData sourceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (fragmentSourcePath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateSourceRuns (ResampledSourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
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

namespace OwnedFragment

/-- The retained source parameters after each original fragment increment, excluding its initial point. -/
def sourceParameters (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) : List Coordinate :=
  List.ofFn (fun edge : Fin fragment.count => fragment.parameters edge.succ)

/-- The terminal parameter of the original fragment is its last retained parameter. -/
theorem source_parameters_terminal (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData) :
    SourceListResampling.terminal (fragment.parameters 0)
      (sourceParameters fragment) =
      fragment.parameters (Fin.last fragment.count) := SourceListResampling.terminal_ofFn _

/-- The original fragment source increments are exactly the parameterized increments of the supplied identical source
owner. -/
theorem source_increments_readback (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData)
    (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine) (same : fragment.entry = entry) :
    (CenteredPathIncrements.Sample.increments fragment.source) = SourceListResampling.increments
      (PairedFragmentValues.sourceValues entry)
      (fragment.parameters 0)
        (sourceParameters fragment)
        := by
  rw [CenteredPathIncrements.Sample.increments_raw fragment.source, ← SourceListResampling.increments_ofFn]
  rw [same]
  rfl

end OwnedFragment

/-- Geometric assembly of a single parent: identical source owner, adjacent parameter endpoints, forward order and the
actual mesh-width bound. -/
inductive SourceFragmentChain (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine) (width :
  InverseRootPolynomial.Coordinate) :
    List (PairedFragmentBlocks.OwnedFragment evaluated data otherData) → InverseRootPolynomial.Coordinate →
      InverseRootPolynomial.Coordinate → Prop
  /-- The empty source chain starts and finishes at the same retained parameter. -/ | nil (point :
    InverseRootPolynomial.Coordinate) :
    SourceFragmentChain entry width []
    point point
  /-- Extend a source chain by one forward fragment with the identical source owner, adjacent endpoint and paid
    parameter width. -/ | cons (fragment : PairedFragmentBlocks.OwnedFragment evaluated data otherData)
      {rest : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)} {last :
        InverseRootPolynomial.Coordinate}
      (same : fragment.entry = entry) (forward : fragment.forward = true)
      (steps : ∀ edge : Fin fragment.count,
        fragment.parameters edge.succ - fragment.parameters edge.castSucc ≤ width)
      (tail : SourceFragmentChain entry
        width rest (fragment.parameters (Fin.last fragment.count)) last) :
      SourceFragmentChain entry width
        (fragment :: rest) (fragment.parameters 0) last

/-- Concatenate the actual retained source parameter lists in fragment order. -/
def sourceFragmentParameters (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) : List
  Coordinate :=
  (fragments.map
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.sourceParameters).flatten

namespace SourceFragmentChain
variable {entry : SourceEntry plan
  sample otherSample fine} {width first last : Coordinate}
  {fragments : List (OwnedFragment
    evaluated data otherData)}

/-- The assembled retained fragment parameters form a complete ascending chain between the original endpoints. -/
theorem parameters_chain (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.SourceFragmentChain entry width fragments first
  last) :
    SourceResampling.Chain first
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.sourceFragmentParameters fragments) last :=
      by
  induction chain with
  | nil point => exact .nil point
  | @cons fragment rest last same forward steps tail ih =>
    have ordered (edge : Fin fragment.count) : fragment.parameters edge.castSucc ≤ fragment.parameters edge.succ := by
      have bound := fragment.ordered edge
      rw [forward] at bound
      exact bound
    exact Chain.append (SourceResampling.chain_ofFn fragment.parameters ordered) ih

/-- Every assembled source parameter step satisfies the common retained fragment width. -/
theorem parameter_widths (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.SourceFragmentChain entry width fragments first
  last) :
    SourceResampling.widths first
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.sourceFragmentParameters fragments) width
      := by
  induction chain with
  | nil point => trivial
  | @cons fragment rest last same forward steps tail ih =>
    have next : SourceResampling.widths
        (SourceListResampling.terminal (fragment.parameters 0)
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.sourceParameters
          fragment))
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.sourceFragmentParameters rest) width :=
          by
      rw
        [(Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.source_parameters_terminal
        fragment)]
      exact ih
    exact SourceListResampling.widths_append
      (SourceResampling.widths_ofFn fragment.parameters width steps) next

/-- Flattening the retained source samples changes neither increments nor primitive owners. Parameter concatenation
includes every junction entry. -/
theorem source_readback (chain :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.SourceFragmentChain entry width fragments first
  last) :
    FragmentFamilies.fragmentSourcePath fragments =
      SourceListResampling.increments (PairedFragmentValues.sourceValues entry) first
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.sourceFragmentParameters fragments) := by
  induction chain with
  | nil point => rfl
  | @cons fragment rest last same forward steps tail ih =>
    change (CenteredPathIncrements.Sample.increments fragment.source) ++ FragmentFamilies.fragmentSourcePath rest =
      SourceListResampling.increments (PairedFragmentValues.sourceValues entry) (fragment.parameters 0)
        ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.sourceParameters fragment)
          ++ Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.sourceFragmentParameters rest)
    rw [SourceListResampling.increments_append,
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.source_parameters_terminal
      fragment),
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.OwnedFragment.source_increments_readback
        fragment) entry same, ih]

end SourceFragmentChain

/-- Build the resampling input from cached fragment increments. All inputs beyond the existing fragments describe
geometry, not analytic accuracy. -/
def ResampledSourceRun.ofFragments (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine)
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) (width :
      InverseRootPolynomial.Coordinate)
    (chain : SourceFragmentChain entry width
      fragments 0 1) :
    ConjugateSourceRuns.ResampledSourceRun plan sample otherSample fine :=
  { entry := entry
    parameters := sourceFragmentParameters
      fragments
    width := width
    actual := FragmentFamilies.fragmentSourcePath fragments
    actual_eq := chain.source_readback
    chain := chain.parameters_chain
    steps := chain.parameter_widths }

/-- The run constructor consumes exactly the family's retained source path. -/
theorem ResampledSourceRun.ofFragments_actual (entry : PairedFragmentQueries.SourceEntry plan sample otherSample fine)
    (fragments : List (PairedFragmentBlocks.OwnedFragment evaluated data otherData)) (width :
      InverseRootPolynomial.Coordinate)
    (chain : SourceFragmentChain entry width
      fragments 0 1) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns.ResampledSourceRun.ofFragments entry
      fragments width chain).actual = FragmentFamilies.fragmentSourcePath fragments := rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceFragmentRuns
