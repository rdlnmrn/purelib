module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Endpoints
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Data.List.DependentProduct

/-! # Ordered signed endpoint sections of the same retained local member

Given zero/unit observation caches precede the interpolation time. The
original dependent product retains both slots at every literal parent
occurrence, then each actual section is constructed once. The unchanged
source geometric/root chains derive every following link, including final
to first. At time one both actual endpoint Steps compare with the SAME
member blocks. These endpoint claims do not assert an interior integral,
primitive normalization or raw canonical cycle realization.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

section Observations

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish} {stage : Nat} {targets : CellEndpoints.Targets path stage}
    (prepared : PreparedParents covered floor targets)
    (zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)

/-- The GIVEN complete zero/unit observations and factories at every original source-parent occurrence.

The ordered dependent product preserves separate first and last slots even
when their coordinates coincide. Its data are observations supplied by the
original query consumers; the factory equations do not execute queries.
-/
@[expose] def EndpointObservations : Type _ :=
  DependentProduct parents (fun index =>
    ({ answer : CellModels.Observations frame (PreparedParent.liftedCell (parents[index.val]'index.isLt))
        (prepared.entry index).preparation.cell.models (prepared.entry index).preparation.query.requests 0 //
      answer = (prepared.entry index).preparation.query.observe frame 0 zeroInside.1 zeroInside.2 } ×
     { answer : CellModels.Observations frame (PreparedParent.liftedCell (parents[index.val]'index.isLt))
        (prepared.entry index).preparation.cell.models (prepared.entry index).preparation.query.requests 1 //
      answer = (prepared.entry index).preparation.query.observe frame 1 oneInside.1 oneInside.2 }))

namespace EndpointObservations

/-- Observe both original endpoint queries once per literal occurrence before selecting any interpolation time.

The SAME retained preparation supplies both query/model owners. Each
original six-channel answer is bound once and stored with its whole factory
law. Source preparation, requested stages and member geometry are unchanged;
this is genuine fresh endpoint-observation work, not endpoint-cache lookup.
-/
def build (prepared : PreparedParents covered floor targets)
    (zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1) :
    EndpointObservations prepared zeroInside oneInside :=
  DependentProduct.ofFn parents (fun index =>
    let retained := prepared.entry index
    let first := retained.preparation.query.observe frame 0 zeroInside.1 zeroInside.2
    let last := retained.preparation.query.observe frame 1 oneInside.1 oneInside.2
    ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩)

variable {prepared zeroInside oneInside}

/-- Read the same whole first observation and its factory at one bounded original occurrence. -/
@[expose] def first (observed : EndpointObservations prepared zeroInside oneInside) (index : Fin parents.length) :
    { answer : CellModels.Observations frame (PreparedParent.liftedCell (parents[index.val]'index.isLt))
        (prepared.entry index).preparation.cell.models (prepared.entry index).preparation.query.requests 0 //
      answer = (prepared.entry index).preparation.query.observe frame 0 zeroInside.1 zeroInside.2 } :=
  (DependentProduct.get parents observed index).1

/-- Read the same independent whole last observation and factory without rebuilding its query. -/
@[expose] def last (observed : EndpointObservations prepared zeroInside oneInside) (index : Fin parents.length) :
    { answer : CellModels.Observations frame (PreparedParent.liftedCell (parents[index.val]'index.isLt))
        (prepared.entry index).preparation.cell.models (prepared.entry index).preparation.query.requests 1 //
      answer = (prepared.entry index).preparation.query.observe frame 1 oneInside.1 oneInside.2 } :=
  (DependentProduct.get parents observed index).2

end EndpointObservations

end Observations

namespace StageAttempt.Requested.LocalMember

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat} {offset : Canonical}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)
    {zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1}
    {oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1}
    (observed : EndpointObservations source.prepared zeroInside oneInside)

/-- One actual per-time endpoint section pair at every unchanged original source occurrence. -/
@[expose] def StripSections (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  DependentProduct (parent :: parents) (fun index => EndpointSections cached index
    zeroInside (observed.first index).val (observed.first index).property
    oneInside (observed.last index).val (observed.last index).property time timeInside)

/-- Materialize each actual first/last section ONCE in literal source order from the GIVEN whole observation caches. -/
def stripSections (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    StripSections cached observed time timeInside :=
  DependentProduct.ofFn (parent :: parents) (fun index => cached.endpointSections index
    zeroInside (observed.first index).val (observed.first index).property
    oneInside (observed.last index).val (observed.last index).property time timeInside)

/-- The signed comparison between the two actual endpoint Steps at one following occurrence. -/
@[expose] def StripLink (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sections : StripSections cached observed time timeInside) (index : Fin (parent :: parents).length) : Type _ :=
  let left := DependentProduct.get (parent :: parents) sections index
  let right := DependentProduct.get (parent :: parents) sections (followingIndex parent parents index)
  NamedEquivalent left.2.2.val.root.value.name right.1.2.val.root.value.name

/-- A retained signed comparison at every actual following occurrence, with literal last-to-first closure. -/
@[expose] def StripLinks (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sections : StripSections cached observed time timeInside) : Type _ :=
  DependentProduct (parent :: parents) (StripLink cached observed time timeInside sections)

/-- Compare the two stored Steps at one literal occurrence without rebuilding their endpoint sections. -/
private def stripLink (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sections : StripSections cached observed time timeInside) (index : Fin (parent :: parents).length) :
    StripLink cached observed time timeInside sections index := by
  let next := followingIndex parent parents index
  let left : Variation.Point.Step (source.prepared.entry index).lastSample
      ((⟨time, 0⟩ : Canonical) * offset) :=
    (DependentProduct.get (parent :: parents) sections index).2.2.val
  let right : Variation.Point.Step (source.prepared.entry next).firstSample
      ((⟨time, 0⟩ : Canonical) * offset) :=
    (DependentProduct.get (parent :: parents) sections next).1.2.val
  exact ShiftedGeometry.followingSteps (parameter := parameter) (frame := frame) (basis := basis)
    (offset := (⟨time, 0⟩ : Canonical) * offset) (parent := parent) (parents := parents)
    (count := count) (floor := floor) (covered := covered) (path := chain.path)
    (stage := source.selected.stage) (targets := source.targets) (root := root)
    source.prepared chain roots index left right

/-- Derive all actual following signs from the original source geometry/root chain and the GIVEN section product.

following_point and followingEquivalent read only the unchanged original
chains, including their genuine return. Existing source-Step comparison
consumes the actual per-time Steps and their own refinements/admissions.
No query, Point, section, member or signed relation is supplied anew.
-/
def stripLinks (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1)
    (sections : StripSections cached observed time timeInside) : StripLinks cached observed time timeInside sections :=
  DependentProduct.ofFn (parent :: parents) (fun index => stripLink cached observed time timeInside sections index)

/-- The SAME stored ordered endpoint sections and their internally derived closed following-link product. -/
@[expose] def StripEndpointChain (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  (sections : StripSections cached observed time timeInside) × StripLinks cached observed time timeInside sections

/-- Bind one actual per-time endpoint product before constructing every link from those SAME retained Steps. -/
def stripEndpointChain (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    StripEndpointChain cached observed time timeInside :=
  let sections := cached.stripSections observed time timeInside
  let linked := cached.stripLinks observed time timeInside sections
  ⟨sections, linked⟩

/-- Every actual time-one endpoint pair agrees with the same retained original member block at its literal position. -/
@[expose] def StripEndpointSigns
    (sections : StripSections cached observed 1 oneInside) : Type _ :=
  DependentProduct (parent :: parents) (fun index =>
    let actual := DependentProduct.get (parent :: parents) sections index
    let block := DependentProduct.get (parent :: parents) cached.member.blocks index
    NamedEquivalent actual.1.2.val.root.value.name block.first.root.value.name ×
      NamedEquivalent actual.2.2.val.root.value.name block.last.root.value.name)

/-- Derive both time-one signs at every original occurrence from the GIVEN sections without a new advancement. -/
def stripEndpointSigns (sections : StripSections cached observed 1 oneInside) :
    StripEndpointSigns cached observed sections :=
  DependentProduct.ofFn (parent :: parents) (fun index =>
    cached.endpointSigns index zeroInside (observed.first index).val (observed.first index).property
      oneInside (observed.last index).val (observed.last index).property
      (DependentProduct.get (parent :: parents) sections index))

/-- Retain one actual time-one closed endpoint chain and all derived signs to its SAME member block endpoints. -/
def stripEndpointChainAtOne :
    (actual : StripEndpointChain cached observed 1 oneInside) × StripEndpointSigns cached observed actual.1 :=
  let actual := cached.stripEndpointChain observed 1 oneInside
  let signed := cached.stripEndpointSigns observed actual.1
  ⟨actual, signed⟩

end StageAttempt.Requested.LocalMember

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
