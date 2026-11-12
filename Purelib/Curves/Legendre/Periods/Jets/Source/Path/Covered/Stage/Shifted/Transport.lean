module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries

/-! # Exact source-accuracy views of retained shifted requests

The original sufficient source request can be displayed at a whole equal
accuracy index. A shifted result materialized on that view transports back
to the same original source. Every endpoint Step, block, physical acquisition,
trace, joined geometry and target Request remains the retained original cache.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {first last : AccuracyRequest}
    (equal : first = last) (source : Requested covered chain current floor rootStage first)
    (view : Requested covered chain current floor rootStage last)
    (view_eq : view = source.castAccuracy equal)
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (target := target) view ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)

/-- View the SAME retained shifted request over its original source at an exactly equal whole accuracy index.

Equality elimination retains the original block family, both endpoint Steps,
full shifted acquisitions, materialized traces, joined geometry and globally
allocated target request. The operation does not execute any source or target
factory. It does not assert that two independent shifted factories agree.
-/
def ofSourceAccuracy :
    Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage := by
  cases view_eq
  cases equal
  exact retained

/-- The accuracy view preserves the entire original shifted-result tuple and every whole factory certificate. -/
theorem ofSourceAccuracy_heq : HEq (ofSourceAccuracy equal source view view_eq retained) retained := by
  cases view_eq
  cases equal
  rfl

/-- The source-accuracy view reads the SAME whole original block family, including all retained endpoint owners. -/
theorem ofSourceAccuracy_blocks :
    HEq (ofSourceAccuracy equal source view view_eq retained).blocks retained.blocks := by
  cases view_eq
  cases equal
  rfl

/-- The SAME retained joined geometry and original closed-chain factory remain intact under the exact view. -/
theorem ofSourceAccuracy_geometry :
    HEq (ofSourceAccuracy equal source view view_eq retained).geometry retained.geometry := by
  cases view_eq
  cases equal
  rfl

/-- The target's SAME independent selection, Request, global Targets, models and checking caches remain intact. -/
theorem ofSourceAccuracy_requested :
    HEq (ofSourceAccuracy equal source view view_eq retained).requested retained.requested := by
  cases view_eq
  cases equal
  rfl

/-- The same target's actual selected stage is identical under original source-accuracy elimination. -/
theorem ofSourceAccuracy_stage :
    (ofSourceAccuracy equal source view view_eq retained).requested.selected.stage =
      retained.requested.selected.stage := by
  cases view_eq
  cases equal
  rfl

/-- The whole original target Request, including its shape, chain, attempt, bank and checks, is retained. -/
theorem ofSourceAccuracy_request :
    HEq (ofSourceAccuracy equal source view view_eq retained).requested.request retained.requested.request := by
  cases view_eq
  cases equal
  rfl

/-- The complete original target preparation and its global Targets/model/query owners remain the SAME cache. -/
theorem ofSourceAccuracy_prepared :
    HEq (ofSourceAccuracy equal source view view_eq retained).requested.prepared retained.requested.prepared := by
  cases view_eq
  cases equal
  rfl

/-- The actual original target model is identical at EVERY stage of its SAME preparation family.

This is a readback of exact equality elimination on the retained shifted
factory. It executes no preparation-family callback or model construction,
and asserts no equality between independently acquired shifted results.
-/
theorem ofSourceAccuracy_model (channel : Fin 6) (stage : Nat) :
    model (ofSourceAccuracy equal source view view_eq retained).requested.request.covered
      (ofSourceAccuracy equal source view view_eq retained).requested.request.chain
      (ofSourceAccuracy equal source view view_eq retained).requested.request.attempt.preparationFamily
      channel stage =
    model retained.requested.request.covered retained.requested.request.chain
      retained.requested.request.attempt.preparationFamily channel stage := by
  cases view_eq
  cases equal
  rfl

/-- Carry the SAME target query-agreement operation back to the literal retained shifted Request.

Only whole source-accuracy equality is eliminated. All target preparation,
observation and parent indices are retained; no arbitrary-preparation or
coordinate identification is used and no query factory is executed.
-/
def ofSourceAccuracyQueries
    (queries : QueryAgreement (ofSourceAccuracy equal source view view_eq retained).requested.prepared) :
    QueryAgreement retained.requested.prepared := by
  cases view_eq
  cases equal
  exact queries

/-- The original target query operation is retained whole under exact source-accuracy elimination. -/
theorem ofSourceAccuracyQueries_heq
    (queries : QueryAgreement (ofSourceAccuracy equal source view view_eq retained).requested.prepared) :
    HEq (ofSourceAccuracyQueries equal source view view_eq retained queries) queries := by
  cases view_eq
  cases equal
  rfl

/-- Carry the SAME complete target acquisitions and Stage back to the literal retained shifted Request.

This is equality elimination on the original source-accuracy view. The
old target attempt, bank/checks/status, retained Commons, new unpaid
acquisitions and entire completed Stage remain the identical cached data.
No Ready retag, completion replay or canonical comparison is introduced.
-/
def ofSourceAccuracyCompletion
    (completed : Completion (ofSourceAccuracy equal source view view_eq retained).requested.request.attempt) :
    Completion retained.requested.request.attempt := by
  cases view_eq
  cases equal
  exact completed

/-- Exact source-accuracy elimination preserves the entire original target Completion cache heterogeneously. -/
theorem ofSourceAccuracyCompletion_heq
    (completed : Completion (ofSourceAccuracy equal source view view_eq retained).requested.request.attempt) :
    HEq (ofSourceAccuracyCompletion equal source view view_eq retained completed) completed := by
  cases view_eq
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
