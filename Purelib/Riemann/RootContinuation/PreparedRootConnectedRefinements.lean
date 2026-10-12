module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement

public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

@[expose] public section

/-!
# Iterated root-connected prepared refinements

Endpoint-safe blocks retain the existing direct integration model.  A finite
bank of these blocks refines both its coordinate chain and its operational
root chain.  The construction remains total at every later finite stage.
This does not identify the resulting samples with an independently seeded
period program or modify that program's existing depth selector.
-/

namespace Purelib.Riemann.RootContinuation.PreparedRootConnectedRefinements

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement DirectPathChain)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named LiftedPoint)
open Purelib.Data.Rat in
/-- The exact rational carrier for retained root-connected refinement requests. -/
private abbrev Coordinate := Fraction.Rational

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- An ordered endpoint-safe block for each original parent edge.

Each block retains its exact parent owner and child list; the inductive tail preserves the original parent order. -/
inductive SafeRefinement : List (CenteredEdge curve differential) → Type 2
  /-- The empty original parent list carries no safe blocks. -/ | nil : SafeRefinement []
  /-- Prepend the endpoint-safe block of the exact original parent to its retained tail refinement. -/ | cons {parent :
    CenteredEdge curve differential} {parents : List (CenteredEdge curve differential)}
      (block : EndpointSafeBlock parent) (tail : SafeRefinement parents) : SafeRefinement (parent :: parents)

constructive_injectivity SafeRefinement

namespace SafeRefinement

/-- Read the original direct block refinement carried by the ordered endpoint-safe blocks. -/
def toDirect : {parents : List (CenteredEdge curve differential)} → SafeRefinement parents →
    DirectBlockRefinement parents
  | [], .nil => .nil
  | _ :: _, .cons block tail => .cons block.block tail.toDirect

open Purelib.Data.Rat in
/-- Build an endpoint-safe block for every original proper parent at the same positive diameter request. -/
def total (diameter : Fraction.Rational) (positive : 0 < diameter) :
    (parents : List (CenteredEdge curve differential)) → AllParentsProper parents → SafeRefinement parents
  | [], _ => .nil
  | parent :: parents, proper =>
      .cons (EndpointSafeBlock.total parent proper.1 diameter positive) (total diameter positive parents proper.2)

open Purelib.Riemann.Topology in
/-- Refine the original root-name chain through every retained safe block, preserving its exact endpoint names. -/
def rootChain : ∀ {parents : List (CenteredEdge curve differential)} {first last : Named}
    (refinement : SafeRefinement parents), RootChain parents first last →
      RootChain refinement.toDirect.children first last
  | [], _, _, .nil, .nil equivalent => .nil equivalent
  | _ :: _, _, _, .cons block tail, .cons _ entry remaining =>
      ((PreparedRefinementRootChains.EndpointSafeBlock.rootChain block).changeStart entry).append (tail.rootChain
        remaining)

end SafeRefinement

set_option genInjectivity false in
/-- An original proper prepared path with both its geometric chain and retained endpoint root-name chain.

The exact lifted endpoints, root names and ordered parent list remain indices and fields; geometric connection and
operational root agreement are retained separately. -/
structure RootedChain (firstPoint lastPoint : LiftedPoint) (firstRoot lastRoot : Named) where
  /-- The retained ordered list of original centered prepared edges. -/ parents : List (CenteredEdge curve differential)
  /-- Every retained parent has strictly ordered original endpoint parameters. -/ proper : AllParentsProper parents
  /-- The retained parent list forms a direct chain between the exact original lifted endpoints. -/ geometry :
    DirectPathChain parents (start := firstPoint) (finish := lastPoint)
  /-- The same retained parent list carries the original endpoint root-name chain. -/ roots : RootChain parents
    firstRoot lastRoot

constructive_injectivity RootedChain

namespace RootedChain

variable {firstPoint lastPoint : LiftedPoint} {firstRoot lastRoot : Named}

/-- Replace the original parent list by the exact children of a retained safe refinement, transporting both geometric
and root-name chains. -/
def ofRefinement (source : RootedChain (curve := curve) (differential := differential)
    firstPoint lastPoint firstRoot lastRoot) (refinement : SafeRefinement source.parents) :
    RootedChain (curve := curve) (differential := differential) firstPoint lastPoint firstRoot lastRoot where
  parents := refinement.toDirect.children
  proper := refinement.toDirect.childrenProper
  geometry := refinement.toDirect.refinedChain source.geometry
  roots := refinement.rootChain source.roots

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the original compatible constant-path refinement between the retained source cells and their exact refined
children. -/
def compatible (source : RootedChain (curve := curve) (differential := differential)
    firstPoint lastPoint firstRoot lastRoot) (refinement : SafeRefinement source.parents) :
    Basic.PathModel.CompatibleConstantPathRefinement
      (source.parents.map CenteredEdge.model) ((source.ofRefinement refinement).parents.map CenteredEdge.model) :=
  refinement.toDirect.toCompatible

open Purelib.Data.Rat
/-- Refine the retained rooted chain at the positive diameter request while preserving both original geometric endpoints
and root names. -/
def refine (source : RootedChain (curve := curve) (differential := differential)
    firstPoint lastPoint firstRoot lastRoot) (diameter : Fraction.Rational) (positive : 0 < diameter) :
    RootedChain (curve := curve) (differential := differential) firstPoint lastPoint firstRoot lastRoot :=
  source.ofRefinement (SafeRefinement.total diameter positive source.parents source.proper)

/-- Iterate the original rooted-chain refinement through the retained positive diameter schedule.

Stage zero is the exact supplied source; each successor refines the previous retained chain using that stage's original
diameter and positivity witness. -/
def iterate (source : RootedChain (curve := curve) (differential := differential)
    firstPoint lastPoint firstRoot lastRoot) (diameter : Nat → Fraction.Rational)
    (positive : ∀ index, 0 < diameter index) : Nat →
    RootedChain (curve := curve) (differential := differential) firstPoint lastPoint firstRoot lastRoot
  | 0 => source
  | index + 1 => (iterate source diameter positive index).refine (diameter index) (positive index)

end RootedChain

end Purelib.Riemann.RootContinuation.PreparedRootConnectedRefinements
