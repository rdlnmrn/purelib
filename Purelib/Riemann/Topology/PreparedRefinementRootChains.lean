module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints

public import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Root-connected actual direct refinements

The coordinate chain and the retained root-child spine are consumed together.
Their displayed start locations also locate every preceding endpoint.  The
cached fixed-box budget then supplies actual root agreement at every join,
including the first and last coarse queries.  No root witness is extracted
from a propositional list-membership proof.
-/

namespace Purelib.Riemann.Topology.PreparedRefinementRootChains

open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (Location)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

/-- The original executable Gaussian name carrier for retained root readings. -/
abbrev Named := Purelib.Approximation.Gaussian.Name.Basic.Named
/-- An original Gaussian point with a retained two-sheet index. -/
abbrev LiftedPoint := Purelib.Geometry.Path.Gaussian.Lifted.Basic.LiftedPoint 2

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- An ordered prepared-edge chain whose original root names are joined by retained operational equivalences.

The empty chain retains its endpoint comparison. Each nonempty step compares the incoming name with the original child
start and continues from that child's exact finish name. -/
inductive RootChain : List (CenteredEdge curve differential) → Named → Named → Type 2
  /-- An empty child list retains the original operational equivalence between its two endpoint names. -/ | nil {first
    last : Named} (equivalent : Equivalence.NamedEquivalent first last) : RootChain [] first last
  /-- Prepend an original prepared child with its retained incoming root-name comparison and the chain continuing from
    its exact finish name. -/ | cons (child : CenteredEdge curve differential)
      {children : List (CenteredEdge curve differential)} {first last : Named}
      (entry : Equivalence.NamedEquivalent first (child.edge.rootName 0 child.edge.baseInside))
      (tail : RootChain children (child.edge.rootName 1 (by decide)) last) :
      RootChain (child :: children) first last

constructive_injectivity RootChain

namespace RootChain

open Purelib.Approximation.Gaussian in
/-- Compose a retained incoming name equivalence with the first comparison of the original root chain. -/
def changeStart : ∀ {children : List (CenteredEdge curve differential)} {first middle last : Named},
    Equivalence.NamedEquivalent first middle → RootChain children middle last → RootChain children first last
  | [], _, _, _, equivalent, .nil finish => .nil (equivalent.trans finish)
  | _ :: _, _, _, _, equivalent, .cons child entry tail => .cons child (equivalent.trans entry) tail

/-- Concatenate two retained root chains at their exact common middle name, preserving the original child order. -/
def append : ∀ {firstChildren secondChildren : List (CenteredEdge curve differential)}
    {first middle last : Named}, RootChain firstChildren first middle →
      RootChain secondChildren middle last → RootChain (firstChildren ++ secondChildren) first last
  | [], _, _, _, _, .nil equivalent, second => second.changeStart equivalent
  | _ :: _, _, _, _, _, .cons child entry tail, second => .cons child entry (tail.append second)

end RootChain

/-- Recover the original geometric chain's start location from retained pointwise subedge relations and the exact final
location. -/
private def startLocation {parent : CenteredEdge curve differential} :
    ∀ {children : List (CenteredEdge curve differential)} {first last : LiftedPoint},
      DirectPathChain children (start := first) (finish := last) → RootSubedgeBlock parent children →
        Location parent last.coordinate → Location parent first.coordinate
  | [], _, _, .nil _, .nil, last => last
  | _ :: _, _, _, .cons child _, .cons head _, _ =>
      ⟨head.start.fraction, head.start.inside, head.start.point_eq.trans child.edge.point_zero⟩

open Purelib.Riemann.RootContinuation in
/-- Construct an original root-name chain from the retained geometric chain and pointwise subedge certificates.

The parent budget compares equal geometric points at every junction. Exact first and last parent locations determine the
endpoint names, and the original child relations retain each sheet comparison. -/
private def rootChainOfSpines {parent : CenteredEdge curve differential} (budget : ParentBudget parent.edge) :
    ∀ {children : List (CenteredEdge curve differential)} {first last : LiftedPoint},
      DirectPathChain children (start := first) (finish := last) → RootSubedgeBlock parent children →
      (firstLocation : Location parent first.coordinate) → (lastLocation : Location parent last.coordinate) →
        RootChain children (parent.edge.rootName firstLocation.fraction firstLocation.inside)
          (parent.edge.rootName lastLocation.fraction lastLocation.inside)
  | [], _, _, .nil _, .nil, first, last =>
      .nil (PreparedRefinementRootEndpoints.samePointEquivalent budget first.fraction last.fraction first.inside
        last.inside
        (first.point_eq.trans last.point_eq.symm))
  | _ :: _, _, _, .cons child chain, .cons head roots, first, last =>
      let next := startLocation chain roots last
      let finish := head.location 1 (by decide)
      let endpoint := (PreparedRefinementRootEndpoints.samePointEquivalent budget next.fraction finish.fraction
        next.inside finish.inside
        ((next.point_eq.trans child.edge.point_one.symm).trans finish.point_eq.symm)).trans (head.equivalent 1 (by
          decide))
      let tail := rootChainOfSpines budget chain roots next last
      let entry := (PreparedRefinementRootEndpoints.samePointEquivalent budget first.fraction head.start.fraction
        first.inside head.start.inside
        (first.point_eq.trans (head.start.point_eq.trans child.edge.point_zero).symm)).trans head.start.rootEquivalent
      .cons child entry (tail.changeStart endpoint.symm)

/-- Recover the original geometric chain's start location from retained pointwise subedge relations and the exact final
location. -/
def startLocationForBlock {parent : CenteredEdge curve differential} :
    ∀ {children : List (CenteredEdge curve differential)} {first last : LiftedPoint},
      DirectPathChain children (start := first) (finish := last) → RootSubedgeBlock parent children →
        Location parent last.coordinate → Location parent first.coordinate
  | [], _, _, .nil _, .nil, last => last
  | _ :: _, _, _, .cons child _, .cons head _, _ =>
      ⟨head.start.fraction, head.start.inside, head.start.point_eq.trans child.edge.point_zero⟩

open Purelib.Riemann.RootContinuation in
/-- Construct an original root-name chain from the retained geometric chain and pointwise subedge certificates.

The parent budget compares equal geometric points at every junction. Exact first and last parent locations determine the
endpoint names, and the original child relations retain each sheet comparison. -/
def rootChainFromSpines {parent : CenteredEdge curve differential} (budget : ParentBudget parent.edge) :
    ∀ {children : List (CenteredEdge curve differential)} {first last : LiftedPoint},
      DirectPathChain children (start := first) (finish := last) → RootSubedgeBlock parent children →
      (firstLocation : Location parent first.coordinate) → (lastLocation : Location parent last.coordinate) →
        RootChain children (parent.edge.rootName firstLocation.fraction firstLocation.inside)
          (parent.edge.rootName lastLocation.fraction lastLocation.inside)
  | [], _, _, .nil _, .nil, first, last =>
      .nil (PreparedRefinementRootEndpoints.samePointEquivalent budget first.fraction last.fraction first.inside
        last.inside
        (first.point_eq.trans last.point_eq.symm))
  | _ :: _, _, _, .cons child chain, .cons head roots, first, last =>
      let next := startLocationForBlock chain roots last
      let finish := head.location 1 (by decide)
      let endpoint := (PreparedRefinementRootEndpoints.samePointEquivalent budget next.fraction finish.fraction
        next.inside finish.inside
        ((next.point_eq.trans child.edge.point_one.symm).trans finish.point_eq.symm)).trans (head.equivalent 1 (by
          decide))
      let tail := rootChainFromSpines budget chain roots next last
      let entry := (PreparedRefinementRootEndpoints.samePointEquivalent budget first.fraction head.start.fraction
        first.inside head.start.inside
        (first.point_eq.trans (head.start.point_eq.trans child.edge.point_zero).symm)).trans head.start.rootEquivalent
      .cons child entry (tail.changeStart endpoint.symm)

namespace EndpointSafeBlock

open Purelib.Riemann.RootContinuation in
/-- Read the original root-name chain through every retained child of an endpoint-safe block.

The exact parent start and finish names are retained, together with the original block geometry, budget and pointwise
subedge comparisons. -/
def rootChain {parent : CenteredEdge curve differential} (safe : EndpointSafeBlock parent) :
    RootChain safe.block.children (parent.edge.rootName 0 parent.edge.baseInside)
      (parent.edge.rootName 1 (by decide)) :=
  rootChainFromSpines safe.budget safe.block.chain (PreparedSubedgeRootQueries.EndpointSafeBlock.subedges safe)
    ⟨0, parent.edge.baseInside, parent.edge.point_zero⟩ ⟨1, by decide, parent.edge.point_one⟩

end EndpointSafeBlock

end Purelib.Riemann.Topology.PreparedRefinementRootChains
