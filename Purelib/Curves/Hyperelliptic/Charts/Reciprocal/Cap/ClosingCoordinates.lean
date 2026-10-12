module
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.PreparedBankRootChains

open Purelib.Approximation

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-!
# Closing joins for the retained cap parent bank

Root return is transported through the cached first and last parent owners.
The coordinate chain supplies their exact common base point. The resulting
join uses the existing cap endpoint occurrences, without preparing new roots.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {count : Nat}

/-- Join the final retained endpoint to the supplied actual occurrence.
The empty bank contributes no endpoint. -/
def LastJoin {point : Normalization.InverseRootPolynomial.Gaussian}
    {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
    (target : Overlap cap point owner) : {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve
      differential)} → Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents → Type
  | [], .nil => PUnit
  | [_], .cons data .nil => Overlap.Join data.data.last.coordinates target
  | _ :: _ :: _, .cons _ (.cons next rest) => Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.LastJoin
    target (.cons next rest)

/-- The closure join identifies the final and initial retained cap coordinates. -/
def ClosingJoin : {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} →
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents → Type
  | [], .nil => PUnit
  | _ :: _, .cons data rest => Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.LastJoin data.data.first.coordinates
    (.cons data rest)

/-- The first cached parent begins at the original lifted chain's initial coordinate. -/
theorem first_coordinate {parent : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents :
  List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {first last : Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (Integration.PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start :=
      first) (finish := last))) :
    parent.edge.point 0 = first.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain
  exact parent.edge.point_zero

/-- Remove the first original parent while retaining the dependent lifted chain of remaining parents. -/
theorem remaining_chain {parent : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {parents :
  List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
    {first last : Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (Integration.PreparedDirectDyadicRefinements.CenteredPathChain (parent :: parents) (start :=
      first) (finish := last))) :
    Nonempty (Integration.PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩) (finish :=
        last)) := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => exact ⟨tail⟩

/-- A singleton cached parent ends at the original lifted chain's final coordinate. -/
theorem final_coordinate {parent : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential} {first last
  : Path.Gaussian.Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (Integration.PreparedDirectDyadicRefinements.CenteredPathChain [parent] (start := first) (finish
      := last))) :
    parent.edge.point 1 = last.coordinate := by
  obtain ⟨chain⟩ := chain
  cases chain with
  | cons _ tail => cases tail; exact parent.edge.point_one

/-- Read the retained equivalence of root names from the empty parent bank's root links. -/
def emptyRoots {first last : Topology.PreparedRefinementRootChains.Named} :
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks (.nil :
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count []) first last →
  Gaussian.Equivalence.NamedEquivalent first last
  | .nil equivalent => equivalent

/-- Construct the final coordinate join using the original cached root links, endpoint geometry and supplied root-return
equivalence. -/
def lastJoin : ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)} (bank :
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : Topology.PreparedRefinementRootChains.Named},
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank first last →
    {start finish : Path.Gaussian.Lifted.Basic.LiftedPoint 2} → Nonempty
      (Integration.PreparedDirectDyadicRefinements.CenteredPathChain parents (start := start) (finish := finish)) →
    {point : Normalization.InverseRootPolynomial.Gaussian} → {owner : Topology.SquareRootContinuationChain.Owner
      ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)} →
    (target : Overlap cap point owner) → finish.coordinate = point → Gaussian.Equivalence.NamedEquivalent last
      target.reciprocal.value.name → Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.LastJoin target bank
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _ => ⟨⟩
  | [_], .cons data .nil, _, _, roots, _, _, chain, _, _, target, pointEq, returned =>
      Overlap.Join.build data.data.last.coordinates target ((data.last_eq.trans
        (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.final_coordinate chain)).trans pointEq) (by
        rw [data.data.last.coordinates.reciprocal_eq]
        exact (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.emptyRoots roots.tail).trans returned)
  | _ :: _ :: _, .cons _ (.cons next rest), _, _, roots, _, _, chain, _, _, target, pointEq, returned =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.lastJoin (.cons next rest) roots.tail
        (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.remaining_chain chain) target pointEq returned

/-- Construct the closing join from actual root return and the erased geometry
of the same cached parent list. -/
def ClosingJoin.build : ∀ {parents : List (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Parent curve differential)}
  (bank : Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank cap differential count parents)
    {first last : Topology.PreparedRefinementRootChains.Named},
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.RootLinks bank first last →
    {start finish : Path.Gaussian.Lifted.Basic.LiftedPoint 2} → Nonempty
      (Integration.PreparedDirectDyadicRefinements.CenteredPathChain parents (start := start) (finish := finish)) →
    start.coordinate = finish.coordinate → Gaussian.Equivalence.NamedEquivalent last first →
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ClosingJoin bank
  | [], .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | _ :: _, .cons data rest, _, _, roots, _, _, chain, pointEq, returned =>
      Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.lastJoin (.cons data rest) roots chain
        data.data.first.coordinates
        (pointEq.symm.trans ((Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.first_coordinate chain).symm.trans
          data.first_eq.symm)) (by
          rw [data.data.first.coordinates.reciprocal_eq]
          exact returned.trans roots.entry)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {owner : Topology.SquareRootContinuationChain.Owner
    ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The complete cap boundary closes at its actual cached cap coordinates. -/
def closingCoordinates (data : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data cap owner differential) :
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ClosingJoin data.covered.bank :=
  Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ClosingJoin.build data.covered.bank data.covered.roots
    data.covered.cache.chain rfl data.returned

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
