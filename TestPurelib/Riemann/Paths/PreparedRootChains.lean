module

import all Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootChain
import all Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.RootChain
import Purelib.Riemann.Topology.PreparedBankRootChains

/-! # Whole original root-chain computations

The historical complete definitions are verifier-only copies. The explicit
import-all is confined to the original comparison-cache root-chain owner,
whose private body must reduce to check complete cached result preservation.
The same diagnostic reduction is needed for the original acquisition-parent
root-chain owner in the complete supplied-cache regression.
No verifier definition is a production root-chain algorithm.
-/

namespace TestPurelib.Riemann.Paths.PreparedRootChains

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge centeredEdges edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName queryEquivalentAdvance subdivisionRootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- The complete original subdivision root-chain computation before adding supplied trace views. -/
private def formerSubdivisionRootChain (curve : HyperellipticCurve genus) (differential : Differential
  genus)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      RootChain (centeredEdges curve differential sheet subdivision centers)
        (ownerName owner) (ownerName subdivision.terminalOwner)
  | _, _, .stop _ owner, _ => .nil (Equivalence.NamedEquivalent.refl (ownerName owner))
  | _, _, .next current owner request cached ordered small remaining, centers =>
      let edge := edgeOfStep curve differential segment within current owner request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      .cons child edge.ownerRootEquivalent_baseQuery
        ((formerSubdivisionRootChain curve differential segment within sheet remaining centers.2).changeStart
          (queryEquivalentAdvance edge))

/-- The entire default result remains the whole original root chain for every retained subdivision and center cache. -/
private theorem subdivision_default_eq_former
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    (segment : ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      subdivisionRootChain curve differential segment within sheet subdivision centers none =
        formerSubdivisionRootChain curve differential segment within sheet subdivision centers
  | _, _, .stop _ _, _ => by rfl
  | _, _, .next current owner request cached ordered small remaining, centers => by
      let edge := edgeOfStep curve differential segment within current owner request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      change RootChain.cons child edge.ownerRootEquivalent_baseQuery
          ((subdivisionRootChain curve differential segment within sheet remaining centers.2 none).changeStart
            (queryEquivalentAdvance edge)) =
        RootChain.cons child edge.ownerRootEquivalent_baseQuery
          ((formerSubdivisionRootChain curve differential segment within sheet remaining centers.2).changeStart
            (queryEquivalentAdvance edge))
      exact congrArg (fun tail => RootChain.cons child edge.ownerRootEquivalent_baseQuery
        (tail.changeStart (queryEquivalentAdvance edge)))
        (subdivision_default_eq_former curve differential segment within sheet remaining centers.2)

/-- The complete original cached fold before delegation to the generalized original subdivision operation. -/
private def formerCachedRootChain {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (centers : CenterStates curve differential sheet subdivision) :
    RootChain (centeredEdges curve differential sheet subdivision centers)
      (ownerRootName inherited.parameterNonzero inherited)
      (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner) :=
  Subdivision.casesOn
    (motive := fun current inherited subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      Cache curve differential budget sheet second movement subdivision fits trace →
      (centers : CenterStates curve differential sheet subdivision) →
      RootChain (centeredEdges curve differential sheet subdivision centers)
        (ownerRootName inherited.parameterNonzero inherited)
        (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner))
    subdivision
    (fun _ owner _ _ _ _ => .nil (NamedEquivalent.refl (ownerRootName owner.parameterNonzero owner)))
    (fun current inherited request cached ordered small remaining fits trace retained centers =>
      let view := retained.1
      let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      let originalSource := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
      let source : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) :=
        NamedEquivalent.transport rfl view.source_name_eq originalSource
      let entry : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (edge.rootName 0 edge.baseInside) :=
        NamedEquivalent.transport rfl edge.rootName_zero_eq_cached.symm source
      let originalRetention := view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
        (view.tail_point.trans view.moving_point.symm)
      let movingName : ownerRootName view.movingOwner.parameterNonzero view.movingOwner =
          ownerRootName view.moving.owner.parameterNonzero view.moving.owner :=
        PreparedBankRootChains.ownerName_eq_of_heq
          (congrArg curve.polynomial.eval view.moving_point).symm view.movingOwner_heq
      let storedName := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) remaining.sourceOwner_eq
      let retention : NamedEquivalent (ownerRootName view.movingOwner.parameterNonzero view.movingOwner)
          (ownerRootName remaining.sourceOwner.parameterNonzero remaining.sourceOwner) :=
        NamedEquivalent.transport movingName.symm view.tail_name_eq originalRetention
      let movingQuery : edge.rootName 1 (by decide) =
          ownerRootName view.movingOwner.parameterNonzero view.movingOwner :=
        edge.rootName_one_eq_transported.trans
          (congrArg (fun owner => ownerRootName owner.parameterNonzero owner) view.movingOwner_eq).symm
      let seam := NamedEquivalent.transport movingQuery.symm storedName retention
      let tail := formerCachedRootChain retained.2.2.2 centers.2
      .cons child entry (tail.changeStart seam))
    fits trace retained centers
termination_by structural subdivision

/-- The same actual comparison cache retains its entire former root-chain value, including all signed procedures. -/
private theorem cached_eq_former :
    ∀ {current : Endpoint} {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current inherited}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
      (retained : Cache curve differential budget sheet second movement subdivision fits trace)
      (centers : CenterStates curve differential sheet subdivision),
      retained.rootChain centers = formerCachedRootChain retained centers
  | _, _, .stop _ _, _, _, _, _ => by rfl
  | _, _, .next current inherited request cached ordered small remaining, fits, trace, retained, centers => by
      let view := retained.1
      let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      let originalSource := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
      let source : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) :=
        NamedEquivalent.transport rfl view.source_name_eq originalSource
      let entry : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (edge.rootName 0 edge.baseInside) :=
        NamedEquivalent.transport rfl edge.rootName_zero_eq_cached.symm source
      let originalRetention := view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
        (view.tail_point.trans view.moving_point.symm)
      let movingName : ownerRootName view.movingOwner.parameterNonzero view.movingOwner =
          ownerRootName view.moving.owner.parameterNonzero view.moving.owner :=
        PreparedBankRootChains.ownerName_eq_of_heq
          (congrArg curve.polynomial.eval view.moving_point).symm view.movingOwner_heq
      let storedName := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) remaining.sourceOwner_eq
      let retention : NamedEquivalent (ownerRootName view.movingOwner.parameterNonzero view.movingOwner)
          (ownerRootName remaining.sourceOwner.parameterNonzero remaining.sourceOwner) :=
        NamedEquivalent.transport movingName.symm view.tail_name_eq originalRetention
      let movingQuery : edge.rootName 1 (by decide) =
          ownerRootName view.movingOwner.parameterNonzero view.movingOwner :=
        edge.rootName_one_eq_transported.trans
          (congrArg (fun owner => ownerRootName owner.parameterNonzero owner) view.movingOwner_eq).symm
      let seam := NamedEquivalent.transport movingQuery.symm storedName retention
      change RootChain.cons child entry ((retained.2.2.2.rootChain centers.2).changeStart seam) =
        RootChain.cons child entry ((formerCachedRootChain retained.2.2.2 centers.2).changeStart seam)
      exact congrArg (fun tail => RootChain.cons child entry (tail.changeStart seam))
        (cached_eq_former retained.2.2.2 centers.2)

section Acquisition

open Purelib.Approximation (AccuracyRequest)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition

variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    {acquired : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
    {count : Nat}
    {actual : OwnerPath curve.polynomial start sourceOwner finish acquired.traced.finishOwner}
    {actual_eq : actual = acquired.traced.trace.get}

/-- The whole historical parent-root fold on the same supplied complete comparison cache. -/
private def formerParentRootChain (parents : Segment.Parents differential sheet count acquired)
    (comparisons : Segment.RootComparisons curve differential acquired actual actual_eq sheet second movement) :
    RootChain parents.covered.parents (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName acquired.traced.finishOwner.parameterNonzero acquired.traced.finishOwner) := by
  let internal := formerCachedRootChain comparisons parents.centers
  have firstName := PreparedBankRootChains.ownerAtStart_name segment sourceOwner
  have lastName := PreparedBankRootChains.finishOwner_name acquired.traced.prepared
  have displayed := congrArg (fun owner : Owner (curve.polynomial.eval finish) =>
    ownerRootName owner.parameterNonzero owner) acquired.traced.finishOwner_eq
  let physical := PreparedBankRootChains.RootChain.castNames firstName (lastName.trans displayed.symm) internal
  exact PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm physical

/-- The original supplied comparison cache preserves the complete former parent-root result through the same casts. -/
private theorem parent_cached_eq_former (parents : Segment.Parents differential sheet count acquired)
    (comparisons : Segment.RootComparisons curve differential acquired actual actual_eq sheet second movement) :
    parents.rootChain comparisons.rootViews = formerParentRootChain parents comparisons := by
  have firstName := PreparedBankRootChains.ownerAtStart_name segment sourceOwner
  have lastName := PreparedBankRootChains.finishOwner_name acquired.traced.prepared
  have displayed := congrArg (fun owner : Owner (curve.polynomial.eval finish) =>
    ownerRootName owner.parameterNonzero owner) acquired.traced.finishOwner_eq
  change PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm
      (PreparedBankRootChains.RootChain.castNames firstName (lastName.trans displayed.symm)
        (comparisons.rootChain parents.centers)) =
    PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm
      (PreparedBankRootChains.RootChain.castNames firstName (lastName.trans displayed.symm)
        (formerCachedRootChain comparisons parents.centers))
  exact congrArg (fun roots => PreparedBankRootChains.RootChain.castChildren parents.parents_eq.symm
    (PreparedBankRootChains.RootChain.castNames firstName (lastName.trans displayed.symm) roots))
    (cached_eq_former comparisons parents.centers)

end Acquisition

end TestPurelib.Riemann.Paths.PreparedRootChains
