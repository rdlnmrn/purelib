module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSubdivisionReplay
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements

public section

/-!
# Exact canonical cycle restoration from checked bank spines

Bank constructors may differ while their full prepared owner chains are
equal.  The actual centred/switched state consumes those chains, not the
bank's presentation tag.  These equations preserve the complete original
state, including stationary switches and the allowance function, without
function extensionality or caller-supplied per-cell source equalities.

Only the existing finite bank and switched-state implementations are used.
No generated bank or additional upstream mathematical import is introduced.
-/

namespace Purelib.Riemann.Topology.PreparedCycleReplay

open Purelib.Riemann.Curves.AlgebraicDifferentials
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (DyadicBank)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedBoundaryDoublePath PreparedDoublePath PreparedCycleData)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements

section
open Purelib.Data
/-- The exact Gaussian rational carrier of retained cycle endpoints. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational carrier of retained cycle bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
end

open Purelib.Geometry.Rational (Box) in
/-- The exact rational box type indexing the original prepared paths. -/
abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Riemann in
/-- The retained operational square-root owner of a polynomial value. -/
abbrev Owner := Topology.SquareRootContinuationChain.Owner

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Geometry.Path.Gaussian.Lifted in
open Purelib.Riemann in
/-- A fixed finite centered-parent list determines its consecutive endpoint chain uniquely. -/
theorem centeredChain_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
    {start finish : Basic.LiftedPoint 2}
    (first second : CenteredPathChain parents (start := start) (finish := finish)) :
    first = second := by
  induction first with
  | nil point => cases second; rfl
  | cons parent tail ih =>
      cases second with
      | cons _ otherTail =>
          have same := ih otherTail
          cases same
          rfl

/-- Equal parent lists determine equal checked centered states with the same endpoints and sheet. -/
theorem centeredState_eq_of_parents_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {sheet : Fin 2} {start finish : Gaussian}
    (first second : CenteredPathChain.CheckedDyadicCenteredState curve source sheet start finish)
    (same : first.parents = second.parents) : first = second := by
  cases first with
  | mk first firstProper firstChain =>
    cases second with
    | mk second secondProper secondChain =>
      cases same
      have chains := centeredChain_eq firstChain secondChain
      cases chains
      rfl

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache in
/-- Reading a dyadic bank or its retained certified cache gives the same complete centered state.

The equality covers every supported bank constructor, including executed certificates, while preserving the actual
parent list and dependent endpoint chain. -/
theorem centeredBank_eq_cache {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {owner : Owner (curve.polynomial.eval
      start)}
    (bank : DyadicBank depth diameter positive path owner) :
    CenteredPathChain.ofDyadicBank curve source sheet bank =
      CenteredPathChain.ofDyadicBank curve source sheet (.certified (DyadicBank.cache bank)) := by
  apply centeredState_eq_of_parents_eq
  cases bank with
  | safe => rfl
  | executed => rfl
  | certified => rfl
  | executedCertified checked =>
      exact CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath
        curve source sheet checked

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Replay in
/-- Fixed finite bank inputs determine the same complete centered state.

The original path, owner, depth and diameter fix the retained prepared spine, including its constant center thunks and
proper endpoint chain. -/
theorem centeredBank_eq {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {ambient : Box} {start finish : Gaussian}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {owner : Owner (curve.polynomial.eval
      start)}
    (first second : DyadicBank depth diameter positive path owner) :
    CenteredPathChain.ofDyadicBank curve source sheet first =
      CenteredPathChain.ofDyadicBank curve source sheet second := by
  rw [centeredBank_eq_cache curve source sheet first,
    centeredBank_eq_cache curve source sheet second,
    PreparedSubdivisionReplay.bank_cache_eq first second]

open Purelib.Riemann in
/-- Appending two proper parent lists preserves every retained properness certificate. -/
private theorem proper_append {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} :
    ∀ {first second : List (CenteredEdge curve source)},
      Integration.PreparedDyadicRefinements.AllParentsProper first →
      Integration.PreparedDyadicRefinements.AllParentsProper second →
      Integration.PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _, _, second => second
  | _ :: _, _, first, second => ⟨first.1, proper_append first.2 second⟩

open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Riemann
open Purelib.Riemann.Integration
/-- Assemble the switched bridge cycle from its two retained centered banks.

The original endpoint anchors, both stationary sheet switches, exact parent concatenation and full allowance function
are retained in the resulting state. -/
@[expose] def bridgeFromCentered {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (start finish : Gaussian)
    (forward : CenteredPathChain.CheckedDyadicCenteredState curve source 0 start finish)
    (backward : CenteredPathChain.CheckedDyadicCenteredState curve source 1 finish start) :
    DirectSwitchedState curve source := by
  let finishSwitch : SwitchedPathChain ([] : List (CenteredEdge curve source))
      (start := { coordinate := finish, sheet := 0 })
      (finish := { coordinate := finish, sheet := 1 }) :=
    SwitchedPathChain.singletonStationary finish 0
  let startSwitch : SwitchedPathChain ([] : List (CenteredEdge curve source))
      (start := { coordinate := start, sheet := 1 })
      (finish := { coordinate := start, sheet := 0 }) :=
    SwitchedPathChain.singletonStationary start 1
  let parents := forward.parents ++ ([] ++ (backward.parents ++ []))
  exact
    { start := { coordinate := start, sheet := 0 }
      finish := { coordinate := start, sheet := 0 }
      parents := parents
      proper := by
        dsimp only [parents]
        simpa only [List.nil_append, Purelib.Data.List.Append.append_nil] using
          proper_append forward.proper backward.proper
      chain := (SwitchedPathChain.ofCenteredPathChain forward.chain).append
        (finishSwitch.append ((SwitchedPathChain.ofCenteredPathChain backward.chain).append startSwitch))
      initialAllowanceBound := fun target =>
        (PathModel.mk
          ((parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

/-- Assemble a finite-cut cycle from its four already retained centered banks.

The displayed anchors and bank states determine the complete switched chain, parent order and allowance function;
construction consumes those values directly. -/
@[expose] def boundaryFromCentered {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (left right : Gaussian)
    (forward : CenteredPathChain.CheckedDyadicCenteredState curve source 0 left right)
    (rightBoundary : CenteredPathChain.CheckedDyadicCenteredState curve source 0 right right)
    (backward : CenteredPathChain.CheckedDyadicCenteredState curve source 1 right left)
    (leftBoundary : CenteredPathChain.CheckedDyadicCenteredState curve source 1 left left) :
    DirectSwitchedState curve source := by
  let rightSwitch : SwitchedPathChain ([] : List (CenteredEdge curve source))
      (start := { coordinate := right, sheet := 0 })
      (finish := { coordinate := right, sheet := 1 }) :=
    SwitchedPathChain.singletonStationary right 0
  let leftSwitch : SwitchedPathChain ([] : List (CenteredEdge curve source))
      (start := { coordinate := left, sheet := 1 })
      (finish := { coordinate := left, sheet := 0 }) :=
    SwitchedPathChain.singletonStationary left 1
  let parents := forward.parents ++ (rightBoundary.parents ++
    ([] ++ (backward.parents ++ (leftBoundary.parents ++ []))))
  exact
    { start := { coordinate := left, sheet := 0 }
      finish := { coordinate := left, sheet := 0 }
      parents := parents
      proper := by
        dsimp only [parents]
        simpa only [List.nil_append, Purelib.Data.List.Append.append_nil] using
          proper_append forward.proper
            (proper_append rightBoundary.proper (proper_append backward.proper leftBoundary.proper))
      chain := (SwitchedPathChain.ofCenteredPathChain forward.chain).append
        ((SwitchedPathChain.ofCenteredPathChain rightBoundary.chain).append
          (rightSwitch.append ((SwitchedPathChain.ofCenteredPathChain backward.chain).append
            ((SwitchedPathChain.ofCenteredPathChain leftBoundary.chain).append leftSwitch))))
      initialAllowanceBound := fun target =>
        (PathModel.mk
          ((parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

end

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
set_option genInjectivity false in
/-- Replacement certified banks indexed by an original prepared boundary cycle.

Each bank retains the original path, owner seed, depth and diameter, giving an exact restoration interface for the four
finite spines. -/
structure BoundaryBanks {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (original : PreparedBoundaryDoublePath curve) where
  /-- The forward connector bank with the original source owner and depth. -/ forward : DyadicBank original.forwardDepth
    original.rootDiameter original.rootDiameterPositive
    original.connector original.forwardOwner
  /-- The right boundary bank with its original owner and depth. -/ right : DyadicBank original.rightBoundaryDepth
    original.rootDiameter original.rootDiameterPositive
    original.rightBoundaryPath original.rightBoundaryOwner
  /-- The reversed connector bank with the original backward owner and depth. -/ backward : DyadicBank
    original.backwardDepth original.rootDiameter original.rootDiameterPositive
    (ClearPath.reverse original.connector) original.backwardOwner
  /-- The left boundary bank with its original owner and depth. -/ left : DyadicBank original.leftBoundaryDepth
    original.rootDiameter original.rootDiameterPositive
    original.leftBoundaryPath original.leftBoundaryOwner

constructive_injectivity BoundaryBanks

open Purelib.Curves in
/-- Replace the four checked banks while retaining the original boundary-cycle geometry and parameters. -/
@[expose] def BoundaryBanks.replace {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (original : PreparedBoundaryDoublePath curve) (banks : BoundaryBanks original) :
    PreparedBoundaryDoublePath curve :=
  { original with
    forwardChecked := banks.forward
    rightBoundaryChecked := banks.right
    backwardChecked := banks.backward
    leftBoundaryChecked := banks.left }

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
/-- Replacing the four indexed banks preserves the complete original boundary state.

The equality retains both stationary switches, the exact parent chain and the entire allowance function through
centered-bank reconstruction. -/
theorem boundaryState_eq {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (original : PreparedBoundaryDoublePath curve)
    (banks : BoundaryBanks original) :
    boundaryState curve source (banks.replace original) = boundaryState curve source original := by
  change boundaryFromCentered curve source original.leftState.box.anchor original.rightState.box.anchor
      (CenteredPathChain.ofDyadicBank curve source 0 banks.forward)
      (CenteredPathChain.ofDyadicBank curve source 0 banks.right)
      (CenteredPathChain.ofDyadicBank curve source 1 banks.backward)
      (CenteredPathChain.ofDyadicBank curve source 1 banks.left) =
    boundaryFromCentered curve source original.leftState.box.anchor original.rightState.box.anchor
      (CenteredPathChain.ofDyadicBank curve source 0 original.forwardChecked)
      (CenteredPathChain.ofDyadicBank curve source 0 original.rightBoundaryChecked)
      (CenteredPathChain.ofDyadicBank curve source 1 original.backwardChecked)
      (CenteredPathChain.ofDyadicBank curve source 1 original.leftBoundaryChecked)
  rw [centeredBank_eq curve source 0 banks.forward original.forwardChecked,
    centeredBank_eq curve source 0 banks.right original.rightBoundaryChecked,
    centeredBank_eq curve source 1 banks.backward original.backwardChecked,
    centeredBank_eq curve source 1 banks.left original.leftBoundaryChecked]

/-- Checked bank reconstruction preserves the compact source-boundary state.

The original geometry, depths and diameter determine the same source allowance, so the complete compact state follows
from the retained bank equalities. -/
theorem compactBoundaryState_eq {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (original : PreparedBoundaryDoublePath curve)
    (banks : BoundaryBanks original) :
    compactCycleState curve source (.finiteCut (banks.replace original)) =
      compactCycleState curve source (.finiteCut original) := by
  unfold compactCycleState
  change (boundaryState curve source (banks.replace original)).withSourceAllowanceBound _ _ = _
  simp only [boundaryState_eq, -eq_self, -iff_self]
  rfl

end

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- Retained executable pieces of a bridge or finite-cut cycle.

Each centered bank carries its actual finite edge list and dependent endpoint chain. The displayed anchors and sheet
indices determine their exact assembly. -/
inductive CycleParts {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) : Type 2
  /-- The two centered banks of a bridge cycle, with forward sheet zero and backward sheet one. -/ | bridge (start
    finish : Gaussian)
      (forward : CenteredPathChain.CheckedDyadicCenteredState curve source 0 start finish)
      (backward : CenteredPathChain.CheckedDyadicCenteredState curve source 1 finish start)
  /-- The four centered banks of a finite-cut cycle, with original endpoint loops and sheet labels. -/ | finiteCut (left
    right : Gaussian)
      (forward : CenteredPathChain.CheckedDyadicCenteredState curve source 0 left right)
      (rightBoundary : CenteredPathChain.CheckedDyadicCenteredState curve source 0 right right)
      (backward : CenteredPathChain.CheckedDyadicCenteredState curve source 1 right left)
      (leftBoundary : CenteredPathChain.CheckedDyadicCenteredState curve source 1 left left)

constructive_injectivity CycleParts

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- Assemble the retained cycle pieces into their exact switched state. -/
@[expose] def CycleParts.state {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} : CycleParts curve source → DirectSwitchedState curve source
  | .bridge start finish forward backward =>
      bridgeFromCentered curve source start finish forward backward
  | .finiteCut left right forward rightBoundary backward leftBoundary =>
      boundaryFromCentered curve source left right forward rightBoundary backward leftBoundary

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
/-- Extract canonical cycle pieces from the retained certified bank spines.

Both bridge and finite-cut cases use the checked caches uniformly across supported bank constructors, preserving the
original anchors and sheet order. -/
@[expose] def CycleParts.canonical {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) : PreparedCycleData curve → CycleParts curve source
  | .bridge data =>
      .bridge data.start data.finish
        (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.forwardChecked)))
        (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.backwardChecked)))
  | .finiteCut data =>
      .finiteCut data.leftState.box.anchor data.rightState.box.anchor
        (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.forwardChecked)))
        (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.rightBoundaryChecked)))
        (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.backwardChecked)))
        (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.leftBoundaryChecked)))

/-- Canonical retained pieces assemble to the complete original cycle state. -/
theorem CycleParts.canonical_state {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (original : PreparedCycleData curve) :
    (canonical curve source original).state = cycleState curve source original := by
  cases original with
  | bridge data =>
      change bridgeFromCentered curve source data.start data.finish
          (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.forwardChecked)))
          (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.backwardChecked))) =
        bridgeFromCentered curve source data.start data.finish
          (CenteredPathChain.ofDyadicBank curve source 0 data.forwardChecked)
          (CenteredPathChain.ofDyadicBank curve source 1 data.backwardChecked)
      rw [← centeredBank_eq_cache curve source 0 data.forwardChecked,
        ← centeredBank_eq_cache curve source 1 data.backwardChecked]
  | finiteCut data =>
      change boundaryFromCentered curve source data.leftState.box.anchor data.rightState.box.anchor
          (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.forwardChecked)))
          (CenteredPathChain.ofDyadicBank curve source 0 (.certified (DyadicBank.cache data.rightBoundaryChecked)))
          (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.backwardChecked)))
          (CenteredPathChain.ofDyadicBank curve source 1 (.certified (DyadicBank.cache data.leftBoundaryChecked))) =
        boundaryFromCentered curve source data.leftState.box.anchor data.rightState.box.anchor
          (CenteredPathChain.ofDyadicBank curve source 0 data.forwardChecked)
          (CenteredPathChain.ofDyadicBank curve source 0 data.rightBoundaryChecked)
          (CenteredPathChain.ofDyadicBank curve source 1 data.backwardChecked)
          (CenteredPathChain.ofDyadicBank curve source 1 data.leftBoundaryChecked)
      rw [← centeredBank_eq_cache curve source 0 data.forwardChecked,
        ← centeredBank_eq_cache curve source 0 data.rightBoundaryChecked,
        ← centeredBank_eq_cache curve source 1 data.backwardChecked,
        ← centeredBank_eq_cache curve source 1 data.leftBoundaryChecked]

end

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- An exact cycle-state restoration cache linked to its original prepared cycle.

The retained executable pieces and rational source allowance carry equations identifying the original switched state and
compact allowance, preserving the full dependent construction. -/
structure CachedCycle {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (original : PreparedCycleData curve) where
  /-- The retained executable cycle pieces. -/ parts : CycleParts curve source
  /-- The retained pieces assemble to the exact original cycle state. -/ parts_eq : parts.state = cycleState curve
    source original
  /-- The cached rational source-channel allowance. -/ sourceAllowance : Coordinate
  /-- The cached allowance is the original cycle's exact aggregate source bound. -/ sourceAllowance_eq : sourceAllowance
    = cycleSourceAggregateBound source original

constructive_injectivity CachedCycle

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
/-- Materialize canonical cycle pieces and the original aggregate source allowance with their exact equations. -/
@[expose] def CachedCycle.canonical {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (source : Basic.Differential genus) (original : PreparedCycleData curve) :
    CachedCycle curve source original where
  parts := CycleParts.canonical curve source original
  parts_eq := CycleParts.canonical_state curve source original
  sourceAllowance := cycleSourceAggregateBound source original
  sourceAllowance_eq := rfl

/-- Restore the compact switched state from the retained pieces and cached rational allowance.

The original cycle is used through the stored specification equalities; the executable construction consumes the cache's
actual fields. -/
@[expose] def CachedCycle.restore {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {original : PreparedCycleData curve}
    (cached : CachedCycle curve source original) : DirectSwitchedState curve source :=
  cached.parts.state.withSourceAllowanceBound cached.sourceAllowance (by
    rw [cached.parts_eq, cached.sourceAllowance_eq]
    exact cycleState_sourceAllowance_le curve source original)

end

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann in
open Purelib.Riemann.Integration in
/-- Equal switched states and equal source bounds give equal states with the retained allowance. -/
private theorem withSourceAllowanceBound_congr {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {source : Basic.Differential genus}
    (first second : DirectSwitchedState curve source) (same : first = second)
    (firstBound secondBound : Coordinate) (boundSame : firstBound = secondBound)
    (firstLe : (PathModel.mk
      ((first.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge source)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance ≤ firstBound)
    (secondLe : (PathModel.mk
      ((second.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge source)).map
        PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance ≤ secondBound) :
    first.withSourceAllowanceBound firstBound firstLe =
      second.withSourceAllowanceBound secondBound secondLe := by
  cases same
  cases boundSame
  rfl

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- The restored cache equals the complete original compact cycle state.

This identity preserves the parent list, stationary switches and allowance function used by every subsequent canonical
refinement and reading. -/
theorem CachedCycle.restore_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {original : PreparedCycleData curve}
    (cached : CachedCycle curve source original) :
    cached.restore = compactCycleState curve source original :=
  withSourceAllowanceBound_congr _ _ cached.parts_eq _ _ cached.sourceAllowance_eq _
    (cycleState_sourceAllowance_le curve source original)

end Purelib.Riemann.Topology.PreparedCycleReplay

end
