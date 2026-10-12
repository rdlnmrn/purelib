module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Algebra.NatCast
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.Constant
public import Purelib.Integration.Polynomial.Gaussian.Path.Execution
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Sequential
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Integration.Program.Gaussian.Presentation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Rational.Box.Sample
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone quarterRadius_scale_mono)

public section

/-!
# Direct refinements with stationary sheet switches

Branch-cut cycles alternate nonstationary prepared banks with exact stationary
sheet transitions.  This module keeps those transitions in the dependent
lifted path while presenting only the nonstationary edges to the executable
direct refiner.  Thus every finite model has the actual closed-cycle geometry,
and no zero-width edge is smuggled into an interface requiring strict parameter
growth.
-/

namespace Purelib.Riemann.Integration.PreparedSwitchedRefinements

open Purelib.Curves.Hyperelliptic
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Algebra

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-- The rational coordinate carrier of the switched refinement bounds. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the switched path models. -/
abbrev Gaussian := Basic.Canonical
/-- The exact square-root continuation owner at its retained polynomial parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The polynomial cell model used for each retained lifted edge or sheet switch. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
/-- The ordered polynomial path model used by switched integral schedules. -/
abbrev PathModel := Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
/-- A prepared differential edge with its retained center and correctness certificate. -/
abbrev CenteredEdge {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedEdgeRecasting.CenteredEdge curve differential
/-- A synchronized refinement of the exact parent edge list at the stated depth and root diameter. -/
abbrev SynchronizedDirectBlockRefinement {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (depth : Nat) (rootDiameter : Coordinate)
    (parents : List (CenteredEdge curve differential)) :=
  Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.SynchronizedDirectBlockRefinement
    depth rootDiameter parents

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial in
/-- The exact zero-integrand cell at a stationary sheet-switch coordinate. -/
@[expose] def stationaryModel (coordinate : Gaussian) : CellModel :=
  Basic.CellModel.exact coordinate coordinate
    (Ascending.Gaussian.Basic.constant 0)

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- A stationary sheet-switch model has zero weighted allowance. -/
@[simp] theorem stationaryModel_weightedAllowance (coordinate : Gaussian) :
    (stationaryModel coordinate).weightedAllowance = 0 := by
  unfold stationaryModel
    Basic.CellModel.weightedAllowance
    Basic.CellModel.exact
  rw [Fraction.Field.mul_zero_direct]

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- A stationary sheet-switch model has zero integral sample. -/
@[simp] theorem stationaryModel_integralSample (coordinate : Gaussian) :
    (stationaryModel coordinate).integralSample = 0 := by
  unfold stationaryModel
    Basic.CellModel.integralSample
    Basic.CellModel.displacement
    Basic.CellModel.exact
  rw [Basic.sub_self]
  apply Basic.ext <;>
    simp only [Basic.mul_re,
      Basic.mul_im,
      Basic.zero_re,
      Basic.zero_im] <;> ring1

set_option linter.unusedVariables false in
set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Branches in
/-- An endpoint-indexed chain of prepared edges and stationary sheet switches.

The parent list counts only geometric edges; stationary cells retain their coordinates and sheet changes without adding
a parent edge. -/
inductive SwitchedPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : Lifted.Basic.LiftedPoint 2} -> Type 2
  /-- The empty chain at one retained lifted point. -/ | nil (point : Lifted.Basic.LiftedPoint 2) : SwitchedPathChain []
    (start := point)
      (finish := point)
  /-- A prepared geometric edge followed by the exact endpoint-compatible tail. -/ | edge (parent : CenteredEdge curve
    differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : Lifted.Basic.LiftedPoint 2}
      (tail : SwitchedPathChain remaining
        (start :=
          { coordinate := parent.edge.segment.pointAt
              parent.edge.request.endpoint.parameter
            sheet := parent.edge.sheet })
        (finish := finish)) :
      SwitchedPathChain (parent :: remaining)
        (start :=
          { coordinate := parent.edge.segment.pointAt parent.edge.left.parameter
            sheet := parent.edge.sheet })
        (finish := finish)
  /-- A stationary switch to the other sheet followed by its endpoint-compatible tail. -/ | stationary (coordinate :
    Gaussian) (sheet : Fin 2)
      {remaining : List (CenteredEdge curve differential)}
      {finish : Lifted.Basic.LiftedPoint 2}
      (tail : SwitchedPathChain remaining
        (start := { coordinate := coordinate, sheet := BranchCutLifts.otherSheet sheet })
        (finish := finish)) :
      SwitchedPathChain remaining
        (start := { coordinate := coordinate, sheet := sheet })
        (finish := finish)

constructive_injectivity SwitchedPathChain

namespace SwitchedPathChain

/-- Append switched chains with the same retained intermediate lifted point.

The result concatenates the original parent lists and preserves the order of both edge and stationary cells. -/
@[expose] def append {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : Lifted.Basic.LiftedPoint 2},
      SwitchedPathChain first (start := start) (finish := middle) ->
      SwitchedPathChain second (start := middle) (finish := finish) ->
        SwitchedPathChain (first ++ second) (start := start)
          (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .edge parent tail, second =>
      .edge parent (append tail second)
  | _, _, _, _, _, .stationary coordinate sheet tail, second =>
      .stationary coordinate sheet (append tail second)

/-- Read a centered edge chain as a switched chain without inserting sheet switches. -/
@[expose] def ofCenteredPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      PreparedDirectDyadicRefinements.CenteredPathChain parents
        (start := start) (finish := finish) ->
      SwitchedPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .edge parent (ofCenteredPathChain tail)

/-- Read a direct edge chain as a switched chain without inserting sheet switches. -/
@[expose] def ofDirectPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      PreparedDirectDyadicRefinements.DirectPathChain parents
        (start := start) (finish := finish) ->
      SwitchedPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .edge parent (ofDirectPathChain tail)

open Purelib.Curves.Hyperelliptic.Branches in
/-- The single stationary cell changing to the other sheet at the retained coordinate. -/
@[expose] def singletonStationary {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (coordinate : Gaussian) (sheet : Fin 2) :
    SwitchedPathChain ([] : List (CenteredEdge curve differential))
      (start := { coordinate := coordinate, sheet := sheet })
      (finish := { coordinate := coordinate, sheet := BranchCutLifts.otherSheet sheet }) :=
  .stationary coordinate sheet (.nil _)

/-- Count stationary sheet switches in the chain, excluding all geometric edges. -/
@[expose] def switchCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) -> Nat
  | [], _, _, .nil _ => 0
  | _ :: _, _, _, .edge _ tail => tail.switchCount
  | _, _, _, .stationary _ _ tail => tail.switchCount + 1

/-- A chain read from centered edges contains no stationary switches. -/
@[simp] theorem switchCount_ofCenteredPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain :
        PreparedDirectDyadicRefinements.CenteredPathChain parents
          (start := start) (finish := finish)),
      (ofCenteredPathChain chain).switchCount = 0
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons _ tail =>
      switchCount_ofCenteredPathChain tail

/-- The single stationary chain contains exactly one switch. -/
@[simp] theorem switchCount_singletonStationary {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (coordinate : Gaussian) (sheet : Fin 2) :
    (singletonStationary (curve := curve) (differential := differential)
      coordinate sheet).switchCount = 1 :=
  rfl

open Purelib.Curves.Hyperelliptic.Branches in
/-- Read the lifted path with each original edge and stationary sheet switch in order. -/
@[expose] def path {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        Lifted.Basic.LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons
        (BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path
  | _, _, _, .stationary coordinate sheet tail =>
      .cons (BranchCutLifts.switchCell coordinate sheet) tail.path

/-- Read the ordered polynomial models, inserting an exact zero cell for each stationary switch. -/
@[expose] def cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        List CellModel
  | [], _, _, .nil _ => []
  | _ :: _, _, _, .edge parent tail => parent.model :: tail.cells
  | _, _, _, .stationary coordinate _sheet tail =>
      stationaryModel coordinate :: tail.cells

section
open Purelib.Riemann.Branches
/-- A centered edge model starts at its original left continuation parameter. -/
theorem model_start {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (Differentials.PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold Differentials.PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_zero] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

/-- A centered edge model finishes at its original request endpoint parameter. -/
theorem model_finish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (Differentials.PreparedModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold Differentials.PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_one] using
    (PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

end

open Purelib.Curves.Hyperelliptic.Integration in
/-- Certify the ordered cell models along the exact retained lifted path.

Edge certificates use their retained differential centers; stationary switches use exact zero integral certificates. -/
@[expose] def certificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      Algebraic.Path.Basis.UniformPathCertificates curve differential chain.cells chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates
  | _, _, _, .stationary coordinate sheet tail => by
      simpa only [cells, path, stationaryModel] using
        (Algebraic.Path.Basis.UniformPathCertificates.cons rfl rfl (.stationary rfl)
          tail.certificates)

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every retained cell has a constant polynomial, including the zero stationary cells. -/
@[expose] def constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      Basic.PathModel.ConstantCells chain.cells
  | [], _, _, .nil _ => .nil
  | _ :: _, _, _, .edge parent tail =>
      .cons { coefficient := parent.center.value, polynomial_eq := rfl }
        tail.constantCells
  | _, _, _, .stationary coordinate _sheet tail => by
      simpa only [cells, stationaryModel] using
        Basic.PathModel.ConstantCells.cons
          (Basic.CellModel.exactConstantCertificate
            coordinate coordinate 0)
          tail.constantCells

/-- Read the same switched geometry using the target differential's recast edge models.

Every parent keeps its original geometric position, and stationary switches remain zero cells at the same coordinates.
-/
@[expose] def recastCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        List CellModel
  | [], _, _, .nil _ => []
  | _ :: _, _, _, .edge parent tail =>
      (PreparedEdgeRecasting.recastCenteredEdge target
        parent).model :: recastCells target tail
  | _, _, _, .stationary coordinate _sheet tail =>
      stationaryModel coordinate :: recastCells target tail

/-- Recasting the differential preserves the original edge's starting parameter. -/
theorem recast_model_start {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) (parent : CenteredEdge curve source) :
    (PreparedEdgeRecasting.recastCenteredEdge target
      parent).model.start =
        parent.edge.segment.pointAt parent.edge.left.parameter := by
  exact model_start
    (PreparedEdgeRecasting.recastCenteredEdge target
      parent)

/-- Recasting the differential preserves the original edge's final parameter. -/
theorem recast_model_finish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) (parent : CenteredEdge curve source) :
    (PreparedEdgeRecasting.recastCenteredEdge target
      parent).model.finish =
        parent.edge.segment.pointAt
          parent.edge.request.endpoint.parameter := by
  exact model_finish
    (PreparedEdgeRecasting.recastCenteredEdge target
      parent)

open Purelib.Curves.Hyperelliptic.Integration in
/-- Certify the recast differential models on the unchanged lifted path. -/
@[expose] def recastCertificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      Algebraic.Path.Basis.UniformPathCertificates curve target (recastCells target chain) chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons (recast_model_start target parent)
        (recast_model_finish target parent)
        ((PreparedEdgeRecasting.recastCenteredEdge target
          parent).edge.centeredValidCertificate curve target
            (PreparedEdgeRecasting.recastCenteredEdge
              target parent).center)
        (recastCertificates target tail)
  | _, _, _, .stationary coordinate sheet tail => by
      simpa only [recastCells, path, stationaryModel] using
        (Algebraic.Path.Basis.UniformPathCertificates.cons rfl rfl (.stationary rfl)
          (recastCertificates target tail))

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Recast differential cells and stationary zero cells retain constant polynomials. -/
@[expose] def recastConstantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      Basic.PathModel.ConstantCells
        (recastCells target chain)
  | [], _, _, .nil _ => .nil
  | _ :: _, _, _, .edge parent tail =>
      .cons
        { coefficient :=
            (PreparedEdgeRecasting.recastCenteredEdge
              target parent).center.value
          polynomial_eq := rfl }
        (recastConstantCells target tail)
  | _, _, _, .stationary coordinate _sheet tail => by
      simpa only [recastCells, stationaryModel] using
        Basic.PathModel.ConstantCells.cons
          (Basic.CellModel.exactConstantCertificate
            coordinate coordinate 0)
          (recastConstantCells target tail)

/-- Replace each geometric parent with its retained synchronized child block.

The endpoint-indexed chain keeps every original stationary switch in place while appending each child's exact direct
path chain. -/
@[expose] def refined {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (_chain : SwitchedPathChain parents (start := start) (finish := finish))
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      SwitchedPathChain blocks.children (start := start) (finish := finish)
  | _, _, [], _, _, .nil point, .nil => .nil point
  | _, _, _ :: _, _, _, .edge _ tail, .cons block _ _ remaining =>
      (ofDirectPathChain block.chain).append (refined tail remaining)
  | _, _, _, _, _, .stationary coordinate sheet tail, blocks =>
      .stationary coordinate sheet (refined tail blocks)

/-- Appending switched chains adds their stationary switch counts. -/
@[simp] theorem switchCount_append {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : Lifted.Basic.LiftedPoint 2}
      (left : SwitchedPathChain first (start := start) (finish := middle))
      (right : SwitchedPathChain second (start := middle) (finish := finish)),
      (left.append right).switchCount = left.switchCount + right.switchCount
  | [], _, _, _, _, .nil _, _right => by
      simp only [append, switchCount, Nat.zero_add]
      rfl
  | _ :: _, _, _, _, _, .edge _ tail, right => by
      simp only [append, switchCount]
      exact switchCount_append tail right
  | _, _, _, _, _, .stationary _ _ tail, right => by
      simp only [append, switchCount, switchCount_append tail right]
      omega

/-- A chain read from direct edges contains no stationary switches. -/
@[simp] theorem switchCount_ofDirectPathChain {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain :
        PreparedDirectDyadicRefinements.DirectPathChain parents
          (start := start) (finish := finish)),
      (ofDirectPathChain chain).switchCount = 0
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons _ tail =>
      switchCount_ofDirectPathChain tail

/-- Synchronized geometric refinement preserves the stationary switch count. -/
@[simp] theorem refined_switchCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish))
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      (chain.refined blocks).switchCount = chain.switchCount
  | _, _, [], _, _, .nil _, .nil => rfl
  | _, _, _ :: _, _, _, .edge _ tail, .cons block _ _ remaining => by
      simp only [refined, switchCount]
      calc
        ((ofDirectPathChain block.chain).append
              (tail.refined remaining)).switchCount =
            (ofDirectPathChain block.chain).switchCount +
              (tail.refined remaining).switchCount :=
          switchCount_append _ _
        _ = tail.switchCount := by
          rw [switchCount_ofDirectPathChain,
            refined_switchCount tail remaining, Nat.zero_add]
  | _, _, _, _, _, .stationary _ _ tail, blocks => by
      rewrite [refined.eq_3, switchCount.eq_3, switchCount.eq_3]
      exact congrArg (fun count => count + 1) (refined_switchCount tail blocks)

/-- The switched cell count is the parent edge count plus the stationary switch count. -/
@[simp] theorem cells_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      chain.cells.length = parents.length + chain.switchCount
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .edge _ tail => by
      simp only [cells, List.length_cons, List.length_cons, switchCount,
        cells_length tail]
      omega
  | _, _, _, .stationary _ _ tail => by
      simp only [cells, List.length_cons, switchCount, cells_length tail]
      omega

/-- Recasting preserves the parent-plus-switch cell count. -/
@[simp] theorem recastCells_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (chain.recastCells target).length =
        parents.length + chain.switchCount
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .edge _ tail => by
      simp only [recastCells, List.length_cons, List.length_cons, switchCount,
        recastCells_length target tail]
      omega
  | _, _, _, .stationary _ _ tail => by
      simp only [recastCells, List.length_cons, switchCount,
        recastCells_length target tail]
      omega

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Stationary switches contribute no weighted allowance to the recast parent models. -/
theorem recastCells_totalWeightedAllowance {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (Basic.PathModel.mk
        (chain.recastCells target)).totalWeightedAllowance =
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := recastCells_totalWeightedAllowance target tail
      change
        (tail.recastCells target).foldr
            (fun cell total => cell.weightedAllowance + total) 0 =
          ((remaining.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model).foldr
            (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      simp only [recastCells, List.map,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [recastCells,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, stationaryModel_weightedAllowance,
        Fraction.Field.zero_add]
      exact recastCells_totalWeightedAllowance target tail

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Stationary switches contribute no integral sample to the recast parent models. -/
theorem recastCells_integralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (Basic.PathModel.mk
        (chain.recastCells target)).integralSample =
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := recastCells_integralSample target tail
      change
        (tail.recastCells target).foldr
            (fun cell total => cell.integralSample + total) 0 =
          ((remaining.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model).foldr
            (fun cell total => cell.integralSample + total) 0 at tailEqual
      simp only [recastCells, List.map,
        Basic.PathModel.integralSample,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [recastCells,
        Basic.PathModel.integralSample,
        List.foldr_cons, stationaryModel_integralSample,
        Basic.zero_add]
      exact recastCells_integralSample target tail

/-- The switched model has exactly the integral sample of its geometric parent models. -/
theorem cells_integralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (Basic.PathModel.mk
        chain.cells).integralSample =
        (Basic.PathModel.mk
          (parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := cells_integralSample tail
      change
        tail.cells.foldr (fun cell total => cell.integralSample + total) 0 =
          (remaining.map
            PreparedSubdivisionModelCore.CenteredEdge.model).foldr
              (fun cell total => cell.integralSample + total) 0 at tailEqual
      simp only [cells, List.map,
        Basic.PathModel.integralSample,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [cells,
        Basic.PathModel.integralSample,
        List.foldr_cons, stationaryModel_integralSample,
        Basic.zero_add]
      exact cells_integralSample tail

end

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The switched model has exactly the total weighted allowance of its geometric parent models. -/
theorem cells_totalWeightedAllowance {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (Basic.PathModel.mk
        chain.cells).totalWeightedAllowance =
        (Basic.PathModel.mk
          (parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := cells_totalWeightedAllowance tail
      change
        tail.cells.foldr (fun cell total => cell.weightedAllowance + total) 0 =
          (remaining.map
            PreparedSubdivisionModelCore.CenteredEdge.model).foldr
              (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      simp only [cells, List.map,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [cells,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, stationaryModel_weightedAllowance,
        Fraction.Field.zero_add]
      exact cells_totalWeightedAllowance tail

/-- A natural-number count casts to a nonnegative rational coordinate. -/
theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Stationary switches increase aggregate allowance by at most their count plus one.

The weighted allowance is unchanged; the bound accounts for the larger total cell count, including the empty-parent
case. -/
theorem cells_aggregateAllowance_le_switchFactor {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (Basic.PathModel.mk
        chain.cells).aggregateAllowance <=
      ((chain.switchCount : Coordinate) + 1) *
        (Basic.PathModel.mk
          (parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance := by
  unfold Basic.PathModel.aggregateAllowance
  rw [cells_length, cells_totalWeightedAllowance]
  cases parents with
  | nil =>
      unfold Basic.PathModel.totalWeightedAllowance
      simp only [List.map, List.length_nil, List.foldr_nil,
        Fraction.Field.mul_zero_direct]
      exact le_rfl
  | cons parent remaining =>
      let weighted :=
        (Basic.PathModel.mk
          ((parent :: remaining).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance
      have weightedNonnegative : 0 <= weighted :=
        Basic.PathModel.totalWeightedAllowance_nonneg _
      have remainingNonnegative :
          (0 : Coordinate) <= (remaining.length : Coordinate) :=
        coordinateNatCast_nonnegative remaining.length
      have switchesNonnegative :
          (0 : Coordinate) <= (chain.switchCount : Coordinate) :=
        coordinateNatCast_nonnegative chain.switchCount
      have countLe :
          (((parent :: remaining).length + chain.switchCount : Nat) :
              Coordinate) <=
            ((chain.switchCount : Coordinate) + 1) *
              ((parent :: remaining).length : Coordinate) := by
        have productNonnegative :
            0 <= (chain.switchCount : Coordinate) *
              (remaining.length : Coordinate) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct switchesNonnegative
            remainingNonnegative
        simp only [List.length_cons, NatCast.add, Nat.cast_succ]
        calc
          ((remaining.length : Coordinate) + 1) +
                (chain.switchCount : Coordinate) <=
              ((remaining.length : Coordinate) + 1) +
                (chain.switchCount : Coordinate) +
                  (chain.switchCount : Coordinate) *
                    (remaining.length : Coordinate) :=
            le_add_of_nonneg_right productNonnegative
          _ = ((chain.switchCount : Coordinate) + 1) *
              ((remaining.length : Coordinate) + 1) := by ring1
      simp only [Map.length_map]
      change
        (((parent :: remaining).length + chain.switchCount : Nat) :
            Coordinate) * weighted <=
          ((chain.switchCount : Coordinate) + 1) *
            (((parent :: remaining).length : Coordinate) * weighted)
      calc
        (((parent :: remaining).length + chain.switchCount : Nat) :
              Coordinate) * weighted <=
            (((chain.switchCount : Coordinate) + 1) *
              ((parent :: remaining).length : Coordinate)) * weighted :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countLe
            weightedNonnegative
        _ = ((chain.switchCount : Coordinate) + 1) *
            (((parent :: remaining).length : Coordinate) * weighted) := by
          ring1

/-- The recast aggregate allowance is the parent-plus-switch count times the recast weighted allowance. -/
theorem recastCells_aggregateAllowance_eq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus)
    {parents : List (CenteredEdge curve source)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (Basic.PathModel.mk
      (chain.recastCells target)).aggregateAllowance =
      ((parents.length + chain.switchCount : Nat) : Coordinate) *
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance := by
  unfold Basic.PathModel.aggregateAllowance
  rw [recastCells_length target chain,
    recastCells_totalWeightedAllowance target chain]

end

/-- One plus the stationary switch count, viewed as a rational allowance factor. -/
@[expose] def switchFactor {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {parents : List (CenteredEdge curve source)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    Coordinate :=
  (chain.switchCount : Coordinate) + 1

/-- The stationary-switch allowance factor is strictly positive.

The retained switch count casts to a nonnegative rational. Adding the original
unit slack makes the exact factor strictly positive, including zero switches. -/
theorem switchFactor_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {parents : List (CenteredEdge curve source)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    0 < chain.switchFactor :=
  Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (coordinateNatCast_nonnegative chain.switchCount) (by decide)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The recast switched allowance is bounded by the switch factor times the recast parent allowance. -/
theorem recastCells_aggregateAllowance_le_switchFactor {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus)
    {parents : List (CenteredEdge curve source)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (Basic.PathModel.mk
        (chain.recastCells target)).aggregateAllowance <=
      chain.switchFactor *
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance := by
  rw [recastCells_aggregateAllowance_eq target chain]
  cases parents with
  | nil =>
      unfold Basic.PathModel.aggregateAllowance
        Basic.PathModel.totalWeightedAllowance
      simp only [List.map, List.length_nil, List.foldr_nil,
        Fraction.Field.mul_zero_direct]
      exact le_rfl
  | cons parent remaining =>
      let weighted :=
        (Basic.PathModel.mk
          (((parent :: remaining).map
            (PreparedEdgeRecasting.recastCenteredEdge
              target)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).totalWeightedAllowance
      have weightedNonnegative : 0 <= weighted :=
        Basic.PathModel.totalWeightedAllowance_nonneg _
      have countLe :
          (((parent :: remaining).length + chain.switchCount : Nat) :
              Coordinate) <=
            chain.switchFactor *
              ((parent :: remaining).length : Coordinate) := by
        have remainingNonnegative :
            (0 : Coordinate) <= (remaining.length : Coordinate) :=
          coordinateNatCast_nonnegative remaining.length
        have switchesNonnegative :
            (0 : Coordinate) <= (chain.switchCount : Coordinate) :=
          coordinateNatCast_nonnegative chain.switchCount
        have productNonnegative :
            0 <= (chain.switchCount : Coordinate) *
              (remaining.length : Coordinate) :=
          Fraction.Order.Arithmetic.mul_nonneg_direct switchesNonnegative
            remainingNonnegative
        simp only [List.length_cons, NatCast.add, Nat.cast_succ, switchFactor]
        calc
          ((remaining.length : Coordinate) + 1) +
                (chain.switchCount : Coordinate) <=
              ((remaining.length : Coordinate) + 1) +
                (chain.switchCount : Coordinate) +
                  (chain.switchCount : Coordinate) *
                    (remaining.length : Coordinate) :=
            le_add_of_nonneg_right productNonnegative
          _ = ((chain.switchCount : Coordinate) + 1) *
              ((remaining.length : Coordinate) + 1) := by ring1
      unfold Basic.PathModel.aggregateAllowance
      simp only [Map.length_map]
      change
        (((parent :: remaining).length + chain.switchCount : Nat) :
            Coordinate) * weighted <=
          chain.switchFactor *
            (((parent :: remaining).length : Coordinate) * weighted)
      calc
        (((parent :: remaining).length + chain.switchCount : Nat) :
              Coordinate) * weighted <=
            (chain.switchFactor *
              ((parent :: remaining).length : Coordinate)) * weighted :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countLe
            weightedNonnegative
        _ = chain.switchFactor *
            (((parent :: remaining).length : Coordinate) * weighted) := by
          ring1

end SwitchedPathChain

/-- Concatenating proper parent lists preserves each retained edge's properness. -/
private theorem allParentsProper_append {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} :
    forall {first second : List (CenteredEdge curve differential)},
      PreparedDyadicRefinements.AllParentsProper first ->
      PreparedDyadicRefinements.AllParentsProper second ->
      PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParentsProper_append firstProper.2 secondProper⟩

/-- Transport the final endpoint of a lifted path along the supplied closing equality. -/
@[expose] def closeLiftedPath
    {start finish : Lifted.Basic.LiftedPoint 2}
    (path : Lifted.Basic.LiftedPath 2 start finish) (closed : finish = start) :
    Lifted.Basic.LiftedPath 2 start start := by
  subst finish
  exact path

open Purelib.Curves.Hyperelliptic.Integration in
/-- Transport the same ordered cell certificates along the supplied closing equality. -/
@[expose] def closeUniformPathCertificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    {cells : List CellModel}
    {start finish : Lifted.Basic.LiftedPoint 2}
    {path : Lifted.Basic.LiftedPath 2 start finish}
    (certificates : Algebraic.Path.Basis.UniformPathCertificates curve differential cells path)
    (closed : finish = start) :
    Algebraic.Path.Basis.UniformPathCertificates curve differential cells
      (closeLiftedPath path closed) := by
  subst finish
  exact certificates

set_option genInjectivity false in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A prepared switched chain with proper parent edges and differential allowance bounds.

The state retains exact lifted endpoints, original centered parents and their switch placement. Each target differential
has a certified bound for the recast parent models. -/
structure DirectSwitchedState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The exact lifted starting point of the retained chain. -/ start : Lifted.Basic.LiftedPoint 2
  /-- The exact lifted final point of the retained chain. -/ finish : Lifted.Basic.LiftedPoint 2
  /-- The ordered centered geometric parents, excluding stationary switches. -/ parents : List (CenteredEdge curve
    source)
  /-- Each original geometric parent has the retained properness evidence. -/ proper :
    PreparedDyadicRefinements.AllParentsProper parents
  /-- The endpoint-indexed chain of these exact parents and stationary sheet switches. -/ chain : SwitchedPathChain
    parents (start := start) (finish := finish)
  /-- The retained initial parent allowance bound for each target differential. -/ initialAllowanceBound :
    Differentials.Basic.Differential genus -> Coordinate
  /-- Each target differential's recast parent model satisfies its retained allowance bound. -/ initialAllowance_le :
    forall target : Differentials.Basic.Differential genus,
    (Basic.PathModel.mk
      ((parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          target)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      initialAllowanceBound target

constructive_injectivity DirectSwitchedState

namespace DirectSwitchedState

/-- Read the exact lifted path from the retained switched state. -/
@[expose] def path {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source) :
    Lifted.Basic.LiftedPath 2 state.start state.finish :=
  state.chain.path

/-- Read the target differential's path model from the retained switched chain. -/
@[expose] def model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differentials.Basic.Differential genus) : PathModel :=
  ⟨state.chain.recastCells target⟩

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Replace only the source differential's retained initial allowance bound.

The supplied proof certifies that bound for the unchanged parents; other differential bounds and all geometric data are
preserved. -/
@[expose] def withSourceAllowanceBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (bound : Coordinate)
    (boundLe :
      (Basic.PathModel.mk
        ((state.parents.map
          (PreparedEdgeRecasting.recastCenteredEdge
            source)).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
        bound) : DirectSwitchedState curve source where
  start := state.start
  finish := state.finish
  parents := state.parents
  proper := state.proper
  chain := state.chain
  initialAllowanceBound := fun target =>
    if target.index = source.index then bound
    else state.initialAllowanceBound target
  initialAllowance_le := by
    intro target
    if equal : target.index = source.index then
      have targetEqual : target = source := by
        cases target
        cases source
        cases equal
        rfl
      subst target
      change _ ≤ (if source.index = source.index then bound else _)
      rewrite [if_pos (Eq.refl source.index)]
      exact boundLe
    else
      change _ ≤ (if target.index = source.index then bound else _)
      rewrite [if_neg equal]
      exact state.initialAllowance_le target

/-- Every target differential model has one cell per parent edge and stationary switch. -/
@[simp] theorem model_cells_length {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differentials.Basic.Differential genus) :
    (state.model target).cells.length =
      state.parents.length + state.chain.switchCount :=
  state.chain.recastCells_length target

open Purelib.Curves.Hyperelliptic.Integration in
/-- Certify the target differential on the state's exact switched path and recast cells. -/
@[expose] def certificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differentials.Basic.Differential genus) :
    Algebraic.Path.Basis.UniformPathCertificates curve target (state.model target).cells state.path :=
  state.chain.recastCertificates target

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every target differential cell of the retained switched state has a constant polynomial. -/
@[expose] def constantCells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differentials.Basic.Differential genus) :
    Basic.PathModel.ConstantCells
      (state.model target).cells :=
  state.chain.recastConstantCells target

/-- Close the retained switched path using the supplied exact endpoint equality. -/
@[expose] def closedLift {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start) : Lifted.Closed.ClosedLiftedPath 2 where
  basepoint := state.start
  path := closeLiftedPath state.path closed

/-- Certify the same closed switched geometry for the target differential. -/
@[expose] def certifiedClosedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start)
    (target : Differentials.Basic.Differential genus) :
    PreparedCycleModels.CertifiedClosedModel curve target where
  lifted := state.closedLift closed
  cells := (state.model target).cells
  certificates := by
    unfold closedLift
    exact closeUniformPathCertificates (state.certificates target) closed

/-- Retain the supplied accurate refinement's child parents and their original switch placement.

The refined state preserves its lifted endpoints and uses the result's exact child properness and differential allowance
certificates. -/
@[expose] def refine {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
        state.parents targets target) :
    DirectSwitchedState curve source where
  start := state.start
  finish := state.finish
  parents := result.blocks.children
  proper := result.blocks.childrenProper
  chain := state.chain.refined result.blocks
  initialAllowanceBound := result.allowanceFor
  initialAllowance_le := fun differential => (result.allowanceFor_eq differential).symm.le

/-- Divide the requested switched-model tolerance by its positive stationary-switch factor. -/
@[expose] def directTarget {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Coordinate) : Coordinate :=
  target / state.chain.switchFactor

/-- A positive switched-model tolerance gives a positive direct-parent tolerance. -/
theorem directTarget_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    {target : Coordinate} (positive : 0 < target) :
    0 < state.directTarget target :=
  Fraction.Order.Field.div_pos_direct positive
    state.chain.switchFactor_positive

/-- Refine the retained proper parents for the requested differentials and switch-adjusted tolerance. -/
@[expose] def accurateRefinement {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (target : Coordinate) (positive : 0 < target) :
    PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
      state.parents targets (state.directTarget target) :=
  PreparedDirectDyadicRefinements.differentialAccurateDirectRefinement
    state.parents state.proper targets (state.directTarget target)
      (state.directTarget_positive positive)

/-- Refine the switched state using an accurate direct refinement paid at the switch-adjusted tolerance. -/
@[expose] def refineAccurately {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (target : Coordinate) (positive : 0 < target) :
    DirectSwitchedState curve source :=
  state.refine (state.accurateRefinement targets target positive)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every requested differential's refined switched model meets the supplied positive tolerance.

The proof retains the unchanged switch count and combines the direct refinement payment with the exact switch-factor
bound. -/
theorem refineAccurately_modelAllowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (target : Coordinate) (positive : 0 < target)
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    ((state.refineAccurately targets target positive).model
      differential).aggregateAllowance <= target := by
  let result := state.accurateRefinement targets target positive
  let refined := state.refine result
  have switchedBound :=
    SwitchedPathChain.recastCells_aggregateAllowance_le_switchFactor
      differential refined.chain
  have directBound := result.modelAllowance_le differential member
  have factorNonnegative : 0 <= state.chain.switchFactor :=
    state.chain.switchFactor_positive.le
  have scaledDirect :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct directBound
      factorNonnegative
  calc
    (refined.model differential).aggregateAllowance <=
        refined.chain.switchFactor *
          (Basic.PathModel.mk
            ((refined.parents.map
              (PreparedEdgeRecasting.recastCenteredEdge
                differential)).map
                  PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance :=
      switchedBound
    _ = state.chain.switchFactor *
          (Basic.PathModel.mk
            ((result.blocks.children.map
              (PreparedEdgeRecasting.recastCenteredEdge
                differential)).map
                  PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance := by
      unfold refined DirectSwitchedState.refine SwitchedPathChain.switchFactor
      rw [SwitchedPathChain.refined_switchCount]
    _ <= state.chain.switchFactor * state.directTarget target := scaledDirect
    _ = target := by
      unfold directTarget
      rw [mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne target
        state.chain.switchFactor
          (ne_of_gt state.chain.switchFactor_positive)

/-- Refinement preserves the original lifted starting point. -/
@[simp] theorem refine_start {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).start = state.start := rfl

/-- Refinement preserves the original lifted final point. -/
@[simp] theorem refine_finish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).finish = state.finish := rfl

/-- Refinement preserves every stationary sheet switch. -/
@[simp] theorem refine_switchCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {targets : List (Differentials.Basic.Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).chain.switchCount = state.chain.switchCount :=
  state.chain.refined_switchCount result.blocks

/-! ### A total common-geometry switched schedule -/

section
open Purelib.Approximation.Rational
/-- The fixed positive geometric slack at scale one and stage four. -/
@[expose] def scheduleSlack : Coordinate :=
  Geometric.Basic.quarterRadius 1 4

/-- The fixed schedule slack is strictly positive. -/
theorem scheduleSlack_positive : 0 < scheduleSlack := by
  unfold scheduleSlack
  exact Geometric.Basic.quarterRadius_pos (by decide) 4

end

/-- Sum the retained initial bounds over the ordered target differential list. -/
@[expose] def initialAllowanceBoundSum {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    List (Differentials.Basic.Differential genus) -> Coordinate
  | [] => 0
  | differential :: remaining =>
      initial.initialAllowanceBound differential +
        initialAllowanceBoundSum initial remaining

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Each retained initial allowance bound is nonnegative. -/
theorem initialAllowanceBound_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differentials.Basic.Differential genus) :
    0 <= initial.initialAllowanceBound differential :=
  (Basic.PathModel.aggregateAllowance_nonneg
    (Basic.PathModel.mk
      ((initial.parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          differential)).map
            PreparedSubdivisionModelCore.CenteredEdge.model))).trans
    (initial.initialAllowance_le differential)

/-- The finite sum of retained initial allowance bounds is nonnegative. -/
theorem initialAllowanceBoundSum_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall targets : List (Differentials.Basic.Differential genus),
      0 <= initialAllowanceBoundSum initial targets
  | [] => le_rfl
  | differential :: remaining =>
      add_nonneg (initialAllowanceBound_nonnegative initial differential)
        (initialAllowanceBoundSum_nonnegative initial remaining)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A listed differential's initial parent allowance is bounded by the whole retained bound sum.

The original differential membership identifies its retained summand. Every other
retained allowance bound is nonnegative, so the finite sum bounds that same
parent model without changing the target list. -/
theorem member_initialAllowance_le_boundSum {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differentials.Basic.Differential genus) :
    forall targets : List (Differentials.Basic.Differential genus), differential ∈ targets ->
      (Basic.PathModel.mk
        ((initial.parents.map
          (PreparedEdgeRecasting.recastCenteredEdge
            differential)).map
              PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
        initialAllowanceBoundSum initial targets
  | [], member => nomatch member
  | head :: remaining, member => by
      rcases Membership.mem_cons.mp member with equal | member
      · subst head
        exact (initial.initialAllowance_le differential).trans
          (le_add_of_nonneg_right
            (initialAllowanceBoundSum_nonnegative initial remaining))
      · exact (member_initialAllowance_le_boundSum initial differential
          remaining member).trans
            (le_add_of_nonneg_left
              (initialAllowanceBound_nonnegative initial head))

/-- The finite initial allowance-bound sum plus the fixed positive schedule slack. -/
@[expose] def scheduleBase {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) : Coordinate :=
  initialAllowanceBoundSum initial targets + scheduleSlack

/-- The schedule base is strictly positive, including for an empty target list.

The retained finite allowance sum is nonnegative and the fixed schedule slack
is strictly positive. Their original sum therefore remains above zero for every
ordered target list. -/
theorem scheduleBase_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) :
    0 < initial.scheduleBase targets := by
  unfold scheduleBase
  exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (initialAllowanceBoundSum_nonnegative initial targets)
    scheduleSlack_positive

section
open Purelib.Approximation.Rational
/-- The geometric allowance target at the successor of the given stage. -/
@[expose] def scheduleTarget {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) (index : Nat) : Coordinate :=
  Geometric.Basic.quarterRadius (initial.scheduleBase targets) (index + 1)

/-- Every retained stage target is strictly positive. -/
theorem scheduleTarget_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) (index : Nat) :
    0 < initial.scheduleTarget targets index :=
  Geometric.Basic.quarterRadius_pos
    (initial.scheduleBase_positive targets) (index + 1)

end

/-- Iterate accurate direct refinements from the exact initial switched state.

Each successor uses the preceding state's proper parent list and the target determined by the original initial state and
differential list. -/
@[expose] def refinementStates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) :
    Nat -> DirectSwitchedState curve source
  | 0 => initial
  | index + 1 =>
      let current := refinementStates initial targets index
      let result :=
        PreparedDirectDyadicRefinements.differentialAccurateDirectRefinement
          current.parents current.proper targets
            (initial.scheduleTarget targets index)
            (initial.scheduleTarget_positive targets index)
      current.refine result

/-- A lazy successor refinement retaining the exact preceding state thunk.

The successor reuses that cached state's parents and properness while obtaining its target from the original initial
thunk and stage index. -/
@[expose] def cachedRefinementSuccessor {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differentials.Basic.Differential genus))
    (previous : Thunk (DirectSwitchedState curve source))
    (index : Nat) : Thunk (DirectSwitchedState curve source) :=
  ⟨fun _ =>
    let current := previous.get
    let result :=
      PreparedDirectDyadicRefinements.differentialAccurateDirectRefinement
        current.parents current.proper targets
          (initial.get.scheduleTarget targets index)
          (initial.get.scheduleTarget_positive targets index)
    current.refine result⟩

/-- Reading the lazy successor agrees with the specified next refinement state. -/
theorem cachedRefinementSuccessor_get {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differentials.Basic.Differential genus))
    (previous : Thunk (DirectSwitchedState curve source))
    (index : Nat)
    (previous_eq :
      previous.get = initial.get.refinementStates targets index) :
    (cachedRefinementSuccessor initial targets previous index).get =
      initial.get.refinementStates targets (index + 1) := by
  rw [cachedRefinementSuccessor, previous_eq]
  rfl

set_option genInjectivity false in
/-- A finite indexed cache of lazy refinement states with exact stage equalities.

Each extension retains the prior cache and a state thunk certified against the original initial state and target
differential list. -/
inductive BoundedRefinementCache {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differentials.Basic.Differential genus)) : Nat -> Type 2
  /-- The empty prefix containing no cached stages. -/ | empty : BoundedRefinementCache initial targets 0
  /-- Retain the prior cache and append one thunk certified as its next original stage. -/ | push {count : Nat}
      (prior : BoundedRefinementCache initial targets count)
      (state : Thunk (DirectSwitchedState curve source))
      (state_eq :
        state.get = initial.get.refinementStates targets count) :
      BoundedRefinementCache initial targets (count + 1)

constructive_injectivity BoundedRefinementCache

namespace BoundedRefinementCache

/-- Read the retained state thunk at an explicitly bounded cache index.

The original cache spine supplies each predecessor capacity. Equality with its
last index selects the retained final thunk; otherwise lookup recurses into the
same retained prefix with its explicit strict bound. -/
@[expose] def get {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)} {count : Nat}
    (cache : BoundedRefinementCache initial targets count)
    (index : Nat) (within : index < count) :
    Thunk (DirectSwitchedState curve source) :=
  match cache with
  | .empty => (Nat.not_lt_zero index within).elim
  | @push _ _ _ _ _ count prior state _state_eq =>
      if equal : index = count then state
      else prior.get index
        (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp within) equal)

/-- The cached thunk reads back exactly the specified original refinement stage. -/
theorem get_state_eq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count)
    (index : Nat) (within : index < count) :
    (cache.get index within).get =
      initial.get.refinementStates targets index := by
  induction cache with
  | empty => exact (Nat.not_lt_zero index within).elim
  | @push count prior state state_eq induction =>
      change
        (if _equal : index = count then state
        else prior.get index _).get =
          initial.get.refinementStates targets index
      split
      · rename_i equal
        subst index
        exact state_eq
      · rename_i unequal
        exact induction
          (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp within) unequal)

/-- Extend the cache by its initial thunk or a lazy successor of its retained final thunk. -/
@[expose] def pushNext {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count) :
    BoundedRefinementCache initial targets (count + 1) :=
  match cache with
  | .empty => .push .empty initial rfl
  | .push prior previous previous_eq =>
      .push (.push prior previous previous_eq)
        (cachedRefinementSuccessor initial targets previous _)
        (cachedRefinementSuccessor_get initial targets previous _ previous_eq)

/-- Append the requested number of lazy successor stages to the retained cache. -/
@[expose] def extend {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count) :
    (extra : Nat) ->
      BoundedRefinementCache initial targets (count + extra)
  | 0 => by simpa only [Nat.add_zero] using cache
  | extra + 1 => by
      rw [Nat.add_succ]
      exact (cache.extend extra).pushNext

/-- Construct the finite refinement cache of the requested length from the original initial thunk. -/
@[expose] def canonical {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differentials.Basic.Differential genus)) (count : Nat) :
    BoundedRefinementCache initial targets count := by
  simpa only [Nat.zero_add] using
    (BoundedRefinementCache.empty (initial := initial)
      (targets := targets)).extend count

/-- Adding one stage preserves every earlier cached thunk exactly. -/
theorem pushNext_get {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count)
    (index : Nat) (within : index < count) :
    cache.pushNext.get index (Nat.lt_succ_of_lt within) =
      cache.get index within := by
  cases cache with
  | empty => exact (Nat.not_lt_zero index within).elim
  | @push priorCount prior state state_eq =>
      change
        (if _equal : index = priorCount + 1 then
          cachedRefinementSuccessor initial targets state priorCount
        else
          (BoundedRefinementCache.push prior state state_eq).get index _) =
        (BoundedRefinementCache.push prior state state_eq).get index within
      split
      · rename_i equal
        exact (Nat.ne_of_lt within equal).elim
      · rfl

/-- Extending the cache preserves every earlier cached thunk exactly. -/
theorem extend_get {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differentials.Basic.Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count)
    (index : Nat) (within : index < count) :
    forall extra : Nat,
      (cache.extend extra).get index
        (within.trans_le (Nat.le_add_right count extra)) =
          cache.get index within
  | 0 => by rfl
  | extra + 1 => by
      rw [show cache.extend (extra + 1) =
          (cache.extend extra).pushNext by rfl]
      rw [(cache.extend extra).pushNext_get index
        (within.trans_le (Nat.le_add_right count extra))]
      exact cache.extend_get index within extra

end BoundedRefinementCache

/-- The accurate parent refinement used between two successive retained stages. -/
@[expose] def scheduledRefinement {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) (index : Nat) :
    PreparedDirectDyadicRefinements.DifferentialAccurateDirectRefinement
      (initial.refinementStates targets index).parents targets
        (initial.scheduleTarget targets index) :=
  PreparedDirectDyadicRefinements.differentialAccurateDirectRefinement
    (initial.refinementStates targets index).parents
    (initial.refinementStates targets index).proper targets
      (initial.scheduleTarget targets index)
      (initial.scheduleTarget_positive targets index)

/-- Read the recast geometric parent model at a stage, excluding stationary switches. -/
@[expose] def flatModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) : PathModel :=
  ⟨(((initial.refinementStates targets index).parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model)⟩

/-- The endpoint-based real lower sum of the stage's recast parent edges. -/
@[expose] def flatModelIntegralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) : Coordinate :=
  PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
    ((initial.refinementStates targets index).parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential))

/-- The retained-ball real lower sum of the stage's recast parent edges. -/
@[expose] def flatModelBallIntegralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) : Coordinate :=
  PreparedSubdivisionModelCore.centeredEdgesBallIntegralRealLower
    ((initial.refinementStates targets index).parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential))

/-- For exponent zero, the endpoint-based lower sum bounds the flat model's real integral sample. -/
theorem flatModelIntegralRealLower_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelIntegralRealLower targets differential index <=
      (initial.flatModel targets differential index).integralSample.re := by
  exact
    PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_le
      exponentZero _

/-- For exponent zero, the retained-ball lower sum bounds the flat model's real integral sample. -/
theorem flatModelBallIntegralRealLower_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelBallIntegralRealLower targets differential index <=
      (initial.flatModel targets differential index).integralSample.re := by
  exact
    PreparedSubdivisionModelCore.centeredEdgesBallIntegralRealLower_le
      exponentZero _

/-- The endpoint-based lower sum in the supplied Gaussian direction. -/
@[expose] def flatModelDirectionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) : Coordinate :=
  PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
    direction
      ((initial.refinementStates targets index).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          differential))

/-- The retained-ball lower sum in the supplied Gaussian direction. -/
@[expose] def flatModelBallDirectionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) : Coordinate :=
  PreparedSubdivisionModelCore.centeredEdgesBallDirectionalIntegralLower
    direction
      ((initial.refinementStates targets index).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          differential))

/-- For exponent zero, the endpoint-based lower sum bounds the sample's scalar projection. -/
theorem flatModelDirectionalIntegralLower_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelDirectionalIntegralLower targets differential direction
        index <=
      direction.re * (initial.flatModel targets differential index).integralSample.re +
        direction.im *
          (initial.flatModel targets differential index).integralSample.im := by
  exact
    PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_le
      direction exponentZero _

/-- For exponent zero, the retained-ball lower sum bounds the sample's scalar projection. -/
theorem flatModelBallDirectionalIntegralLower_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelBallDirectionalIntegralLower targets differential direction
        index <=
      direction.re * (initial.flatModel targets differential index).integralSample.re +
        direction.im *
          (initial.flatModel targets differential index).integralSample.im := by
  exact
    PreparedSubdivisionModelCore.centeredEdgesBallDirectionalIntegralLower_le
      direction exponentZero _

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The exact compatible constant-cell refinement between successive flat differential models. -/
@[expose] def flatRefinementStep {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    Basic.PathModel.CompatibleConstantPathRefinement
      (initial.flatModel targets differential index).cells
      (initial.flatModel targets differential (index + 1)).cells := by
  change Basic.PathModel.CompatibleConstantPathRefinement
    ((((initial.refinementStates targets index).parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model))
    ((((initial.scheduledRefinement targets index).blocks.children.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential)).map
          PreparedSubdivisionModelCore.CenteredEdge.model))
  exact (initial.scheduledRefinement targets index).compatible differential

/-- A requested differential's initial flat allowance is bounded by the schedule base. -/
theorem initialFlatModelAllowance_le_base {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    (initial.flatModel targets differential 0).aggregateAllowance <=
      initial.scheduleBase targets := by
  unfold flatModel refinementStates scheduleBase
  exact
    (member_initialAllowance_le_boundSum initial differential targets
      member).trans
        (le_add_of_nonneg_right scheduleSlack_positive.le)

section
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Every requested flat model meets the geometric allowance bound at its exact stage. -/
theorem flatModel_allowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    forall index,
      (initial.flatModel targets differential index).aggregateAllowance <=
        Geometric.Basic.quarterRadius
          (initial.scheduleBase targets) index
  | 0 => by
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct] using
          initial.initialFlatModelAllowance_le_base targets differential member
  | index + 1 => by
      change
        (Basic.PathModel.mk
          ((((initial.scheduledRefinement targets index).blocks.children.map
            (PreparedEdgeRecasting.recastCenteredEdge
              differential)).map
                PreparedSubdivisionModelCore.CenteredEdge.model))).aggregateAllowance <=
          initial.scheduleTarget targets index
      exact (initial.scheduledRefinement targets index).modelAllowance_le
        differential member

/-- Successive flat comparisons meet the geometric bound with three times the schedule base. -/
theorem flatRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets)
    (index : Nat) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (initial.flatRefinementStep
      targets differential index)) <=
      Geometric.Basic.quarterRadius
        (3 * initial.scheduleBase targets) index := by
  let result := initial.scheduledRefinement targets index
  have comparisonBound := result.comparisonAllowance_le differential member
  have parentBound := initial.flatModel_allowance_le targets differential
    member index
  have doubledParent :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent :
      initial.scheduleTarget targets index <=
        Geometric.Basic.quarterRadius
          (initial.scheduleBase targets) index :=
    quarterRadius_antitone
      (initial.scheduleBase_positive targets).le (Nat.le_succ index)
  change
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (result.compatible
      differential)) <=
      Geometric.Basic.quarterRadius
        (3 * initial.scheduleBase targets) index
  calc
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (result.compatible
      differential)) <=
        2 * (initial.flatModel targets differential index).aggregateAllowance +
          initial.scheduleTarget targets index := comparisonBound
    _ <= 2 * Geometric.Basic.quarterRadius
            (initial.scheduleBase targets) index +
          Geometric.Basic.quarterRadius
            (initial.scheduleBase targets) index :=
      add_le_add doubledParent targetLeParent
    _ = Geometric.Basic.quarterRadius
        (3 * initial.scheduleBase targets) index := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end

open Purelib.Integration.Program in
/-- Package the flat differential models and successive refinements with scale three times the schedule base.

The exact model sequence and constant-cell witnesses supply finite geometric comparison bounds and the retained initial
allowance payment. -/
@[expose] def flatSequentialProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram
    where
  model := initial.flatModel targets differential
  steps := initial.flatRefinementStep targets differential
  stepScale := 3 * initial.scheduleBase targets
  stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (initial.scheduleBase_positive targets).le
  initialAllowance_le := by
    have initialBound := initial.initialFlatModelAllowance_le_base targets
      differential member
    have baseNonnegative := (initial.scheduleBase_positive targets).le
    calc
      (initial.flatModel targets differential 0).aggregateAllowance <=
          initial.scheduleBase targets := initialBound
      _ = 1 * initial.scheduleBase targets := by ring1
      _ <= 12 * initial.scheduleBase targets :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * initial.scheduleBase targets) := by ring1
  comparisonAllowance_le :=
    initial.flatRefinementStep_comparisonAllowance_le targets differential member

/-- Every refinement stage retains the initial stationary switch count. -/
@[simp] theorem refinementStates_switchCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) :
    forall index,
      (initial.refinementStates targets index).chain.switchCount =
        initial.chain.switchCount
  | 0 => rfl
  | index + 1 => by
      change
        ((initial.refinementStates targets index).refine
          (initial.scheduledRefinement targets index)).chain.switchCount =
            initial.chain.switchCount
      rw [refine_switchCount,
        initial.refinementStates_switchCount targets index]

/-- An initial stationary switch guarantees a nonempty model at every stage and differential. -/
theorem refinementStates_model_cells_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus)
    (hasSwitch : 0 < initial.chain.switchCount)
    (index : Nat) :
    0 < ((initial.refinementStates targets index).model
      differential).cells.length := by
  rw [model_cells_length,
    initial.refinementStates_switchCount targets index]
  omega0

/-- Every refinement stage retains the initial lifted starting point. -/
@[simp] theorem refinementStates_start {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) :
    forall index,
      (initial.refinementStates targets index).start = initial.start
  | 0 => rfl
  | index + 1 => by
      change (initial.refinementStates targets index).start = initial.start
      exact initial.refinementStates_start targets index

/-- Every refinement stage retains the initial lifted final point. -/
@[simp] theorem refinementStates_finish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus)) :
    forall index,
      (initial.refinementStates targets index).finish = initial.finish
  | 0 => rfl
  | index + 1 => by
      change (initial.refinementStates targets index).finish = initial.finish
      exact initial.refinementStates_finish targets index

/-- An initially closed switched path stays closed at every refinement stage. -/
theorem refinementStates_closed {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (closed : initial.finish = initial.start) :
    forall index,
      (initial.refinementStates targets index).finish =
        (initial.refinementStates targets index).start
  | index => by
      rw [initial.refinementStates_finish targets index,
        initial.refinementStates_start targets index]
      exact closed

/-- The switched and flat differential models have exactly the same integral sample. -/
theorem model_integralSample_eq_flatModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    ((initial.refinementStates targets index).model
        differential).integralSample =
      (initial.flatModel targets differential index).integralSample :=
  SwitchedPathChain.recastCells_integralSample differential
    (initial.refinementStates targets index).chain

/-- A positive literal real lower certificate for the exact recast parents at a refinement stage. -/
abbrev FlatPositiveLiteralRealLowerCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat) :=
  PreparedSubdivisionModelCore.CenteredPathRecache.PositiveLiteralRealLowerCertificate
    ((initial.refinementStates targets index).parents.map
      (PreparedEdgeRecasting.recastCenteredEdge
        differential))

/-- The retained literal lower value bounds the corresponding switched model's real integral sample. -/
theorem FlatPositiveLiteralRealLowerCertificate.lower_le_model
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {initial : DirectSwitchedState curve source}
    {targets : List (Differentials.Basic.Differential genus)}
    {differential : Differentials.Basic.Differential genus} {index : Nat}
    (certificate : FlatPositiveLiteralRealLowerCertificate initial targets
      differential index) :
    certificate.lower <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact certificate.lower_le_canonical

/-- For exponent zero, the endpoint-based flat lower sum also bounds the switched sample's real part. -/
theorem flatModelIntegralRealLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelIntegralRealLower targets differential index <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelIntegralRealLower_le targets differential index
    exponentZero

/-- For exponent zero, the ball-based flat lower sum also bounds the switched sample's real part. -/
theorem flatModelBallIntegralRealLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelBallIntegralRealLower targets differential index <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelBallIntegralRealLower_le targets differential index
    exponentZero

/-- For exponent zero, the endpoint-based flat lower sum bounds the switched sample's directional projection. -/
theorem flatModelDirectionalIntegralLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelDirectionalIntegralLower targets differential direction
        index <=
      direction.re *
          ((initial.refinementStates targets index).model
            differential).integralSample.re +
        direction.im *
          ((initial.refinementStates targets index).model
            differential).integralSample.im := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelDirectionalIntegralLower_le targets differential
    direction index exponentZero

/-- For exponent zero, the ball-based flat lower sum bounds the switched sample's directional projection. -/
theorem flatModelBallDirectionalIntegralLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelBallDirectionalIntegralLower targets differential direction
        index <=
      direction.re *
          ((initial.refinementStates targets index).model
            differential).integralSample.re +
        direction.im *
          ((initial.refinementStates targets index).model
            differential).integralSample.im := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelBallDirectionalIntegralLower_le targets differential
    direction index exponentZero

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Evaluate the initial recast parent sample with the supplied balanced-summation fuel. -/
@[expose] def balancedInitialIntegralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differentials.Basic.Differential genus) (fuel : Nat) : Gaussian :=
  Basic.PathModel.balancedMappedIntegralSample
    fuel initial.parents
      (fun parent =>
        PreparedSubdivisionModelCore.CenteredEdge.model
          (PreparedEdgeRecasting.recastCenteredEdge
            differential parent))

/-- The initial switched sample equals the balanced parent evaluation for every fuel value.

Both evaluations read the same recast parent sequence. Structural map readback
and the original balanced-sum certificate identify the exact samples for the
supplied finite fuel. -/
theorem model_zero_integralSample_eq_balanced {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (fuel : Nat) :
    ((initial.refinementStates targets 0).model differential).integralSample =
      initial.balancedInitialIntegralSample differential fuel := by
  rw [initial.model_integralSample_eq_flatModel targets differential 0]
  unfold flatModel balancedInitialIntegralSample
  simp only [refinementStates, Map.map_map]
  rw [Basic.PathModel.integralSample_eq_tailIntegralSample,
    Basic.PathModel.tailIntegralSample_map]
  exact
    (Basic.PathModel.balancedMappedIntegralSample_eq
      (fun parent =>
        PreparedSubdivisionModelCore.CenteredEdge.model
          (PreparedEdgeRecasting.recastCenteredEdge
            differential parent)) fuel initial.parents).symm

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
/-- The refinement program for the retained switched differential models.

Its allowance and comparison scale includes the fixed stationary-switch factor; integral samples and their uniform bound
come from the exact flat models. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    Gaussian.Basic.RefinementProgram := by
  let flat :=
    (initial.flatSequentialProgram targets differential member).toRefinementProgram
  let factor := initial.chain.switchFactor
  have factorNonnegative : 0 <= factor :=
    initial.chain.switchFactor_positive.le
  have oneLeFactor : (1 : Coordinate) <= factor := by
    unfold factor SwitchedPathChain.switchFactor
    exact le_add_of_nonneg_left
      (SwitchedPathChain.coordinateNatCast_nonnegative
        initial.chain.switchCount)
  exact
    { model := fun index =>
        (initial.refinementStates targets index).model differential
      errorScale := factor * flat.errorScale
      errorScale_nonneg :=
        Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
          flat.errorScale_nonneg
      modelAllowance_le := by
        intro index
        have switchedBound :=
          SwitchedPathChain.recastCells_aggregateAllowance_le_switchFactor
            differential (initial.refinementStates targets index).chain
        have flatBound := flat.modelAllowance_le index
        have scaledFlat :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct flatBound
            factorNonnegative
        calc
          ((initial.refinementStates targets index).model
              differential).aggregateAllowance <=
              (initial.refinementStates targets index).chain.switchFactor *
                (initial.flatModel targets differential index).aggregateAllowance :=
            switchedBound
          _ = factor *
                (initial.flatModel targets differential index).aggregateAllowance := by
            unfold factor SwitchedPathChain.switchFactor
            rw [initial.refinementStates_switchCount targets index]
          _ <= factor * Geometric.Basic.quarterRadius
                flat.errorScale index := scaledFlat
          _ = Geometric.Basic.quarterRadius
              (factor * flat.errorScale) index := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      later_close := by
        intro earlier later order
        rw [initial.model_integralSample_eq_flatModel targets differential,
          initial.model_integralSample_eq_flatModel targets differential]
        have flatClose := flat.later_close (earlier := earlier) (later := later) order
        rw [← Norm.Basic.normSq_eq_canonical]
        have radiusNonnegative := Geometric.Basic.quarterRadius_nonneg
          flat.errorScale_nonneg earlier
        calc
          Data.Gaussian.Norm.Basic.normSq
              ((initial.flatModel targets differential later).integralSample -
                (initial.flatModel targets differential earlier).integralSample) <=
              Geometric.Basic.quarterRadius flat.errorScale earlier :=
            (Norm.Basic.normSq_eq_canonical _).trans_le flatClose
          _ = 1 * Geometric.Basic.quarterRadius flat.errorScale earlier := by
            ring1
          _ <= factor *
                Geometric.Basic.quarterRadius flat.errorScale earlier :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              oneLeFactor radiusNonnegative
          _ = Geometric.Basic.quarterRadius
              (factor * flat.errorScale) earlier := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      centerBound := flat.centerBound
      centerBound_nonneg := flat.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [initial.model_integralSample_eq_flatModel targets differential]
        exact flat.sample_bounded index }

/-- The switched error scale is the switch factor times twelve times the schedule base. -/
theorem integral_errorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differentials.Basic.Differential genus))
    (differential : Differentials.Basic.Differential genus) (member : differential ∈ targets) :
    (initial.integral targets differential member).errorScale =
      initial.chain.switchFactor *
        (4 * (3 * initial.scheduleBase targets)) := rfl

/-! ### Source-centred switched schedules

The common-differential constructor above deliberately recentres every target,
including the source.  A generated literal comparison may instead select a
later persisted source centre.  The following source-only schedule retains
those centres at index zero and then uses the ordinary direct child centres.
-/

/-- The source differential's initial allowance bound plus the fixed positive slack. -/
@[expose] def sourceScheduleBase {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) : Coordinate :=
  initial.initialAllowanceBound source + scheduleSlack

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The source schedule base is strictly positive. -/
theorem sourceScheduleBase_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    0 < initial.sourceScheduleBase := by
  unfold sourceScheduleBase
  exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    ((Basic.PathModel.aggregateAllowance_nonneg _).trans
      (initial.initialAllowance_le source))
    scheduleSlack_positive

section
open Purelib.Approximation.Rational
/-- The source-only geometric target at the successor stage. -/
@[expose] def sourceScheduleTarget {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : Coordinate :=
  Geometric.Basic.quarterRadius initial.sourceScheduleBase (index + 1)

/-- Every source-only stage target is strictly positive. -/
theorem sourceScheduleTarget_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    0 < initial.sourceScheduleTarget index :=
  Geometric.Basic.quarterRadius_pos
    initial.sourceScheduleBase_positive (index + 1)

end

/-- Refine the source parents with the supplied exact accurate-refinement result.

The state retains the original lifted endpoints and stationary switches while adopting the result's child parents,
properness and differential bounds. -/
@[expose] def refineSource {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    {target : Coordinate}
    (result :
      PreparedDirectDyadicRefinements.AccurateDirectRefinement
        state.parents target) : DirectSwitchedState curve source where
  start := state.start
  finish := state.finish
  parents := result.blocks.children
  proper := result.blocks.childrenProper
  chain := state.chain.refined result.blocks
  initialAllowanceBound := result.allowanceFor
  initialAllowance_le := fun differential => (result.allowanceFor_eq differential).symm.le

/-- Iterate source-only accurate refinements from the retained initial state.

Every successor uses its predecessor's exact proper parents and the original initial state's geometric target. -/
@[expose] def sourceRefinementStates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    Nat -> DirectSwitchedState curve source
  | 0 => initial
  | index + 1 =>
      let current := sourceRefinementStates initial index
      let result :=
        PreparedDirectDyadicRefinements.accurateDirectRefinement
          current.parents current.proper
            (initial.sourceScheduleTarget index)
            (initial.sourceScheduleTarget_positive index)
      current.refineSource result

/-- The exact source-only parent refinement between successive stages. -/
@[expose] def sourceScheduledRefinement {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    PreparedDirectDyadicRefinements.AccurateDirectRefinement
      (initial.sourceRefinementStates index).parents
        (initial.sourceScheduleTarget index) :=
  PreparedDirectDyadicRefinements.accurateDirectRefinement
    (initial.sourceRefinementStates index).parents
    (initial.sourceRefinementStates index).proper
    (initial.sourceScheduleTarget index)
    (initial.sourceScheduleTarget_positive index)

/-- Read the geometric source parent models at a stage, excluding stationary switches. -/
@[expose] def sourceFlatModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : PathModel :=
  ⟨((initial.sourceRefinementStates index).parents.map
    PreparedSubdivisionModelCore.CenteredEdge.model)⟩

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The compatible constant-cell refinement between successive flat source models. -/
@[expose] def sourceFlatRefinementStep {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    Basic.PathModel.CompatibleConstantPathRefinement
      (initial.sourceFlatModel index).cells
      (initial.sourceFlatModel (index + 1)).cells := by
  change Basic.PathModel.CompatibleConstantPathRefinement
    ((initial.sourceRefinementStates index).parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)
    ((initial.sourceScheduledRefinement index).blocks.children.map
      PreparedSubdivisionModelCore.CenteredEdge.model)
  exact (initial.sourceScheduledRefinement index).blocks.toCompatibleChildren

section
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Every flat source model meets its stage's geometric allowance bound. -/
theorem sourceFlatModel_allowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index,
      (initial.sourceFlatModel index).aggregateAllowance <=
        Geometric.Basic.quarterRadius initial.sourceScheduleBase index
  | 0 => by
      unfold sourceFlatModel sourceRefinementStates sourceScheduleBase
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct]
      calc
        (Basic.PathModel.mk
            (initial.parents.map
              PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance =
            (Basic.PathModel.mk
              ((initial.parents.map
                (PreparedEdgeRecasting.recastCenteredEdge
                  source)).map
                    PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance :=
          (PreparedDirectDyadicRefinements.recastCenteredEdges_self_aggregateAllowance
            initial.parents).symm
        _ <= initial.initialAllowanceBound source :=
          initial.initialAllowance_le source
        _ <= initial.initialAllowanceBound source + scheduleSlack :=
          le_add_of_nonneg_right scheduleSlack_positive.le
  | index + 1 => by
      change
        (Basic.PathModel.mk
          ((initial.sourceScheduledRefinement index).blocks.children.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
          initial.sourceScheduleTarget index
      exact (initial.sourceScheduledRefinement index).modelAllowance_le

/-- Each source-only comparison meets the bound with three times the source schedule base. -/
theorem sourceFlatRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      (initial.sourceFlatRefinementStep index)) <=
      Geometric.Basic.quarterRadius
        (3 * initial.sourceScheduleBase) index := by
  have comparisonBound :=
    (initial.sourceScheduledRefinement index).comparisonAllowanceChildren_le
  have parentBound := initial.sourceFlatModel_allowance_le index
  have doubledParent :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent : initial.sourceScheduleTarget index <=
      Geometric.Basic.quarterRadius initial.sourceScheduleBase index :=
    quarterRadius_antitone
      initial.sourceScheduleBase_positive.le (Nat.le_succ index)
  calc
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      (initial.sourceFlatRefinementStep index)) <=
        2 * (initial.sourceFlatModel index).aggregateAllowance +
          initial.sourceScheduleTarget index := comparisonBound
    _ <= 2 * Geometric.Basic.quarterRadius
            initial.sourceScheduleBase index +
          Geometric.Basic.quarterRadius
            initial.sourceScheduleBase index :=
      add_le_add doubledParent targetLeParent
    _ = Geometric.Basic.quarterRadius
        (3 * initial.sourceScheduleBase) index := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end

open Purelib.Approximation.Rational in
open Purelib.Integration.Program in
/-- Package the source-only flat models and consecutive compatible refinements.

The program retains their exact cell sequence and uses three times the source schedule base for its geometric comparison
scale. -/
@[expose] def sourceFlatSequentialProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram
    where
  model := initial.sourceFlatModel
  steps := initial.sourceFlatRefinementStep
  stepScale := 3 * initial.sourceScheduleBase
  stepScale_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    initial.sourceScheduleBase_positive.le
  initialAllowance_le := by
    have baseNonnegative := initial.sourceScheduleBase_positive.le
    calc
      (initial.sourceFlatModel 0).aggregateAllowance <=
          initial.sourceScheduleBase := by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using
            initial.sourceFlatModel_allowance_le 0
      _ = 1 * initial.sourceScheduleBase := by ring1
      _ <= 12 * initial.sourceScheduleBase :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * initial.sourceScheduleBase) := by ring1
  comparisonAllowance_le := initial.sourceFlatRefinementStep_comparisonAllowance_le

/-- Every source-only stage preserves the initial stationary switch count. -/
@[simp] theorem sourceRefinementStates_switchCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index,
      (initial.sourceRefinementStates index).chain.switchCount =
        initial.chain.switchCount
  | 0 => rfl
  | index + 1 => by
      change
        ((initial.sourceRefinementStates index).chain.refined
          (initial.sourceScheduledRefinement index).blocks).switchCount =
            initial.chain.switchCount
      rw [SwitchedPathChain.refined_switchCount,
        initial.sourceRefinementStates_switchCount index]

/-- Every source-only stage preserves the initial lifted starting point. -/
@[simp] theorem sourceRefinementStates_start {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index, (initial.sourceRefinementStates index).start = initial.start
  | 0 => rfl
  | index + 1 => initial.sourceRefinementStates_start index

/-- Every source-only stage preserves the initial lifted final point. -/
@[simp] theorem sourceRefinementStates_finish {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index, (initial.sourceRefinementStates index).finish = initial.finish
  | 0 => rfl
  | index + 1 => initial.sourceRefinementStates_finish index

/-- Source-only refinement preserves the supplied initial closing equality. -/
theorem sourceRefinementStates_closed {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (closed : initial.finish = initial.start) :
    forall index,
      (initial.sourceRefinementStates index).finish =
        (initial.sourceRefinementStates index).start
  | index => by
      rw [initial.sourceRefinementStates_finish index,
        initial.sourceRefinementStates_start index]
      exact closed

/-- Read the complete switched source model at the retained refinement stage. -/
@[expose] def sourceModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : PathModel :=
  ⟨(initial.sourceRefinementStates index).chain.cells⟩

/-- The complete switched source sample equals its flat parent sample exactly. -/
theorem sourceModel_integralSample_eq_flatModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    (initial.sourceModel index).integralSample =
      (initial.sourceFlatModel index).integralSample :=
  SwitchedPathChain.cells_integralSample
    (initial.sourceRefinementStates index).chain

namespace SourceCache

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- One cached source refinement stage with its exact index and state equality.

The retained thunk is certified against the same original initial thunk, so successor entries can reuse its computed
state. -/
structure Entry (initial : Thunk (DirectSwitchedState curve source)) where
  /-- The original source refinement index of this cached entry. -/ index : Nat
  /-- The retained lazy state at the certified source refinement index. -/ state : Thunk (DirectSwitchedState curve
    source)
  /-- Reading the retained thunk gives exactly the source refinement at its stored index. -/ state_eq : state.get =
    initial.get.sourceRefinementStates index

constructive_injectivity Entry

/-- The initial source-cache entry at stage zero, retaining the supplied thunk. -/
@[expose] def first (initial : Thunk (DirectSwitchedState curve source)) : Entry initial :=
  ⟨0, initial, rfl⟩

/-- The lazy source-refinement successor of the exact retained cache entry.

It reads the predecessor's cached parents and properness and preserves the certified equality to the original stage
sequence. -/
@[expose] def Entry.next {initial : Thunk (DirectSwitchedState curve source)}
    (entry : Entry initial) : Entry initial where
  index := entry.index + 1
  state := ⟨fun _ =>
    let current := entry.state.get
    let refinement :=
      PreparedDirectDyadicRefinements.accurateDirectRefinement
        current.parents current.proper (initial.get.sourceScheduleTarget entry.index)
        (initial.get.sourceScheduleTarget_positive entry.index)
    current.refineSource refinement⟩
  state_eq := by
    change (entry.state.get.refineSource _) = _
    rw [entry.state_eq]
    rfl

set_option genInjectivity false in
/-- A finite prefix of certified source-stage entries in exact index order.

Appending an entry retains the entire earlier prefix and proves that the new entry's index equals its position. -/
inductive Prefix (initial : Thunk (DirectSwitchedState curve source)) : Nat → Type 2
  /-- The empty prefix containing no cached stages. -/ | empty : Prefix initial 0
  /-- Retain the previous prefix and append an entry whose index is the next position. -/ | snoc {count : Nat} (prior :
    Prefix initial count) (entry : Entry initial)
      (index_eq : entry.index = count) : Prefix initial (count + 1)

constructive_injectivity Prefix

namespace Prefix

/-- Append the initial entry or the lazy successor of the retained last source entry. -/
@[expose] def push {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) : Prefix initial (count + 1) :=
  match cache with
  | .empty => .snoc .empty (first initial) rfl
  | .snoc prior entry equal =>
      .snoc (.snoc prior entry equal) entry.next (congrArg (· + 1) equal)

/-- Append the requested number of lazy successor stages to the retained cache. -/
@[expose] def extend {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) : (extra : Nat) → Prefix initial (count + extra)
  | 0 => cache
  | extra + 1 => (cache.extend extra).push

/-- Construct the source prefix in stage order by retaining each predecessor entry. -/
@[expose] def canonical (initial : Thunk (DirectSwitchedState curve source)) :
    (count : Nat) → Prefix initial count
  | 0 => .empty
  | count + 1 => (canonical initial count).push

/-- Read the retained state thunk at an explicitly bounded cache index. -/
@[expose] def get {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) (index : Nat) (within : index < count) :
    Thunk (DirectSwitchedState curve source) :=
  match cache with
  | .empty => (Nat.not_lt_zero index within).elim
  | @snoc _ _ _ _ count prior entry _ =>
      if old : index < count then prior.get index old else entry.state

/-- Reading a bounded source-cache entry gives the exact original source refinement stage. -/
theorem get_eq {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) (index : Nat) (within : index < count) :
    (cache.get index within).get = initial.get.sourceRefinementStates index := by
  induction cache with
  | empty => exact (Nat.not_lt_zero index within).elim
  | @snoc count prior entry equal induction =>
      unfold get
      split
      · exact induction _
      · rename_i notOld
        have same : count = index := by omega
        exact entry.state_eq.trans (congrArg initial.get.sourceRefinementStates (equal.trans same))

/-- Appending a source-cache entry preserves every earlier state thunk exactly. -/
theorem push_get {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) (index : Nat) (within : index < count) :
    cache.push.get index (Nat.lt_succ_of_lt within) = cache.get index within := by
  cases cache with
  | empty => exact (Nat.not_lt_zero index within).elim
  | snoc prior entry equal =>
      change (if old : index < _ then _ else _) = _
      rw [dif_pos within]

/-- Extending the cache preserves every earlier cached thunk exactly. -/
theorem extend_get {initial : Thunk (DirectSwitchedState curve source)} {count : Nat}
    (cache : Prefix initial count) (extra index : Nat) (within : index < count) :
    (cache.extend extra).get index (within.trans_le (Nat.le_add_right _ _)) =
      cache.get index within := by
  induction extra with
  | zero => rfl
  | succ extra induction =>
      rw [extend, push_get]
      exact induction

end Prefix

end SourceCache

set_option genInjectivity false in
/-- A retained initial state thunk and its finite certified source-stage prefix.

Bounded reads reuse the stored state thunks; requests beyond the prefix retain the original source-refinement
computation. -/
structure SourceCache {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The exact initial source-state thunk retained by every prefix entry. -/ initial : Thunk (DirectSwitchedState curve
    source)
  /-- The number of retained cached source stages. -/ count : Nat
  /-- The certified prefix of exactly the retained number of source stages. -/ states : SourceCache.Prefix initial count

constructive_injectivity SourceCache

namespace SourceCache

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Construct the requested source prefix from the exact initial state thunk. -/
@[expose] def canonical (initial : Thunk (DirectSwitchedState curve source)) (count : Nat) :
    SourceCache curve source := ⟨initial, count, Prefix.canonical initial count⟩

/-- Append the requested number of lazy successor stages to the retained cache. -/
@[expose] def extend (cache : SourceCache curve source) (extra : Nat) : SourceCache curve source :=
  ⟨cache.initial, cache.count + extra, cache.states.extend extra⟩

/-- Read a retained cached source stage, or compute the original stage beyond the cached prefix. -/
@[expose] def state (cache : SourceCache curve source) (index : Nat) : DirectSwitchedState curve source :=
  if within : index < cache.count then (cache.states.get index within).get
  else cache.initial.get.sourceRefinementStates index

/-- A source-cache read gives exactly the original source refinement state at that index. -/
theorem state_eq (cache : SourceCache curve source) (index : Nat) :
    cache.state index = cache.initial.get.sourceRefinementStates index := by
  unfold state
  split
  · exact cache.states.get_eq index _
  · rfl

/-- Read the switched source model from the retained cached stage, with the original computation beyond the prefix. -/
@[expose] def model (cache : SourceCache curve source) (index : Nat) : PathModel :=
  ⟨(cache.state index).chain.cells⟩

/-- The model read from a source cache equals the original source model at the same stage. -/
theorem model_eq (cache : SourceCache curve source) (index : Nat) :
    cache.model index = cache.initial.get.sourceModel index := by
  rw [model, cache.state_eq]
  rfl

end SourceCache

open Purelib.Curves.Hyperelliptic.Integration in
/-- Certify the source model on the exact switched path at the retained stage. -/
@[expose] def sourceCertificates {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    Algebraic.Path.Basis.UniformPathCertificates curve source
      (initial.sourceModel index).cells
      (initial.sourceRefinementStates index).path :=
  (initial.sourceRefinementStates index).chain.certificates

/-- Certify the source cells on the switched path closed by the supplied endpoint equality. -/
@[expose] def certifiedClosedSourceModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start) :
    PreparedCycleModels.CertifiedClosedModel curve source where
  lifted := state.closedLift closed
  cells := state.chain.cells
  certificates := by
    unfold closedLift
    exact closeUniformPathCertificates state.chain.certificates closed

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
/-- The switched source integral program with a retained 64-stage lazy cache.

Its exact models read from that cache, with the original source sequence as fallback. The fixed switch factor scales the
flat allowances and comparisons while preserving the sample bound. -/
@[expose] def sourceIntegral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) :
    Gaussian.Basic.RefinementProgram := by
  let flat := initial.sourceFlatSequentialProgram.toRefinementProgram
  let cache := SourceCache.canonical (⟨fun _ => initial⟩ : Thunk _) 64
  have cacheInitial : cache.initial.get = initial := rfl
  let factor := initial.chain.switchFactor
  have factorNonnegative : 0 <= factor := initial.chain.switchFactor_positive.le
  have oneLeFactor : (1 : Coordinate) <= factor := by
    unfold factor SwitchedPathChain.switchFactor
    exact le_add_of_nonneg_left
      (SwitchedPathChain.coordinateNatCast_nonnegative
        initial.chain.switchCount)
  exact
    { model := cache.model
      errorScale := factor * flat.errorScale
      errorScale_nonneg :=
        Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
          flat.errorScale_nonneg
      modelAllowance_le := by
        intro index
        rw [cache.model_eq, cacheInitial]
        have switchedBound :=
          SwitchedPathChain.cells_aggregateAllowance_le_switchFactor
            (initial.sourceRefinementStates index).chain
        have flatBound := flat.modelAllowance_le index
        have scaledFlat :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct flatBound
            factorNonnegative
        calc
          (initial.sourceModel index).aggregateAllowance <=
              (initial.sourceRefinementStates index).chain.switchFactor *
                (initial.sourceFlatModel index).aggregateAllowance := by
            simpa only [sourceModel, sourceFlatModel,
              SwitchedPathChain.switchFactor] using switchedBound
          _ = factor * (initial.sourceFlatModel index).aggregateAllowance := by
            unfold factor SwitchedPathChain.switchFactor
            rw [initial.sourceRefinementStates_switchCount index]
          _ <= factor * Geometric.Basic.quarterRadius
                flat.errorScale index := scaledFlat
          _ = Geometric.Basic.quarterRadius
              (factor * flat.errorScale) index := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      later_close := by
        intro earlier later order
        rw [cache.model_eq, cache.model_eq, cacheInitial]
        rw [initial.sourceModel_integralSample_eq_flatModel,
          initial.sourceModel_integralSample_eq_flatModel]
        have flatClose := flat.later_close (earlier := earlier) (later := later) order
        rw [← Norm.Basic.normSq_eq_canonical]
        have radiusNonnegative := Geometric.Basic.quarterRadius_nonneg
          flat.errorScale_nonneg earlier
        calc
          Data.Gaussian.Norm.Basic.normSq
              ((initial.sourceFlatModel later).integralSample -
                (initial.sourceFlatModel earlier).integralSample) <=
              Geometric.Basic.quarterRadius flat.errorScale earlier :=
            (Norm.Basic.normSq_eq_canonical _).trans_le flatClose
          _ = 1 * Geometric.Basic.quarterRadius flat.errorScale earlier := by
            ring1
          _ <= factor *
                Geometric.Basic.quarterRadius flat.errorScale earlier :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              oneLeFactor radiusNonnegative
          _ = Geometric.Basic.quarterRadius
              (factor * flat.errorScale) earlier := by
            rw [Geometric.Basic.quarterRadius_eq_mul_pow,
              Geometric.Basic.quarterRadius_eq_mul_pow]
            ring1
      centerBound := flat.centerBound
      centerBound_nonneg := flat.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [cache.model_eq, cacheInitial]
        rw [initial.sourceModel_integralSample_eq_flatModel]
        exact flat.sample_bounded index }

/-- The cached source program's model equals the original source model at every stage. -/
theorem sourceIntegral_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    initial.sourceIntegral.model index = initial.sourceModel index :=
  (SourceCache.canonical (⟨fun _ => initial⟩ : Thunk _) 64).model_eq index

/-- A singleton target list gives that differential's initial allowance bound plus slack.

The singleton fold retains its one original allowance bound. Its empty tail
contributes zero before the fixed schedule slack is added. -/
theorem scheduleBase_singleton {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differentials.Basic.Differential genus) :
    initial.scheduleBase [differential] =
      initial.initialAllowanceBound differential + scheduleSlack := by
  change (initial.initialAllowanceBound differential + 0) + scheduleSlack = _
  exact congrArg (fun value => value + scheduleSlack)
    (_root_.add_zero (initial.initialAllowanceBound differential))

end DirectSwitchedState

set_option genInjectivity false in
/-- A closed initial switched state for source-only refinement.

The retained closing equality links the original lifted endpoints and yields closed certified models at every source
refinement stage. -/
structure SourceSwitchedClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The retained initial switched state from which this schedule or cache is derived. -/ initial : DirectSwitchedState
    curve source
  /-- The retained initial lifted endpoints are exactly equal. -/ closed : initial.finish = initial.start

constructive_injectivity SourceSwitchedClosedSchedule

namespace SourceSwitchedClosedSchedule

/-- Read the closed lifted-cycle sequence from the retained switched refinement stages. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) :
    Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    (schedule.initial.sourceRefinementStates index).closedLift
      (schedule.initial.sourceRefinementStates_closed schedule.closed index)

/-- Certify the retained closed switched model at the specified stage. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) (index : Nat) :
    PreparedCycleModels.CertifiedClosedModel curve source :=
  (schedule.initial.sourceRefinementStates index).certifiedClosedSourceModel
    (schedule.initial.sourceRefinementStates_closed schedule.closed index)

open Purelib.Curves.Hyperelliptic.Integration in
/-- Pair the retained switched integral program with certificates for its exact closed lifted-cycle sequence. -/
@[expose] def certifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve source schedule.cycle where
  integral := schedule.initial.sourceIntegral
  certificates := by
    intro index
    rw [DirectSwitchedState.sourceIntegral_model]
    exact (schedule.certifiedModel index).certificates

end SourceSwitchedClosedSchedule

set_option genInjectivity false in
/-- A closed switched state with an ordered list of target differentials.

All requested differentials share the same retained geometric stage sequence; each integral certificate remains indexed
by its own target differential. -/
structure DifferentialSwitchedClosedSchedule {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) where
  /-- The retained initial switched state from which this schedule or cache is derived. -/ initial : DirectSwitchedState
    curve source
  /-- The ordered differentials requested on the shared switched geometry. -/ targets : List
    (Differentials.Basic.Differential genus)
  /-- The retained initial lifted endpoints are exactly equal. -/ closed : initial.finish = initial.start

constructive_injectivity DifferentialSwitchedClosedSchedule

namespace DifferentialSwitchedClosedSchedule

/-- Read the closed lifted-cycle sequence from the retained switched refinement stages. -/
@[expose] def cycle {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source) :
    Lifted.Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    (schedule.initial.refinementStates schedule.targets index).closedLift
      (schedule.initial.refinementStates_closed schedule.targets
        schedule.closed index)

/-- Certify the retained closed switched model at the specified stage. -/
@[expose] def certifiedModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus) (index : Nat) :
    PreparedCycleModels.CertifiedClosedModel curve differential := by
  let state := schedule.initial.refinementStates schedule.targets index
  exact state.certifiedClosedModel
      (schedule.initial.refinementStates_closed schedule.targets
        schedule.closed index)
      differential

open Purelib.Integration.Program in
/-- Read the integral program for a differential explicitly present in the retained target list. -/
@[expose] def integral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) :
    Gaussian.Basic.RefinementProgram :=
  schedule.initial.integral schedule.targets differential member

/-- The initial program sample equals balanced evaluation of the retained recast parents for every fuel value. -/
theorem integral_model_zero_integralSample_eq_balanced {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) (fuel : Nat) :
    ((schedule.integral differential member).model 0).integralSample =
      schedule.initial.balancedInitialIntegralSample differential fuel :=
  schedule.initial.model_zero_integralSample_eq_balanced schedule.targets
    differential fuel

/-- The integral program and certified closed model retain exactly the same cell list. -/
@[simp] theorem integral_model_cells {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedModel differential index).cells := rfl

/-- An initial stationary switch guarantees a nonempty integral cell list at every stage. -/
theorem integral_model_cells_positive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets)
    (hasSwitch : 0 < schedule.initial.chain.switchCount)
    (index : Nat) :
    0 < ((schedule.integral differential member).model index).cells.length :=
  schedule.initial.refinementStates_model_cells_positive schedule.targets
    differential hasSwitch index

open Purelib.Curves.Hyperelliptic.Integration in
/-- Pair the retained switched integral program with certificates for its exact closed lifted-cycle sequence. -/
@[expose] def certifiedPeriodProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (schedule : DifferentialSwitchedClosedSchedule curve source)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ schedule.targets) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral differential member
  certificates := by
    intro index
    rw [schedule.integral_model_cells differential member index]
    exact (schedule.certifiedModel differential index).certificates

end DifferentialSwitchedClosedSchedule

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Concatenating cell lists adds their total weighted allowances. -/
private theorem totalWeightedAllowance_append
    (first second : List Basic.CellModel) :
    (Basic.PathModel.mk
      (first ++ second)).totalWeightedAllowance =
      (Basic.PathModel.mk
        first).totalWeightedAllowance +
      (Basic.PathModel.mk
        second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      rw [zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      change
        (remaining ++ second).foldr
            (fun model total => model.weightedAllowance + total) 0 =
          remaining.foldr
              (fun model total => model.weightedAllowance + total) 0 +
            second.foldr
              (fun model total => model.weightedAllowance + total) 0 at inductionHypothesis
      rw [inductionHypothesis]
      ring1

section
open Purelib.Data.Gaussian
/-- Concatenating Gaussian lists adds their sums of squared norms. -/
private theorem gaussianNormSqSum_append (first second : List Gaussian) :
    Norm.Sum.Basic.gaussianNormSqSum (first ++ second) =
      Norm.Sum.Basic.gaussianNormSqSum first +
        Norm.Sum.Basic.gaussianNormSqSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        Norm.Sum.Basic.gaussianNormSqSum]
      rw [zero_add]
  | cons value remaining inductionHypothesis =>
      simp only [List.cons_append,
        Norm.Sum.Basic.gaussianNormSqSum]
      rw [inductionHypothesis]
      ring1

/-- A finite sum of Gaussian squared norms is nonnegative. -/
private theorem gaussianNormSqSum_nonnegative : forall values : List Gaussian,
    0 <= Norm.Sum.Basic.gaussianNormSqSum values
  | [] => le_rfl
  | value :: remaining =>
      add_nonneg (by
          simpa only [Norm.Basic.normSq_eq_canonical] using
            Norm.Basic.normSq_nonneg value)
        (gaussianNormSqSum_nonnegative remaining)

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- A path model's integral sample is the Gaussian sum of its ordered cell samples. -/
private theorem pathModel_integralSample_eq_gaussianSum
    (cells : List Basic.CellModel) :
    (Basic.PathModel.mk cells).integralSample =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (cells.map fun cell => cell.integralSample) := by
  induction cells with
  | nil => rfl
  | cons cell remaining inductionHypothesis =>
      simp only [Basic.PathModel.integralSample,
        List.foldr_cons, List.map_cons,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum]
      change
        remaining.foldr (fun cell total => cell.integralSample + total) 0 =
          Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (remaining.map fun cell => cell.integralSample)
        at inductionHypothesis
      rw [inductionHypothesis]

/-- Reading samples through centered edge models preserves the original parent order.

Structural recursion reads the same integral sample at each original head.
Constructor congruence preserves the unchanged mapped tail and all repetitions. -/
private theorem centeredEdgeIntegralSamples_map_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus} :
    forall parents : List (CenteredEdge curve source),
      (parents.map
          PreparedSubdivisionModelCore.CenteredEdge.model).map
            (fun cell => cell.integralSample) =
        parents.map (fun parent => parent.model.integralSample)
  | [] => rfl
  | parent :: remaining =>
      congrArg (List.cons parent.model.integralSample)
        (centeredEdgeIntegralSamples_map_model remaining)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Build a switched state from the retained forward and reverse bridge banks.

The first bank is read on sheet zero and the second on sheet one, with stationary switches at the exact finish and start
coordinates. The parent list and certificates retain both original banks. -/
@[expose] def bridgeState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    DirectSwitchedState curve source := by
  let forward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let backward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.backwardChecked
  let forwardChain :=
    SwitchedPathChain.ofCenteredPathChain forward.chain
  let finishSwitch : SwitchedPathChain
      ([] : List (CenteredEdge curve source))
      (start := { coordinate := data.finish, sheet := 0 })
      (finish := { coordinate := data.finish, sheet := 1 }) :=
    SwitchedPathChain.singletonStationary data.finish 0
  let backwardChain :=
    SwitchedPathChain.ofCenteredPathChain backward.chain
  let startSwitch : SwitchedPathChain
      ([] : List (CenteredEdge curve source))
      (start := { coordinate := data.start, sheet := 1 })
      (finish := { coordinate := data.start, sheet := 0 }) :=
    SwitchedPathChain.singletonStationary data.start 1
  let combined := forwardChain.append
    (finishSwitch.append (backwardChain.append startSwitch))
  let parents := forward.parents ++ ([] ++ (backward.parents ++ []))
  exact
    { start := { coordinate := data.start, sheet := 0 }
      finish := { coordinate := data.start, sheet := 0 }
      parents := parents
      proper := by
        dsimp only [parents]
        rewrite [List.nil_append, Append.append_nil]
        exact allParentsProper_append forward.proper backward.proper
      chain := combined
      initialAllowanceBound := fun differential =>
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              differential)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

section
open Purelib.Curves.Hyperelliptic.Branches
/-- The sum of forward and reverse bridge segment counts at the retained shared dyadic depth. -/
@[expose] def bridgeSourceParentCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleModels.PreparedDoublePath curve) : Nat :=
  2 ^ data.depth * data.basePath.segmentCount +
    2 ^ data.depth *
      (BranchCutLifts.ClearPath.reverse
        data.basePath).segmentCount

/-- The sum of the two bridge banks' source weighted-allowance bounds. -/
@[expose] def bridgeSourceTotalWeightedBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.depth data.basePath +
    PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.depth
        (BranchCutLifts.ClearPath.reverse data.basePath)

/-- The sum of the two bridge banks' dyadic preflight weighted bounds. -/
@[expose] def bridgeSourceTotalWeightedPreflightBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.depth data.basePath +
    PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.depth
        (BranchCutLifts.ClearPath.reverse data.basePath)

/-- The sum of the two bridge banks' integral squared-norm ceiling bounds. -/
@[expose] def bridgeSourceIntegralNormSqSumBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.depth data.basePath +
    PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.depth
        (BranchCutLifts.ClearPath.reverse data.basePath)

end

/-- The bridge parent count times its total source weighted bound. -/
@[expose] def bridgeSourceAggregateBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  (bridgeSourceParentCount data : Coordinate) *
    bridgeSourceTotalWeightedBound source data

/-- The bridge parent count times its dyadic preflight weighted bound. -/
@[expose] def bridgeSourcePreflightAggregateBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  (bridgeSourceParentCount data : Coordinate) *
    bridgeSourceTotalWeightedPreflightBound source data

open Purelib.Curves.Hyperelliptic.Branches in
/-- The retained bridge aggregate bound is no larger than its dyadic preflight bound. -/
theorem bridgeSourceAggregateBound_le_preflight {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    bridgeSourceAggregateBound source data <=
      bridgeSourcePreflightAggregateBound source data := by
  unfold bridgeSourceAggregateBound bridgeSourcePreflightAggregateBound
    bridgeSourceTotalWeightedBound
    bridgeSourceTotalWeightedPreflightBound
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.depth data.basePath)
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.depth
          (BranchCutLifts.ClearPath.reverse data.basePath))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

/-- The bridge state's parents are exactly the forward bank followed by the reverse bank.

The two stationary sheet switches contribute no geometric parents. The retained
forward and reverse banks therefore appear consecutively in their original order. -/
theorem bridgeState_parents {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).parents =
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 0 data.forwardChecked).parents ++
        (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 1 data.backwardChecked).parents := by
  dsimp only [bridgeState]
  rewrite [Append.append_nil]
  exact Eq.refl _

open Purelib.Data.Gaussian in
/-- The bridge parent samples satisfy the retained squared-norm sum bound. -/
theorem bridgeState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    Norm.Sum.Basic.gaussianNormSqSum
        ((bridgeState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      bridgeSourceIntegralNormSqSumBound source data := by
  rw [bridgeState_parents]
  unfold bridgeSourceIntegralNormSqSumBound
  simp only [Map.map_append]
  rw [gaussianNormSqSum_append]
  exact add_le_add
    (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 0 data.forwardChecked)
    (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 1 data.backwardChecked)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The bridge's recast source parent allowance satisfies its retained aggregate bound. -/
theorem bridgeState_sourceAllowance_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    (Basic.PathModel.mk
      (((bridgeState curve source data).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      bridgeSourceAggregateBound source data := by
  let forward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let backward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.backwardChecked
  rw [bridgeState_parents]
  unfold Basic.PathModel.aggregateAllowance
    bridgeSourceAggregateBound bridgeSourceParentCount
    bridgeSourceTotalWeightedBound
  simp only [Map.map_append, Append.length_append, Map.length_map]
  rw [PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.forwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.backwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.forwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.backwardChecked,
    totalWeightedAllowance_append]
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 0 data.forwardChecked)
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 1 data.backwardChecked)
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

/-- A prepared bridge has exactly two stationary sheet switches. -/
@[simp] theorem bridgeState_switchCount {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).chain.switchCount = 2 := by
  unfold bridgeState
  simp only [SwitchedPathChain.switchCount_append,
    SwitchedPathChain.switchCount_ofCenteredPathChain]
  rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Build a switched state from the four retained finite-cut path banks.

The forward and right boundary banks are read on sheet zero; the reverse and left boundary banks are read on sheet one.
Exact stationary switches join the sheets at the original right and left box anchors. -/
@[expose] def boundaryState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    DirectSwitchedState curve source := by
  let forward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let rightBoundary :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.rightBoundaryChecked
  let backward :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.backwardChecked
  let leftBoundary :=
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.leftBoundaryChecked
  let forwardChain := SwitchedPathChain.ofCenteredPathChain forward.chain
  let rightChain :=
    SwitchedPathChain.ofCenteredPathChain rightBoundary.chain
  let rightSwitch : SwitchedPathChain
      ([] : List (CenteredEdge curve source))
      (start := { coordinate := data.rightState.box.anchor, sheet := 0 })
      (finish := { coordinate := data.rightState.box.anchor, sheet := 1 }) :=
    SwitchedPathChain.singletonStationary data.rightState.box.anchor 0
  let backwardChain := SwitchedPathChain.ofCenteredPathChain backward.chain
  let leftChain := SwitchedPathChain.ofCenteredPathChain leftBoundary.chain
  let leftSwitch : SwitchedPathChain
      ([] : List (CenteredEdge curve source))
      (start := { coordinate := data.leftState.box.anchor, sheet := 1 })
      (finish := { coordinate := data.leftState.box.anchor, sheet := 0 }) :=
    SwitchedPathChain.singletonStationary data.leftState.box.anchor 1
  let combined := forwardChain.append
    (rightChain.append (rightSwitch.append
      (backwardChain.append (leftChain.append leftSwitch))))
  let parents := forward.parents ++ (rightBoundary.parents ++
    ([] ++ (backward.parents ++ (leftBoundary.parents ++ []))))
  exact
    { start := { coordinate := data.leftState.box.anchor, sheet := 0 }
      finish := { coordinate := data.leftState.box.anchor, sheet := 0 }
      parents := parents
      proper := by
        dsimp only [parents]
        rewrite [List.nil_append, Append.append_nil]
        exact allParentsProper_append forward.proper
          (allParentsProper_append rightBoundary.proper
            (allParentsProper_append backward.proper leftBoundary.proper))
      chain := combined
      initialAllowanceBound := fun differential =>
        (Basic.PathModel.mk
          ((parents.map
            (PreparedEdgeRecasting.recastCenteredEdge
              differential)).map
                PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

section
open Purelib.Curves.Hyperelliptic.Branches
/-- The total parent count from the four retained paths and their individual dyadic depths. -/
@[expose] def boundarySourceParentCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Nat :=
  2 ^ data.forwardDepth * data.connector.segmentCount +
    (2 ^ data.rightBoundaryDepth * data.rightBoundaryPath.segmentCount +
      (2 ^ data.backwardDepth *
          (BranchCutLifts.ClearPath.reverse
            data.connector).segmentCount +
        2 ^ data.leftBoundaryDepth * data.leftBoundaryPath.segmentCount))

/-- The sum of the four finite-cut banks' source weighted-allowance bounds. -/
@[expose] def boundarySourceTotalWeightedBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.forwardDepth data.connector +
    (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
          source data.rootDiameter data.backwardDepth
            (BranchCutLifts.ClearPath.reverse data.connector) +
        PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
          source data.rootDiameter data.leftBoundaryDepth data.leftBoundaryPath))

/-- The sum of the four finite-cut banks' dyadic preflight weighted bounds. -/
@[expose] def boundarySourceTotalWeightedPreflightBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.forwardDepth data.connector +
    (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source data.rootDiameter data.backwardDepth
            (BranchCutLifts.ClearPath.reverse data.connector) +
        PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source data.rootDiameter data.leftBoundaryDepth
            data.leftBoundaryPath))

/-- The sum of the four finite-cut banks' integral squared-norm ceiling bounds. -/
@[expose] def boundarySourceIntegralNormSqSumBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.forwardDepth data.connector +
    (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source data.rootDiameter data.backwardDepth
            (BranchCutLifts.ClearPath.reverse data.connector) +
        PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source data.rootDiameter data.leftBoundaryDepth data.leftBoundaryPath))

end

/-- The finite-cut parent count times its total source weighted bound. -/
@[expose] def boundarySourceAggregateBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  (boundarySourceParentCount data : Coordinate) *
    boundarySourceTotalWeightedBound source data

/-- The finite-cut parent count times its dyadic preflight weighted bound. -/
@[expose] def boundarySourcePreflightAggregateBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  (boundarySourceParentCount data : Coordinate) *
    boundarySourceTotalWeightedPreflightBound source data

open Purelib.Curves.Hyperelliptic.Branches in
/-- The finite-cut aggregate bound is no larger than its dyadic preflight bound. -/
theorem boundarySourceAggregateBound_le_preflight {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    boundarySourceAggregateBound source data <=
      boundarySourcePreflightAggregateBound source data := by
  unfold boundarySourceAggregateBound boundarySourcePreflightAggregateBound
    boundarySourceTotalWeightedBound
    boundarySourceTotalWeightedPreflightBound
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.forwardDepth data.connector)
      (add_le_add
        (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
          source data.rootDiameterPositive.le data.rightBoundaryDepth
            data.rightBoundaryPath)
        (add_le_add
          (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
            source data.rootDiameterPositive.le data.backwardDepth
              (BranchCutLifts.ClearPath.reverse data.connector))
          (PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
            source data.rootDiameterPositive.le data.leftBoundaryDepth
              data.leftBoundaryPath)))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

/-- The finite-cut parents retain forward, right-boundary, reverse and left-boundary bank order.

The empty parent lists of the two sheet switches disappear from the
concatenation, while all four original bank lists retain their exact order. -/
theorem boundaryState_parents {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).parents =
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 0 data.forwardChecked).parents ++
        ((PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
            curve source 0 data.rightBoundaryChecked).parents ++
          ((PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 data.backwardChecked).parents ++
            (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 data.leftBoundaryChecked).parents)) := by
  dsimp only [boundaryState]
  rewrite [Append.append_nil]
  exact Eq.refl _

open Purelib.Data.Gaussian in
/-- The finite-cut parent samples satisfy the retained squared-norm sum bound. -/
theorem boundaryState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Norm.Sum.Basic.gaussianNormSqSum
        ((boundaryState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      boundarySourceIntegralNormSqSumBound source data := by
  rw [boundaryState_parents]
  unfold boundarySourceIntegralNormSqSumBound
  simp only [Map.map_append]
  rw [gaussianNormSqSum_append, gaussianNormSqSum_append,
    gaussianNormSqSum_append]
  exact add_le_add
    (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 0 data.forwardChecked)
    (add_le_add
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
        curve source 0 data.rightBoundaryChecked)
      (add_le_add
        (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
          curve source 1 data.backwardChecked)
        (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
          curve source 1 data.leftBoundaryChecked)))

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The finite-cut recast source parent allowance satisfies its retained aggregate bound. -/
theorem boundaryState_sourceAllowance_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (Basic.PathModel.mk
      (((boundaryState curve source data).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      boundarySourceAggregateBound source data := by
  rw [boundaryState_parents]
  unfold Basic.PathModel.aggregateAllowance
    boundarySourceAggregateBound boundarySourceParentCount
    boundarySourceTotalWeightedBound
  simp only [Map.map_append, Append.length_append, Map.length_map]
  rw [PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.forwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.rightBoundaryChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.backwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.leftBoundaryChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.forwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.rightBoundaryChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.backwardChecked,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.leftBoundaryChecked,
    totalWeightedAllowance_append, totalWeightedAllowance_append,
    totalWeightedAllowance_append]
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 0 data.forwardChecked)
      (add_le_add
        (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
          curve source 0 data.rightBoundaryChecked)
        (add_le_add
          (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
            curve source 1 data.backwardChecked)
          (PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
            curve source 1 data.leftBoundaryChecked)))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

/-- A prepared finite-cut cycle has exactly two stationary sheet switches. -/
@[simp] theorem boundaryState_switchCount {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).chain.switchCount = 2 := by
  unfold boundaryState
  simp only [SwitchedPathChain.switchCount_append,
    SwitchedPathChain.switchCount_ofCenteredPathChain]
  rfl

/-- Count the retained prepared path steps of a bridge or finite-cut cycle. -/
@[expose] def preparedCycleParentCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} :
    PreparedCycleModels.PreparedCycleData curve -> Nat
  | .bridge data => data.forward.stepCount + data.backward.stepCount
  | .finiteCut data =>
      data.forward.stepCount + data.rightBoundary.stepCount +
        data.backward.stepCount + data.leftBoundary.stepCount

section
open Purelib.Riemann.Paths
/-- The bridge parent count equals the two retained prepared path step counts. -/
@[simp] theorem bridgeState_parents_length {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).parents.length =
      data.forward.stepCount + data.backward.stepCount := by
  unfold bridgeState
  simp only [Append.length_append, List.length_nil, Nat.add_zero, Nat.zero_add,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length,
    PreparedCycleModels.PreparedDoublePath.forward,
    PreparedCycleModels.PreparedDoublePath.backward]
  rw [PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked]

/-- The finite-cut parent count equals the four retained prepared path step counts. -/
@[simp] theorem boundaryState_parents_length {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).parents.length =
      data.forward.stepCount + data.rightBoundary.stepCount +
        data.backward.stepCount + data.leftBoundary.stepCount := by
  unfold boundaryState
  simp only [Append.length_append, List.length_nil, Nat.add_zero, Nat.zero_add,
    PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length,
    PreparedCycleModels.PreparedBoundaryDoublePath.forward,
    PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary,
    PreparedCycleModels.PreparedBoundaryDoublePath.backward,
    PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary]
  rw [PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.rightBoundaryChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.leftBoundaryChecked]
  omega0

end

/-- Build the switched state for the supplied bridge or finite-cut cycle data. -/
@[expose] def cycleState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus) :
    PreparedCycleModels.PreparedCycleData curve ->
      DirectSwitchedState curve source
  | .bridge data => bridgeState curve source data
  | .finiteCut data => boundaryState curve source data

/-- The exact dyadic parent count of the supplied bridge or finite-cut cycle. -/
@[expose] def cycleSourceParentCount {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} :
    PreparedCycleModels.PreparedCycleData curve -> Nat
  | .bridge data => bridgeSourceParentCount data
  | .finiteCut data => boundarySourceParentCount data

/-- The retained parent-sample squared-norm sum bound for either cycle construction. -/
@[expose] def cycleSourceIntegralNormSqSumBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus) :
    PreparedCycleModels.PreparedCycleData curve -> Coordinate
  | .bridge data => bridgeSourceIntegralNormSqSumBound source data
  | .finiteCut data => boundarySourceIntegralNormSqSumBound source data

/-- The switched state's parent length equals the retained dyadic cycle count. -/
@[simp] theorem cycleState_parents_length {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).parents.length =
      cycleSourceParentCount data := by
  cases data with
  | bridge bridge =>
      unfold cycleState cycleSourceParentCount bridgeSourceParentCount
      rw [bridgeState_parents, Append.length_append,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 bridge.forwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 bridge.backwardChecked]
  | finiteCut boundary =>
      unfold cycleState cycleSourceParentCount boundarySourceParentCount
      rw [boundaryState_parents, Append.length_append, Append.length_append,
        Append.length_append,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 boundary.forwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 boundary.rightBoundaryChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 boundary.backwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 boundary.leftBoundaryChecked]

open Purelib.Data.Gaussian in
/-- The cycle parent samples satisfy their retained squared-norm sum bound. -/
theorem cycleState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Norm.Sum.Basic.gaussianNormSqSum
        ((cycleState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      cycleSourceIntegralNormSqSumBound source data := by
  cases data with
  | bridge bridge =>
      exact bridgeState_sourceIntegralNormSqSum_le curve source bridge
  | finiteCut boundary =>
      exact boundaryState_sourceIntegralNormSqSum_le curve source boundary

/-- The retained cycle squared-norm sum bound is nonnegative. -/
theorem cycleSourceIntegralNormSqSumBound_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceIntegralNormSqSumBound source data :=
  (gaussianNormSqSum_nonnegative
    ((cycleState curve source data).parents.map
      fun parent => parent.model.integralSample)).trans
        (cycleState_sourceIntegralNormSqSum_le curve source data)

/-- Recasting cycle parents to their own source differential preserves the exact parent list.

Each retained bank is recast to its original source. Pointwise bank readback and
structural concatenation preserve the original ordered parent occurrences. -/
theorem cycleState_recastParents_self {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source) =
      (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [cycleState, bridgeState_parents, Map.map_append]
      rw [PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 bridge.forwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 bridge.backwardChecked]
  | finiteCut boundary =>
      simp only [cycleState, boundaryState_parents, Map.map_append]
      rw [PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 boundary.forwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 boundary.rightBoundaryChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 boundary.backwardChecked,
        PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 boundary.leftBoundaryChecked]

/-- The prepared cycle's real lower reading equals the corresponding centered-parent lower sum. -/
theorem cycleState_integralRealLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    data.integralRealLower source =
      PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower
        (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [PreparedCycleModels.PreparedCycleData.integralRealLower,
        cycleState]
      unfold PreparedCycleModels.PreparedDoublePath.integralRealLower
        PreparedCycleModels.PreparedDoublePath.forward
        PreparedCycleModels.PreparedDoublePath.backward
      rw [bridgeState_parents,
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_append,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 bridge.forwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 bridge.backwardChecked]
      rfl
  | finiteCut boundary =>
      simp only [PreparedCycleModels.PreparedCycleData.integralRealLower,
        cycleState]
      unfold PreparedCycleModels.PreparedBoundaryDoublePath.integralRealLower
        PreparedCycleModels.PreparedBoundaryDoublePath.forward
        PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary
        PreparedCycleModels.PreparedBoundaryDoublePath.backward
        PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary
      rw [boundaryState_parents,
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_append,
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_append,
        PreparedSubdivisionModelCore.centeredEdgesIntegralRealLower_append,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 boundary.forwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 boundary.rightBoundaryChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 boundary.backwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 boundary.leftBoundaryChecked]
      rfl

/-- The prepared cycle's directional lower reading equals the corresponding centered-parent lower sum. -/
theorem cycleState_directionalIntegralLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (direction : Gaussian)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    data.directionalIntegralLower source direction =
      PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower
        direction (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [
        PreparedCycleModels.PreparedCycleData.directionalIntegralLower,
        cycleState]
      unfold
        PreparedCycleModels.PreparedDoublePath.directionalIntegralLower
        PreparedCycleModels.PreparedDoublePath.forward
        PreparedCycleModels.PreparedDoublePath.backward
      rw [bridgeState_parents,
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_append,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction bridge.forwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction bridge.backwardChecked]
  | finiteCut boundary =>
      simp only [
        PreparedCycleModels.PreparedCycleData.directionalIntegralLower,
        cycleState]
      unfold
        PreparedCycleModels.PreparedBoundaryDoublePath.directionalIntegralLower
        PreparedCycleModels.PreparedBoundaryDoublePath.forward
        PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary
        PreparedCycleModels.PreparedBoundaryDoublePath.backward
        PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary
      rw [boundaryState_parents,
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_append,
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_append,
        PreparedSubdivisionModelCore.centeredEdgesDirectionalIntegralLower_append,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction boundary.forwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction boundary.rightBoundaryChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction boundary.backwardChecked,
        ← PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction boundary.leftBoundaryChecked]
/-- The retained parent count times the parent-sample squared-norm sum bound. -/
@[expose] def cycleSourceInitialSampleNormSqBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourceParentCount data : Coordinate) *
    cycleSourceIntegralNormSqSumBound source data

/-- The initial cycle sample bound is nonnegative. -/
theorem cycleSourceInitialSampleNormSqBound_nonnegative {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceInitialSampleNormSqBound source data := by
  unfold cycleSourceInitialSampleNormSqBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (SwitchedPathChain.coordinateNatCast_nonnegative _)
    (cycleSourceIntegralNormSqSumBound_nonnegative source data)

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The initial source sample satisfies the retained finite-sum squared-norm bound. -/
theorem cycleState_sourceInitialSample_normSq_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Data.Gaussian.Norm.Basic.normSq
        ((Basic.PathModel.mk
          ((cycleState curve source data).parents.map
            PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) <=
      cycleSourceInitialSampleNormSqBound source data := by
  let samples := (cycleState curve source data).parents.map
    fun parent => parent.model.integralSample
  rw [pathModel_integralSample_eq_gaussianSum]
  rw [centeredEdgeIntegralSamples_map_model]
  have finiteCauchy :=
    Norm.Sum.Basic.normSq_gaussianSum_le samples
  have additiveBound := cycleState_sourceIntegralNormSqSum_le curve source data
  unfold cycleSourceInitialSampleNormSqBound
  change
    Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum samples) <= _
  calc
    Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum samples) <=
      (samples.length : Coordinate) *
        Norm.Sum.Basic.gaussianNormSqSum samples :=
          (Norm.Basic.normSq_eq_canonical _).trans_le finiteCauchy
    _ = (cycleSourceParentCount data : Coordinate) *
        Norm.Sum.Basic.gaussianNormSqSum samples := by
      unfold samples
      rw [Map.length_map, cycleState_parents_length]
    _ <= (cycleSourceParentCount data : Coordinate) *
        cycleSourceIntegralNormSqSumBound source data :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct additiveBound
        (SwitchedPathChain.coordinateNatCast_nonnegative _)

/-- The retained source aggregate-allowance bound for either prepared cycle construction. -/
@[expose] def cycleSourceAggregateBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus) :
    PreparedCycleModels.PreparedCycleData curve -> Coordinate
  | .bridge data => bridgeSourceAggregateBound source data
  | .finiteCut data => boundarySourceAggregateBound source data

set_option genInjectivity false in
/-- The two scalar preflight bounds for a prepared source cycle.

The aggregate allowance and initial squared-norm bounds are kept separate so schedule scales can be computed without
reading the full refinement sequence. -/
structure CycleSourcePreflightBounds where
  /-- The retained scalar bound on the source parents' aggregate allowance. -/ aggregateBound : Coordinate
  /-- The retained scalar bound on the initial source sample's squared norm. -/ initialSampleNormSqBound : Coordinate

constructive_injectivity CycleSourcePreflightBounds

namespace CycleSourcePreflightBounds

/-- The retained aggregate preflight bound plus fixed positive schedule slack. -/
@[expose] def scheduleBase (bounds : CycleSourcePreflightBounds) : Coordinate :=
  bounds.aggregateBound + DirectSwitchedState.scheduleSlack

/-- The preflight error scale, retaining the switch, sequential and comparison factors three, four and three. -/
@[expose] def errorScale (bounds : CycleSourcePreflightBounds) : Coordinate :=
  3 * (4 * (3 * bounds.scheduleBase))

/-- Twice the sum of the initial squared-norm bound and preflight error scale. -/
@[expose] def centerBound (bounds : CycleSourcePreflightBounds) : Coordinate :=
  2 * (bounds.initialSampleNormSqBound + bounds.errorScale)

end CycleSourcePreflightBounds

set_option genInjectivity false in
/-- A retained scalar summary of the cycle's preflight bounds and derived schedule constants.

The record stores aggregate and initial-sample bounds together with the derived schedule base, error scale and uniform
center bound. -/
structure CycleSourcePreflightSummary where
  /-- The retained scalar bound on the source parents' aggregate allowance. -/ aggregateBound : Coordinate
  /-- The retained scalar bound on the initial source sample's squared norm. -/ initialSampleNormSqBound : Coordinate
  /-- The retained preflight aggregate bound plus fixed positive schedule slack. -/ scheduleBase : Coordinate
  /-- The derived preflight comparison scale, retaining all three numerical factors. -/ errorScale : Coordinate
  /-- The derived uniform squared-norm bound for the retained source samples. -/ centerBound : Coordinate

constructive_injectivity CycleSourcePreflightSummary

namespace CycleSourcePreflightBounds

/-- Compute the preflight schedule constants once from the two retained scalar bounds. -/
@[expose] def summary (bounds : CycleSourcePreflightBounds) :
    CycleSourcePreflightSummary :=
  let scheduleBase := bounds.scheduleBase
  let errorScale := 3 * (4 * (3 * scheduleBase))
  { aggregateBound := bounds.aggregateBound
    initialSampleNormSqBound := bounds.initialSampleNormSqBound
    scheduleBase := scheduleBase
    errorScale := errorScale
    centerBound :=
      2 * (bounds.initialSampleNormSqBound + errorScale) }

/-- The preflight summary preserves the aggregate bound. -/
@[simp] theorem summary_aggregateBound (bounds : CycleSourcePreflightBounds) :
    bounds.summary.aggregateBound = bounds.aggregateBound := rfl

/-- The preflight summary preserves the initial squared-norm bound. -/
@[simp] theorem summary_initialSampleNormSqBound
    (bounds : CycleSourcePreflightBounds) :
    bounds.summary.initialSampleNormSqBound =
      bounds.initialSampleNormSqBound := rfl

/-- The preflight summary stores the specified schedule base. -/
@[simp] theorem summary_scheduleBase (bounds : CycleSourcePreflightBounds) :
    bounds.summary.scheduleBase = bounds.scheduleBase := rfl

/-- The preflight summary stores the specified error scale. -/
@[simp] theorem summary_errorScale (bounds : CycleSourcePreflightBounds) :
    bounds.summary.errorScale = bounds.errorScale := rfl

/-- The preflight summary stores the specified uniform center bound. -/
@[simp] theorem summary_centerBound (bounds : CycleSourcePreflightBounds) :
    bounds.summary.centerBound = bounds.centerBound := rfl

end CycleSourcePreflightBounds

/-- Compute the aggregate and initial-sample preflight bounds from the retained cycle banks. -/
@[expose] def cycleSourcePreflightBounds {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus) :
    PreparedCycleModels.PreparedCycleData curve ->
      CycleSourcePreflightBounds
  | .bridge data =>
      { aggregateBound := bridgeSourcePreflightAggregateBound source data
        initialSampleNormSqBound :=
          (bridgeSourceParentCount data : Coordinate) *
            bridgeSourceIntegralNormSqSumBound source data }
  | .finiteCut data =>
      { aggregateBound := boundarySourcePreflightAggregateBound source data
        initialSampleNormSqBound :=
          (boundarySourceParentCount data : Coordinate) *
            boundarySourceIntegralNormSqSumBound source data }

/-- The exact source aggregate bound is bounded by the retained preflight bound. -/
theorem cycleSourceAggregateBound_le_preflight {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceAggregateBound source data <=
      (cycleSourcePreflightBounds source data).aggregateBound := by
  cases data with
  | bridge bridge =>
      exact bridgeSourceAggregateBound_le_preflight source bridge
  | finiteCut boundary =>
      exact boundarySourceAggregateBound_le_preflight source boundary

/-- The exact initial sample bound is bounded by the retained preflight bound. -/
theorem cycleSourceInitialSampleNormSqBound_le_preflight
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceInitialSampleNormSqBound source data <=
      (cycleSourcePreflightBounds source data).initialSampleNormSqBound := by
  cases data <;> exact le_rfl

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- The cycle state's recast source parents meet the retained aggregate bound. -/
theorem cycleState_sourceAllowance_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (Basic.PathModel.mk
      (((cycleState curve source data).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source)).map
            PreparedSubdivisionModelCore.CenteredEdge.model)).aggregateAllowance <=
      cycleSourceAggregateBound source data := by
  cases data with
  | bridge bridge =>
      exact bridgeState_sourceAllowance_le curve source bridge
  | finiteCut boundary =>
      exact boundaryState_sourceAllowance_le curve source boundary

/-- The retained source aggregate bound is nonnegative. -/
theorem cycleSourceAggregateBound_nonnegative {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceAggregateBound source data :=
  (Basic.PathModel.aggregateAllowance_nonneg
    (Basic.PathModel.mk
      (((cycleState curve source data).parents.map
        (PreparedEdgeRecasting.recastCenteredEdge
          source)).map
            PreparedSubdivisionModelCore.CenteredEdge.model))).trans
      (cycleState_sourceAllowance_le curve source data)

end

/-- Attach the retained compact source bound to the unchanged prepared cycle state.

Only the source differential's allowance bound changes; the exact parents, switches, owners and other differential
bounds remain those of the original state. -/
@[expose] def compactCycleState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    DirectSwitchedState curve source := by
  let state := cycleState curve source data
  exact state.withSourceAllowanceBound
    (cycleSourceAggregateBound source data)
    (cycleState_sourceAllowance_le curve source data)

/-- The compact state retains the original cycle state's exact parent list. -/
@[simp] theorem compactCycleState_parents {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).parents =
      (cycleState curve source data).parents := rfl

section
open Purelib.Data.Gaussian
/-- The compact state's initial flat source sample meets the retained squared-norm bound. -/
theorem compactCycleState_sourceFlatInitialSample_normSq_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Data.Gaussian.Norm.Basic.normSq
        ((compactCycleState curve source data).flatModel [source] source
          0).integralSample <=
      cycleSourceInitialSampleNormSqBound source data := by
  unfold DirectSwitchedState.flatModel DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data]
  exact cycleState_sourceInitialSample_normSq_le curve source data

/-- The compact state's initial switched source sample meets the same retained squared-norm bound. -/
theorem compactCycleState_sourceInitialSample_normSq_le {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (member : source ∈ [source]) :
    Data.Gaussian.Norm.Basic.normSq
        ((((compactCycleState curve source data).integral [source] source
          member).model 0).integralSample) <=
      cycleSourceInitialSampleNormSqBound source data := by
  change Data.Gaussian.Norm.Basic.normSq
      (((compactCycleState curve source data).refinementStates [source] 0).model
        source).integralSample <= _
  rw [(compactCycleState curve source data).model_integralSample_eq_flatModel
    [source] source 0]
  exact compactCycleState_sourceFlatInitialSample_normSq_le curve source data

end

/-- Either prepared cycle construction has exactly two stationary switches. -/
@[simp] theorem cycleState_switchCount {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).chain.switchCount = 2 := by
  cases data with
  | bridge data => exact bridgeState_switchCount curve source data
  | finiteCut data => exact boundaryState_switchCount curve source data

/-- The compact prepared cycle state retains exactly two stationary switches. -/
@[simp] theorem compactCycleState_switchCount {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).chain.switchCount = 2 := by
  unfold compactCycleState DirectSwitchedState.withSourceAllowanceBound
  exact cycleState_switchCount curve source data

/-- The exact source aggregate bound plus the fixed schedule slack. -/
@[expose] def cycleSourceExactScheduleBase {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  cycleSourceAggregateBound source data + DirectSwitchedState.scheduleSlack

/-- The exact schedule base scaled by the retained factors three, four and three. -/
@[expose] def cycleSourceExactErrorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  3 * (4 * (3 * cycleSourceExactScheduleBase source data))

/-- The schedule base derived from the cycle's retained preflight bounds. -/
@[expose] def cycleSourceScheduleBase {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).scheduleBase

/-- The error scale derived from the cycle's retained preflight bounds. -/
@[expose] def cycleSourceErrorScale {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).errorScale

/-- The uniform center bound derived from the cycle's retained preflight bounds. -/
@[expose] def cycleSourceCenterBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).centerBound

/-- The retained preflight schedule base is strictly positive.

The retained preflight aggregate bounds dominate a nonnegative original
allowance, and the fixed positive slack remains in the same schedule base. -/
theorem cycleSourceScheduleBase_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
  (data : PreparedCycleModels.PreparedCycleData curve) :
    0 < cycleSourceScheduleBase source data := by
  unfold cycleSourceScheduleBase CycleSourcePreflightBounds.scheduleBase
  exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    ((cycleSourceAggregateBound_nonnegative curve source data).trans
      (cycleSourceAggregateBound_le_preflight source data))
    DirectSwitchedState.scheduleSlack_positive

/-- The exact schedule base is bounded by its retained preflight base. -/
theorem cycleSourceExactScheduleBase_le_preflight {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceExactScheduleBase source data <=
      cycleSourceScheduleBase source data := by
  unfold cycleSourceExactScheduleBase cycleSourceScheduleBase
    CycleSourcePreflightBounds.scheduleBase
  exact Fraction.Order.Arithmetic.add_le_add_right_direct
    (cycleSourceAggregateBound_le_preflight source data)
    DirectSwitchedState.scheduleSlack

/-- The exact error scale is bounded by its retained preflight scale. -/
theorem cycleSourceExactErrorScale_le_preflight {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceExactErrorScale source data <=
      cycleSourceErrorScale source data := by
  unfold cycleSourceExactErrorScale cycleSourceErrorScale
    CycleSourcePreflightBounds.errorScale
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (cycleSourceExactScheduleBase_le_preflight source data) (by decide))
      (by decide))
    (by decide)

/-- The retained preflight error scale is nonnegative. -/
theorem cycleSourceErrorScale_nonnegative {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
  (data : PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceErrorScale source data := by
  unfold cycleSourceErrorScale CycleSourcePreflightBounds.errorScale
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (cycleSourceScheduleBase_positive curve source data).le))

/-- The retained preflight uniform center bound is nonnegative. -/
theorem cycleSourceCenterBound_nonnegative {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
  (data : PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceCenterBound source data := by
  unfold cycleSourceCenterBound CycleSourcePreflightBounds.centerBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      ((cycleSourceInitialSampleNormSqBound_nonnegative source data).trans
        (cycleSourceInitialSampleNormSqBound_le_preflight source data))
      (cycleSourceErrorScale_nonnegative curve source data))

/-- The compact state stores the exact retained cycle source aggregate bound.

The source differential has the same retained index on both sides of the
conditional, so this field reads the supplied original source bound. -/
@[simp] theorem compactCycleState_initialAllowanceBound_source {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).initialAllowanceBound source =
      cycleSourceAggregateBound source data := by
  unfold compactCycleState DirectSwitchedState.withSourceAllowanceBound
  exact if_pos (Eq.refl source.index)

/-- The compact state's singleton-source base equals the exact retained cycle schedule base. -/
theorem compactCycleState_scheduleBase_singleton {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).scheduleBase [source] =
      cycleSourceExactScheduleBase source data := by
  unfold DirectSwitchedState.scheduleBase
    DirectSwitchedState.initialAllowanceBoundSum cycleSourceExactScheduleBase
  simp only [DirectSwitchedState.initialAllowanceBoundSum]
  rw [compactCycleState_initialAllowanceBound_source]
  ring1

open Purelib.Integration.Program in
/-- The compact singleton-source integral has the exact retained cycle error scale. -/
theorem compactCycleState_sourceIntegral_errorScale {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (member : source ∈ [source]) :
    (((compactCycleState curve source data).integral [source] source
      member).errorScale) = cycleSourceExactErrorScale source data := by
  unfold DirectSwitchedState.integral
  simp only [Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram.toRefinementProgram,
    Gaussian.Sequential.SequentialCompatibleConstantRefinementProgram.errorScale,
    DirectSwitchedState.flatSequentialProgram,
    SwitchedPathChain.switchFactor, compactCycleState_switchCount,
    Nat.cast_ofNat]
  rw [compactCycleState_scheduleBase_singleton]
  rfl

/-- A lazy retained compact state for the exact curve, source differential and prepared cycle. -/
@[expose] def compactSourceState {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Thunk (DirectSwitchedState curve source) :=
  ⟨fun _ => compactCycleState curve source data⟩

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the singleton-source switched model from the retained compact state at the given stage. -/
@[expose] def compactSourceModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (state : Thunk (DirectSwitchedState curve source))
    (index : Nat) : Basic.PathModel :=
  ((state.get.refinementStates [source] index).model source)

/-- A positive literal real lower certificate for the compact source parents at a fixed stage. -/
abbrev CompactSourcePositiveLiteralRealLowerCertificate {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) :=
  DirectSwitchedState.FlatPositiveLiteralRealLowerCertificate
    (compactCycleState curve source data) [source] source index

/-- The retained literal lower value bounds the corresponding switched model's real integral sample. -/
theorem CompactSourcePositiveLiteralRealLowerCertificate.lower_le_model
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {index : Nat}
    (certificate : CompactSourcePositiveLiteralRealLowerCertificate
      curve source data index) :
    certificate.lower <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re :=
  DirectSwitchedState.FlatPositiveLiteralRealLowerCertificate.lower_le_model
    certificate

/-- The compact source's endpoint-based real lower reading at a refinement stage. -/
@[expose] def compactSourceIntegralRealLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelIntegralRealLower
    [source] source index

/-- The compact source's retained-ball real lower reading at a refinement stage. -/
@[expose] def compactSourceBallIntegralRealLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelBallIntegralRealLower
    [source] source index

/-- The initial compact real lower reading equals the original prepared cycle reading. -/
theorem compactSourceIntegralRealLower_zero {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    compactSourceIntegralRealLower curve source data 0 =
      data.integralRealLower source := by
  unfold compactSourceIntegralRealLower
    DirectSwitchedState.flatModelIntegralRealLower
    DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data,
    ← cycleState_integralRealLower curve source data]

/-- For source exponent zero, the compact real lower reading bounds its model's real sample. -/
theorem compactSourceIntegralRealLower_le_model {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) (exponentZero : source.exponent = 0) :
    compactSourceIntegralRealLower curve source data index <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re := by
  exact (compactCycleState curve source data).flatModelIntegralRealLower_le_model
    [source] source index exponentZero

/-- For source exponent zero, the compact ball lower reading bounds its model's real sample. -/
theorem compactSourceBallIntegralRealLower_le_model {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) (exponentZero : source.exponent = 0) :
    compactSourceBallIntegralRealLower curve source data index <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re := by
  exact
    (compactCycleState curve source data).flatModelBallIntegralRealLower_le_model
      [source] source index exponentZero

/-- For exponent zero, the original cycle real lower reading bounds the initial compact sample. -/
theorem preparedCycleIntegralRealLower_le_compactSourceModel_zero {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (exponentZero : source.exponent = 0) :
    data.integralRealLower source <=
      (compactSourceModel (compactSourceState curve source data)
        0).integralSample.re := by
  rw [← compactSourceIntegralRealLower_zero curve source data]
  exact compactSourceIntegralRealLower_le_model curve source data 0
    exponentZero

/-- The compact source's endpoint-based lower reading in the supplied direction. -/
@[expose] def compactSourceDirectionalIntegralLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelDirectionalIntegralLower
    [source] source direction index

/-- The compact source's retained-ball lower reading in the supplied direction. -/
@[expose] def compactSourceBallDirectionalIntegralLower {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelBallDirectionalIntegralLower
    [source] source direction index

/-- The initial compact directional lower reading equals the original cycle reading. -/
theorem compactSourceDirectionalIntegralLower_zero {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) :
    compactSourceDirectionalIntegralLower curve source data direction 0 =
      data.directionalIntegralLower source direction := by
  unfold compactSourceDirectionalIntegralLower
    DirectSwitchedState.flatModelDirectionalIntegralLower
    DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data,
    ← cycleState_directionalIntegralLower curve source direction data]

/-- For exponent zero, the compact directional reading bounds its sample's scalar projection. -/
theorem compactSourceDirectionalIntegralLower_le_model {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat)
    (exponentZero : source.exponent = 0) :
    compactSourceDirectionalIntegralLower curve source data direction index <=
      direction.re *
          (compactSourceModel (compactSourceState curve source data)
            index).integralSample.re +
        direction.im *
          (compactSourceModel (compactSourceState curve source data)
            index).integralSample.im := by
  exact
    (compactCycleState curve source data).flatModelDirectionalIntegralLower_le_model
      [source] source direction index exponentZero

/-- For exponent zero, the compact ball directional reading bounds its sample's scalar projection. -/
theorem compactSourceBallDirectionalIntegralLower_le_model {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat)
    (exponentZero : source.exponent = 0) :
    compactSourceBallDirectionalIntegralLower curve source data direction index <=
      direction.re *
          (compactSourceModel (compactSourceState curve source data)
            index).integralSample.re +
        direction.im *
          (compactSourceModel (compactSourceState curve source data)
            index).integralSample.im := by
  exact
    (compactCycleState curve source data).flatModelBallDirectionalIntegralLower_le_model
      [source] source direction index exponentZero

/-- For exponent zero, the original cycle directional reading bounds the initial compact sample projection. -/
theorem preparedCycleDirectionalIntegralLower_le_compactSourceModel_zero
    {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian)
    (exponentZero : source.exponent = 0) :
    data.directionalIntegralLower source direction <=
      direction.re *
          (compactSourceModel (compactSourceState curve source data)
            0).integralSample.re +
        direction.im *
          (compactSourceModel (compactSourceState curve source data)
            0).integralSample.im := by
  rw [← compactSourceDirectionalIntegralLower_zero curve source data
    direction]
  exact compactSourceDirectionalIntegralLower_le_model curve source data
    direction 0 exponentZero

set_option genInjectivity false in
/-- A finite cache of compact source stages tied to the exact prepared cycle.

The retained initial thunk is certified against the compact cycle state, and each cached refinement retains that same
initial owner and singleton source list. -/
structure CompactSourceCache {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) where
  /-- The retained lazy compact state for the exact prepared cycle and source differential. -/ initial : Thunk
    (DirectSwitchedState curve source)
  /-- The cached initial thunk reads exactly the specified compact prepared-cycle state. -/ initial_eq : initial.get =
    compactCycleState curve source data
  /-- The bounded refinement cache retaining this exact initial thunk and singleton source list. -/ refinements :
    DirectSwitchedState.BoundedRefinementCache initial [source] count

constructive_injectivity CompactSourceCache

namespace CompactSourceCache

/-- Build the requested finite cache from one retained compact prepared-cycle state thunk.

All refinement stages retain that exact initial thunk and singleton source differential list, with certified stage
equalities. -/
@[expose] def canonical {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) : CompactSourceCache curve source data count :=
  let initial := compactSourceState curve source data
  { initial := initial
    initial_eq := rfl
    refinements :=
      DirectSwitchedState.BoundedRefinementCache.canonical initial [source]
        count }

/-- Extend the compact source cache while retaining its initial thunk, identity certificate and earlier stage thunks. -/
@[expose] def extend {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (extra : Nat) : CompactSourceCache curve source data (count + extra) where
  initial := cache.initial
  initial_eq := cache.initial_eq
  refinements := cache.refinements.extend extra

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the recast source model from the retained cache, with the original compact computation beyond its bound. -/
@[expose] def model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : Basic.PathModel :=
  if within : index < count then
    ((cache.refinements.get index within).get.model source)
  else compactSourceModel cache.initial index

/-- Read the cached endpoint-based real lower bound, using the original computation beyond the cache. -/
@[expose] def integralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelIntegralRealLower
      [source] source 0
  else cache.initial.get.flatModelIntegralRealLower [source] source index

/-- Read the cached ball-based real lower bound, using the original computation beyond the cache. -/
@[expose] def ballIntegralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelBallIntegralRealLower
      [source] source 0
  else cache.initial.get.flatModelBallIntegralRealLower [source] source index

/-- Read the cached endpoint-based directional bound, using the original computation beyond the cache. -/
@[expose] def directionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelDirectionalIntegralLower
      [source] source direction 0
  else
    cache.initial.get.flatModelDirectionalIntegralLower
      [source] source direction index

/-- Read the cached ball-based directional bound, using the original computation beyond the cache. -/
@[expose] def ballDirectionalIntegralLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelBallDirectionalIntegralLower
      [source] source direction 0
  else
    cache.initial.get.flatModelBallDirectionalIntegralLower
      [source] source direction index

/-- The cached compact model equals the original compact source model at the same stage. -/
theorem model_eq_compactSourceModel {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) :
    cache.model index =
      compactSourceModel (compactSourceState curve source data) index := by
  unfold model
  split
  · rename_i within
    rw [cache.refinements.get_state_eq index within, cache.initial_eq]
    rfl
  · unfold compactSourceModel
    rw [cache.initial_eq]
    rfl

/-- The cached real lower reading equals the original compact source reading. -/
theorem integralRealLower_eq_compactSourceIntegralRealLower {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) :
    cache.integralRealLower index =
      compactSourceIntegralRealLower curve source data index := by
  unfold integralRealLower compactSourceIntegralRealLower
  split
  · rename_i within
    rw [cache.refinements.get_state_eq index within, cache.initial_eq]
    rfl
  · rw [cache.initial_eq]

/-- The cached ball real lower reading equals the original compact source reading. -/
theorem ballIntegralRealLower_eq_compactSourceBallIntegralRealLower
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) :
    cache.ballIntegralRealLower index =
      compactSourceBallIntegralRealLower curve source data index := by
  unfold ballIntegralRealLower compactSourceBallIntegralRealLower
  split
  · rename_i within
    rw [cache.refinements.get_state_eq index within, cache.initial_eq]
    rfl
  · rw [cache.initial_eq]

/-- The cached directional reading equals the original compact source reading. -/
theorem directionalIntegralLower_eq_compactSourceDirectionalIntegralLower
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) :
    cache.directionalIntegralLower direction index =
      compactSourceDirectionalIntegralLower curve source data direction
        index := by
  unfold directionalIntegralLower compactSourceDirectionalIntegralLower
  split
  · rename_i within
    rw [cache.refinements.get_state_eq index within, cache.initial_eq]
    rfl
  · rw [cache.initial_eq]

/-- The cached ball directional reading equals the original compact source reading. -/
theorem ballDirectionalIntegralLower_eq_compactSourceBallDirectionalIntegralLower
    {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) :
    cache.ballDirectionalIntegralLower direction index =
      compactSourceBallDirectionalIntegralLower curve source data direction
        index := by
  unfold ballDirectionalIntegralLower
    compactSourceBallDirectionalIntegralLower
  split
  · rename_i within
    rw [cache.refinements.get_state_eq index within, cache.initial_eq]
    rfl
  · rw [cache.initial_eq]

/-- For source exponent zero, the cached real lower reading bounds the cached sample's real part. -/
theorem integralRealLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) (exponentZero : source.exponent = 0) :
    cache.integralRealLower index <= (cache.model index).integralSample.re := by
  rw [cache.integralRealLower_eq_compactSourceIntegralRealLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceIntegralRealLower_le_model curve source data index
    exponentZero

/-- For source exponent zero, the cached ball reading bounds the cached sample's real part. -/
theorem ballIntegralRealLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) (exponentZero : source.exponent = 0) :
    cache.ballIntegralRealLower index <= (cache.model index).integralSample.re := by
  rw [cache.ballIntegralRealLower_eq_compactSourceBallIntegralRealLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceBallIntegralRealLower_le_model curve source data index
    exponentZero

/-- For source exponent zero, the cached directional reading bounds the cached sample projection. -/
theorem directionalIntegralLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat)
    (exponentZero : source.exponent = 0) :
    cache.directionalIntegralLower direction index <=
      direction.re * (cache.model index).integralSample.re +
        direction.im * (cache.model index).integralSample.im := by
  rw [cache.directionalIntegralLower_eq_compactSourceDirectionalIntegralLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceDirectionalIntegralLower_le_model curve source data
    direction index exponentZero

/-- For source exponent zero, the cached ball directional reading bounds the cached sample projection. -/
theorem ballDirectionalIntegralLower_le_model {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat)
    (exponentZero : source.exponent = 0) :
    cache.ballDirectionalIntegralLower direction index <=
      direction.re * (cache.model index).integralSample.re +
        direction.im * (cache.model index).integralSample.im := by
  rw [cache.ballDirectionalIntegralLower_eq_compactSourceBallDirectionalIntegralLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceBallDirectionalIntegralLower_le_model curve source data
    direction index exponentZero

/-- Extending the compact cache preserves each model already inside the original cache. -/
theorem extend_model_of_lt {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    {data : PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (extra index : Nat) (within : index < count) :
    (cache.extend extra).model index = cache.model index := by
  have extendedWithin : index < count + extra :=
    within.trans_le (Nat.le_add_right count extra)
  simp only [model, extend, dif_pos extendedWithin, dif_pos within]
  rw [cache.refinements.extend_get index within extra]

end CompactSourceCache

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
/-- The compact source integral program with retained preflight error and center bounds.

The exact compact state supplies every model; authenticated bounds on its initial sample and later movement justify the
preflight constants without replacing the geometric sequence. -/
@[expose] def compactSourceIntegral {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve) :
    Gaussian.Basic.RefinementProgram := by
  let member : source ∈ [source] := List.Mem.head []
  let original :=
    (compactCycleState curve source data).integral [source] source member
  let preflightCore := cycleSourcePreflightBounds source data
  let preflight := preflightCore.summary
  let state := compactSourceState curve source data
  exact
    { model := compactSourceModel state
      errorScale := preflight.errorScale
      errorScale_nonneg := by
        simpa only [preflight, preflightCore,
          CycleSourcePreflightBounds.summary_errorScale,
          cycleSourceErrorScale] using
          cycleSourceErrorScale_nonnegative curve source data
      modelAllowance_le := by
        intro index
        change _ <= Geometric.Basic.quarterRadius
          (cycleSourceErrorScale source data) index
        calc
          _ <= Geometric.Basic.quarterRadius original.errorScale index :=
            original.modelAllowance_le index
          _ = Geometric.Basic.quarterRadius
              (cycleSourceExactErrorScale source data) index := by
            rewrite [compactCycleState_sourceIntegral_errorScale curve source data
              member]
            exact Eq.refl _
          _ <= Geometric.Basic.quarterRadius
              (cycleSourceErrorScale source data) index :=
            quarterRadius_scale_mono
              (cycleSourceExactErrorScale_le_preflight source data) index
      later_close := by
        intro earlier later order
        change _ <= Geometric.Basic.quarterRadius
          (cycleSourceErrorScale source data) earlier
        calc
          _ <= Geometric.Basic.quarterRadius original.errorScale earlier :=
            original.later_close order
          _ = Geometric.Basic.quarterRadius
              (cycleSourceExactErrorScale source data) earlier := by
            rewrite [compactCycleState_sourceIntegral_errorScale curve source data
              member]
            exact Eq.refl _
          _ <= Geometric.Basic.quarterRadius
              (cycleSourceErrorScale source data) earlier :=
            quarterRadius_scale_mono
              (cycleSourceExactErrorScale_le_preflight source data) earlier
      centerBound := preflight.centerBound
      centerBound_nonneg := by
        simpa only [preflight, preflightCore,
          CycleSourcePreflightBounds.summary_centerBound,
          cycleSourceCenterBound] using
          cycleSourceCenterBound_nonnegative curve source data
      sample_bounded := by
        intro index
        rw [← Norm.Basic.normSq_eq_canonical]
        let current :=
          (((compactCycleState curve source data).refinementStates [source]
            index).model source).integralSample
        let initial :=
          (((compactCycleState curve source data).refinementStates [source]
            0).model source).integralSample
        have movement :
            Data.Gaussian.Norm.Basic.normSq
                (current - initial) <= cycleSourceErrorScale source data := by
          calc
            Data.Gaussian.Norm.Basic.normSq
                (current - initial) <=
              Geometric.Basic.quarterRadius original.errorScale 0 :=
                (Norm.Basic.normSq_eq_canonical _).trans_le
                  (original.later_close (earlier := 0) (later := index) (Nat.zero_le index))
            _ = Geometric.Basic.quarterRadius
                (cycleSourceExactErrorScale source data) 0 := by
              rewrite [compactCycleState_sourceIntegral_errorScale curve source data
                member]
              exact Eq.refl _
            _ <= Geometric.Basic.quarterRadius
                (cycleSourceErrorScale source data) 0 :=
              quarterRadius_scale_mono
                (cycleSourceExactErrorScale_le_preflight source data) 0
            _ <= cycleSourceErrorScale source data :=
              Geometric.Basic.quarterRadius_le_scale
                (cycleSourceErrorScale_nonnegative curve source data) 0
        have initialBound :
            Data.Gaussian.Norm.Basic.normSq initial <=
              cycleSourceInitialSampleNormSqBound source data :=
          compactCycleState_sourceInitialSample_normSq_le curve source data
            member
        have initialPreflightBound :
            Data.Gaussian.Norm.Basic.normSq initial <=
              preflight.initialSampleNormSqBound :=
          initialBound.trans
            (cycleSourceInitialSampleNormSqBound_le_preflight source data)
        have identity : (current - initial) + initial = current := by
          apply Basic.ext <;>
            simp only [Basic.sub_re,
              Basic.sub_im,
              Basic.add_re,
              Basic.add_im] <;> ring1
        change Data.Gaussian.Norm.Basic.normSq current <= _
        rw [← identity]
        calc
          Data.Gaussian.Norm.Basic.normSq
              ((current - initial) + initial) <=
            2 * (Data.Gaussian.Norm.Basic.normSq
                  (current - initial) +
                Data.Gaussian.Norm.Basic.normSq initial) :=
              Norm.Bounds.normSq_add_le_two _ _
          _ <= 2 * (cycleSourceErrorScale source data +
                preflight.initialSampleNormSqBound) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add movement initialPreflightBound) (by decide)
          _ = preflight.centerBound := by
            dsimp only [preflight, preflightCore,
              CycleSourcePreflightBounds.summary]
            unfold cycleSourceErrorScale CycleSourcePreflightBounds.errorScale
            ring1 }

/-- The compact integral program uses the exact retained compact source model. -/
@[simp] theorem compactSourceIntegral_model {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) :
    (compactSourceIntegral curve source data).model index =
      compactSourceModel (compactSourceState curve source data) index := rfl

section
open Purelib.Integration.Program
/-- Use the supplied retained compact cache for the original integral program's exact models.

The cache's model equalities transport the original allowance, comparison and sample certificates while preserving its
cached computations. -/
@[expose] def compactSourceIntegralOfCache {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    {count : Nat} (cache : CompactSourceCache curve source data count) :
    Gaussian.Basic.RefinementProgram :=
  (compactSourceIntegral curve source data).withEquivalentModels cache.model
    (by
      intro index
      rw [cache.model_eq_compactSourceModel, compactSourceIntegral_model])

/-- Construct the compact integral program with a retained cache of the requested finite length. -/
@[expose] def boundedCompactSourceIntegral {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (data : PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) : Gaussian.Basic.RefinementProgram :=
  compactSourceIntegralOfCache curve source data
    (CompactSourceCache.canonical curve source data count)
end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The tail-evaluated weighted allowance splits over the cycle's exact ordered component banks. -/
theorem cycleState_tailMappedWeightedAllowance {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (model : CenteredEdge curve source ->
      Basic.CellModel) :
    forall (data : PreparedCycleModels.PreparedCycleData curve),
    Basic.PathModel.tailMappedWeightedAllowance
        (cycleState curve source data).parents model =
      match data with
      | .bridge bridge =>
          let forward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 bridge.forwardChecked
          let backward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 bridge.backwardChecked
          Basic.PathModel.tailMappedWeightedAllowance
              forward.parents model +
            Basic.PathModel.tailMappedWeightedAllowance
              backward.parents model
      | .finiteCut boundary =>
          let forward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.forwardChecked
          let rightBoundary :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.rightBoundaryChecked
          let backward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.backwardChecked
          let leftBoundary :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.leftBoundaryChecked
          Basic.PathModel.tailMappedWeightedAllowance
              forward.parents model +
            Basic.PathModel.tailMappedWeightedAllowance
                rightBoundary.parents model +
              Basic.PathModel.tailMappedWeightedAllowance
                  backward.parents model +
                Basic.PathModel.tailMappedWeightedAllowance
                  leftBoundary.parents model
  | .bridge bridge => by
      dsimp only [cycleState, bridgeState]
      rewrite [List.nil_append, Append.append_nil]
      repeat' rewrite [Basic.PathModel.tailMappedWeightedAllowance_append]
      exact Eq.refl _
  | .finiteCut boundary => by
      dsimp only [cycleState, boundaryState]
      rewrite [List.nil_append, Append.append_nil]
      repeat' rewrite [Basic.PathModel.tailMappedWeightedAllowance_append]
      ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The tail-evaluated integral sample splits over the cycle's exact ordered component banks. -/
theorem cycleState_tailMappedIntegralSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (source : Differentials.Basic.Differential genus)
    (model : CenteredEdge curve source ->
      Basic.CellModel) :
    forall (data : PreparedCycleModels.PreparedCycleData curve),
    Basic.PathModel.tailMappedIntegralSample
        (cycleState curve source data).parents model =
      match data with
      | .bridge bridge =>
          let forward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 bridge.forwardChecked
          let backward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 bridge.backwardChecked
          Basic.PathModel.tailMappedIntegralSample
              forward.parents model +
            Basic.PathModel.tailMappedIntegralSample
              backward.parents model
      | .finiteCut boundary =>
          let forward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.forwardChecked
          let rightBoundary :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.rightBoundaryChecked
          let backward :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.backwardChecked
          let leftBoundary :=
            PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.leftBoundaryChecked
          Basic.PathModel.tailMappedIntegralSample
              forward.parents model +
            Basic.PathModel.tailMappedIntegralSample
                rightBoundary.parents model +
              Basic.PathModel.tailMappedIntegralSample
                  backward.parents model +
                Basic.PathModel.tailMappedIntegralSample
                  leftBoundary.parents model
  | .bridge bridge => by
      dsimp only [cycleState, bridgeState]
      rewrite [List.nil_append, Append.append_nil]
      repeat' rewrite [Basic.PathModel.tailMappedIntegralSample_append]
      exact Eq.refl _
  | .finiteCut boundary => by
      dsimp only [cycleState, boundaryState]
      rewrite [List.nil_append, Append.append_nil]
      repeat' rewrite [Basic.PathModel.tailMappedIntegralSample_append]
      apply Basic.ext <;>
        simp only [Basic.add_re,
          Basic.add_im] <;> ring1

/-- Build a shared switched schedule from the exact prepared cycle and target differential list. -/
@[expose] def scheduleOfPreparedCycleData {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (targets : List (Differentials.Basic.Differential genus))
    (data : PreparedCycleModels.PreparedCycleData curve) :
    DifferentialSwitchedClosedSchedule curve source where
  initial := compactCycleState curve source data
  targets := targets
  closed := by cases data <;> rfl

/-- Every requested differential model of the prepared cycle schedule has a nonempty cell list. -/
theorem scheduleOfPreparedCycleData_integral_model_cells_positive {genus : Nat}
    (curve : Basic.HyperellipticCurve genus)
    (source : Differentials.Basic.Differential genus)
    (targets : List (Differentials.Basic.Differential genus))
    (data : PreparedCycleModels.PreparedCycleData curve)
    (differential : Differentials.Basic.Differential genus)
    (member : differential ∈ targets)
    (index : Nat) :
    0 < (((scheduleOfPreparedCycleData curve source targets data).integral
      differential member).model index).cells.length := by
  apply
    DifferentialSwitchedClosedSchedule.integral_model_cells_positive
  change 0 < (compactCycleState curve source data).chain.switchCount
  rw [compactCycleState_switchCount]
  decide

end Purelib.Riemann.Integration.PreparedSwitchedRefinements

end
