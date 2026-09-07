import CCL.Riemann.PreparedDirectDyadicRefinements
import CCL.Riemann.PreparedCycleModels

/-!
# Direct refinements with stationary sheet switches

Branch-cut cycles alternate nonstationary prepared banks with exact stationary
sheet transitions.  This module keeps those transitions in the dependent
lifted path while presenting only the nonstationary edges to the executable
direct refiner.  Thus every finite model has the actual closed-cycle geometry,
and no zero-width edge is smuggled into an interface requiring strict parameter
growth.
-/

namespace CCL.Riemann.PreparedSwitchedRefinements

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.BranchCutLifts
open CCL.Riemann.LiftedPaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev PathModel := CCL.ProgressiveGaussianIntegration.PathModel
abbrev CenteredEdge {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredEdge curve differential
abbrev SynchronizedDirectBlockRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (depth : Nat) (rootDiameter : Coordinate)
    (parents : List (CenteredEdge curve differential)) :=
  CCL.Riemann.PreparedDirectDyadicRefinements.SynchronizedDirectBlockRefinement
    depth rootDiameter parents

/-- The exact constant-zero integration cell associated to a stationary sheet
transition. -/
def stationaryModel (coordinate : Gaussian) : CellModel :=
  CCL.ProgressiveGaussianIntegration.CellModel.exact coordinate coordinate
    (CCL.FiniteGaussianPolynomial.constant 0)

@[simp] theorem stationaryModel_weightedAllowance (coordinate : Gaussian) :
    (stationaryModel coordinate).weightedAllowance = 0 := by
  unfold stationaryModel
    CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.exact
  rw [RFAP.ConstructiveFraction.mul_zero_direct]

@[simp] theorem stationaryModel_integralSample (coordinate : Gaussian) :
    (stationaryModel coordinate).integralSample = 0 := by
  unfold stationaryModel
    CCL.ProgressiveGaussianIntegration.CellModel.integralSample
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.ProgressiveGaussianIntegration.CellModel.exact
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] <;> ring1

set_option linter.unusedVariables false in
/-- A dependent lifted path made of positive-width centered edges and exact
stationary sheet switches.  The parent list deliberately omits the switches,
so it remains a valid input to the direct dyadic refiner. -/
inductive SwitchedPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    (parents : List (CenteredEdge curve differential)) ->
      {start finish : LiftedPoint 2} -> Type 2
  | nil (point : LiftedPoint 2) : SwitchedPathChain [] (start := point)
      (finish := point)
  | edge (parent : CenteredEdge curve differential)
      {remaining : List (CenteredEdge curve differential)}
      {finish : LiftedPoint 2}
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
  | stationary (coordinate : Gaussian) (sheet : Fin 2)
      {remaining : List (CenteredEdge curve differential)}
      {finish : LiftedPoint 2}
      (tail : SwitchedPathChain remaining
        (start := { coordinate := coordinate, sheet := otherSheet sheet })
        (finish := finish)) :
      SwitchedPathChain remaining
        (start := { coordinate := coordinate, sheet := sheet })
        (finish := finish)

namespace SwitchedPathChain

/-- Concatenate switched chains at their exact dependent endpoint. -/
def append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : LiftedPoint 2},
      SwitchedPathChain first (start := start) (finish := middle) ->
      SwitchedPathChain second (start := middle) (finish := finish) ->
        SwitchedPathChain (first ++ second) (start := start)
          (finish := finish)
  | [], _, _, _, _, .nil _, second => second
  | _ :: _, _, _, _, _, .edge parent tail, second =>
      .edge parent (append tail second)
  | _, _, _, _, _, .stationary coordinate sheet tail, second =>
      .stationary coordinate sheet (append tail second)

/-- Embed a centered positive-width chain without adding any switch. -/
def ofCenteredPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain parents
        (start := start) (finish := finish) ->
      SwitchedPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .edge parent (ofCenteredPathChain tail)

/-- Embed a direct positive-width chain without adding any switch. -/
def ofDirectPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      CCL.Riemann.PreparedDirectDyadicRefinements.DirectPathChain parents
        (start := start) (finish := finish) ->
      SwitchedPathChain parents (start := start) (finish := finish)
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .cons parent tail =>
      .edge parent (ofDirectPathChain tail)

/-- One exact stationary transition as a switched chain. -/
def singletonStationary {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (coordinate : Gaussian) (sheet : Fin 2) :
    SwitchedPathChain ([] : List (CenteredEdge curve differential))
      (start := { coordinate := coordinate, sheet := sheet })
      (finish := { coordinate := coordinate, sheet := otherSheet sheet }) :=
  .stationary coordinate sheet (.nil _)

/-- Number of exact stationary transitions retained by a switched chain. -/
def switchCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) -> Nat
  | [], _, _, .nil _ => 0
  | _ :: _, _, _, .edge _ tail => tail.switchCount
  | _, _, _, .stationary _ _ tail => tail.switchCount + 1

@[simp] theorem switchCount_ofCenteredPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain :
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain parents
          (start := start) (finish := finish)),
      (ofCenteredPathChain chain).switchCount = 0
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons _ tail =>
      switchCount_ofCenteredPathChain tail

@[simp] theorem switchCount_singletonStationary {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (coordinate : Gaussian) (sheet : Fin 2) :
    (singletonStationary (curve := curve) (differential := differential)
      coordinate sheet).switchCount = 1 :=
  rfl

/-- Canonical lifted path, including every stationary switch in place. -/
def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        LiftedPath 2 start finish
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons
        (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet
          parent.edge.localSegment)
        tail.path
  | _, _, _, .stationary coordinate sheet tail =>
      .cons (switchCell coordinate sheet) tail.path

/-- Integration cells in the exact geometric order of the switched path. -/
def cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        List CellModel
  | [], _, _, .nil _ => []
  | _ :: _, _, _, .edge parent tail => parent.model :: tail.cells
  | _, _, _, .stationary coordinate _sheet tail =>
      stationaryModel coordinate :: tail.cells

private theorem model_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.start =
      parent.edge.segment.pointAt parent.edge.left.parameter := by
  change parent.edge.point 0 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 0 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_zero] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 0).symm

private theorem model_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    (parent : CenteredEdge curve differential) :
    parent.model.finish =
      parent.edge.segment.pointAt
        parent.edge.request.endpoint.parameter := by
  change parent.edge.point 1 = _
  change
    (CCL.Riemann.PreparedDifferentialModels.edge curve parent.edge.segment
      parent.edge.within parent.edge.left parent.edge.request).pointAt 1 = _
  unfold CCL.Riemann.PreparedDifferentialModels.edge
  simpa only [CCL.Riemann.PreparedSheetContinuation.parameterAt_one] using
    (CCL.Riemann.PreparedSheetContinuation.pointAt_parameterAt
      parent.edge.segment parent.edge.within parent.edge.left
        parent.edge.request 1).symm

/-- Cell-for-cell uniform algebraic semantics on the switched path. -/
def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      UniformPathCertificates curve differential chain.cells chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons (model_start parent) (model_finish parent)
        (parent.edge.centeredValidCertificate curve differential parent.center)
        tail.certificates
  | _, _, _, .stationary coordinate sheet tail => by
      simpa only [cells, path, stationaryModel] using
        (UniformPathCertificates.cons rfl rfl (.stationary rfl)
          tail.certificates)

/-- Every switched model is cellwise Gaussian constant. -/
def constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells chain.cells
  | [], _, _, .nil _ => .nil
  | _ :: _, _, _, .edge parent tail =>
      .cons { coefficient := parent.center.value, polynomial_eq := rfl }
        tail.constantCells
  | _, _, _, .stationary coordinate _sheet tail => by
      simpa only [cells, stationaryModel] using
        CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells.cons
          (CCL.ProgressiveGaussianIntegration.CellModel.exactConstantCertificate
            coordinate coordinate 0)
          tail.constantCells

/-- Recenter the nonstationary cells for another differential without
changing the switched path geometry. -/
def recastCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2},
      SwitchedPathChain parents (start := start) (finish := finish) ->
        List CellModel
  | [], _, _, .nil _ => []
  | _ :: _, _, _, .edge parent tail =>
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
        parent).model :: recastCells target tail
  | _, _, _, .stationary coordinate _sheet tail =>
      stationaryModel coordinate :: recastCells target tail

private theorem recast_model_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) (parent : CenteredEdge curve source) :
    (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
      parent).model.start =
        parent.edge.segment.pointAt parent.edge.left.parameter := by
  exact model_start
    (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
      parent)

private theorem recast_model_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) (parent : CenteredEdge curve source) :
    (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
      parent).model.finish =
        parent.edge.segment.pointAt
          parent.edge.request.endpoint.parameter := by
  exact model_finish
    (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
      parent)

/-- Uniform certificates for every target differential on the unchanged
switched path. -/
def recastCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      UniformPathCertificates curve target (recastCells target chain) chain.path
  | [], _, _, .nil point => .nil point
  | _ :: _, _, _, .edge parent tail =>
      .cons (recast_model_start target parent)
        (recast_model_finish target parent)
        ((CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge target
          parent).edge.centeredValidCertificate curve target
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target parent).center)
        (recastCertificates target tail)
  | _, _, _, .stationary coordinate sheet tail => by
      simpa only [recastCells, path, stationaryModel] using
        (UniformPathCertificates.cons rfl rfl (.stationary rfl)
          (recastCertificates target tail))

/-- Target-recentered switched cells remain Gaussian constant. -/
def recastConstantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
        (recastCells target chain)
  | [], _, _, .nil _ => .nil
  | _ :: _, _, _, .edge parent tail =>
      .cons
        { coefficient :=
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target parent).center.value
          polynomial_eq := rfl }
        (recastConstantCells target tail)
  | _, _, _, .stationary coordinate _sheet tail => by
      simpa only [recastCells, stationaryModel] using
        CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells.cons
          (CCL.ProgressiveGaussianIntegration.CellModel.exactConstantCertificate
            coordinate coordinate 0)
          (recastConstantCells target tail)

/-- Replace every nonstationary parent by its synchronized child chain and
retain each stationary switch at its original position. -/
def refined {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (_chain : SwitchedPathChain parents (start := start) (finish := finish))
      (blocks : SynchronizedDirectBlockRefinement depth rootDiameter parents),
      SwitchedPathChain blocks.children (start := start) (finish := finish)
  | _, _, [], _, _, .nil point, .nil => .nil point
  | _, _, _ :: _, _, _, .edge _ tail, .cons block _ _ remaining =>
      (ofDirectPathChain block.chain).append (refined tail remaining)
  | _, _, _, _, _, .stationary coordinate sheet tail, blocks =>
      .stationary coordinate sheet (refined tail blocks)

@[simp] theorem switchCount_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)}
      {start middle finish : LiftedPoint 2}
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

@[simp] theorem switchCount_ofDirectPathChain {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain :
        CCL.Riemann.PreparedDirectDyadicRefinements.DirectPathChain parents
          (start := start) (finish := finish)),
      (ofDirectPathChain chain).switchCount = 0
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .cons _ tail =>
      switchCount_ofDirectPathChain tail

@[simp] theorem refined_switchCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {depth : Nat} {rootDiameter : Coordinate}
      {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
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
      simp only [refined, switchCount, refined_switchCount tail blocks]

@[simp] theorem cells_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
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

@[simp] theorem recastCells_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
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

/-- Stationary cells contribute exactly zero to the weighted semantic-error
sum.  Removing them therefore leaves the flattened recentered parent sum. -/
theorem recastCells_totalWeightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (chain.recastCells target)).totalWeightedAllowance =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := recastCells_totalWeightedAllowance target tail
      change
        (tail.recastCells target).foldr
            (fun cell total => cell.weightedAllowance + total) 0 =
          ((remaining.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
            (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      simp only [recastCells, List.map,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [recastCells,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons, stationaryModel_weightedAllowance,
        RFAP.ConstructiveFraction.zero_add]
      exact recastCells_totalWeightedAllowance target tail

/-- Stationary transitions likewise contribute exactly zero to the finite
integral sample. -/
theorem recastCells_integralSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus) :
    forall {parents : List (CenteredEdge curve source)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (chain.recastCells target)).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := recastCells_integralSample target tail
      change
        (tail.recastCells target).foldr
            (fun cell total => cell.integralSample + total) 0 =
          ((remaining.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
            (fun cell total => cell.integralSample + total) 0 at tailEqual
      simp only [recastCells, List.map,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [recastCells,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons, stationaryModel_integralSample,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
      exact recastCells_integralSample target tail

/-- Stationary transitions contribute zero to the finite integral even when
the retained source centres are used verbatim. -/
theorem cells_integralSample {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        chain.cells).integralSample =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := cells_integralSample tail
      change
        tail.cells.foldr (fun cell total => cell.integralSample + total) 0 =
          (remaining.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
              (fun cell total => cell.integralSample + total) 0 at tailEqual
      simp only [cells, List.map,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [cells,
        CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons, stationaryModel_integralSample,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
      exact cells_integralSample tail

/-- Stationary transitions contribute zero to the retained source model's
weighted allowance. -/
theorem cells_totalWeightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {parents : List (CenteredEdge curve differential)}
      {start finish : LiftedPoint 2}
      (chain : SwitchedPathChain parents (start := start) (finish := finish)),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        chain.cells).totalWeightedAllowance =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance
  | [], _, _, .nil _ => rfl
  | _parent :: remaining, _, _, .edge _ tail => by
      have tailEqual := cells_totalWeightedAllowance tail
      change
        tail.cells.foldr (fun cell total => cell.weightedAllowance + total) 0 =
          (remaining.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
              (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      simp only [cells, List.map,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons]
      rw [tailEqual]
  | _, _, _, .stationary coordinate _sheet tail => by
      simp only [cells,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_cons, stationaryModel_weightedAllowance,
        RFAP.ConstructiveFraction.zero_add]
      exact cells_totalWeightedAllowance tail

private theorem coordinateNatCast_nonnegative (value : Nat) :
    (0 : Coordinate) <= (value : Coordinate) := by
  induction value with
  | zero => exact le_rfl
  | succ value inductionHypothesis =>
      rw [Nat.cast_succ]
      exact add_nonneg inductionHypothesis (by decide)

/-- Source-centred switched models obey the same finite switch-factor bound
as recentered target models. -/
theorem cells_aggregateAllowance_le_switchFactor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {parents : List (CenteredEdge curve differential)}
    {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
        chain.cells).aggregateAllowance <=
      ((chain.switchCount : Coordinate) + 1) *
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [cells_length, cells_totalWeightedAllowance]
  cases parents with
  | nil =>
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.map, List.length_nil, List.foldr_nil,
        RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | cons parent remaining =>
      let weighted :=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parent :: remaining).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance
      have weightedNonnegative : 0 <= weighted :=
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance_nonneg _
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
          RFAP.ConstructiveFraction.mul_nonneg_direct switchesNonnegative
            remainingNonnegative
        simp only [List.length_cons, Nat.cast_add, Nat.cast_succ]
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
      simp only [List.length_map]
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
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct countLe
            weightedNonnegative
        _ = ((chain.switchCount : Coordinate) + 1) *
            (((parent :: remaining).length : Coordinate) * weighted) := by
          ring1

/-- Exact aggregate allowance of a switched model in terms of the ordinary
flattened positive-width model and the finite switch count. -/
theorem recastCells_aggregateAllowance_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    {parents : List (CenteredEdge curve source)}
    {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (chain.recastCells target)).aggregateAllowance =
      ((parents.length + chain.switchCount : Nat) : Coordinate) *
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [recastCells_length target chain,
    recastCells_totalWeightedAllowance target chain]

/-- The fixed rational factor paying for the stationary cells in aggregate
finite-path error estimates. -/
def switchFactor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    Coordinate :=
  (chain.switchCount : Coordinate) + 1

theorem switchFactor_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {parents : List (CenteredEdge curve source)}
    {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    0 < chain.switchFactor :=
  add_pos_of_nonneg_of_pos
    (coordinateNatCast_nonnegative chain.switchCount) (by decide)

/-- Adding finitely many zero-weight stationary cells increases the aggregate
allowance by at most `switchCount + 1`.  The empty-parent case is exact zero;
for a nonempty parent list the estimate is the elementary finite count bound
`n + s <= (s + 1) * n`. -/
theorem recastCells_aggregateAllowance_le_switchFactor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (target : Differential genus)
    {parents : List (CenteredEdge curve source)}
    {start finish : LiftedPoint 2}
    (chain : SwitchedPathChain parents (start := start) (finish := finish)) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (chain.recastCells target)).aggregateAllowance <=
      chain.switchFactor *
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance := by
  rw [recastCells_aggregateAllowance_eq target chain]
  cases parents with
  | nil =>
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.map, List.length_nil, List.foldr_nil,
        RFAP.ConstructiveFraction.mul_zero_direct]
      exact le_rfl
  | cons parent remaining =>
      let weighted :=
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (((parent :: remaining).map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              target)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance
      have weightedNonnegative : 0 <= weighted :=
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance_nonneg _
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
          RFAP.ConstructiveFraction.mul_nonneg_direct switchesNonnegative
            remainingNonnegative
        simp only [List.length_cons, Nat.cast_add, Nat.cast_succ, switchFactor]
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
      unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
      simp only [List.length_map]
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
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct countLe
            weightedNonnegative
        _ = chain.switchFactor *
            (((parent :: remaining).length : Coordinate) * weighted) := by
          ring1

end SwitchedPathChain

private theorem allParentsProper_append {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} :
    forall {first second : List (CenteredEdge curve differential)},
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper first ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper second ->
      CCL.Riemann.PreparedDyadicRefinements.AllParentsProper (first ++ second)
  | [], _second, _firstProper, secondProper => secondProper
  | _ :: _, _second, firstProper, secondProper =>
      ⟨firstProper.1,
        allParentsProper_append firstProper.2 secondProper⟩

private def closeLiftedPath
    {start finish : LiftedPoint 2}
    (path : LiftedPath 2 start finish) (closed : finish = start) :
    LiftedPath 2 start start := by
  subst finish
  exact path

private def closeUniformPathCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {cells : List CellModel}
    {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates : UniformPathCertificates curve differential cells path)
    (closed : finish = start) :
    UniformPathCertificates curve differential cells
      (closeLiftedPath path closed) := by
  subst finish
  exact certificates

/-- A complete switched path state.  Its positive-width parents are the only
objects refined; the dependent chain retains their order together with all
exact stationary sheet transitions. -/
structure DirectSwitchedState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) where
  start : LiftedPoint 2
  finish : LiftedPoint 2
  parents : List (CenteredEdge curve source)
  proper : CCL.Riemann.PreparedDyadicRefinements.AllParentsProper parents
  chain : SwitchedPathChain parents (start := start) (finish := finish)
  initialAllowanceBound : Differential genus -> Coordinate
  initialAllowance_le : forall target : Differential genus,
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          target)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      initialAllowanceBound target

namespace DirectSwitchedState

/-- The exact lifted geometry of a switched state. -/
def path {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source) :
    LiftedPath 2 state.start state.finish :=
  state.chain.path

/-- Target-differential model on the unchanged switched geometry. -/
def model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differential genus) : PathModel :=
  ⟨state.chain.recastCells target⟩

/-- Replace only the cached bound for the source differential.  Other target
differentials retain the state's existing bound, so higher-genus callers may
specialize one channel without weakening the remaining finite family. -/
def withSourceAllowanceBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (bound : Coordinate)
    (boundLe :
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((state.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            source)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
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
      simpa only [if_pos] using boundLe
    else
      simpa only [if_neg equal] using state.initialAllowance_le target

@[simp] theorem model_cells_length {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differential genus) :
    (state.model target).cells.length =
      state.parents.length + state.chain.switchCount :=
  state.chain.recastCells_length target

/-- Uniform target-differential semantics for the complete switched path. -/
def certificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differential genus) :
    UniformPathCertificates curve target (state.model target).cells state.path :=
  state.chain.recastCertificates target

/-- Target-recentered switched models retain the constant-cell invariant. -/
def constantCells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Differential genus) :
    CCL.ProgressiveGaussianIntegration.PathModel.ConstantCells
      (state.model target).cells :=
  state.chain.recastConstantCells target

/-- Close a switched state whose dependent endpoints agree. -/
def closedLift {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start) : ClosedLiftedPath 2 where
  basepoint := state.start
  path := closeLiftedPath state.path closed

/-- Uniformly certified closed model on a closed switched state. -/
def certifiedClosedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start)
    (target : Differential genus) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve target where
  lifted := state.closedLift closed
  cells := (state.model target).cells
  certificates := by
    unfold closedLift
    exact closeUniformPathCertificates (state.certificates target) closed

/-- Apply one synchronized source refinement while retaining every stationary
transition. -/
def refine {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {targets : List (Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
        state.parents targets target) :
    DirectSwitchedState curve source where
  start := state.start
  finish := state.finish
  parents := result.blocks.children
  proper := result.blocks.childrenProper
  chain := state.chain.refined result.blocks
  initialAllowanceBound := fun differential =>
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((result.blocks.children.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance
  initialAllowance_le := fun _ => le_rfl

/-- The smaller direct-refinement target which leaves room for the fixed
stationary-cell count in the complete switched aggregate allowance. -/
def directTarget {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (target : Coordinate) : Coordinate :=
  target / state.chain.switchFactor

theorem directTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    {target : Coordinate} (positive : 0 < target) :
    0 < state.directTarget target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    state.chain.switchFactor_positive

/-- Compute one common differential-family refinement small enough for the
complete switched path, not merely for its nonstationary sublist. -/
def accurateRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
      state.parents targets (state.directTarget target) :=
  CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialAccurateDirectRefinement
    state.parents state.proper targets (state.directTarget target)
      (state.directTarget_positive positive)

/-- The state produced by one accuracy-selected switched refinement. -/
def refineAccurately {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (target : Coordinate) (positive : 0 < target) :
    DirectSwitchedState curve source :=
  state.refine (state.accurateRefinement targets target positive)

/-- Every listed differential's complete switched child model meets the
original requested allowance after paying for its stationary cells. -/
theorem refineAccurately_modelAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (target : Coordinate) (positive : 0 < target)
    (differential : Differential genus) (member : differential ∈ targets) :
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
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct directBound
      factorNonnegative
  calc
    (refined.model differential).aggregateAllowance <=
        refined.chain.switchFactor *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((refined.parents.map
              (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
                differential)).map
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance :=
      switchedBound
    _ = state.chain.switchFactor *
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            ((result.blocks.children.map
              (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
                differential)).map
                  CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance := by
      unfold refined DirectSwitchedState.refine SwitchedPathChain.switchFactor
      rw [SwitchedPathChain.refined_switchCount]
    _ <= state.chain.switchFactor * state.directTarget target := scaledDirect
    _ = target := by
      unfold directTarget
      rw [mul_comm]
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target
        state.chain.switchFactor
          (ne_of_gt state.chain.switchFactor_positive)

@[simp] theorem refine_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {targets : List (Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).start = state.start := rfl

@[simp] theorem refine_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {targets : List (Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).finish = state.finish := rfl

@[simp] theorem refine_switchCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {targets : List (Differential genus)} {target : Coordinate}
    (state : DirectSwitchedState curve source)
    (result :
      CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
        state.parents targets target) :
    (state.refine result).chain.switchCount = state.chain.switchCount :=
  state.chain.refined_switchCount result.blocks

/-! ### A total common-geometry switched schedule -/

/-- Small strictly positive padding for the computed initial model allowance.
The padding is needed only to keep the recursive schedule target positive when
all displayed allowances vanish.  A unit-sized pad would force several
otherwise unnecessary whole-path refinements before the first ordinary
sampler request. -/
def scheduleSlack : Coordinate :=
  CCL.FiniteGeometric.quarterRadius 1 4

theorem scheduleSlack_positive : 0 < scheduleSlack := by
  unfold scheduleSlack
  exact CCL.FiniteGeometric.quarterRadius_pos (by decide) 4

/-- Sum the state's cached initial bounds over a displayed finite target
family.  Unlike the legacy model fold, this does not force construction of
the target coefficient model when the state carries a compact geometric
bound. -/
def initialAllowanceBoundSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    List (Differential genus) -> Coordinate
  | [] => 0
  | differential :: remaining =>
      initial.initialAllowanceBound differential +
        initialAllowanceBoundSum initial remaining

theorem initialAllowanceBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differential genus) :
    0 <= initial.initialAllowanceBound differential :=
  (CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((initial.parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))).trans
    (initial.initialAllowance_le differential)

theorem initialAllowanceBoundSum_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall targets : List (Differential genus),
      0 <= initialAllowanceBoundSum initial targets
  | [] => le_rfl
  | differential :: remaining =>
      add_nonneg (initialAllowanceBound_nonnegative initial differential)
        (initialAllowanceBoundSum_nonnegative initial remaining)

theorem member_initialAllowance_le_boundSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differential genus) :
    forall targets : List (Differential genus), differential ∈ targets ->
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((initial.parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            differential)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
        initialAllowanceBoundSum initial targets
  | [], member => by simp only [List.not_mem_nil] at member
  | head :: remaining, member => by
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact (initial.initialAllowance_le differential).trans
          (le_add_of_nonneg_right
            (initialAllowanceBoundSum_nonnegative initial remaining))
      · exact (member_initialAllowance_le_boundSum initial differential
          remaining member).trans
            (le_add_of_nonneg_left
              (initialAllowanceBound_nonnegative initial head))

/-- Positive initial scale dominating every listed differential's flattened
nonstationary model. -/
def scheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) : Coordinate :=
  initialAllowanceBoundSum initial targets + scheduleSlack

theorem scheduleBase_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) :
    0 < initial.scheduleBase targets := by
  unfold scheduleBase
  exact add_pos_of_nonneg_of_pos
    (initialAllowanceBoundSum_nonnegative initial targets)
    scheduleSlack_positive

/-- New-error target for the successor after `index`. -/
def scheduleTarget {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius (initial.scheduleBase targets) (index + 1)

theorem scheduleTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) (index : Nat) :
    0 < initial.scheduleTarget targets index :=
  CCL.FiniteGeometric.quarterRadius_pos
    (initial.scheduleBase_positive targets) (index + 1)

/-- Recursively refine the full nonstationary parent list at one common depth
and reinsert all stationary transitions in their original positions. -/
def refinementStates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) :
    Nat -> DirectSwitchedState curve source
  | 0 => initial
  | index + 1 =>
      let current := refinementStates initial targets index
      let result :=
        CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialAccurateDirectRefinement
          current.parents current.proper targets
            (initial.scheduleTarget targets index)
            (initial.scheduleTarget_positive targets index)
      current.refine result

/-- One delayed successor of an already retained switched-refinement state.
The target radius still comes from the canonical initial state, while all
parent geometry comes from the preceding cached state. -/
def cachedRefinementSuccessor {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differential genus))
    (previous : Thunk (DirectSwitchedState curve source))
    (index : Nat) : Thunk (DirectSwitchedState curve source) :=
  ⟨fun _ =>
    let current := previous.get
    let result :=
      CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialAccurateDirectRefinement
        current.parents current.proper targets
          (initial.get.scheduleTarget targets index)
          (initial.get.scheduleTarget_positive targets index)
    current.refine result⟩

theorem cachedRefinementSuccessor_get {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differential genus))
    (previous : Thunk (DirectSwitchedState curve source))
    (index : Nat)
    (previous_eq :
      previous.get = initial.get.refinementStates targets index) :
    (cachedRefinementSuccessor initial targets previous index).get =
      initial.get.refinementStates targets (index + 1) := by
  rw [cachedRefinementSuccessor, previous_eq]
  rfl

/-- A finite call-by-need prefix of switched-refinement states.  A `push`
retains the complete preceding cache and adds exactly the canonical state at
its next index; no entry is an unproved approximation to that state. -/
inductive BoundedRefinementCache {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differential genus)) : Nat -> Type 2
  | empty : BoundedRefinementCache initial targets 0
  | push {count : Nat}
      (prior : BoundedRefinementCache initial targets count)
      (state : Thunk (DirectSwitchedState curve source))
      (state_eq :
        state.get = initial.get.refinementStates targets count) :
      BoundedRefinementCache initial targets (count + 1)

namespace BoundedRefinementCache

/-- Retrieve one of the actual stored thunks.  Repeated calls at the same
index therefore force the same call-by-need cell in compiled clients. -/
def get {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)} :
    {count : Nat} -> BoundedRefinementCache initial targets count ->
      (index : Nat) -> index < count ->
        Thunk (DirectSwitchedState curve source)
  | 0, .empty, index, within =>
      (Nat.not_lt_zero index within).elim
  | count + 1, .push prior state _state_eq, index, within =>
      if equal : index = count then state
      else prior.get index
        (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp within) equal)

/-- Every retained thunk is propositionally the corresponding canonical
recursive state. -/
theorem get_state_eq {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)}
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

/-- Append the next canonical state.  At a positive bound its thunk closes
over the stored last thunk, so forcing the new entry cannot restart from the
initial state. -/
def pushNext {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count) :
    BoundedRefinementCache initial targets (count + 1) :=
  match cache with
  | .empty => .push .empty initial rfl
  | .push prior previous previous_eq =>
      .push (.push prior previous previous_eq)
        (cachedRefinementSuccessor initial targets previous _)
        (cachedRefinementSuccessor_get initial targets previous _ previous_eq)

/-- Extending a finite prefix reuses its stored thunks and allocates only the
requested number of new delayed successors. -/
def extend {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)}
    {count : Nat} (cache : BoundedRefinementCache initial targets count) :
    (extra : Nat) ->
      BoundedRefinementCache initial targets (count + extra)
  | 0 => by simpa only [Nat.add_zero] using cache
  | extra + 1 => by
      rw [Nat.add_succ]
      exact (cache.extend extra).pushNext

/-- Construct a fresh finite prefix without forcing its initial state. -/
def canonical {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : Thunk (DirectSwitchedState curve source))
    (targets : List (Differential genus)) (count : Nat) :
    BoundedRefinementCache initial targets count := by
  simpa only [Nat.zero_add] using
    (BoundedRefinementCache.empty (initial := initial)
      (targets := targets)).extend count

/-- Appending one state preserves each thunk already in the cache, not just
the mathematical value obtained after forcing it. -/
theorem pushNext_get {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)}
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

/-- A chunked extension retains the exact thunks of the original prefix. -/
theorem extend_get {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : Thunk (DirectSwitchedState curve source)}
    {targets : List (Differential genus)}
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

/-- The synchronized nonstationary refinement used at one successor. -/
def scheduledRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) (index : Nat) :
    CCL.Riemann.PreparedDirectDyadicRefinements.FiniteDifferentialAccurateDirectRefinement
      (initial.refinementStates targets index).parents targets
        (initial.scheduleTarget targets index) :=
  CCL.Riemann.PreparedDirectDyadicRefinements.finiteDifferentialAccurateDirectRefinement
    (initial.refinementStates targets index).parents
    (initial.refinementStates targets index).proper targets
      (initial.scheduleTarget targets index)
      (initial.scheduleTarget_positive targets index)

/-- Flattened nonstationary target model used to derive the finite Cauchy
estimate. -/
def flatModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) : PathModel :=
  ⟨(((initial.refinementStates targets index).parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)⟩

/-- Sign-aware rational lower endpoint for the real part of one flattened
switched refinement sample. -/
def flatModelIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) : Coordinate :=
  CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
    ((initial.refinementStates targets index).parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential))

/-- Sharp real endpoint from the process balls retained by one flattened
switched refinement state. -/
def flatModelBallIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) : Coordinate :=
  CCL.Riemann.PreparedSubdivisionModels.centeredEdgesBallIntegralRealLower
    ((initial.refinementStates targets index).parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential))

/-- The finite box lower endpoints bound the flattened path sample at every
displayed refinement index. -/
theorem flatModelIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelIntegralRealLower targets differential index <=
      (initial.flatModel targets differential index).integralSample.re := by
  exact
    CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_le
      exponentZero _

theorem flatModelBallIntegralRealLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelBallIntegralRealLower targets differential index <=
      (initial.flatModel targets differential index).integralSample.re := by
  exact
    CCL.Riemann.PreparedSubdivisionModels.centeredEdgesBallIntegralRealLower_le
      exponentZero _

/-- Centre-free lower endpoint for one arbitrary rational projection of a
flattened switched-refinement sample. -/
def flatModelDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
    (index : Nat) : Coordinate :=
  CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
    direction
      ((initial.refinementStates targets index).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential))

/-- Sharp arbitrary-direction endpoint from the retained coefficient process
balls of one flattened refinement state. -/
def flatModelBallDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
    (index : Nat) : Coordinate :=
  CCL.Riemann.PreparedSubdivisionModels.centeredEdgesBallDirectionalIntegralLower
    direction
      ((initial.refinementStates targets index).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential))

/-- The directional parent endpoints bound the same projection of every
displayed flattened refinement model. -/
theorem flatModelDirectionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelDirectionalIntegralLower targets differential direction
        index <=
      direction.re * (initial.flatModel targets differential index).integralSample.re +
        direction.im *
          (initial.flatModel targets differential index).integralSample.im := by
  exact
    CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_le
      direction exponentZero _

theorem flatModelBallDirectionalIntegralLower_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
    (index : Nat) (exponentZero : differential.exponent = 0) :
    initial.flatModelBallDirectionalIntegralLower targets differential direction
        index <=
      direction.re * (initial.flatModel targets differential index).integralSample.re +
        direction.im *
          (initial.flatModel targets differential index).integralSample.im := by
  exact
    CCL.Riemann.PreparedSubdivisionModels.centeredEdgesBallDirectionalIntegralLower_le
      direction exponentZero _

/-- Compatible flattened parent--child models on the exact common source
geometry. -/
def flatRefinementStep {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :
    CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
      (initial.flatModel targets differential index).cells
      (initial.flatModel targets differential (index + 1)).cells := by
  change CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
    ((((initial.refinementStates targets index).parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))
    ((((initial.scheduledRefinement targets index).blocks.children.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))
  exact (initial.scheduledRefinement targets index).compatible differential

/-- Every listed initial flattened model is dominated by the common base. -/
theorem initialFlatModelAllowance_le_base {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    (initial.flatModel targets differential 0).aggregateAllowance <=
      initial.scheduleBase targets := by
  unfold flatModel refinementStates scheduleBase
  exact
    (member_initialAllowance_le_boundSum initial differential targets
      member).trans
        (le_add_of_nonneg_right scheduleSlack_positive.le)

/-- Every listed flattened model meets the common quarter-radius semantic
target. -/
theorem flatModel_allowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    forall index,
      (initial.flatModel targets differential index).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius
          (initial.scheduleBase targets) index
  | 0 => by
      simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
        RFAP.ConstructiveFraction.mul_one_direct] using
          initial.initialFlatModelAllowance_le_base targets differential member
  | index + 1 => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((((initial.scheduledRefinement targets index).blocks.children.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              differential)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))).aggregateAllowance <=
          initial.scheduleTarget targets index
      exact (initial.scheduledRefinement targets index).modelAllowance_le
        differential member

/-- Consecutive flattened comparison allowance on the common family scale. -/
theorem flatRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets)
    (index : Nat) :
    (initial.flatRefinementStep targets differential index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * initial.scheduleBase targets) index := by
  let result := initial.scheduledRefinement targets index
  have comparisonBound := result.comparisonAllowance_le differential member
  have parentBound := initial.flatModel_allowance_le targets differential
    member index
  have doubledParent :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent :
      initial.scheduleTarget targets index <=
        CCL.FiniteGeometric.quarterRadius
          (initial.scheduleBase targets) index :=
    CCL.FiniteGeometric.quarterRadius_antitone
      (initial.scheduleBase_positive targets).le (Nat.le_succ index)
  change
    (result.compatible differential).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * initial.scheduleBase targets) index
  calc
    (result.compatible differential).comparisonAllowance <=
        2 * (initial.flatModel targets differential index).aggregateAllowance +
          initial.scheduleTarget targets index := comparisonBound
    _ <= 2 * CCL.FiniteGeometric.quarterRadius
            (initial.scheduleBase targets) index +
          CCL.FiniteGeometric.quarterRadius
            (initial.scheduleBase targets) index :=
      add_le_add doubledParent targetLeParent
    _ = CCL.FiniteGeometric.quarterRadius
        (3 * initial.scheduleBase targets) index := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

/-- Consecutive compatible program for the flattened nonstationary cells. -/
def flatSequentialProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram
    where
  model := initial.flatModel targets differential
  steps := initial.flatRefinementStep targets differential
  stepScale := 3 * initial.scheduleBase targets
  stepScale_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
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
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * initial.scheduleBase targets) := by ring1
  comparisonAllowance_le :=
    initial.flatRefinementStep_comparisonAllowance_le targets differential member

@[simp] theorem refinementStates_switchCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) :
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

/-- A retained stationary transition makes every finite switched refinement
model nonempty, independently of how many positive-width parents survive. -/
theorem refinementStates_model_cells_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus)
    (hasSwitch : 0 < initial.chain.switchCount)
    (index : Nat) :
    0 < ((initial.refinementStates targets index).model
      differential).cells.length := by
  rw [model_cells_length,
    initial.refinementStates_switchCount targets index]
  omega0

@[simp] theorem refinementStates_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) :
    forall index,
      (initial.refinementStates targets index).start = initial.start
  | 0 => rfl
  | index + 1 => by
      change (initial.refinementStates targets index).start = initial.start
      exact initial.refinementStates_start targets index

@[simp] theorem refinementStates_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus)) :
    forall index,
      (initial.refinementStates targets index).finish = initial.finish
  | 0 => rfl
  | index + 1 => by
      change (initial.refinementStates targets index).finish = initial.finish
      exact initial.refinementStates_finish targets index

theorem refinementStates_closed {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (closed : initial.finish = initial.start) :
    forall index,
      (initial.refinementStates targets index).finish =
        (initial.refinementStates targets index).start
  | index => by
      rw [initial.refinementStates_finish targets index,
        initial.refinementStates_start targets index]
      exact closed

/-- Stationary cells do not alter the displayed finite integral sample. -/
theorem model_integralSample_eq_flatModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :
    ((initial.refinementStates targets index).model
        differential).integralSample =
      (initial.flatModel targets differential index).integralSample :=
  SwitchedPathChain.recastCells_integralSample differential
    (initial.refinementStates targets index).chain

/-- Chunkable literal certificate for the nonstationary cells of one exact
switched refinement state.  Stationary sheet transitions are omitted because
their displayed integral is identically zero. -/
abbrev FlatPositiveLiteralRealLowerCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat) :=
  CCL.Riemann.PreparedSubdivisionModels.CenteredPathRecache.PositiveLiteralRealLowerCertificate
    ((initial.refinementStates targets index).parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        differential))

/-- A checked literal lower endpoint for the flattened cells bounds the
complete switched model at the same finite refinement state. -/
theorem FlatPositiveLiteralRealLowerCertificate.lower_le_model
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {initial : DirectSwitchedState curve source}
    {targets : List (Differential genus)}
    {differential : Differential genus} {index : Nat}
    (certificate : FlatPositiveLiteralRealLowerCertificate initial targets
      differential index) :
    certificate.lower <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact certificate.lower_le_canonical

/-- Stationary sheet transitions contribute zero, so the same finite rational
lower endpoint also bounds the complete switched model. -/
theorem flatModelIntegralRealLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelIntegralRealLower targets differential index <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelIntegralRealLower_le targets differential index
    exponentZero

theorem flatModelBallIntegralRealLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (index : Nat)
    (exponentZero : differential.exponent = 0) :
    initial.flatModelBallIntegralRealLower targets differential index <=
      ((initial.refinementStates targets index).model
        differential).integralSample.re := by
  rw [initial.model_integralSample_eq_flatModel targets differential index]
  exact initial.flatModelBallIntegralRealLower_le targets differential index
    exponentZero

/-- Stationary switches likewise preserve every rational linear projection
of the flattened sample. -/
theorem flatModelDirectionalIntegralLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
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

theorem flatModelBallDirectionalIntegralLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (direction : Gaussian)
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

/-- Ordinary Gaussian refinement program whose displayed models contain the
actual switched path cells.  Its Cauchy estimate and sample bound are derived
from the compatible flattened program, using the exact-zero switch samples. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram := by
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
        RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
          flat.errorScale_nonneg
      modelAllowance_le := by
        intro index
        have switchedBound :=
          SwitchedPathChain.recastCells_aggregateAllowance_le_switchFactor
            differential (initial.refinementStates targets index).chain
        have flatBound := flat.modelAllowance_le index
        have scaledFlat :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct flatBound
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
          _ <= factor * CCL.FiniteGeometric.quarterRadius
                flat.errorScale index := scaledFlat
          _ = CCL.FiniteGeometric.quarterRadius
              (factor * flat.errorScale) index := by
            rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
            ring1
      later_close := by
        intro earlier later order
        rw [initial.model_integralSample_eq_flatModel targets differential,
          initial.model_integralSample_eq_flatModel targets differential]
        have flatClose := flat.later_close order
        have radiusNonnegative := CCL.FiniteGeometric.quarterRadius_nonneg
          flat.errorScale_nonneg earlier
        calc
          RFAP.ConstructiveGaussian.Gaussian.normSq
              ((initial.flatModel targets differential later).integralSample -
                (initial.flatModel targets differential earlier).integralSample) <=
              CCL.FiniteGeometric.quarterRadius flat.errorScale earlier :=
            flatClose
          _ = 1 * CCL.FiniteGeometric.quarterRadius flat.errorScale earlier := by
            ring1
          _ <= factor *
                CCL.FiniteGeometric.quarterRadius flat.errorScale earlier :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              oneLeFactor radiusNonnegative
          _ = CCL.FiniteGeometric.quarterRadius
              (factor * flat.errorScale) earlier := by
            rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
            ring1
      centerBound := flat.centerBound
      centerBound_nonneg := flat.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [initial.model_integralSample_eq_flatModel targets differential]
        exact flat.sample_bounded index }

/-- Exact finite scale exposed by the switched program constructor.  Keeping
this small structural identity public lets explicit examples replace the
large initial allowance fold by an equal stack-safe presentation before
performing kernel arithmetic. -/
theorem integral_errorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (targets : List (Differential genus))
    (differential : Differential genus) (member : differential ∈ targets) :
    (initial.integral targets differential member).errorScale =
      initial.chain.switchFactor *
        (4 * (3 * initial.scheduleBase targets)) := rfl

/-! ### Source-centred switched schedules

The common-differential constructor above deliberately recentres every target,
including the source.  A generated literal comparison may instead select a
later persisted source centre.  The following source-only schedule retains
those centres at index zero and then uses the ordinary direct child centres.
-/

/-- Canonically recasting retained centres to their existing differential
does not change the finite weighted-allowance sum. -/
private theorem recastCenteredEdges_self_totalWeightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus} :
    forall parents : List (CenteredEdge curve source),
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        ((parents.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            source)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance =
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          (parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).totalWeightedAllowance
  | [] => rfl
  | parent :: remaining => by
      have tailEqual :=
        recastCenteredEdges_self_totalWeightedAllowance remaining
      change
        ((remaining.map
          (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
            source)).map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
                (fun cell total => cell.weightedAllowance + total) 0 =
          (remaining.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).foldr
              (fun cell total => cell.weightedAllowance + total) 0 at tailEqual
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.map, List.foldr_cons]
      rw [CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge_self_weightedAllowance,
        tailEqual]

/-- The aggregate allowance is likewise invariant under same-differential
canonical recasting; coefficient centres do not enter this error budget. -/
theorem recastCenteredEdges_self_aggregateAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (parents : List (CenteredEdge curve source)) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  change
    (↑(((parents.map
      (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
        source)).map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).length) : Coordinate) * _ =
      (↑((parents.map
        CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).length) : Coordinate) * _
  simp only [List.length_map]
  rw [recastCenteredEdges_self_totalWeightedAllowance]

/-- Positive scale dominating the retained source-centred initial model. -/
def sourceScheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) : Coordinate :=
  initial.initialAllowanceBound source + scheduleSlack

theorem sourceScheduleBase_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    0 < initial.sourceScheduleBase := by
  unfold sourceScheduleBase
  exact add_pos_of_nonneg_of_pos
    ((CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg _).trans
      (initial.initialAllowance_le source))
    scheduleSlack_positive

/-- New-error target for one successor of the source-centred schedule. -/
def sourceScheduleTarget {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : Coordinate :=
  CCL.FiniteGeometric.quarterRadius initial.sourceScheduleBase (index + 1)

theorem sourceScheduleTarget_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    0 < initial.sourceScheduleTarget index :=
  CCL.FiniteGeometric.quarterRadius_pos
    initial.sourceScheduleBase_positive (index + 1)

/-- Refine the retained source parents without first replacing their centre
states by canonical ones. -/
def refineSource {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    {target : Coordinate}
    (result :
      CCL.Riemann.PreparedDirectDyadicRefinements.AccurateDirectRefinement
        state.parents target) : DirectSwitchedState curve source where
  start := state.start
  finish := state.finish
  parents := result.blocks.children
  proper := result.blocks.childrenProper
  chain := state.chain.refined result.blocks
  initialAllowanceBound := fun differential =>
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      ((result.blocks.children.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          differential)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance
  initialAllowance_le := fun _ => le_rfl

/-- Recursively refined switched states whose index-zero centres are retained
verbatim. -/
def sourceRefinementStates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    Nat -> DirectSwitchedState curve source
  | 0 => initial
  | index + 1 =>
      let current := sourceRefinementStates initial index
      let result :=
        CCL.Riemann.PreparedDirectDyadicRefinements.accurateDirectRefinement
          current.parents current.proper
            (initial.sourceScheduleTarget index)
            (initial.sourceScheduleTarget_positive index)
      current.refineSource result

/-- The source-only direct refinement performed at one successor. -/
def sourceScheduledRefinement {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    CCL.Riemann.PreparedDirectDyadicRefinements.AccurateDirectRefinement
      (initial.sourceRefinementStates index).parents
        (initial.sourceScheduleTarget index) :=
  CCL.Riemann.PreparedDirectDyadicRefinements.accurateDirectRefinement
    (initial.sourceRefinementStates index).parents
    (initial.sourceRefinementStates index).proper
    (initial.sourceScheduleTarget index)
    (initial.sourceScheduleTarget_positive index)

/-- Flattened positive-width source model, retaining its actual centres. -/
def sourceFlatModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : PathModel :=
  ⟨((initial.sourceRefinementStates index).parents.map
    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)⟩

/-- One compatible source-centred refinement step. -/
def sourceFlatRefinementStep {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
      (initial.sourceFlatModel index).cells
      (initial.sourceFlatModel (index + 1)).cells := by
  change CCL.ProgressiveGaussianIntegration.PathModel.CompatibleConstantPathRefinement
    ((initial.sourceRefinementStates index).parents.map
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
    ((initial.sourceScheduledRefinement index).blocks.children.map
      CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)
  exact (initial.sourceScheduledRefinement index).blocks.toCompatibleChildren

/-- Every source-centred model meets its geometric allowance target. -/
theorem sourceFlatModel_allowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index,
      (initial.sourceFlatModel index).aggregateAllowance <=
        CCL.FiniteGeometric.quarterRadius initial.sourceScheduleBase index
  | 0 => by
      unfold sourceFlatModel sourceRefinementStates sourceScheduleBase
      simp only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
        RFAP.ConstructiveFraction.mul_one_direct]
      calc
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (initial.parents.map
              CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance =
            (CCL.ProgressiveGaussianIntegration.PathModel.mk
              ((initial.parents.map
                (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
                  source)).map
                    CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance :=
          (recastCenteredEdges_self_aggregateAllowance initial.parents).symm
        _ <= initial.initialAllowanceBound source :=
          initial.initialAllowance_le source
        _ <= initial.initialAllowanceBound source + scheduleSlack :=
          le_add_of_nonneg_right scheduleSlack_positive.le
  | index + 1 => by
      change
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((initial.sourceScheduledRefinement index).blocks.children.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
          initial.sourceScheduleTarget index
      exact (initial.sourceScheduledRefinement index).modelAllowance_le

/-- Consecutive source-centred comparisons decay on one common scale. -/
theorem sourceFlatRefinementStep_comparisonAllowance_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    (initial.sourceFlatRefinementStep index).comparisonAllowance <=
      CCL.FiniteGeometric.quarterRadius
        (3 * initial.sourceScheduleBase) index := by
  have comparisonBound :=
    (initial.sourceScheduledRefinement index).comparisonAllowanceChildren_le
  have parentBound := initial.sourceFlatModel_allowance_le index
  have doubledParent :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct parentBound
      (show (0 : Coordinate) <= 2 by decide)
  have targetLeParent : initial.sourceScheduleTarget index <=
      CCL.FiniteGeometric.quarterRadius initial.sourceScheduleBase index :=
    CCL.FiniteGeometric.quarterRadius_antitone
      initial.sourceScheduleBase_positive.le (Nat.le_succ index)
  calc
    (initial.sourceFlatRefinementStep index).comparisonAllowance <=
        2 * (initial.sourceFlatModel index).aggregateAllowance +
          initial.sourceScheduleTarget index := comparisonBound
    _ <= 2 * CCL.FiniteGeometric.quarterRadius
            initial.sourceScheduleBase index +
          CCL.FiniteGeometric.quarterRadius
            initial.sourceScheduleBase index :=
      add_le_add doubledParent targetLeParent
    _ = CCL.FiniteGeometric.quarterRadius
        (3 * initial.sourceScheduleBase) index := by
      rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
        CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
      ring1

/-- Source-centred compatible program for the nonstationary cells. -/
def sourceFlatSequentialProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram
    where
  model := initial.sourceFlatModel
  steps := initial.sourceFlatRefinementStep
  stepScale := 3 * initial.sourceScheduleBase
  stepScale_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    initial.sourceScheduleBase_positive.le
  initialAllowance_le := by
    have baseNonnegative := initial.sourceScheduleBase_positive.le
    calc
      (initial.sourceFlatModel 0).aggregateAllowance <=
          initial.sourceScheduleBase := by
        simpa only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_zero,
          RFAP.ConstructiveFraction.mul_one_direct] using
            initial.sourceFlatModel_allowance_le 0
      _ = 1 * initial.sourceScheduleBase := by ring1
      _ <= 12 * initial.sourceScheduleBase :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 12 by decide) baseNonnegative
      _ = 4 * (3 * initial.sourceScheduleBase) := by ring1
  comparisonAllowance_le := initial.sourceFlatRefinementStep_comparisonAllowance_le

@[simp] theorem sourceRefinementStates_switchCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
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

@[simp] theorem sourceRefinementStates_start {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index, (initial.sourceRefinementStates index).start = initial.start
  | 0 => rfl
  | index + 1 => initial.sourceRefinementStates_start index

@[simp] theorem sourceRefinementStates_finish {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    forall index, (initial.sourceRefinementStates index).finish = initial.finish
  | 0 => rfl
  | index + 1 => initial.sourceRefinementStates_finish index

theorem sourceRefinementStates_closed {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (closed : initial.finish = initial.start) :
    forall index,
      (initial.sourceRefinementStates index).finish =
        (initial.sourceRefinementStates index).start
  | index => by
      rw [initial.sourceRefinementStates_finish index,
        initial.sourceRefinementStates_start index]
      exact closed

/-- Complete source-centred model with every stationary switch reinserted. -/
def sourceModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) : PathModel :=
  ⟨(initial.sourceRefinementStates index).chain.cells⟩

theorem sourceModel_integralSample_eq_flatModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    (initial.sourceModel index).integralSample =
      (initial.sourceFlatModel index).integralSample :=
  SwitchedPathChain.cells_integralSample
    (initial.sourceRefinementStates index).chain

/-- Uniform semantics of the complete source-centred model at one index. -/
def sourceCertificates {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    UniformPathCertificates curve source
      (initial.sourceModel index).cells
      (initial.sourceRefinementStates index).path :=
  (initial.sourceRefinementStates index).chain.certificates

/-- Close one retained source-centred state without recentering its cells. -/
def certifiedClosedSourceModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : DirectSwitchedState curve source)
    (closed : state.finish = state.start) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve source where
  lifted := state.closedLift closed
  cells := state.chain.cells
  certificates := by
    unfold closedLift
    exact closeUniformPathCertificates state.chain.certificates closed

/-- Source-centred switched refinement program.  Unlike `integral`, its
index-zero model retains the exact persisted centres supplied by the caller. -/
def sourceIntegral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram := by
  let flat := initial.sourceFlatSequentialProgram.toRefinementProgram
  let factor := initial.chain.switchFactor
  have factorNonnegative : 0 <= factor := initial.chain.switchFactor_positive.le
  have oneLeFactor : (1 : Coordinate) <= factor := by
    unfold factor SwitchedPathChain.switchFactor
    exact le_add_of_nonneg_left
      (SwitchedPathChain.coordinateNatCast_nonnegative
        initial.chain.switchCount)
  exact
    { model := initial.sourceModel
      errorScale := factor * flat.errorScale
      errorScale_nonneg :=
        RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
          flat.errorScale_nonneg
      modelAllowance_le := by
        intro index
        have switchedBound :=
          SwitchedPathChain.cells_aggregateAllowance_le_switchFactor
            (initial.sourceRefinementStates index).chain
        have flatBound := flat.modelAllowance_le index
        have scaledFlat :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct flatBound
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
          _ <= factor * CCL.FiniteGeometric.quarterRadius
                flat.errorScale index := scaledFlat
          _ = CCL.FiniteGeometric.quarterRadius
              (factor * flat.errorScale) index := by
            rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
            ring1
      later_close := by
        intro earlier later order
        rw [initial.sourceModel_integralSample_eq_flatModel,
          initial.sourceModel_integralSample_eq_flatModel]
        have flatClose := flat.later_close order
        have radiusNonnegative := CCL.FiniteGeometric.quarterRadius_nonneg
          flat.errorScale_nonneg earlier
        calc
          RFAP.ConstructiveGaussian.Gaussian.normSq
              ((initial.sourceFlatModel later).integralSample -
                (initial.sourceFlatModel earlier).integralSample) <=
              CCL.FiniteGeometric.quarterRadius flat.errorScale earlier :=
            flatClose
          _ = 1 * CCL.FiniteGeometric.quarterRadius flat.errorScale earlier := by
            ring1
          _ <= factor *
                CCL.FiniteGeometric.quarterRadius flat.errorScale earlier :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              oneLeFactor radiusNonnegative
          _ = CCL.FiniteGeometric.quarterRadius
              (factor * flat.errorScale) earlier := by
            rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
            ring1
      centerBound := flat.centerBound
      centerBound_nonneg := flat.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [initial.sourceModel_integralSample_eq_flatModel]
        exact flat.sample_bounded index }

theorem sourceIntegral_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source) (index : Nat) :
    initial.sourceIntegral.model index = initial.sourceModel index := rfl

/-- A singleton differential family has exactly one initial path allowance
in its common switched base. -/
theorem scheduleBase_singleton {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (initial : DirectSwitchedState curve source)
    (differential : Differential genus) :
    initial.scheduleBase [differential] =
      initial.initialAllowanceBound differential + scheduleSlack := by
  simp only [scheduleBase, initialAllowanceBoundSum, _root_.add_zero]

end DirectSwitchedState

/-- A closed source-centred switched schedule.  This is the single-
differential counterpart of `FiniteDifferentialSwitchedClosedSchedule`; its
index-zero centres are retained verbatim. -/
structure SourceSwitchedClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) where
  initial : DirectSwitchedState curve source
  closed : initial.finish = initial.start

namespace SourceSwitchedClosedSchedule

def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) :
    CCL.Riemann.LiftedPaths.LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    (schedule.initial.sourceRefinementStates index).closedLift
      (schedule.initial.sourceRefinementStates_closed schedule.closed index)

def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) (index : Nat) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve source :=
  (schedule.initial.sourceRefinementStates index).certifiedClosedSourceModel
    (schedule.initial.sourceRefinementStates_closed schedule.closed index)

/-- Certified period program whose initial model retains externally selected
persisted source centres. -/
def certifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : SourceSwitchedClosedSchedule curve source) :
    CertifiedPeriodProgram curve source schedule.cycle where
  integral := schedule.initial.sourceIntegral
  certificates := by
    intro index
    exact (schedule.certifiedModel index).certificates

end SourceSwitchedClosedSchedule

/-- One closed switched state whose total finite refinement geometry is
shared by every differential in a displayed family. -/
structure FiniteDifferentialSwitchedClosedSchedule {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) where
  initial : DirectSwitchedState curve source
  targets : List (Differential genus)
  closed : initial.finish = initial.start

namespace FiniteDifferentialSwitchedClosedSchedule

/-- Persistent closed lifted cycle with every stationary transition retained
at every index. -/
def cycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source) :
    CCL.Riemann.LiftedPaths.LiftedCycleRefinement 2 where
  liftedPath := fun index =>
    (schedule.initial.refinementStates schedule.targets index).closedLift
      (schedule.initial.refinementStates_closed schedule.targets
        schedule.closed index)

/-- Certified closed finite model for any target differential on the exact
common switched cycle. -/
def certifiedModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source)
    (differential : Differential genus) (index : Nat) :
    CCL.Riemann.PreparedCycleModels.CertifiedClosedModel curve differential := by
  let state := schedule.initial.refinementStates schedule.targets index
  exact state.certifiedClosedModel
      (schedule.initial.refinementStates_closed schedule.targets
        schedule.closed index)
      differential

/-- Executable switched Gaussian program of one listed differential. -/
def integral {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram :=
  schedule.initial.integral schedule.targets differential member

@[simp] theorem integral_model_cells {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) (index : Nat) :
    ((schedule.integral differential member).model index).cells =
      (schedule.certifiedModel differential index).cells := rfl

/-- A closed switched schedule with a retained transition has a nonempty
finite integration model at every request. -/
theorem integral_model_cells_positive {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets)
    (hasSwitch : 0 < schedule.initial.chain.switchCount)
    (index : Nat) :
    0 < ((schedule.integral differential member).model index).cells.length :=
  schedule.initial.refinementStates_model_cells_positive schedule.targets
    differential hasSwitch index

/-- Certified period program on the differential-independent switched cycle. -/
def certifiedPeriodProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (schedule : FiniteDifferentialSwitchedClosedSchedule curve source)
    (differential : Differential genus)
    (member : differential ∈ schedule.targets) :
    CertifiedPeriodProgram curve differential schedule.cycle where
  integral := schedule.integral differential member
  certificates := by
    intro index
    rw [schedule.integral_model_cells differential member index]
    exact (schedule.certifiedModel differential index).certificates

end FiniteDifferentialSwitchedClosedSchedule

private theorem totalWeightedAllowance_append
    (first second : List CCL.ProgressiveGaussianIntegration.CellModel) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (first ++ second)).totalWeightedAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        first).totalWeightedAllowance +
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
        List.foldr_nil]
      rw [zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append,
        CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance,
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

private theorem gaussianNormSqSum_append (first second : List Gaussian) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum (first ++ second) =
      RFAP.ConstructiveFiniteNorm.gaussianNormSqSum first +
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum second := by
  induction first with
  | nil =>
      simp only [List.nil_append,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      rw [zero_add]
  | cons value remaining inductionHypothesis =>
      simp only [List.cons_append,
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum]
      rw [inductionHypothesis]
      ring1

private theorem gaussianNormSqSum_nonnegative : forall values : List Gaussian,
    0 <= RFAP.ConstructiveFiniteNorm.gaussianNormSqSum values
  | [] => le_rfl
  | value :: remaining =>
      add_nonneg (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg value)
        (gaussianNormSqSum_nonnegative remaining)

private theorem pathModel_integralSample_eq_gaussianSum
    (cells : List CCL.ProgressiveGaussianIntegration.CellModel) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk cells).integralSample =
      RFAP.ConstructiveFiniteNorm.gaussianSum
        (cells.map fun cell => cell.integralSample) := by
  induction cells with
  | nil => rfl
  | cons cell remaining inductionHypothesis =>
      simp only [CCL.ProgressiveGaussianIntegration.PathModel.integralSample,
        List.foldr_cons, List.map_cons,
        RFAP.ConstructiveFiniteNorm.gaussianSum]
      change
        remaining.foldr (fun cell total => cell.integralSample + total) 0 =
          RFAP.ConstructiveFiniteNorm.gaussianSum
            (remaining.map fun cell => cell.integralSample)
        at inductionHypothesis
      rw [inductionHypothesis]

private theorem centeredEdgeIntegralSamples_map_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus} :
    forall parents : List (CenteredEdge curve source),
      (parents.map
          CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model).map
            (fun cell => cell.integralSample) =
        parents.map (fun parent => parent.model.integralSample)
  | [] => rfl
  | parent :: remaining => by
      simp only [List.map_cons,
        centeredEdgeIntegralSamples_map_model remaining]

/-- Build the exact two-bank switched state carried by a prepared bridge. -/
def bridgeState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    DirectSwitchedState curve source := by
  let forward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let backward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
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
        simpa only [List.nil_append, List.append_nil] using
          allParentsProper_append forward.proper backward.proper
      chain := combined
      initialAllowanceBound := fun differential =>
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              differential)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

/-- Number of nonstationary parents in a prepared two-bank bridge, computed
from the two original clear paths and their common dyadic depth. -/
def bridgeSourceParentCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) : Nat :=
  2 ^ data.depth * data.basePath.segmentCount +
    2 ^ data.depth *
      (CCL.Riemann.BranchCutLifts.ClearPath.reverse
        data.basePath).segmentCount

/-- Owner-independent total-weight bound for the two displayed bridge paths. -/
def bridgeSourceTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.depth data.basePath +
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.depth
        (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.basePath)

/-- Fixed-grid owner-independent total-weight bound used only by executable
bridge preflight.  The sharper unrounded bound remains theorem-facing. -/
def bridgeSourceTotalWeightedPreflightBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.depth data.basePath +
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.depth
        (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.basePath)

/-- Owner-independent additive squared-sample bound for the two paths. -/
def bridgeSourceIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.depth data.basePath +
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.depth
        (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.basePath)

def bridgeSourceAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  (bridgeSourceParentCount data : Coordinate) *
    bridgeSourceTotalWeightedBound source data

def bridgeSourcePreflightAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    Coordinate :=
  (bridgeSourceParentCount data : Coordinate) *
    bridgeSourceTotalWeightedPreflightBound source data

theorem bridgeSourceAggregateBound_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    bridgeSourceAggregateBound source data <=
      bridgeSourcePreflightAggregateBound source data := by
  unfold bridgeSourceAggregateBound bridgeSourcePreflightAggregateBound
    bridgeSourceTotalWeightedBound
    bridgeSourceTotalWeightedPreflightBound
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.depth data.basePath)
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.depth
          (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.basePath))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

theorem bridgeState_parents {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).parents =
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 0 data.forwardChecked).parents ++
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 1 data.backwardChecked).parents := by
  unfold bridgeState
  simp only [List.nil_append, List.append_nil]

/-- The actual source-bank initial samples obey the compact two-bank bound. -/
theorem bridgeState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
        ((bridgeState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      bridgeSourceIntegralNormSqSumBound source data := by
  rw [bridgeState_parents]
  unfold bridgeSourceIntegralNormSqSumBound
  simp only [List.map_append]
  rw [gaussianNormSqSum_append]
  exact add_le_add
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 0 data.forwardChecked)
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 1 data.backwardChecked)

/-- Source-differential allowance of a two-bank switched state is bounded
without constructing any leaf coefficient model. -/
theorem bridgeState_sourceAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (((bridgeState curve source data).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      bridgeSourceAggregateBound source data := by
  let forward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let backward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.backwardChecked
  rw [bridgeState_parents]
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
    bridgeSourceAggregateBound bridgeSourceParentCount
    bridgeSourceTotalWeightedBound
  simp only [List.map_append, List.length_append, List.length_map]
  rw [CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.forwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.backwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.forwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.backwardChecked,
    totalWeightedAllowance_append]
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 0 data.forwardChecked)
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 1 data.backwardChecked)
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

@[simp] theorem bridgeState_switchCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).chain.switchCount = 2 := by
  unfold bridgeState
  simp only [SwitchedPathChain.switchCount_append,
    SwitchedPathChain.switchCount_ofCenteredPathChain]
  rfl

/-- Build the exact four-bank switched state carried by a prepared finite
cut, including both winding-one boundary paths before their switches. -/
def boundaryState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    DirectSwitchedState curve source := by
  let forward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.forwardChecked
  let rightBoundary :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 0 data.rightBoundaryChecked
  let backward :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
      curve source 1 data.backwardChecked
  let leftBoundary :=
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
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
        simpa only [List.nil_append, List.append_nil] using
          allParentsProper_append forward.proper
            (allParentsProper_append rightBoundary.proper
              (allParentsProper_append backward.proper leftBoundary.proper))
      chain := combined
      initialAllowanceBound := fun differential =>
        (CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((parents.map
            (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
              differential)).map
                CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance
      initialAllowance_le := fun _ => le_rfl }

def boundarySourceParentCount {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Nat :=
  2 ^ data.forwardDepth * data.connector.segmentCount +
    (2 ^ data.rightBoundaryDepth * data.rightBoundaryPath.segmentCount +
      (2 ^ data.backwardDepth *
          (CCL.Riemann.BranchCutLifts.ClearPath.reverse
            data.connector).segmentCount +
        2 ^ data.leftBoundaryDepth * data.leftBoundaryPath.segmentCount))

def boundarySourceTotalWeightedBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
      source data.rootDiameter data.forwardDepth data.connector +
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
          source data.rootDiameter data.backwardDepth
            (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.connector) +
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound
          source data.rootDiameter data.leftBoundaryDepth data.leftBoundaryPath))

/-- Fixed-grid owner-independent total-weight bound used only by executable
finite-cut preflight. -/
def boundarySourceTotalWeightedPreflightBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
      source data.rootDiameter data.forwardDepth data.connector +
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source data.rootDiameter data.backwardDepth
            (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.connector) +
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedDyadicBound
          source data.rootDiameter data.leftBoundaryDepth
            data.leftBoundaryPath))

def boundarySourceIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
      source data.rootDiameter data.forwardDepth data.connector +
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
        source data.rootDiameter data.rightBoundaryDepth
          data.rightBoundaryPath +
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source data.rootDiameter data.backwardDepth
            (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.connector) +
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathIntegralNormSqCeilBound
          source data.rootDiameter data.leftBoundaryDepth data.leftBoundaryPath))

def boundarySourceAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  (boundarySourceParentCount data : Coordinate) *
    boundarySourceTotalWeightedBound source data

def boundarySourcePreflightAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    Coordinate :=
  (boundarySourceParentCount data : Coordinate) *
    boundarySourceTotalWeightedPreflightBound source data

theorem boundarySourceAggregateBound_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    boundarySourceAggregateBound source data <=
      boundarySourcePreflightAggregateBound source data := by
  unfold boundarySourceAggregateBound boundarySourcePreflightAggregateBound
    boundarySourceTotalWeightedBound
    boundarySourceTotalWeightedPreflightBound
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
        source data.rootDiameterPositive.le data.forwardDepth data.connector)
      (add_le_add
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
          source data.rootDiameterPositive.le data.rightBoundaryDepth
            data.rightBoundaryPath)
        (add_le_add
          (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
            source data.rootDiameterPositive.le data.backwardDepth
              (CCL.Riemann.BranchCutLifts.ClearPath.reverse data.connector))
          (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.dyadicPathTotalWeightedBound_le_dyadicBound
            source data.rootDiameterPositive.le data.leftBoundaryDepth
              data.leftBoundaryPath)))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

theorem boundaryState_parents {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).parents =
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
          curve source 0 data.forwardChecked).parents ++
        ((CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
            curve source 0 data.rightBoundaryChecked).parents ++
          ((CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 data.backwardChecked).parents ++
            (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 data.leftBoundaryChecked).parents)) := by
  unfold boundaryState
  simp only [List.nil_append, List.append_nil]

/-- The actual source-bank samples of the four-bank finite cut obey their
compact additive squared-norm bound. -/
theorem boundaryState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
        ((boundaryState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      boundarySourceIntegralNormSqSumBound source data := by
  rw [boundaryState_parents]
  unfold boundarySourceIntegralNormSqSumBound
  simp only [List.map_append]
  rw [gaussianNormSqSum_append, gaussianNormSqSum_append,
    gaussianNormSqSum_append]
  exact add_le_add
    (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
      curve source 0 data.forwardChecked)
    (add_le_add
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
        curve source 0 data.rightBoundaryChecked)
      (add_le_add
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
          curve source 1 data.backwardChecked)
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralNormSqSum_le
          curve source 1 data.leftBoundaryChecked)))

/-- Source-differential allowance of the four-bank finite-cut state is
bounded by its compact path geometry. -/
theorem boundaryState_sourceAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (((boundaryState curve source data).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      boundarySourceAggregateBound source data := by
  rw [boundaryState_parents]
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
    boundarySourceAggregateBound boundarySourceParentCount
    boundarySourceTotalWeightedBound
  simp only [List.map_append, List.length_append, List.length_map]
  rw [CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.forwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 0 data.rightBoundaryChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.backwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
      curve source 1 data.leftBoundaryChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.forwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 0 data.rightBoundaryChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.backwardChecked,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
      curve source 1 data.leftBoundaryChecked,
    totalWeightedAllowance_append, totalWeightedAllowance_append,
    totalWeightedAllowance_append]
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
        curve source 0 data.forwardChecked)
      (add_le_add
        (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
          curve source 0 data.rightBoundaryChecked)
        (add_le_add
          (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
            curve source 1 data.backwardChecked)
          (CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_totalWeightedAllowance_le
            curve source 1 data.leftBoundaryChecked)))
  · exact SwitchedPathChain.coordinateNatCast_nonnegative _

@[simp] theorem boundaryState_switchCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).chain.switchCount = 2 := by
  unfold boundaryState
  simp only [SwitchedPathChain.switchCount_append,
    SwitchedPathChain.switchCount_ofCenteredPathChain]
  rfl

/-- Number of nonstationary centred parents retained by either prepared-cycle
constructor.  The two stationary switches are deliberately excluded. -/
def preparedCycleParentCount {genus : Nat}
    {curve : HyperellipticCurve genus} :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve -> Nat
  | .bridge data => data.forward.stepCount + data.backward.stepCount
  | .finiteCut data =>
      data.forward.stepCount + data.rightBoundary.stepCount +
        data.backward.stepCount + data.leftBoundary.stepCount

@[simp] theorem bridgeState_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedDoublePath curve) :
    (bridgeState curve source data).parents.length =
      data.forward.stepCount + data.backward.stepCount := by
  unfold bridgeState
  simp only [List.length_append, List.length_nil, Nat.add_zero, Nat.zero_add,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length,
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath.forward,
    CCL.Riemann.PreparedCycleModels.PreparedDoublePath.backward]
  rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked]

@[simp] theorem boundaryState_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath curve) :
    (boundaryState curve source data).parents.length =
      data.forward.stepCount + data.rightBoundary.stepCount +
        data.backward.stepCount + data.leftBoundary.stepCount := by
  unfold boundaryState
  simp only [List.length_append, List.length_nil, Nat.add_zero, Nat.zero_add,
    CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length,
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.forward,
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary,
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.backward,
    CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary]
  rw [CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.forwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.rightBoundaryChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.backwardChecked,
    CCL.Riemann.PreparedClearPathModels.PreparedPath.DyadicBank.prepared_stepCount
      data.leftBoundaryChecked]
  omega0

/-- Exact switched state for either prepared cycle constructor. -/
def cycleState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve ->
      DirectSwitchedState curve source
  | .bridge data => bridgeState curve source data
  | .finiteCut data => boundaryState curve source data

def cycleSourceParentCount {genus : Nat}
    {curve : HyperellipticCurve genus} :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve -> Nat
  | .bridge data => bridgeSourceParentCount data
  | .finiteCut data => boundarySourceParentCount data

def cycleSourceIntegralNormSqSumBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve -> Coordinate
  | .bridge data => bridgeSourceIntegralNormSqSumBound source data
  | .finiteCut data => boundarySourceIntegralNormSqSumBound source data

@[simp] theorem cycleState_parents_length {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).parents.length =
      cycleSourceParentCount data := by
  cases data with
  | bridge bridge =>
      unfold cycleState cycleSourceParentCount bridgeSourceParentCount
      rw [bridgeState_parents, List.length_append,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 bridge.forwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 bridge.backwardChecked]
  | finiteCut boundary =>
      unfold cycleState cycleSourceParentCount boundarySourceParentCount
      rw [boundaryState_parents, List.length_append, List.length_append,
        List.length_append,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 boundary.forwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 0 boundary.rightBoundaryChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 boundary.backwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_parents_length
          curve source 1 boundary.leftBoundaryChecked]

theorem cycleState_sourceIntegralNormSqSum_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    RFAP.ConstructiveFiniteNorm.gaussianNormSqSum
        ((cycleState curve source data).parents.map
          fun parent => parent.model.integralSample) <=
      cycleSourceIntegralNormSqSumBound source data := by
  cases data with
  | bridge bridge =>
      exact bridgeState_sourceIntegralNormSqSum_le curve source bridge
  | finiteCut boundary =>
      exact boundaryState_sourceIntegralNormSqSum_le curve source boundary

theorem cycleSourceIntegralNormSqSumBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceIntegralNormSqSumBound source data :=
  (gaussianNormSqSum_nonnegative
    ((cycleState curve source data).parents.map
      fun parent => parent.model.integralSample)).trans
        (cycleState_sourceIntegralNormSqSum_le curve source data)

theorem cycleState_recastParents_self {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source) =
      (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [cycleState, bridgeState_parents, List.map_append]
      rw [CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 bridge.forwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 bridge.backwardChecked]
  | finiteCut boundary =>
      simp only [cycleState, boundaryState_parents, List.map_append]
      rw [CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 boundary.forwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 0 boundary.rightBoundaryChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 boundary.backwardChecked,
        CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_recast_self
          curve source 1 boundary.leftBoundaryChecked]

/-- The centre-free endpoint exposed by prepared-cycle data is exactly the
lower fold over the initial direct-refinement parents.  In particular, this
identity does not construct any successor refinement state. -/
theorem cycleState_integralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    data.integralRealLower source =
      CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower
        (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [CCL.Riemann.PreparedCycleModels.PreparedCycleData.integralRealLower,
        cycleState]
      unfold CCL.Riemann.PreparedCycleModels.PreparedDoublePath.integralRealLower
        CCL.Riemann.PreparedCycleModels.PreparedDoublePath.forward
        CCL.Riemann.PreparedCycleModels.PreparedDoublePath.backward
      rw [bridgeState_parents,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_append,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 bridge.forwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 bridge.backwardChecked]
      rfl
  | finiteCut boundary =>
      simp only [CCL.Riemann.PreparedCycleModels.PreparedCycleData.integralRealLower,
        cycleState]
      unfold CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.integralRealLower
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.forward
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.backward
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary
      rw [boundaryState_parents,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_append,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_append,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesIntegralRealLower_append,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 boundary.forwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 0 boundary.rightBoundaryChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 boundary.backwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_integralRealLower
          curve source 1 boundary.leftBoundaryChecked]
      rfl

/-- The prepared-cycle directional endpoint is exactly the same fold over
the initial direct-refinement parents. -/
theorem cycleState_directionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (direction : Gaussian)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    data.directionalIntegralLower source direction =
      CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower
        direction (cycleState curve source data).parents := by
  cases data with
  | bridge bridge =>
      simp only [
        CCL.Riemann.PreparedCycleModels.PreparedCycleData.directionalIntegralLower,
        cycleState]
      unfold
        CCL.Riemann.PreparedCycleModels.PreparedDoublePath.directionalIntegralLower
        CCL.Riemann.PreparedCycleModels.PreparedDoublePath.forward
        CCL.Riemann.PreparedCycleModels.PreparedDoublePath.backward
      rw [bridgeState_parents,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_append,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction bridge.forwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction bridge.backwardChecked]
  | finiteCut boundary =>
      simp only [
        CCL.Riemann.PreparedCycleModels.PreparedCycleData.directionalIntegralLower,
        cycleState]
      unfold
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.directionalIntegralLower
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.forward
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.rightBoundary
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.backward
        CCL.Riemann.PreparedCycleModels.PreparedBoundaryDoublePath.leftBoundary
      rw [boundaryState_parents,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_append,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_append,
        CCL.Riemann.PreparedSubdivisionModels.centeredEdgesDirectionalIntegralLower_append,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction boundary.forwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 0 direction boundary.rightBoundaryChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction boundary.backwardChecked,
        ← CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank_directionalIntegralLower
          curve source 1 direction boundary.leftBoundaryChecked]
/-- Compact squared norm bound for the complete initial source-period sample,
obtained from the displayed finite parent count and additive cell bounds. -/
def cycleSourceInitialSampleNormSqBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourceParentCount data : Coordinate) *
    cycleSourceIntegralNormSqSumBound source data

theorem cycleSourceInitialSampleNormSqBound_nonnegative {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceInitialSampleNormSqBound source data := by
  unfold cycleSourceInitialSampleNormSqBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (SwitchedPathChain.coordinateNatCast_nonnegative _)
    (cycleSourceIntegralNormSqSumBound_nonnegative source data)

theorem cycleState_sourceInitialSample_normSq_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((CCL.ProgressiveGaussianIntegration.PathModel.mk
          ((cycleState curve source data).parents.map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).integralSample) <=
      cycleSourceInitialSampleNormSqBound source data := by
  let samples := (cycleState curve source data).parents.map
    fun parent => parent.model.integralSample
  rw [pathModel_integralSample_eq_gaussianSum]
  rw [centeredEdgeIntegralSamples_map_model]
  have finiteCauchy :=
    RFAP.ConstructiveFiniteNorm.normSq_gaussianSum_le samples
  have additiveBound := cycleState_sourceIntegralNormSqSum_le curve source data
  unfold cycleSourceInitialSampleNormSqBound
  change
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteNorm.gaussianSum samples) <= _
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.ConstructiveFiniteNorm.gaussianSum samples) <=
      (samples.length : Coordinate) *
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum samples := finiteCauchy
    _ = (cycleSourceParentCount data : Coordinate) *
        RFAP.ConstructiveFiniteNorm.gaussianNormSqSum samples := by
      unfold samples
      rw [List.length_map, cycleState_parents_length]
    _ <= (cycleSourceParentCount data : Coordinate) *
        cycleSourceIntegralNormSqSumBound source data :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct additiveBound
        (SwitchedPathChain.coordinateNatCast_nonnegative _)

def cycleSourceAggregateBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve -> Coordinate
  | .bridge data => bridgeSourceAggregateBound source data
  | .finiteCut data => boundarySourceAggregateBound source data

/-- Paired cycle preflight summary.  The common bank diameter already bounds
every accepted root box, so this value folds only the original clear paths
and never traverses their retained dyadic leaves. -/
structure CycleSourcePreflightBounds where
  aggregateBound : Coordinate
  initialSampleNormSqBound : Coordinate

namespace CycleSourcePreflightBounds

def scheduleBase (bounds : CycleSourcePreflightBounds) : Coordinate :=
  bounds.aggregateBound + DirectSwitchedState.scheduleSlack

def errorScale (bounds : CycleSourcePreflightBounds) : Coordinate :=
  3 * (4 * (3 * bounds.scheduleBase))

def centerBound (bounds : CycleSourcePreflightBounds) : Coordinate :=
  2 * (bounds.initialSampleNormSqBound + bounds.errorScale)

end CycleSourcePreflightBounds

/-- Fully materialized compact preflight data.  Constructing this record once
keeps all five downstream projections on one shared evaluation path. -/
structure CycleSourcePreflightSummary where
  aggregateBound : Coordinate
  initialSampleNormSqBound : Coordinate
  scheduleBase : Coordinate
  errorScale : Coordinate
  centerBound : Coordinate

namespace CycleSourcePreflightBounds

def summary (bounds : CycleSourcePreflightBounds) :
    CycleSourcePreflightSummary :=
  let scheduleBase := bounds.scheduleBase
  let errorScale := 3 * (4 * (3 * scheduleBase))
  { aggregateBound := bounds.aggregateBound
    initialSampleNormSqBound := bounds.initialSampleNormSqBound
    scheduleBase := scheduleBase
    errorScale := errorScale
    centerBound :=
      2 * (bounds.initialSampleNormSqBound + errorScale) }

@[simp] theorem summary_aggregateBound (bounds : CycleSourcePreflightBounds) :
    bounds.summary.aggregateBound = bounds.aggregateBound := rfl

@[simp] theorem summary_initialSampleNormSqBound
    (bounds : CycleSourcePreflightBounds) :
    bounds.summary.initialSampleNormSqBound =
      bounds.initialSampleNormSqBound := rfl

@[simp] theorem summary_scheduleBase (bounds : CycleSourcePreflightBounds) :
    bounds.summary.scheduleBase = bounds.scheduleBase := rfl

@[simp] theorem summary_errorScale (bounds : CycleSourcePreflightBounds) :
    bounds.summary.errorScale = bounds.errorScale := rfl

@[simp] theorem summary_centerBound (bounds : CycleSourcePreflightBounds) :
    bounds.summary.centerBound = bounds.centerBound := rfl

end CycleSourcePreflightBounds

def cycleSourcePreflightBounds {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus) :
    CCL.Riemann.PreparedCycleModels.PreparedCycleData curve ->
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

theorem cycleSourceAggregateBound_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceAggregateBound source data <=
      (cycleSourcePreflightBounds source data).aggregateBound := by
  cases data with
  | bridge bridge =>
      exact bridgeSourceAggregateBound_le_preflight source bridge
  | finiteCut boundary =>
      exact boundarySourceAggregateBound_le_preflight source boundary

theorem cycleSourceInitialSampleNormSqBound_le_preflight
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceInitialSampleNormSqBound source data <=
      (cycleSourcePreflightBounds source data).initialSampleNormSqBound := by
  cases data <;> exact le_rfl

theorem cycleState_sourceAllowance_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (((cycleState curve source data).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model)).aggregateAllowance <=
      cycleSourceAggregateBound source data := by
  cases data with
  | bridge bridge =>
      exact bridgeState_sourceAllowance_le curve source bridge
  | finiteCut boundary =>
      exact boundaryState_sourceAllowance_le curve source boundary

theorem cycleSourceAggregateBound_nonnegative {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceAggregateBound source data :=
  (CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance_nonneg
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (((cycleState curve source data).parents.map
        (CCL.Riemann.PreparedDirectDyadicRefinements.recastCenteredEdge
          source)).map
            CCL.Riemann.PreparedSubdivisionModels.CenteredEdge.model))).trans
      (cycleState_sourceAllowance_le curve source data)

/-- Cycle state whose source channel uses the compact cached-root bank bound.
This retains the sharp root-box information while evaluating differential
coefficients only once per original clear segment. -/
def compactCycleState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    DirectSwitchedState curve source := by
  let state := cycleState curve source data
  exact state.withSourceAllowanceBound
    (cycleSourceAggregateBound source data)
    (cycleState_sourceAllowance_le curve source data)

@[simp] theorem compactCycleState_parents {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).parents =
      (cycleState curve source data).parents := rfl

/-- The compact cycle state's initial source sample is bounded without
constructing any persisted coefficient centre. -/
theorem compactCycleState_sourceFlatInitialSample_normSq_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((compactCycleState curve source data).flatModel [source] source
          0).integralSample <=
      cycleSourceInitialSampleNormSqBound source data := by
  unfold DirectSwitchedState.flatModel DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data]
  exact cycleState_sourceInitialSample_normSq_le curve source data

/-- The same compact bound applies to the switched initial source model,
because its stationary sheet-switch cells integrate to zero. -/
theorem compactCycleState_sourceInitialSample_normSq_le {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (member : source ∈ [source]) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((((compactCycleState curve source data).integral [source] source
          member).model 0).integralSample) <=
      cycleSourceInitialSampleNormSqBound source data := by
  change RFAP.ConstructiveGaussian.Gaussian.normSq
      (((compactCycleState curve source data).refinementStates [source] 0).model
        source).integralSample <= _
  rw [(compactCycleState curve source data).model_integralSample_eq_flatModel
    [source] source 0]
  exact compactCycleState_sourceFlatInitialSample_normSq_le curve source data

@[simp] theorem cycleState_switchCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (cycleState curve source data).chain.switchCount = 2 := by
  cases data <;> simp only [cycleState, bridgeState_switchCount,
    boundaryState_switchCount]

@[simp] theorem compactCycleState_switchCount {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).chain.switchCount = 2 := by
  unfold compactCycleState DirectSwitchedState.withSourceAllowanceBound
  exact cycleState_switchCount curve source data

/-- Compact singleton-source schedule base, stated independently of the
full switched refinement record so executable preflight need not construct
its coefficient centres. -/
def cycleSourceExactScheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  cycleSourceAggregateBound source data + DirectSwitchedState.scheduleSlack

def cycleSourceExactErrorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  3 * (4 * (3 * cycleSourceExactScheduleBase source data))

def cycleSourceScheduleBase {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).scheduleBase

/-- Exact error scale used by the singleton-source switched period program. -/
def cycleSourceErrorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).errorScale

/-- Compact all-sample bound derived from the compact initial sample and the
exact finite telescoping scale. -/
def cycleSourceCenterBound {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Coordinate :=
  (cycleSourcePreflightBounds source data).centerBound

theorem cycleSourceScheduleBase_positive {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
  (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 < cycleSourceScheduleBase source data := by
  unfold cycleSourceScheduleBase CycleSourcePreflightBounds.scheduleBase
  exact add_pos_of_nonneg_of_pos
    ((cycleSourceAggregateBound_nonnegative curve source data).trans
      (cycleSourceAggregateBound_le_preflight source data))
    DirectSwitchedState.scheduleSlack_positive

theorem cycleSourceExactScheduleBase_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceExactScheduleBase source data <=
      cycleSourceScheduleBase source data := by
  unfold cycleSourceExactScheduleBase cycleSourceScheduleBase
    CycleSourcePreflightBounds.scheduleBase
  exact RFAP.ConstructiveFraction.add_le_add_right_direct
    (cycleSourceAggregateBound_le_preflight source data)
    DirectSwitchedState.scheduleSlack

theorem cycleSourceExactErrorScale_le_preflight {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    cycleSourceExactErrorScale source data <=
      cycleSourceErrorScale source data := by
  unfold cycleSourceExactErrorScale cycleSourceErrorScale
    CycleSourcePreflightBounds.errorScale
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (cycleSourceExactScheduleBase_le_preflight source data) (by decide))
      (by decide))
    (by decide)

private theorem quarterRadius_scale_mono {small large : Coordinate}
    (order : small <= large) (index : Nat) :
    CCL.FiniteGeometric.quarterRadius small index <=
      CCL.FiniteGeometric.quarterRadius large index := by
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct order
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index)

theorem cycleSourceErrorScale_nonnegative {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
  (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceErrorScale source data := by
  unfold cycleSourceErrorScale CycleSourcePreflightBounds.errorScale
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (cycleSourceScheduleBase_positive curve source data).le))

theorem cycleSourceCenterBound_nonnegative {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
  (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    0 <= cycleSourceCenterBound source data := by
  unfold cycleSourceCenterBound CycleSourcePreflightBounds.centerBound
  exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      ((cycleSourceInitialSampleNormSqBound_nonnegative source data).trans
        (cycleSourceInitialSampleNormSqBound_le_preflight source data))
      (cycleSourceErrorScale_nonnegative curve source data))

@[simp] theorem compactCycleState_initialAllowanceBound_source {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).initialAllowanceBound source =
      cycleSourceAggregateBound source data := by
  unfold compactCycleState DirectSwitchedState.withSourceAllowanceBound
  simp only [if_pos]

theorem compactCycleState_scheduleBase_singleton {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    (compactCycleState curve source data).scheduleBase [source] =
      cycleSourceExactScheduleBase source data := by
  unfold DirectSwitchedState.scheduleBase
    DirectSwitchedState.initialAllowanceBoundSum cycleSourceExactScheduleBase
  simp only [DirectSwitchedState.initialAllowanceBoundSum]
  rw [compactCycleState_initialAllowanceBound_source]
  ring1

theorem compactCycleState_sourceIntegral_errorScale {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (member : source ∈ [source]) :
    (((compactCycleState curve source data).integral [source] source
      member).errorScale) = cycleSourceExactErrorScale source data := by
  unfold DirectSwitchedState.integral
  simp only [CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.toRefinementProgram,
    CCL.ProgressiveGaussianIntegration.SequentialCompatibleConstantRefinementProgram.errorScale,
    DirectSwitchedState.flatSequentialProgram,
    SwitchedPathChain.switchFactor, compactCycleState_switchCount,
    Nat.cast_ofNat]
  rw [compactCycleState_scheduleBase_singleton]
  rfl

/-- Call-by-need cache for the complete centred state of one compact source
program.  The runtime forces this thunk on the first model request and reuses
the same state for every later refinement index. -/
def compactSourceState {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    Thunk (DirectSwitchedState curve source) :=
  ⟨fun _ => compactCycleState curve source data⟩

/-- Delayed compact source model.  Keeping both the cached state and the
refinement index explicit prevents compiled preflight clients from eagerly
materializing the complete centred cycle merely to close over its model
function. -/
def compactSourceModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    (state : Thunk (DirectSwitchedState curve source))
    (index : Nat) : CCL.ProgressiveGaussianIntegration.PathModel :=
  ((state.get.refinementStates [source] index).model source)

/-- Literal finite lower certificate for one compact singleton-source model.
The certificate itself names the exact flattened parent list, while this
alias keeps that dependent implementation detail out of downstream explicit
example signatures. -/
abbrev CompactSourcePositiveLiteralRealLowerCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) :=
  DirectSwitchedState.FlatPositiveLiteralRealLowerCertificate
    (compactCycleState curve source data) [source] source index

/-- A verified literal certificate bounds the displayed compact source model
at the identical finite refinement index. -/
theorem CompactSourcePositiveLiteralRealLowerCertificate.lower_le_model
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {index : Nat}
    (certificate : CompactSourcePositiveLiteralRealLowerCertificate
      curve source data index) :
    certificate.lower <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re :=
  DirectSwitchedState.FlatPositiveLiteralRealLowerCertificate.lower_le_model
    certificate

/-- Executable sign-aware lower endpoint for the real part of one compact
source model.  Its definition reads the same finite refinement state as the
model, so retained clients can cache both behind one source-state thunk. -/
def compactSourceIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelIntegralRealLower
    [source] source index

/-- Sharp real endpoint for a compact source model, using the coefficient
process balls already retained by its refinement state. -/
def compactSourceBallIntegralRealLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelBallIntegralRealLower
    [source] source index

/-- At index zero, the compact executable lower is definitionally the named
prepared-cycle endpoint.  This is the static theorem-facing anchor used by
explicit period certificates. -/
theorem compactSourceIntegralRealLower_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    compactSourceIntegralRealLower curve source data 0 =
      data.integralRealLower source := by
  unfold compactSourceIntegralRealLower
    DirectSwitchedState.flatModelIntegralRealLower
    DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data,
    ← cycleState_integralRealLower curve source data]

/-- The compact source lower endpoint bounds the real part of the exact
finite model sample at the same refinement index. -/
theorem compactSourceIntegralRealLower_le_model {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) (exponentZero : source.exponent = 0) :
    compactSourceIntegralRealLower curve source data index <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re := by
  exact (compactCycleState curve source data).flatModelIntegralRealLower_le_model
    [source] source index exponentZero

/-- The sharp process-ball endpoint bounds the same compact source model. -/
theorem compactSourceBallIntegralRealLower_le_model {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) (exponentZero : source.exponent = 0) :
    compactSourceBallIntegralRealLower curve source data index <=
      (compactSourceModel (compactSourceState curve source data)
        index).integralSample.re := by
  exact
    (compactCycleState curve source data).flatModelBallIntegralRealLower_le_model
      [source] source index exponentZero

/-- Static prepared-cycle certificate for compact model zero.  Clients can
prove positivity from the named prepared endpoint and obtain a model bound
without reducing the compact state or any successor refinement. -/
theorem preparedCycleIntegralRealLower_le_compactSourceModel_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (exponentZero : source.exponent = 0) :
    data.integralRealLower source <=
      (compactSourceModel (compactSourceState curve source data)
        0).integralSample.re := by
  rw [← compactSourceIntegralRealLower_zero curve source data]
  exact compactSourceIntegralRealLower_le_model curve source data 0
    exponentZero

/-- Executable directional endpoint read from the same retained refinement
state as the compact source model. -/
def compactSourceDirectionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelDirectionalIntegralLower
    [source] source direction index

/-- Sharp arbitrary-direction endpoint for one compact source model. -/
def compactSourceBallDirectionalIntegralLower {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  (compactCycleState curve source data).flatModelBallDirectionalIntegralLower
    [source] source direction index

/-- At model zero the compact directional endpoint is exactly the named
prepared-cycle endpoint, with no successor refinement constructed. -/
theorem compactSourceDirectionalIntegralLower_zero {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (direction : Gaussian) :
    compactSourceDirectionalIntegralLower curve source data direction 0 =
      data.directionalIntegralLower source direction := by
  unfold compactSourceDirectionalIntegralLower
    DirectSwitchedState.flatModelDirectionalIntegralLower
    DirectSwitchedState.refinementStates
  rw [compactCycleState_parents,
    cycleState_recastParents_self curve source data,
    ← cycleState_directionalIntegralLower curve source direction data]

/-- The compact directional endpoint bounds the same projection of the exact
finite source model at every refinement index. -/
theorem compactSourceDirectionalIntegralLower_le_model {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
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

theorem compactSourceBallDirectionalIntegralLower_le_model {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
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

/-- Static prepared-cycle directional certificate for compact model zero. -/
theorem preparedCycleDirectionalIntegralLower_le_compactSourceModel_zero
    {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
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

/-- A caller-bounded cache for one compact source program.  The initial
centred state and every refinement thunk belong to this retained value, so a
client can extend the finite prefix without allocating a second prepared
cycle. -/
structure CompactSourceCache {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) where
  initial : Thunk (DirectSwitchedState curve source)
  initial_eq : initial.get = compactCycleState curve source data
  refinements :
    DirectSwitchedState.BoundedRefinementCache initial [source] count

namespace CompactSourceCache

/-- Allocate a finite lazy prefix.  Constructing the cache itself does not
force the prepared cycle or any successor state. -/
def canonical {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) : CompactSourceCache curve source data count :=
  let initial := compactSourceState curve source data
  { initial := initial
    initial_eq := rfl
    refinements :=
      DirectSwitchedState.BoundedRefinementCache.canonical initial [source]
        count }

/-- Add a caller-selected finite number of lazy states while retaining the
entire earlier prefix verbatim. -/
def extend {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (extra : Nat) : CompactSourceCache curve source data (count + extra) where
  initial := cache.initial
  initial_eq := cache.initial_eq
  refinements := cache.refinements.extend extra

/-- Read through the bounded prefix when possible and through the same
retained initial-state thunk otherwise. -/
def model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : CCL.ProgressiveGaussianIntegration.PathModel :=
  if within : index < count then
    ((cache.refinements.get index within).get.model source)
  else compactSourceModel cache.initial index

/-- Read the sign-aware real lower endpoint through the same retained state
thunk as `model`.  A cached state already represents the requested direct
index, so its local lower endpoint is read at refinement zero. -/
def integralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelIntegralRealLower
      [source] source 0
  else cache.initial.get.flatModelIntegralRealLower [source] source index

/-- Read the sharp process-ball real endpoint through the same retained state
thunk as `model`. -/
def ballIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelBallIntegralRealLower
      [source] source 0
  else cache.initial.get.flatModelBallIntegralRealLower [source] source index

/-- Read an arbitrary rational projection endpoint through the same retained
state thunk as `model`. -/
def directionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelDirectionalIntegralLower
      [source] source direction 0
  else
    cache.initial.get.flatModelDirectionalIntegralLower
      [source] source direction index

/-- Read a sharp arbitrary-direction endpoint through the retained state
cache. -/
def ballDirectionalIntegralLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (direction : Gaussian) (index : Nat) : Coordinate :=
  if within : index < count then
    (cache.refinements.get index within).get.flatModelBallDirectionalIntegralLower
      [source] source direction 0
  else
    cache.initial.get.flatModelBallDirectionalIntegralLower
      [source] source direction index

/-- Cached models are exactly the canonical compact source models. -/
theorem model_eq_compactSourceModel {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

/-- Cached and canonical lower endpoints are the same exact finite rational.
This is a specification theorem for runtime sharing, not a recomputation
request for downstream clients. -/
theorem integralRealLower_eq_compactSourceIntegralRealLower {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

/-- Cached and canonical sharp real endpoints are the same finite rational. -/
theorem ballIntegralRealLower_eq_compactSourceBallIntegralRealLower
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

/-- Cached and canonical directional endpoints are the same exact finite
rational, while the cached form shares the retained refinement state. -/
theorem directionalIntegralLower_eq_compactSourceDirectionalIntegralLower
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

theorem ballDirectionalIntegralLower_eq_compactSourceBallDirectionalIntegralLower
    {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

/-- The cached lower endpoint bounds the cached model at the same direct
refinement index. -/
theorem integralRealLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) (exponentZero : source.exponent = 0) :
    cache.integralRealLower index <= (cache.model index).integralSample.re := by
  rw [cache.integralRealLower_eq_compactSourceIntegralRealLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceIntegralRealLower_le_model curve source data index
    exponentZero

theorem ballIntegralRealLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (index : Nat) (exponentZero : source.exponent = 0) :
    cache.ballIntegralRealLower index <= (cache.model index).integralSample.re := by
  rw [cache.ballIntegralRealLower_eq_compactSourceBallIntegralRealLower,
    cache.model_eq_compactSourceModel]
  exact compactSourceBallIntegralRealLower_le_model curve source data index
    exponentZero

/-- The cached directional endpoint bounds the matching projection of the
cached model at the same direct refinement index. -/
theorem directionalIntegralLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

theorem ballDirectionalIntegralLower_le_model {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
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

/-- Extending a cache leaves every already bounded model backed by the same
stored thunk. -/
theorem extend_model_of_lt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {source : Differential genus}
    {data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve}
    {count : Nat} (cache : CompactSourceCache curve source data count)
    (extra index : Nat) (within : index < count) :
    (cache.extend extra).model index = cache.model index := by
  have extendedWithin : index < count + extra :=
    within.trans_le (Nat.le_add_right count extra)
  simp only [model, extend, dif_pos extendedWithin, dif_pos within]
  rw [cache.refinements.extend_get index within extra]

end CompactSourceCache

/-- Singleton-source refinement program with the original switched models and
Cauchy theorem, but compact preflight scalars.  Its executable construction
does not evaluate an initial coefficient centre. -/
def compactSourceIntegral {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram := by
  let member : source ∈ [source] := by
    simp only [List.mem_cons]
    exact Or.inl trivial
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
        change _ <= CCL.FiniteGeometric.quarterRadius
          (cycleSourceErrorScale source data) index
        calc
          _ <= CCL.FiniteGeometric.quarterRadius original.errorScale index :=
            original.modelAllowance_le index
          _ = CCL.FiniteGeometric.quarterRadius
              (cycleSourceExactErrorScale source data) index := by
            rw [compactCycleState_sourceIntegral_errorScale curve source data
              member]
          _ <= CCL.FiniteGeometric.quarterRadius
              (cycleSourceErrorScale source data) index :=
            quarterRadius_scale_mono
              (cycleSourceExactErrorScale_le_preflight source data) index
      later_close := by
        intro earlier later order
        change _ <= CCL.FiniteGeometric.quarterRadius
          (cycleSourceErrorScale source data) earlier
        calc
          _ <= CCL.FiniteGeometric.quarterRadius original.errorScale earlier :=
            original.later_close order
          _ = CCL.FiniteGeometric.quarterRadius
              (cycleSourceExactErrorScale source data) earlier := by
            rw [compactCycleState_sourceIntegral_errorScale curve source data
              member]
          _ <= CCL.FiniteGeometric.quarterRadius
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
        let current :=
          (((compactCycleState curve source data).refinementStates [source]
            index).model source).integralSample
        let initial :=
          (((compactCycleState curve source data).refinementStates [source]
            0).model source).integralSample
        have movement :
            RFAP.ConstructiveGaussian.Gaussian.normSq
                (current - initial) <= cycleSourceErrorScale source data := by
          calc
            RFAP.ConstructiveGaussian.Gaussian.normSq
                (current - initial) <=
              CCL.FiniteGeometric.quarterRadius original.errorScale 0 :=
                original.later_close (Nat.zero_le index)
            _ = CCL.FiniteGeometric.quarterRadius
                (cycleSourceExactErrorScale source data) 0 := by
              rw [compactCycleState_sourceIntegral_errorScale curve source data
                member]
            _ <= CCL.FiniteGeometric.quarterRadius
                (cycleSourceErrorScale source data) 0 :=
              quarterRadius_scale_mono
                (cycleSourceExactErrorScale_le_preflight source data) 0
            _ <= cycleSourceErrorScale source data :=
              CCL.FiniteGeometric.quarterRadius_le_scale
                (cycleSourceErrorScale_nonnegative curve source data) 0
        have initialBound :
            RFAP.ConstructiveGaussian.Gaussian.normSq initial <=
              cycleSourceInitialSampleNormSqBound source data :=
          compactCycleState_sourceInitialSample_normSq_le curve source data
            member
        have initialPreflightBound :
            RFAP.ConstructiveGaussian.Gaussian.normSq initial <=
              preflight.initialSampleNormSqBound :=
          initialBound.trans
            (cycleSourceInitialSampleNormSqBound_le_preflight source data)
        have identity : (current - initial) + initial = current := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
        change RFAP.ConstructiveGaussian.Gaussian.normSq current <= _
        rw [← identity]
        calc
          RFAP.ConstructiveGaussian.Gaussian.normSq
              ((current - initial) + initial) <=
            2 * (RFAP.ConstructiveGaussian.Gaussian.normSq
                  (current - initial) +
                RFAP.ConstructiveGaussian.Gaussian.normSq initial) :=
              RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
          _ <= 2 * (cycleSourceErrorScale source data +
                preflight.initialSampleNormSqBound) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add movement initialPreflightBound) (by decide)
          _ = preflight.centerBound := by
            dsimp only [preflight, preflightCore,
              CycleSourcePreflightBounds.summary]
            unfold cycleSourceErrorScale CycleSourcePreflightBounds.errorScale
            ring1 }

@[simp] theorem compactSourceIntegral_model {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (index : Nat) :
    (compactSourceIntegral curve source data).model index =
      compactSourceModel (compactSourceState curve source data) index := rfl

/-- The compact refinement program read through one retained caller-bounded
state cache.  All analytic fields are transported from the canonical program
by pointwise model equality. -/
def compactSourceIntegralOfCache {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    {count : Nat} (cache : CompactSourceCache curve source data count) :
    CCL.ProgressiveGaussianIntegration.RefinementProgram :=
  (compactSourceIntegral curve source data).withEquivalentModels cache.model
    (by
      intro index
      rw [cache.model_eq_compactSourceModel, compactSourceIntegral_model])

/-- Convenience constructor for a fresh bounded compact source program.
Clients which retry in chunks should retain and extend `CompactSourceCache`
directly instead. -/
def boundedCompactSourceIntegral {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (count : Nat) : CCL.ProgressiveGaussianIntegration.RefinementProgram :=
  compactSourceIntegralOfCache curve source data
    (CompactSourceCache.canonical curve source data count)
/-- The exact mapped allowance accumulator of a prepared cycle decomposes
bankwise before any large concatenated parent list is materialized. -/
theorem cycleState_tailMappedWeightedAllowance {genus : Nat}
    {curve : HyperellipticCurve genus}
    (source : Differential genus)
    (model : CenteredEdge curve source ->
      CCL.ProgressiveGaussianIntegration.CellModel) :
    forall (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve),
    CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
        (cycleState curve source data).parents model =
      match data with
      | .bridge bridge =>
          let forward :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 bridge.forwardChecked
          let backward :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 bridge.backwardChecked
          CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
              forward.parents model +
            CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
              backward.parents model
      | .finiteCut boundary =>
          let forward :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.forwardChecked
          let rightBoundary :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 0 boundary.rightBoundaryChecked
          let backward :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.backwardChecked
          let leftBoundary :=
            CCL.Riemann.PreparedDirectDyadicRefinements.CenteredPathChain.ofDyadicBank
              curve source 1 boundary.leftBoundaryChecked
          CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
              forward.parents model +
            CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
                rightBoundary.parents model +
              CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
                  backward.parents model +
                CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance
                  leftBoundary.parents model
  | .bridge bridge => by
      unfold cycleState bridgeState
      simp only [List.nil_append, List.append_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance_append]
  | .finiteCut boundary => by
      unfold cycleState boundaryState
      simp only [List.nil_append, List.append_nil,
        CCL.ProgressiveGaussianIntegration.PathModel.tailMappedWeightedAllowance_append]
      ring1

/-- Total closed switched schedule extracted from either prepared cycle
geometry and one displayed finite differential family. -/
def scheduleOfPreparedCycleData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (targets : List (Differential genus))
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve) :
    FiniteDifferentialSwitchedClosedSchedule curve source where
  initial := compactCycleState curve source data
  targets := targets
  closed := by cases data <;> rfl

/-- Both standard prepared-cycle constructors retain their two exact sheet
transitions, so every generated finite integration model is nonempty. -/
theorem scheduleOfPreparedCycleData_integral_model_cells_positive {genus : Nat}
    (curve : HyperellipticCurve genus)
    (source : Differential genus)
    (targets : List (Differential genus))
    (data : CCL.Riemann.PreparedCycleModels.PreparedCycleData curve)
    (differential : Differential genus)
    (member : differential ∈ targets)
    (index : Nat) :
    0 < (((scheduleOfPreparedCycleData curve source targets data).integral
      differential member).model index).cells.length := by
  apply
    FiniteDifferentialSwitchedClosedSchedule.integral_model_cells_positive
  change 0 < (compactCycleState curve source data).chain.switchCount
  rw [compactCycleState_switchCount]
  decide

end CCL.Riemann.PreparedSwitchedRefinements
