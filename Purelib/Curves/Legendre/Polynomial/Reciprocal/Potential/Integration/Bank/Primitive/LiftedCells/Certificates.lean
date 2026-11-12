module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells.Path
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Parents
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Lifted
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Endpoints
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial

/-! # Original centered-model certificates on the actual cached lifted path

The whole lifted-cell factory identity identifies each retained cell with
the same original parent's clear segment and sheet. The resulting path
agrees with the original centered chain. Existing uniform certificates are
then transported to the supplied already-assembled path, without preparing
parents, acquiring Points or rebuilding the lifted-cell cache or path.

The certified models remain the original centered parents' models for the
reversed differential. This does not certify the new sampled Head
integrands or attach the path to a canonical homology cycle.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath LiftedCell)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
  (CenteredPathChain castUniformPathCertificatesPath)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The complete factory equation identifies the actual cached head cell with its original transported cell. -/
private theorem head_heq
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (factory : paths = build (.cons data rest) planned) : HEq paths.2.2.1 data.liftedCell :=
  Eq.mpr (congrArg (fun value : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned =>
    HEq value.2.2.1 data.liftedCell) (factory.trans (build_cons data rest planned))) HEq.rfl

/-- A closed lifted path with no cells is the actual empty path at its retained point. -/
private theorem empty_eq {point : LiftedPoint 2} (kept : LiftedPath 2 point point)
    (zero : kept.cellCount = 0) : kept = .nil point := by
  cases kept with
  | nil => rfl
  | cons _cell _remaining => cases zero

/-- The actual cached-cell path is exactly the original centered parent's ordered geometric path.

Each head comparison preserves the complete original cell, including its
sheet bijection. The induction consumes literal cached tails. The chain is
used only to prove this equality; it supplies no replacement path data.
-/
theorem path_eq :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) →
          (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) bank planned) →
            (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
              (chain : CenteredPathChain parents (start := start) (finish := finish)) →
                path bank planned paths factory ⟨chain⟩ = chain.path := by
  intro parents bank
  induction bank with
  | nil =>
      intro planned paths factory start finish chain
      cases chain with
      | nil =>
          exact empty_eq (path .nil planned paths factory ⟨.nil start⟩)
            (path_cellCount .nil planned paths factory ⟨.nil start⟩)
  | @cons parent parents data rest ih =>
      intro planned paths factory start finish chain
      cases chain with
      | cons _ tail =>
          have head :
              paths.2.2.1.castEndpoints
                (firstPoint_eq data rest planned paths factory ⟨.cons parent tail⟩)
                (lastPoint_eq data rest planned paths factory) =
                BranchCutLifts.ClearSegment.liftOnSheet parent.edge.sheet parent.edge.localSegment :=
            eq_of_heq ((LiftedCell.castEndpoints_heq paths.2.2.1
              (firstPoint_eq data rest planned paths factory ⟨.cons parent tail⟩)
              (lastPoint_eq data rest planned paths factory)).trans
                ((head_heq data rest planned paths factory).trans data.liftedCell_heq))
          rewrite [path_cons data rest planned paths factory ⟨.cons parent tail⟩]
          exact congrArg₂ (fun cell remaining => LiftedPath.cons cell remaining) head
            (ih planned.2.2.2 paths.2.2.2.2 (tail_eq data rest planned paths factory) tail)

/-- Put the original centered parents' uniform model certificates on the same already-assembled cached path.

The computational chain is assembled from the given parent records. Its
existence proof pays only exact endpoint indices. The given path and cell
cache are preserved by their whole factory equations, while the source
models and reversed differential remain unchanged.
-/
def certificates
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor bank)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) bank planned)
    (factory : paths = build bank planned)
    {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish)))
    (keptPath : LiftedPath 2 start finish)
    (pathFactory : keptPath = path bank planned paths factory chain) :
    Basis.UniformPathCertificates (HyperellipticReciprocalCurve.reciprocalCurve (Fibre.frameCurve frame))
      (HyperellipticReciprocal.reversedDifferential sourceDifferential)
      (parents.map CenteredEdge.model) keptPath :=
  let original := CenteredPathChain.ofParents parents chain
  castUniformPathCertificatesPath
    ((path_eq bank planned paths factory original).symm.trans pathFactory.symm)
    original.certificates

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

end
