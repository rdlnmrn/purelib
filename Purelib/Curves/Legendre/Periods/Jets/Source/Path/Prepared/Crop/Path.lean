module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Models
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Endpoints
public import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Data.List.OfFn.Basic
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-! # Lifted affine subdivisions with their actual uniform integrand certificates

The finite interval walk fixes every oriented child endpoint. Each child
retains the original parent's complete sheet transport. The certificate
constructor consumes actual child model and uniform-certificate caches;
it requests no new observation or source preparation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable (parent : CenteredEdge (Fibre.frameCurve frame) basis) {intervals : List Interval}

/-- Construct the oriented lifted child chain of the exact retained interval walk. -/
def walkPath : {first last : Rational} → IncreasingWalk intervals first last →
    LiftedPath 2 ⟨parent.edge.point first, parent.edge.sheet⟩ ⟨parent.edge.point last, parent.edge.sheet⟩
  | _, _, .nil point => .nil ⟨parent.edge.point point, parent.edge.sheet⟩
  | _, _, .cons interval _ tail =>
      .cons (croppedCell (frame := frame) (parent := parent) interval.lower interval.upper) (walkPath tail)

/-- Assemble actual retained uniform child certificates on the same oriented lifted interval chain. -/
def certifyWalk (channel : Fin 6) :
    {first last : Rational} → (walk : IncreasingWalk intervals first last) →
    (cells : Fin walk.edges.length → CellModel) →
    (∀ index, (cells index).start = parent.edge.point (walk.edges[index.val]'index.isLt).lower) →
    (∀ index, (cells index).finish = parent.edge.point (walk.edges[index.val]'index.isLt).upper) →
    (∀ index, UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (croppedCell (frame := frame) (parent := parent)
        (walk.edges[index.val]'index.isLt).lower (walk.edges[index.val]'index.isLt).upper) (cells index)) →
    UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (List.ofFn cells) (walkPath parent walk)
  | _, _, .nil point, _, _, _, _ => .nil ⟨parent.edge.point point, parent.edge.sheet⟩
  | _, _, .cons interval member tail, cells, starts, finishes, valid =>
      Eq.mpr (congrArg (fun models : List CellModel =>
        UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
          models (walkPath parent (.cons interval member tail)))
        (OfFn.Basic.ofFn_succ (function := cells)))
        (.cons (starts (0 : Fin (tail.edges.length + 1)))
          (finishes (0 : Fin (tail.edges.length + 1)))
          (.uniform (valid (0 : Fin (tail.edges.length + 1))))
        (certifyWalk channel tail (fun index => cells index.succ)
          (fun index => starts index.succ) (fun index => finishes index.succ)
          (fun index => valid index.succ)))

/-- The original zero-fraction lifted point is the original parent's exact source point and sheet. -/
theorem first_eq : (⟨parent.edge.point 0, parent.edge.sheet⟩ : LiftedPoint 2) = startPoint parent :=
  congrArg (fun point : Canonical => (⟨point, parent.edge.sheet⟩ : LiftedPoint 2)) parent.edge.point_zero

/-- The original unit-fraction lifted point is the original parent's exact target point and sheet. -/
theorem last_eq : (⟨parent.edge.point 1, parent.edge.sheet⟩ : LiftedPoint 2) = finishPoint parent :=
  congrArg (fun point : Canonical => (⟨point, parent.edge.sheet⟩ : LiftedPoint 2)) parent.edge.point_one

/-- Construct the actual original partition's oriented lifted refinement at the parent's exact endpoints. -/
def partitionPath {cuts : List Rational} (partition : AxisPartition 0 1 cuts) :
    LiftedPath 2 (startPoint parent) (finishPoint parent) :=
  ((walkPath parent partition.walk).castStart (first_eq parent)).castFinish (last_eq parent)

/-- The whole retained partition path is its original interval-walk construction with exact endpoint transports. -/
theorem partitionPath_eq {cuts : List Rational} (partition : AxisPartition 0 1 cuts) :
    partitionPath parent partition =
      ((walkPath parent partition.walk).castStart (first_eq parent)).castFinish (last_eq parent) := by
  unfold partitionPath
  rfl

/-- Append actual stored parent refinements along the original geometric chain and its exact endpoint owners. -/
def parentPath : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    {first last : LiftedPoint 2} → (chain : CenteredPathChain parents (start := first) (finish := last)) →
    ((index : Fin parents.length) →
      LiftedPath 2 (startPoint (parents[index.val]'index.isLt)) (finishPoint (parents[index.val]'index.isLt))) →
    LiftedPath 2 first last
  | [], _, _, .nil point, _ => .nil point
  | _ :: _, _, _, .cons _ tail, paths => (paths 0).append (parentPath tail (fun index => paths index.succ))

/-- The actual parent certificate caches concatenate on that same original geometric chain. -/
def certifyParents (channel : Fin 6) : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    {first last : LiftedPoint 2} → (chain : CenteredPathChain parents (start := first) (finish := last)) →
    (paths : (index : Fin parents.length) →
      LiftedPath 2 (startPoint (parents[index.val]'index.isLt)) (finishPoint (parents[index.val]'index.isLt))) →
    (cells : Fin parents.length → List CellModel) →
    (∀ index, UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (cells index) (paths index)) →
    UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (List.ofFn cells).flatten (parentPath chain paths)
  | [], _, _, .nil point, _, _, _ => .nil point
  | _ :: _, _, _, .cons head tail, paths, cells, valid =>
      Eq.mpr (congrArg (fun models : List CellModel =>
        UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
          models (parentPath (.cons head tail) paths))
        (congrArg List.flatten (OfFn.Basic.ofFn_succ (function := cells))))
        (UniformPathCertificates.append (paths 0) (valid 0)
        (certifyParents channel tail (fun index => paths index.succ) (fun index => cells index.succ)
          (fun index => valid index.succ)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop

end
