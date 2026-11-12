module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.LiftedCells
public import Purelib.Geometry.Path.Gaussian.Lifted.Closed
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Endpoints
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Ordered paths assembled from retained original lifted cells

The actual cached cells supply the path data. Their whole factory equation
supplies only erased sheet and tail equalities. The original parent-chain
existence proof supplies only endpoint identities; no computational chain
is selected from Nonempty, and no lifted-cell cache is rebuilt.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

/-- The literal cached tail has the original tail builder's whole factory identity. -/
theorem tail_eq
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (factory : paths = build (.cons data rest) planned) :
    paths.2.2.2.2 = build rest planned.2.2.2 :=
  congrArg (fun value : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned => value.2.2.2.2)
    (factory.trans (build_cons data rest planned))

/-- The actual cached first point has the original parent chain's starting coordinate and sheet. -/
theorem firstPoint_eq
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (factory : paths = build (.cons data rest) planned)
    {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain (parent :: parents) (start := start) (finish := finish))) :
    (⟨data.segment.comparison.first, paths.1⟩ : LiftedPoint 2) = start := by
  have sheet := congrArg (fun value : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned => value.1)
    (factory.trans (build_cons data rest planned))
  have original := congrArg₂ (fun point : Gaussian => fun sheet : Fin 2 => (⟨point, sheet⟩ : LiftedPoint 2))
    (data.first_eq.trans parent.edge.point_zero) sheet
  have source : (⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩ : LiftedPoint 2) =
      start := by
    obtain ⟨kept⟩ := chain
    exact kept.start_eq
  exact original.trans source

/-- The actual cached last point is the original head parent's retained terminal point and sheet. -/
theorem lastPoint_eq
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (factory : paths = build (.cons data rest) planned) :
    (⟨data.segment.comparison.last, paths.2.1⟩ : LiftedPoint 2) =
      ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩ := by
  have sheet := congrArg (fun value : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
    (sourceDifferential := sourceDifferential) (count := count)
    (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned => value.2.1)
    (factory.trans (build_cons data rest planned))
  exact congrArg₂ (fun point : Gaussian => fun sheet : Fin 2 => (⟨point, sheet⟩ : LiftedPoint 2))
    (data.last_eq.trans parent.edge.point_one) sheet

/-- The exact path-construction function on an existing cell cache and erased original chain evidence. -/
private def PathFamily :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {parents} bank =>
    (planned : Plan error errorPositive floor bank) →
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor) bank planned) →
        paths = build bank planned → {start finish : LiftedPoint 2} →
          Nonempty (CenteredPathChain parents (start := start) (finish := finish)) → LiftedPath 2 start finish

/-- An empty cache constructs the original starting point's empty path, using only the proved endpoint equality. -/
private def emptyPath :
    PathFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) .nil := by
  intro planned paths factory start finish chain
  have endpoints : start = finish := by
    obtain ⟨kept⟩ := chain
    exact kept.empty_eq
  exact (LiftedPath.nil start).castFinish endpoints

/-- Prepend the actual cached head cell before assembling the same literal cached tail. -/
private def pathStep
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (following : Unit → PathFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) rest) :
    PathFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) :=
  fun planned paths factory {_start _finish} chain =>
    let cell := paths.2.2.1.castEndpoints (firstPoint_eq data rest planned paths factory chain)
      (lastPoint_eq data rest planned paths factory)
    let remaining := following ()
    let tail := remaining planned.2.2.2 paths.2.2.2.2 (tail_eq data rest planned paths factory)
      (remaining_chain chain)
    .cons cell tail

/-- Assemble the same ordered cached cells into the original parent chain's lifted path.

The factory equation is consumed only in endpoint and tail proofs. Every
computational head comes from the supplied paths cache, and every tail is
its literal retained tail. Nonempty is eliminated only into propositions.
-/
def path :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) →
          (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) bank planned) →
            paths = build bank planned → {start finish : LiftedPoint 2} →
              Nonempty (CenteredPathChain parents (start := start) (finish := finish)) → LiftedPath 2 start finish :=
  fun {_parents} bank =>
    Bank.fold (motive := PathFamily (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor))
      (emptyPath (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor))
      (pathStep (parameter := parameter) (frame := frame) (cap := cap)
        (sourceDifferential := sourceDifferential) (count := count)
        (error := error) (errorPositive := errorPositive) (floor := floor)) bank

/-- The nonempty path retains its actual cached head cell and unchanged ordered tail path. -/
theorem path_cons
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) planned)
    (factory : paths = build (.cons data rest) planned)
    {start finish : LiftedPoint 2}
    (chain : Nonempty (CenteredPathChain (parent :: parents) (start := start) (finish := finish))) :
    path (.cons data rest) planned paths factory chain =
      .cons (paths.2.2.1.castEndpoints (firstPoint_eq data rest planned paths factory chain)
        (lastPoint_eq data rest planned paths factory))
        (path rest planned.2.2.2 paths.2.2.2.2 (tail_eq data rest planned paths factory) (remaining_chain chain)) := by
  have folded := Bank.fold_cons (motive := PathFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor))
    (emptyPath (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor))
    (pathStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)) data rest
  exact congrArg (fun next : PathFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor) (.cons data rest) =>
    next planned paths factory chain) folded

/-- The assembled path keeps every original occurrence, including repeated and stationary cells. -/
theorem path_cellCount :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) →
          (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
            (sourceDifferential := sourceDifferential) (count := count)
            (error := error) (errorPositive := errorPositive) (floor := floor) bank planned) →
            (factory : paths = build bank planned) → {start finish : LiftedPoint 2} →
              (chain : Nonempty (CenteredPathChain parents (start := start) (finish := finish))) →
                (path bank planned paths factory chain).cellCount = parents.length := by
  intro parents bank
  induction bank with
  | nil =>
      intro planned paths factory start finish chain
      have folded := Bank.fold_nil (motive := PathFamily (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor))
        (emptyPath (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor))
        (pathStep (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor))
      have projected := congrArg (fun next : PathFamily (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor) .nil =>
        (next planned paths factory chain).cellCount) folded
      have zero : (emptyPath (parameter := parameter) (frame := frame) (cap := cap)
          (sourceDifferential := sourceDifferential) (count := count)
          (error := error) (errorPositive := errorPositive) (floor := floor)
          planned paths factory chain).cellCount = 0 := by
        obtain ⟨kept⟩ := chain
        cases kept
        rfl
      exact projected.trans zero
  | cons data rest ih =>
      intro planned paths factory start finish chain
      have head := congrArg (fun value : LiftedPath 2 start finish => value.cellCount)
        (path_cons data rest planned paths factory chain)
      exact head.trans (congrArg Nat.succ
        (ih planned.2.2.2 paths.2.2.2.2 (tail_eq data rest planned paths factory) (remaining_chain chain)))

/-- Assemble the existing boundary cache into its displayed closed lifted path.

The original cache already declares its starting and finishing labelled
anchor. This constructor uses that geometry and its same cached cells.
The separate actual root-return certificate remains closed.returned and is
still required by endpoint and period comparisons.
-/
def closedPath
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential)
    (planned : Plan error errorPositive floor closed.covered.bank)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned)
    (factory : paths = build closed.covered.bank planned) : ClosedLiftedPath 2 :=
  ⟨⟨collar.box.anchor, 0⟩, path closed.covered.bank planned paths factory closed.covered.cache.chain⟩

/-- The same assembled closed boundary retains its original cached parent count. -/
theorem closedPath_cellCount
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential)
    (planned : Plan error errorPositive floor closed.covered.bank)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor) closed.covered.bank planned)
    (factory : paths = build closed.covered.bank planned) :
    (closedPath closed planned paths factory).cellCount = closed.covered.parentCount :=
  (path_cellCount closed.covered.bank planned paths factory closed.covered.cache.chain).trans
    closed.covered.parents_length

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.LiftedCells

end
