module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank.Primitive.Endpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Endpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Fold
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Equivalence

/-! # Closing evidence for the original requested primitive endpoints

The terminal requested Point is compared with the initial requested Point
through the original retained parent root links and actual root-return
certificate. The coordinate identity follows separately from the same
original parent chain. No quotient-coordinate comparison replaces root
ownership, and no endpoint or path preparation is repeated.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace LastRelation

/-- The exact function space of final-endpoint relation types on one original bank.

The bank remains abstract while the supplied plan, path and endpoint cache
are applied. This type alias preserves their original nominal owners.
-/
@[expose] def Function (coefficient : Polynomial) (target : Coordinate)
    (_targetPoint : Gaussian) (_targetRoot : Named) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {_parents} bank =>
    (planned : Plan error errorPositive floor bank) →
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        bank planned) →
        EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
          coefficient target bank planned paths → Type

/-- Construct the cons relation type from the same head and literal following relation type.

A final occurrence retains both its actual generator comparison and exact
coordinate property. A longer bank passes the unchanged cache tails to the
supplied following type function. The body is exposed for client reduction.
-/
@[expose] def cons (coefficient : Polynomial) (target : Coordinate)
    (targetPoint : Gaussian) (targetRoot : Named)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (following : Unit → Function (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot rest) :
    Function (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot (.cons data rest) := by
  cases rest with
  | nil =>
      intro planned paths endpoints
      exact { compared : NamedEquivalent endpoints.2.1.val.certificate.value.name targetRoot //
        planned.2.1.point 1 = targetPoint }
  | cons next remaining =>
      intro planned paths endpoints
      exact following () planned.2.2.2 paths.2.2.2.2 endpoints.2.2.2.2

end LastRelation

/-- The literal final requested Point has the supplied coordinate and original generator.

The subtype retains the actual operational generator comparison. Its
separate property is the exact coordinate identification; neither relation
is inferred from the other. Empty banks have no final occurrence.
-/
@[expose] def LastRelation (coefficient : Polynomial) (target : Coordinate)
    (targetPoint : Gaussian) (targetRoot : Named) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) → (paths : LiftedCells
      (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      bank planned) →
          EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target bank planned paths → Type := by
  intro parents bank
  exact Bank.rec (motive := fun parents bank =>
      LastRelation.Function (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot (parents := parents) bank)
    (fun _ _ _ => PUnit)
    (fun {_parent} {_parents} data rest following =>
      LastRelation.cons (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot data rest (fun _ => following)) bank

/-- The exact function type for building a final relation from retained roots and original parent geometry. -/
private def BuildFamily (coefficient : Polynomial) (target : Coordinate)
    (targetPoint : Gaussian) (targetRoot : Named) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      Bank cap sourceDifferential count parents → Type 3 :=
  fun {parents} bank =>
    (planned : Plan error errorPositive floor bank) →
      (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        bank planned) →
        (endpoints : EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
          coefficient target bank planned paths) →
          {first last : Named} → RootLinks bank first last →
            {start finish : LiftedPoint 2} →
              Nonempty (CenteredPathChain parents (start := start) (finish := finish)) →
                finish.coordinate = targetPoint → NamedEquivalent last targetRoot →
                  LastRelation (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot bank planned paths endpoints

/-- Build one final relation or pass the same literal caches and retained root-link tail onward. -/
private def lastStep (coefficient : Polynomial) (target : Coordinate)
    (targetPoint : Gaussian) (targetRoot : Named)
    {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (following : Unit → BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot rest) :
    BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot (.cons data rest) := by
  cases rest with
  | nil =>
      intro planned paths endpoints first last roots start finish chain pointEq returned
      exact ⟨(data.lastPoint_owner planned.2.1 endpoints.2.1.val).symm.trans
          ((emptyRoots roots.tail).trans returned),
        planned.2.1.point_one.trans ((data.last_eq.trans (final_coordinate chain)).trans pointEq)⟩
  | cons next remaining =>
      intro planned paths endpoints first last roots start finish chain pointEq returned
      exact following () planned.2.2.2 paths.2.2.2.2 endpoints.2.2.2.2 roots.tail
        (remaining_chain chain) pointEq returned

/-- Read the final original root link and parent geometry through the same shared bank algebra.

The private value fold keeps its result family abstract. Its only final
comparison composes the retained requested Point relation, original final
root link and supplied actual return; no endpoint is reconstructed.
-/
private def lastRelation (coefficient : Polynomial) (target : Coordinate)
    (targetPoint : Gaussian) (targetRoot : Named) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot bank := by
  intro parents bank
  refine Bank.fold (motive := BuildFamily (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot) ?_
    (lastStep (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
        coefficient target targetPoint targetRoot) bank
  intro planned paths endpoints first last roots start finish chain pointEq returned
  exact ⟨⟩

/-- The final and initial original requested Points have equal coordinates and equivalent generators.

The whole request bank remains the index of this relation. In particular,
the initial Point is the retained first callback result, even when an
endpoint or whole occurrence is stationary.
-/
@[expose] def Closing (coefficient : Polynomial) (target : Coordinate) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) →
        (planned : Plan error errorPositive floor bank) → (paths : LiftedCells
      (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      bank planned) →
          EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target bank planned paths → Type
  | [], .nil, _, _, _ => PUnit
  | _ :: _, .cons data rest, planned, paths, endpoints =>
      LastRelation (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target (planned.2.1.point 0) endpoints.1.val.certificate.value.name
        (.cons data rest) planned paths endpoints

namespace Closing

/-- Derive closing evidence from the same original root-link spine, closed parent geometry and actual root return.

The supplied return compares the retained external finish and start owners.
Both original endpoint Point comparisons are constructed from those same
parents' patches. Equal endpoint coordinates alone supply no root return.
-/
def build (coefficient : Polynomial) (target : Coordinate) :
    ∀ {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
      (bank : Bank cap sourceDifferential count parents)
      (planned : Plan error errorPositive floor bank) (paths : LiftedCells
      (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      bank planned)
      (endpoints : EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target bank planned paths)
      {first last : Named}, RootLinks bank first last →
      {start finish : LiftedPoint 2} → Nonempty (CenteredPathChain parents (start := start) (finish := finish)) →
      start.coordinate = finish.coordinate → NamedEquivalent last first →
        Closing (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := count)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target bank planned paths endpoints
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _ => ⟨⟩
  | _ :: _, .cons data rest, planned, paths, endpoints, _, _, roots, _, _, chain, pointEq, returned =>
      lastRelation coefficient target (planned.2.1.point 0) endpoints.1.val.certificate.value.name
        (.cons data rest) planned paths endpoints roots chain
        (pointEq.symm.trans ((first_coordinate chain).symm.trans
          (data.first_eq.symm.trans planned.2.1.point_zero.symm)))
        (returned.trans (roots.entry.trans (data.firstPoint_owner planned.2.1 endpoints.1.val)))

/-- The existing complete boundary supplies closing evidence for its same original primitive endpoint bank.

Only the supplied boundary's cached bank, parent chain, root links and
returned certificate are consumed. No path, parent, Point, request or
root-return preparation is reconstructed.
-/
def ofBoundary (coefficient : Polynomial) (target : Coordinate)
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval collar.box.anchor)}
    (closed : Boundary.Data cap owner sourceDifferential)
    (planned : Plan error errorPositive floor closed.covered.bank)
    (paths : LiftedCells (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      closed.covered.bank planned)
    (endpoints : EndpointRequests (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target closed.covered.bank planned paths) :
    Closing (parameter := parameter) (frame := frame) (cap := cap)
      (sourceDifferential := sourceDifferential) (count := 1)
      (error := error) (errorPositive := errorPositive) (floor := floor)
      coefficient target closed.covered.bank planned paths endpoints :=
  build coefficient target closed.covered.bank planned paths endpoints
    closed.covered.roots closed.covered.cache.chain rfl closed.returned

end Closing

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan.Primitive.EndpointRequests

end
