module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Reversal
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
public import Purelib.Integration.Polynomial.Gaussian.Path.Reversal
import Purelib.Tactic.Ring

open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

section
@[expose] public section

/-!
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace Purelib.Geometry.Path.Gaussian.Lifted.Basic
namespace LiftedPath

section
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- The original lifted path follows the exact endpoint coordinates of the supplied ordered cell models.

The inductive witness retains the lifted cells and path endpoints while matching each original polynomial model's start
and finish coordinates. -/
inductive FollowedBy {sheets : Nat} :
    List Basic.CellModel -> {start finish : LiftedPoint sheets} ->
      Lifted.Basic.LiftedPath sheets start finish -> Prop
  /-- The empty model list follows the original empty lifted path at its retained point. -/ | nil (point :
    LiftedPoint sheets) : FollowedBy [] (.nil point)
  /-- Retain both endpoint-coordinate equalities for the original head model and the exact tail-following witness. -/ |
    cons {start middle finish : LiftedPoint sheets}
      {model : Basic.CellModel} {models : List Basic.CellModel}
      {cell : Lifted.Basic.LiftedCell start middle}
      {remaining : Lifted.Basic.LiftedPath sheets middle finish}
      (start_eq : model.start = start.coordinate)
      (finish_eq : model.finish = middle.coordinate)
      (tail : FollowedBy models remaining) :
      FollowedBy (model :: models) (.cons cell remaining)

/-- The retained model list length equals the original followed lifted path's cell count.

The original following witness matches each retained model to one exact
lifted cell. Its inductive tail therefore gives the same finite successor count. -/
theorem followedBy_length {sheets : Nat} {models : List
  Basic.CellModel}
    {start finish : LiftedPoint sheets} {path : Lifted.Basic.LiftedPath sheets start finish}
    (follows : FollowedBy models path) :
    models.length = path.cellCount := by
  induction follows with
  | nil => rfl
  | cons start_eq finish_eq tail inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The followed model displacements telescope to the original lifted path's endpoint displacement.

The original head endpoint equalities align the model displacement with
its exact lifted cell. The retained tail witness telescopes the same remaining sum. -/
theorem followedBy_displacementSum {sheets : Nat}
    {models : List Basic.CellModel}
    {start finish : LiftedPoint sheets}
    {path : Lifted.Basic.LiftedPath sheets start finish}
    (follows : FollowedBy models path) :
    Basic.PathModel.displacementSum models =
      finish.coordinate - start.coordinate := by
  induction follows with
  | nil point =>
      change (0 : Purelib.Data.Gaussian.Basic.Canonical) = point.coordinate - point.coordinate
      exact (Basic.sub_self point.coordinate).symm
  | @cons start middle finish model models cell remaining start_eq finish_eq
      tail inductionHypothesis =>
      simp only [Basic.PathModel.displacementSum_cons]
      unfold Basic.CellModel.displacement
      rw [start_eq, finish_eq, inductionHypothesis]
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.add_re,
          Basic.add_im] <;> ring1

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Appending original model lists follows the concatenation of their exact endpoint-compatible lifted paths. -/
theorem followedBy_append {sheets : Nat}
    {firstModels secondModels : List Basic.CellModel}
    {start middle finish : LiftedPoint sheets}
    {first : Lifted.Basic.LiftedPath sheets start middle}
    {second : Lifted.Basic.LiftedPath sheets middle finish}
    (firstFollows : FollowedBy firstModels first)
    (secondFollows : FollowedBy secondModels second) :
    FollowedBy (firstModels ++ secondModels) (first.append second) := by
  induction firstFollows with
  | nil => exact secondFollows
  | cons start_eq finish_eq tail inductionHypothesis =>
      exact .cons start_eq finish_eq (inductionHypothesis secondFollows)

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Certified reversal models follow the exact reversal of the original lifted path. -/
theorem followedBy_reverse {sheets : Nat} {models : List
  Basic.CellModel}
    {start finish : LiftedPoint sheets} {path : Lifted.Basic.LiftedPath sheets start finish}
    (follows : FollowedBy models path)
    (reversal : Basic.PathModel.ReversalCells
      models) :
    FollowedBy (Reversal.PathModel.ReversalCells.reversed reversal) path.reverse := by
  induction follows with
  | nil point =>
      cases reversal
      exact .nil point
  | @cons start middle finish model models cell remaining start_eq finish_eq
      tail inductionHypothesis =>
      cases reversal with
      | cons head rest =>
          change FollowedBy
            ((Reversal.PathModel.ReversalCells.reversed rest) ++
              [Basic.CellModel.reverse model head])
            (remaining.reverse.append
              (.cons cell.reverse (.nil start)))
          apply followedBy_append (inductionHypothesis rest)
          exact .cons finish_eq start_eq (.nil start)
end LiftedPath
end Purelib.Geometry.Path.Gaussian.Lifted.Basic

end

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Geometry.Path.Gaussian.Lifted.Refinement

namespace CycleJoin

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The original concatenated model lists follow the closed lifted-path join at the supplied common basepoint.

The supplied exact basepoint equality identifies the retained path indices.
The original following witnesses then compose along their unchanged path append. -/
theorem appendFollowed {sheets : Nat}
    (first second : Lifted.Closed.ClosedLiftedPath sheets)
    (basepoint_eq : first.basepoint = second.basepoint)
    {firstModels secondModels : List
      Basic.CellModel}
    (firstFollows : Lifted.Basic.LiftedPath.FollowedBy firstModels first.path)
    (secondFollows : Lifted.Basic.LiftedPath.FollowedBy secondModels second.path) :
    Lifted.Basic.LiftedPath.FollowedBy (firstModels ++ secondModels)
      (Lifted.Refinement.CycleJoin.appendClosed first second basepoint_eq).path := by
  cases first with
  | mk firstBase firstPath =>
      cases second with
      | mk secondBase secondPath =>
          dsimp only at basepoint_eq
          subst secondBase
          exact Lifted.Basic.LiftedPath.followedBy_append firstFollows secondFollows

end CycleJoin
end Purelib.Geometry.Path.Gaussian.Lifted.Refinement

end
