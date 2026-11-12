module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs

/-! # Actual global source requests at an independently chosen joint accuracy

The retained shifted geometry precedes a finite sufficient-stage selection.
One new original Request then allocates its actual whole-path Targets and
source bank at that selected stage. Every original cell allowance pays the
supplied positive accuracy. Earlier source models and requests are not
retagged, resampled or replaced by this separately retained construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)

variable {parameter increment : Canonical} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root)

/-- A sufficient original stage and its actual new global source request retain both whole factory equations.

The supplied accuracy may be the already computed minimum of independent
spatial and parameter-fourth requests. It is chosen before this source
acquisition. The same original geometry owns the newly allocated global
Targets, prepared sources, bank and all typed endpoint-checking outcomes.
-/
@[expose] def Requested (nonempty : geometry.parents ≠ []) (current floor rootStage : Nat)
    (accuracy : AccuracyRequest) :=
  (selected : { value : Geometric.Search.Selection 1 current accuracy.tolerance //
    value = Geometric.Search.Selection.build 1 (of_decide_eq_true rfl) current
      accuracy.tolerance accuracy.positive }) ×
  { request : Request geometry selected.val.stage floor rootStage //
    request = Request.build geometry nonempty selected.val.stage floor rootStage }

namespace Requested

/-- Select the finite original stage first, then run the complete new global source request exactly once. -/
def build (nonempty : geometry.parents ≠ []) (current floor rootStage : Nat) (accuracy : AccuracyRequest) :
    Requested geometry nonempty current floor rootStage accuracy :=
  let selected := Geometric.Search.Selection.build 1 (of_decide_eq_true rfl) current
    accuracy.tolerance accuracy.positive
  let request := Request.build geometry nonempty selected.stage floor rootStage
  ⟨⟨selected, rfl⟩, ⟨request, rfl⟩⟩

variable {geometry} {nonempty : geometry.parents ≠ []} {current floor rootStage : Nat}
    {accuracy : AccuracyRequest} (retained : Requested geometry nonempty current floor rootStage accuracy)

/-- Read the same original sufficient-stage selection without repeating the bounded search. -/
@[expose] def selected : Geometric.Search.Selection 1 current accuracy.tolerance := retained.1.val

/-- Read the complete actual new global Request on the same geometry at its retained selected stage. -/
@[expose] def request : Request geometry retained.selected.stage floor rootStage := retained.2.val

/-- The sufficient-stage cache retains the exact original search factory and supplied positive accuracy. -/
theorem selected_eq : retained.selected = Geometric.Search.Selection.build 1 (of_decide_eq_true rfl) current
    accuracy.tolerance accuracy.positive := retained.1.property

/-- The whole actual new source request is its original factory, including the original global Targets and bank. -/
theorem request_eq : retained.request = Request.build geometry nonempty retained.selected.stage floor rootStage :=
  retained.2.property

/-- Read the actual new request's original global Targets cache, including its count-dependent allocation. -/
@[expose] def targets := retained.request.attempt.1.val

/-- The exact original preparation product at this retained request's own global Targets.

The complete request, cover, floor and retained allocation remain indices
of the original PreparedParents family. This type names the existing
owned product without constructing a preparation or changing its Targets.
-/
@[expose] def PreparedAt : Type 1 :=
  PreparedParents (parameter := parameter + increment) (frame := target) (basis := basis) (count := count)
    retained.request.covered floor retained.request.attempt.1.val

/-- Read the same actual new source preparations at their original global target index. -/
@[expose] def prepared : PreparedAt retained := retained.request.attempt.2.1

/-- The actual new global allocation strictly pays the supplied independently selected joint accuracy. -/
theorem localBound_lt : retained.targets.localBound < accuracy.tolerance :=
  retained.targets.localBound_le_quarterRadius.trans_lt
    (retained.selected.later_accurate (Nat.le_refl _))

/-- Every actual new source-cell allowance pays that same joint accuracy on its original global occurrence. -/
theorem cell_allowance_lt (index : Fin (retained.request.shape.val.1 :: retained.request.shape.val.2).length)
    (channel : Fin 6) :
    ((retained.prepared.entry index).preparation.cell.models.cell channel).localAllowance < accuracy.tolerance :=
  ((retained.prepared.entry index).cell_allowance channel).trans_lt retained.localBound_lt

/-- The actual new global source-bank endpoint request pays the same independently chosen joint accuracy. -/
theorem endpoint_lt : retained.targets.endpoint < accuracy.tolerance := by
  rewrite [retained.targets.endpoint_eq]
  exact retained.localBound_lt

end Requested

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
