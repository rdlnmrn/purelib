module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Pair
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations

/-! # Six original spatial cells with both prepared endpoint attachments

The original patch, six uniform requests and two endpoint plans are
retained inputs. Their common model is selected once, then one coordinate
cache constructs the six physical polynomial cells. The original Cell,
both endpoint attachments and the existing six-channel Query consume those
identical selected source and model caches.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)

variable {parameter : Canonical} {count floor firstFloor lastFloor : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
variable {bounds : UniformBounds patch} {start finish : LiftedPoint 2} {lifted : LiftedCell start finish}
variable {firstSample : ContinuedNeighborhood.Point patch start.coordinate}
variable {lastSample : ContinuedNeighborhood.Point patch finish.coordinate}
variable {allowance firstAllocation lastAllocation target : Rational}

/-- One actual source selection, six physical cell models, the original Cell and its paid six-channel query.

Both endpoint plans are attached to the same retained model stage. The
Cell's complete factory equation binds its exact original lifted segment,
request, models and endpoint containments; the Query keeps that same Cell.
-/
abbrev Preparation (requests : IntegrandRequests bounds floor (allowance / 4))
    (firstPlan : EndpointPlan firstSample firstFloor firstAllocation)
    (lastPlan : EndpointPlan lastSample lastFloor lastAllocation)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate)
    (target : Rational) (positive : 0 < target) :=
  (attached : EndpointPlan.AttachedPair requests cache firstPlan lastPlan target positive) ×
  (models : CellModels attached.source start.coordinate finish.coordinate allowance) ×
  (cell : { original : Cell (parameter := parameter) lifted //
    original = Cell.ofModels attached.source lifted models startInside finishInside }) ×
  Query cell.val

namespace Preparation

variable {requests : IntegrandRequests bounds floor (allowance / 4)}
variable {firstPlan : EndpointPlan firstSample firstFloor firstAllocation}
variable {lastPlan : EndpointPlan lastSample lastFloor lastAllocation}
variable {startInside : patch.box.Contains start.coordinate} {finishInside : patch.box.Contains finish.coordinate}
variable {positive : 0 < target}

/-- Read both actual endpoint attachments and their single retained original source request. -/
@[expose] def attached
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive) :
    EndpointPlan.AttachedPair requests cache firstPlan lastPlan target positive := prepared.1

/-- Read the identical retained coordinate and six polynomial pullbacks of that selected original model. -/
@[expose] def models
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive) :
    CellModels prepared.attached.source start.coordinate finish.coordinate allowance := prepared.2.1

/-- Read the original spatial source Cell without constructing another request or cell list. -/
@[expose] def cell
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive) :
    Cell (parameter := parameter) lifted := prepared.2.2.1.val

/-- The original Cell retains the complete selected source, six-model cache and physical endpoint admission. -/
theorem cell_eq
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive) :
    prepared.cell = Cell.ofModels prepared.attached.source lifted prepared.models startInside finishInside :=
  prepared.2.2.1.property

/-- Read the existing six-channel query tied to this identical complete original Cell. -/
@[expose] def query
    (prepared : Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive) :
    Query prepared.cell := prepared.2.2.2

end Preparation

variable (lifted)

/-- Select and cache one physical six-channel source with both original prepared endpoint plans.

The six integrand and two endpoint stage floors are paid internally by the
existing source request. Every polynomial cache is built once after that
selection; neither endpoint root observation is used as another's witness.
-/
def prepare
    (requests : IntegrandRequests bounds floor (allowance / 4)) (cache : Cache patch)
    (firstPlan : EndpointPlan firstSample firstFloor firstAllocation)
    (lastPlan : EndpointPlan lastSample lastFloor lastAllocation)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate)
    (allowancePositive : 0 < allowance) (target : Rational) (positive : 0 < target) :
    Preparation (cache := cache) (lifted := lifted)
      requests firstPlan lastPlan startInside finishInside target positive :=
  let attached := EndpointPlan.attachPair requests cache firstPlan lastPlan target positive
  let models := CellModels.build attached.source start.coordinate finish.coordinate allowance allowancePositive.le
  let cell := Cell.ofModels attached.source lifted models startInside finishInside
  let query := Query.ofModels attached.source models startInside finishInside requests allowancePositive
    attached.integrands_paid cell rfl
  ⟨attached, models, ⟨cell, rfl⟩, query⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
