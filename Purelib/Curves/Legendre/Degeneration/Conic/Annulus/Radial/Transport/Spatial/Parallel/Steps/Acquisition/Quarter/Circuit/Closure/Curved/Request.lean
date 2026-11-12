module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Curved
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Joint requests for the same four old curved banks and paid closed spine

The sufficient dyadic depth is selected before any bank or primitive
observation. Its original bank request is passed to the original inverse
Closed.Requested allocator. That factory chooses the complete path count,
then observes once at exactly the intended local accuracy. The identical
closed cache supplies all quarter views and its single closing comparison.
No arbitrary old cache is assigned a smaller request after observation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

open Purelib.Algebra
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

namespace Closure.Result.Curved

variable (result : Closure.Result execution) (row : Row)
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) (row.form parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} (source : Differential.Circuit.Cells data circuit initialAccuracy)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

set_option genInjectivity false in
/-- One actual joint stage retains its original inverse request, closed observations, views, banks and Comparisons.

Every complete original factory runs once in the displayed order. The
original intended local bank accuracy is computed before observations.
The retained exact request equality supplies arithmetic payment only; it
never retags, replaces or re-observes an already selected old cache.
-/
structure Stage (depth : Nat) where
  /-- The original inverse allocator retains the exact count, request and one old spine with its single closing. -/
  cachedObservations : { value : Primitive.Closed.Requested result.traced.path
        (PreparedParents.Trace.defined row result.traced.path) result.join (Bank.Quarter.request depth) //
      value = Primitive.Closed.Requested.build result.traced.path
        (PreparedParents.Trace.defined row result.traced.path) result.join (Bank.Quarter.request depth) }
  /-- The complete original quarter partition consumes that identical retained old closed execution. -/
  cachedPartition : { value : Partitioned result (row.expression parameter)
        (PreparedParents.Trace.defined row result.traced.path) cachedObservations.val.request //
      value = Partitioned.ofObserved result (row.expression parameter)
        (PreparedParents.Trace.defined row result.traced.path) cachedObservations.val.request
        cachedObservations.val.closed }
  /-- The complete original physical descent keeps every old quarter, Block, Segment and stationary occurrence. -/
  cachedDescent : { value : Partitioned.Descent cachedPartition.val //
      value = Partitioned.Descent.build cachedPartition.val }
  /-- The four original bank realizations retain all original cells, samples, endpoints and factory identities. -/
  cachedBanks : { value : Bank.Circuit.Quarters (specification := specification) source depth //
      value = Bank.Circuit.Quarters.build (specification := specification) source depth }
  /-- All eight actual endpoint Comparisons are computed on these SAME old bank and paid-spine caches. -/
  cachedCompared : { value : Compared cachedPartition.val cachedDescent.val cachedBanks.val //
      value = Compared.build cachedPartition.val cachedDescent.val cachedBanks.val }

constructive_injectivity Stage

namespace Stage

/-- Compute the intended requests first, then retain every original observer, partition, bank and Comparison once. -/
def build (depth : Nat) : Stage result row source depth :=
  let observations := Primitive.Closed.Requested.build result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join (Bank.Quarter.request depth)
  let partition := Partitioned.ofObserved result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) observations.request observations.closed
  let descended := Partitioned.Descent.build partition
  let banks := Bank.Circuit.Quarters.build (specification := specification) source depth
  let compared := Compared.build partition descended banks
  ⟨⟨observations, rfl⟩, ⟨partition, rfl⟩, ⟨descended, rfl⟩, ⟨banks, rfl⟩, ⟨compared, rfl⟩⟩

variable {result row source} {depth : Nat}
variable (stage : Stage result row source depth)

/-- Read the same original inverse-request/closed observation cache, including its literal closing Comparison. -/
@[expose] def observations : Primitive.Closed.Requested result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join (Bank.Quarter.request depth) :=
  stage.cachedObservations.val

/-- Read the same whole original old quarter partition. -/
@[expose] def partition : Partitioned result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) stage.observations.request := stage.cachedPartition.val

/-- Read the same complete physical old-spine descent, without a second observer or path construction. -/
@[expose] def descended : Partitioned.Descent stage.partition := stage.cachedDescent.val

/-- Read the four original old Bank realizations, retaining their complete cells and endpoint caches. -/
@[expose] def banks : Bank.Circuit.Quarters (specification := specification) source depth :=
  stage.cachedBanks.val

/-- Read the same eight original endpoint Comparison results and their exact complete factory identities. -/
@[expose] def compared : Compared stage.partition stage.descended stage.banks := stage.cachedCompared.val

/-- Sum the four actual cached original bank samples without evaluating the separate program-model factory. -/
@[expose] def sample : Canonical := FiniteSum.Fin.sumFin (samples stage.banks)

/-- The cached sample has the exact original curved program's integral readback at this same depth. -/
theorem sample_eq : stage.sample = (source.program.model depth).integralSample := samples_sum_eq stage.banks

/-- The inverse observer is its exact original factory at the intended local bank request. -/
theorem observations_eq : stage.observations = Primitive.Closed.Requested.build result.traced.path
    (PreparedParents.Trace.defined row result.traced.path) result.join (Bank.Quarter.request depth) :=
  stage.cachedObservations.property

/-- The partition is its original complete-cache factory on this SAME already selected old Closed execution. -/
theorem partition_eq : stage.partition = Partitioned.ofObserved result (row.expression parameter)
    (PreparedParents.Trace.defined row result.traced.path) stage.observations.request stage.observations.closed :=
  stage.cachedPartition.property

/-- The physical descent is its original cache-only factory on this SAME retained complete partition. -/
theorem descended_eq : stage.descended = Partitioned.Descent.build stage.partition := stage.cachedDescent.property

/-- The four banks are their original factory at this depth and on the identical original curved source cells. -/
theorem banks_eq : stage.banks = Bank.Circuit.Quarters.build
    (specification := specification) source depth := stage.cachedBanks.property

/-- The endpoint Comparisons are their exact original factory on these SAME old caches. -/
theorem compared_eq : stage.compared = Compared.build stage.partition stage.descended stage.banks :=
  stage.cachedCompared.property

/-- The partition retains the identical old Closed acquisition, including the SAME original closing Comparison. -/
theorem partition_observed : stage.partition.observed = stage.observations.closed :=
  (congrArg (fun partition : Partitioned result (row.expression parameter)
      (PreparedParents.Trace.defined row result.traced.path) stage.observations.request => partition.observed)
    stage.partition_eq).trans
    (Partitioned.ofObserved_observed result (row.expression parameter)
      (PreparedParents.Trace.defined row result.traced.path) stage.observations.request stage.observations.closed)

/-- The actual old vertex request is exactly the intended original bank request, with all old observations unchanged. -/
theorem observed_accuracy : stage.partition.observed.observations.accuracy = Bank.Quarter.request depth :=
  (congrArg (fun closed : Primitive.Closed result.traced.path
      (PreparedParents.Trace.defined row result.traced.path) result.join stage.observations.request =>
      closed.observations.accuracy) stage.partition_observed).trans
    (Primitive.Closed.Requested.accuracy_eq stage.observations)

end Stage

/-- Fixed original Taylor/cell ceilings and the exact joint bank/vertex allocation determine this contraction scale. -/
@[expose] def scale : Rational :=
  450 + 16 * Bank.Circuit.ceilingSum (specification := specification) source

/-- The computed contraction scale is nonnegative from the actual original bank cell ceilings. -/
theorem scale_nonnegative : 0 ≤ scale row source := by
  have base : (0 : Rational) ≤ 450 := by
    change (0 : Rational) ≤ ((450 : Nat) : Rational)
    exact Cast.Order.natCast_le_direct (m := 0) (n := 450) (Nat.zero_le 450)
  have coefficient : (0 : Rational) ≤ 16 := of_decide_eq_true rfl
  have multiplied := Order.Arithmetic.mul_nonneg_direct coefficient
    (Bank.Circuit.ceilingSum_nonnegative (specification := specification) source)
  have combined : (0 : Rational) + 0 ≤
      450 + 16 * Bank.Circuit.ceilingSum (specification := specification) source :=
    Order.Arithmetic.add_le_add_direct base multiplied
  rewrite [Purelib.Data.Rat.Fraction.zero_add] at combined
  exact combined

namespace Stage

variable {result row source} {depth : Nat}
variable (stage : Stage result row source depth)

include stage in
/-- The same actual old bank/vertex requests give a decaying bound on the original curved relation-program sample.

Only the scalar tolerance equality is used in the bound. Neither complete
old observation cache is transported or replaced. The original bank
arithmetic accuracy rho squared and actual old vertex accuracy are equal
because the inverse request was computed before either was observed.
-/
theorem program_sample_le : Norm.Basic.normSq (source.program.model depth).integralSample ≤
    Geometric.Basic.quarterRadius (scale row source) depth := by
  have paid := Curved.program_sample_le stage.partition stage.descended stage.banks stage.compared
  have accuracy := congrArg AccuracyRequest.tolerance stage.observed_accuracy
  rewrite [accuracy] at paid
  let radius := Geometric.Basic.quarterRadius 1 depth
  have radiusNonnegative : 0 ≤ radius :=
    Geometric.Basic.quarterRadius_nonneg (of_decide_eq_true rfl : (0 : Rational) ≤ 1) depth
  have radiusUpper : radius ≤ 1 :=
    Geometric.Basic.quarterRadius_le_scale (of_decide_eq_true rfl : (0 : Rational) ≤ 1) depth
  have squared : radius ^ 2 ≤ radius := by
    calc
      _ = radius * radius := by ring1
      _ ≤ radius * 1 := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusUpper radiusNonnegative
      _ = _ := Field.mul_one_direct _
  have tolerance : (Bank.Quarter.request depth).tolerance = radius ^ 2 := rfl
  rewrite [tolerance] at paid
  have scalar (ceiling radius : Rational) :
      16 * ceiling * radius + 256 * radius ^ 2 + 194 * radius ^ 2 =
        16 * ceiling * radius + 450 * radius ^ 2 := by ring1
  have combined : Norm.Basic.normSq (source.program.model depth).integralSample ≤
      16 * Bank.Circuit.ceilingSum (specification := specification) source * radius +
        450 * radius ^ 2 := paid.trans_eq (scalar _ _)
  have positive : (0 : Rational) ≤ 450 := by
    change (0 : Rational) ≤ ((450 : Nat) : Rational)
    exact Cast.Order.natCast_le_direct (m := 0) (n := 450) (Nat.zero_le 450)
  calc
    _ ≤ 16 * Bank.Circuit.ceilingSum (specification := specification) source * radius +
        450 * radius ^ 2 := combined
    _ ≤ 16 * Bank.Circuit.ceilingSum (specification := specification) source * radius + 450 * radius :=
      Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _)
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared positive)
    _ = _ := by
      unfold scale radius
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

include stage in
/-- An actual joint stage at or beyond the original sufficient depth pays the same curved relation-sample request. -/
theorem requested_sample_lt {current : Nat} (request : AccuracyRequest)
    (selected : Geometric.Search.Selection (scale row source) current request.tolerance)
    (after : selected.stage ≤ depth) :
    Norm.Basic.normSq (source.program.model depth).integralSample < request.tolerance :=
  stage.program_sample_le.trans_lt (selected.later_accurate after)

end Stage

/-- The original finite geometric search computes a sufficient depth from fixed original bank constants. -/
def selection (current : Nat) (request : AccuracyRequest) :
    Geometric.Search.Selection (scale row source) current request.tolerance :=
  Geometric.Search.Selection.build (scale row source) (scale_nonnegative row source)
    current request.tolerance request.positive

namespace Requested

/-- The exact original sufficient-depth result with its complete request/source factory equality. -/
@[expose] def Selection (current : Nat) (request : AccuracyRequest) :=
  { value : Geometric.Search.Selection (scale row source) current request.tolerance //
    value = selection row source current request }

/-- The same joint observation/bank stage with its complete original factory equality at the selected depth. -/
@[expose] def Realization (depth : Nat) :=
  { value : Stage result row source depth // value = Stage.build result row source depth }

end Requested

/-- One requested actual curved relation sample retains its sufficient depth and all jointly chosen old caches.

The original finite search runs before either bank or paid primitive
observation. Its stage then controls both old accuracies through their
original exact request factories. Earlier observations are not reused as
if they had been made at this later depth.
-/
@[expose] def Requested (current : Nat) (request : AccuracyRequest) :=
  Σ selected : Requested.Selection row source current request,
    Requested.Realization result row source selected.val.stage

namespace Requested

/-- Select sufficient original requests first, then build one actual complete joint bank/paid-spine stage. -/
def build (current : Nat) (request : AccuracyRequest) : Requested result row source current request :=
  let selected := selection row source current request
  let stage := Stage.build result row source selected.stage
  ⟨⟨selected, rfl⟩, ⟨stage, rfl⟩⟩

variable {result row source} {current : Nat} {request : AccuracyRequest}
variable (retained : Requested result row source current request)

/-- Read the same complete original sufficient-depth selection, without a repeated search. -/
@[expose] def selected : Geometric.Search.Selection (scale row source) current request.tolerance :=
  retained.1.val

/-- Read the SAME actual joint old bank/spine/closing/endpoint Comparison caches at the retained selected depth. -/
@[expose] def stage : Stage result row source retained.selected.stage := retained.2.val

/-- Read the sample from the SAME retained four bank caches, without another program-model evaluation. -/
@[expose] def sample : Canonical := retained.stage.sample

/-- The actual cached sample reads back to the original program at the identical retained selected depth. -/
theorem sample_eq : retained.sample = (source.program.model retained.selected.stage).integralSample :=
  retained.stage.sample_eq

/-- The stored selection is its original factory on this request and the actual original source-cell constants. -/
theorem selected_eq : retained.selected = selection row source current request := retained.1.property

/-- The complete joint stage is its exact original factory at the SAME retained sufficient depth. -/
theorem stage_eq : retained.stage = Stage.build result row source retained.selected.stage :=
  retained.2.property

/-- The actual original curved relation-program sample strictly pays the caller's request by internal finite bounds. -/
theorem sample_lt : Norm.Basic.normSq retained.sample < request.tolerance := by
  rewrite [retained.sample_eq]
  exact retained.stage.program_sample_le.trans_lt (retained.selected.later_accurate (Nat.le_refl _))

end Requested

end Closure.Result.Curved

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
