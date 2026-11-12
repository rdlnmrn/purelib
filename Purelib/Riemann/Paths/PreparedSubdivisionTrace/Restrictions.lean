module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Axis
import Purelib.Data.Gaussian.Scale
import Purelib.Tactic.Ring

/-! # Polynomial cells on the actual three-link subdivision trace

Each accepted original request keeps its actual source/moving/retention
trace view and three polynomial restriction caches. Repeated stationary
roles remain separate entries. The literal following trace is reused;
no query, continuation, reserve reset or trace factory is executed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} (budget : PreparedTraceBudget segment first last) (cell : CellModel)

/-- One actual polynomial restriction cache on two original retained subdivision endpoints. -/
@[expose] def CellAt (first last : Endpoint) :=
  {cached : Cached cell.polynomial (Cast.Path.ofCoordinate first.parameter)
      (Cast.Path.ofCoordinate last.parameter) //
    cached = Cached.canonical cell.polynomial (Cast.Path.ofCoordinate first.parameter)
      (Cast.Path.ofCoordinate last.parameter)}

namespace CellAt

/-- Materialize a restriction on these exact original endpoint parameters once. -/
def build (first last : Endpoint) : CellAt cell first last :=
  ⟨Cached.canonical cell.polynomial (Cast.Path.ofCoordinate first.parameter)
    (Cast.Path.ofCoordinate last.parameter), rfl⟩

variable {first last : Endpoint} (cached : CellAt cell first last)

/-- The actual model reads this same stored restriction table and original source allowance. -/
@[expose] def model : CellModel := Cell.Restriction.model cell cached.val

/-- The actual sample reads this same stored unit integral with its physical displacement. -/
@[expose] def sample : Canonical := (model cell cached).displacement * cached.val.sample

/-- The cached sample is the exact original source integral on its same retained parameter interval. -/
theorem sample_eq : sample cell cached = cell.displacement * Integral.definiteIntegral cell.polynomial
    (Cast.Path.ofCoordinate first.parameter) (Cast.Path.ofCoordinate last.parameter) :=
  (congrArg (fun value : Canonical => (model cell cached).displacement * value) cached.val.sample_eq).trans
    (Cell.Restriction.integralSample_eq cell cached.val)

/-- The stored model starts and finishes at the exact original source parameters. -/
theorem endpoints : (model cell cached).start = cell.point first.parameter ∧
    (model cell cached).finish = cell.point last.parameter := ⟨rfl, rfl⟩

end CellAt

/-- The SAME source cell and retained segment have identical physical parameter points. -/
theorem point_eq_segment (sourceStart : cell.start = start) (sourceFinish : cell.finish = finish)
    (time : Rational) : cell.point time = segment.pointAt time := by
  unfold CellModel.point CellModel.displacement
  rewrite [sourceStart, sourceFinish]
  change start + Cast.Path.ofCoordinate time * (finish - start) =
    start + Scale.scale time (finish - start)
  exact congrArg (fun value : Canonical => start + value) (Scale.scalar_mul_eq_scale time (finish - start))

/-- Three actual model caches and a literal trace view per original accepted request, followed by its SAME tail. -/
@[expose] def Restrictions :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (fits : budget.RequestsFit current subdivision.requests) (_trace : Trace budget subdivision fits), Type
  | _, _, .stop _ _, _, _ => PUnit
  | _, _, .next current inherited request cached ordered small remaining, fits, trace =>
      (view : View budget current inherited request cached ordered small remaining fits trace) ×
      CellAt cell current current × CellAt cell current request.endpoint ×
      CellAt cell request.endpoint request.endpoint ×
      Restrictions remaining fits.2.2 view.tailTrace
termination_by structural _ _ subdivision _ _ => subdivision

namespace Restrictions

variable {budget cell}

/-- Materialize the same actual trace views and each finite polynomial restriction once in original request order. -/
def build {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (fits : budget.RequestsFit current subdivision.requests) (trace : Trace budget subdivision fits) :
    Restrictions budget cell subdivision fits trace :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) → Restrictions budget cell subdivision fits trace)
    subdivision
    (fun _ _ _ _ => PUnit.unit)
    (fun current _ request _ _ _ remaining fits trace =>
      let view := View.build trace
      let source := CellAt.build cell current current
      let moving := CellAt.build cell current request.endpoint
      let retained := CellAt.build cell request.endpoint request.endpoint
      let following := build remaining fits.2.2 view.tailTrace
      ⟨view, source, moving, retained, following⟩)
    fits trace
termination_by structural subdivision

/-- Read every stored model in actual source/moving/retention order, including all stationary repetitions. -/
@[expose] def cells :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
      Restrictions budget cell subdivision fits trace → List CellModel
  | _, _, .stop _ _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ _, _, _, kept =>
      CellAt.model cell kept.2.1 :: CellAt.model cell kept.2.2.1 :: CellAt.model cell kept.2.2.2.1 ::
        cells kept.2.2.2.2
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Sum the same three retained integral caches per actual accepted request in their exact old trace order. -/
@[expose] def sample :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
      Restrictions budget cell subdivision fits trace → Canonical
  | _, _, .stop _ _, _, _, _ => 0
  | _, _, .next _ _ _ _ _ _ _, _, _, kept =>
      CellAt.sample cell kept.2.1 + CellAt.sample cell kept.2.2.1 + CellAt.sample cell kept.2.2.2.1 +
        sample kept.2.2.2.2
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Four same-source interval integrals telescope, retaining the two repeated endpoint roles. -/
private theorem step_integral (first middle last : Canonical) :
    cell.displacement * Integral.definiteIntegral cell.polynomial first first +
      cell.displacement * Integral.definiteIntegral cell.polynomial first middle +
      cell.displacement * Integral.definiteIntegral cell.polynomial middle middle +
      cell.displacement * Integral.definiteIntegral cell.polynomial middle last =
        cell.displacement * Integral.definiteIntegral cell.polynomial first last := by
  unfold Integral.definiteIntegral
  ring1

/-- The SAME stored restrictions recover the original source integral on the actual subdivision endpoints. -/
theorem sample_eq :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
      (kept : Restrictions budget cell subdivision fits trace),
      sample kept = cell.displacement * Integral.definiteIntegral cell.polynomial
        (Cast.Path.ofCoordinate current.parameter) (Cast.Path.ofCoordinate subdivision.endpoint.parameter)
  | _, _, .stop _ _, _, _, _ => by
      change (0 : Canonical) = _
      rewrite [Subdivision.endpoint_stop]
      unfold Integral.definiteIntegral
      ring1
  | _, _, .next current _ request _ _ _ remaining, _, _, kept => by
      rewrite [Subdivision.endpoint_next]
      change CellAt.sample cell kept.2.1 + CellAt.sample cell kept.2.2.1 + CellAt.sample cell kept.2.2.2.1 +
        sample kept.2.2.2.2 = _
      exact (congrArg (fun value : Canonical => value + sample kept.2.2.2.2)
        (congrArg₂ (fun first last : Canonical => first + last)
          (congrArg₂ (fun first last : Canonical => first + last)
            (CellAt.sample_eq cell kept.2.1) (CellAt.sample_eq cell kept.2.2.1))
          (CellAt.sample_eq cell kept.2.2.2.1))).trans
        ((congrArg (fun value : Canonical =>
          cell.displacement * Integral.definiteIntegral cell.polynomial
              (Cast.Path.ofCoordinate current.parameter) (Cast.Path.ofCoordinate current.parameter) +
            cell.displacement * Integral.definiteIntegral cell.polynomial
              (Cast.Path.ofCoordinate current.parameter) (Cast.Path.ofCoordinate request.endpoint.parameter) +
            cell.displacement * Integral.definiteIntegral cell.polynomial
              (Cast.Path.ofCoordinate request.endpoint.parameter) (Cast.Path.ofCoordinate request.endpoint.parameter) +
            value) (sample_eq kept.2.2.2.2)).trans
          (step_integral (cell := cell) (Cast.Path.ofCoordinate current.parameter)
            (Cast.Path.ofCoordinate request.endpoint.parameter)
            (Cast.Path.ofCoordinate remaining.endpoint.parameter)))
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- The same three models have the actual source/moving/retention link endpoints at every retained trace view. -/
@[expose] def Follows :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
      Restrictions budget cell subdivision fits trace → Prop
  | _, _, .stop _ _, _, _, _ => True
  | _, _, .next current _ _ _ _ _ _, _, _, kept =>
      (CellAt.model cell kept.2.1).start = segment.pointAt current.parameter ∧
      (CellAt.model cell kept.2.1).finish = kept.1.source.point ∧
      (CellAt.model cell kept.2.2.1).start = kept.1.source.point ∧
      (CellAt.model cell kept.2.2.1).finish = kept.1.moving.point ∧
      (CellAt.model cell kept.2.2.2.1).start = kept.1.moving.point ∧
      (CellAt.model cell kept.2.2.2.1).finish = kept.1.tail.point ∧
      Follows kept.2.2.2.2
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Original source endpoint identities derive every actual retained per-link model endpoint internally.

The trace view supplies exact point and whole-Owner identities independently
of these coordinate facts. Every source and retention slot remains present,
even when its endpoints coincide with a neighboring role.
-/
theorem follows (sourceStart : cell.start = start) (sourceFinish : cell.finish = finish) :
    ∀ {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
      {subdivision : Subdivision segment within current owner}
      {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
      (kept : Restrictions budget cell subdivision fits trace), Follows kept
  | _, _, .stop _ _, _, _, _ => True.intro
  | _, _, .next current _ request _ _ _ _, _, _, kept => by
      have firstPoint := point_eq_segment (segment := segment) cell sourceStart sourceFinish current.parameter
      have lastPoint := point_eq_segment (segment := segment) cell sourceStart sourceFinish request.endpoint.parameter
      exact ⟨firstPoint, firstPoint.trans kept.1.source_point.symm,
        firstPoint.trans kept.1.source_point.symm, lastPoint.trans kept.1.moving_point.symm,
        lastPoint.trans kept.1.moving_point.symm, lastPoint.trans kept.1.tail_point.symm,
        follows sourceStart sourceFinish kept.2.2.2.2⟩
termination_by structural _ _ subdivision _ _ _ => subdivision

end Restrictions

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace

end
