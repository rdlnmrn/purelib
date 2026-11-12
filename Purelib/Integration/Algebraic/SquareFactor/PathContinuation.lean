module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Inherited square-root continuation on the retained parameter path

The cached polynomial `Q(t)=q(start+t*(finish-start))` is evaluated on the
real unit segment.  This uses the existing genus-independent Rouché owner
machinery without changing the original path or inventing a holomorphic
basis index.  The input checker supplies its quantitative clearance, and
the existing finite algorithm computes a sufficient continuation mesh.

Only the initial root owner is selected independently.  Every later owner
in the returned subdivision is inherited from its predecessor.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.PathContinuation

open Purelib.Data.Nat

open Purelib

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for continuation parameters and diameter requests. -/
abbrev Coordinate := Fraction.Rational
/-- The original square-root continuation owner carrier indexed by its exact target value. -/
abbrev Owner := SquareRootContinuationChain.Owner
/-- The retained in-unit endpoint carrier used by sheet subdivision. -/
abbrev Endpoint := ClearSheetContinuation.Subdivision.Endpoint

variable {polynomial : GaussianPolynomial} {request :
  Request}
  {prepared : Prepared polynomial request} {segment :
    Segment}

/-- The certified parameter-zero endpoint. -/
@[expose] def first : Endpoint := ⟨0, by decide⟩
/-- The certified parameter-one endpoint. -/
@[expose] def last : Endpoint := ⟨1, by decide⟩

section
open Purelib
open Purelib.Data.Gaussian
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches
/-- Use the exact retained positive radicand margin as horizontal parameter-line clearance. -/
@[expose] def parameterClearance {data : Data prepared segment} (safe : data.Safe) :
    Polynomial.Clearance.Box.Line.Basic.HorizontalLineClearance data.radicand.parameterPolynomial
      ClearSheetContinuation.parameterAmbient 0 where
  bound := data.radicand.lowerBound
  positive := safe.radicandPositive
  lower := by
    intro parameter lower upper
    have scalar := data.radicand.lowerBound_le_value (parameter := parameter) ⟨lower, upper⟩
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-- Construct the cleared horizontal unit-parameter segment for the original radicand parameter polynomial. -/
@[expose] def clearSegment {data : Data prepared segment} (safe : data.Safe) :
    Polynomial.Geometry.ClearPath.ClearSegment data.radicand.parameterPolynomial
      ClearSheetContinuation.parameterAmbient (Components.Basic.point 0 0) (Components.Basic.point 1 0) :=
  .horizontal 0 1 0 (by decide) (by decide) (by decide) (by decide) (parameterClearance safe)

end

open Purelib.Integration.Algebraic.SquareFactor in
/-- The constructed parameter segment lies inside the original parameter ambient box. -/
theorem within {data : Data prepared segment} (safe : data.Safe) :
    (clearSegment safe).WithinAmbient := ⟨le_rfl, le_rfl⟩

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Reading the cleared parameter segment gives the exact real-coordinate Gaussian embedding. -/
theorem pointAt_eq {data : Data prepared segment} (safe : data.Safe) (parameter : Coordinate)
  :
    (clearSegment safe).pointAt parameter = Cast.Path.ofCoordinate parameter := by
  apply Basic.ext <;>
    simp only [Polynomial.Geometry.ClearPath.ClearSegment.pointAt, Scale.scale_re, Scale.scale_im,
      Components.Basic.point, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1

open Purelib.Integration.Algebraic.SquareFactor in
/-- The cleared parameter polynomial reading equals the original radicand at the physical segment point. -/
theorem radicand_eq {data : Data prepared segment} (safe : data.Safe) (parameter :
  Coordinate) :
    data.radicand.parameterPolynomial.eval ((clearSegment safe).pointAt parameter) =
      prepared.reduction.radicand.eval (segment.point parameter) := by
  rw [pointAt_eq]
  exact data.radicand.value_eq parameter

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Topology in
/-- Construct the original starting square-root owner for the supplied sheet using the retained nonzero radicand margin.
-/
@[expose] def initialOwner {data : Data prepared segment} (safe : data.Safe) (sheet : Fin 2) :
    Owner (data.radicand.parameterPolynomial.eval ((clearSegment safe).pointAt
      PathContinuation.first.parameter)) :=
  SquareRootContinuationChain.Owner.independent (by
    rw [radicand_eq]
    exact safe.radicand_nonzero PathContinuation.first.inside) sheet

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- The maximum of the certified sufficient dyadic depth and the requested minimum depth. -/
@[expose] def maximumDepth {data : Data prepared segment} (safe : data.Safe)
    (rootDiameter : Coordinate) (minimumDepth : Nat) : Nat :=
  max (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth (clearSegment safe)
    PathContinuation.first last rootDiameter) minimumDepth

set_option genInjectivity false in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- A retained accepted dyadic subdivision tied to the exact original starting owner and diameter request.

Its actual depth lies between the requested minimum and the derived sufficient maximum, and its acceptance equation
names the exact checked run. -/
structure SelectedMesh {data : Data prepared segment} (safe : data.Safe)
    (owner : Owner (data.radicand.parameterPolynomial.eval ((clearSegment
      safe).pointAt PathContinuation.first.parameter)))
    (rootDiameter : Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat) where
  /-- The actual selected dyadic subdivision depth. -/ depth : Nat
  /-- The selected depth is at least the original requested minimum. -/ minimumDepth_le : minimumDepth ≤ depth
  /-- The selected depth does not exceed the derived sufficient maximum. -/ depth_le_maximum : depth ≤
    maximumDepth safe rootDiameter minimumDepth
  /-- The exact retained subdivision run indexed by the original starting owner. -/ run :
    PreparedSheetContinuation.Subdivision (clearSegment safe) (within safe)
    PathContinuation.first owner
  /-- The checker at the retained depth and original diameter request returns this exact run. -/ accepted :
    PreparedSheetContinuation.Subdivision.tryDyadic (clearSegment safe) (within safe)
    PathContinuation.first last owner depth rootDiameter positive = some run

constructive_injectivity SelectedMesh

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Search successive dyadic depths while retaining the exact original owner, diameter request and bounded remaining
range.

An accepted attempt returns its original run. At the sufficient final depth, the mathematical safety certificate
constructs and certifies the checked subdivision. -/
@[expose] def searchMesh {data : Data prepared segment} (safe : data.Safe)
    (owner : Owner (data.radicand.parameterPolynomial.eval ((clearSegment
      safe).pointAt PathContinuation.first.parameter)))
    (rootDiameter : Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat)
    (depth : Nat) : (remaining : Nat) → minimumDepth ≤ depth →
      maximumDepth safe rootDiameter minimumDepth = depth + remaining →
      SelectedMesh safe owner rootDiameter positive minimumDepth
  | 0, minimum, upper => by
      have sufficient : PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
          (clearSegment safe) PathContinuation.first last rootDiameter ≤ depth := by
        have bound := Order.le_max_left
          (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
            (clearSegment safe) PathContinuation.first last rootDiameter) minimumDepth
        rw [← Order.max_eq_natMax] at bound
        change _ ≤ maximumDepth safe rootDiameter minimumDepth at bound
        rw [upper, Nat.add_zero] at bound
        exact bound
      let safety := PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le
        (clearSegment safe) PathContinuation.first last owner depth rootDiameter
          positive (by decide) sufficient
      exact
        { depth
          minimumDepth_le := minimum
          depth_le_maximum := by omega
          run := PreparedSheetContinuation.Subdivision.checkedDyadic (clearSegment safe)
            (within safe) PathContinuation.first last owner depth rootDiameter
              positive safety
          accepted := PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic
            (clearSegment safe) (within safe) PathContinuation.first
              last owner depth rootDiameter positive safety }
  | remaining + 1, minimum, upper =>
      match found : PreparedSheetContinuation.Subdivision.tryDyadic (clearSegment safe)
          (within safe) PathContinuation.first last owner depth rootDiameter positive
            with
      | some run =>
          { depth
            minimumDepth_le := minimum
            depth_le_maximum := by omega
            run
            accepted := found }
      | none => PathContinuation.searchMesh safe owner rootDiameter positive
        minimumDepth (depth + 1)
          remaining (by omega) (by omega)

open Purelib.Integration.Algebraic.SquareFactor in
/-- Search from the requested minimum using the same retained starting root owner.

The supplied owner is passed to every checked subdivision and retained in
the selected mesh. No independent root isolation is performed.
-/
@[expose] def selectMeshFromOwner {data : Data prepared segment} (safe : data.Safe)
    (owner : Owner (data.radicand.parameterPolynomial.eval
      ((clearSegment safe).pointAt PathContinuation.first.parameter)))
    (rootDiameter : Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat) :
    SelectedMesh safe owner rootDiameter positive minimumDepth :=
  searchMesh safe owner rootDiameter positive minimumDepth minimumDepth
    (maximumDepth safe rootDiameter minimumDepth - minimumDepth) le_rfl (by
      have bound : minimumDepth ≤ maximumDepth safe rootDiameter minimumDepth := by
        unfold maximumDepth
        rw [Order.max_eq_natMax]
        exact Order.le_max_right _ _
      omega)

open Purelib.Integration.Algebraic.SquareFactor in
/-- Search from the requested minimum depth using the original independently selected starting sheet owner.

The finite search stops no later than the retained sufficient depth and returns an accepted run with its exact owner and
request indices. -/
@[expose] def selectMesh {data : Data prepared segment} (safe : data.Safe) (sheet : Fin 2)
    (rootDiameter : Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat) :
    SelectedMesh safe (initialOwner safe sheet) rootDiameter positive minimumDepth :=
  selectMeshFromOwner safe (initialOwner safe sheet)
    rootDiameter positive minimumDepth

namespace SelectedMesh

/-- Transport the selected mesh to an equal original starting owner without rebuilding its retained subdivision. -/
@[expose] def castOwner {data : Data prepared segment} {safe : data.Safe}
    {first second : Owner (data.radicand.parameterPolynomial.eval
      ((clearSegment safe).pointAt PathContinuation.first.parameter))}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (equal : first = second) (mesh : SelectedMesh safe first rootDiameter positive minimumDepth) :
    SelectedMesh safe second rootDiameter positive minimumDepth := by
  cases equal
  exact mesh

variable {data : Data prepared segment} {safe : data.Safe}
  {owner : Owner (data.radicand.parameterPolynomial.eval
    ((clearSegment safe).pointAt
    PathContinuation.first.parameter))}
  {rootDiameter : Coordinate} {positive : 0 < rootDiameter}
    {minimumDepth : Nat}
  (mesh : SelectedMesh safe owner rootDiameter positive
    minimumDepth)

section
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches
/-- The accepted retained subdivision ends at the original parameter-one endpoint. -/
theorem endpoint : mesh.run.endpoint = last :=
  PreparedSheetContinuation.Subdivision.tryDyadic_endpoint (clearSegment safe) (within
    safe)
    PathContinuation.first last owner mesh.depth rootDiameter positive mesh.accepted

/-- The retained accepted subdivision has exactly two to the power of its selected depth steps. -/
theorem stepCount : mesh.run.stepCount = 2 ^ mesh.depth :=
  PreparedSheetContinuation.Subdivision.tryDyadic_stepCount (clearSegment safe)
    (within safe)
    PathContinuation.first last owner mesh.depth rootDiameter positive mesh.accepted

end

/-- The retained subdivision's terminal parameter reads the original physical segment finish. -/
theorem physical_finish : segment.point mesh.run.endpoint.parameter = segment.finish := by
  rw [mesh.endpoint]
  exact segment.point_one

end SelectedMesh

end Purelib.Integration.Algebraic.SquareFactor.PathContinuation
