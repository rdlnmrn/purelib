module
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-!
# Exact operational owner handoffs for concatenated prepared paths

The labelled endpoint of a lifted path does not by itself identify the root
owner used by the next integration piece.  Extract the actual terminal owner
of the retained preparation and thread that owner through concatenation.
These constructions do not infer root agreement from sheet labels.
-/

namespace Purelib.Riemann.Paths.PreparedPathGluing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (GaussianPolynomial Gaussian Box Owner PreparedPath CompleteSegment zeroEndpoint oneEndpoint)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath
  (CheckedDyadic AllRequestsDyadic AllEdgesProper CertifiedDyadic
    dyadicEdges_strictParameterEdges certify)

section
open Purelib.Polynomial
/-- Concatenation of the original clear paths is associative with their endpoint indices retained. -/
private theorem clearPath_append_assoc {polynomial : GaussianPolynomial} {ambient : Box}
    {first second third fourth : Gaussian}
    (left : Polynomial.Geometry.ClearPath polynomial ambient first second) (middle : Polynomial.Geometry.ClearPath
      polynomial ambient second third)
    (right : Polynomial.Geometry.ClearPath polynomial ambient third fourth) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    change Polynomial.Geometry.ClearPath.cons head _ = Polynomial.Geometry.ClearPath.cons head _; rw [ih]

/-- Read the exact final root owner by following the original prepared path's retained tail owners. -/
@[expose] def finishOwner {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} → {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} →
      {owner : Owner (polynomial.eval start)} → PreparedPath path owner → Owner (polynomial.eval finish)
  | _, _, _, _, .nil _ owner => owner
  | _, _, _, _, .cons _ _ _ _ _ tail => finishOwner tail

/-- Concatenate prepared paths whose shared endpoint uses the first path's exact finish owner.

Each original complete segment, cache and order certificate is retained in sequence; the result starts at the original
source owner. -/
@[expose] def append {polynomial : GaussianPolynomial} {ambient : Box} :
    {start middle finish : Gaussian} →
      {left : Polynomial.Geometry.ClearPath polynomial ambient start middle} →
      {right : Polynomial.Geometry.ClearPath polynomial ambient middle finish} →
      {owner : Owner (polynomial.eval start)} →
      (first : PreparedPath left owner) → PreparedPath right (finishOwner first) →
        PreparedPath (left.append right) owner
  | _, _, _, _, _, _, .nil _ _, second => second
  | _, _, _, _, _, _, .cons head tail owner within preparedHead preparedTail, second =>
      .cons head (tail.append _) owner within preparedHead (append preparedTail second)

/-- Concatenation retains exactly the second prepared path's final root owner. -/
theorem append_finishOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian} {left : Polynomial.Geometry.ClearPath polynomial ambient start middle}
    {right : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
    (first : PreparedPath left owner) (second : PreparedPath right (finishOwner first)) :
    finishOwner (append first second) = (finishOwner second) := by
  induction first with
  | nil => rfl
  | cons head tail owner within preparedHead preparedTail ih => exact ih second

/-- Reading the prepared concatenation's clear path equals concatenating the two original clear-path readbacks. -/
theorem append_toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian} {left : Polynomial.Geometry.ClearPath polynomial ambient start middle}
    {right : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
    (first : PreparedPath left owner) (second : PreparedPath right (finishOwner first)) :
    (append first second).toClearPath = first.toClearPath.append second.toClearPath := by
  induction first with
  | nil => rfl
  | cons head tail owner within preparedHead preparedTail ih =>
      change preparedHead.clearPath.append (append preparedTail second).toClearPath =
        (preparedHead.clearPath.append preparedTail.toClearPath).append second.toClearPath
      rw [ih second, clearPath_append_assoc]
      rfl

end

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The real integral lower reading is additive under owner-aligned prepared-path concatenation. -/
theorem append_integralRealLower {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Basic.Differential genus) (sheet : Fin
      2)
    {ambient : Box} {start middle finish : Gaussian}
    {left : Polynomial.Geometry.ClearPath curve.polynomial ambient start middle} {right : Polynomial.Geometry.ClearPath
      curve.polynomial ambient middle finish}
    {owner : Owner (curve.polynomial.eval start)}
    (first : PreparedPath left owner) (second : PreparedPath right (finishOwner first)) :
    (append first second).integralRealLower curve differential sheet =
      first.integralRealLower curve differential sheet + second.integralRealLower curve differential sheet := by
  induction first with
  | nil =>
      change second.integralRealLower curve differential sheet = 0 + second.integralRealLower curve differential sheet
      exact (_root_.zero_add _).symm
  | cons head tail owner within preparedHead preparedTail ih =>
      change preparedHead.integralRealLower curve differential sheet +
        (append preparedTail second).integralRealLower curve differential sheet = _
      rw [ih second]
      change _ = (preparedHead.integralRealLower curve differential sheet +
        preparedTail.integralRealLower curve differential sheet) + second.integralRealLower curve differential sheet
      exact (Fraction.Field.add_assoc _ _ _).symm

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
open Purelib.Data.List in
/-- Certifying the prepared concatenation gives exactly the concatenation of the original certified cell lists.

Finite induction retains each original head cell and the same prepared tail. Structural list associativity compares
their ordered certified cells without replacing either prepared owner handoff. -/
theorem append_certify_cells {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Basic.Differential genus) (sheet : Fin
      2)
    {ambient : Box} {start middle finish : Gaussian}
    {left : Polynomial.Geometry.ClearPath curve.polynomial ambient start middle} {right : Polynomial.Geometry.ClearPath
      curve.polynomial ambient middle finish}
    {owner : Owner (curve.polynomial.eval start)}
    (first : PreparedPath left owner) (second : PreparedPath right (finishOwner first)) :
    (certify curve differential sheet (append first second)).cells =
      (certify curve differential sheet first).cells ++ (certify curve differential sheet second).cells := by
  induction first with
  | nil => rfl
  | cons head tail owner within preparedHead preparedTail ih =>
      change _ ++ (certify curve differential sheet (append preparedTail second)).cells =
        (_ ++ (certify curve differential sheet preparedTail).cells) ++ (certify curve differential sheet second).cells
      rw [ih second, Append.append_assoc]
      rfl

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- The certified path model's integral sample is additive under owner-aligned prepared concatenation. -/
theorem append_integralSample {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Basic.Differential genus) (sheet : Fin
      2)
    {ambient : Box} {start middle finish : Gaussian}
    {left : Polynomial.Geometry.ClearPath curve.polynomial ambient start middle} {right : Polynomial.Geometry.ClearPath
      curve.polynomial ambient middle finish}
    {owner : Owner (curve.polynomial.eval start)}
    (first : PreparedPath left owner) (second : PreparedPath right (finishOwner first)) :
    (Basic.PathModel.mk (certify curve differential sheet (append first second)).cells).integralSample =
      (Basic.PathModel.mk (certify curve differential sheet first).cells).integralSample +
      (Basic.PathModel.mk (certify curve differential sheet second).cells).integralSample := by
  rw [append_certify_cells]
  exact Basic.PathModel.integralSample_mk_append _ _

namespace CheckedDyadic

open Purelib.Data.Rat
open Purelib.Polynomial
/-- A checked dyadic path's retained preparation has exactly the requests at its original depth and diameter. -/
theorem prepared_generated {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} (checked : CheckedDyadic depth diameter positive path owner) :
    AllRequestsDyadic depth diameter positive checked.prepared := by
  induction checked with
  | nil => trivial
  | cons head tail owner within safe remaining ih =>
      exact ⟨CompleteSegment.ofSafeDyadic_requests head within owner depth diameter positive safe, ih⟩

/-- Every parameter interval retained by a checked dyadic path is strictly increasing. -/
theorem prepared_proper {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} (checked : CheckedDyadic depth diameter positive path owner) :
    AllEdgesProper checked.prepared := by
  induction checked with
  | nil => trivial
  | cons head tail owner within safe remaining ih =>
      refine ⟨?_, ih⟩
      rw [CompleteSegment.ofSafeDyadic_parameterEdges]
      exact dyadicEdges_strictParameterEdges depth zeroEndpoint oneEndpoint (by decide)

/-- Retain a checked dyadic path's exact preparation as a certified cache.

The result preserves ambient containment, request generation, strict parameter ordering, step count and clear-path
readback of the original checked path. -/
@[expose] def cache {polynomial : GaussianPolynomial} {ambient : Box}
    {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {owner : Owner (polynomial.eval start)} (checked : CheckedDyadic depth diameter positive path owner) :
    CertifiedDyadic depth diameter positive path owner where
  within := checked.within
  prepared := checked.prepared
  generated := prepared_generated checked
  prepared_allEdgesProper := prepared_proper checked
  prepared_stepCount := checked.prepared_stepCount
  prepared_toClearPath := checked.prepared_toClearPath_eq_dyadicRefinePath

end CheckedDyadic

end Purelib.Riemann.Paths.PreparedPathGluing
