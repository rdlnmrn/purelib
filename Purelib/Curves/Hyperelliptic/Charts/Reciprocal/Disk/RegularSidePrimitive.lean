module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring
import Purelib.Data.List.Map

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-!
# One signed regular primitive across all retained exterior parents

The actual source-root joins identify the cached parent polynomials. Their
literal paths therefore use one shared polynomial, with each retained
parent's own coarse depth and the common fine depth preserved.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides (Plans Results)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Read dyadic increments of the supplied polynomial along this original parent's inverse source path at its retained
coarse depth plus the supplied fine depth. -/
@[expose] def Preparation.regularPrimitivePath {count : Nat} {parent : PreparedSubdivisionModelCore.CenteredEdge curve
  differential}
    {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch count}
    {cover : UniformReciprocalCover.Cover data} (_prepared : ParentComparison.Preparation regular cover) (value :
      InverseRootPolynomial.Polynomial) (depth : Nat) : List Gaussian :=
  DyadicPrimitivePaths.dyadicIncrements (fun parameter => value.eval (parent.edge.point parameter)⁻¹) (cover.mesh.depth
    + depth) 0 1

namespace SideBank

/-- Pointwise opposite primitive readings give the exact elementwise-negated dyadic increment list.

The two ordered midpoint halves retain the same supplied values; scalar negation changes each original increment without
selecting new endpoints. -/
private theorem increments_neg {firstValues lastValues : InverseRootPolynomial.Coordinate →
  InverseRootPolynomial.Gaussian}
    (opposite : ∀ parameter, firstValues parameter = -lastValues parameter)
    (depth : Nat) (first last : InverseRootPolynomial.Coordinate) :
    DyadicPrimitivePaths.dyadicIncrements firstValues depth first last = (DyadicPrimitivePaths.dyadicIncrements
      lastValues depth first last).map Neg.neg := by
  induction depth generalizing first last with
  | zero =>
      change [firstValues last - firstValues first] = [-(lastValues last - lastValues first)]
      rw [opposite, opposite, show -lastValues last - -lastValues first = -(lastValues last - lastValues first) by
        ring1]
  | succ depth ih =>
    rw [DyadicPrimitivePaths.dyadicIncrements, DyadicPrimitivePaths.dyadicIncrements, Map.map_append, ih, ih]

/-- Read each original parent's dyadic primitive path using one supplied polynomial and the same fine depth. -/
@[expose] def regularPrimitivePaths (value : InverseRootPolynomial.Polynomial) (depth : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    ParentJoins.SideBank regular covers → List (List InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head tail =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath head value depth
    :: regularPrimitivePaths value
    depth tail

/-- Negating the shared polynomial negates every actual retained parent increment. -/
private theorem primitivePaths_neg (value : InverseRootPolynomial.Polynomial) (depth : Nat)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (prepared : ParentJoins.SideBank regular covers) :
    regularPrimitivePaths (-value) depth
      prepared =
      (regularPrimitivePaths value depth
        prepared).map (fun path => path.map Neg.neg) := by
  induction prepared with
  | nil => rfl
  | cons head tail ih =>
      change Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath head
        (-value) depth ::
        regularPrimitivePaths (-value) depth
        tail =
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.Preparation.regularPrimitivePath head value
          depth).map Neg.neg ::
          (regularPrimitivePaths value depth
          tail).map (fun path => path.map Neg.neg)
      exact congrArg₂ List.cons
        (increments_neg (fun _ =>
        DensePolynomial.eval_neg _ _) _ _ _) ih

/-- Flattening elementwise-negated paths gives the elementwise negation of the complete original increment list.

Each original path keeps its occurrence order, and negating the flattened entries agrees with negating each retained
path. -/
private theorem flatten_neg (paths : List (List InverseRootPolynomial.Gaussian)) :
    (paths.map (fun path => path.map Neg.neg)).flatten = paths.flatten.map Neg.neg := by
  induction paths with
  | nil => rfl
  | cons head tail ih => rw [List.map_cons, List.flatten_cons, List.flatten_cons, Map.map_append, ih]

/-- Simultaneously negating the actual origin and every increment preserves the complete trace area. -/
private theorem traceArea_neg (path : List InverseRootPolynomial.Gaussian) (start : InverseRootPolynomial.Gaussian) :
    IncrementArea.traceArea (-start) (path.map Neg.neg) = IncrementArea.traceArea start path := by
  induction path generalizing start with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, IncrementArea.traceArea, IncrementArea.traceArea,
        show -start + -head = -(start + head) by ring1, ih]
      have opposite (first last : InverseRootPolynomial.Gaussian) : BoundaryRibbon.area (-first) (-last) =
        BoundaryRibbon.area first last := by
        apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
          Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
      rw [opposite]

/-- Negating every actual path increment preserves its zero-origin area. -/
private theorem pathArea_neg (path : List InverseRootPolynomial.Gaussian) :
    IncrementArea.pathArea (path.map Neg.neg) = IncrementArea.pathArea path := by
  have same := traceArea_neg path 0
  rw [neg_zero] at same
  exact same

/-- One common sign choice on the shared polynomial preserves the complete retained parent-path area. -/
theorem primitivePaths_signed (value : InverseRootPolynomial.Polynomial) (bit : Bool) (depth : Nat)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (prepared : ParentJoins.SideBank regular covers) :
    IncrementArea.pathArea
      (regularPrimitivePaths (if bit then
      -value else value) depth prepared).flatten =
      IncrementArea.pathArea
        (regularPrimitivePaths value depth
        prepared).flatten := by
  cases bit with
  | false => rfl
  | true =>
      change IncrementArea.pathArea
        (regularPrimitivePaths (-value) depth
        prepared).flatten = _
      rw [primitivePaths_neg,
        flatten_neg,
        pathArea_neg]

namespace Regular.Results

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Coordinate} {minimum index depth readingIndex : Nat}
  {box : Purelib.Geometry.Rational.Box} {sample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the first actual retained regular primitive, using the original sample primitive for an empty bank. -/
@[expose] def primitive : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : RegularSides.Plans requests} → {evaluated : SideBank.Evaluations sample depth readingIndex requests} →
    RegularSides.Results plans evaluated → InverseRootPolynomial.Polynomial
  | _, _, _, _, _, .nil, _ => sample.primitive.value
  | _, _, _, _, _, .cons _ _, results => results.1.primitive

/-- Every actual retained regular parent result uses this exact supplied polynomial primitive. -/
@[expose] def WithPrimitive (value : InverseRootPolynomial.Polynomial) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers : UniformReciprocalCover.ParentCovers
  parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : RegularSides.Plans requests} → {evaluated : SideBank.Evaluations sample depth readingIndex requests} →
    RegularSides.Results plans evaluated → Prop
  | _, _, _, _, _, .nil, _ => True
  | _, _, _, _, _, .cons _ _, results => results.1.primitive = value ∧
    WithPrimitive
    value results.2

variable {parents : List (CenteredEdge curve differential)}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {prepared : SideBank regular covers} {requests :
    Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}
  {plans : Plans requests} {evaluated :
    Evaluations sample depth readingIndex
    requests}

/-- Actual original root joins identify all retained regular parent primitives with the first one. -/
theorem shared (results : RegularSides.Results plans evaluated) (links : SideBank.Links prepared) :
  WithPrimitive
  (primitive results) results
  := by
  induction evaluated with
  | nil => trivial
  | cons head tail ih =>
      cases tail with
      | nil => exact ⟨rfl, trivial⟩
      | cons next rest =>
          cases links with
          | cons joined remaining =>
              have same := RegularEndpoint.join results.1.last results.2.1.first joined
                (head.original_index.trans next.original_index.symm) (head.capSample_eq.trans next.capSample_eq.symm)
                  results.1.ready
              refine ⟨rfl, ?_⟩
              change
                WithPrimitive
                results.1.primitive results.2
              rw [same]
              exact ih results.2 remaining

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.Regular.Results in
/-- The complete retained cap-path bank is exactly the actual parent subdivision evaluated with its shared polynomial.
-/
theorem cap_paths (results : RegularSides.Results plans evaluated) (value : InverseRootPolynomial.Polynomial) (shared :
  WithPrimitive value results)
  :
    results.pairs.map Prod.snd =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths value depth
      prepared := by
  induction evaluated with
  | nil => rfl
  | @cons parent remaining patch data cover covers prepared tail request requests head rest ih =>
      have path := RegularCells.cap_path_eq cover.mesh results.1.cells prepared.owners prepared.links results.1.ready
      rw [← results.1.primitive_eq, shared.1] at path
      change (results.1.cells.pairs.map Prod.snd).flatten :: (Results.pairs results.2).map Prod.snd = _
      exact congrArg₂ List.cons path (ih results.2 shared.2)

/-- Read the first actual retained parent's sign bit, using false for an empty bank. -/
@[expose] def flip : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : RegularSides.Plans requests} → {evaluated : SideBank.Evaluations sample depth readingIndex requests} →
    RegularSides.Results plans evaluated → Bool
  | _, _, _, _, _, .nil, _ => false
  | _, _, _, _, _, .cons _ _, results => RegularCells.flip results.1.cells

/-- Equal retained sample indices and identical dependent sample owners give the same cached polynomial primitive. -/
private theorem sample_primitive_eq {leftIndex rightIndex : Nat}
    (left : Primitives.Sample cap differential leftIndex box)
    (right : Primitives.Sample cap differential rightIndex box)
    (indices : leftIndex = rightIndex) (same : HEq left right) : left.primitive.value = right.primitive.value := by
  cases indices
  cases eq_of_heq same
  rfl

/-- The actual shared regular primitive is the original sample primitive with its retained common sign bit. -/
theorem primitive_signed (results : RegularSides.Results plans evaluated) :
    primitive results = if
      flip results then
      -sample.primitive.value else sample.primitive.value := by
  cases evaluated with
  | nil => rfl
  | cons head tail =>
      have same :=
        sample_primitive_eq
        head.capSample sample head.original_index head.capSample_eq
      change results.1.primitive = if RegularCells.flip results.1.cells then -sample.primitive.value else
        sample.primitive.value
      rw [results.1.primitive_eq, RegularCells.primitive_signed results.1.cells, same]

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.Regular.Results in
/-- Every parent and cross term now uses the same cap polynomial as the energy construction, while retaining its actual
nonuniform subdivision. -/
theorem cap_area_unsigned (results : RegularSides.Results plans evaluated) (links : SideBank.Links prepared) :
    results.capSummary.area = IncrementArea.pathArea
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.regularPrimitivePaths
      sample.primitive.value depth prepared).flatten := by
  rw [results.capSummary.area_eq,
    cap_paths results
    (primitive results)
    (shared results links),
    primitive_signed results]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive.SideBank.primitivePaths_signed _ _ _ _

end Regular.Results
end SideBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
