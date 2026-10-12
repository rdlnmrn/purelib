module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests

open Purelib.Integration.Path

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-!
# Shared primitive witnesses independent of local request budgets

Extract endpoint and literal-path certificates from existing regular cap
results. Their concatenation retains the supplied banks and paths, allowing
the period's actual root joins to identify one signed primitive throughout.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints (RegularEndpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank (Requests Evaluations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides (Plans Results)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {index otherIndex depth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential otherIndex box}

namespace RegularWitnesses

/-- Transport the retained regular endpoint certificate along equality of its original cap sample and model index. -/
@[expose] public def castEndpoint {edge : ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
  UniformReciprocalCover.Cell
  data edge}
    {model : UniformReciprocalRootChannels.RootModel cell} {parameter : InverseRootPolynomial.Coordinate}
    {point : ArcOwners.Point cap model parameter} {value : InverseRootPolynomial.Polynomial}
    (endpoint : RegularEndpoints.RegularEndpoint regular sample point value) (indices : index = otherIndex) (same : HEq
      sample otherSample) :
    RegularEndpoints.RegularEndpoint regular otherSample point value := by
  cases indices
  cases eq_of_heq same
  exact endpoint

/-- Equal original cap samples retain exactly the same primitive polynomial. -/
public theorem samplePrimitive_eq (indices : index = otherIndex) (same : HEq sample otherSample) :
    sample.primitive.value = otherSample.primitive.value := by
  cases indices
  cases eq_of_heq same
  rfl

set_option genInjectivity false in
/-- The path is an index: extraction does not evaluate or flatten another primitive path merely to recover its
explanatory certificates. -/
structure RegularWitness (prepared : ParentComparison.Preparation regular cover)
    (sample : Primitives.Sample cap differential index box) (depth : Nat) (path : List InverseRootPolynomial.Gaussian)
      where
  /-- The actual signed primitive polynomial already retained by this parent result. -/ primitive :
    InverseRootPolynomial.Polynomial
  /-- The original first endpoint certificate on this exact retained primitive. -/ first :
    RegularEndpoints.RegularEndpoint regular sample prepared.boundary.first.point primitive
  /-- The original terminal endpoint certificate on that same retained primitive. -/ last :
    RegularEndpoints.RegularEndpoint regular sample prepared.boundary.last.point primitive
  /-- The indexed actual path equals the original prepared regular primitive path at the retained depth. -/ path_eq :
    path = Preparation.regularPrimitivePath prepared primitive depth
  /-- The actual sign choice of this retained parent primitive. -/ flip : Bool
  /-- The retained polynomial is exactly the original cap primitive with its cached sign. -/ primitive_signed :
    primitive = if flip then -sample.primitive.value else sample.primitive.value
  /-- The original common cap-sample stage is at least two. -/ ready : 2 ≤ index

constructive_injectivity RegularWitness

end RegularWitnesses

section SideBank

set_option genInjectivity false in
/-- The ordered bank of actual regular primitive witnesses indexed by the original side bank and literal retained paths.
-/
inductive RegularWitnesses (sample : Primitives.Sample cap differential index box) (depth : Nat) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} →
    ParentJoins.SideBank regular covers → List (List InverseRootPolynomial.Gaussian) → Type 2
  /-- The empty original side bank retains an empty primitive-witness path list. -/ | nil :
    RegularWitnesses sample depth .nil []
  /-- Retain one original parent's regular primitive witness before the exact remaining side bank and paths. -/ | cons
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch
        genus}
      {cover : UniformReciprocalCover.Cover data} {covers : UniformReciprocalCover.ParentCovers parents}
      {prepared : ParentComparison.Preparation regular cover} {bank : ParentJoins.SideBank regular covers} {path : List
        InverseRootPolynomial.Gaussian} {paths : List (List InverseRootPolynomial.Gaussian)}
      (head : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.RegularWitness prepared sample depth path)
        (tail : RegularWitnesses sample
        depth bank paths) :
      RegularWitnesses sample depth (.cons
        prepared bank) (path :: paths)

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity RegularWitnesses

namespace RegularWitnesses

/-- Concatenate the actual retained side witness banks and their original literal path lists. -/
@[expose] def append : {first last : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {firstCovers : UniformReciprocalCover.ParentCovers first} → {lastCovers : UniformReciprocalCover.ParentCovers last}
      →
    {firstBank : ParentJoins.SideBank regular firstCovers} → {lastBank : ParentJoins.SideBank regular lastCovers} →
    {firstPaths lastPaths : List (List InverseRootPolynomial.Gaussian)} →
      RegularWitnesses sample depth firstBank
      firstPaths →
    RegularWitnesses sample depth lastBank
      lastPaths → RegularWitnesses sample depth
      (firstBank.append lastBank) (firstPaths ++ lastPaths)
  | _, _, _, _, _, _, _, _, .nil, last => last
  | _, _, _, _, _, _, _, _, .cons head tail, last => .cons head
    (append tail last)

/-- Read the first actual retained primitive, using the original cap primitive for an empty bank. -/
@[expose] def primitive : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {bank : ParentJoins.SideBank regular covers} → {paths : List (List InverseRootPolynomial.Gaussian)} →
      RegularWitnesses sample depth bank paths →
      InverseRootPolynomial.Polynomial
  | _, _, _, _, .nil => sample.primitive.value
  | _, _, _, _, .cons head _ => head.primitive

/-- Every actual retained parent witness uses the supplied original primitive polynomial. -/
@[expose] def WithPrimitive (value : InverseRootPolynomial.Polynomial) : {parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {covers : UniformReciprocalCover.ParentCovers parents} → {bank : ParentJoins.SideBank regular covers} →
    {paths : List (List InverseRootPolynomial.Gaussian)} →
      RegularWitnesses sample depth bank paths →
      Prop
  | _, _, _, _, .nil => True
  | _, _, _, _, .cons head tail => head.primitive = value ∧ tail.WithPrimitive value

variable {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {paths : List (List
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian)}

/-- The original root-join certificates identify one common retained primitive throughout the actual side bank. -/
theorem shared (witnesses : RegularWitnesses
  sample depth bank paths) (links : SideBank.Links bank) :
    witnesses.WithPrimitive witnesses.primitive := by
  induction witnesses with
  | nil => trivial
  | cons head tail ih =>
      cases tail with
      | nil => exact ⟨rfl, trivial⟩
      | cons next rest =>
          cases links with
          | cons joined remaining =>
              have equal := head.last.join next.first joined rfl (HEq.rfl) head.ready
              refine ⟨rfl, ?_⟩
              change
                WithPrimitive
                head.primitive (.cons next rest)
              rw [equal]
              exact ih remaining

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses in
/-- A common retained primitive identifies the exact original list of regular paths. -/
theorem paths_eq (witnesses : RegularWitnesses
  sample depth bank paths) (value : InverseRootPolynomial.Polynomial)
    (shared : witnesses.WithPrimitive value) : paths = SideBank.regularPrimitivePaths value depth bank := by
  induction witnesses with
  | nil => rfl
  | cons head tail ih =>
      simp only [SideBank.regularPrimitivePaths]
      rw [head.path_eq, shared.1, ih shared.2]

/-- Read the first actual retained sign, using the unsigned sign for an empty bank. -/
@[expose] def flip : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {bank : ParentJoins.SideBank regular covers} → {paths : List (List InverseRootPolynomial.Gaussian)} →
      RegularWitnesses sample depth bank paths →
      Bool
  | _, _, _, _, .nil => false
  | _, _, _, _, .cons head _ => head.flip

/-- The selected shared primitive equals the original cap primitive with the retained first sign. -/
theorem primitive_signed (witnesses :
  RegularWitnesses sample depth bank paths) :
    witnesses.primitive = if witnesses.flip then -sample.primitive.value else sample.primitive.value := by
  cases witnesses with
  | nil => rfl
  | cons head tail => exact head.primitive_signed

/-- The full actual regular-path area equals the area using the original unsigned cap primitive. -/
theorem area_unsigned (witnesses :
  RegularWitnesses sample depth bank paths) (links
  : SideBank.Links bank) :
    IncrementArea.pathArea paths.flatten =
      IncrementArea.pathArea (SideBank.regularPrimitivePaths sample.primitive.value depth bank).flatten := by
  rw [witnesses.paths_eq witnesses.primitive (witnesses.shared links), witnesses.primitive_signed]
  exact SideBank.primitivePaths_signed _ _ _ _

end RegularWitnesses

namespace RegularWitnesses.SideBank.Regular.Results

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum readingIndex : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.SideBank.Regular.Results in
/-- Extract the actual retained endpoint and literal-path witnesses from the original regular results without
resampling. -/
@[expose] def witnesses : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
    {requests : SideBank.Requests sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget minimum
      prepared} →
    {plans : RegularSides.Plans requests} → {evaluated : SideBank.Evaluations sample depth readingIndex requests} →
    (results : RegularSides.Results plans evaluated) →
      RegularWitnesses sample depth prepared
      (results.pairs.map Prod.snd)
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, .cons prepared _, _, _, .cons head tail, results => by
      let first := Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.castEndpoint results.1.first
        head.original_index head.capSample_eq
      let last := Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.castEndpoint results.1.last
        head.original_index head.capSample_eq
      have path := RegularCells.cap_path_eq _ results.1.cells prepared.owners prepared.links results.1.ready
      rw [← results.1.primitive_eq] at path
      have signed := RegularCells.primitive_signed results.1.cells
      rw [← results.1.primitive_eq,
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses.samplePrimitive_eq head.original_index
        head.capSample_eq] at signed
      have ready : 2 ≤ index := by rw [← head.original_index]; exact results.1.ready
      exact .cons ⟨results.1.primitive, first, last, path,
        RegularCells.flip results.1.cells, signed, ready⟩ (witnesses results.2)

end RegularWitnesses.SideBank.Regular.Results
end SideBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
