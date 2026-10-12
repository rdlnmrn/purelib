module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

public section

/-! One preselected stage samples the complete original common-interval spine.
Every block uses the same original and reciprocal numerical banks. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (PrimitiveRequest primitiveSample)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- The complete original primitive request spine indexed by its retained common-interval list. -/
inductive CommonPrimitivePlans (regular : RegularBounds.Data cap) (target : InverseRootPolynomial.Coordinate) (floor :
  Nat) :
    List (CommonCover.BasisCommonInterval cover covers) → Type 2
  /-- The original request spine for an empty common-interval list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
    target floor []
  /-- Retain one original interval request and the actual remaining request spine. -/ | cons {interval :
    CommonCover.BasisCommonInterval cover covers} {rest : List (CommonCover.BasisCommonInterval cover covers)}
      (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (tail :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans
        regular target floor rest) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
        target floor (interval :: rest)

constructive_injectivity CommonPrimitivePlans

namespace CommonPrimitivePlans

/-- Prepare one original primitive request per retained interval in its actual list order. -/
@[expose] def build (regular : RegularBounds.Data cap) (target : InverseRootPolynomial.Coordinate) (positive : 0 <
  target) (floor : Nat) :
    (intervals : List (CommonCover.BasisCommonInterval cover covers)) →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target
      floor intervals
  | [] => .nil
  | interval :: rest => .cons (BasisCommonInterval.primitiveRequest interval regular target positive floor)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.build
    regular target positive floor rest)

/-- This maximum is selected before either numerical bank is sampled. -/
@[expose] def stage : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor
  intervals → Nat
  | _, .nil => floor
  | _, .cons request tail => max request.index tail.stage

/-- The complete original common-interval plan stage pays the supplied numerical floor. -/
theorem floor_le : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (plans : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      target floor intervals) → floor ≤ plans.stage
  | _, .nil => Nat.le_refl _
  | _, .cons _ tail =>
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.floor_le
    tail).trans (Purelib.Data.Nat.Order.le_max_right ..)

variable {polynomials :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- The shared-bank sample is named to keep the dependent block signatures compact. -/
@[expose] def intervalSample (interval : CommonCover.BasisCommonInterval cover covers) (regular : RegularBounds.Data
  cap)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
      :=
  BasisCommonInterval.primitiveSample interval regular polynomials originals cells

set_option genInjectivity false in
/-- The acquired source and pullback blocks indexed by the exact original request spine.

Every block shares the supplied original and reciprocal numerical banks, coefficient vector and dyadic depth. -/
inductive Blocks (regular : RegularBounds.Data cap) (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target
      floor intervals → Type 2
  /-- The acquired block bank for the original empty request spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
    regular polynomials originals cells coefficients depth .nil
  /-- Retain one actual shared-bank block, its original paid request stage and the remaining acquired spine. -/ | cons
    {interval : CommonCover.BasisCommonInterval cover covers} {rest : List (CommonCover.BasisCommonInterval cover
    covers)}
      {request : BasisCommonInterval.PrimitiveRequest interval regular target floor} {tail :
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target
        floor rest}
      (head : PrimitiveSample.Block
        (intervalSample
        interval regular polynomials originals cells) coefficients depth)
      (later : request.index ≤ index) (remaining :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
        regular polynomials originals cells coefficients depth tail) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
        regular polynomials originals cells coefficients depth (.cons request tail)

constructive_injectivity Blocks

/-- Read the retained reciprocal cells and construct every literal block in original interval order at the supplied
common index. -/
@[expose] def acquire (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} → (plans :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target
      floor intervals) →
    plans.stage ≤ index →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals cells coefficients depth plans
  | _, .nil, _ => .nil
  | _, .cons (interval := interval) _ tail, later =>
      let sample :=
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.intervalSample
        interval regular polynomials originals cells
      .cons (PrimitiveSample.block sample coefficients depth) ((Purelib.Data.Nat.Order.le_max_left ..).trans later)

          (acquire
          polynomials originals cells coefficients depth tail ((Purelib.Data.Nat.Order.le_max_right ..).trans later))

namespace Blocks

variable {originals :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
  covers index} {cells :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
  index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The actual original source and pullback increment lists in retained common-interval order. -/
@[expose] def paths : {intervals : List (CommonCover.BasisCommonInterval cover covers)} → {plans :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor
  intervals} →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals cells coefficients depth plans → List (List InverseRootPolynomial.Gaussian × List
      InverseRootPolynomial.Gaussian)
  | _, _, .nil => []
  | _, _, .cons head _ remaining => (head.source.increments, head.pullback.increments) :: remaining.paths

/-- The retained paired block list contains exactly one entry per original common interval. -/
theorem paths_count : {intervals : List (CommonCover.BasisCommonInterval cover covers)} → {plans :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor
  intervals} →
    (blocks : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
      regular polynomials originals cells coefficients depth plans) → blocks.paths.length = intervals.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ remaining => congrArg Nat.succ remaining.paths_count

/-- Join cached summaries in the same order as the literal flattened paths. -/
@[expose] def sourceSummary : {intervals : List (CommonCover.BasisCommonInterval cover covers)} → {plans :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor
  intervals} →
    (blocks : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
      regular polynomials originals cells coefficients depth plans) →
    IncrementArea.Summary (blocks.paths.map Prod.fst).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head _ remaining => head.source.summary.append remaining.sourceSummary

/-- Join the cached original pullback summaries in the exact order of their retained flattened increment paths. -/
@[expose] def pullbackSummary : {intervals : List (CommonCover.BasisCommonInterval cover covers)} → {plans :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor
  intervals} →
    (blocks : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks
      regular polynomials originals cells coefficients depth plans) →
    IncrementArea.Summary (blocks.paths.map Prod.snd).flatten
  | _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons head _ remaining => head.pullback.summary.append remaining.pullbackSummary

end Blocks
end CommonPrimitivePlans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
