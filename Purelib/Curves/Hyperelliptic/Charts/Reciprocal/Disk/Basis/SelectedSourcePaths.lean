module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedParentSplitSelection

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Indexed readback preserves the complete common-source path bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSourcePaths

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {index minimum readingIndex : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {stage energyFloor radialDepth : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}

/-- The source sides of the original restoration pairs equal the indexed readback of every retained parent selection.

The complete path list and parent order are preserved, including the actual incoming predecessor used by the
restoration. -/
theorem Samples.PreparedComparisons.sourcePaths_eq : {parents : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) → (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) →
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) → (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage) →
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared) →
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples) →
    (previous : Normalization.InverseRootPolynomial.Gaussian) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors sources
      bank plans inputs readings prepared samples comparisons previous).map Prod.snd =
      List.ofFn (fun position : Fin parents.length =>
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection.Samples.PreparedComparisons.select anchors sources
          bank plans inputs readings prepared samples comparisons position).weighted.values.map Prod.fst)
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, previous => by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs,
        List.map_cons, Purelib.Data.List.OfFn.Basic.ofFn_succ]
      exact congrArg₂ List.cons rfl
        (sourcePaths_eq tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
          samples.1.endpoints.last.2)

/-- Parent transport leaves the cached scalar values unchanged. -/
theorem PreparedSelection.castParent_values {first last : Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential} (equal : first = last)
    {input : Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput first index}
    (selected : PreparedSelection input basis allowance
      coefficientTarget coverFloor floor polynomials coefficients) :
    (PreparedSelection.castParent equal
      selected).weighted.values = selected.weighted.values := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSourcePaths
