module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.Nat.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSample
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Riemann.Integration.PreparedParentSplitSelection
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

public section

/-! Select the retained prepared acquisition at a canonical parent position. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (Plans NumericalBank Readings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples (FanPreparations
    Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor :
    Nat}
  {index minimum readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergyPreparation (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank (BasisCommonParentEntry)

variable {stage energyFloor radialDepth : Nat} {coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus}

set_option genInjectivity false in
/-- Prepared children and their summaries retain the exact selected numerical input. No source model, child integral or
weighted summary is rebuilt. -/
structure PreparedSelection (input : NumericalSelection.SelectedInput parent index)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : InverseRootPolynomial.Coordinate) (coverFloor floor : Nat)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
      where
  /-- The original common-parent request on the selected numerical input's exact covers. -/ entry :
    CommonParentBank.BasisCommonParentEntry input.cover input.sources basis allowance coefficientTarget coverFloor floor
  /-- The actual prepared child integrals acquired on that retained input and polynomial bank. -/ integrals :
    entry.request.prepared.request.Acquisition polynomials input.numerical.originals input.numerical.cells
    coefficients entry.request.arcs.depth
  /-- The retained source/integral child pairs of the actual acquisition. -/ pairs : Acquisition.ChildPairs integrals
  /-- The cached coefficient-weighted child pairs and their original summaries. -/ weighted : ChildPairs.Weighted pairs

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity PreparedSelection

namespace PreparedSelection

/-- Transport the scalar parent identity without rebuilding the selected input or any of its dependent prepared data. -/
@[expose] def castParent {first last : PreparedSubdivisionModelCore.CenteredEdge curve differential}
  (equal : first = last)
    {input : NumericalSelection.SelectedInput first index}
    (selected : PreparedSelection input basis
      allowance coefficientTarget coverFloor floor polynomials coefficients) :
    PreparedSelection (Eq.mp (congrArg (fun parent
      => NumericalSelection.SelectedInput parent index) equal) input)
      basis allowance coefficientTarget coverFloor floor polynomials coefficients := by
  cases equal
  exact selected

end PreparedSelection

namespace PreparedSelection.Samples.PreparedComparisons

/-- Select the original prepared comparison at a retained parent position.

The returned entry, child integrals and weighted summaries are read directly from the existing dependent bank. -/
@[expose] def select : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (bank : CommonParentBank.BasisCommonParentBank anchors sources basis allowance coefficientTarget coverFloor floor) →
    (plans : CommonParentPlans.Plans capSample polynomials minimum anchors sources bank) → (inputs :
      CommonParentPlans.NumericalBank index anchors sources) →
    (readings : CommonParentPlans.Readings anchors sources bank plans inputs stage) →
    (prepared : CommonParentSamples.FanPreparations energyFloor anchors sources bank plans inputs readings) →
    (samples : CommonParentSamples.Samples coefficients radialDepth anchors sources bank plans inputs readings prepared)
      →
    Samples.PreparedComparisons anchors sources bank plans inputs readings prepared samples →
    (position : Fin parents.length) →
    PreparedSelection (NumericalBank.select anchors
      sources inputs position) basis allowance coefficientTarget coverFloor floor polynomials coefficients
  | _, .nil, _, _, _, _, _, _, _, _, position => Fin.elim0 position
  | _, .cons _ _ _ _, _, bank, _, _, _, _, _, comparisons, ⟨0, _⟩ =>
      ⟨bank.1, comparisons.1.integrals, comparisons.1.pairs, comparisons.1.weighted⟩
  | _, .cons _ _ _ tail, sources, bank, plans, inputs, readings, prepared, samples, comparisons, ⟨position + 1, bound⟩
    =>
      select tail sources.tail bank.2 plans.2 inputs.2 readings.2 prepared.2 samples.2 comparisons.2
        ⟨position, Nat.lt_of_succ_lt_succ bound⟩

end PreparedSelection.Samples.PreparedComparisons

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis
