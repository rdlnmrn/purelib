module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

open Purelib.Riemann.Integration

@[expose] public section

/-! Bound selected numerical slopes by their original finite cover family. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSlopeBound
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Riemann.Integration.PreparedParentSplitSelection (parentAt)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank (select)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples
  (weightedSourceSlopeMaximum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers (primitiveSlope)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Data.Rat in
/-- Every retained numerical selection uses a slope bounded before acquisition. -/
theorem NumericalBank.select_slope_le {index : Nat} : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (inputs : CommonParentPlans.NumericalBank index anchors sources) → (position : Fin parents.length) →
    BasisSourceCovers.primitiveSlope (NumericalBank.select anchors sources inputs position).sources ≤
      Samples.weightedSourceSlopeMaximum anchors sources
  | _, .nil, _, _, position => Fin.elim0 position
  | _, .cons _ _ _ _, _, _, ⟨0, _⟩ => Fraction.Order.Basic.le_max_left ..
  | _, .cons _ _ _ tail, sources, inputs, ⟨position + 1, bound⟩ =>
      (select_slope_le tail sources.tail inputs.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩).trans
        (Fraction.Order.Basic.le_max_right ..)

/-- Equality transport changes the parent type, not its retained scalar slope. -/
theorem SelectedInput.transport_slope {first last : PreparedSubdivisionModelCore.CenteredEdge curve differential} {index
  : Nat}
    (equal : first = last) (input : NumericalSelection.SelectedInput first index) :
    BasisSourceCovers.primitiveSlope (Eq.mp (congrArg (fun parent => NumericalSelection.SelectedInput parent index)
      equal) input).sources =
      BasisSourceCovers.primitiveSlope input.sources := by
  cases equal
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSlopeBound
