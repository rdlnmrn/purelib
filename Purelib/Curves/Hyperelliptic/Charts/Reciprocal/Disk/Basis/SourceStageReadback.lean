module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Riemann.Integration.PreparedParentSplitSelection

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection

open Purelib.Riemann.Integration

@[expose] public section

/-! The source covers selected before acquisition are independent of the numerical stage. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection (SelectedInput)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Riemann.Integration.PreparedParentSplitSelection (parentAt)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

namespace SelectedInput

/-- Parent equality transports the static source cover just as it transports its numerical input. No source or numerical
data is regenerated. -/
theorem cast_sources {first last : PreparedSubdivisionModelCore.CenteredEdge curve differential} (equal : first = last)
    {index : Nat} (input : NumericalSelection.SelectedInput first index) :
    (Eq.mp (congrArg (fun parent => NumericalSelection.SelectedInput parent index) equal) input).sources =
      Eq.mp (congrArg (fun parent => SourceLocations.BasisSourceCovers parent) equal) input.sources := by
  cases equal
  rfl

end SelectedInput
namespace NumericalBank

/-- Advancing the acquired numerical stage preserves the exact retained source cover. -/
theorem select_sources_eq {firstIndex lastIndex : Nat} :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    (first : CommonParentPlans.NumericalBank firstIndex anchors sources) → (last : CommonParentPlans.NumericalBank
      lastIndex anchors sources) →
    (position : Fin parents.length) →
    (NumericalBank.select anchors sources first position).sources = (NumericalBank.select anchors sources last
      position).sources
  | _, .nil, _, _, _, position => Fin.elim0 position
  | _, .cons _ _ _ _, _, _, _, ⟨0, _⟩ => rfl
  | _, .cons _ _ _ tail, sources, first, last, ⟨position + 1, bound⟩ =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback.NumericalBank.select_sources_eq tail
        sources.tail first.2 last.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩

end NumericalBank
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceStageReadback
