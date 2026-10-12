module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonNumericalBank
public import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Init.Data.Fin.Basic
import Init.Data.Nat.Basic
import Init.Prelude

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

@[expose] public section

/-! Positional readback of retained common-basis numerical inputs. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalInput NumericalBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers
  BasisParentSourceCovers)
open Purelib.Riemann.Integration.PreparedParentSplitSelection (parentAt)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- The retained numerical input at one original parent position.

The patch, model, anchor cover and basis covers belong to that exact parent, and the numerical bank keeps their acquired
cells and source primitives. -/
structure SelectedInput (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (index : Nat) where
  /-- The original prepared patch at the selected parent. -/ patch : UniformPrimitiveSheetCompatibility.PreparedPatch
    parent
  /-- The retained reciprocal model for that exact patch. -/ data : UniformReciprocalModels.Data patch genus
  /-- The actual anchor cover of the retained reciprocal model. -/ cover : UniformReciprocalCover.Cover data
  /-- The original basis source covers at the selected parent. -/ sources : SourceLocations.BasisSourceCovers parent
  /-- The acquired numerical input on these exact anchor and basis covers. -/ numerical :
    CommonParentPlans.NumericalInput cover sources index

constructive_injectivity SelectedInput

/-- Read the selected tuple from the bank. Covers, cells and original primitive samples are retained; no numerical
builder is called. -/
def NumericalBank.select {index : Nat} : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) →
    CommonParentPlans.NumericalBank index anchors sources → (position : Fin parents.length) →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.SelectedInput
      (PreparedParentSplitSelection.parentAt parents position) index
  | _, .nil, _, _, position => Fin.elim0 position
  | _, .cons patch data cover _, sources, inputs, ⟨0, _⟩ =>
      ⟨patch, data, cover, sources.head, inputs.1⟩
  | _, .cons _ _ _ tail, sources, inputs, ⟨position + 1, bound⟩ =>
      select tail sources.tail inputs.2 ⟨position, Nat.lt_of_succ_lt_succ bound⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
