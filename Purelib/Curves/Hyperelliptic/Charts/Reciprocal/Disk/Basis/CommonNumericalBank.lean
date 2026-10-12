module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Periods.PeriodMatrix

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives

open Purelib.Data.Vector

open Purelib.Riemann.Integration

@[expose] public section

/-! Materialize numerical inputs once on the retained anchor and basis covers.
Later common-parent readings, source paths and traces share this bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonNumericalBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (PrimitiveCells SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans (NumericalBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisParentSourceCovers)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Acquire all original anchor and basis primitive inputs once at the supplied polynomial stage.

The dependent bank preserves each parent's actual covers and cached basis source primitives. -/
def NumericalBank.build (index : Nat) : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  →
    (anchors : UniformReciprocalCover.ParentCovers parents) → (sources : SourceLocations.BasisParentSourceCovers
      parents) → CommonParentPlans.NumericalBank index anchors sources
  | _, .nil, _ => PUnit.unit
  | _, .cons _ _ cover tail, sources =>
      let head := sources.head
      let cells := DependentVector.ofFn fun row => PrimitiveCells.build index (head.get row).cover.cells
      let originals := DependentVector.ofFn fun row => SourcePrimitive.build (head.get row).data index
      (⟨PrimitiveCells.build index cover.cells, cells, originals⟩, build index tail sources.tail)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonNumericalBank
