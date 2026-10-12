module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences
public import Purelib.Data.Vector.Dependent
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid

/-! Linear-size banks of prefix and adjacent-edge comparisons on a retained
straight trace. Duplicate coordinates keep distinct vertex indices. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Data.Nat
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation

public section

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {count : Nat} {points : Fin (count + 1) → Gaussian.Basic.Canonical}

set_option genInjectivity false in
/-- The original contained trace points and clear segments between every pair of retained vertex indices.

The original indexed points retain their face containment and their clear
segments. Every displayed segment remains inside the same face box. -/
structure SideGeometry (models : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
  face) (points : Fin (count + 1) → Gaussian.Basic.Canonical) where
  /-- Every original indexed trace point lies in the retained face cell. -/ inside : ∀ vertex, face.cell.box.Contains
    (points vertex)
  /-- The original clear segment between each retained pair of trace indices. -/ segment : ∀ first last,
    Geometry.ClearPath.ClearSegment curve.polynomial face.cell.box (points first) (points last)
  /-- Each original retained segment stays inside the actual face box. -/ within : ∀ first last, (segment first
    last).WithinAmbient

constructive_injectivity SideGeometry

namespace SideGeometry

/-- Construct the original horizontal trace geometry from retained containment and a common imaginary coordinate.

The supplied containment and common imaginary coordinate certify each original segment. Both endpoint indices and the
original face owner are retained. -/
@[expose] def horizontal (models : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels
  frames face) (points : Fin (count + 1) → Gaussian.Basic.Canonical)
    (inside : ∀ vertex, face.cell.box.Contains (points vertex))
    {height : Fraction.Rational} (heightEq : ∀ vertex, (points vertex).im = height) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points :=
  ⟨inside, fun first last =>
    SegmentPreparation.horizontalSegment models _ _ (inside
    first) (inside last)
      ((heightEq first).trans (heightEq last).symm),
    fun first last =>
      SegmentPreparation.horizontalSegment_within models _ _
      (inside first) (inside last)
      ((heightEq first).trans (heightEq last).symm)⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry in
/-- Construct the original vertical trace geometry from retained containment and a common real coordinate.

The supplied containment and common real coordinate certify each original segment. Both endpoint indices and the
original face owner are retained. -/
@[expose] def vertical (models : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames
  face) (points : Fin (count + 1) → Gaussian.Basic.Canonical)
    (inside : ∀ vertex, face.cell.box.Contains (points vertex))
    {horizontal : Fraction.Rational} (horizontalEq : ∀ vertex, (points vertex).re = horizontal) :
      Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points :=
  ⟨inside, fun first last =>
    SegmentPreparation.verticalSegment models _ _ (inside
    first) (inside last)
      ((horizontalEq first).trans (horizontalEq last).symm),
    fun first last =>
      SegmentPreparation.verticalSegment_within models _ _
      (inside first) (inside last)
      ((horizontalEq first).trans (horizontalEq last).symm)⟩

variable {geometry : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points}
  {sheet : Fin 2} {domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet}
  {left right : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance : Fraction.Rational}

set_option genInjectivity false in
/-- One original segment preparation and paired differential reference between retained trace indices.

The original prepared segment retains its incoming root owner. Both
differential references belong to that same segment and retained domain. -/
structure PairRequest (geometry : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points)
  (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
    (left right : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) (first last :
      Fin (count + 1)) where
  /-- The actual original segment preparation with its retained incoming root owner. -/ prepared :
    SegmentPreparation models sheet (geometry.segment first
    last)
  /-- Both original differential references on that exact retained segment and domain. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences.PairedReference prepared domain left right
    tolerance

constructive_injectivity PairRequest

namespace PairRequest

/-- Prepare the original trace segment from its supplied retained incoming owner and cache both differential references.

The supplied incoming root owner and geometric segment determine one cached preparation. Both original differential
references use that same prepared segment and domain. -/
@[expose] def build (geometry : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points)
  (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
    (left right : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) (positive : 0 <
      tolerance)
    (first last : Fin (count + 1)) (incoming : Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation.ForwardOwner
      models sheet (points first)) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest geometry domain left right
      tolerance first last :=
  let prepared := SegmentPreparation.ofOwner incoming
    (geometry.segment first last) (geometry.within first last)
    (geometry.inside first) (geometry.inside last)
  ⟨prepared, Hyperelliptic.Meshes.PuncturedGrid.NewtonPairedSegmentReferences.PairedReference.build prepared domain left
    right tolerance positive⟩

end PairRequest

set_option genInjectivity false in
/-- A linear-size bank of original prefix and adjacent-edge comparisons at one retained sufficient stage.

Original prefix and adjacent-edge comparisons share their retained maximum
stage. Their indexed owners and cached references are not replaced. -/
structure Request (geometry : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points)
  (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
    (left right : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) where
  /-- The original comparisons from the retained zero vertex to every indexed trace point. -/ prefixes :
    Data.Vector.DependentVector (fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest geometry domain left right
    tolerance 0 vertex)
  /-- The original comparisons along every retained adjacent indexed edge. -/ edges : Data.Vector.DependentVector (fun
    edge : Fin count =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest geometry domain left right
      tolerance edge.castSucc edge.succ)
  /-- The shared sufficient original stage for all retained prefix and edge references. -/ index : Nat
  /-- Every original retained prefix reference is ready at the common stage. -/ prefixes_later : ∀ vertex, (prefixes.get
    vertex).reference.index ≤ index
  /-- Every original retained adjacent-edge reference is ready at the common stage. -/ edges_later : ∀ edge, (edges.get
    edge).reference.index ≤ index

constructive_injectivity Request

namespace Request

/-- Cache original vertex owners once, prepare all prefixes and adjacent edges, and retain the maximum reference stage.

The complete prefix and adjacent-edge banks cache the same original vertex owners. Their reference maxima determine one
sufficient stage without replacing or reevaluating the comparisons. -/
@[expose] def build (geometry : Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models points)
  (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
    (left right : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) (positive : 0 <
      tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.Request geometry domain left right tolerance :=
  let owners := Data.Vector.DependentVector.ofFn fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation.ForwardOwner.build models sheet (points vertex)
    (geometry.inside vertex)
  let prefixes := Data.Vector.DependentVector.ofFn fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest.build geometry domain left right
    tolerance positive 0 vertex (owners.get 0)
  let edges := Data.Vector.DependentVector.ofFn fun edge : Fin count =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry.PairRequest.build geometry domain left right
      tolerance positive edge.castSucc edge.succ (owners.get edge.castSucc)
  let prefixIndex := prefixes.maximum (fun _ request => request.reference.index)
  let edgeIndex := edges.maximum (fun _ request => request.reference.index)
  ⟨prefixes, edges, max prefixIndex edgeIndex,
    fun vertex => (prefixes.get_le_maximum (fun _ request => request.reference.index) vertex).trans (((congrArg (Nat.le
      _) (Order.max_eq_natMax _ _)).mpr (Order.le_max_left _ _))),
    fun edge => (edges.get_le_maximum (fun _ request => request.reference.index) edge).trans (((congrArg (Nat.le _)
      (Order.max_eq_natMax _ _)).mpr (Order.le_max_right _ _)))⟩

end Request
end SideGeometry
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
