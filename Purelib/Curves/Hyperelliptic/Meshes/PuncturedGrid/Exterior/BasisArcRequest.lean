module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Periods

public section

/-! A common executable request for all exterior basis-pair comparisons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily (PairedArcRequest)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

namespace BasisArcRequest

/-- Each basis preparation is built once and shared by its entire row. -/
@[expose] def BasisArcPreparations (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) :=
  Data.Vector.DependentVector (fun first : Fin genus =>
    ExteriorProgram.AllSurfacePreparation regular domains (PeriodMatrix.standardDifferential first))

end BasisArcRequest

namespace BasisArcRequest.BasisArcPreparations

/-- Build each original basis exterior preparation once for reuse by every paired request in its row. -/
@[expose] def build (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains :=
  DependentVector.ofFn fun first => AllSurfacePreparation.build regular domains (PeriodMatrix.standardDifferential
    first)

end BasisArcRequest.BasisArcPreparations

namespace BasisArcRequest

/-- The complete dependent matrix of original paired arc requests sharing one preparation per basis row. -/
@[expose] def BasisArcRequests (preparations :
  BasisArcPreparations regular domains) (target :
  Fraction.Rational) (minimum : Nat) :=
  Data.Vector.DependentVector (fun first : Fin genus => Data.Vector.DependentVector (fun second : Fin genus =>
    PairedArcFamily.PairedArcRequest (preparations.get first) (PeriodMatrix.standardDifferential second) target
      minimum))

end BasisArcRequest

namespace BasisArcRequest.BasisArcRequests
variable {preparations : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations
  regular domains} {target : Rational} {minimum : Nat}

/-- Every actual retained basis-pair polynomial request stage is paid by the supplied common index. -/
@[expose] def IndexBound (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcRequests
  preparations target minimum) (index : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ index

/-- Every actual retained basis-pair spatial request is paid by the supplied common depth. -/
@[expose] def DepthBound (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcRequests
  preparations target minimum) (depth : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).depth ≤ depth

end BasisArcRequest.BasisArcRequests

set_option genInjectivity false in
/-- One finite numerical stage and one spatial lower bound for every basis pair, retaining all original row preparations
and pair requests. -/
structure BasisArcRequest (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (target : Fraction.Rational) (minimum
      depthFloor : Nat) where
  /-- The original exterior preparation built once for each actual first basis row. -/ preparations :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains
  /-- The complete retained matrix of paired arc requests on those exact original row preparations. -/ entries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcRequests preparations target minimum
  /-- The cached common polynomial stage paying all original pair requests and the external minimum. -/ index : Nat
  /-- The polynomial stage is exactly the original minimum combined with the complete retained pair-stage maximum. -/
    index_eq : index = max minimum (entries.maximum fun _ row => row.maximum fun _ request => request.index)
  /-- The retained common polynomial stage pays the original external minimum. -/ minimum_le : minimum ≤ index
  /-- Every actual original basis-pair request stage is bounded by the retained common stage. -/ index_ge :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcRequests.IndexBound entries index
  /-- The cached common spatial floor paying every original pair request and the supplied depth floor. -/ depth : Nat
  /-- The spatial floor is exactly the original depth floor combined with the complete retained pair-depth maximum. -/
    depth_eq : depth = max depthFloor (entries.maximum fun _ row => row.maximum fun _ request => request.depth)
  /-- The retained common spatial depth pays the original external floor. -/ depthFloor_le : depthFloor ≤ depth
  /-- Every actual original basis-pair spatial request is bounded by the retained common depth. -/ depth_ge :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcRequests.DepthBound entries depth

constructive_injectivity BasisArcRequest

namespace BasisArcRequest

/-- The maxima depend only on the finite requests, before the common cap polynomials or any fine source paths are
sampled. -/
@[expose] def build (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (target : Fraction.Rational) (positive : 0 < target) (minimum depthFloor : Nat) :
    BasisArcRequest regular domains target minimum
      depthFloor := by
  let preparations := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build
    regular domains
  let entries : BasisArcRequests preparations target
    minimum := DependentVector.ofFn fun first =>
    DependentVector.ofFn fun second =>
      PairedArcRequest.build (preparations.get first) (PeriodMatrix.standardDifferential second) target positive minimum
  let index := max minimum (entries.maximum fun _ row => row.maximum fun _ request => request.index)
  let depth := max depthFloor (entries.maximum fun _ row => row.maximum fun _ request => request.depth)
  refine ⟨preparations, entries, index, rfl, Nat.Order.le_max_left _ _, ?_, depth, rfl, Nat.Order.le_max_left _ _, ?_⟩
  · intro first second
    exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first).trans
        (Nat.Order.le_max_right _ _))
  · intro first second
    exact ((entries.get first).get_le_maximum (fun _ request => request.depth) second).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.depth) first).trans
        (Nat.Order.le_max_right _ _))

variable {target : Rational} {minimum depthFloor stage depth : Nat} {box :
  Purelib.Geometry.Rational.Box}

/-- Every pair uses the supplied common polynomial bank and requested depth. The source areas and their endpoint chords
are cached by `ofEvaluation`. -/
@[expose] def evaluate (request : BasisArcRequest
  regular domains target minimum depthFloor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap stage box)
    (chart : HyperellipticReciprocal.originOrder curve = 0)
    (later : request.index ≤ stage) (spatial : request.depth ≤ depth) :
    BasisArcSamples (regular := regular) (domains := domains) polynomials target minimum depth :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    let pair := (request.entries.get first).get second
    let after := (request.index_ge first second).trans later
    let refined := (request.depth_ge first second).trans spatial
    BasisArcSample.ofEvaluation (request.preparations.get first) pair
      (pair.evaluate (polynomials.get first) (polynomials.get second) chart after refined) after

end BasisArcRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
