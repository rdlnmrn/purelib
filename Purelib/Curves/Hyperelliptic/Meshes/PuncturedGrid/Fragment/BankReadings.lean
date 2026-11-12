module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-!
# Original fragment readings from one common face mesh bank

Face, sheet and domain equalities transport only the cached data. Each
fragment reads the same indexed numerical bank and the same point mesh as
every other occurrence of that face and sheet.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {domains :
    Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {cuts : List Fraction.Rational} {partition : Rectangle.AxisPartition 0 1 cuts} {interval :
    Rectangle.Partition.PreparedAxisPartitions.Interval}
  {fragment : RegularFaces.RegularPrimitiveFragment axes parent partition
    interval}
  {count : Nat} {target : Fraction.Rational} {request : Readings.UniformPreparedRequests.LocalRequest parent count
    target}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

/-- Read the original fragment's face and sheet mesh budget using only its retained owner-equality transports. -/
def meshBudget (assigned : SheetEntries.RegularPrimitiveFragment.SheetEntry
  fragment domains request) (budgets : Face.CommonMeshes.FaceMeshBudgets source
  points tolerance (numerator := numerator) domains) :
    Face.CommonMeshes.DomainMeshBudget assigned.domain source points tolerance (numerator := numerator) :=
  (((Face.CommonMeshes.FaceMeshBudgets.get budgets
    fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain assigned.domain_eq.symm

/-- Read the fragment from the original shared numerical bank and point mesh without rebuilding either cache. -/
def meshReadings (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes (numerator := numerator) budgets numerics) :
    Face.CommonMeshes.DomainMeshReadings
      (BankReadings.meshBudget assigned budgets)
      (SharedComparison.sharedPrimitives assigned numerics) :=
  (((Face.CommonMeshes.FaceSharedMeshes.get shared
    fragment.face.located.index).castFace fragment.face.located.indexed).atSheet
    assigned.entry.sheet).castDomain assigned.domain_eq.symm

/-- The exact original fragment comparison using its retained mesh bounds, sufficient stage and cached readings. -/
abbrev BankReading (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :=
  SharedComparison (assigned := assigned) (bounds :=
    (BankReadings.meshBudget assigned budgets).bounds)
    (accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex
      (BankReadings.meshBudget assigned budgets).accuracy index
      (BankReadings.meshReadings assigned shared).later)
    (BankReadings.meshReadings assigned shared).readings

/-- Construct the original fragment comparison from the shared bank and containment of its retained split points. -/
def BankReading.build (assigned :
  SheetEntries.RegularPrimitiveFragment.SheetEntry fragment domains request)
    {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance domains}
      {numerics : Face.PrimitiveData.FacePrimitiveBank source index domains}
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (included : ∀
      point ∈ assigned.split.points, point ∈ points) :
    BankReading assigned shared :=
  SharedComparison.build (assigned := assigned) (bounds :=
    (BankReadings.meshBudget assigned budgets).bounds)
    (accuracy := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex
      (BankReadings.meshBudget assigned budgets).accuracy index
      (BankReadings.meshReadings assigned shared).later)
    (BankReadings.meshReadings assigned shared).readings included

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
