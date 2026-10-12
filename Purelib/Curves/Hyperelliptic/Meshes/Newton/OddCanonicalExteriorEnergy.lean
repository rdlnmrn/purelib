module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Curves.Hyperelliptic.Meshes.Newton.CanonicalExteriorEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.CanonicalExteriorEnergy

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorRequest.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Readings

public section

/-! Automatic odd exterior comparison and remaining-surface energy transport. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request (Samples)
open Purelib.Integration.Path.PairedIncrementArea (area)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_mul_left)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars}
  {newSheet : Fin 2} {excision : AllHoleExcision grid
    current}
  {magnitudes : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis))}
  {error : Rational} {floor stage : Nat}
  {cache : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis) stage domains)}
  {triangles : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    TriangleReadings (cache.get basis)
    current.mesh)}
  {surfaces : EnergySurfaces current.cutPolygon.patch (fun basis
    => (triangles.get basis).values)}
  {pairs : EnergyPairs surfaces}
  {request : Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision
    magnitudes error floor}

/-- The computed odd lap family pays the canonical exterior comparison for every coefficient vector. -/
theorem Samples.odd_components_energy_upper (samples : HomogeneousPhysicalComparison.Request.Samples triangles surfaces
  pairs request)
    {allowance : Fraction.Rational} {joiningFloor : Nat}
    (joining : OddCanonicalExteriorRequest magnitudes allowance joiningFloor)
    (later : joining.index ≤ stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (2 * samples.exterior coefficients - Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map
      (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))).im / 4 ≤
      allowance * PreparedObservationCoercivity.coefficientNormSq coefficients :=
  Samples.exterior_components_energy_upper samples
    (fun first second => OddCanonicalExteriorRequest.accurate joining first second (triangles.get first) (triangles.get
      second) later newSheet degree)
    joining.positive.le joining.paid coefficients

/-- Transfer the remaining-surface bound through the actual odd canonical polygons. -/
theorem Samples.remaining_odd_exterior_energy_upper (samples : HomogeneousPhysicalComparison.Request.Samples triangles
  surfaces pairs request)
    {allowance surfaceAllowance : Fraction.Rational} {joiningFloor : Nat}
    (joining : OddCanonicalExteriorRequest magnitudes allowance joiningFloor)
    (later : joining.index ≤ stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (remaining : Data.Gaussian.Basic.Canonical)
    (surfaceUpper : (remaining + Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word
      =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))).im / 4 ≤
      surfaceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    (remaining + 2 * samples.exterior coefficients).im / 4 ≤
      (surfaceAllowance + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bounds := Fraction.Order.Arithmetic.add_le_add_direct surfaceUpper
    (Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy.Samples.odd_components_energy_upper samples joining
    later degree coefficients)
  have split : (remaining + 2 * samples.exterior coefficients).im / 4 =
      (remaining + Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))).im / 4 + (2 * samples.exterior coefficients -
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
      PairedIncrementArea.area (word.map (fun edge => ConjugatePathReadback.conjugateDiagonal
        (FiniteSum.Fin.sumFin fun row => coefficients row * CanonicalEdgeValues.edgeValuation current.mesh
          (triangles.get row).values edge)))))).im / 4 := by
    simp only [-eq_self, -iff_self, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_im,
      Fraction.Field.div_eq_mul_inv_direct]
    ring1
  exact split.trans_le (bounds.trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OddCanonicalExteriorEnergy
