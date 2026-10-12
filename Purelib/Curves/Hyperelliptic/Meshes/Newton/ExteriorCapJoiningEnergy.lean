module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalMeshEndpoints
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! Homogeneous comparison of cached Newton exteriors with cap joining energy. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Riemann

open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest (exterior)

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
  {newSheet : Fin 2} {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current}
  {magnitudes : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor stage : Nat}
  {cache : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
    basis) stage domains)}
  {triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh)}
  {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces current.cutPolygon.patch (fun basis =>
    (triangles.get basis).values)}
  {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces}
  {request : Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
    error floor}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {basisTarget : Fraction.Rational} {minimum
    depthFloor : Nat} {box : Rational.Box}
  {basis : PuncturedGrid.Exterior.PhysicalBasisRequest regular domains
    basisTarget minimum depthFloor}

/-- Pairwise comparison budgets are independent of the coefficient vector.
The contraction reads the cached period offsets and the actual cap attachments. -/
theorem Samples.exterior_joining_bound (samples :
  Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs request)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
      {pairBound : Fraction.Rational}
    (bounded : ∀ first second,
      Data.Gaussian.Norm.Basic.normSq (2 *
        ConjugatePhysicalRequest.exterior (paired := paired)
        newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get
          second).values) -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
          (attachments.get first) (polynomials.get first) (polynomials.get second)) ≤ pairBound)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (2 * samples.exterior coefficients -
      PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
      attachments polynomials coefficients) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients ^ 2 *
        pairBound := by
  let residual := fun first second => 2 * ((samples.get first).get second).exterior -
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
      (attachments.get first) (polynomials.get first) (polynomials.get second)
  have bounds (first second : Fin genus) : Data.Gaussian.Norm.Basic.normSq (residual first second) ≤ pairBound := by
    dsimp only [residual]
    rw [((samples.get first).get second).exterior_eq]
    exact bounded first second
  have estimate := Periods.BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj
    (coefficients basis)) coefficients residual bounds
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at estimate
  have expanded : FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
    (coefficients first) * coefficients second * residual first second)) =
      2 * samples.exterior coefficients -
        PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
        attachments polynomials coefficients := by
    calc
      _ = FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        2 * (Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ((samples.get first).get
          second).exterior) -
          Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
            Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
              (attachments.get first) (polynomials.get first) (polynomials.get second))) := by
        apply FiniteSum.Fin.sumFin_congr
        intro first
        apply FiniteSum.Fin.sumFin_congr
        intro second
        dsimp only [residual]
        ring1
      _ = _ := by simp only [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left, -eq_self, -iff_self]; rfl
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients basis))]
    at estimate
  exact (congrArg Data.Gaussian.Norm.Basic.normSq expanded.symm).trans_le (estimate.trans_eq (by
    unfold Readings.PreparedObservationCoercivity.coefficientNormSq; ring1))

/-- A scalar budget on the basis pairs pays the energy comparison uniformly,
including the zero coefficient vector. -/
theorem Samples.exterior_joining_energy_upper (samples :
  Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs request)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
      {pairBound allowance : Fraction.Rational}
    (bounded : ∀ first second,
      Data.Gaussian.Norm.Basic.normSq (2 *
        ConjugatePhysicalRequest.exterior (paired := paired)
        newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get
          second).values) -
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
          (attachments.get first) (polynomials.get first) (polynomials.get second)) ≤ pairBound)
    (nonnegative : 0 ≤ allowance) (paid : (genus : Fraction.Rational) ^ 2 * pairBound ≤ 16 * allowance ^ 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (2 * samples.exterior coefficients -
      PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
      attachments polynomials coefficients).im / 4 ≤
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have close := samples.exterior_joining_bound attachments polynomials bounded coefficients
  have payment := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
  have scaled : (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients ^ 2
    * pairBound ≤
      (4 * (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    calc
      _ = ((genus : Fraction.Rational) ^ 2 * pairBound) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ^ 2 := by ring1
      _ ≤ (16 * allowance ^ 2) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ^ 2 := payment
      _ = _ := by ring1
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Gaussian.Norm.Basic.normSq_nonneg (coefficients row))
    rw [FiniteSum.Fin.sumFin_congr (fun row => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))] at bound
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  let residual := 2 * samples.exterior coefficients -
    PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
    attachments polynomials coefficients
  have squared : Data.Gaussian.Norm.Basic.normSq (residual - 0) ≤ (4 * (allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rw [Data.Gaussian.Basic.sub_zero]
    exact close.trans scaled
  have bound := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le residual 0
    (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative normNonnegative) squared
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct bound (allowance *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
  have left : residual.im / 4 - allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients +
    allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients = residual.im / 4 := by ring1
  rw [left] at shifted
  exact shifted.trans_eq (by
    change (0 : Fraction.Rational) / 4 + _ = _
    rw [show (0 : Fraction.Rational) / 4 = 0 by decide, Fraction.Field.zero_add])

/-- One retained basis-wide request supplies every pairwise premise. Its
canonical squared target pays the requested homogeneous energy allowance. -/
theorem Samples.regular_joining_energy_upper (samples :
  Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs request)
    {allowance : Fraction.Rational} {joiningFloor depth readingIndex : Nat}
    (joining : Hyperelliptic.Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily (paired := paired)
      basis.preparations magnitudes
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
        joiningFloor)
    {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
    (evaluated : joining.Evaluations polynomials cache depth readingIndex)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (later : joining.index ≤ stage) (positive : 0 < allowance)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (2 * samples.exterior coefficients -
      PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
      attachments polynomials coefficients).im / 4 ≤
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have paid : (genus : Fraction.Rational) ^ 2 *
    Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance ≤
      16 * allowance ^ 2 :=
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid positive).trans_eq (by
      ring1)
  exact samples.exterior_joining_energy_upper attachments polynomials
    (fun first second => (joining.accurate evaluated triangles attachments later newSheet degree first second).le)
    positive.le paid coefficients

/-- Transfer the paid remaining-surface cap bound to the actual cached Newton
exterior. The supplied cap upper bound is furnished by the shared physical schedule. -/
theorem Samples.remaining_exterior_energy_upper (samples :
  Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request.Samples triangles surfaces pairs request)
    {allowance capAllowance : Fraction.Rational} {joiningFloor depth readingIndex : Nat}
    (joining : Hyperelliptic.Meshes.Newton.Regular.JoiningFamily.RegularJoiningFamily (paired := paired)
      basis.preparations magnitudes
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance)
        joiningFloor)
    {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
    (evaluated : joining.Evaluations polynomials cache depth readingIndex)
    (attachments : Data.Vector.DependentVector (fun first =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (basis.preparations.get
      first)))
    (later : joining.index ≤ stage) (positive : 0 < allowance)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (remaining : Gaussian.Basic.Canonical)
    (capUpper : (remaining +
      PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
      attachments polynomials coefficients).im / 4 ≤
      capAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    (remaining + 2 * samples.exterior coefficients).im / 4 ≤
      (capAllowance + allowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have joiningBound := samples.regular_joining_energy_upper joining evaluated attachments later positive degree
    coefficients
  have bounds := Fraction.Order.Arithmetic.add_le_add_direct capUpper joiningBound
  have split : (remaining + 2 * samples.exterior coefficients).im / 4 =
      (remaining +
        PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
        attachments polynomials coefficients).im / 4 +
      (2 * samples.exterior coefficients -
        PuncturedGrid.Exterior.PhysicalMeshRequest.Readings.capJoiningEnergy
        attachments polynomials coefficients).im / 4 := by
    simp only [Gaussian.Basic.add_im, Gaussian.Basic.sub_im,
      Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
    ring1
  exact split.trans_le (bounds.trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison.Request
