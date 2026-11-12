module
import Purelib.Algebra.NatCast
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalJoiningComponents
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

public section

/-! Assemble component energy estimates on the canonical exterior boundary bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential}

namespace AllSurfacePreparation

open Purelib.Data.Rat.Fraction.Compatibility

/-- A common upper bound on each remaining-plus-joining component energy bounds their total by the number of retained
components. -/
private theorem component_energy_sum_upper
    (remaining joining :
      SurfaceComponent
      regular domains differential → InverseRootPolynomial.Gaussian)
    (bound : InverseRootPolynomial.Coordinate) :
    (components : List
      (SurfaceComponent
      regular domains differential)) →
    (∀ component ∈ components, (remaining component + joining component).im / 4 ≤ bound) →
    (Gaussian.Norm.Sum.Basic.gaussianSum (components.map remaining) + Gaussian.Norm.Sum.Basic.gaussianSum
      (components.map joining)).im / 4 ≤
      (components.length : InverseRootPolynomial.Coordinate) * bound
  | [], _ => by
      change ((0 : InverseRootPolynomial.Gaussian) + 0).im / 4 ≤ (0 :
        InverseRootPolynomial.Coordinate) * bound
      rw [Gaussian.Basic.zero_add]
      change (0 : InverseRootPolynomial.Coordinate) / 4 ≤ 0 * bound
      simp only [Fraction.Field.div_eq_mul_inv_direct, zero_mul, -eq_self, -iff_self]
      exact le_refl _
  | head :: tail, bounds => by
      have first := bounds head (List.mem_cons_self ..)
      have rest :=
        component_energy_sum_upper
        remaining joining bound tail
        (fun component member => bounds component (List.mem_cons_of_mem head member))
      have both := Fraction.Order.Arithmetic.add_le_add_direct first rest
      have split : (Gaussian.Norm.Sum.Basic.gaussianSum ((head :: tail).map remaining) +
        Gaussian.Norm.Sum.Basic.gaussianSum ((head :: tail).map joining)).im / 4 =
          (remaining head + joining head).im / 4 +
            (Gaussian.Norm.Sum.Basic.gaussianSum (tail.map remaining) + Gaussian.Norm.Sum.Basic.gaussianSum
              (tail.map joining)).im / 4 := by
        change ((remaining head + Gaussian.Norm.Sum.Basic.gaussianSum (tail.map remaining)) +
          (joining head + Gaussian.Norm.Sum.Basic.gaussianSum (tail.map joining))).im / 4 = _
        simp only [Gaussian.Basic.add_im, Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
        ring1
      exact split.trans_le (both.trans_eq (by
        simp only [List.length_cons, NatCast.add, Nat.cast_one, -eq_self, -iff_self]
        ring1))

/-- Sum the complete component estimates and identify exactly the canonical exterior sum.
Each remaining term retains its component's side and endpoint corrections. -/
theorem built_canonical_energy_upper {stage : Nat}
    (cache : RegularDomainMeshes.RegularMeshes.Numerics domains stage) (coefficients
      : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (readings : (row : Fin genus) → TrianglePrimitiveReadings.TriangleReadings
      (cache.get row) lifted.mesh)
    (remaining :
      SurfaceComponent
      regular domains differential → InverseRootPolynomial.Gaussian) {allowance :
      InverseRootPolynomial.Coordinate}
    (bounded : ∀ component ∈
      (build
      (lifted := lifted) regular domains differential).components,
      (remaining component + Path.PairedIncrementArea.area (component.program.indexed.map
        (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
            edge)))).im / 4 ≤
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    (Gaussian.Norm.Sum.Basic.gaussianSum
      ((build
      regular domains differential).components.map remaining) +
      Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word => Path.PairedIncrementArea.area
        (word.map
        (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
            edge)))))).im / 4 ≤

        ((build
        (lifted := lifted) regular domains differential).components.length :
        InverseRootPolynomial.Coordinate) *
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have bound :=
    component_energy_sum_upper
    remaining
    (fun component => Path.PairedIncrementArea.area (component.program.indexed.map
      (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
        CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge))))
    (allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)

      (build
      regular domains differential).components bounded
  rw
    [built_component_areas]
    at bound
  exact bound.trans_eq (by ring1)

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
