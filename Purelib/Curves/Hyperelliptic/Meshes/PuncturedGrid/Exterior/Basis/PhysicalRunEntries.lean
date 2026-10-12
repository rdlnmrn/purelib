module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Retain the actual occurrence banks with their individual geometry and budget indices. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {faceIndex depth capacity minimum : Nat} {sideArea : Normalization.InverseRootPolynomial.Gaussian} {requested
    allowance tolerance : Normalization.InverseRootPolynomial.Coordinate}

namespace PhysicalRunEntries

set_option genInjectivity false in
/-- The geometry and scalar caps index the retained bank directly. No component
assembly reacquires a side or changes its traversal or prepared numerical owner. -/
structure PhysicalRunEntry (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
      (faceIndex : Nat) where
  /-- The refinement depth of this exact occurrence bank. -/ depth : Nat
  /-- The physical parent-fragment capacity of this occurrence. -/ capacity : Nat
  /-- The area readback retained by the original oriented side sample. -/ sideArea :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The allowance cap indexing the retained physical bank. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The tolerance cap indexing the retained physical bank. -/ tolerance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The original occurrence bank indexed by these exact geometric and scalar data. -/ bank :
    PhysicalRunBank retained inputs outer coefficients
    faceIndex depth capacity sideArea allowance tolerance

constructive_injectivity PhysicalRunEntry

end PhysicalRunEntries

namespace PhysicalRunEntries.PhysicalRunEntry

/-- Package an existing physical occurrence bank with its original depth, capacity, area and budget indices. -/
@[expose] def ofBank (bank : PhysicalRunBank retained
  inputs outer coefficients faceIndex depth capacity sideArea allowance tolerance) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries.PhysicalRunEntry retained inputs outer
      coefficients faceIndex :=
  ⟨depth, capacity, sideArea, allowance, tolerance, bank⟩

end PhysicalRunEntries.PhysicalRunEntry

/-- Each occurrence keeps its own physical partition, depth and side sample. -/
@[expose] def PhysicalRunEntries (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (faceIndex : Nat) :=
  Data.Vector.DependentVector (fun outer : Fin prepared.occurrences.length =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries.PhysicalRunEntry retained inputs outer
      coefficients faceIndex)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
