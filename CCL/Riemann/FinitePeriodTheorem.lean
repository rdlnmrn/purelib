import CCL.Riemann.EvenCellularHomology
import CCL.Riemann.BranchCutLifts
import CCL.Riemann.ClearDifferentialObservations
import CCL.Riemann.PeriodMatrix
import CCL.Riemann.PreparedStokes
import CCL.Riemann.PreparedEnergy
import CCL.Riemann.PreparedEnergySurface
import CCL.Riemann.PreparedRefinementPrograms

/-!
# The finite hyperelliptic period theorem package

This module assembles the constructive conclusions proved by the finite
topology and persistent-integration layers.  The cell complex, Euler
characteristic, genus, cellular quotient, and symplectic basis are computed
from the curve's degree shape.  The analytic layer remains certificate driven:
its lifted path traces, algebraic observation programs, fraction-free inverse,
and finite bilinear witnesses are explicit data checked by their respective
interfaces.
-/

namespace CCL.Riemann.FinitePeriodTheorem

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.LiftedPaths
open CCL.Riemann.PeriodMatrix

def OddCountAgreement (genus : Nat) : Prop :=
  (CCL.Riemann.HyperellipticCells.oddCellComplex genus).vertices.length =
      (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).vertices.length /\
    (CCL.Riemann.HyperellipticCells.oddCellComplex genus).edges.length =
      (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).edges.length /\
    (CCL.Riemann.HyperellipticCells.oddCellComplex genus).faces.length =
      (CCL.Riemann.Hyperelliptic.oddDegreeModel genus).faces.length

def EvenCountAgreement (genus : Nat) : Prop :=
  (CCL.Riemann.HyperellipticCells.evenCellComplex genus).vertexCount =
      (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).vertices.length /\
    (CCL.Riemann.HyperellipticCells.evenCellComplex genus).edges.length =
      (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).edges.length /\
    (CCL.Riemann.HyperellipticCells.evenCellComplex genus).faces.length =
      (CCL.Riemann.Hyperelliptic.evenDegreeModel genus).faces.length

/-- The degree-dependent concrete cell model and its proved symplectic
cellular quotient. -/
inductive TopologyCertificate {genus : Nat}
    (curve : HyperellipticCurve genus) : Type
  | odd
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
      (cellCounts : OddCountAgreement genus)
      (homology : CCL.Riemann.OddSymplecticHomology.Certificate genus)
  | even
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
      (cellCounts : EvenCountAgreement genus)
      (homology : CCL.Riemann.EvenCellularHomology.Certificate genus)

/-- Construct the complete finite topological certificate by inspecting the
two executable degree-shape constructors. -/
def topologyCertificate {genus : Nat} (curve : HyperellipticCurve genus) :
    TopologyCertificate curve := by
  cases shape : curve.degreeShape with
  | odd degreeEqual =>
      exact .odd degreeEqual
        (by
          unfold OddCountAgreement
          exact CCL.Riemann.HyperellipticCells.oddCellComplex_matches_countModel genus)
        (CCL.Riemann.OddSymplecticHomology.certificate genus)
  | even degreeEqual =>
      exact .even degreeEqual
        (by
          unfold EvenCountAgreement
          exact CCL.Riemann.HyperellipticCells.evenCellComplex_matches_countModel genus)
        (CCL.Riemann.EvenCellularHomology.certificate genus)

/-- The explicitly checked analytic inputs in their constructive dependency
order: raw finite periods, their pre-normalization Stokes data, an
operationally valid fraction-free inverse presentation, and finite
geometry-backed energy requests for the resulting normalized matrix.  The
inverse presentation may use the canonical stream from its first sample or a
certified finite tail. -/
structure AnalyticCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve) where
  periodData : PeriodData curve
  cycles_realization :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization curve
      periodData.cycles basis.cycles
  preBilinear :
    CCL.Riemann.FiniteBilinear.PreNormalizationCertificate periodData
  aInverse : ScaledInverseCertificate periodData.aMatrix
  energy : CCL.Riemann.FiniteEnergy.Certificate
    (NormalizedPeriodData.ofScaledInverse periodData aInverse)

namespace AnalyticCertificate

/-- Candidate separation is converted constructively into the apartified
fraction-free inverse package. -/
def inverse {genus : Nat} {curve : HyperellipticCurve genus}
    {basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    ScaledInverseCertificate analytic.periodData.aMatrix :=
  analytic.aInverse

/-- Normalization is formed from the explicit finite inverse-scalar apartness
certificate.  Surface energy is subsequently requested for the fraction-free
coefficients produced by each synchronized inverse sample, with any displayed
boundary error paid before transport. -/
def normalized {genus : Nat} {curve : HyperellipticCurve genus}
    {basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve}
    (analytic : AnalyticCertificate curve basis) : NormalizedPeriodData curve :=
  NormalizedPeriodData.ofScaledInverse analytic.periodData analytic.inverse

/-- The stored finite energy request family is definitionally attached to the
same operational inverse used by normalization. -/
def normalizedEnergy {genus : Nat} {curve : HyperellipticCurve genus}
    {basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    CCL.Riemann.FiniteEnergy.Certificate analytic.normalized := by
  simpa only [normalized, inverse] using analytic.energy

/-- Assemble both normalized bilinear conclusions from the pre-normalization
certificate and the post-inversion energy transport. -/
def bilinear {genus : Nat} {curve : HyperellipticCurve genus}
    {basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve}
    (analytic : AnalyticCertificate curve basis) :
    CCL.Riemann.FiniteBilinear.Certificate analytic.normalized where
  preNormalization := analytic.preBilinear
  energy := analytic.normalizedEnergy

end AnalyticCertificate

/-- All conclusions of the finite theorem, with the automatically constructed
topology kept separate from the explicitly audited analytic certificates. -/
structure Result {genus : Nat} (curve : HyperellipticCurve genus) where
  basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve
  topology : TopologyCertificate curve
  eulerCharacteristic :
    curve.finiteCellModel.eulerCharacteristic = (2 : Int) - 2 * genus
  analytic : AnalyticCertificate curve basis

/-- Finite Riemann period theorem from an explicit constructed symplectic
basis and analytic certificates attached to that same basis. -/
def finiteRiemannPeriodTheorem_of_basis_certificates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve)
    (analytic : AnalyticCertificate curve basis) : Result curve where
  basis := basis
  topology := topologyCertificate curve
  eulerCharacteristic := curve.finiteCellModel_eulerCharacteristic
  analytic := analytic

/-- Assemble the genus-one theorem from any explicitly realized finite period
program and its single unit cut-surface inequality.  This is the worked-example
interface: the period program may use hand-audited branch tracks and executable
continuation banks instead of the conservative automatic schedule. -/
def finiteRiemannPeriodTheorem_genusOne_of_basis_unitSurfaceLower
    (curve : HyperellipticCurve 1)
    (basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve)
    (data : PeriodData curve)
    (realizes :
      CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
        curve data.cycles basis.cycles)
    (unitSurfaceLower :
      CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate data) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_basis_certificates curve basis
    { periodData := data
      cycles_realization := realizes
      preBilinear :=
        { stokesClosure :=
            CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne data }
      aInverse :=
        unitSurfaceLower.toScalarCandidateLowerCertificate.toScaledInverseCertificate
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse,
          CCL.Riemann.FiniteEnergy.normalizedData] using
          unitSurfaceLower.genusOneTransportCertificate.toCertificate }

/-- The corresponding minimal two-face interface.  One lower bound on the
first triangle of the finite commutator polygon supplies the complete
genus-one Riemann period certificate. -/
def finiteRiemannPeriodTheorem_genusOne_of_basis_canonicalFaceLower
    (curve : HyperellipticCurve 1)
    (basis : CCL.Riemann.BranchCutLifts.SymplecticBasis curve)
    (data : PeriodData curve)
    (realizes :
      CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
        curve data.cycles basis.cycles)
    (faceLower :
      CCL.Riemann.PreparedEnergySurface.GenusOneCanonicalFaceLowerCertificate
        data) : Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_basis_unitSurfaceLower curve basis data
    realizes faceLower.toUnitSurfaceLowerCertificate

/-- Finite Riemann period theorem from explicit analytic certificates on the
automatic branch basis.

The construction itself uses only finite case analysis.  Its result contains
the concrete degree-dependent cell model and symplectic cellular basis, the
sheet-aware certified period programs, the fraction-free normalized matrix,
and the operational symmetry and pointwise positivity witnesses. -/
def finiteRiemannPeriodTheorem_of_certificates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (analytic : AnalyticCertificate curve
      (CCL.Riemann.BranchCutLifts.symplecticBasis curve)) : Result curve :=
  finiteRiemannPeriodTheorem_of_basis_certificates curve
    (CCL.Riemann.BranchCutLifts.symplecticBasis curve) analytic

/-- Assemble the finite theorem directly from mesh-prepared period schedules.
The realization witness ties every requested subdivision to the automatically
constructed raw symplectic basis without requiring equality of differently
subdivided lifted paths. -/
def finiteRiemannPeriodTheorem_of_prepared_schedules {genus : Nat}
    (curve : HyperellipticCurve genus)
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (realizes : geometry.Realizes
      (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix)
    (boundaryReduction :
      CCL.Riemann.PreparedStokes.CompatibleUpperCellularProgramBoundaryReduction
        schedules)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      schedules.toPeriodData inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_certificates curve
    { periodData := schedules.toPeriodData
      cycles_realization := .legacy (schedules.cyclesRealization realizes)
      preBilinear :=
        { stokesClosure := boundaryReduction.toFiniteStokesClosure }
      aInverse := inverseLower.toScaledInverseCertificate
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse,
          CCL.Riemann.FiniteEnergy.normalizedData] using
          surfaceEnergy.toCertificate }

/-- The first nontrivial case needs no user-supplied Stokes reduction.  For a
genus-one curve the sole antisymmetric matrix entry closes automatically, so
only the prepared periods, their basis realization, finite inverse separation,
and the constructive surface-energy data remain. -/
def finiteRiemannPeriodTheorem_genusOne_of_prepared_schedules
    (curve : HyperellipticCurve 1)
    {geometry :
      CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      CCL.Riemann.PreparedCycleModels.CompatiblePeriodSchedules curve geometry)
    (realizes : geometry.Realizes
      (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles)
    (inverseLower : ScalarCandidateLowerCertificate
      schedules.toPeriodData.aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      schedules.toPeriodData inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_certificates curve
    { periodData := schedules.toPeriodData
      cycles_realization := .legacy (schedules.cyclesRealization realizes)
      preBilinear :=
        { stokesClosure :=
            CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne
              schedules.toPeriodData }
      aInverse := inverseLower.toScaledInverseCertificate
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse,
          CCL.Riemann.FiniteEnergy.normalizedData] using
          surfaceEnergy.toCertificate }

/-! ## Automatic standard period programs -/

/-! The explicit-data entry points retain exactly the same finite period and
energy checks while allowing examples to supply a small audited branch-track
family instead of executing the generic global isolator. -/

/-- Assemble the theorem from standard switched period programs built from
explicit degree-complete branch tracks. -/
def finiteRiemannPeriodTheorem_of_explicit_standard_periods {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (preBilinear : CCL.Riemann.FiniteBilinear.PreNormalizationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
        curve branches))
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
        curve branches).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
        curve branches) inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_basis_certificates curve
    (CCL.Riemann.BranchCutLifts.symplecticBasisOfData curve branches)
    { periodData :=
        CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
          curve branches
      cycles_realization :=
        CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData_realization
          curve branches
      preBilinear := preBilinear
      aInverse := inverseLower.toScaledInverseCertificate
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse,
          CCL.Riemann.FiniteEnergy.normalizedData] using
          surfaceEnergy.toCertificate }

/-- Genus-one explicit-data theorem: diagonal Stokes closure is automatic, so
only A-period separation and the finite surface-energy transport remain. -/
def finiteRiemannPeriodTheorem_genusOne_of_explicit_standard_periods
    (curve : HyperellipticCurve 1)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
        curve branches).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
        curve branches) inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_explicit_standard_periods curve branches
    { stokesClosure :=
        CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne
          (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
            curve branches) }
    inverseLower surfaceEnergy

/-- Sharp genus-one explicit-data entry point from the unit cut-surface
inequality. -/
def finiteRiemannPeriodTheorem_genusOne_of_explicit_standard_unitSurfaceLower
    (curve : HyperellipticCurve 1)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (unitSurfaceLower :
      CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate
        (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
          curve branches)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_explicit_standard_periods
    curve branches unitSurfaceLower.toScalarCandidateLowerCertificate
      unitSurfaceLower.genusOneTransportCertificate

/-- Minimal explicit-data genus-one entry point from the canonical two-face
commutator surface lower bound. -/
def finiteRiemannPeriodTheorem_genusOne_of_explicit_standard_canonicalFaceLower
    (curve : HyperellipticCurve 1)
    (branches : CCL.Riemann.BranchIsolation.Data curve)
    (faceLower :
      CCL.Riemann.PreparedEnergySurface.GenusOneCanonicalFaceLowerCertificate
        (CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
          curve branches)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_explicit_standard_unitSurfaceLower
    curve branches faceLower.toUnitSurfaceLowerCertificate

/-- Execute a bounded inverse-tail scan on the canonical standard A-period
matrix constructed from the curve.  Failure is ordinary finite information:
the requested prefix contained no anchor whose exact rational centre cleared
the geometric tail error. -/
def automaticStandardInverseTailSearch {genus : Nat}
    (curve : HyperellipticCurve genus) (bound : Nat) :
    Option (BoundedScalarTailSeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix bound) :=
  scalarTailSeparationWithin?
    (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
      curve).aMatrix bound

/-- Assemble the theorem from the canonical switched branch-cut programs.
The period data and its realization of the computed symplectic basis are
constructed from the curve alone; only the genuinely analytic bilinear,
inverse-separation, and energy inputs remain. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_periods {genus : Nat}
    (curve : HyperellipticCurve genus)
    (preBilinear : CCL.Riemann.FiniteBilinear.PreNormalizationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_certificates curve
    { periodData :=
        CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve
      cycles_realization :=
        CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
          curve
      preBilinear := preBilinear
      aInverse := inverseLower.toScaledInverseCertificate
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse,
          CCL.Riemann.FiniteEnergy.normalizedData] using
          surfaceEnergy.toCertificate }

/-- Tail-separated automatic theorem.  A finite number of coarse canonical
inverse-scalar centres may vanish: normalization drops that prefix, records
the operational equivalence with the original scalar, and uses finite cell
energy attached directly to the resulting normalized process. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_tail
    {genus : Nat} (curve : HyperellipticCurve genus)
    (preBilinear : CCL.Riemann.FiniteBilinear.PreNormalizationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (inverseTail : ScalarTailSeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (energy : CCL.Riemann.FiniteEnergy.Certificate
      (NormalizedPeriodData.ofScaledInverse
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
        inverseTail.toScaledInverseCertificate)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_certificates curve
    { periodData :=
        CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve
      cycles_realization :=
        CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
          curve
      preBilinear := preBilinear
      aInverse := inverseTail.toScaledInverseCertificate
      energy := energy }

/-- Genus-generic automatic theorem whose first bilinear input is given by
independent local two-dimensional triangulations.  Exact incidence proves
internal-edge cancellation, so the analytic hypotheses are per-face wedge
estimates rather than a comparison with the assembled global residual. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_localFaces
    {genus : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve
    { stokesClosure := localFaces.toFiniteStokesClosure }
    inverseLower surfaceEnergy

/-- Automatic theorem from genuine refining cut-surface meshes.  Unlike the
fixed-face compatibility constructor, every refinement may introduce a new
finite vertex and triangle bank; exact incidence and the summed local wedge
budgets derive the first bilinear relation. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces
    {genus : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve
    { stokesClosure := localFaces.toFiniteStokesClosure }
    inverseLower surfaceEnergy

/-- Fully tail-compatible automatic theorem from refining cut-surface Stokes
and finite normalized cell energy.  Coarse singular inverse centres may be
discarded without weakening the operational matrix identities. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tail
    {genus : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseTail : ScalarTailSeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (energy : CCL.Riemann.FiniteEnergy.Certificate
      (NormalizedPeriodData.ofScaledInverse
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
        inverseTail.toScaledInverseCertificate)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_tail curve
    { stokesClosure := localFaces.toFiniteStokesClosure }
    inverseTail energy

/-- Geometry-complete tail-compatible theorem interface.  The first relation
comes from refinement-dependent cut-surface meshes; the second comes from
controlled finite surface cells whose boundary error is paid before a
retained exact quotient sample is transported to the persistent centre. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tailControlled
    {genus : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseTail : ScalarTailSeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseTail) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tail
    curve localFaces inverseTail surfaceEnergy.toEnergyCertificate

/-- The strongest automatic-standard constructor after a successful bounded
inverse scan.  The scan result supplies the tail certificate and retains its
auditable finite search bound; the remaining inputs are the two genuine
cut-surface calculations. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_boundedTailControlled
    {genus searchBound : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseFound : BoundedScalarTailSeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix searchBound)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseFound.certificate) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tailControlled
    curve localFaces inverseFound.certificate surfaceEnergy

/-- Genus-generic automatic theorem from the exact two-triangle algebraic
decomposition of every symplectic handle.  Exact commutator incidence and
boundary matching are constructed internally; callers supply one shrinking
cancellation modulus for each strict-upper differential pair. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_handleFaces
    {genus : Nat} (curve : HyperellipticCurve genus)
    (handleFaces : CCL.Riemann.PreparedStokes.UpperHandleFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve
    { stokesClosure := handleFaces.toFiniteStokesClosure }
    inverseLower surfaceEnergy

/-- Generic-genus automatic standard theorem from one inverse-independent raw
surface lower theorem.  Raw energy proves every finite A-sample nonsingular
and computes the entire inverse-scalar prefix; the caller supplies only one
tail-clearance check plus the remaining finite normalization schedule. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_surfaceLower
    {genus : Nat} (curve : HyperellipticCurve genus)
    (preBilinear : CCL.Riemann.FiniteBilinear.PreNormalizationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  let inverseLower :=
    surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve preBilinear
    inverseLower
      (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Local triangulated first-relation data plus one raw surface-lower theorem
give the generic automatic theorem with no global Stokes comparison field. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_localFaces_surfaceLower
    {genus : Nat} (curve : HyperellipticCurve genus)
    (localFaces : CCL.Riemann.PreparedStokes.UpperLocalFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_surfaceLower curve
    { stokesClosure := localFaces.toFiniteStokesClosure }
    surfaceLower anchor tailPositive transport

/-- A canonical handle-bank cancellation modulus plus one
inverse-independent raw surface theorem gives the generic automatic result
without a separately assumed inverse certificate. -/
def finiteRiemannPeriodTheorem_of_automatic_standard_handleFaces_surfaceLower
    {genus : Nat} (curve : HyperellipticCurve genus)
    (handleFaces : CCL.Riemann.PreparedStokes.UpperHandleFaceReduction
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve))
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_surfaceLower curve
    { stokesClosure := handleFaces.toFiniteStokesClosure }
    surfaceLower anchor tailPositive transport

/-- For genus two the complete first bilinear relation has exactly one
independent off-diagonal equation.  The diagonal and transposed equations are
constructed by finite operational algebra. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_periods
    (curve : HyperellipticCurve 2)
    (zeroOne : CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve) 0 1).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name)
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve
    { stokesClosure :=
        CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusTwo_of_zeroOne
          (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
            curve) zeroOne }
    inverseLower surfaceEnergy

/-- Genus-two automatic theorem from its one genuine local triangulated
surface certificate.  The remaining three matrix entries are closed by
diagonal cancellation and skew symmetry. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_localFaces
    (curve : HyperellipticCurve 2)
    (localFaces : CCL.Riemann.PreparedStokes.LocalFaceCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve) 0 1)
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_localFaces curve
    (CCL.Riemann.PreparedStokes.UpperLocalFaceReduction.genusTwo
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      localFaces)
    inverseLower surfaceEnergy

/-- Genus-two automatic theorem from one shrinking cancellation modulus over
the four exact terms obtained by splitting its two commutator polygons. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_handleFaces
    (curve : HyperellipticCurve 2)
    (handleFaces : CCL.Riemann.PreparedStokes.HandleFaceCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve) 0 1)
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_handleFaces curve
    (CCL.Riemann.PreparedStokes.UpperHandleFaceReduction.genusTwo
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      handleFaces)
    inverseLower surfaceEnergy

/-- In genus two, one off-diagonal Stokes equation and one raw surface theorem
now suffice for all finite A-sample nondegeneracy.  Only a single persistent
tail-clearance check and the normalization schedule remain separate. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_surfaceLower
    (curve : HyperellipticCurve 2)
    (zeroOne : CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve) 0 1).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name)
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_surfaceLower curve
    { stokesClosure :=
        CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusTwo_of_zeroOne
          (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
            curve) zeroOne }
    surfaceLower anchor tailPositive transport

/-- The reduced genus-two entry point with local triangle Stokes data and raw
surface energy. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_localFaces_surfaceLower
    (curve : HyperellipticCurve 2)
    (localFaces : CCL.Riemann.PreparedStokes.LocalFaceCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve) 0 1)
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_localFaces_surfaceLower curve
    (CCL.Riemann.PreparedStokes.UpperLocalFaceReduction.genusTwo
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      localFaces)
    surfaceLower anchor tailPositive transport

/-- Reduced genus-two entry point with the canonical four-term handle-bank
cancellation modulus and one raw surface-energy theorem. -/
def finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_handleFaces_surfaceLower
    (curve : HyperellipticCurve 2)
    (handleFaces : CCL.Riemann.PreparedStokes.HandleFaceCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve) 0 1)
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve))
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse
            (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
              curve).aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_handleFaces_surfaceLower curve
    (CCL.Riemann.PreparedStokes.UpperHandleFaceReduction.genusTwo
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      handleFaces)
    surfaceLower anchor tailPositive transport

/-- For a genus-one curve, the canonical switched period programs and their
basis realization are automatic, and the first bilinear relation is the
single diagonal identity.  Thus only finite A-period separation and
geometry-backed energy transport remain as inputs. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_periods
    (curve : HyperellipticCurve 1)
    (inverseLower : ScalarCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      inverseLower) :
    Result curve :=
  finiteRiemannPeriodTheorem_of_automatic_standard_periods curve
    { stokesClosure :=
        CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne
          (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
            curve) }
    inverseLower surfaceEnergy

/-- Dimension-one pivot algebra reduces the inverse input further to a
uniform lower bound on the sole standard A-period itself. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_aPeriodLower
    (curve : HyperellipticCurve 1)
    (aPeriodLower : OneByOneEntryCandidateLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      aPeriodLower.toScalarCandidateLowerCertificate) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_periods curve
    aPeriodLower.toScalarCandidateLowerCertificate surfaceEnergy

/-- A finite prefix and one tail-clearance inequality suffice for the
dimension-one A-period lower bound, so the public automatic theorem never
needs an infinite family of caller-supplied inequalities. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_finiteAPeriodSeparation
    (curve : HyperellipticCurve 1)
    (aPeriodSeparation : FiniteOneByOneEntrySeparationCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve).aMatrix)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData curve)
      aPeriodSeparation.toScalarCandidateLowerCertificate) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_periods curve
    aPeriodSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- In genus one a single pre-normalization cut-surface theorem supplies
A-period nondegeneracy, every normalized boundary reduction, and all finite
normalization radii through the fixed-box energy lower. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_rawEnergy
    (curve : HyperellipticCurve 1)
    (raw : CCL.Riemann.PreparedEnergy.RawCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_periods curve
    raw.toScalarCandidateLowerCertificate
    raw.genusOneTransportCertificate

/-- Sharp genus-one entry point: a caller proves the cut-surface inequality
only for the standard unit differential `dx/y`.  Exact one-dimensional
homogeneity constructs A-period separation and every normalized coefficient
request internally. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    (curve : HyperellipticCurve 1)
    (unitSurfaceLower :
      CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_periods curve
    unitSurfaceLower.toScalarCandidateLowerCertificate
    unitSurfaceLower.genusOneTransportCertificate

/-- Two-dimensional genus-one entry point.  Exact triangulation incidence,
boundary matching, and local face energy bounds derive the unit surface
inequality before the one-dimensional homogeneity reduction is applied. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitTriangulation
    (curve : HyperellipticCurve 1)
    (surface :
      CCL.Riemann.PreparedEnergySurface.GenusOneUnitTriangulatedSurfaceCertificate
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    curve surface.toUnitSurfaceLowerCertificate

/-- Stronger local-analytic genus-one entry point.  Each triangle carries a
rational affine differential model; exact Jacobian algebra derives face
nonnegativity and the selected positive lower before finite incidence closes
the surface. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitAffineTriangulation
    (curve : HyperellipticCurve 1)
    (surface :
      CCL.Riemann.PreparedEnergySurface.GenusOneUnitAffineTriangulatedSurfaceCertificate
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    curve surface.toUnitSurfaceLowerCertificate

/-- Prepared-quadrature-facing genus-one entry point.  Primitive vertices may
differ from their affine local models; three explicit rational square budgets
per face pay those errors before the exact surface incidence theorem. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitErrorControlledAffineTriangulation
    (curve : HyperellipticCurve 1)
    (surface :
      CCL.Riemann.PreparedEnergySurface.GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    curve surface.toUnitSurfaceLowerCertificate

/-- Smallest canonical genus-one cut-polygon entry point.  One local lower
bound on the first triangle `0,a,a+b` suffices: the diagonal subdivision has
two equal face energies whose sum is exactly the raw A/B pairing. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_canonicalFaceLower
    (curve : HyperellipticCurve 1)
    (faceLower :
      CCL.Riemann.PreparedEnergySurface.GenusOneCanonicalFaceLowerCertificate
        (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
          curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    curve faceLower.toUnitSurfaceLowerCertificate

/-- Equivalent minimal genus-one entry point: callers prove only the checked
surface lower inequality.  The edge-free exact decomposition and its
nonnegative remainder are constructed internally. -/
def finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_surfaceLower
    (curve : HyperellipticCurve 1)
    (surfaceLower : CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
      (CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
        curve)) :
    Result curve :=
  finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_rawEnergy curve
    surfaceLower.toRawCertificate

/-- Complete genus-one input after the automatic diagonal Stokes theorem has
removed the first-relation boundary field. -/
structure GenusOnePreparedCertificate
    (curve : HyperellipticCurve 1) where
  geometry : CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve
  scheduleCores :
    CCL.Riemann.PreparedCycleModels.StrictCompatiblePeriodCores curve geometry
  realizes : geometry.Realizes
    (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles
  inverseSeparation : FiniteScalarSeparationCertificate
    scheduleCores.toCompatiblePeriodSchedules.toPeriodData.aMatrix
  surfaceEnergy : CCL.Riemann.PreparedEnergy.CompatibleControlledCertificate
    scheduleCores.toCompatiblePeriodSchedules
    inverseSeparation.toScalarCandidateLowerCertificate

/-- Packaged finite period theorem for an elliptic hyperelliptic curve.  Its
input contains no Stokes or symmetry assumption. -/
def finiteRiemannPeriodTheorem_genusOne
    (curve : HyperellipticCurve 1)
    (certificate : GenusOnePreparedCertificate curve) : Result curve :=
  let schedules := certificate.scheduleCores.toCompatiblePeriodSchedules
  finiteRiemannPeriodTheorem_genusOne_of_prepared_schedules curve
    schedules certificate.realizes
      certificate.inverseSeparation.toScalarCandidateLowerCertificate
        certificate.surfaceEnergy.toTransportCertificate

/-- Complete finite analytic input in its dependency order.  Every field is
finite data or a request-indexed finite certificate: common prepared cycle
geometry, compatible integration programs, realization of the computed
symplectic basis, finite inverse-scalar separation, the independent
upper-triangular first-relation boundary reductions, and the controlled-error
geometry-backed second-relation reduction. -/
structure PreparedCertificate {genus : Nat}
    (curve : HyperellipticCurve genus) where
  geometry : CCL.Riemann.PreparedCycleModels.SymplecticCycleSchedule curve
  scheduleCores :
    CCL.Riemann.PreparedCycleModels.StrictCompatiblePeriodCores curve geometry
  realizes : geometry.Realizes
    (CCL.Riemann.BranchCutLifts.symplecticBasis curve).cycles
  inverseSeparation : FiniteScalarSeparationCertificate
    scheduleCores.toCompatiblePeriodSchedules.toPeriodData.aMatrix
  boundaryReduction :
    CCL.Riemann.PreparedStokes.CompatibleUpperCellularProgramBoundaryReduction
      scheduleCores.toCompatiblePeriodSchedules
  surfaceEnergy : CCL.Riemann.PreparedEnergy.CompatibleControlledCertificate
    scheduleCores.toCompatiblePeriodSchedules
    inverseSeparation.toScalarCandidateLowerCertificate

/-- Finite Riemann period theorem from one complete prepared certificate.
The output computes the degree-dependent topology and exposes persistent A/B
periods, the normalized persistent matrix, operational symmetry, and a
positive rational witness for every nonzero rational-vector request. -/
def finiteRiemannPeriodTheorem {genus : Nat}
    (curve : HyperellipticCurve genus)
    (certificate : PreparedCertificate curve) : Result curve :=
  let schedules := certificate.scheduleCores.toCompatiblePeriodSchedules
  finiteRiemannPeriodTheorem_of_prepared_schedules curve
    schedules certificate.realizes
      certificate.inverseSeparation.toScalarCandidateLowerCertificate
        certificate.boundaryReduction
          certificate.surfaceEnergy.toTransportCertificate

/-! ## Unconditional genus-zero case -/

/-- There are no holomorphic basis differentials in genus zero, so the two
period-program families and both period matrices are genuinely empty. -/
def genusZeroPeriodData (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) : PeriodData curve where
  cycles := cycles
  aProgram := fun differential => Fin.elim0 differential
  bProgram := fun differential => Fin.elim0 differential

/-- The empty `A` matrix has canonical inverse scalar one at every finite
sample. -/
def genusZeroInverseLower (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) :
    ScalarCandidateLowerCertificate
      (genusZeroPeriodData curve cycles).aMatrix where
  lowerSq := 1
  positive := by decide
  sample_lower := by
    intro index
    change (1 : Coordinate) <=
      RFAP.ConstructiveGaussian.Gaussian.normSq 1
    rw [RFAP.ConstructiveGaussian.Gaussian.normSq_one]

/-- The empty fraction-free inverse is obtained by candidate apartification,
with no independently supplied whole-ball certificate. -/
def genusZeroInverse (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) :
    ScaledInverseCertificate (genusZeroPeriodData curve cycles).aMatrix :=
  (genusZeroInverseLower curve cycles).toScaledInverseCertificate

/-- Complete normalized period data in genus zero. -/
def genusZeroNormalized (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) : NormalizedPeriodData curve where
  toPeriodData := genusZeroPeriodData curve cycles
  aInverse := genusZeroInverse curve cycles

/-- The canonical primitive closure and quantitative positivity request are
both vacuous in dimension zero: a closure query has no row, while a claimed
nonzero rational vector contains an impossible `Fin 0` witness. -/
def genusZeroFiniteBilinear (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) :
    CCL.Riemann.FiniteBilinear.Certificate
  (genusZeroNormalized curve cycles) where
  preNormalization :=
    { stokesClosure :=
        { closed := fun row => Fin.elim0 row } }
  energy :=
    { certify := fun _vector nonzero => Fin.elim0 nonzero.index }

/-- Public bilinear interface derived from the empty paired boundary. -/
def genusZeroBilinear (curve : HyperellipticCurve 0)
    (cycles : LiftedSymplecticCycles 2 0) :
    BilinearRelationsCertificate (genusZeroNormalized curve cycles) :=
  (genusZeroFiniteBilinear curve cycles).toBilinearRelations

/-- The finite Riemann period theorem without analytic input in genus zero.
This is a complete base case of the general construction: branch geometry,
cellular topology, Euler characteristic, the empty normalized matrix, and
both finite bilinear relations are all constructed from the curve alone. -/
def finiteRiemannPeriodTheorem_genusZero
    (curve : HyperellipticCurve 0) : Result curve := by
  let basis := CCL.Riemann.BranchCutLifts.symplecticBasis curve
  let normalized := genusZeroNormalized curve basis.cycles
  let bilinear := genusZeroFiniteBilinear curve basis.cycles
  let analytic : AnalyticCertificate curve basis :=
    { periodData := normalized.toPeriodData
      cycles_realization :=
        CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization.ofEq
          rfl
      preBilinear := bilinear.preNormalization
      aInverse := normalized.aInverse
      energy := by
        simpa only [NormalizedPeriodData.ofScaledInverse] using bilinear.energy }
  exact
    { basis := basis
      topology := topologyCertificate curve
      eulerCharacteristic := curve.finiteCellModel_eulerCharacteristic
      analytic := analytic }

namespace Result

/-- The constructed branch family has exactly the polynomial degree many
finite sites. -/
theorem branchPointCount {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) :
    result.basis.family.cuts.configuration.branches.siteCount =
      curve.polynomial.natDegree :=
  result.basis.family.cuts.configuration.branches.count_eq

/-- Every constructed branch-point name returns exactly every requested
finite prefix. -/
theorem branchPointRequest {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (index : CCL.Riemann.BranchIsolation.Data.Index
      result.basis.family.cuts.configuration.branches)
    (count : Nat) :
    (CCL.Riemann.BranchIsolation.Data.name
        result.basis.family.cuts.configuration.branches index).machine.emitted.IsPrefix
      (CCL.ProgressiveTransducer.advance
        (CCL.Riemann.BranchIsolation.Data.name
          result.basis.family.cuts.configuration.branches index).machine count).emitted /\
    (CCL.ProgressiveTransducer.advance
      (CCL.Riemann.BranchIsolation.Data.name
        result.basis.family.cuts.configuration.branches index).machine count).emitted.length = count :=
  result.basis.family.cuts.configuration.branches.name_productive index count

/-- Every standard branch cut has an explicitly closed two-sheet lift. -/
def branchCutLift {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) (index : Fin (genus + 1)) :
    LiftedCycleRefinement 2 :=
  result.basis.family.cycleAt index

theorem branchCutLift_returns_to_startingSheet {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (index : Fin (genus + 1)) (refinement : Nat) :
    ((result.branchCutLift index).liftedPath refinement).path.sheetTransport.forward
        ((result.branchCutLift index).liftedPath refinement).basepoint.sheet =
      ((result.branchCutLift index).liftedPath refinement).basepoint.sheet :=
  result.basis.family.returns_to_startingSheet index refinement

/-- The automatically constructed lifted `a` paths have zero mutual
intersection in their exact cellular traces. -/
theorem lifted_a_intersection {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (result.basis.aTrace left) (result.basis.aTrace right) = 0 :=
  result.basis.a_a left right

/-- The automatically constructed lifted `b` paths have zero mutual
intersection. -/
theorem lifted_b_intersection {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (result.basis.bTrace left) (result.basis.bTrace right) = 0 :=
  result.basis.b_b left right

/-- The mixed intersection matrix of the constructed lifted basis is the
identity. -/
theorem lifted_a_b_intersection {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (result.basis.aTrace left) (result.basis.bTrace right) =
        if left = right then 1 else 0 :=
  result.basis.a_b left right

def periodData {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) : PeriodData curve :=
  result.analytic.normalized.toPeriodData

/-- The operational fraction-free inverse satisfies the left scaled identity.
This statement remains valid when inverse separation begins only after a
certified finite tail shift. -/
def aInverse_left_identity {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (row column : Fin genus) :
    CCL.OperationalEquivalence.NamedEquivalent
      (matrixMul result.analytic.normalized.aInverse.adjugate
        result.periodData.aMatrix row column).name
      (scaleIdentity result.analytic.normalized.aInverse.scalar
        row column).name :=
  result.analytic.normalized.aInverse.left_identity row column

/-- The same tail-compatible fraction-free presentation satisfies the right
scaled identity. -/
def aInverse_right_identity {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (row column : Fin genus) :
    CCL.OperationalEquivalence.NamedEquivalent
      (matrixMul result.periodData.aMatrix
        result.analytic.normalized.aInverse.adjugate row column).name
      (scaleIdentity result.analytic.normalized.aInverse.scalar
        row column).name :=
  result.analytic.normalized.aInverse.right_identity row column

/-- The integration programs realize the automatically constructed two-sheet
cut basis.  Unrefined programs may do so by equality; prepared programs carry
the exact raw bridge or owner-boundary construction behind every finite
subdivision. -/
theorem periodCycles_realize_branchCutCycles {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve) :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization curve
      result.periodData.cycles result.basis.cycles :=
  result.analytic.cycles_realization

def omega {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) : NamedMatrix genus :=
  result.analytic.normalized.omega

/-- Every requested `A`-period entry returns a finite shared-table contract. -/
theorem aPeriodRequest {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) (differential cycle : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract result.periodData.table.channels
      (result.periodData.aMatrix differential cycle) target positive count :=
  result.periodData.aEntry_sharedRequest
    differential cycle target positive count

/-- Every requested `B`-period entry returns the corresponding finite
shared-table contract. -/
theorem bPeriodRequest {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) (differential cycle : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract result.periodData.table.channels
      (result.periodData.bMatrix differential cycle) target positive count :=
  result.periodData.bEntry_sharedRequest
    differential cycle target positive count

/-- Every normalized `Ω` entry likewise answers one finite shared-table
request. -/
theorem omegaRequest {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) (row column : Fin genus)
    (target : CCL.ProgressiveFiniteTable.Coordinate) (positive : 0 < target)
    (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract
      result.analytic.normalized.omegaTable.channels
      (result.omega row column) target positive count :=
  result.analytic.normalized.omegaEntry_sharedRequest
    row column target positive count

/-- The normalized period matrix is operationally symmetric. -/
def omega_symmetric {genus : Nat} {curve : HyperellipticCurve genus}
    (result : Result curve) (row column : Fin genus) :
    CCL.OperationalEquivalence.NamedEquivalent
      (result.omega row column).name (result.omega column row).name :=
  result.analytic.bilinear.symmetry.symmetric row column

/-- Every displayed nonzero rational vector and positive request produces
finite cell energy clearing the normalized matrix enclosure budget. -/
def omega_positive_energy_request {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FiniteEnergy.RequestCertificate
      result.analytic.normalized vector nonzero target positive :=
  result.analytic.normalizedEnergy.certify vector nonzero target positive

/-- The finite energy comparison selects a refinement whose rational centre
strictly exceeds its computed error budget. -/
def omega_positive_margin_request {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FinitePositivity.MarginCertificate
      result.analytic.normalized vector nonzero target positive :=
  (result.omega_positive_energy_request
    vector nonzero target positive).toMarginCertificate

/-- The centre-margin request canonically produces explicit positive entry
radii and a positive rational output margin. -/
def omega_positive_radius_request {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FinitePositivity.RadiusCertificate
      result.analytic.normalized vector nonzero
      target positive :=
  (result.omega_positive_margin_request
    vector nonzero target positive).toRadiusCertificate

/-- The automatically computed entrywise error budgets and weighted
perturbation inequalities. -/
def omega_positive_robust_request {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    CCL.Riemann.FinitePositivity.RequestCertificate
      result.analytic.normalized vector nonzero target positive :=
  (result.omega_positive_radius_request vector nonzero target positive).toRequestCertificate

/-- Public positivity contract derived by finite perturbation summation from
the robust request data. -/
def omega_positive_request {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    PositiveRequestCertificate result.analytic.normalized vector nonzero
      target positive :=
  (result.omega_positive_robust_request vector nonzero target positive).toPositiveRequestCertificate

/-- The positive rational lower bound computed for one pointwise request. -/
def omega_positive_lower_bound {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) : Coordinate :=
  (result.omega_positive_request vector nonzero target positive).epsilon

theorem omega_positive_lower_bound_positive {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    0 < result.omega_positive_lower_bound vector nonzero target positive :=
  (result.omega_positive_request vector nonzero target positive).epsilon_positive

/-- The familiar positive-imaginary-part conclusion at the finite rational
centre selected by one request.  Both the centre and its strictly positive
lower margin are computed by the request certificate. -/
theorem omega_center_imaginaryQuadraticForm_positive {genus : Nat}
    {curve : HyperellipticCurve genus} (result : Result curve)
    (vector : RationalVector genus) (nonzero : NonzeroVector vector)
    (target : Coordinate) (positive : 0 < target) :
    let request := result.omega_positive_request vector nonzero target positive
    0 < imaginaryQuadraticForm vector
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  dsimp only
  exact (result.omega_positive_request vector nonzero target positive).epsilon_positive.trans
    (result.omega_positive_request vector nonzero target positive).center_positive

end Result

end CCL.Riemann.FinitePeriodTheorem
