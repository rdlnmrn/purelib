import CCL.Riemann.FinitePeriodTheorem
import CCL.Riemann.FinitePeriodCurves

/-!
# Worked finite hyperelliptic period examples

This module records explicit squarefree cyclic curves for the worked examples
of the finite period theorem.  Every polynomial is the concrete finite dense
power polynomial `Z^d - 1`.  Its nonzeroness, degree, and displayed Bézout
identity are proved by the finite power-monodromy algebra, so the examples
introduce no separate squarefreeness assumption.

The five nontrivial examples are

* `y² = x³ - 1` and `y² = x⁴ - 1` in genus one;
* `y² = x⁵ - 1` and `y² = x⁶ - 1` in genus two;
* `y² = x⁷ - 1` in genus three.

Two genus-zero controls, `y² = x - 1` and `y² = x² - 1`, exercise the
complete unconditional theorem and its genuinely empty period matrix.

The topology statements below compute the classical Euler characteristics
`0`, `-2`, and `-4` and expose the expected symplectic intersection basis.
The analytic period conclusions will be attached to these same examples
through the public theorem interface, rather than by introducing unrelated
mock matrices.
-/

namespace CCL.Riemann.FinitePeriodExamples

/-! ## Computed classical topology -/

theorem linear_eulerCharacteristic :
    linearCurve.finiteCellModel.eulerCharacteristic = 2 := by
  simpa using linearCurve.finiteCellModel_eulerCharacteristic

theorem quadratic_eulerCharacteristic :
    quadraticCurve.finiteCellModel.eulerCharacteristic = 2 := by
  simpa using quadraticCurve.finiteCellModel_eulerCharacteristic

theorem cubic_eulerCharacteristic :
    cubicCurve.finiteCellModel.eulerCharacteristic = 0 := by
  simpa using cubicCurve.finiteCellModel_eulerCharacteristic

theorem quartic_eulerCharacteristic :
    quarticCurve.finiteCellModel.eulerCharacteristic = 0 := by
  simpa using quarticCurve.finiteCellModel_eulerCharacteristic

theorem quintic_eulerCharacteristic :
    quinticCurve.finiteCellModel.eulerCharacteristic = -2 := by
  simpa using quinticCurve.finiteCellModel_eulerCharacteristic

theorem sextic_eulerCharacteristic :
    sexticCurve.finiteCellModel.eulerCharacteristic = -2 := by
  simpa using sexticCurve.finiteCellModel_eulerCharacteristic

theorem septic_eulerCharacteristic :
    septicCurve.finiteCellModel.eulerCharacteristic = -4 := by
  simpa using septicCurve.finiteCellModel_eulerCharacteristic

/-! ## Complete genus-zero controls -/

def linearPeriodTheorem :
    CCL.Riemann.FinitePeriodTheorem.Result linearCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusZero
    linearCurve

def quadraticPeriodTheorem :
    CCL.Riemann.FinitePeriodTheorem.Result quadraticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusZero
    quadraticCurve

theorem linear_periodBranchPointCount :
    linearPeriodTheorem.basis.family.cuts.configuration.branches.siteCount =
      1 :=
  linearPeriodTheorem.branchPointCount.trans linear_degree

theorem quadratic_periodBranchPointCount :
    quadraticPeriodTheorem.basis.family.cuts.configuration.branches.siteCount =
      2 :=
  quadraticPeriodTheorem.branchPointCount.trans quadratic_degree

/-- There is no normalized-period entry in genus zero, exactly as in the
classical theorem. -/
theorem linear_omega_index_impossible (row : Fin 0) : False :=
  Fin.elim0 row

/-- Pointwise positivity has no nonzero vector request in dimension zero. -/
theorem quadratic_nonzero_vector_impossible
    (vector : CCL.Riemann.PeriodMatrix.RationalVector 0)
    (nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector vector) : False :=
  Fin.elim0 nonzero.index

/-! ## Explicit symplectic bases -/

def cubicBasis := CCL.Riemann.BranchCutLifts.symplecticBasis cubicCurve
def quarticBasis := CCL.Riemann.BranchCutLifts.symplecticBasis quarticCurve
def quinticBasis := CCL.Riemann.BranchCutLifts.symplecticBasis quinticCurve
def sexticBasis := CCL.Riemann.BranchCutLifts.symplecticBasis sexticCurve
def septicBasis := CCL.Riemann.BranchCutLifts.symplecticBasis septicCurve

theorem cubic_branchPointCount :
    cubicBasis.family.cuts.configuration.branches.siteCount = 3 := by
  exact cubicBasis.family.cuts.configuration.branches.count_eq.trans
    cubic_degree

theorem quartic_branchPointCount :
    quarticBasis.family.cuts.configuration.branches.siteCount = 4 := by
  exact quarticBasis.family.cuts.configuration.branches.count_eq.trans
    quartic_degree

theorem quintic_branchPointCount :
    quinticBasis.family.cuts.configuration.branches.siteCount = 5 := by
  exact quinticBasis.family.cuts.configuration.branches.count_eq.trans
    quintic_degree

theorem sextic_branchPointCount :
    sexticBasis.family.cuts.configuration.branches.siteCount = 6 := by
  exact sexticBasis.family.cuts.configuration.branches.count_eq.trans
    sextic_degree

theorem septic_branchPointCount :
    septicBasis.family.cuts.configuration.branches.siteCount = 7 := by
  exact septicBasis.family.cuts.configuration.branches.count_eq.trans
    septic_degree

theorem cubic_a_b_intersection :
    CCL.Riemann.CellularHomology.intersection
      (cubicBasis.aTrace 0) (cubicBasis.bTrace 0) = 1 := by
  simpa using cubicBasis.a_b (0 : Fin 1) (0 : Fin 1)

theorem quartic_a_b_intersection :
    CCL.Riemann.CellularHomology.intersection
      (quarticBasis.aTrace 0) (quarticBasis.bTrace 0) = 1 := by
  simpa using quarticBasis.a_b (0 : Fin 1) (0 : Fin 1)

theorem quintic_symplectic_intersections (left right : Fin 2) :
    CCL.Riemann.CellularHomology.intersection
        (quinticBasis.aTrace left) (quinticBasis.bTrace right) =
      if left = right then 1 else 0 :=
  quinticBasis.a_b left right

theorem sextic_symplectic_intersections (left right : Fin 2) :
    CCL.Riemann.CellularHomology.intersection
        (sexticBasis.aTrace left) (sexticBasis.bTrace right) =
      if left = right then 1 else 0 :=
  sexticBasis.a_b left right

theorem septic_symplectic_intersections (left right : Fin 3) :
    CCL.Riemann.CellularHomology.intersection
        (septicBasis.aTrace left) (septicBasis.bTrace right) =
      if left = right then 1 else 0 :=
  septicBasis.a_b left right

/-! ## Analytic theorem entry points -/

/-- Canonical switched period programs for the cubic elliptic curve.  No
cycle geometry or integration schedule is supplied by the caller. -/
def cubicStandardPeriodData :
    CCL.Riemann.PeriodMatrix.PeriodData cubicCurve :=
  CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
    cubicCurve

/-- Canonical switched period programs for the quartic elliptic curve. -/
def quarticStandardPeriodData :
    CCL.Riemann.PeriodMatrix.PeriodData quarticCurve :=
  CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
    quarticCurve

/-- Canonical switched period programs for the odd genus-two example. -/
def quinticStandardPeriodData :
    CCL.Riemann.PeriodMatrix.PeriodData quinticCurve :=
  CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
    quinticCurve

/-- Canonical switched period programs for the even genus-two example. -/
def sexticStandardPeriodData :
    CCL.Riemann.PeriodMatrix.PeriodData sexticCurve :=
  CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
    sexticCurve

/-- The automatically generated cubic programs realize the displayed
symplectic branch-cut basis through exact switched subdivision. -/
theorem cubicStandardPeriodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      cubicCurve cubicStandardPeriodData.cycles cubicBasis.cycles := by
  exact
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
      cubicCurve

/-- The automatically generated quartic programs realize the displayed
symplectic branch-cut basis through exact switched subdivision. -/
theorem quarticStandardPeriodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      quarticCurve quarticStandardPeriodData.cycles quarticBasis.cycles := by
  exact
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
      quarticCurve

/-- The genus-two quintic programs follow the computed four-cycle symplectic
basis at every finite refinement. -/
theorem quinticStandardPeriodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      quinticCurve quinticStandardPeriodData.cycles quinticBasis.cycles := by
  exact
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
      quinticCurve

/-- The same automatic realization for the even sextic model. -/
theorem sexticStandardPeriodData_realizes_basis :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      sexticCurve sexticStandardPeriodData.cycles sexticBasis.cycles := by
  exact
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData_realization
      sexticCurve

/-- Any certified period programs on the cubic curve satisfy the first
bilinear relation automatically; genus one has no off-diagonal Stokes case. -/
def cubicStokesClosure
    (data : CCL.Riemann.PeriodMatrix.PeriodData cubicCurve) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure data :=
  CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne data

/-- The same automatic first relation applies to the quartic elliptic model. -/
def quarticStokesClosure
    (data : CCL.Riemann.PeriodMatrix.PeriodData quarticCurve) :
    CCL.Riemann.FiniteBilinear.FiniteStokesClosure data :=
  CCL.Riemann.FiniteBilinear.FiniteStokesClosure.genusOne data

/-- The remaining constructive nonvanishing input for the sole cubic
standard A-period. -/
abbrev CubicStandardAPeriodSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.FiniteOneByOneEntrySeparationCertificate
    cubicStandardPeriodData.aMatrix

/-- The remaining constructive nonvanishing input for the sole quartic
standard A-period. -/
abbrev QuarticStandardAPeriodSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.FiniteOneByOneEntrySeparationCertificate
    quarticStandardPeriodData.aMatrix

/-- One inverse-independent raw cut-surface theorem for all cubic standard
differential combinations and synchronized samples. -/
abbrev CubicStandardRawEnergyCertificate :=
  CCL.Riemann.PreparedEnergy.RawCertificate cubicStandardPeriodData

/-- The corresponding raw second-relation theorem for the quartic model. -/
abbrev QuarticStandardRawEnergyCertificate :=
  CCL.Riemann.PreparedEnergy.RawCertificate quarticStandardPeriodData

/-- The cubic analytic input reduced to the one canonical `dx/y` surface
inequality at every synchronized period sample. -/
abbrev CubicStandardUnitSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate
    cubicStandardPeriodData

/-- The identical one-differential input for the quartic elliptic model. -/
abbrev QuarticStandardUnitSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate
    quarticStandardPeriodData

/-- Genuine finite two-dimensional cubic cut-surface input: an oriented
triangulation and one local energy lower bound per face at every sample. -/
abbrev CubicStandardUnitTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitTriangulatedSurfaceCertificate
    cubicStandardPeriodData

/-- The corresponding triangulated cut-surface input for the quartic. -/
abbrev QuarticStandardUnitTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitTriangulatedSurfaceCertificate
    quarticStandardPeriodData

/-- Cubic surface input reduced further to affine local differential models
and exact rational coordinate triangles. -/
abbrev CubicStandardUnitAffineTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitAffineTriangulatedSurfaceCertificate
    cubicStandardPeriodData

/-- The corresponding affine local surface input for the quartic. -/
abbrev QuarticStandardUnitAffineTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitAffineTriangulatedSurfaceCertificate
    quarticStandardPeriodData

/-- Cubic affine surface model with explicit finite primitive-error budgets. -/
abbrev CubicStandardUnitErrorControlledAffineTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
    cubicStandardPeriodData

/-- Quartic affine surface model with the same local error accounting. -/
abbrev QuarticStandardUnitErrorControlledAffineTriangulatedSurfaceCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneUnitErrorControlledAffineTriangulatedSurfaceCertificate
    quarticStandardPeriodData

/-- Single canonical triangle lower bound for the cubic commutator polygon. -/
abbrev CubicStandardCanonicalFaceLowerCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneCanonicalFaceLowerCertificate
    cubicStandardPeriodData

/-- Single canonical triangle lower bound for the quartic commutator. -/
abbrev QuarticStandardCanonicalFaceLowerCertificate :=
  CCL.Riemann.PreparedEnergySurface.GenusOneCanonicalFaceLowerCertificate
    quarticStandardPeriodData

/-- Minimal cubic second-relation statement: every checked singleton surface
box lies below the synchronized raw period-pairing energy. -/
abbrev CubicStandardSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
    cubicStandardPeriodData

/-- Minimal quartic second-relation statement. -/
abbrev QuarticStandardSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
    quarticStandardPeriodData

/-- Minimal inverse-independent surface theorem for the odd genus-two
example. -/
abbrev QuinticStandardSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
    quinticStandardPeriodData

/-- Minimal inverse-independent surface theorem for the even genus-two
example. -/
abbrev SexticStandardSurfaceLowerCertificate :=
  CCL.Riemann.PreparedEnergy.RawSurfaceLowerCertificate
    sexticStandardPeriodData

/-- The sole independent first-relation equation for the quintic genus-two
standard period matrix. -/
abbrev QuinticStandardStokesZeroOneCertificate :=
  CCL.OperationalEquivalence.NamedEquivalent
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
      quinticStandardPeriodData 0 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

/-- The corresponding single off-diagonal Stokes equation for the sextic. -/
abbrev SexticStandardStokesZeroOneCertificate :=
  CCL.OperationalEquivalence.NamedEquivalent
    (CCL.Riemann.FiniteBilinear.periodPairingPrimitiveFinish
      sexticStandardPeriodData 0 1).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

/-- Genuine local two-dimensional triangulation input for the odd
genus-two example. -/
abbrev QuinticStandardLocalFaceCertificate :=
  CCL.Riemann.PreparedStokes.LocalFaceCertificate
    quinticStandardPeriodData 0 1

/-- Genuine local two-dimensional triangulation input for the even
genus-two example. -/
abbrev SexticStandardLocalFaceCertificate :=
  CCL.Riemann.PreparedStokes.LocalFaceCertificate
    sexticStandardPeriodData 0 1

/-- Refinement-dependent cut-surface mesh input for the odd genus-two
example. -/
abbrev QuinticStandardRefiningFaceCertificate :=
  CCL.Riemann.PreparedStokes.RefiningLocalFaceCertificate
    quinticStandardPeriodData 0 1

/-- Refinement-dependent cut-surface mesh input for the even genus-two
example. -/
abbrev SexticStandardRefiningFaceCertificate :=
  CCL.Riemann.PreparedStokes.RefiningLocalFaceCertificate
    sexticStandardPeriodData 0 1

/-- Canonical four-term handle-bank cancellation modulus for the odd
genus-two example.  The exact terms and their commutator boundary are fixed
by the standard period matrices. -/
abbrev QuinticStandardHandleFaceCertificate :=
  CCL.Riemann.PreparedStokes.HandleFaceCertificate
    quinticStandardPeriodData 0 1

/-- Canonical four-term handle-bank cancellation modulus for the even
genus-two example. -/
abbrev SexticStandardHandleFaceCertificate :=
  CCL.Riemann.PreparedStokes.HandleFaceCertificate
    sexticStandardPeriodData 0 1

abbrev QuinticStandardInverseSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.FiniteScalarSeparationCertificate
    quinticStandardPeriodData.aMatrix

abbrev SexticStandardInverseSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.FiniteScalarSeparationCertificate
    sexticStandardPeriodData.aMatrix

abbrev QuinticStandardTailSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.ScalarTailSeparationCertificate
    quinticStandardPeriodData.aMatrix

abbrev SexticStandardTailSeparationCertificate :=
  CCL.Riemann.PeriodMatrix.ScalarTailSeparationCertificate
    sexticStandardPeriodData.aMatrix

/-- Executably scan a finite prefix of the canonical quintic inverse-scalar
stream for a tail-clearance anchor. -/
def quinticStandardInverseTailSearch (bound : Nat) :=
  CCL.Riemann.FinitePeriodTheorem.automaticStandardInverseTailSearch
    quinticCurve bound

/-- The identical finite scan for the even-degree genus-two example. -/
def sexticStandardInverseTailSearch (bound : Nat) :=
  CCL.Riemann.FinitePeriodTheorem.automaticStandardInverseTailSearch
    sexticCurve bound

/-- The cubic theorem using the canonical period programs.  Its only
remaining arguments are a uniform finite lower bound for the sole A-period
and the controlled surface-energy comparison. -/
def cubicStandardPeriodTheorem
    (aPeriodSeparation : CubicStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      cubicStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_finiteAPeriodSeparation
    cubicCurve aPeriodSeparation surfaceEnergy

/-- The quartic theorem using the canonical period programs, with the same
two remaining analytic inputs as the cubic case. -/
def quarticStandardPeriodTheorem
    (aPeriodSeparation : QuarticStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quarticStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_finiteAPeriodSeparation
    quarticCurve aPeriodSeparation surfaceEnergy

/-- Genus-two quintic theorem from its one independent Stokes equation,
finite determinant separation, and normalized surface-energy transport. -/
def quinticStandardPeriodTheorem
    (stokes : QuinticStandardStokesZeroOneCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_periods
    quinticCurve stokes
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Even-degree genus-two counterpart with the same three constructive
analytic obligations and no redundant diagonal or transposed Stokes fields. -/
def sexticStandardPeriodTheorem
    (stokes : SexticStandardStokesZeroOneCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_periods
    sexticCurve stokes
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Quintic period theorem from local facewise Stokes estimates, exact mesh
incidence, inverse separation, and normalized surface-energy transport. -/
def quinticStandardPeriodTheorem_of_localFaces
    (localFaces : QuinticStandardLocalFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_localFaces
    quinticCurve localFaces
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Sextic counterpart using the same local two-dimensional interface. -/
def sexticStandardPeriodTheorem_of_localFaces
    (localFaces : SexticStandardLocalFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_localFaces
    sexticCurve localFaces
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Strongest quintic interface: a genuinely refining cut-surface mesh, one
tail inverse clearance, and controlled finite surface energy whose boundary
error is paid before normalization. -/
def quinticStandardPeriodTheorem_of_refiningTailControlled
    (localFaces : QuinticStandardRefiningFaceCertificate)
    (inverseTail : QuinticStandardTailSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      quinticStandardPeriodData inverseTail) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tailControlled
    quinticCurve
    (CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction.genusTwo
      quinticStandardPeriodData localFaces)
    inverseTail surfaceEnergy

/-- Even-degree genus-two counterpart of the complete refining/tail/error
interface. -/
def sexticStandardPeriodTheorem_of_refiningTailControlled
    (localFaces : SexticStandardRefiningFaceCertificate)
    (inverseTail : SexticStandardTailSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      sexticStandardPeriodData inverseTail) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_tailControlled
    sexticCurve
    (CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction.genusTwo
      sexticStandardPeriodData localFaces)
    inverseTail surfaceEnergy

/-- A successful bounded inverse scan replaces the separately assembled tail
certificate in the strongest quintic entry point. -/
def quinticStandardPeriodTheorem_of_refiningBoundedTailControlled
    {searchBound : Nat}
    (localFaces : QuinticStandardRefiningFaceCertificate)
    (inverseFound :
      CCL.Riemann.PeriodMatrix.BoundedScalarTailSeparationCertificate
        quinticStandardPeriodData.aMatrix searchBound)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      quinticStandardPeriodData inverseFound.certificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_boundedTailControlled
    quinticCurve
    (CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction.genusTwo
      quinticStandardPeriodData localFaces)
    inverseFound surfaceEnergy

/-- Even-degree genus-two theorem after the same executable bounded inverse
scan. -/
def sexticStandardPeriodTheorem_of_refiningBoundedTailControlled
    {searchBound : Nat}
    (localFaces : SexticStandardRefiningFaceCertificate)
    (inverseFound :
      CCL.Riemann.PeriodMatrix.BoundedScalarTailSeparationCertificate
        sexticStandardPeriodData.aMatrix searchBound)
    (surfaceEnergy : CCL.Riemann.PreparedEnergy.TailControlledCertificate
      sexticStandardPeriodData inverseFound.certificate) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_of_automatic_standard_refiningLocalFaces_boundedTailControlled
    sexticCurve
    (CCL.Riemann.PreparedStokes.UpperRefiningLocalFaceReduction.genusTwo
      sexticStandardPeriodData localFaces)
    inverseFound surfaceEnergy

/-- Quintic theorem using the exact two-triangle decomposition of each
symplectic handle and one shrinking modulus for the complete four-term sum. -/
def quinticStandardPeriodTheorem_of_handleFaces
    (handleFaces : QuinticStandardHandleFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_handleFaces
    quinticCurve handleFaces
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Even-degree counterpart with the same canonical four-term cancellation
modulus. -/
def sexticStandardPeriodTheorem_of_handleFaces
    (handleFaces : SexticStandardHandleFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusTwo_of_automatic_standard_handleFaces
    sexticCurve handleFaces
      inverseSeparation.toScalarCandidateLowerCertificate surfaceEnergy

/-- Strengthened quintic entry point: raw surface energy proves every finite
A-matrix sample nonsingular and computes the inverse prefix.  The remaining
inverse datum is one rational tail-clearance check. -/
def quinticStandardPeriodTheorem_of_surfaceLower
    (stokes : QuinticStandardStokesZeroOneCertificate)
    (surfaceLower : QuinticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      quinticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  quinticStandardPeriodTheorem stokes inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Even-degree genus-two surface-lower entry point with the same reduced
inverse obligation. -/
def sexticStandardPeriodTheorem_of_surfaceLower
    (stokes : SexticStandardStokesZeroOneCertificate)
    (surfaceLower : SexticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      sexticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  sexticStandardPeriodTheorem stokes inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Quintic reduced entry point with local triangle estimates and raw surface
energy. -/
def quinticStandardPeriodTheorem_of_localFaces_surfaceLower
    (localFaces : QuinticStandardLocalFaceCertificate)
    (surfaceLower : QuinticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      quinticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  quinticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Sextic reduced entry point with local triangle estimates and raw surface
energy. -/
def sexticStandardPeriodTheorem_of_localFaces_surfaceLower
    (localFaces : SexticStandardLocalFaceCertificate)
    (surfaceLower : SexticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      sexticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  sexticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Quintic reduced entry point with the canonical handle-bank cancellation
modulus and one raw surface lower theorem. -/
def quinticStandardPeriodTheorem_of_handleFaces_surfaceLower
    (handleFaces : QuinticStandardHandleFaceCertificate)
    (surfaceLower : QuinticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            quinticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      quinticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  quinticStandardPeriodTheorem handleFaces.closePrimitive inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- Sextic reduced entry point with the same four-term cancellation modulus. -/
def sexticStandardPeriodTheorem_of_handleFaces_surfaceLower
    (handleFaces : SexticStandardHandleFaceCertificate)
    (surfaceLower : SexticStandardSurfaceLowerCertificate)
    (anchor : Nat)
    (tailPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq
          ((CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.sample anchor) / 2 -
        CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.PeriodMatrix.canonicalScaledInverse
            sexticStandardPeriodData.aMatrix).scalar.errorScale anchor)
    (transport : CCL.Riemann.PreparedEnergy.RawTransportSchedule
      sexticStandardPeriodData
        (surfaceLower.toScalarCandidateLowerCertificate anchor tailPositive)) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  let inverseSeparation :=
    surfaceLower.toFiniteScalarSeparationCertificate anchor tailPositive
  sexticStandardPeriodTheorem handleFaces.closePrimitive inverseSeparation
    (transport.toTransportCertificate surfaceLower.toRawCertificate)

/-- The quintic raw surface inequality alone rules out singularity of every
displayed complete fraction-free A-inverse sample. -/
theorem quinticStandard_aScalarSample_nonzero
    (surfaceLower : QuinticStandardSurfaceLowerCertificate)
    (sampleIndex : Nat) :
    (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
      (CCL.Riemann.PeriodMatrix.sampledMatrix
        quinticStandardPeriodData.aMatrix sampleIndex)).scalar ≠ 0 :=
  surfaceLower.sampledCompleteScaledInverse_scalar_nonzero sampleIndex

/-- The same genuinely genus-two nondegeneracy theorem for the even sextic
model. -/
theorem sexticStandard_aScalarSample_nonzero
    (surfaceLower : SexticStandardSurfaceLowerCertificate)
    (sampleIndex : Nat) :
    (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
      (CCL.Riemann.PeriodMatrix.sampledMatrix
        sexticStandardPeriodData.aMatrix sampleIndex)).scalar ≠ 0 :=
  surfaceLower.sampledCompleteScaledInverse_scalar_nonzero sampleIndex

/-- Preferred cubic entry point: the raw finite cut-surface theorem itself
derives A-period separation, normalization radii, and every transported
positive-energy request. -/
def cubicStandardPeriodTheorem_of_rawEnergy
    (raw : CubicStandardRawEnergyCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_rawEnergy
    cubicCurve raw

/-- Preferred quartic entry point with the identical constructive dependency:
one raw second-relation certificate. -/
def quarticStandardPeriodTheorem_of_rawEnergy
    (raw : QuarticStandardRawEnergyCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_rawEnergy
    quarticCurve raw

/-- Cubic finite period theorem from only the standard `dx/y` surface
inequality; all nonzero rational coefficient combinations are derived by
exact genus-one homogeneity. -/
def cubicStandardPeriodTheorem_of_unitSurfaceLower
    (unitSurfaceLower : CubicStandardUnitSurfaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    cubicCurve unitSurfaceLower

/-- Quartic counterpart with the same single-differential analytic input. -/
def quarticStandardPeriodTheorem_of_unitSurfaceLower
    (unitSurfaceLower : QuarticStandardUnitSurfaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitSurfaceLower
    quarticCurve unitSurfaceLower

/-- Cubic result from local two-dimensional face inequalities and exact
triangulation incidence; no global surface-to-period inequality is assumed. -/
def cubicStandardPeriodTheorem_of_unitTriangulation
    (surface : CubicStandardUnitTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitTriangulation
    cubicCurve surface

/-- Quartic result through the same triangulated finite Stokes bridge. -/
def quarticStandardPeriodTheorem_of_unitTriangulation
    (surface : QuarticStandardUnitTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitTriangulation
    quarticCurve surface

/-- Cubic theorem from affine coordinate triangles; local energy and
nonnegativity are derived rather than supplied as fields. -/
def cubicStandardPeriodTheorem_of_unitAffineTriangulation
    (surface : CubicStandardUnitAffineTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitAffineTriangulation
    cubicCurve surface

/-- Quartic theorem through the same affine local Jacobian bridge. -/
def quarticStandardPeriodTheorem_of_unitAffineTriangulation
    (surface : QuarticStandardUnitAffineTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitAffineTriangulation
    quarticCurve surface

/-- Cubic theorem from approximate affine primitive triangles after all local
quadrature errors have been paid by rational square checks. -/
def cubicStandardPeriodTheorem_of_unitErrorControlledAffineTriangulation
    (surface :
      CubicStandardUnitErrorControlledAffineTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitErrorControlledAffineTriangulation
    cubicCurve surface

/-- Quartic theorem through the same error-controlled local affine bridge. -/
def quarticStandardPeriodTheorem_of_unitErrorControlledAffineTriangulation
    (surface :
      QuarticStandardUnitErrorControlledAffineTriangulatedSurfaceCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_unitErrorControlledAffineTriangulation
    quarticCurve surface

/-- Cubic result from its one independent canonical handle-triangle lower
bound. -/
def cubicStandardPeriodTheorem_of_canonicalFaceLower
    (faceLower : CubicStandardCanonicalFaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_canonicalFaceLower
    cubicCurve faceLower

/-- Quartic result from the corresponding single local triangle theorem. -/
def quarticStandardPeriodTheorem_of_canonicalFaceLower
    (faceLower : QuarticStandardCanonicalFaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_canonicalFaceLower
    quarticCurve faceLower

/-- Cubic theorem from only the genuine surface lower inequality, with the
decomposition remainder constructed automatically. -/
def cubicStandardPeriodTheorem_of_surfaceLower
    (surfaceLower : CubicStandardSurfaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_surfaceLower
    cubicCurve surfaceLower

/-- Quartic counterpart of the minimal second-relation interface. -/
def quarticStandardPeriodTheorem_of_surfaceLower
    (surfaceLower : QuarticStandardSurfaceLowerCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne_of_automatic_standard_surfaceLower
    quarticCurve surfaceLower

/-! The remaining analytic input is named curve by curve, so a completed
finite certificate cannot accidentally be applied to a different example. -/

abbrev CubicPreparedCertificate :=
  CCL.Riemann.FinitePeriodTheorem.GenusOnePreparedCertificate cubicCurve

abbrev QuarticPreparedCertificate :=
  CCL.Riemann.FinitePeriodTheorem.GenusOnePreparedCertificate quarticCurve

abbrev QuinticPreparedCertificate :=
  CCL.Riemann.FinitePeriodTheorem.PreparedCertificate quinticCurve

abbrev SexticPreparedCertificate :=
  CCL.Riemann.FinitePeriodTheorem.PreparedCertificate sexticCurve

abbrev SepticPreparedCertificate :=
  CCL.Riemann.FinitePeriodTheorem.PreparedCertificate septicCurve

def cubicPeriodTheorem (certificate : CubicPreparedCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result cubicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne
    cubicCurve certificate

def quarticPeriodTheorem (certificate : QuarticPreparedCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quarticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem_genusOne
    quarticCurve certificate

def quinticPeriodTheorem (certificate : QuinticPreparedCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result quinticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem
    quinticCurve certificate

def sexticPeriodTheorem (certificate : SexticPreparedCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result sexticCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem
    sexticCurve certificate

def septicPeriodTheorem (certificate : SepticPreparedCertificate) :
    CCL.Riemann.FinitePeriodTheorem.Result septicCurve :=
  CCL.Riemann.FinitePeriodTheorem.finiteRiemannPeriodTheorem
    septicCurve certificate

/-! A concrete nonzero rational test vector in every positive dimension. -/

def onesVector (predecessor : Nat) :
    CCL.Riemann.PeriodMatrix.RationalVector (predecessor + 1) :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun _ => 1

def onesVector_nonzero (predecessor : Nat) :
    CCL.Riemann.PeriodMatrix.NonzeroVector (onesVector predecessor) where
  index := 0
  coefficient_nonzero := by
    simp only [onesVector, RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
    decide

/-! Each worked curve now exposes the two familiar conclusions through its
own theorem result: symmetry for every matrix entry, and a strictly positive
imaginary quadratic form for the displayed all-ones vector. -/

def cubic_omega_symmetric (certificate : CubicPreparedCertificate)
    (row column : Fin 1) :=
  (cubicPeriodTheorem certificate).omega_symmetric row column

def quartic_omega_symmetric (certificate : QuarticPreparedCertificate)
    (row column : Fin 1) :=
  (quarticPeriodTheorem certificate).omega_symmetric row column

/-- Symmetry of the normalized cubic period matrix obtained from the
canonical switched programs. -/
def cubicStandard_omega_symmetric
    (aPeriodSeparation : CubicStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      cubicStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 1) :=
  (cubicStandardPeriodTheorem aPeriodSeparation surfaceEnergy).omega_symmetric
    row column

/-- Symmetry of the normalized quartic period matrix obtained from the
canonical switched programs. -/
def quarticStandard_omega_symmetric
    (aPeriodSeparation : QuarticStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quarticStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 1) :=
  (quarticStandardPeriodTheorem aPeriodSeparation surfaceEnergy).omega_symmetric
    row column

/-- The single quintic Stokes equation yields symmetry of all four normalized
period-matrix entries. -/
def quinticStandard_omega_symmetric
    (stokes : QuinticStandardStokesZeroOneCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (quinticStandardPeriodTheorem stokes inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- Full normalized symmetry for the even sextic example from its unique
independent off-diagonal surface identity. -/
def sexticStandard_omega_symmetric
    (stokes : SexticStandardStokesZeroOneCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (sexticStandardPeriodTheorem stokes inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- Exact local triangulated Stokes data yields symmetry of every entry of
the odd genus-two normalized period matrix. -/
def quinticStandardLocal_omega_symmetric
    (localFaces : QuinticStandardLocalFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (quinticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- Exact local triangulated Stokes data likewise yields full symmetry for
the even genus-two sextic model. -/
def sexticStandardLocal_omega_symmetric
    (localFaces : SexticStandardLocalFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (sexticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- A canonical handle-bank cancellation modulus proves symmetry of all four
quintic normalized period entries. -/
def quinticStandardHandle_omega_symmetric
    (handleFaces : QuinticStandardHandleFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (quinticStandardPeriodTheorem_of_handleFaces handleFaces inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- A canonical handle-bank cancellation modulus proves symmetry of the
sextic normalized matrix. -/
def sexticStandardHandle_omega_symmetric
    (handleFaces : SexticStandardHandleFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate)
    (row column : Fin 2) :=
  (sexticStandardPeriodTheorem_of_handleFaces handleFaces inverseSeparation
    surfaceEnergy).omega_symmetric row column

/-- Symmetry obtained from the single cubic raw-energy theorem, with its
inverse no longer supplied independently. -/
def cubicStandardRaw_omega_symmetric
    (raw : CubicStandardRawEnergyCertificate)
    (row column : Fin 1) :=
  (cubicStandardPeriodTheorem_of_rawEnergy raw).omega_symmetric row column

/-- The analogous quartic symmetry conclusion. -/
def quarticStandardRaw_omega_symmetric
    (raw : QuarticStandardRawEnergyCertificate)
    (row column : Fin 1) :=
  (quarticStandardPeriodTheorem_of_rawEnergy raw).omega_symmetric row column

def quintic_omega_symmetric (certificate : QuinticPreparedCertificate)
    (row column : Fin 2) :=
  (quinticPeriodTheorem certificate).omega_symmetric row column

def sextic_omega_symmetric (certificate : SexticPreparedCertificate)
    (row column : Fin 2) :=
  (sexticPeriodTheorem certificate).omega_symmetric row column

def septic_omega_symmetric (certificate : SepticPreparedCertificate)
    (row column : Fin 3) :=
  (septicPeriodTheorem certificate).omega_symmetric row column

theorem cubic_omega_positive (certificate : CubicPreparedCertificate) :
    let result := cubicPeriodTheorem certificate
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (cubicPeriodTheorem certificate).omega_center_imaginaryQuadraticForm_positive
    (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

theorem quartic_omega_positive (certificate : QuarticPreparedCertificate) :
    let result := quarticPeriodTheorem certificate
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (quarticPeriodTheorem certificate).omega_center_imaginaryQuadraticForm_positive
    (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

/-- Strict positivity for the displayed nonzero vector in the normalized
cubic matrix computed from the canonical switched programs. -/
theorem cubicStandard_omega_positive
    (aPeriodSeparation : CubicStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      cubicStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate) :
    let result := cubicStandardPeriodTheorem aPeriodSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (cubicStandardPeriodTheorem aPeriodSeparation surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

/-- Strict positivity for the displayed nonzero vector in the normalized
quartic matrix computed from the canonical switched programs. -/
theorem quarticStandard_omega_positive
    (aPeriodSeparation : QuarticStandardAPeriodSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quarticStandardPeriodData
        aPeriodSeparation.toScalarCandidateLowerCertificate) :
    let result := quarticStandardPeriodTheorem aPeriodSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (quarticStandardPeriodTheorem aPeriodSeparation surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

/-- The genus-two quintic result gives the expected strict positive imaginary
quadratic form for the nonzero real vector `(1,1)`. -/
theorem quinticStandard_omega_positive
    (stokes : QuinticStandardStokesZeroOneCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := quinticStandardPeriodTheorem stokes inverseSeparation
      surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (quinticStandardPeriodTheorem stokes inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- The same `(1,1)` positive-definiteness witness for the even sextic
normalized period matrix. -/
theorem sexticStandard_omega_positive
    (stokes : SexticStandardStokesZeroOneCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := sexticStandardPeriodTheorem stokes inverseSeparation
      surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (sexticStandardPeriodTheorem stokes inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- The local-triangulation quintic route proves the expected strict positive
imaginary quadratic form on the displayed nonzero vector `(1,1)`. -/
theorem quinticStandardLocal_omega_positive
    (localFaces : QuinticStandardLocalFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := quinticStandardPeriodTheorem_of_localFaces localFaces
      inverseSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (quinticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- The even sextic local-triangulation route proves the same positive
definiteness witness. -/
theorem sexticStandardLocal_omega_positive
    (localFaces : SexticStandardLocalFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := sexticStandardPeriodTheorem_of_localFaces localFaces
      inverseSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (sexticStandardPeriodTheorem_of_localFaces localFaces inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- The canonical four-term quintic route yields the expected strict positive
imaginary quadratic form on `(1,1)`. -/
theorem quinticStandardHandle_omega_positive
    (handleFaces : QuinticStandardHandleFaceCertificate)
    (inverseSeparation : QuinticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      quinticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := quinticStandardPeriodTheorem_of_handleFaces handleFaces
      inverseSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (quinticStandardPeriodTheorem_of_handleFaces handleFaces inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- The even sextic canonical handle-bank route gives the same `(1,1)` strict
positivity witness. -/
theorem sexticStandardHandle_omega_positive
    (handleFaces : SexticStandardHandleFaceCertificate)
    (inverseSeparation : SexticStandardInverseSeparationCertificate)
    (surfaceEnergy : CCL.Riemann.FiniteEnergy.TransportCertificate
      sexticStandardPeriodData
        inverseSeparation.toScalarCandidateLowerCertificate) :
    let result := sexticStandardPeriodTheorem_of_handleFaces handleFaces
      inverseSeparation surfaceEnergy
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (sexticStandardPeriodTheorem_of_handleFaces handleFaces inverseSeparation
      surfaceEnergy).omega_center_imaginaryQuadraticForm_positive
        (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

/-- Strict cubic positivity transported from the same raw certificate that
constructs the A-period inverse. -/
theorem cubicStandardRaw_omega_positive
    (raw : CubicStandardRawEnergyCertificate) :
    let result := cubicStandardPeriodTheorem_of_rawEnergy raw
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (cubicStandardPeriodTheorem_of_rawEnergy raw).omega_center_imaginaryQuadraticForm_positive
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

/-- Strict quartic positivity with no separately assumed A-period lower. -/
theorem quarticStandardRaw_omega_positive
    (raw : QuarticStandardRawEnergyCertificate) :
    let result := quarticStandardPeriodTheorem_of_rawEnergy raw
    let request := result.omega_positive_request
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact
    (quarticStandardPeriodTheorem_of_rawEnergy raw).omega_center_imaginaryQuadraticForm_positive
      (onesVector 0) (onesVector_nonzero 0) 1 (by decide)

theorem quintic_omega_positive (certificate : QuinticPreparedCertificate) :
    let result := quinticPeriodTheorem certificate
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (quinticPeriodTheorem certificate).omega_center_imaginaryQuadraticForm_positive
    (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

theorem sextic_omega_positive (certificate : SexticPreparedCertificate) :
    let result := sexticPeriodTheorem certificate
    let request := result.omega_positive_request
      (onesVector 1) (onesVector_nonzero 1) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (sexticPeriodTheorem certificate).omega_center_imaginaryQuadraticForm_positive
    (onesVector 1) (onesVector_nonzero 1) 1 (by decide)

theorem septic_omega_positive (certificate : SepticPreparedCertificate) :
    let result := septicPeriodTheorem certificate
    let request := result.omega_positive_request
      (onesVector 2) (onesVector_nonzero 2) 1 (by decide)
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 2)
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
        result.analytic.normalized.omegaCenter request.refinementTarget
          request.refinementPositive row column) := by
  exact (septicPeriodTheorem certificate).omega_center_imaginaryQuadraticForm_positive
    (onesVector 2) (onesVector_nonzero 2) 1 (by decide)

/-! ## Unconditional exact finite period-matrix examples

The curve examples above exercise the full certified integration interface.
The following two exact rational-Gaussian models are unconditional worked
examples of the matrix conclusion itself.  They are finite analogues of the
familiar points in Siegel upper half-space: the square elliptic parameter
`[i]`, and the coupled genus-two matrix `[[2i,i],[i,2i]]`.  The second example
is not diagonal, so symmetry and positive definiteness are both substantive.
-/

abbrev ExactCoordinate := RFAP.ConstructiveFraction.Rational
abbrev ExactGaussianMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size
abbrev ExactNamedMatrix (size : Nat) :=
  CCL.Riemann.PeriodMatrix.NamedMatrix size
abbrev ExactNamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

def exactGaussianI : Gaussian := ⟨0, 1⟩
def exactGaussianTwoI : Gaussian := ⟨0, 2⟩

/-- The exact normalized matrix of the square elliptic lattice. -/
def squareEllipticOmega : ExactGaussianMatrix 1 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _ _ => exactGaussianI

/-- A symmetric, nondiagonal exact genus-two normalized matrix. -/
def coupledGenusTwoOmega : ExactGaussianMatrix 2 :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    if row = column then exactGaussianTwoI else exactGaussianI

@[simp] theorem squareEllipticOmega_apply (row column : Fin 1) :
    squareEllipticOmega row column = exactGaussianI :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem coupledGenusTwoOmega_apply (row column : Fin 2) :
    coupledGenusTwoOmega row column =
      if row = column then exactGaussianTwoI else exactGaussianI :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- A nonzero canonical rational has a strictly positive square. -/
theorem exact_rational_sq_pos {value : ExactCoordinate}
    (nonzero : value ≠ 0) : 0 < value ^ 2 := by
  have nonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct value
  exact ⟨nonnegative, fun reverse => nonzero
    ((RFAP.ConstructiveFraction.sq_eq_zero_direct value).1
      (RFAP.CanonicalFraction.le_antisymm _ _ reverse nonnegative))⟩

private theorem exact_sumFin_fin_zero (values : Fin 0 -> ExactCoordinate) :
    RFAP.ConstructiveFiniteMatrix.sumFin values = 0 := rfl

private theorem exact_sumFin_fin_two (values : Fin 2 -> ExactCoordinate) :
    RFAP.ConstructiveFiniteMatrix.sumFin values = values 0 + values 1 := by
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change values 0 +
      (values 1 + RFAP.ConstructiveFiniteMatrix.sumFin (fun index : Fin 0 =>
        values index.succ.succ)) = _
  rw [exact_sumFin_fin_zero, _root_.add_zero]

/-- In genus one the imaginary quadratic form is exactly `v₀²`. -/
theorem squareEllipticOmega_form
    (vector : CCL.Riemann.PeriodMatrix.RationalVector 1) :
    CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector
        squareEllipticOmega =
      (vector 0) ^ 2 := by
  unfold CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change RFAP.ConstructiveFiniteMatrix.sumFin (fun column : Fin 1 =>
      vector 0 * (squareEllipticOmega 0 column).im * vector column) +
      RFAP.ConstructiveFiniteMatrix.sumFin (fun row : Fin 0 =>
        RFAP.ConstructiveFiniteMatrix.sumFin (fun column : Fin 1 =>
          vector row.succ * (squareEllipticOmega row.succ column).im *
            vector column)) = _
  rw [exact_sumFin_fin_zero]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun column : Fin 1 =>
      vector 0 * exactGaussianI.im * vector column)
    (fun column => by rw [squareEllipticOmega_apply])]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change vector 0 * (1 : ExactCoordinate) * vector 0 +
      RFAP.ConstructiveFiniteMatrix.sumFin (fun column : Fin 0 =>
        vector 0 * exactGaussianI.im * vector column.succ) + 0 = _
  rw [exact_sumFin_fin_zero, RFAP.ConstructiveFraction.mul_one_direct,
    _root_.add_zero, _root_.add_zero, pow_two]

/-- The coupled genus-two form is the manifest sum of three squares
`v₀² + v₁² + (v₀+v₁)²`. -/
theorem coupledGenusTwoOmega_form
    (vector : CCL.Riemann.PeriodMatrix.RationalVector 2) :
    CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector
        coupledGenusTwoOmega =
      (vector 0) ^ 2 + ((vector 1) ^ 2 + (vector 0 + vector 1) ^ 2) := by
  unfold CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm
  rw [exact_sumFin_fin_two]
  change
    RFAP.ConstructiveFiniteMatrix.sumFin (fun column : Fin 2 =>
        vector 0 * (coupledGenusTwoOmega 0 column).im * vector column) +
      RFAP.ConstructiveFiniteMatrix.sumFin (fun column : Fin 2 =>
        vector 1 * (coupledGenusTwoOmega 1 column).im * vector column) = _
  rw [exact_sumFin_fin_two, exact_sumFin_fin_two]
  rw [coupledGenusTwoOmega_apply, coupledGenusTwoOmega_apply,
    coupledGenusTwoOmega_apply, coupledGenusTwoOmega_apply]
  simp only [if_true, if_neg (by decide : (0 : Fin 2) ≠ 1),
    if_neg (by decide : (1 : Fin 2) ≠ 0), exactGaussianI,
    exactGaussianTwoI]
  ring1

theorem squareEllipticOmega_symmetric (row column : Fin 1) :
    squareEllipticOmega row column = squareEllipticOmega column row := by
  unfold squareEllipticOmega
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

theorem coupledGenusTwoOmega_symmetric (row column : Fin 2) :
    coupledGenusTwoOmega row column = coupledGenusTwoOmega column row := by
  unfold coupledGenusTwoOmega
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  by_cases equal : row = column
  · subst column
    rfl
  · rw [if_neg equal, if_neg (fun reverse => equal reverse.symm)]

/-- Strict positivity for every nonzero rational vector in the elliptic
example. -/
theorem squareEllipticOmega_positive
    (vector : CCL.Riemann.PeriodMatrix.RationalVector 1)
    (nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector vector) :
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector
      squareEllipticOmega := by
  rw [squareEllipticOmega_form]
  have indexZero : nonzero.index = (0 : Fin 1) := by
    apply Fin.ext
    omega0
  exact exact_rational_sq_pos (by
    simpa only [indexZero] using nonzero.coefficient_nonzero)

/-- Strict positivity of the nondiagonal genus-two example, obtained
constructively from whichever displayed coefficient witnesses nonzeroness. -/
theorem coupledGenusTwoOmega_positive
    (vector : CCL.Riemann.PeriodMatrix.RationalVector 2)
    (nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector vector) :
    0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector
      coupledGenusTwoOmega := by
  rw [coupledGenusTwoOmega_form]
  rcases CCL.Riemann.HyperellipticCells.sheet_eq_zero_or_one nonzero.index with
    indexZero | indexOne
  · have firstNonzero : vector 0 ≠ 0 := by
      have indexLiteral : nonzero.index = (0 : Fin 2) :=
        indexZero.trans (by apply Fin.ext; rfl)
      have witness := nonzero.coefficient_nonzero
      rw [indexLiteral] at witness
      exact witness
    exact (exact_rational_sq_pos firstNonzero).trans_le
      (le_add_of_nonneg_right (add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (vector 1))
        (RFAP.ConstructiveFraction.sq_nonneg_direct
          (vector 0 + vector 1))))
  · have secondNonzero : vector 1 ≠ 0 := by
      have indexLiteral : nonzero.index = (1 : Fin 2) :=
        indexOne.trans (by apply Fin.ext; rfl)
      have witness := nonzero.coefficient_nonzero
      rw [indexLiteral] at witness
      exact witness
    exact add_pos_of_nonneg_of_pos
      (RFAP.ConstructiveFraction.sq_nonneg_direct (vector 0))
      ((exact_rational_sq_pos secondNonzero).trans_le
        (le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct
            (vector 0 + vector 1))))

/-- Exact finite matrix form of the two Riemann conclusions. -/
structure FiniteRiemannMatrixWitness (size : Nat) where
  omega : ExactGaussianMatrix size
  symmetric : forall row column, omega row column = omega column row
  positive : forall
    (vector : CCL.Riemann.PeriodMatrix.RationalVector size),
    CCL.Riemann.PeriodMatrix.NonzeroVector vector ->
      0 < CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector omega

namespace FiniteRiemannMatrixWitness

/-- Exact rational matrices are also productive CCL matrices. -/
def namedOmega {size : Nat} (witness : FiniteRiemannMatrixWitness size) :
    ExactNamedMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.ProgressiveCoherence.CoherentNamed.exact (witness.omega row column)

/-- Exact symmetry becomes operational equality of the corresponding CCL
entry names. -/
def operationally_symmetric {size : Nat}
    (witness : FiniteRiemannMatrixWitness size) (row column : Fin size) :
    ExactNamedEquivalent (witness.namedOmega row column).name
      (witness.namedOmega column row).name := by
  rw [namedOmega, RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    witness.symmetric row column]
  exact CCL.OperationalEquivalence.NamedEquivalent.refl _

/-- Explicit positive rational evidence returned for a nonzero vector. -/
def requestedMargin {size : Nat}
    (witness : FiniteRiemannMatrixWitness size)
    (vector : CCL.Riemann.PeriodMatrix.RationalVector size) :
    ExactCoordinate :=
  CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector witness.omega / 2

private theorem exact_half_lt_self {value : ExactCoordinate}
    (positive : 0 < value) : value / 2 < value := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : ExactCoordinate) < 2)).2
  calc
    value = value * 1 := by ring1
    _ < value * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct positive
        (by decide)

theorem requestedMargin_positive {size : Nat}
    (witness : FiniteRiemannMatrixWitness size)
    (vector : CCL.Riemann.PeriodMatrix.RationalVector size)
    (nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector vector) :
    0 < witness.requestedMargin vector :=
  RFAP.ConstructiveFraction.div_pos_direct (witness.positive vector nonzero)
    (by decide)

theorem requestedMargin_lt_form {size : Nat}
    (witness : FiniteRiemannMatrixWitness size)
    (vector : CCL.Riemann.PeriodMatrix.RationalVector size)
    (nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector vector) :
    witness.requestedMargin vector <
      CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm vector witness.omega :=
  exact_half_lt_self (witness.positive vector nonzero)

end FiniteRiemannMatrixWitness

/-- First unconditional nontrivial worked example: the exact elliptic matrix
`[i]`. -/
def squareEllipticMatrixWitness : FiniteRiemannMatrixWitness 1 where
  omega := squareEllipticOmega
  symmetric := squareEllipticOmega_symmetric
  positive := squareEllipticOmega_positive

/-- Second unconditional nontrivial worked example: the coupled exact
genus-two matrix `[[2i,i],[i,2i]]`. -/
def coupledGenusTwoMatrixWitness : FiniteRiemannMatrixWitness 2 where
  omega := coupledGenusTwoOmega
  symmetric := coupledGenusTwoOmega_symmetric
  positive := coupledGenusTwoOmega_positive

/-- On the displayed elliptic test vector `(1)`, the exact imaginary energy
is one and the returned positive rational margin is one half. -/
theorem squareElliptic_ones_energy :
    CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      squareEllipticMatrixWitness.omega = 1 := by
  change CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 0)
      squareEllipticOmega = 1
  rw [squareEllipticOmega_form]
  simp only [onesVector, RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  rfl

theorem squareElliptic_ones_margin :
    squareEllipticMatrixWitness.requestedMargin (onesVector 0) =
      (1 : ExactCoordinate) / 2 := by
  unfold FiniteRiemannMatrixWitness.requestedMargin
  rw [squareElliptic_ones_energy]

/-- On the genuinely two-dimensional vector `(1,1)`, the coupled matrix has
exact imaginary energy six and returns the positive rational margin three. -/
theorem coupledGenusTwo_ones_energy :
    CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      coupledGenusTwoMatrixWitness.omega = 6 := by
  change CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm (onesVector 1)
      coupledGenusTwoOmega = 6
  rw [coupledGenusTwoOmega_form]
  simp only [onesVector, RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  norm_num1
  rfl

theorem coupledGenusTwo_ones_margin :
    coupledGenusTwoMatrixWitness.requestedMargin (onesVector 1) = 3 := by
  unfold FiniteRiemannMatrixWitness.requestedMargin
  rw [coupledGenusTwo_ones_energy]
  decide

end CCL.Riemann.FinitePeriodExamples
