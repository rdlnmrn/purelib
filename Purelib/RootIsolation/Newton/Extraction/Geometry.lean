module

public import Purelib.RootIsolation.Newton.Extraction.Prepare
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.RootIsolation.Newton.Extraction

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree (NewtonCenterCertificate)
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget
open Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor

open Purelib
open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial

set_option genInjectivity false in
/-- Retained source, radius and Newton point of a local extraction.

The original current state and accuracy index the geometric data needed by
Newton bands. Exact radius readback and the original displacement, protected
strip and Taylor certificates accompany the same source and Newton point.
The extracted square and its boundary clearance are separate data.
-/
structure Geometry
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Rat.Fraction.Rational) where
  /-- The original raw-winding source inside the current box. -/
  source : State.Raw.RawWindingState p current.box
  /-- The retained positive extraction radius. -/
  radius : Rat.Fraction.Rational
  /-- The retained radius is strictly positive. -/
  radiusPositive : 0 < radius
  /-- The radius reads back the original squarefree extraction budget. -/
  radius_eq : radius = Squarefree.extractionRadius
    squarefree current.box current.clearance epsilon
  /-- The original source's retained Newton point and certificates. -/
  newton : NewtonCenterCertificate p current.box source.box squarefree
  /-- The original center displacement fits the retained radius. -/
  displacementSmall : Gaussian.Norm.Basic.normSq
    (anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  /-- The source retains its four original protected-boundary gaps. -/
  stripBounds : current.box.xLower + 4 *
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance < source.box.xLower ∧
    source.box.xUpper < current.box.xUpper - 4 *
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance ∧
    current.box.yLower + 4 *
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance < source.box.yLower ∧
    source.box.yUpper < current.box.yUpper - 4 *
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance
  /-- The original radius-scaled Taylor remainder is below the derivative margin. -/
  bandTaylorSmall : 2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box

constructive_injectivity Geometry

namespace Geometry

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {squarefree : SquarefreeCertificate p}
  {current : State.Raw.RawWindingState p ambient} {epsilon : Rat.Fraction.Rational}

/-- Read the retained geometric fields of a complete original local extraction. -/
@[expose] def ofOutput (output : Basic.Output squarefree current epsilon)
    (radius : output.radius = Squarefree.extractionRadius
      squarefree current.box current.clearance epsilon) : Geometry squarefree current epsilon where
  source := output.source
  radius := output.radius
  radiusPositive := output.radiusPositive
  radius_eq := radius
  newton := output.newton
  displacementSmall := output.displacementSmall
  stripBounds := output.stripBounds
  bandTaylorSmall := output.bandTaylorSmall

/-- Compute the original extraction geometry directly from its retained source.

Only the original radius and Newton point are numerical producers here. The
complete original extraction supplies erased certificates; its square and
boundary-clearance constructors are not consumed by this geometry builder.
-/
@[expose] def fromSource (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (positive : 0 < epsilon)
    (saved : Source.SourceOutput squarefree current epsilon) : Geometry squarefree current epsilon := by
  let original := Prepare.fromSource degreeAtLeastTwo squarefree current positive saved
  let point := anchorNewtonCenter p saved.source.box
  let newton : NewtonCenterCertificate p current.box saved.source.box squarefree :=
    { point := point
      point_eq := rfl
      residual := original.newton.residual
      derivativeNonzero := original.newton.derivativeNonzero
      derivativeLower := original.newton.derivativeLower
      displacement := original.newton.displacement
      displacementMargin := original.newton.displacementMargin }
  exact
    { source := saved.source
      radius := Squarefree.extractionRadius
        squarefree current.box current.clearance epsilon
      radiusPositive := original.radiusPositive
      radius_eq := rfl
      newton := newton
      displacementSmall := original.displacementSmall
      stripBounds := original.stripBounds
      bandTaylorSmall := original.bandTaylorSmall }

/-- Direct geometry has exactly the complete original extraction's retained fields. -/
theorem fromSource_eq (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (positive : 0 < epsilon)
    (saved : Source.SourceOutput squarefree current epsilon) :
    fromSource degreeAtLeastTwo squarefree current positive saved =
      ofOutput (Prepare.fromSource degreeAtLeastTwo squarefree current positive saved) rfl := rfl

/-- Direct geometry consumes the exact retained original source. -/
theorem fromSource_source (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (positive : 0 < epsilon)
    (saved : Source.SourceOutput squarefree current epsilon) :
    (fromSource degreeAtLeastTwo squarefree current positive saved).source = saved.source := rfl

/-- Direct geometry retains the original coefficient-computed radius. -/
theorem fromSource_radius (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (positive : 0 < epsilon)
    (saved : Source.SourceOutput squarefree current epsilon) :
    (fromSource degreeAtLeastTwo squarefree current positive saved).radius =
      Squarefree.extractionRadius
        squarefree current.box current.clearance epsilon := rfl

/-- Direct geometry retains the same original source-anchor Newton point. -/
theorem fromSource_point (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (positive : 0 < epsilon)
    (saved : Source.SourceOutput squarefree current epsilon) :
    (fromSource degreeAtLeastTwo squarefree current positive saved).newton.point =
      anchorNewtonCenter p saved.source.box := rfl

end Geometry

end Purelib.RootIsolation.Newton.Extraction
