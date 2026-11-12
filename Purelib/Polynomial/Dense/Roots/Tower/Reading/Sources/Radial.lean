module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources
public import Purelib.Data.Gaussian.Norm.Radial
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Pre-observation radial source scheduling

The same original tower parameters and Gaussian leading coefficient determine
one root norm total, inverse and inverse norm. The original radial request
uses those exact retained bounds, and its cap supplies the same original
source schedule without repeating the inverse, norm or schedule computation.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Ring (Weight)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

universe u

set_option genInjectivity false in
/-- The original radial request and source schedule sharing their same retained coefficient and root-bound caches.

The original budget, leading invariant, pair-separation floor and collar
width remain indices. No candidate or model is supplied. Each exact
component equation refers to the original procedure on these same caches.
-/
structure Radial {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K} {coefficient : Canonical}
    (leading : Leading tower embed coefficient) (separation width : Rational) where
  /-- The same original pair-separation floor is positive. -/
  separationPositive : 0 < separation
  /-- The same original collar width is positive. -/
  widthPositive : 0 < width
  /-- The once-computed inverse of the original Gaussian leading coefficient. -/
  coefficientInverse : Canonical
  /-- The inverse is the original Gaussian inverse on that same coefficient. -/
  coefficientInverse_eq : coefficientInverse = coefficient⁻¹
  /-- The once-computed norm of that same original inverse. -/
  inverseNorm : Rational
  /-- The inverse norm uses the same retained coefficient inverse. -/
  inverseNorm_eq : inverseNorm = Norm.Basic.normSq coefficientInverse
  /-- The original inverse norm is nonnegative. -/
  inverseNormNonnegative : 0 ≤ inverseNorm
  /-- The once-computed bound for all original root readings. -/
  rootBound : Rational
  /-- The bound is the same original parameter chain's structural total. -/
  rootBound_eq : rootBound = parameters.rootBoundTotal
  /-- The same root bound is nonnegative. -/
  rootBoundNonnegative : 0 ≤ rootBound
  /-- The actual original radial request using the same common radius, total, inverse norm and collar. -/
  radial : Norm.Radial.Request radius rootBound inverseNorm width
  /-- The radial request consumes exactly those same retained original values. -/
  radial_eq : radial = Norm.Radial.Request.prepare radius rootBound inverseNorm width
    parameters.radius_nonnegative rootBoundNonnegative inverseNormNonnegative widthPositive
  /-- The same original source schedule, indexed by this exact retained radial cap. -/
  sources : Sources budget leading separation radial.cap
  /-- Source scheduling consumes the same retained inverse and norm without recomputing either. -/
  sources_eq : sources = Sources.ofInverseNorm budget leading separation radial.cap
    separationPositive radial.cap_positive coefficientInverse coefficientInverse_eq inverseNorm inverseNorm_eq

constructive_injectivity Radial

namespace Radial

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius}
variable {embed : Canonical → K} {coefficient : Canonical}

/-- The exact original radial-request type with its four original scalar indices. -/
abbrev Request (radius rootBound inverseNorm width : Rational) :=
  Norm.Radial.Request radius rootBound inverseNorm width

/-- The original source schedule indexed by the same retained radial request's actual cap. -/
abbrev Source (budget : Budget parameters target tolerance) (leading : Leading tower embed coefficient)
    (separation : Rational) {rootBound inverseNorm width : Rational}
    (radial : Request radius rootBound inverseNorm width) := Sources budget leading separation radial.cap

/-- Assemble retained original request components with their exact original procedure equations.

The supplied inverse, norm and structural total are retained directly. The
original radial and source records consume those same cached values; this
constructor invokes no inverse, norm, parameter fold or request producer.
-/
@[expose] def ofRequests (budget : Budget parameters target tolerance) (leading : Leading tower embed coefficient)
    (separation width : Rational) (separationPositive : 0 < separation) (widthPositive : 0 < width)
    (coefficientInverse : Canonical) (coefficientInverseEq : coefficientInverse = coefficient⁻¹)
    (inverseNorm : Rational) (inverseNormEq : inverseNorm = Norm.Basic.normSq coefficientInverse)
    (rootBound : Rational) (rootBoundEq : rootBound = parameters.rootBoundTotal)
    (radial : Request radius rootBound inverseNorm width)
    (radialEq : radial = Norm.Radial.Request.prepare radius rootBound inverseNorm width
      parameters.radius_nonnegative (rootBoundEq.symm ▸ parameters.rootBoundTotal_nonnegative)
      (inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg coefficientInverse) widthPositive)
    (sources : Source budget leading separation radial)
    (sourcesEq : sources = Sources.ofInverseNorm budget leading separation radial.cap
      separationPositive radial.cap_positive coefficientInverse coefficientInverseEq inverseNorm inverseNormEq) :
    Radial budget leading separation width :=
  { separationPositive, widthPositive, coefficientInverse, coefficientInverse_eq := coefficientInverseEq
    inverseNorm, inverseNorm_eq := inverseNormEq
    inverseNormNonnegative := inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg coefficientInverse
    rootBound, rootBound_eq := rootBoundEq
    rootBoundNonnegative := rootBoundEq.symm ▸ parameters.rootBoundTotal_nonnegative
    radial, radial_eq := radialEq, sources, sources_eq := sourcesEq }

/-- Compute one original radial cap and source schedule before observing any root or model.

The inverse, its norm and the same original parameter total are computed
once. One radial request supplies its cap to the source constructor, which
consumes the retained inverse and norm and prepares its schedule once.
-/
@[expose] def prepare (budget : Budget parameters target tolerance) (leading : Leading tower embed coefficient)
    (separation width : Rational) (separationPositive : 0 < separation) (widthPositive : 0 < width) :
    Radial budget leading separation width :=
  let coefficientInverse := coefficient⁻¹
  let inverseNorm := Norm.Basic.normSq coefficientInverse
  let rootBound := parameters.rootBoundTotal
  let radial := Norm.Radial.Request.prepare radius rootBound inverseNorm width parameters.radius_nonnegative
    parameters.rootBoundTotal_nonnegative (Norm.Basic.normSq_nonneg coefficientInverse) widthPositive
  let sources := Sources.ofInverseNorm budget leading separation radial.cap separationPositive radial.cap_positive
    coefficientInverse rfl inverseNorm rfl
  ofRequests budget leading separation width separationPositive widthPositive coefficientInverse rfl
    inverseNorm rfl rootBound rfl radial rfl sources rfl

/-- Retaining the same exact original components preserves the complete radial source preparation result. -/
theorem ofRequests_eq_prepare (budget : Budget parameters target tolerance) (leading : Leading tower embed coefficient)
    (separation width : Rational) (separationPositive : 0 < separation) (widthPositive : 0 < width)
    (coefficientInverse : Canonical) (coefficientInverseEq : coefficientInverse = coefficient⁻¹)
    (inverseNorm : Rational) (inverseNormEq : inverseNorm = Norm.Basic.normSq coefficientInverse)
    (rootBound : Rational) (rootBoundEq : rootBound = parameters.rootBoundTotal)
    (radial : Request radius rootBound inverseNorm width)
    (radialEq : radial = Norm.Radial.Request.prepare radius rootBound inverseNorm width
      parameters.radius_nonnegative (rootBoundEq.symm ▸ parameters.rootBoundTotal_nonnegative)
      (inverseNormEq.symm ▸ Norm.Basic.normSq_nonneg coefficientInverse) widthPositive)
    (sources : Source budget leading separation radial)
    (sourcesEq : sources = Sources.ofInverseNorm budget leading separation radial.cap
      separationPositive radial.cap_positive coefficientInverse coefficientInverseEq inverseNorm inverseNormEq) :
    ofRequests budget leading separation width separationPositive widthPositive coefficientInverse coefficientInverseEq
        inverseNorm inverseNormEq rootBound rootBoundEq radial radialEq sources sourcesEq =
      prepare budget leading separation width separationPositive widthPositive := by
  cases coefficientInverseEq
  cases inverseNormEq
  cases rootBoundEq
  cases radialEq
  cases sourcesEq
  rfl

variable {budget : Budget parameters target tolerance} {leading : Leading tower embed coefficient}
variable {separation width : Rational}

/-- The source schedule supplies its retained positive initial original-polynomial sample tolerance. -/
theorem initial_positive (request : Radial budget leading separation width) :
    0 < request.sources.schedule.val.initial := request.sources.initial_positive

/-- Source scheduling retains this same cached original Gaussian inverse. -/
theorem sources_inverse_eq (request : Radial budget leading separation width) :
    request.sources.coefficientInverse = request.coefficientInverse :=
  congrArg Sources.coefficientInverse request.sources_eq

/-- Source scheduling retains this same cached original inverse norm. -/
theorem sources_norm_eq (request : Radial budget leading separation width) :
    request.sources.inverseNorm = request.inverseNorm := congrArg Sources.inverseNorm request.sources_eq

/-- The original source cap is this same retained radial request's cap. -/
abbrev cap (request : Radial budget leading separation width) := request.radial.cap

/-- Reading the original source cap returns this same stored radial cap exactly. -/
theorem cap_eq (request : Radial budget leading separation width) : request.cap = request.radial.cap := rfl

/-- View the same retained radial request at the original total and source norm indices without reconstructing it. -/
@[expose] def originalRadial (request : Radial budget leading separation width) :
    Norm.Radial.Request radius parameters.rootBoundTotal request.sources.inverseNorm width :=
  request.sources_norm_eq.symm ▸ (request.rootBound_eq ▸ request.radial)

/-- Scalar cap projection commutes with the two exact original index transports. -/
private theorem transported_cap {radius oldRoot newRoot oldNorm newNorm width : Rational}
    (request : Norm.Radial.Request radius oldRoot oldNorm width) (rootEq : oldRoot = newRoot)
    (normEq : oldNorm = newNorm) :
    (normEq ▸ (rootEq ▸ request) : Norm.Radial.Request radius newRoot newNorm width).cap = request.cap := by
  cases rootEq
  cases normEq
  rfl

/-- The exact original-index view preserves the same retained radial cap. -/
theorem originalRadial_cap (request : Radial budget leading separation width) :
    request.originalRadial.cap = request.radial.cap :=
  transported_cap request.radial request.rootBound_eq request.sources_norm_eq.symm

end Radial
end Purelib.Polynomial.Dense.Roots.Tower.Reading.Sources

end
