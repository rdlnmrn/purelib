import CCL.Boundary.Description
import CCL.Boundary.Curve.Events

/-!
# Total analysis of a described CCL boundary

Parameterized boundaries are sent directly to the cleared-gcd/Sturm event
classifier.  Finite zero sets are evaluated pointwise, and a universal form
is retained explicitly.  This is the finite dispatch layer between formula
provenance and equality ownership.
-/

namespace CCL.CCLBoundaryAnalysis

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev Description := CCL.CCLBoundaryDescription.Description
abbrev CurveSource := CCL.CCLBoundaryDescription.CurveSource

/-- Exact evaluation decision at one member of a finite atom zero set. -/
inductive PointDecision (p : GaussianPolynomial) (point : Gaussian) where
  | root (equal : p.eval point = 0)
  | clear (nonzero : p.eval point ≠ 0)

def decidePoint (p : GaussianPolynomial) (point : Gaussian) :
    PointDecision p point := by
  if equal : p.eval point = 0 then
    exact .root equal
  else
    exact .clear equal

/-- One point bundled with its exact polynomial-evaluation decision. -/
structure EvaluatedPoint (p : GaussianPolynomial) where
  point : Gaussian
  decision : PointDecision p point

def evaluatePoints (p : GaussianPolynomial) (points : List Gaussian) :
    List (EvaluatedPoint p) :=
  points.map fun point => ⟨point, decidePoint p point⟩

/-- Total finite analysis corresponding to each kind of boundary
description. -/
inductive Outcome (p : GaussianPolynomial)
    {reference : Mat2} {form : HermitianForm} :
    Description reference form → Type where
  | curve
      (source : CurveSource reference form)
      (analysis : CCL.CurveEvents.Analysis p
        source.primary.curve)
      (companionAnalysis : ∀ companion,
        companion ∈ source.companions →
          CCL.CurveEvents.Analysis p companion.curve) :
      Outcome p (.curve source)
  | finite (points : List Gaussian)
      (complete : ∀ value, form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ form.eval value)
      (evaluations : List (EvaluatedPoint p))
      (evaluations_eq : evaluations = evaluatePoints p points) :
      Outcome p (.finite points complete nonnegative)
  | universal (zero : ∀ value, form.eval value = 0) :
      Outcome p (.universal zero)

/-- A boundary description paired with its executed analysis. -/
structure AnalyzedBoundary
    (p : GaussianPolynomial) (reference : Mat2)
    (form : HermitianForm) where
  description : Description reference form
  outcome : Outcome p description

/-- Execute the complete finite analysis. -/
def analyze
    (p : GaussianPolynomial) {reference : Mat2} {form : HermitianForm}
    (description : Description reference form) :
    AnalyzedBoundary p reference form := by
  cases description with
  | curve source =>
      exact ⟨.curve source,
        .curve source
          (CCL.CurveEvents.analyze p source.primary.curve)
          (fun companion _member =>
            CCL.CurveEvents.analyze p companion.curve)⟩
  | finite points complete nonnegative =>
      exact ⟨.finite points complete nonnegative,
        .finite points complete nonnegative (evaluatePoints p points) rfl⟩
  | universal zero =>
      exact ⟨.universal zero, .universal zero⟩

end CCL.CCLBoundaryAnalysis
