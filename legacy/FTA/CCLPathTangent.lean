import FTA.CCLFormulaPath
import FTA.CCLMultiOwnerGrid

/-!
# Exact tangent-table tests along projective event paths

The event classifier works with rational polynomials in a path parameter,
whereas the owner grid tests planar directional derivatives.  This module
connects the two finite computations: after multiplying by the strictly
positive projective denominator norm, a cleared slope polynomial has exactly
the sign of the corresponding planar slope.
-/

namespace FTA
namespace CCLPathTangent

open CCL CCL.GaussianRat
open FTA.CCLFormulaPath
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.ProjectivePath

abbrev QI := CCL.GaussianRat

/-- Positivity of a cleared slope is exactly positivity of the genuine
directional derivative at every affine path parameter. -/
theorem eval_clearedDirectionalSlope_pos_iff
    (form : HermitianForm) (path : Path) (direction : QI) (t : ℚ)
    (denominator :
      path.denominator.eval (FTA.PathPolynomial.ofRat t) ≠ 0) :
    0 < (clearedDirectionalSlope form path direction).eval t ↔
      0 < directionalSlope form (path.value t) direction := by
  rw [eval_clearedDirectionalSlope form path direction t denominator]
  have denominatorPositive :=
    FTA.CCLPathIntersection.eval_denominatorNorm_pos path t denominator
  constructor
  · intro productPositive
    rcases mul_pos_iff.mp productPositive with positive | negative
    · exact positive.2
    · exact (not_lt_of_ge denominatorPositive.le negative.1).elim
  · exact mul_pos denominatorPositive

/-- The finite list of cleared slope polynomials for one table direction. -/
def clearedDirectionalSlopes
    (forms : List HermitianForm) (path : Path) (direction : QI) :=
  forms.map fun form => clearedDirectionalSlope form path direction

/-- Executable polynomial-side version of the simultaneous tangent test. -/
def clearedSlopesPositive?
    (forms : List HermitianForm) (path : Path) (t : ℚ)
    (direction : QI) : Bool :=
  forms.all fun form =>
    decide (0 < (clearedDirectionalSlope form path direction).eval t)

theorem clearedSlopesPositive?_eq_true_iff
    (forms : List HermitianForm) (path : Path) (t : ℚ)
    (direction : QI) :
    clearedSlopesPositive? forms path t direction = true ↔
      ∀ form ∈ forms,
        0 < (clearedDirectionalSlope form path direction).eval t := by
  simp [clearedSlopesPositive?]

/-- Search the same fixed eight directions as the owner grid, but evaluate
the denominator-cleared univariate slope polynomials. -/
def clearedTangentDirection?
    (forms : List HermitianForm) (path : Path) (t : ℚ) : Option QI :=
  coordinateDirections.find? fun direction =>
    clearedSlopesPositive? forms path t direction

theorem clearedTangentDirection?_some_mem
    {forms : List HermitianForm} {path : Path} {t : ℚ} {direction : QI}
    (search : clearedTangentDirection? forms path t = some direction) :
    direction ∈ coordinateDirections := by
  exact List.mem_of_find?_eq_some search

theorem clearedTangentDirection?_some_slopes
    {forms : List HermitianForm} {path : Path} {t : ℚ} {direction : QI}
    (search : clearedTangentDirection? forms path t = some direction) :
    ∀ form ∈ forms,
      0 < (clearedDirectionalSlope form path direction).eval t := by
  apply (clearedSlopesPositive?_eq_true_iff forms path t direction).mp
  exact List.find?_some search

/-- A successful cleared-polynomial table search is a successful executable
planar tangent search at the corresponding rational path point. -/
theorem tangentDirectionCertificate?_isSome_of_cleared_search
    {forms : List HermitianForm} {path : Path} {t : ℚ} {direction : QI}
    (denominator :
      path.denominator.eval (FTA.PathPolynomial.ofRat t) ≠ 0)
    (search : clearedTangentDirection? forms path t = some direction) :
    (tangentDirectionCertificate? forms (path.value t)).isSome := by
  apply tangentDirectionCertificate?_isSome_of_mem
    (clearedTangentDirection?_some_mem search)
  intro form member
  apply (eval_clearedDirectionalSlope_pos_iff
    form path direction t denominator).1
  exact clearedTangentDirection?_some_slopes search form member

end CCLPathTangent
end FTA
