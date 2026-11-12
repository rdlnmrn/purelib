module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity.Index
public import Purelib.Riemann.RootContinuation.CoherentRoot.PointComparison
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.RootIsolation.FTA.Positive.Input

/-!
# Exact decisions at original multiplicity root cache entries

Exact linear readings use their retained scalar comparison. Nonlinear entries
use the existing point comparison on the same stored root certificate and
squarefree factor. The decision stays indexed by the original cached channel.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)

namespace Realization

/-- Decide exact zero or compute denominator preparation for the same retained original factor-root channel. -/
def decide {entry : PositiveEntry} {factor : Residual.Multiplicity.Factor entry}
    (roots : Realization factor) (index : Fin (count factor)) : Division.Prepared.Decision (roots.channel index) := by
  cases factor with
  | linear degree data inverseNorm inverseNorm_eq =>
    cases roots with
    | linear value value_eq geometric geometric_eq =>
      have equivalent : Equivalence.NamedEquivalent value.name (CoherentNamed.Coherence.exact data.point).name := by
        rewrite [value_eq]
        exact Equivalence.NamedEquivalent.refl _
      let scalar : RationalSidecar value := ⟨data.point, equivalent⟩
      exact scalar.decide
  | higher degree preparation =>
    cases roots with
    | higher roots =>
      exact PointComparison.decide (roots.get index) ⟨entry.part.squarefree, entry.degreePositive⟩ 0

end Realization

namespace Family

/-- Decide zero or preparation at an unchanged original structural root occurrence and cached numerical channel. -/
def decide {entries : List PositiveEntry} {preparation : Residual.Multiplicity.Family entries}
    (roots : Family preparation) (index : Index preparation) : Division.Prepared.Decision (roots.channel index) := by
  rewrite [roots.channel_projections index]
  exact (roots.get index.factorIndex).decide index.rootIndex

end Family

end Purelib.Riemann.RootContinuation.CoherentRoot.Multiplicity

end
