module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Riemann.Paths.PreparedPathTrace
public import Purelib.Riemann.Branches.PreparedPrimitiveSheets
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.RootIsolation.Track.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.State.WindingOne.Basic

@[expose] public section

/-!
# Cached primitive neighborhoods of actual path endpoints

The endpoint owner supplies the neighborhood's seed. Alternative generated
patches retain their exact center equation and executable same-occurrence
witness; they need not reproduce canonical root preparation. No independent
root isolation is used by the constructor.
-/

namespace Purelib.Riemann.Paths.TracedPrimitiveNeighborhood

/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The dense Gaussian polynomial carrier. -/
private abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Normalization.AlignedInverseRootSeed (AlignedSeed)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {source : Owner
    (polynomial.eval start)}

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A continued neighborhood centered at the original finish point with an exact source-name equivalence.

The patch keeps its original polynomial and count; the supplied patch-name operation identifies the retained seed name
compared with the original source. -/
structure NeighborhoodData (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (finish : Basic.Canonical) (count : Nat)
    (sourceName : Name.Basic.Named)
    (patchName : ContinuedNeighborhood polynomial count → Name.Basic.Named) where
  /-- The retained original continued neighborhood and its exact polynomial/count indices. -/ patch :
    ContinuedNeighborhood polynomial count
  /-- The stored patch center equals the original finish point. -/ center_eq : patch.base.site.center = finish
  /-- The original source name is equivalent to the name of the retained patch seed. -/ seedEquivalent :
    Equivalence.NamedEquivalent sourceName (patchName patch)

constructive_injectivity NeighborhoodData

/-- A continued neighborhood at the traced path's finish point, aligned with its exact retained terminal root owner. -/
abbrev Neighborhood (traced : TracedPath path source) (count : Nat) :=
  NeighborhoodData polynomial finish count (ownerName traced.finishOwner)
    (fun patch => ownerName patch.base.seed.owner)

namespace Neighborhood

variable {traced : TracedPath path source} {count : Nat}

open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
/-- The original aligned-neighborhood construction retains exactly the supplied aligned seed. -/
public theorem ofAligned_seed {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}
    (site : PreparedObservationNeighborhoods.ObservationNeighborhood polynomial count)
    {owner : Owner (polynomial.eval site.center)} (aligned : AlignedSeed owner) :
    (ContinuedNeighborhood.ofAligned site aligned).base.seed = aligned.seed := rfl

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- The original owner name is equivalent to the name of its retained aligned seed owner.

The comparison uses the exact initial-box refinement of the two original root tracks. -/
public def alignedEquivalent {parameter : Basic.Canonical} (owner : Owner parameter) (aligned : AlignedSeed owner) :
    Equivalence.NamedEquivalent (ownerName owner) (ownerName aligned.seed.owner) :=
  PreparedPrimitiveSheets.rootEquivalent_of_initial_refines owner.parameterNonzero
    owner.track aligned.seed.owner.track aligned.refines

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Readings in
/-- Construct a continued primitive neighborhood from the original traced terminal owner.

The finish point and nonzero parameter define the observation site. The aligned seed gives the retained patch and its
exact root-name equivalence. -/
def build (traced : TracedPath path source) (count : Nat) : Neighborhood traced count := by
  let site := PreparedObservationNeighborhoods.ObservationNeighborhood.ofPoint polynomial count finish
    traced.finishOwner.parameterNonzero
  let aligned := AlignedSeed.ofOwner traced.finishOwner
  let patch := ContinuedNeighborhood.ofAligned site aligned
  refine ⟨patch, rfl, ?_⟩
  change Equivalence.NamedEquivalent (ownerName traced.finishOwner) (ownerName (ContinuedNeighborhood.ofAligned site
    aligned).base.seed.owner)
  rw [ofAligned_seed]
  exact alignedEquivalent traced.finishOwner aligned

/-- The original traced finish point lies in its retained continued neighborhood box. -/
theorem center_inside (neighborhood : Neighborhood traced count) : neighborhood.patch.box.Contains finish := by
  have inside := neighborhood.patch.center_inside
  rw [neighborhood.center_eq] at inside
  exact inside

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- At the exact neighborhood center, the original seed owner name is equivalent to the retained point reading name.

The center equality preserves the original parameter, and the point certificate supplies the exact root-track
refinement. -/
public def seedPointEquivalent {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) {point : Basic.Canonical}
    (equal : patch.base.site.center = point) (sample : ContinuedNeighborhood.Point patch point) :
    Equivalence.NamedEquivalent (ownerName patch.base.seed.owner) sample.certificate.value.name := by
  cases equal
  exact PreparedPrimitiveSheets.rootEquivalent_of_initial_refines sample.owner.parameterNonzero
    patch.base.seed.owner.track sample.owner.track sample.refines

open Purelib.Approximation.Gaussian in
/-- Compare the original traced terminal owner with a retained reading at the neighborhood's exact finish point.

The comparison composes the retained terminal-to-seed equivalence with the original seed-to-point refinement comparison.
-/
def pointEquivalent (neighborhood : Neighborhood traced count)
    (sample : ContinuedNeighborhood.Point neighborhood.patch finish) :
    Equivalence.NamedEquivalent (ownerName traced.finishOwner) sample.certificate.value.name :=
  neighborhood.seedEquivalent.trans (seedPointEquivalent neighborhood.patch neighborhood.center_eq sample)

end Neighborhood

end Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
