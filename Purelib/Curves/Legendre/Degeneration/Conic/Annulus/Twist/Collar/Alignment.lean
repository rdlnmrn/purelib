module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Cofactor
import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Comparison
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.Gaussian.Norm.Basic

/-! # Original signed-unit alignment of a retained collar cofactor lift

Both actual root names retain native readings in the original signed node
box. At time zero their independent square comparisons reach the same
original cofactor. Its genuine box sum floor determines their operational
agreement and recovers the same original curve ordinate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (Enclosure)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}

/-- The actual unit-owner factory transports its original signed initial box to the retained coordinate channels. -/
theorem unitOwner_initial_box (channels : CoordinateChannels site parameter point source unit)
    (inside : (spatialBox site).Contains point) (factory : unit = UnitRoot.owner site point inside) :
    channels.unitOwner.track.initial.box = UnitRoot.box site :=
  (congrArg (fun owner : Owner ((unitPolynomial site).eval point) => owner.track.initial.box)
    (channels.unitOwner_eq.trans factory)).trans (UnitRoot.owner_initial_box site point inside)

/-- Every native reading of the SAME retained original unit certificate lies in its supplied signed initial box. -/
theorem unitRoot_native_inside (channels : CoordinateChannels site parameter point source unit)
    (originalBox : channels.unitOwner.track.initial.box = UnitRoot.box site) (index : Nat) :
    (UnitRoot.box site).Contains ((Name.Sampling.approximation channels.unitRoot.value.name).sample index) := by
  have possible := Process.Sampling.witnessAt_possible_start
    channels.unitRoot.value.name.process channels.unitRoot.value.name.state index
  have inside := CertifiedSquareRoot.Sampling.candidate_in_initial_box
    channels.unitOwner channels.unitRoot_eq possible
  exact Eq.mp (congrArg (fun region : Box => region.Contains
    ((Name.Sampling.approximation channels.unitRoot.value.name).sample index)) originalBox) inside

variable {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    {profile : Profile channels bound}

namespace Sweep.Reconstruction

section Root

variable {time : Fraction.Rational} {rotated : Sweep channels bound profile time}
    {actual : Reconstruction rotated} {base : Enclosure actual.2.1.val}
    {contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value}

namespace Lift

variable (lifted : Lift actual base contained)

/-- Read the SAME cofactor root channel retained in the supplied signed lift. -/
@[expose] def root : CoherentNamed := lifted.2.1.val.root

/-- The SAME retained root has its original cofactor square comparison through the cached enclosure. -/
def root_square : NamedEquivalent (lifted.root.mul lifted.root).name actual.2.2.2.1.val.name :=
  lifted.2.1.val.square.trans lifted.1.val.equivalent.symm

/-- Every native reading of the SAME lifted root lies in the original node's signed root box. -/
theorem root_native_inside (index : Nat) :
    (UnitRoot.box site).Contains ((Name.Sampling.approximation lifted.root.name).sample index) :=
  UnitRoot.Transport.PatchStream.native_inside (site := site) (base := base.source)
    (radicand := lifted.1.val.source) (inside := samples_inside actual base contained)
    (samples := cofactor_samples actual base lifted.1) lifted.2.1.val index

end Lift

end Root

section Zero

variable {rotated : Sweep channels bound profile 0} {actual : Reconstruction rotated}
    {base : Enclosure actual.2.1.val}
    {contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value}

namespace Lift

variable (lifted : Lift actual base contained)

/-- The actual new zero-time cofactor root agrees with the original signed unit-root certificate.

The supplied evidence identifies the original unit owner's signed box, not
its root with the new root. Independent native box containment gives the
positive sum floor; their two original square certificates then derive the
operational comparison with separate all-later sampling indices.
-/
def root_zero (originalBox : channels.unitOwner.track.initial.box = UnitRoot.box site) :
    NamedEquivalent lifted.root.name channels.unitRoot.value.name := by
  have newSquare := lifted.root_square.trans
    (cofactor_zero (channels := channels) (profile := profile) (rotated := rotated) actual)
  exact SquareRootProvenance.equivalent_of_sum_lower newSquare channels.unitRoot.square
    1 (by decide +kernel) (fun leftIndex rightIndex => by
      have lower := UnitRoot.box_sum_lower site (lifted.root_native_inside leftIndex)
        (channels.unitRoot_native_inside originalBox rightIndex)
      exact lower.trans_eq (Norm.Basic.normSq_eq_canonical _))

/-- The SAME zero-time lifted ordinate recovers the original curve channel with its derived signed root agreement.

The original ordinate factory, actual root comparison, commutation law and
retained reconstruction recovery are composed. No root, observation, phase
or coordinate producer is re-executed by this comparison constructor.
-/
def ordinate_zero (originalBox : channels.unitOwner.track.initial.box = UnitRoot.box site) :
    NamedEquivalent lifted.2.2.1.val.name source.name := by
  let roots := lifted.root_zero originalBox
  have product := Congruence.coherentMul_respects
    actual.2.2.1.val actual.2.2.1.val lifted.root channels.unitRoot.value (NamedEquivalent.refl _) roots
  have cached := NamedEquivalent.transport (congrArg CoherentNamed.name lifted.2.2.1.property.symm) rfl product
  exact cached.trans ((Laws.coherentMul_comm actual.2.2.1.val channels.unitRoot.value).trans
    (source_zero (channels := channels) (profile := profile) (rotated := rotated) actual))

end Lift

end Zero

end Sweep.Reconstruction

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels

end
