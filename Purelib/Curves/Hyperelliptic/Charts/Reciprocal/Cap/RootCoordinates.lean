module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Name.Apart.Exact
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalCollarTransport
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.ClearBoxPaths

public section

/-!
# Cap coordinates from the actual reciprocal collar root

Divide the retained reciprocal root by the root of the retained regular model.
The resulting channel squares to w^originOrder: it is the ramified coordinate
in odd degree and the sheet sign in even degree. Its prepared presentation
and attached winding owner both reconstruct the original reciprocal root.
The pointwise constructor retains the supplied root occurrence and model root channel;
the boundary constructor also retains the original collar crossing.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian CoherentNamed NamedEquivalent
  Prepared)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_comm
  coherentMul_squares_interchange)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)

/-- The quotient of the two retained root channels squares to the exact target fixed by their parameter identity.

The supplied certificates retain both channels and the denominator apartness.
Their product identity and exact target equality give the same quotient square. -/
@[expose] def quotient_square {first second : Gaussian} (numerator : CertifiedSquareRoot.Certificate first)
    (denominator : CertifiedSquareRoot.Certificate second) (target : Gaussian) (identity : second * target = first) :
    SquareRootProvenance.SquareIdentity (Coherent.CoherentNamed.div numerator.value denominator.value denominator.apart)
      target := by
  let quotient := Coherent.CoherentNamed.div numerator.value denominator.value denominator.apart
  let scalar := Coherent.CoherentNamed.Coherence.exact second
  have cancel : NamedEquivalent (Coherent.CoherentNamed.mul denominator.value quotient).name numerator.value.name :=
    (Coherent.Arithmetic.Product.Laws.coherentMul_comm denominator.value quotient).trans
      (Cancellation.coherentDiv_mul_cancel numerator.value denominator.value denominator.apart)
  have left : NamedEquivalent (Coherent.CoherentNamed.mul scalar (Coherent.CoherentNamed.mul quotient quotient)).name
    (Coherent.CoherentNamed.Coherence.exact first).name :=
    (Coherent.Arithmetic.Product.Congruence.coherentMul_respects scalar (Coherent.CoherentNamed.mul denominator.value
      denominator.value) (Coherent.CoherentNamed.mul quotient quotient) (Coherent.CoherentNamed.mul quotient quotient)
      denominator.square.symm (Equivalence.NamedEquivalent.refl _)).trans
      ((Coherent.Arithmetic.Product.Laws.coherentMul_squares_interchange denominator.value quotient).trans
        ((Coherent.Arithmetic.Product.Congruence.coherentMul_respects (Coherent.CoherentNamed.mul denominator.value
          quotient) numerator.value
          (Coherent.CoherentNamed.mul denominator.value quotient) numerator.value cancel cancel).trans
            numerator.square))
  have right : NamedEquivalent (Coherent.CoherentNamed.mul scalar (Coherent.CoherentNamed.Coherence.exact target)).name
    (Coherent.CoherentNamed.Coherence.exact first).name := by
    rw [← identity]
    exact Coherent.Exact.Arithmetic.exact_mul second target
  exact Cancellation.coherentMul_cancel_left scalar (Coherent.CoherentNamed.mul quotient quotient)
    (Coherent.CoherentNamed.Coherence.exact target)
    (exactApart second (SquareRootChannelOwnership.parameter_nonzero denominator))
    (left.trans right.symm)

set_option genInjectivity false in
/-- The ratio, its division-safe presentation and its reconstruction law are retained together.

The indexed numerator and denominator certificates fix both root occurrences.
The cached quotient and its prepared form retain that same pair of channels. -/
structure RootCoordinate {first second : Gaussian} (numerator : CertifiedSquareRoot.Certificate first)
    (denominator : CertifiedSquareRoot.Certificate second) (target : Gaussian) where
  /-- The cached original operational quotient of the supplied numerator and denominator root channels. -/ quotient :
    CoherentNamed
  /-- The cached quotient uses exactly the two original root channels and the original denominator apartness. -/
    quotient_eq : quotient = Coherent.CoherentNamed.div numerator.value denominator.value denominator.apart
  /-- The retained division-ready presentation of the same cached quotient. -/ prepared :
    Purelib.Approximation.Gaussian.Division.Prepared quotient
  /-- The retained prepared coordinate channel squares operationally to its original target. -/ square :
    SquareRootProvenance.SquareIdentity prepared.denominator target
  /-- Multiplying the retained coordinate channel by the original regular root reconstructs the original reciprocal
    root. -/ reconstruct : NamedEquivalent (Coherent.CoherentNamed.mul prepared.denominator denominator.value).name
    numerator.value.name

constructive_injectivity RootCoordinate

namespace RootCoordinate

/-- Cache the quotient of the supplied original root channels and construct its prepared coordinate certificate and
reconstruction law. -/
@[expose] def build {first second : Gaussian} (numerator : CertifiedSquareRoot.Certificate first) (denominator :
  CertifiedSquareRoot.Certificate second)
    (target : Gaussian) (nonzero : target ≠ 0) (identity : second * target = first) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate numerator denominator target := by
  let quotient := Coherent.CoherentNamed.div numerator.value denominator.value denominator.apart
  let square := Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.quotient_square numerator denominator target
    identity
  let prepared := SquareRootProvenance.prepared_of_square square nonzero
  exact ⟨quotient, rfl, prepared,
    (Coherent.Arithmetic.Product.Congruence.coherentMul_respects prepared.denominator quotient prepared.denominator
      quotient
      prepared.equivalent.symm prepared.equivalent.symm).trans square,
    (Coherent.Arithmetic.Product.Congruence.coherentMul_respects prepared.denominator quotient denominator.value
      denominator.value
      prepared.equivalent.symm (Equivalence.NamedEquivalent.refl _)).trans
      (Cancellation.coherentDiv_mul_cancel numerator.value denominator.value denominator.apart)⟩

/-- Read the square-root certificate from the retained prepared coordinate channel. -/
@[expose] def certificate {first second target : Gaussian} {numerator : CertifiedSquareRoot.Certificate first}
  {denominator : CertifiedSquareRoot.Certificate second}
    (coordinate : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate numerator denominator
      target) : CertifiedSquareRoot.Certificate target :=
  ⟨coordinate.prepared.denominator, coordinate.prepared.apart, coordinate.square⟩

end RootCoordinate

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {source : Gaussian}

set_option genInjectivity false in
/-- The retained coordinate comparison between an original reciprocal owner and the same cap model's regular root.

Both original certificates, their exact readbacks, prepared quotient coordinate and attached winding owner remain
linked. -/
structure Overlap (cap : ReciprocalInnerInverse.Data curve collar)
    (point : Gaussian)
    (reciprocalOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) where
  /-- The retained original cap-model root channel at the overlap point. -/ regular : Owners.Point cap point
  /-- The cached certificate of the supplied original reciprocal winding owner. -/ reciprocal :
    CertifiedSquareRoot.Certificate ((HyperellipticReciprocal.polynomial curve).eval point)
  /-- The cached reciprocal certificate is exactly the supplied original owner's certificate. -/ reciprocal_eq :
    reciprocal = reciprocalOwner.certificate reciprocalOwner.parameterNonzero
  /-- The cached original regular cap-model root certificate. -/ regularRoot : CertifiedSquareRoot.Certificate
    (cap.polynomial.eval point)
  /-- The cached regular certificate is exactly the retained original model channel's certificate. -/ regularRoot_eq :
    regularRoot = regular.certificate
  /-- The prepared quotient of these exact original root certificates, squaring to the reciprocal origin factor. -/
    coordinate : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate reciprocal regularRoot (point
    ^ HyperellipticReciprocal.originOrder curve)
  /-- The winding owner attached to this exact retained prepared coordinate channel. -/ attached :
    SquareRootChannelOwnership.Attachment coordinate.prepared.denominator
    (point ^ HyperellipticReciprocal.originOrder curve)

constructive_injectivity Overlap

namespace Overlap

/-- Construct the regular model channel and quotient coordinate from the supplied original reciprocal owner at a covered
point. -/
@[expose] def build (cap : ReciprocalInnerInverse.Data curve collar) (point : Gaussian) (inside : collar.box.Contains
  point)
    (reciprocalOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap point reciprocalOwner :=
  let regular := Owners.Point.build cap point inside
  let reciprocal := reciprocalOwner.certificate reciprocalOwner.parameterNonzero
  let regularRoot := regular.certificate
  have identity : cap.polynomial.eval point * point ^ HyperellipticReciprocal.originOrder curve =
      (HyperellipticReciprocal.polynomial curve).eval point := by
    rw [cap.polynomial_eq, HyperellipticReciprocal.polynomial_eval]
  have nonzero : point ^ HyperellipticReciprocal.originOrder curve ≠ 0 := by
    intro zero
    apply reciprocalOwner.parameterNonzero
    exact identity.symm.trans (by rw [zero, Data.Gaussian.Basic.mul_zero])
  let coordinate := Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate.build reciprocal
    regularRoot _ nonzero identity
  ⟨regular, reciprocal, rfl, regularRoot, rfl, coordinate, SquareRootChannelOwnership.attach coordinate.certificate⟩

/-- Multiplying the retained coordinate channel by the original regular root reconstructs the original reciprocal root.
-/
@[expose] def reconstruct {cap : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    {owner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap point owner) :
    let root := overlap.attached.owner.certificate overlap.attached.owner.parameterNonzero
    NamedEquivalent (Coherent.CoherentNamed.mul root.value overlap.regularRoot.value).name overlap.reciprocal.value.name
      := by
  let root := overlap.attached.owner.certificate overlap.attached.owner.parameterNonzero
  exact (Coherent.Arithmetic.Product.Congruence.coherentMul_respects root.value overlap.coordinate.prepared.denominator
    overlap.regularRoot.value overlap.regularRoot.value overlap.attached.equivalent.symm
      (Equivalence.NamedEquivalent.refl _)).trans overlap.coordinate.reconstruct

end Overlap

set_option genInjectivity false in
/-- An affine owner supplies the entire overlap: scaling, its attached reciprocal owner, the actual collar crossing and
the cap coordinate.

The indexed fields retain the supplied owners, channels and exact cached
data. Their identities bind each displayed field to those same inputs. -/
structure BoundaryOverlap (cap : ReciprocalInnerInverse.Data curve collar)
    (fiber : ReciprocalCollarTransport.Fiber collar source)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) where
  /-- The winding owner attached to the reciprocal scaling of the exact original affine boundary root. -/ attached :
    SquareRootChannelOwnership.Attachment
    (ReciprocalRootNames.ofBoundaryOwner curve source fiber.boundary original).prepared.denominator
    ((HyperellipticReciprocal.polynomial curve).eval source⁻¹)
  /-- The retained trace of the actual collar route from the attached reciprocal owner. -/ collarTrace :
    PreparedPathTrace.TracedPath fiber.route.path attached.owner
  /-- The coordinate comparison at the actual retained collar-trace finishing owner. -/ coordinates :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap (collar.sidePoint source)
    collarTrace.finishOwner

constructive_injectivity BoundaryOverlap

/-- Retain the original affine-to-reciprocal crossing and construct cap coordinates from its actual finishing owner. -/
@[expose] def BoundaryOverlap.build (cap : ReciprocalInnerInverse.Data curve collar)
    (fiber : ReciprocalCollarTransport.Fiber collar source)
    (original : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.BoundaryOverlap cap fiber original :=
  let crossed := ReciprocalRootOwners.cross fiber original
  ⟨crossed.1, crossed.2, Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.build cap (collar.sidePoint
    source) (by
    rw [collar.box_eq, collar.sidePoint_eq]
    exact ReciprocalExteriorCollar.chord_contains curve fiber.boundary.1) crossed.2.finishOwner⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
