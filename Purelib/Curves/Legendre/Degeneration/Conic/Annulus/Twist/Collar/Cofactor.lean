module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Collar.Coordinates
public import Purelib.Curves.Legendre.Degeneration.UnitRoot.Stream
public import Purelib.Approximation.Gaussian.Geometric.Enclosure
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Signed cofactor re-lifting of a retained named collar reconstruction

A genuine original-base enclosure contained in the collision patch supplies
all finite cofactor movement payments. One original signed reference budget
then constructs the actual named cofactor root, and the SAME normalized
ordinate has the derived factorized cubic square. No exact Gaussian point is
manufactured from the named base.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation Enclosure)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Legendre.Degeneration.UnitRoot
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Polynomial.Dense.Gaussian.Linear

variable {site : Fin 2} {parameter point : Canonical} {source : CoherentNamed}
    {unit : Owner ((unitPolynomial site).eval point)}
    {channels : CoordinateChannels site parameter point source unit}
    {bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)}
    {profile : Profile channels bound} {time : Fraction.Rational}
    {rotated : Sweep channels bound profile time} (actual : Reconstruction rotated)

/-- Enclose the SAME retained named cofactor by one original-base addition and its whole arithmetic factory. -/
def cofactorEnclosure (base : Enclosure actual.2.1.val) : Enclosure actual.2.2.2.1.val :=
  (base.add (Enclosure.exact (-(remainingValue site)))).cast actual.2.2.2.1.property.symm

/-- The cofactor enclosure reads the original affine polynomial at the SAME base-program sample. -/
theorem cofactorEnclosure_sample (base : Enclosure actual.2.1.val) (index : Nat) :
    (cofactorEnclosure actual base).source.sample index = (unitPolynomial site).eval (base.source.sample index) := by
  have castRead := Enclosure.cast_sample (base.add (Enclosure.exact (-(remainingValue site))))
    actual.2.2.2.1.property.symm index
  have sumRead := Enclosure.add_sample base (Enclosure.exact (-(remainingValue site))) index
  have constantRead := Enclosure.exact_sample (-(remainingValue site)) index
  have read := castRead.trans (sumRead.trans
    (congrArg (fun value : Canonical => base.source.sample index + value) constantRead))
  have scalar (value offset : Canonical) : value + -offset = value - offset := by ring1
  have evaluated : (unitPolynomial site).eval (base.source.sample index) =
      base.source.sample index - remainingValue site :=
    Translated.translatedCoordinate_eval (remainingValue site) (base.source.sample index)
  exact read.trans ((scalar _ _).trans evaluated.symm)

/-- The GIVEN enclosure's common-ball inclusion supplies each actual base sample's original patch membership. -/
theorem samples_inside (base : Enclosure actual.2.1.val)
    (contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value)
    (index : Nat) : (spatialBox site).Contains (base.source.sample index) :=
  contained _ (base.contains index)

/-- A GIVEN once-bound cofactor enclosure retains its original affine sample formula without reconstruction. -/
theorem cofactor_samples (base : Enclosure actual.2.1.val)
    (cofactor : { value : Enclosure actual.2.2.2.1.val // value = cofactorEnclosure actual base }) (index : Nat) :
    cofactor.val.source.sample index = (unitPolynomial site).eval (base.source.sample index) :=
  (congrArg (fun value : Enclosure actual.2.2.2.1.val => value.source.sample index) cofactor.property).trans
    (cofactorEnclosure_sample actual base index)

/-- The retained cofactor enclosure and signed root stream determine one new ordinate and its actual cubic factors. -/
@[expose] def Lift (base : Enclosure actual.2.1.val)
    (contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value) : Type _ :=
  (cofactor : { value : Enclosure actual.2.2.2.1.val // value = cofactorEnclosure actual base }) ×
  (roots : { value : Transport.PatchStream site base.source cofactor.val.source
      (samples_inside actual base contained) (cofactor_samples actual base cofactor) //
    value = Transport.fromSamples site base.source cofactor.val.source
      (samples_inside actual base contained) (cofactor_samples actual base cofactor) }) ×
  (ordinate : { value : CoherentNamed // value = actual.2.2.1.val.mul roots.val.root }) ×
    NamedEquivalent (ordinate.val.mul ordinate.val).name
      ((((actual.1.val.mul actual.1.val).add (Coherence.exact (smoothing site parameter)).neg).mul
        actual.2.2.2.1.val).name)

/-- Re-lift the GIVEN reconstruction using one actual cofactor enclosure and the original signed-box root stream.

The supplied common-ball containment is an intrinsic geometric admission.
Every root movement and square comparison is derived internally. The
returned stream retains its original source budget and executable query rule.
The existing source and phase caches are reused; new root queries perform
fresh finite work when requested.
-/
def lift (base : Enclosure actual.2.1.val)
    (contained : ∀ value : Canonical, base.ball.Contains value → (spatialBox site).Contains value) :
    Lift actual base contained := by
  let cofactor := cofactorEnclosure actual base
  let cofactorCache : { value : Enclosure actual.2.2.2.1.val // value = cofactorEnclosure actual base } :=
    ⟨cofactor, rfl⟩
  let roots := Transport.fromSamples site base.source cofactor.source
    (samples_inside actual base contained) (cofactor_samples actual base cofactorCache)
  let ordinate := actual.2.2.1.val.mul roots.root
  have rootSquare : NamedEquivalent (roots.root.mul roots.root).name actual.2.2.2.1.val.name :=
    roots.square.trans cofactor.equivalent.symm
  have rearrange := Laws.coherentMul_interchange actual.2.2.1.val roots.root actual.2.2.1.val roots.root
  have factors := Congruence.coherentMul_respects
    (actual.2.2.1.val.mul actual.2.2.1.val)
    ((actual.1.val.mul actual.1.val).add (Coherence.exact (smoothing site parameter)).neg)
    (roots.root.mul roots.root) actual.2.2.2.1.val actual.2.2.2.2 rootSquare
  exact ⟨cofactorCache, ⟨roots, rfl⟩, ⟨ordinate, rfl⟩, rearrange.trans factors⟩

end Purelib.Curves.Legendre.Degeneration.CoordinateChannels.Sweep.Reconstruction

end
