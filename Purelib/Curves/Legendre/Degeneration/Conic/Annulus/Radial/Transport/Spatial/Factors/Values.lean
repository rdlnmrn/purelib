module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Factors
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Arithmetic
import Purelib.Curves.Legendre.Degeneration.Conic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Tactic.Ring

/-! # Full cubic values on actual retained factor certificates

The supplied original unit and normalized Owners keep their separate full
certificate caches. One actual coherent product is constructed and retained;
its full cubic square follows from the original product-square comparison and
Legendre factorization. Original CoordinateChannels consume that same value
and unit certificate without inventing an off-curve rational conic point.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

/-- The actual supplied factor product has the original full cubic square at its unchanged physical coordinate. -/
def cubicSquare (site : Fin 2) (parameter point : Canonical)
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point))
    (normalRoot : CertifiedSquareRoot.Certificate (Clearance.normalizedRadicand site parameter point))
    (value : CoherentNamed) (retained : value = unitRoot.value.mul normalRoot.value) :
    NamedEquivalent (value.mul value).name (Named.exact ((Paths.polynomial parameter).eval point)) := by
  have factors := CertifiedSquareRoot.Certificate.productSquare unitRoot normalRoot value retained
  have scalar : (unitPolynomial site).eval point * Clearance.normalizedRadicand site parameter point =
      (Paths.polynomial parameter).eval point := by
    unfold Clearance.normalizedRadicand
    rewrite [polynomial_centered]
    exact Basic.mul_comm _ _
  exact NamedEquivalent.transport rfl (congrArg Named.exact scalar) factors

/-- Original factor certificate caches, one actual full product and original forward coordinate channels.

Both complete Owners remain indices. Whole certificate equalities retain
those exact Owners, and the value/coordinate subtype equations bind the
stored original arithmetic product and completed coordinate factory to those
identical cached inputs. No normalized-only full-root certificate is used.
-/
@[expose] def Values (site : Fin 2) (parameter point : Canonical)
    (unit : SquareRootContinuationChain.Owner ((unitPolynomial site).eval point))
    (normal : SquareRootContinuationChain.Owner (Clearance.normalizedRadicand site parameter point)) : Type 1 :=
  Σ unitRoot : { retained : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point) //
      retained = unit.certificate unit.parameterNonzero },
    Σ normalRoot : { retained : CertifiedSquareRoot.Certificate (Clearance.normalizedRadicand site parameter point) //
        retained = normal.certificate normal.parameterNonzero },
      Σ value : { retained : CoherentNamed // retained = unitRoot.val.value.mul normalRoot.val.value },
        { channels : CoordinateChannels site parameter point value.val unit // channels =
            CoordinateChannels.ofRoot site parameter point value.val
              (cubicSquare site parameter point unitRoot.val normalRoot.val value.val value.property)
              unit unitRoot.val unitRoot.property }

namespace Values

variable {site : Fin 2} {parameter point : Canonical}
variable {unit : SquareRootContinuationChain.Owner ((unitPolynomial site).eval point)}
variable {normal : SquareRootContinuationChain.Owner (Clearance.normalizedRadicand site parameter point)}

/-- Retain completed factor certificates, full product and coordinates with exact whole-cache identities. -/
@[expose] def ofCompleted
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero)
    (normalRoot : CertifiedSquareRoot.Certificate (Clearance.normalizedRadicand site parameter point))
    (normalRoot_eq : normalRoot = normal.certificate normal.parameterNonzero)
    (value : CoherentNamed) (value_eq : value = unitRoot.value.mul normalRoot.value)
    (channels : CoordinateChannels site parameter point value unit)
    (channels_eq : channels = CoordinateChannels.ofRoot site parameter point value
      (cubicSquare site parameter point unitRoot normalRoot value value_eq) unit unitRoot unitRoot_eq) :
    Values site parameter point unit normal :=
  ⟨⟨unitRoot, unitRoot_eq⟩, ⟨⟨normalRoot, normalRoot_eq⟩, ⟨⟨value, value_eq⟩, ⟨channels, channels_eq⟩⟩⟩⟩

/-- Construct one full product and coordinate cache from the identical supplied original factor certificates. -/
def ofCertificates
    (unitRoot : CertifiedSquareRoot.Certificate ((unitPolynomial site).eval point))
    (unitRoot_eq : unitRoot = unit.certificate unit.parameterNonzero)
    (normalRoot : CertifiedSquareRoot.Certificate (Clearance.normalizedRadicand site parameter point))
    (normalRoot_eq : normalRoot = normal.certificate normal.parameterNonzero) :
    Values site parameter point unit normal :=
  let value := unitRoot.value.mul normalRoot.value
  let square := cubicSquare site parameter point unitRoot normalRoot value rfl
  let channels := CoordinateChannels.ofRoot site parameter point value square unit unitRoot unitRoot_eq
  ofCompleted unitRoot unitRoot_eq normalRoot normalRoot_eq value rfl channels rfl

/-- Cache each supplied Owner's original full certificate once, then retain their actual full product. -/
def build (unit : SquareRootContinuationChain.Owner ((unitPolynomial site).eval point))
    (normal : SquareRootContinuationChain.Owner (Clearance.normalizedRadicand site parameter point)) :
    Values site parameter point unit normal :=
  let unitRoot := unit.certificate unit.parameterNonzero
  let normalRoot := normal.certificate normal.parameterNonzero
  ofCertificates unitRoot rfl normalRoot rfl

/-- Read the complete unchanged original cofactor certificate cache. -/
@[expose] def unitRoot (values : Values site parameter point unit normal) := values.1.val

/-- Read the complete unchanged original normalized certificate cache of the distinct supplied normalized Owner. -/
@[expose] def normalRoot (values : Values site parameter point unit normal) := values.2.1.val

/-- Read the one actual stored full cubic arithmetic product. -/
@[expose] def value (values : Values site parameter point unit normal) : CoherentNamed := values.2.2.1.val

/-- Read the whole original coordinate construction on that identical stored value and cofactor certificate. -/
@[expose] def channels (values : Values site parameter point unit normal) :
    CoordinateChannels site parameter point values.value unit := values.2.2.2.val

/-- The cofactor certificate belongs to the supplied complete original Owner. -/
theorem unitRoot_eq (values : Values site parameter point unit normal) :
    values.unitRoot = unit.certificate unit.parameterNonzero := values.1.property

/-- The normalized certificate belongs to the separately supplied complete original Owner. -/
theorem normalRoot_eq (values : Values site parameter point unit normal) :
    values.normalRoot = normal.certificate normal.parameterNonzero := values.2.1.property

/-- The stored full ordinate is the actual product of the same two retained original factor values. -/
theorem value_eq (values : Values site parameter point unit normal) :
    values.value = values.unitRoot.value.mul values.normalRoot.value := values.2.2.1.property

/-- The cached full product satisfies the original cubic at that unchanged physical coordinate. -/
def square (values : Values site parameter point unit normal) :
    NamedEquivalent (values.value.mul values.value).name (Named.exact ((Paths.polynomial parameter).eval point)) :=
  cubicSquare site parameter point values.unitRoot values.normalRoot values.value values.value_eq

/-- The complete original coordinate cache is the completed factory on these identical retained factor/value inputs. -/
theorem channels_eq (values : Values site parameter point unit normal) : values.channels =
    CoordinateChannels.ofRoot site parameter point values.value values.square unit values.unitRoot values.unitRoot_eq :=
  values.2.2.2.property

/-- The original coordinate factory keeps the identical complete retained cofactor certificate. -/
theorem channels_unitRoot (values : Values site parameter point unit normal) :
    values.channels.unitRoot = values.unitRoot := by
  rewrite [values.channels_eq]
  exact CoordinateChannels.ofRoot_unitRoot _ _ _ _ _ _ _ _

end Values

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
