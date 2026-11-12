module

public import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Preparation
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.Multiplication
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Polynomial quadratic expressions at their original selected generator

Polynomial coefficients are evaluated at the retained coordinate, then
interpreted by the original pair denotation. Neither coefficient injection nor
nonsquareness is asserted: evaluation at one coordinate has no such property.
The source denominator guard and original generator equation remain explicit.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Algebra.Quadratic.Pair
open Purelib.Approximation.Gaussian.Division
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Field
open Purelib.Algebra
open Purelib.Approximation.Gaussian.Arithmetic

variable {radicand : Coefficients}

/-- Interpret the divided coefficients at the same supplied coordinate and original selected generator.

The total coefficient readback has mathematical quotient meaning on the
original `Defined` domain. Arithmetic laws additionally consume the original
generator's operational square equation. -/
@[expose] def denote (value : Expression radicand) (point : Canonical) (generator : CoherentNamed) : CoherentNamed :=
  Gaussian.denote id generator (value.evaluate point)

/-- The interpreted formal generator agrees with the same original selected generator. -/
@[noinline, nospecialize] def denote_generator (point : Canonical) (original : CoherentNamed) :
    NamedEquivalent ((generator (radicand := radicand)).denote point original).name original.name := by
  unfold denote
  rewrite [evaluate_generator]
  exact Gaussian.denote_generator id rfl rfl original

/-- A scalar expression realizes the exact original polynomial evaluation. -/
@[noinline, nospecialize] def denote_scalar (value : Coefficients) (point : Canonical) (original : CoherentNamed) :
    NamedEquivalent ((scalar (radicand := radicand) value).denote point original).name
      (Coherence.exact (value.eval point)).name := by
  unfold denote
  rewrite [evaluate_scalar]
  exact Gaussian.denote_scalar id rfl original (value.eval point)

/-- Coefficient equality supplies operational agreement on the original shared denominator domain. -/
@[noinline, nospecialize] def Equal.denote_equivalent {left right : Expression radicand}
    (equal : left.Equal right) (point : Canonical) (original : CoherentNamed)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    NamedEquivalent (left.denote point original).name (right.denote point original).name := by
  unfold denote
  rewrite [equal.evaluate_eq point leftDefined rightDefined]
  exact NamedEquivalent.refl _

/-- Addition realizes the original numerical operation on the same retained generator and domain. -/
@[noinline, nospecialize] def denote_add (left right : Expression radicand) (point : Canonical)
    (original : CoherentNamed) (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    NamedEquivalent (CoherentNamed.add (left.denote point original) (right.denote point original)).name
      ((left.add right).denote point original).name := by
  unfold denote
  rewrite [evaluate_add left right point leftDefined rightDefined]
  exact Gaussian.denote_add id (fun _ _ => rfl) original (left.evaluate point) (right.evaluate point)

/-- Multiplication realizes the original numerical operation using the original operational square equation. -/
@[noinline, nospecialize] def denote_mul (left right : Expression radicand) (point : Canonical)
    (original : CoherentNamed) (identity : PowerIdentity original 2 (radicand.eval point))
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    NamedEquivalent (CoherentNamed.mul (left.denote point original) (right.denote point original)).name
      ((left.mul right).denote point original).name := by
  unfold denote
  rewrite [evaluate_mul left right point leftDefined rightDefined]
  have equation : PowerIdentity original 2 (-id (-radicand.eval point)) := by
    change PowerIdentity original 2 (-(-radicand.eval point))
    rewrite [neg_neg]
    exact identity
  exact Gaussian.denote_mul id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    original equation (left.evaluate point) (right.evaluate point)

set_option genInjectivity false in
/-- Cached coefficient readback and channel at an admitted original selected generator.

The source expression, coordinate, generator, domain evidence and operational
square equation are indexed or retained. The weaker interpretation does not
claim coefficient injection or completeness of selected-sheet equality. -/
structure Denotation (original : Expression radicand) (point : Canonical) (generator : CoherentNamed) where
  /-- The original common-denominator expression as executable data. -/
  source : Expression radicand
  /-- The cached source retains the original expression. -/
  source_eq : source = original
  /-- The original displayed denominator is nonzero at this coordinate. -/
  defined : original.Defined point
  /-- The operational square equation of the same original selected generator. -/
  identity : PowerIdentity generator 2 (radicand.eval point)
  /-- The cached scalar quadratic pair, with the original evaluated radicand. -/
  value : Pair Canonical (-radicand.eval point)
  /-- The cached readback uses the original expression at this coordinate. -/
  value_eq : value = original.evaluate point
  /-- The cached numerical interpretation of these exact divided coefficients. -/
  channel : CoherentNamed
  /-- The cached channel uses this same original selected generator. -/
  channel_eq : channel = Gaussian.denote id generator value

constructive_injectivity Denotation

/-- Retain one admitted coefficient readback and its original-generator channel once. -/
@[expose] def retain (original : Expression radicand) (point : Canonical) (generator : CoherentNamed)
    (defined : original.Defined point) (identity : PowerIdentity generator 2 (radicand.eval point)) :
    Denotation original point generator :=
  let value := original.evaluate point
  ⟨original, rfl, defined, identity, value, rfl, Gaussian.denote id generator value, rfl⟩

/-- The retained channel is the original expression's denotation at this generator. -/
theorem Denotation.channel_readback {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (retained : Denotation original point generator) :
    retained.channel = original.denote point generator := by
  rewrite [retained.channel_eq, retained.value_eq]
  rfl

/-- Reinterpret the same cached pair and channel using equality at their actual retained coordinate.

Both expressions retain genuine nonzero denominator evidence there. The
operation changes only the expression/readback certificate; the original
generator, power identity, divided pair and channel remain literal caches.
No coefficient injectivity or equality away from this point is asserted.
-/
@[expose] def Denotation.reinterpretAt {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.evaluate point = original.evaluate point) (defined : target.Defined point) :
    Denotation target point generator :=
  ⟨target, rfl, defined, source.identity, source.value, source.value_eq.trans equal.symm,
    source.channel, source.channel_eq⟩

/-- Pointwise reinterpretation retains the same whole original coefficient and channel caches. -/
private theorem Denotation.packaged_reinterpretAt_factory {radicand : Coefficients}
    {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.evaluate point = original.evaluate point) (defined : target.Defined point) :
    source.reinterpretAt target equal defined =
      ⟨target, rfl, defined, source.identity, source.value, source.value_eq.trans equal.symm,
        source.channel, source.channel_eq⟩ := by rfl

/-- Pointwise reinterpretation retains the same whole original coefficient and channel caches. -/
theorem Denotation.reinterpretAt_factory {radicand : Coefficients}
    {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.evaluate point = original.evaluate point) (defined : target.Defined point) :
    source.reinterpretAt target equal defined =
      ⟨target, rfl, defined, source.identity, source.value, source.value_eq.trans equal.symm,
        source.channel, source.channel_eq⟩ := source.packaged_reinterpretAt_factory target equal defined

/-- Reuse the same scalar pair and channel for a finitely equal expression on the original domain.

The supplied cleared coefficient check is interpreted at this retained point.
Both expression denominator guards remain explicit; the original selected
generator and its power identity are retained without reevaluation.
-/
@[expose] def Denotation.reinterpret {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.Equal source.source) (defined : target.Defined point) : Denotation target point generator := by
  have sourceDefined : source.source.Defined point := by
    rewrite [source.source_eq]
    exact source.defined
  have readback : target.evaluate point = original.evaluate point :=
    source.source_eq ▸ equal.evaluate_eq point defined sourceDefined
  exact source.reinterpretAt target readback defined

/-- Global coefficient reinterpretation retains its complete original all-input factory value. -/
private theorem Denotation.packaged_reinterpret_factory {radicand : Coefficients}
    {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.Equal source.source) (defined : target.Defined point) :
    source.reinterpret target equal defined =
  (
    by
      have sourceDefined : source.source.Defined point := by
        rewrite [source.source_eq]
        exact source.defined
      have readback : target.evaluate point = original.evaluate point :=
        source.source_eq ▸ equal.evaluate_eq point defined sourceDefined
      exact ⟨target, rfl, defined, source.identity, source.value,
        source.value_eq.trans readback.symm, source.channel, source.channel_eq⟩
    : Denotation target point generator) := by rfl

/-- Global coefficient reinterpretation retains its complete original all-input factory value. -/
theorem Denotation.reinterpret_factory {radicand : Coefficients}
    {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (target : Expression radicand)
    (equal : target.Equal source.source) (defined : target.Defined point) :
    source.reinterpret target equal defined =
  (
    by
      have sourceDefined : source.source.Defined point := by
        rewrite [source.source_eq]
        exact source.defined
      have readback : target.evaluate point = original.evaluate point :=
        source.source_eq ▸ equal.evaluate_eq point defined sourceDefined
      exact ⟨target, rfl, defined, source.identity, source.value,
        source.value_eq.trans readback.symm, source.channel, source.channel_eq⟩
    : Denotation target point generator) := source.packaged_reinterpret_factory target equal defined

/-- Reuse the cached coefficients at an explicitly compared retained generator.

The source expression, coordinate, denominator guard and pair readback remain
unchanged. Only the interpreted channel and its operational square equation
are transported along the supplied comparison.
-/
@[expose] def Denotation.transport {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator) (target : CoherentNamed)
    (equivalent : NamedEquivalent target.name generator.name) : Denotation original point target :=
  ⟨source.source, source.source_eq, source.defined, source.identity.transport equivalent,
    source.value, source.value_eq, Gaussian.denote id target source.value, rfl⟩

/-- The transported channel compares to the original channel with the same exact cached pair. -/
@[noinline, nospecialize] def Denotation.transport_equivalent {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator) (target : CoherentNamed)
    (equivalent : NamedEquivalent target.name generator.name) :
    NamedEquivalent (source.transport target equivalent).channel.name source.channel.name := by
  rewrite [source.channel_eq]
  exact Gaussian.denote_transport id target generator equivalent source.value

set_option genInjectivity false in
/-- A cached polynomial scaling of one original denotation at its retained coordinate and generator.

The factor is evaluated once. Its actual pair multiplication, interpreted
channel and numerical scalar product consume that same cached value and the
original source coefficients.
-/
structure Denotation.Scaling {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (factor : Coefficients) where
  /-- The original denotation retained for the scaling operation. -/
  retainedSource : Denotation original point generator
  /-- The retained source belongs to this exact scaling input. -/
  retainedSource_eq : retainedSource = source
  /-- The retained original polynomial factor. -/
  retainedFactor : Coefficients
  /-- The factor is this exact original scaling input. -/
  retainedFactor_eq : retainedFactor = factor
  /-- The factor's one cached readback at the original coordinate. -/
  factorValue : Canonical
  /-- The cached factor uses the original retained polynomial and coordinate. -/
  factorValue_eq : factorValue = retainedFactor.eval point
  /-- The cached exact scaled pair and its interpreted channel at the original generator. -/
  target : Denotation (original.scale factor) point generator
  /-- The target consumes the cached factor and original cached pair. -/
  target_value_eq : target.value = Pair.scale factorValue retainedSource.value
  /-- The cached numerical scalar product of the same original channel and factor. -/
  output : CoherentNamed
  /-- The product consumes the cached factor and original retained source channel. -/
  output_eq : output = CoherentNamed.mul (Coherence.exact factorValue) retainedSource.channel
  /-- The actual scalar product realizes the exact scaled coefficients at the same retained generator. -/
  equivalent : NamedEquivalent output.name target.channel.name

constructive_injectivity Denotation.Scaling

/-- Compute one scaling while reusing the original cached coefficient table and pair readback. -/
@[expose] def Denotation.scale {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (factor : Coefficients) : source.Scaling factor := by
  let factorValue := factor.eval point
  let value := Pair.scale factorValue source.value
  let channel := Gaussian.denote id generator value
  let target : Denotation (original.scale factor) point generator :=
    ⟨source.source.scale factor, congrArg (Expression.scale factor) source.source_eq,
      Expression.defined_scale factor original point source.defined, source.identity, value, by
        change Pair.scale factorValue source.value = (original.scale factor).evaluate point
        rewrite [Expression.evaluate_scale, source.value_eq]
        rfl, channel, rfl⟩
  let output := CoherentNamed.mul (Coherence.exact factorValue) source.channel
  refine ⟨source, rfl, factor, rfl, factorValue, rfl, target, rfl, output, rfl, ?_⟩
  change NamedEquivalent (CoherentNamed.mul (Coherence.exact factorValue) source.channel).name channel.name
  rewrite [source.channel_eq]
  exact Gaussian.denote_scale id (fun _ _ => rfl) generator factorValue source.value

/-- The original inverse-root denotation retains the exact zero scalar coordinate and reciprocal-radicand
coefficient. -/
theorem Denotation.inverseRoot_value {point : Canonical} {generator : CoherentNamed}
    (source : Denotation (inverseRoot radicand) point generator) :
    source.value = ⟨0, (radicand.eval point)⁻¹⟩ := by
  rewrite [source.value_eq]
  apply Pair.ext
  · change (0 : Coefficients).eval point / _ = 0
    rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
    rfl
  · change (DensePolynomial.constant (1 : Canonical)).eval point /
      (Dense.Power.power radicand 1).eval point = _
    rewrite [DensePolynomial.eval_constant, Dense.Power.eval_power, pow_one, ExplicitField.div_eq_mul_inv]
    exact Basic.Canonical.one_mul _

/-- The original root and its cached formal inverse-root readback have operational product one. -/
@[noinline, nospecialize] def Denotation.inverseRoot_unit {point : Canonical} {generator : CoherentNamed}
    (source : Denotation (inverseRoot radicand) point generator) :
    NamedEquivalent (CoherentNamed.mul generator source.channel).name (Coherence.exact 1).name := by
  have nonzero : radicand.eval point ≠ 0 := by
    have defined := source.defined
    change (Dense.Power.power radicand 1).eval point ≠ 0 at defined
    rewrite [Dense.Power.eval_power, pow_one] at defined
    exact defined
  have equation : PowerIdentity generator 2 (-id (-radicand.eval point)) := by
    change PowerIdentity generator 2 (-(-radicand.eval point))
    rewrite [neg_neg]
    exact source.identity
  have product : (Pair.generator : Pair Canonical (-radicand.eval point)) * source.value = 1 := by
    rewrite [source.inverseRoot_value]
    apply Pair.ext
    · change 0 * 0 - (-radicand.eval point) * 1 * (radicand.eval point)⁻¹ = 1
      rewrite [Basic.zero_mul, Basic.mul_one,
        Ring.Multiplication.neg_mul, Basic.zero_sub, neg_neg]
      exact ExplicitField.mul_inv_cancel _ nonzero
    · change 0 * (radicand.eval point)⁻¹ + 1 * 0 = 0
      rewrite [Basic.zero_mul, Basic.mul_zero,
        Basic.zero_add]
      rfl
  have original := Product.Congruence.coherentMul_respects generator
    (Gaussian.denote id generator (Pair.generator : Pair Canonical (-radicand.eval point)))
    source.channel source.channel (Gaussian.denote_generator id rfl rfl generator).symm (NamedEquivalent.refl _)
  have multiplied := Gaussian.denote_mul id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    generator equation (Pair.generator : Pair Canonical (-radicand.eval point)) source.value
  rewrite [product] at multiplied
  have unit := Gaussian.denote_scalar (parameter := -radicand.eval point) id rfl generator (1 : Canonical)
  rewrite [← source.channel_eq] at multiplied
  exact original.trans (multiplied.trans unit)

/-- Actual reciprocal arithmetic compares to the same cached inverse-root coefficients at an original apart
generator. -/
@[noinline, nospecialize] def Denotation.inverseRoot_reciprocal {point : Canonical} {generator : CoherentNamed}
    (source : Denotation (inverseRoot radicand) point generator)
    (apart : Purelib.Approximation.Gaussian.Name.Basic.Named.Apart generator.name) :
    NamedEquivalent (CoherentNamed.div (Coherence.exact 1) generator apart).name source.channel.name :=
  let prepared : Prepared generator := ⟨generator, apart, NamedEquivalent.refl _⟩
  prepared.reciprocal_equivalent_of_product source.channel source.inverseRoot_unit

/-- The two exact cached inverse coefficients give an operational unit product at the original retained source.

Both numerical factors use the same original selected generator. The algebraic
identity is read back only after the source and norm guards have passed. -/
@[noinline, nospecialize] def Denotation.inverse_product {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator)
    (attempt : Inverse original) (admitted : attempt.Admitted point)
    (target : Denotation attempt.expression point generator) :
    NamedEquivalent (CoherentNamed.mul source.channel target.channel).name (Coherence.exact 1).name := by
  have equation : PowerIdentity generator 2 (-id (-radicand.eval point)) := by
    change PowerIdentity generator 2 (-(-radicand.eval point))
    rewrite [neg_neg]
    exact source.identity
  have comparison := Gaussian.denote_mul id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    generator equation source.value target.value
  have pairProduct : source.value * target.value = 1 := by
    rewrite [source.value_eq, target.value_eq, attempt.expression_eq]
    apply Expression.inverse_product original point admitted.1
    rewrite [← attempt.norm_eq]
    exact admitted.2
  rewrite [pairProduct] at comparison
  have unit := Gaussian.denote_scalar (parameter := -radicand.eval point) id rfl generator (1 : Canonical)
  rewrite [source.channel_eq, target.channel_eq]
  exact NamedEquivalent.trans comparison unit

set_option genInjectivity false in
/-- Actual numerical inversion through the retained original source and algebraic norm attempt.

The target denotation, factor observation, prepared denominator and quotient
are cached separately. The output uses the prepared source channel directly;
its comparison identifies the original inverse expression at the same sheet. -/
structure Reciprocal {original : Expression radicand} {point : Canonical} {generator : CoherentNamed}
    (source : Denotation original point generator) (attempt : Inverse original) where
  /-- The full original source denotation retained for execution. -/
  retainedSource : Denotation original point generator
  /-- The cached source is the original input denotation. -/
  retainedSource_eq : retainedSource = source
  /-- The full original inverse coefficient attempt. -/
  retainedAttempt : Inverse original
  /-- The cached attempt is the original input computation. -/
  retainedAttempt_eq : retainedAttempt = attempt
  /-- The source denominator and cached norm both satisfy their actual guards. -/
  admitted : attempt.Admitted point
  /-- The inverse expression's exact readback and channel at the same original generator. -/
  target : Denotation attempt.expression point generator
  /-- A finite source-factor observation obtained from the exact unit product. -/
  observation : Prepared.Factor.Observation source.channel target.channel 1
  /-- The cached preparation of the exact retained source channel. -/
  prepared : Prepared source.channel
  /-- Preparation consumes the cached factor observation. -/
  prepared_eq : prepared = observation.prepare
  /-- The actual cached reciprocal program using the prepared source. -/
  output : CoherentNamed
  /-- The output is the quotient by the same prepared source channel. -/
  output_eq : output = prepared.quotient (Coherence.exact 1)
  /-- The actual numerical reciprocal realizes the original guarded inverse coefficients. -/
  equivalent : NamedEquivalent output.name target.channel.name

constructive_injectivity Reciprocal

/-- Construct the actual reciprocal while consuming the source's cached readback and generator.

The factor observation is derived from the exact coefficient inverse identity.
It is not supplied by the caller and is reused by the denominator preparation
and the resulting division program. -/
@[noinline, nospecialize] def Denotation.reciprocal {original : Expression radicand} {point : Canonical}
    {generator : CoherentNamed} (source : Denotation original point generator)
    (attempt : Inverse original) (admitted : attempt.Admitted point) : Reciprocal source attempt :=
  let target := retain attempt.expression point generator (attempt.defined point admitted) source.identity
  let product := source.inverse_product attempt admitted target
  let observation := Prepared.Factor.observe source.channel target.channel 1 BoundaryCanonical.one_ne_zero product
  let prepared := observation.prepare
  let output := prepared.quotient (Coherence.exact 1)
  { retainedSource := source
    retainedSource_eq := rfl
    retainedAttempt := attempt
    retainedAttempt_eq := rfl
    admitted := admitted
    target := target
    observation := observation
    prepared := prepared
    prepared_eq := rfl
    output := output
    output_eq := rfl
    equivalent := prepared.reciprocal_equivalent_of_product target.channel product }

end Purelib.Algebra.Quadratic.Pair.Polynomial.Expression

end
