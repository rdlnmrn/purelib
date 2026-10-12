module
public import Purelib.Tactic.Omega.Constraint
public import Purelib.Tactic.Omega.LinearCombination
public import Purelib.Tactic.Omega.NatLinear
-- Generated client proofs retain these original integer comparison certificates.
public import Purelib.Data.Int.Order
-- Generated client equalities retain the original integer subtraction certificate.
public import Purelib.Data.Int.Arithmetic
-- Generated division certificates retain the original positive-divisor operations.
public import Purelib.Data.Int.Division

import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Omega.OmegaM
public meta import Lean.Elab.Tactic.Omega.Frontend
public import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Closure
meta import Lean.Util.MonadCache
public meta import Lean.Elab.Tactic.BuiltinTactic

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

public section

namespace Purelib.Tactic.QuotientFreeOmega

open Lean.Omega

/-- Reduce a finite coordinate evaluation by its explicit list and integer equations.

This local tactic unfolds only the displayed coefficient constructors, dot product and scalar zero/one identities. -/
local macro "coordinate_rfl" : tactic =>
  `(tactic|
    simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith, Int.one_mul, Int.zero_mul, Int.add_zero,
      Int.zero_add])
attribute [local simp] Purelib.Tactic.Omega.NatLinear.natExpr_denote_toPoly

open Lean Elab Tactic Meta

-- Dense case splitting avoids proof-bearing sparse exclusions in generated matchers.
-- Scope it to the private elaboration routines; ordinary theorem APIs are unchanged.

set_option backward.match.sparseCases false in
/-- Decode the literal integer lists emitted by Omega's `ToExpr Coeffs`
instance. -/
private meta def coefficientsOfExprAux : Nat → Lean.Expr → MetaM Coeffs
  | 0, expression =>
      throwError "Omega emitted an excessively deep coefficient vector: {expression}"
  | fuel + 1, expression => do
      let function := expression.getAppFn
      if function.isConstOf ``List.nil then
        return []
      let arguments := expression.getAppArgs
      if function.isConstOf ``List.cons then
        if retainedSize : arguments.size = 3 then
          have headBound : 1 < arguments.size := by rw [retainedSize]; decide
          have tailBound : 2 < arguments.size := by rw [retainedSize]; decide
          let head := arguments[1]'headBound
          let tail := arguments[2]'tailBound
          let some value ← getIntValue? head |
            throwError "Omega emitted a non-literal coefficient: {head}"
          return value :: (← coefficientsOfExprAux fuel tail)
      throwError "Omega emitted an unrecognized coefficient vector: {expression}"

/-- Decode a literal Omega coefficient list using fuel determined by the expression depth. -/
private meta def coefficientsOfExpr (expression : Lean.Expr) :
    MetaM Coeffs :=
  coefficientsOfExprAux (expression.approxDepth.toNat + 1) expression

/-- Replace one concrete `tidy_sat` application by the divisor and scaling
certificate that the tactic has just calculated. -/
private meta def replaceTidyProof (constraint coefficients values proof :
    Lean.Expr) : MetaM Lean.Expr := do
  let source ← coefficientsOfExpr coefficients
  let nonnegativeLeading := decide (0 ≤ source.leading)
  let prepared := if nonnegativeLeading then source else -source
  let divisor := prepared.gcd
  if divisor = 0 then
    let sourceZeroType ← mkAppM ``Coeffs.isZero #[coefficients]
    let sourceZeroProof ← mkDecideProof sourceZeroType
    let leadingExpression ← mkAppM ``Coeffs.leading #[coefficients]
    let leadingZeroType ← mkAppM ``Eq
      #[leadingExpression, toExpr (0 : Int)]
    let leadingZeroProof ← mkDecideProof leadingZeroType
    let gcdExpression ← mkAppM ``Coeffs.gcd #[coefficients]
    let gcdZeroType ← mkAppM ``Eq #[gcdExpression, toExpr (0 : Nat)]
    let gcdZeroProof ← mkDecideProof gcdZeroType
    return mkAppN (.const ``Purelib.Tactic.Omega.Constraint.tidy_sat_of_zero [])
      #[constraint, coefficients, values, sourceZeroProof,
        leadingZeroProof, gcdZeroProof, proof]
  let target := prepared.sdiv divisor
  let targetExpression := toExpr target
  let divisorExpression := toExpr divisor
  let divisorIntExpression := toExpr (divisor : Int)
  let scaledExpression ←
    mkAppM ``HMul.hMul #[divisorIntExpression, targetExpression]
  let sourceExpression ← if nonnegativeLeading then
      pure coefficients
    else
      mkAppM ``Neg.neg #[coefficients]
  let scalingProof ←
    Elab.Tactic.Omega.mkEqReflWithExpectedType
      sourceExpression scaledExpression
  let nonzeroType ← mkAppM ``Ne #[divisorExpression, toExpr (0 : Nat)]
  let nonzeroProof ← mkDecideProof nonzeroType
  let checker := if nonnegativeLeading then
      ``Purelib.Tactic.Omega.Constraint.div_sat_of_scaled
    else
      ``Purelib.Tactic.Omega.Constraint.neg_div_sat_of_scaled
  return mkAppN (.const checker [])
    #[constraint, coefficients, targetExpression, values, divisorExpression,
      nonzeroProof, scalingProof, proof]

set_option backward.match.sparseCases false in
/-- Read one original optional constraint field as the literal bound Omega retained.

The returned projection still refers to the original constraint. Decoding only
selects the displayed integer; the replacement proof separately certifies the
field equation in the kernel. -/
private meta def constraintBoundOfExpr (constraint : Lean.Expr)
    (projection : Name) : MetaM (Lean.Expr × Int) := do
  let field ← mkAppM projection #[constraint]
  let reduced ← whnf field
  let arguments := reduced.getAppArgs
  if reduced.getAppFn.isConstOf ``Option.some then
    if retainedSize : arguments.size = 2 then
      have boundPosition : 1 < arguments.size := by rw [retainedSize]; decide
      let bound := arguments[1]'boundPosition
      let some value ← getIntValue? bound |
        throwError "Omega emitted a non-literal constraint bound: {bound}"
      return (field, value)
  throwError "Omega emitted an absent or unrecognized contradiction bound: {field}"

/-- Reconstruct a concrete impossible-constraint proof from its original retained bounds.

Both projected-field equalities and the strict comparison are kernel-certified.
The original constraint, coefficient owners and satisfaction witness are passed
unchanged to the direct bounds theorem. -/
private meta def replaceImpossibleProof (constraint source values satisfies :
    Lean.Expr) : MetaM Lean.Expr := do
  let (lowerField, lower) ← constraintBoundOfExpr constraint ``Constraint.lowerBound
  let (upperField, upper) ← constraintBoundOfExpr constraint ``Constraint.upperBound
  let lowerExpression := toExpr lower
  let upperExpression := toExpr upper
  let retainedLower ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    lowerField (toExpr (some lower))
  let retainedUpper ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    upperField (toExpr (some upper))
  let strictType ← mkAppM ``LT.lt #[upperExpression, lowerExpression]
  let strictComparison ← mkDecideProof strictType
  return mkAppN (.const ``Purelib.Tactic.Omega.Constraint.not_sat'_of_bounds [])
    #[constraint, source, values, lowerExpression, upperExpression,
      retainedLower, retainedUpper, strictComparison, satisfies]

set_option backward.match.sparseCases false in
/-- Reconstruct a modular-elimination certificate from exact finite quotient data.

The source coefficients, values and added-coordinate index remain the original
inputs. Kernel reduction verifies the proposed coefficient and remainder
quotients, the unused reduced coordinate and the actual added-variable equation. -/
private meta def replaceBmodProof (modulus remainder index coefficients values satisfies :
    Lean.Expr) : MetaM Lean.Expr := do
  let some naturalModulus ← getNatValue? modulus |
    throwError "Omega emitted a non-literal modular divisor: {modulus}"
  let some scalarRemainder ← getIntValue? remainder |
    throwError "Omega emitted a non-literal modular remainder: {remainder}"
  let source ← coefficientsOfExpr coefficients
  let reduced := source.map (fun coefficient => Int.bmod coefficient naturalModulus)
  let quotients := source.zipWith
    (fun coefficient reduced => (coefficient - reduced) / (naturalModulus : Int)) reduced
  let balancedRemainder := Int.bmod scalarRemainder naturalModulus
  let remainderQuotient :=
    (scalarRemainder - balancedRemainder) / (naturalModulus : Int)
  let reducedExpression := toExpr reduced
  let quotientExpression := toExpr quotients
  let quotientScalarExpression := toExpr remainderQuotient
  let divisorExpression := toExpr (naturalModulus : Int)
  let scaledCoefficients ← mkAppM ``HMul.hMul #[divisorExpression, quotientExpression]
  let reconstructedCoefficients ← mkAppM ``HAdd.hAdd
    #[scaledCoefficients, reducedExpression]
  let coefficientEquation ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    coefficients reconstructedCoefficients
  let balancedExpression ← mkAppM ``Int.bmod #[remainder, modulus]
  let scalarProduct ← mkAppM ``HMul.hMul
    #[divisorExpression, quotientScalarExpression]
  let reconstructedRemainder ← mkAppM ``HAdd.hAdd #[scalarProduct, balancedExpression]
  let remainderEquation ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    remainder reconstructedRemainder
  let reducedCoordinate ← mkAppM ``Purelib.Tactic.Omega.Coefficients.get
    #[reducedExpression, index]
  let unusedCoordinate ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    reducedCoordinate (toExpr (0 : Int))
  let sourceDot ← mkAppM ``Coeffs.dot #[coefficients, values]
  let reducedDot ← mkAppM ``Coeffs.dot #[reducedExpression, values]
  let balancedDot ← mkAppM ``Int.bmod #[sourceDot, modulus]
  let difference ← mkAppM ``HSub.hSub #[balancedDot, reducedDot]
  let addedValue ← mkAppM ``Int.ediv #[difference, divisorExpression]
  let actualValue ← mkAppM ``Purelib.Tactic.Omega.Coefficients.get #[values, index]
  let coordinateEquation ← Elab.Tactic.Omega.mkEqReflWithExpectedType
    actualValue addedValue
  return mkAppN (.const ``Purelib.Tactic.Omega.Constraint.bmod_sat [])
    #[modulus, remainder, index, coefficients, reducedExpression, quotientExpression,
      values, quotientScalarExpression, coefficientEquation, remainderEquation,
      unusedCoordinate, coordinateEquation, satisfies]

/-- Reconstruct direct evidence from a complete natural-linear validity certificate.

The original expression constraint and context are retained. Its finite normalized
checker is certified by kernel reduction, and the constructive witness replaces
the proposition-equality certificate only at a complete proof use. -/
private meta def validConstraintProof? (certificate : Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  unless certificate.getAppFn.isConstOf ``Nat.Linear.ExprCnstr.eq_true_of_isValid do
    return none
  let arguments := certificate.getAppArgs
  if retainedSize : arguments.size = 3 then
    have contextBound : 0 < arguments.size := by rw [retainedSize]; decide
    have constraintBound : 1 < arguments.size := by rw [retainedSize]; decide
    let context := arguments[0]'contextBound
    let constraint := arguments[1]'constraintBound
    let normalized ← mkAppM ``Nat.Linear.ExprCnstr.toNormPoly #[constraint]
    let checker ← mkAppM ``Purelib.Tactic.Omega.NatLinear.isValid #[normalized]
    let valid ← Elab.Tactic.Omega.mkEqReflWithExpectedType checker (toExpr true)
    return some <| mkAppN
      (.const ``Purelib.Tactic.Omega.NatLinear.natExprCnstr_denote_of_isValid [])
      #[context, constraint, valid]
  return none

set_option backward.match.sparseCases false in
/-- Instantiate a complete constant application's original declared type.

The original universe parameters and argument expressions instantiate the
successive forall bodies directly. Retained loose bound variables need no local
context, and no type inference is performed on the open application itself. -/
private meta def constantApplicationType (expression : Lean.Expr) : MetaM Lean.Expr := do
  let .const name levels := expression.getAppFn |
    throwError "Omega certificate is not a constant application: {expression}"
  let declaration ← getConstInfo name
  let mut type := declaration.type.instantiateLevelParams declaration.levelParams levels
  for argument in expression.getAppArgs do
    let .forallE _ _ body _ := type |
      throwError "Omega certificate has more arguments than its declared type: {expression}"
    type := body.instantiate1 argument
  return type

set_option backward.match.sparseCases false in
/-- Specialize a positive-literal divisor certificate with its original numerator.

The proposition comparison uses a fresh arbitrary Int in place of the complete
numerator argument, so it never inspects loose variables inside that expression.
The returned application retains the actual numerator and original scalar data. -/
private meta def positiveDivisorProof? (name : Name) (numerator divisor proof : Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  if divisor.hasLooseBVars then return none
  let some value ← getIntValue? divisor | return none
  match value with
  | .negSucc _ => return none
  | .ofNat 0 => return none
  | .ofNat (denominator + 1) =>
      let naturalDivisor := toExpr (denominator + 1)
      let positive := mkApp (.const ``Nat.zero_lt_succ []) (toExpr denominator)
      let candidate := mkAppN (.const name []) #[numerator, naturalDivisor, positive]
      let same ← withLocalDeclD `numerator (.const ``Int []) fun parameter => do
        let arguments := proof.getAppArgs
        let original ←
          if arguments.size = 2 then
            pure (mkAppN proof.getAppFn #[parameter, divisor])
          else if retainedSize : arguments.size = 3 then
            have witnessBound : 2 < arguments.size := by rw [retainedSize]; decide
            pure (mkAppN proof.getAppFn #[parameter, divisor, arguments[2]'witnessBound])
          else
            throwError "Omega division certificate has an unexpected argument count"
        let retained := mkAppN (.const name []) #[parameter, naturalDivisor, positive]
        let expected ← constantApplicationType original
        let provided ← constantApplicationType retained
        withTransparency .all (isDefEq expected provided)
      if same then return some candidate
      return none

set_option backward.match.sparseCases false in
/-- Compare a literal coefficient spine with arbitrary typed scalar parameters.

Each original cons position introduces one fresh Int and keeps its original tail
position. Omega's original identity wrapper `Coeffs.ofList` is retained around
the parameterized spine. The continuation runs under these local declarations;
an unknown list spine remains unknown rather than assuming a recursive identity. -/
private meta partial def withParametricCoefficients (source : Lean.Expr)
    (continuation : Lean.Expr → MetaM Bool) : MetaM (Option Bool) := do
  let function := source.getAppFn
  let arguments := source.getAppArgs
  if function.isConstOf ``Lean.Omega.Coeffs.ofList then
    if retainedSize : arguments.size = 1 then
      have listBound : 0 < arguments.size := by rw [retainedSize]; decide
      return ← withParametricCoefficients (arguments[0]'listBound) fun parameters =>
        continuation (mkApp function parameters)
    else return none
  if function.isConstOf ``List.nil then
    if arguments.size = 1 then
      return some (← continuation (mkApp (.const ``List.nil [0]) (.const ``Int [])))
  if function.isConstOf ``List.cons then
    if retainedSize : arguments.size = 3 then
      have tailBound : 2 < arguments.size := by rw [retainedSize]; decide
      withLocalDeclD `coefficient (.const ``Int []) fun parameter =>
        withParametricCoefficients (arguments[2]'tailBound) fun tail =>
          continuation (mkAppN (.const ``List.cons [0]) #[.const ``Int [], parameter, tail])
    else return none
  else return none

set_option backward.match.sparseCases false in
/-- Replace a literal finite lookup after comparing its complete parametric expressions.

Literal indices and complete list spines are retained. Arbitrary fresh Int heads
establish the same original coordinate or padded zero without normalizing the
actual heads, which may contain loose variables; unknown cases stay unchanged. -/
private meta def coefficientLookupProof? (source index : Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  if index.hasLooseBVars then return none
  let literal :=
    match index with
    | .lit (.natVal _) => true
    | _ =>
        let arguments := index.getAppArgs
        if index.getAppFn.isConstOf ``OfNat.ofNat then
          if retainedSize : arguments.size = 3 then
            have literalBound : 1 < arguments.size := by rw [retainedSize]; decide
            match arguments[1]'literalBound with
            | .lit (.natVal _) => true
            | _ => false
          else false
        else false
  if !literal then return none
  let same ← withParametricCoefficients source fun parameters => do
    let original := mkAppN (.const ``Lean.Omega.Coeffs.get []) #[parameters, index]
    let retained := mkAppN (.const ``Purelib.Tactic.Omega.Coefficients.get []) #[parameters, index]
    withTransparency .all (isDefEq original retained)
  match same with
  | some true =>
      return some (mkAppN (.const ``Purelib.Tactic.Omega.Coefficients.get []) #[source, index])
  | some false => return none
  | none => return none

set_option backward.match.sparseCases false in
/-- Replace one already-traversed proof node by its direct finite certificate.

Complete applications retain their original constraints, coordinates and
satisfaction witnesses. Scalar equalities, disequalities and linear negation
pass their original arguments directly, including bound variables, to the
owned proofs. Positive literal division retains the original operations; finite
lookup changes only after kernel definitional comparison. Normalization and
coordinate readback retain their original inputs. -/
private meta def replaceProofRoot (proof : Lean.Expr) : MetaM Lean.Expr := do
  let function := proof.getAppFn
  let arguments := proof.getAppArgs
  if function.isConstOf ``Lean.Omega.Coeffs.get then
    if retainedSize : arguments.size = 2 then
      have sourceBound : 0 < arguments.size := by rw [retainedSize]; decide
      have indexBound : 1 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← coefficientLookupProof?
          (arguments[0]'sourceBound) (arguments[1]'indexBound) then
        return direct
  if function.isConstOf ``Lean.Omega.Int.le_of_not_lt then
    if arguments.size = 3 then
      return mkAppN (.const ``Purelib.Data.Int.Order.le_of_not_lt []) arguments
  if function.isConstOf ``Lean.Omega.Int.lt_of_not_le then
    if arguments.size = 3 then
      return mkAppN (.const ``Purelib.Data.Int.Order.lt_of_not_le []) arguments
  if function.isConstOf ``Lean.Omega.Int.ofNat_sub_dichotomy then
    if arguments.size = 2 then
      return mkAppN (.const ``Purelib.Data.Int.Order.natCast_sub_dichotomy []) arguments
  if function.isConstOf ``Int.mul_ediv_self_le then
    if retainedSize : arguments.size = 3 then
      have numeratorBound : 0 < arguments.size := by rw [retainedSize]; decide
      have divisorBound : 1 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← positiveDivisorProof? ``Purelib.Data.Int.Division.mul_ediv_self_le
          (arguments[0]'numeratorBound) (arguments[1]'divisorBound) proof then
        return direct
  if function.isConstOf ``Int.lt_mul_ediv_self_add then
    if retainedSize : arguments.size = 3 then
      have numeratorBound : 0 < arguments.size := by rw [retainedSize]; decide
      have divisorBound : 1 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← positiveDivisorProof? ``Purelib.Data.Int.Division.lt_mul_ediv_self_add
          (arguments[0]'numeratorBound) (arguments[1]'divisorBound) proof then
        return direct
  if function.isConstOf ``Int.emod_def then
    if retainedSize : arguments.size = 2 then
      have numeratorBound : 0 < arguments.size := by rw [retainedSize]; decide
      have divisorBound : 1 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← positiveDivisorProof? ``Purelib.Data.Int.Division.emod_def
          (arguments[0]'numeratorBound) (arguments[1]'divisorBound) proof then
        return direct
  if function.isConstOf ``Lean.Omega.LinearCombo.coordinate_eval then
    if arguments.size = 2 then
      return mkAppN (.const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval [])
        arguments
  if function.isConstOf ``Int.lt_or_gt_of_ne then
    if retainedSize : arguments.size = 3 then
      have leftBound : 0 < arguments.size := by rw [retainedSize]; decide
      have rightBound : 1 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 2 < arguments.size := by rw [retainedSize]; decide
      return mkAppN (.const ``Purelib.Data.Int.Order.lt_or_gt_of_ne [])
        #[arguments[0]'leftBound, arguments[1]'rightBound,
          arguments[2]'witnessBound]
  if function.isConstOf ``Lean.Omega.LinearCombo.neg_eval then
    if retainedSize : arguments.size = 2 then
      have combinationBound : 0 < arguments.size := by rw [retainedSize]; decide
      have valuesBound : 1 < arguments.size := by rw [retainedSize]; decide
      return mkAppN (.const ``Purelib.Tactic.Omega.LinearCombination.neg_eval [])
        #[arguments[0]'combinationBound, arguments[1]'valuesBound]
  if function.isConstOf ``Lean.Omega.Constraint.addEquality_sat then
    if retainedSize : arguments.size = 4 then
      have constantBound : 0 < arguments.size := by rw [retainedSize]; decide
      have sourceBound : 1 < arguments.size := by rw [retainedSize]; decide
      have valuesBound : 2 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 3 < arguments.size := by rw [retainedSize]; decide
      return mkAppN (.const ``Purelib.Tactic.Omega.Constraint.addEquality_sat [])
        #[arguments[0]'constantBound, arguments[1]'sourceBound,
          arguments[2]'valuesBound, arguments[3]'witnessBound]
  if function.isConstOf ``Int.sub_eq_zero_of_eq then
    if retainedSize : arguments.size = 3 then
      have leftBound : 0 < arguments.size := by rw [retainedSize]; decide
      have rightBound : 1 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 2 < arguments.size := by rw [retainedSize]; decide
      return mkAppN (.const ``Purelib.Data.Int.Arithmetic.sub_eq_zero_of_eq [])
        #[arguments[0]'leftBound, arguments[1]'rightBound,
          arguments[2]'witnessBound]
  if function.isConstOf ``Lean.Omega.Int.ofNat_le_of_le then
    if retainedSize : arguments.size = 3 then
      have leftBound : 0 < arguments.size := by rw [retainedSize]; decide
      have rightBound : 1 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 2 < arguments.size := by rw [retainedSize]; decide
      let comparison := mkAppN (.const ``Purelib.Data.Int.Order.natCast_le_iff [])
        #[arguments[0]'leftBound, arguments[1]'rightBound]
      let left := arguments[0]'leftBound
      let right := arguments[1]'rightBound
      let integerComparison := mkApp2 (.const ``Int.le [])
        (mkApp (.const ``Int.ofNat []) left) (mkApp (.const ``Int.ofNat []) right)
      let naturalComparison := mkApp2 (.const ``Nat.le []) left right
      return mkAppN (.const ``Iff.mpr [])
        #[integerComparison, naturalComparison, comparison, arguments[2]'witnessBound]
  if function.isConstOf ``Lean.Omega.Int.ofNat_lt_of_lt then
    if retainedSize : arguments.size = 3 then
      have leftBound : 0 < arguments.size := by rw [retainedSize]; decide
      have rightBound : 1 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 2 < arguments.size := by rw [retainedSize]; decide
      let comparison := mkAppN (.const ``Purelib.Data.Int.Order.natCast_lt_iff [])
        #[arguments[0]'leftBound, arguments[1]'rightBound]
      let left := arguments[0]'leftBound
      let right := arguments[1]'rightBound
      let integerComparison := mkApp2 (.const ``Int.lt [])
        (mkApp (.const ``Int.ofNat []) left) (mkApp (.const ``Int.ofNat []) right)
      let naturalComparison := mkApp2 (.const ``Nat.lt []) left right
      return mkAppN (.const ``Iff.mpr [])
        #[integerComparison, naturalComparison, comparison, arguments[2]'witnessBound]
  if function.isConstOf ``of_eq_true then
    if retainedSize : arguments.size = 2 then
      have certificateBound : 1 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← validConstraintProof? (arguments[1]'certificateBound) then
        return direct
  if function.isConstOf ``Eq.mpr then
    if retainedSize : arguments.size = 4 then
      have certificateBound : 2 < arguments.size := by rw [retainedSize]; decide
      if let some direct ← validConstraintProof? (arguments[2]'certificateBound) then
        return direct
  if function.isConstOf ``Eq.mp then
    if retainedSize : arguments.size = 4 then
      have certificateBound : 2 < arguments.size := by rw [retainedSize]; decide
      if (arguments[2]'certificateBound).getAppFn.isConstOf
          ``Nat.Linear.ExprCnstr.eq_true_of_isValid then
        return .const ``True.intro []
  if function.isConstOf ``Lean.Omega.Constraint.not_sat'_of_isImpossible then
    let arguments := proof.getAppArgs
    if retainedSize : arguments.size = 5 then
      have constraintBound : 0 < arguments.size := by rw [retainedSize]; decide
      have sourceBound : 2 < arguments.size := by rw [retainedSize]; decide
      have valuesBound : 3 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 4 < arguments.size := by rw [retainedSize]; decide
      return ← replaceImpossibleProof (arguments[0]'constraintBound)
        (arguments[2]'sourceBound) (arguments[3]'valuesBound)
        (arguments[4]'witnessBound)
  if function.isConstOf ``Lean.Omega.bmod_sat then
    let arguments := proof.getAppArgs
    if retainedSize : arguments.size = 8 then
      have modulusBound : 0 < arguments.size := by rw [retainedSize]; decide
      have remainderBound : 1 < arguments.size := by rw [retainedSize]; decide
      have indexBound : 2 < arguments.size := by rw [retainedSize]; decide
      have sourceBound : 3 < arguments.size := by rw [retainedSize]; decide
      have valuesBound : 4 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 7 < arguments.size := by rw [retainedSize]; decide
      return ← replaceBmodProof (arguments[0]'modulusBound)
        (arguments[1]'remainderBound) (arguments[2]'indexBound)
        (arguments[3]'sourceBound) (arguments[4]'valuesBound)
        (arguments[7]'witnessBound)
  if function.isConstOf ``Lean.Omega.combo_sat' then
    let arguments := proof.getAppArgs
    if arguments.size = 9 then
      return mkAppN (.const ``Purelib.Tactic.Omega.Constraint.combo_sat' []) arguments
  if function.isConstOf ``Lean.Omega.tidy_sat then
    let arguments := proof.getAppArgs
    if retainedSize : arguments.size = 4 then
      have constraintBound : 0 < arguments.size := by rw [retainedSize]; decide
      have sourceBound : 1 < arguments.size := by rw [retainedSize]; decide
      have valuesBound : 2 < arguments.size := by rw [retainedSize]; decide
      have witnessBound : 3 < arguments.size := by rw [retainedSize]; decide
      return ← replaceTidyProof (arguments[0]'constraintBound)
        (arguments[1]'sourceBound) (arguments[2]'valuesBound)
        (arguments[3]'witnessBound)
  match proof with
  | .const ``Int.sub_nonneg_of_le levels =>
      return .const ``Purelib.Data.Int.Order.sub_nonneg_of_le levels
  | .const ``Lean.Omega.Constraint.combine_sat' levels =>
      return .const ``Purelib.Tactic.Omega.Constraint.combine_sat' levels
  | .const ``Lean.Omega.Constraint.addInequality_sat levels =>
      return .const ``Purelib.Tactic.Omega.Constraint.addInequality_sat levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_0 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_0 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_1 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_1 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_2 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_2 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_3 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_3 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_4 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_4 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_5 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_5 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_6 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_6 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_7 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_7 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_8 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_8 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_9 levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.coordinate_eval_9 levels
  | .const ``Lean.Omega.LinearCombo.add_eval levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.add_eval levels
  | .const ``Lean.Omega.LinearCombo.sub_eval levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.sub_eval levels
  | .const ``Lean.Omega.LinearCombo.mul_eval levels =>
      return .const ``Purelib.Tactic.Omega.LinearCombination.mul_eval levels
  | _ => return proof

set_option backward.match.sparseCases false in
/-- Reconstruct each shared proof node once, after its original immediate children.

Structural cache equality retains binder names and annotations. The original
binary application spine and raw bound variables pass through unchanged,
including domains, values and bodies of lambda, forall and let expressions. -/
private meta partial def replaceProofRootsCached (proof : Lean.Expr) :
    MonadCacheT ExprStructEq Lean.Expr MetaM Lean.Expr :=
  checkCache { val := proof : ExprStructEq } fun _ => do
    let rebuilt ← proof.traverseChildren replaceProofRootsCached
    liftM <| replaceProofRoot rebuilt

/-- Substitute direct finite checker lemmas throughout one generated Omega proof.

A fresh cache retains completed rewrites of the original shared expression
nodes. Each node uses the unchanged root reconstruction after its children;
the resulting proof is then sealed in the original auxiliary theorem. -/
private meta def replaceProofRoots (proof : Lean.Expr) : MetaM Lean.Expr :=
  (replaceProofRootsCached proof).run

set_option backward.match.sparseCases false in
/-- Run Omega, rewrite its finite certificate proof, and only then package the
usually large proof in an auxiliary declaration. -/
private meta def omegaTactic
    (configuration : Meta.Omega.OmegaConfig) : TacticM Unit := do
  recordExtraModUse (isMeta := false) `Init.Omega
  liftMetaFinishingTactic fun goal => do
    if debug.terminalTacticsAsSorry.get (← getOptions) then
      goal.admit
    else
      let some goal ← goal.falseOrByContra | return ()
      goal.withContext do
        let target ← goal.getType
        let proofGoal ← mkFreshExprSyntheticOpaqueMVar target
        let hypotheses := (← getLocalHyps).toList
        Elab.Tactic.Omega.omega hypotheses proofGoal.mvarId! configuration
        let proof ← instantiateMVarsProfiling proofGoal
        let proof ← replaceProofRoots proof
        let auxiliary ← mkAuxTheorem target proof (zetaDelta := true)
        goal.assign auxiliary

/-! Importing this module upgrades existing `omega` source.  This later rule
takes precedence over Lean's frontend while retaining its syntax. -/
elab_rules : tactic
  | `(tactic| omega%$token $configuration:optConfig) => do
      Meta.withReducibleAndInstances (evalAssumption token) <|> do
      let configuration ←
        Lean.Elab.Tactic.Omega.elabOmegaConfig configuration
      omegaTactic configuration

/-- Explicit quotient-free spelling for use in modules where another import
registers an `omega` frontend after this one. -/
elab "omega0" configuration:optConfig : tactic => do
  let configuration ←
    Lean.Elab.Tactic.Omega.elabOmegaConfig configuration
  omegaTactic configuration
end Purelib.Tactic.QuotientFreeOmega

end
