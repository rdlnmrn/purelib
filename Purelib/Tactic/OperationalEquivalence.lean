module

public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Polynomial.Multivariate.Gaussian.PowerReduction
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization.Power
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Acquisition
-- Closed reconstruction consumes the original exposed comparison procedure;
-- its mathematical certificates remain in their ordinary execution phase.
import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
import Purelib.Polynomial.Multivariate.Gaussian.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
import Purelib.Approximation.Gaussian.Acquisition.Expression.Evaluation
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
meta import Lean.Elab.Tactic.Basic
meta import Lean.Elab.Tactic.ElabTerm
meta import Lean.Meta.Tactic.Intro
meta import Lean.Meta.AppBuilder
meta import Lean.Meta.Check
meta import Lean.Meta.Reduce

/-!
# Checked operational polynomial identities

The frontend recognizes original coherent arithmetic and finite natural powers.
Supplied intrinsic sidecars retain their original polynomial-zero programmes;
retained inverse and conjugation laws concern the same original channels.
Other channels remain opaque atoms, shared by exact elaborated expressions or
supplied comparisons. Existing normalization and equation-reduction operations
build each polynomial comparison, and kernel decision checks its finite coefficients.
Closed independent algebraic owners fall back to the original retained root
comparison programme; its actual equality or separation certificate is read
and the complete reconstructed proof is kernel-checked.

Supplied admission trees run before coefficient normalization. Their original
checker also constructs typed outcomes, retaining the ordered first reciprocal
obstruction and complete original children rather than cancelling through it.
-/

meta section

namespace Purelib.Tactic.OperationalEquivalence

open Lean Meta Elab Tactic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Polynomial.Multivariate
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

/-- A recognized arithmetic tree retaining exact original coefficient expressions and atom positions. -/
private inductive Arithmetic where
  | atom (index : Nat) (original equivalent : Expr)
  | constant (value : Expr)
  | neg (input : Arithmetic)
  | add (left right : Arithmetic)
  | mul (left right : Arithmetic)
  | power (input : Arithmetic) (exponent : Nat)
  /-- Retain an actual original-channel comparison before interpreting the same recognized child. -/
  | related (original equivalent : Expr) (input : Arithmetic)

/-- Read a coherent channel from an explicit projection of its original process name. -/
private def channelOfName (name : Expr) : MetaM Expr := do
  match name with
  | .proj ``CoherentNamed 0 channel => return channel
  | _ =>
      if name.isAppOfArity ``CoherentNamed.name 1 then return name.getAppArgs[0]!
      throwError "ccl_equiv: expected the name of an explicit coherent channel, received {name}"

/-- An actual supplied comparison with its exact original coherent endpoints. -/
private structure Evidence where
  /-- The exact original first coherent channel expression. -/
  left : Expr
  /-- The exact original second coherent channel expression. -/
  right : Expr
  /-- The supplied original-name comparison term in the actual local context. -/
  equivalent : Expr

/-- An actual retained power equation at its original generator and concrete degree/coefficient. -/
private structure PowerRelation where
  /-- The exact original coherent generator expression. -/
  generator : Expr
  /-- The retained concrete natural degree. -/
  degree : Expr
  /-- The exact closed Gaussian coefficient expression. -/
  parameter : Expr
  /-- The original degree-generic power-identity term. -/
  identity : Expr

/-- Check the finite data required for kernel coefficient reduction at a retained original power equation. -/
private def retainPowerRelation (generator degree parameter identity : Expr) : MetaM PowerRelation := do
  let degree ← instantiateMVars degree
  let reducedDegree ← whnf degree
  let some _ ← getNatValue? reducedDegree |
    throwError "ccl_equiv: retained power relation needs a concrete finite degree, received {degree}"
  let parameter ← instantiateMVars parameter
  if parameter.hasFVar || parameter.hasMVar then
    throwError "ccl_equiv: retained power relation needs an exact closed coefficient, received {parameter}"
  return ⟨generator, degree, parameter, identity⟩

/-- Transport the same original residual and cache together along its exact retained coefficient readback. -/
private def polynomialView (sidecar polynomial same : Expr) : MetaM Expr := do
  let actualType ← inferType sidecar
  let channel := actualType.getAppArgs[0]!
  let origin ← mkAppM ``Algebraic.Sidecar.origin #[sidecar]
  let residual ← mkAppM ``Algebraic.Sidecar.residual #[sidecar]
  let cached ← mkAppM ``Algebraic.Sidecar.cached #[sidecar]
  let residualType ← inferType residual
  let cachedType ← inferType cached
  withLocalDeclD `polynomial (← inferType polynomial) fun coefficient => do
    let residualType := mkAppN residualType.getAppFn #[coefficient, channel]
    let family ← withLocalDeclD `residual residualType fun retained => do
      mkLambdaFVars #[retained] (mkAppN cachedType.getAppFn #[channel, origin, coefficient, retained])
    let pairType ← mkAppM ``Sigma #[family]
    let transport ← mkLambdaFVars #[coefficient] pairType
    let equality ← mkCongrArg transport same
    let oldFamily ← withLocalDeclD `residual (← inferType residual) fun retained => do
      mkLambdaFVars #[retained] (mkAppN cachedType.getAppFn
        #[channel, origin, (← mkAppM ``Algebraic.Sidecar.polynomial #[sidecar]), retained])
    let pair ← mkAppOptM ``Sigma.mk
      #[some (← inferType residual), some oldFamily, some residual, some cached]
    let moved ← mkEqMP equality pair
    let actualResidual ← mkAppM ``Sigma.fst #[moved]
    let actualCached ← mkAppM ``Sigma.snd #[moved]
    mkAppOptM ``Algebraic.Sidecar.mk
      #[some channel, some origin, some polynomial, some actualResidual, some actualCached]

/-- Make an isolated root's displayed coefficients available through its original exact polynomial readback. -/
private def retainedSidecar (sidecar : Expr) : MetaM Expr := do
  if sidecar.isAppOfArity ``Algebraic.Sidecar.ofRoot 2 then
    let root := sidecar.getAppArgs[1]!
    if root.getAppFn.isConstOf ``PolynomialRoot.Sidecar.ofIsolated then
      let arguments := root.getAppArgs
      let first ← mkAppM ``Algebraic.Sidecar.ofRoot_polynomial #[root]
      let second ← mkAppM ``PolynomialRoot.Sidecar.ofIsolated_residual_polynomial
        #[arguments[arguments.size - 2]!, arguments.back!]
      let same ← mkEqTrans first second
      return ← polynomialView sidecar arguments[0]! same
  return sidecar

/-- Inspect the same displayed coefficients with the original typed recognition laws, keeping its opaque proof owner. -/
private def inspectSidecar (sidecar : Expr) : MetaM Expr := do
  let polynomial ← mkAppM ``Algebraic.Sidecar.polynomial #[sidecar]
  let residual ← mkAppM ``Algebraic.Sidecar.residual #[sidecar]
  let degree ← mkAppM ``Purelib.Polynomial.Dense.Basic.DensePolynomial.natDegree #[polynomial]
  let positive ← mkAppM ``Purelib.Polynomial.Approximation.Gaussian.Residual.degreePositive #[residual]
  let bounded ← mkAppM ``Purelib.Data.Nat.Positive.RootDegree.mk #[degree, positive]
  let zero ← mkAppM ``Purelib.Data.Gaussian.Basic.Canonical.mk
    #[mkConst ``Purelib.Data.Rat.Fraction.zero, mkConst ``Purelib.Data.Rat.Fraction.zero]
  let parameter ← mkAppM ``Neg.neg #[← mkAppM
    ``Purelib.Polynomial.Dense.Basic.DensePolynomial.eval #[polynomial, zero]]
  let candidate ← mkAppM ``Purelib.Polynomial.Power.Gaussian.rootPolynomial #[parameter, bounded]
  let equality ← mkEq polynomial candidate
  let recognized ← isDefEq (← mkDecide equality) (mkConst ``Bool.true)
  let channel := (← inferType sidecar).getAppArgs[0]!
  let (form, specified) ← if recognized then do
      let same ← mkDecideProof equality
      let identity ← mkAppM ``Purelib.Polynomial.Approximation.Gaussian.Residual.powerIdentity
        #[residual, parameter, bounded, same]
      let form ← mkAppOptM ``Purelib.Polynomial.Approximation.Gaussian.Residual.PowerForm.recognized
        #[some polynomial, some channel, some residual, some same, some identity]
      pure (form, ← mkAppM ``Purelib.Polynomial.Approximation.Gaussian.Residual.inspectPower_recognized
        #[residual, same])
    else do
      let different ← mkDecideProof (← mkAppM ``Not #[equality])
      let form ← mkAppOptM ``Purelib.Polynomial.Approximation.Gaussian.Residual.PowerForm.other
        #[some polynomial, some channel, some residual, some different]
      pure (form, ← mkAppM ``Purelib.Polynomial.Approximation.Gaussian.Residual.inspectPower_other
        #[residual, different])
  let reverse ← mkEqSymm specified
  mkAppOptM ``Base.PowerInspection.mk #[some channel, some sidecar, some form, some reverse]

/-- Read original comparisons, intrinsic equations, retained inverses and checked construction evidence. -/
private def readEvidence (hints : Array Syntax) :
    TacticM (Array Evidence × Array PowerRelation × Array (Expr × Expr) ×
      Array Evidence × Array Expr × Array Expr) := do
  let mut evidence := #[]
  let mut powers := #[]
  let mut sidecars := #[]
  let mut rewrites := #[]
  let mut admitted := #[]
  let mut compared := #[]
  for hint in hints do
    let proof ← instantiateMVars (← elabTerm hint none)
    let type := (← instantiateMVars (← inferType proof)).consumeMData
    let arguments := type.getAppArgs
    if type.isAppOfArity ``Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity 3 then
      powers := powers.push (← retainPowerRelation arguments[0]! arguments[1]! arguments[2]! proof)
    else if type.isAppOfArity ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent 2 then
      let left ← channelOfName arguments[0]!
      let right ← channelOfName arguments[1]!
      if left.isAppOfArity ``Power.namedPower 2 && right.isAppOfArity ``CoherentNamed.Coherence.exact 1 then
        powers := powers.push (← retainPowerRelation left.getAppArgs[0]! left.getAppArgs[1]!
          right.getAppArgs[0]! proof)
      else if right.isAppOfArity ``Power.namedPower 2 && left.isAppOfArity ``CoherentNamed.Coherence.exact 1 then
        let reverse ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.symm #[proof]
        powers := powers.push (← retainPowerRelation right.getAppArgs[0]! right.getAppArgs[1]!
          left.getAppArgs[0]! reverse)
      else
        evidence := evidence.push ⟨left, right, proof⟩
    else if type.isAppOfArity ``Algebraic.Sidecar 1 then
      sidecars := sidecars.push (arguments[0]!, ← retainedSidecar proof)
    else if type.isAppOfArity ``PolynomialRoot.Sidecar 1 then
      sidecars := sidecars.push (arguments[0]!, ← retainedSidecar (← mkAppM ``Algebraic.Sidecar.ofRoot #[proof]))
    else if type.isAppOfArity ``RationalSidecar 1 then
      sidecars := sidecars.push (arguments[0]!, ← mkAppM ``Algebraic.Sidecar.ofRational #[proof])
    else if type.isAppOfArity ``Gaussian.Normalized.Inverse 4 then
      let equivalent ← mkAppM ``Gaussian.Normalized.Inverse.reciprocal_equivalent #[proof]
      let relationType ← inferType equivalent
      let relationArgs := relationType.getAppArgs
      rewrites := rewrites.push ⟨← channelOfName relationArgs[0]!, ← channelOfName relationArgs[1]!, equivalent⟩
      let outputEq ← mkAppM ``Gaussian.Normalized.Inverse.output_eq #[proof]
      let rightRefl ← mkEqRefl relationArgs[1]!
      let quotientRewrite ← withLocalDeclD `output (mkConst ``CoherentNamed) fun output => do
        let outputName ← mkAppM ``CoherentNamed.name #[output]
        let name ← mkLambdaFVars #[output] outputName
        let namedOutputEq ← mkCongrArg name outputEq
        let transported ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.transport
          #[namedOutputEq, rightRefl, equivalent]
        let transportType ← inferType transported
        let endpoints := transportType.getAppArgs
        pure (⟨← channelOfName endpoints[0]!, ← channelOfName endpoints[1]!, transported⟩ : Evidence)
      rewrites := rewrites.push quotientRewrite
      let product ← mkAppM ``Gaussian.Normalized.Inverse.reciprocal_product #[proof]
      let productType ← inferType product
      let productArgs := productType.getAppArgs
      evidence := evidence.push ⟨← channelOfName productArgs[0]!, ← channelOfName productArgs[1]!, product⟩
      let inputChannel := arguments[2]!
      let productRewrite ← withLocalDeclD `output (mkConst ``CoherentNamed) fun output => do
        let multiplied ← mkAppM ``CoherentNamed.mul #[output, inputChannel]
        let multipliedName ← mkAppM ``CoherentNamed.name #[multiplied]
        let name ← mkLambdaFVars #[output] multipliedName
        let same ← mkCongrArg name outputEq
        let reflexive ← mkEqRefl productArgs[1]!
        let transported ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.transport
          #[same, reflexive, product]
        let transportedType ← inferType transported
        let endpoints := transportedType.getAppArgs
        pure (⟨← channelOfName endpoints[0]!, ← channelOfName endpoints[1]!, transported⟩ : Evidence)
      evidence := evidence.push productRewrite
      let generator ← mkAppM ``Gaussian.Normalized.Inverse.generator #[proof]
      let generatorType ← inferType generator
      sidecars := sidecars.push (generatorType.getAppArgs[0]!, generator)
    else if type.isAppOfArity ``Algebraic.Sidecar.Compared 6 then
      compared := compared.push proof
    else if type.isAppOfArity ``Finished 3 then
      let completed ← mkAppM ``Finished.materialize #[proof]
      let sidecar ← mkAppM ``Completed.sidecar #[completed]
      let sidecarType ← inferType sidecar
      sidecars := sidecars.push (sidecarType.getAppArgs[0]!, sidecar)
    else if type.isAppOfArity ``Completed 3 then
      let sidecar ← mkAppM ``Completed.sidecar #[proof]
      let sidecarType ← inferType sidecar
      sidecars := sidecars.push (sidecarType.getAppArgs[0]!, sidecar)
    else if type.isAppOfArity ``Admitted 3 then
      admitted := admitted.push proof
    else
      throwError "ccl_equiv: evidence needs an original comparison, power equation, intrinsic sidecar, \
        retained inverse, checked completion, retained algebraic comparison or checked admission; received {type}"
  let originals := sidecars
  for (channel, sidecar) in originals do
    sidecars := sidecars.push (← mkAppM ``CoherentNamed.conj #[channel],
      ← mkAppM ``Algebraic.Sidecar.conj #[sidecar])
  return (evidence, powers, sidecars, rewrites, admitted, compared)

/-- Search finite supplied comparison paths to an already retained atom, composing their actual witnesses. -/
private def findAtomComparison (channel : Expr) (evidence : Array Evidence) (atoms : Array Expr) :
    MetaM (Option (Nat × Expr)) := do
  let name ← mkAppM ``CoherentNamed.name #[channel]
  let reflexive ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.refl #[name]
  let mut pending := #[(channel, reflexive)]
  let mut visited := #[channel]
  for index in [:2 * evidence.size + 1] do
    if index ≥ pending.size then break
    let (current, comparison) := pending[index]!
    if let some position := atoms.findIdx? (· == current) then return some (position, comparison)
    for edge in evidence do
      if current == edge.left && !visited.contains edge.right then
        let composed ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.trans
          #[comparison, edge.equivalent]
        visited := visited.push edge.right
        pending := pending.push (edge.right, composed)
      if current == edge.right && !visited.contains edge.left then
        let reverse ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.symm
          #[edge.equivalent]
        let composed ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.trans
          #[comparison, reverse]
        visited := visited.push edge.left
        pending := pending.push (edge.left, composed)
  return none

/-- Retain an original atom and its actual comparison to the selected original binding. -/
private def retainAtom (evidence : Array Evidence) (channel : Expr) : StateT (Array Expr) MetaM Arithmetic := do
  let atoms ← get
  if let some (index, equivalent) ← findAtomComparison channel evidence atoms then
    return .atom index channel equivalent
  let name ← mkAppM ``CoherentNamed.name #[channel]
  let equivalent ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.refl #[name]
  set (atoms.push channel)
  return .atom atoms.size channel equivalent

/-- Reify recognized constructors before reduction, retaining unsupported channels as opaque original atoms. -/
private partial def reify (evidence : Array Evidence) (rewrites : Array Evidence) (checked : Bool)
    (channel : Expr) : StateT (Array Expr) MetaM Arithmetic := do
  let channel ← instantiateMVars channel
  if evidence.any (fun edge => edge.left == channel || edge.right == channel) then
    return ← retainAtom evidence channel
  for rewrite in rewrites do
    if channel == rewrite.left then
      return .related channel rewrite.equivalent (← reify evidence #[] checked rewrite.right)
  let arguments := channel.getAppArgs
  let function := channel.getAppFn
  if function.isConstOf ``CoherentNamed.conj && arguments.size == 1 then
    let inner := arguments[0]!
    if inner.isAppOfArity ``CoherentNamed.conj 1 then
      let original := inner.getAppArgs[0]!
      let equivalent ← mkAppM ``CoherentNamed.conj_conj #[original]
      return .related channel equivalent (← reify evidence rewrites checked original)
    if inner.isAppOfArity ``CoherentNamed.Coherence.exact 1 then
      let coefficient := inner.getAppArgs[0]!
      let equivalent ← mkAppM ``CoherentNamed.conj_exact #[coefficient]
      let conjugated ← mkAppM ``Purelib.Data.Gaussian.Basic.Canonical.conj #[coefficient]
      return .related channel equivalent (.constant conjugated)
  if checked && function.isConstOf ``Horner.polynomialEval && arguments.size == 2 then
    let coefficients ← mkAppM ``Purelib.Polynomial.Dense.Basic.DensePolynomial.coeffs #[arguments[0]!]
    let zero ← mkAppM ``Purelib.Data.Gaussian.Basic.Canonical.mk
      #[mkConst ``Purelib.Data.Rat.Fraction.zero, mkConst ``Purelib.Data.Rat.Fraction.zero]
    let initial ← mkAppM ``CoherentNamed.Coherence.exact #[zero]
    let rec loop (initial coefficients : Expr) : StateT (Array Expr) MetaM Arithmetic := do
      let coefficients ← whnf coefficients
      if coefficients.isAppOfArity ``List.nil 1 then return ← reify evidence rewrites checked initial
      unless coefficients.isAppOfArity ``List.cons 3 do
        throwError "ccl_equiv: original Horner coefficients are not a displayed finite list: {coefficients}"
      let entries := coefficients.getAppArgs
      let product ← mkAppM ``CoherentNamed.mul #[initial, arguments[1]!]
      let coefficient ← mkAppM ``CoherentNamed.Coherence.exact #[entries[1]!]
      loop (← mkAppM ``CoherentNamed.add #[product, coefficient]) entries[2]!
    return ← loop initial coefficients
  if function.isConstOf ``CoherentNamed.add && arguments.size == 2 then
    return .add (← reify evidence rewrites checked arguments[0]!) (← reify evidence rewrites checked arguments[1]!)
  if function.isConstOf ``CoherentNamed.mul && arguments.size == 2 then
    return .mul (← reify evidence rewrites checked arguments[0]!) (← reify evidence rewrites checked arguments[1]!)
  if function.isConstOf ``CoherentNamed.neg && arguments.size == 1 then
    return .neg (← reify evidence rewrites checked arguments[0]!)
  if function.isConstOf ``CoherentNamed.Coherence.exact && arguments.size == 1 then
    let coefficient := arguments[0]!
    if !coefficient.hasFVar && !coefficient.hasMVar then return .constant coefficient
  if function.isConstOf ``Power.namedPower && arguments.size == 2 then
    if let some exponent ← getNatValue? arguments[1]! then
      return .power (← reify evidence rewrites checked arguments[0]!) exponent
    throwError "ccl_equiv: natural power has no retained concrete exponent: {arguments[1]!}"
  if function.isConstOf ``Basic.Expr.denote && arguments.size == 3 then
    let environment := arguments[1]!
    let sourceSyntax ← whnf arguments[2]!
    let children := sourceSyntax.getAppArgs
    let constructor := sourceSyntax.getAppFn
    if constructor.isConstOf ``Basic.Expr.neg && children.size == 3 then
      if (← whnf children[1]!).isConstOf ``Basic.Mode.total then
        return .neg (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[2]!]))
    if constructor.isConstOf ``Basic.Expr.add && children.size == 4 then
      if (← whnf children[1]!).isConstOf ``Basic.Mode.total then
        return .add (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[2]!]))
          (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[3]!]))
    if constructor.isConstOf ``Basic.Expr.sub && children.size == 4 then
      if (← whnf children[1]!).isConstOf ``Basic.Mode.total then
        return .add (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[2]!]))
          (.neg (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[3]!])))
    if constructor.isConstOf ``Basic.Expr.mul && children.size == 4 then
      if (← whnf children[1]!).isConstOf ``Basic.Mode.total then
        return .mul (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[2]!]))
          (← reify evidence rewrites checked (mkAppN function #[arguments[0]!, environment, children[3]!]))
    if constructor.isConstOf ``Basic.Expr.rational && children.size == 2 then
      return ← reify evidence rewrites checked (← mkAppM ``CoherentNamed.Coherence.exact #[children[1]!])
    if constructor.isConstOf ``Basic.Expr.atom && children.size == 2 then
      return ← retainAtom evidence (← mkAppM ``Purelib.Approximation.Gaussian.Acquisition.Annotated.channel
        #[mkApp environment children[1]!])
  retainAtom evidence channel

/-- Interpret the same retained arithmetic tree in the original algebraic Sidecar operations.

Missing intrinsic atoms remain absent. Supplied comparisons transport their
actual original sidecars; the interpreter creates no root owner or admission
for an unsupported analytic atom.
-/
private def algebraicSidecar (evidence : Array Evidence) (sidecars : Array (Expr × Expr)) :
    Arithmetic → MetaM (Option Expr)
  | .atom _ original _ => do
      let channels := sidecars.map Prod.fst
      let some (position, equivalent) ← findAtomComparison original evidence channels | return none
      if original == channels[position]! then return some sidecars[position]!.2
      return some (← mkAppM ``Algebraic.Sidecar.transport #[sidecars[position]!.2, equivalent])
  | .constant value => do
      let reading ← mkAppM ``RationalSidecar.exact #[value]
      return some (← mkAppM ``Algebraic.Sidecar.ofRational #[reading])
  | .neg input => do
      let some child ← algebraicSidecar evidence sidecars input | return none
      return some (← mkAppM ``Algebraic.Sidecar.neg #[child])
  | .add left right => do
      let some first ← algebraicSidecar evidence sidecars left | return none
      let some second ← algebraicSidecar evidence sidecars right | return none
      return some (← mkAppM ``Algebraic.Sidecar.add #[first, second])
  | .mul left right => do
      let some first ← algebraicSidecar evidence sidecars left | return none
      let some second ← algebraicSidecar evidence sidecars right | return none
      return some (← mkAppM ``Algebraic.Sidecar.mul #[first, second])
  | .power input exponent => do
      let some child ← algebraicSidecar evidence sidecars input | return none
      return some (← mkAppM ``Algebraic.Sidecar.pow #[child, mkNatLit exponent])
  | .related _ equivalent input => do
      let some child ← algebraicSidecar evidence sidecars input | return none
      return some (← mkAppM ``Algebraic.Sidecar.transport #[child, equivalent])

/-- Expand only actual local let values before deciding whether an original input is closed.

A genuinely quantified root, coefficient or process stays a free variable and
is never replaced by a convenient closed owner. The reverse context order
also expands dependencies of later local let values.
-/
private def originalClosedValue (value : Expr) : MetaM Expr := do
  let mut value ← instantiateMVars value
  let declarations := (← getLCtx).foldl (fun entries declaration => entries.push declaration) #[]
  for declaration in declarations.reverse do
    if let some body := declaration.value? then
      value := value.replaceFVar declaration.toExpr body
  instantiateMVars value

/-- Reuse a supplied whole comparison or build the original classifier on both retained algebraic trees.

The original default starts and inspection requests are passed unchanged.
The optional result records only absent intrinsic admissions; a present term
is the actual original typed equality/separation programme, including all its
parents and quantitative certificates.
-/
private def algebraicComparison (evidence : Array Evidence) (sidecars : Array (Expr × Expr))
    (compared : Array Expr) (rewrites : Array Evidence) (left right : Expr)
    (retainedTrees : Option (Arithmetic × Arithmetic) := none) : MetaM (Option Expr) := do
  for retained in compared do
    let arguments := (← inferType retained).getAppArgs
    if (← isDefEq arguments[0]! left) && (← isDefEq arguments[1]! right) then
      return some (← mkAppM ``Algebraic.Sidecar.Compared.comparison #[retained])
  let checked := !sidecars.isEmpty || !rewrites.isEmpty
  let (first, second) ← match retainedTrees with
    | some trees => pure trees
    | none => do
        let (trees, _) ← (do
          let first ← reify evidence rewrites checked left
          let second ← reify evidence rewrites checked right
          pure (first, second)).run #[]
        pure trees
  let some first ← algebraicSidecar evidence sidecars first | return none
  let some second ← algebraicSidecar evidence sidecars second | return none
  let retained ← mkAppM ``Algebraic.Sidecar.compare
    #[first, second, mkNatLit 0, mkNatLit 0, mkConst ``Bool.true, mkConst ``Bool.true, mkConst ``Bool.true]
  return some (← mkAppM ``Algebraic.Sidecar.Compared.comparison #[retained])

/-- Read a closed original comparison's actual certificate without trusting a host-computed decision tag.

Both equality and separation come from the original mathematical constructor.
The surrounding solver kernel-checks the reconstructed complete proof. An
irreducible or genuinely symbolic programme remains unresolved at elaboration;
its typed comparison can still be retained for ordinary execution.
-/
private def comparisonCertificate (comparison : Expr) (separated : Bool) : MetaM Expr := do
  let original ← originalClosedValue comparison
  if original.hasFVar || original.hasMVar then
    throwError "ccl_equiv: the original algebraic comparison contains symbolic inputs.\n\
      Retain its typed Algebraic.Comparison for execution; no closed selected-root decision was assumed."
  let selected ← withTransparency .all (whnf original)
  if selected.getAppFn.isConstOf ``Algebraic.Comparison.equal then
    if separated then
      throwError "ccl_equiv: the original algebraic comparison identifies the same selected site.\n\
        Actual original-channel certificate: {selected.getAppArgs.back!}"
    return selected.getAppArgs.back!
  if selected.getAppFn.isConstOf ``Algebraic.Comparison.distinct then
    let arguments := selected.getAppArgs
    if separated then return arguments.back!
    throwError "ccl_equiv: the original algebraic comparison separates the selected sites.\n\
      Actual quantitative difference preparation: {arguments[arguments.size - 2]!}\n\
      Actual non-equivalence certificate: {arguments.back!}"
  throwError "ccl_equiv: the original closed algebraic comparison is not reducible to its actual constructor.\n\
    Retain its typed Algebraic.Comparison for execution; no comparison result was assumed.\n\
    Original comparison: {comparison}\n\
    Stopped expression: {selected}"

/-- A generated coefficient expression and the existing ordinary normalization certificate computing it. -/
private structure Certificate where
  form : Expr
  normalized : Expr
  /-- The original normalization's named exact coefficient readback. -/
  formEq : Expr

/-- Apply an original normalization operation with an empty cache at its actual dependent input type. -/
private def withDefaultCache (operation : Name) (arguments : Array Expr) : MetaM Expr := do
  let applied ← mkAppM operation arguments
  let .forallE _ cacheType _ _ ← whnf (← inferType applied) |
    throwError "ccl_equiv: normalization operation has no cache input: {operation}"
  let cacheType ← whnf cacheType
  unless cacheType.isAppOfArity ``Option 1 do
    throwError "ccl_equiv: normalization cache input is not an Option: {cacheType}"
  let empty ← mkAppOptM ``Option.none #[some cacheType.appArg!]
  mkAppM' applied #[empty]

/-- Transport an original unary coefficient operation through its retained exact child-form equality. -/
private def unaryForm (operation : Name) (input : Certificate) (arguments : Array Expr := #[]) : MetaM Expr := do
  withLocalDeclD `form (← inferType input.form) fun form => do
    let result ← mkAppM operation (#[form] ++ arguments)
    let operation ← mkLambdaFVars #[form] result
    mkCongrArg operation input.formEq

/-- Transport an original binary coefficient operation through both actual child-form equalities. -/
private def binaryForm (operation : Name) (first second : Certificate) : MetaM Expr := do
  withLocalDeclD `first (← inferType first.form) fun left => do
    withLocalDeclD `second (← inferType second.form) fun right => do
      let result ← mkAppM operation #[left, right]
      let operation ← mkLambdaFVars #[left, right] result
      mkAppM ``congrArg₂ #[operation, first.formEq, second.formEq]

/-- Build finite coefficient data and checked operational schema applications in the actual local context. -/
private def certify (arity bindings : Expr) : Arithmetic → MetaM Certificate
  | .atom index original equivalent => do
      let bound ← mkAppM ``LT.lt #[mkNatLit index, arity]
      let proof ← mkDecideProof bound
      let position ← mkAppM ``Fin.mk #[mkNatLit index, proof]
      let form ← mkAppOptM ``Sparse.atom #[some (mkConst ``Purelib.Data.Gaussian.Basic.Canonical),
        none, none, none, some arity, none, some position]
      let normalized ← mkAppOptM ``Gaussian.Normalized.ofAtomComparison
        #[some arity, some bindings, some position, some original, some equivalent]
      let specified ← mkAppOptM ``Gaussian.Normalized.ofAtomComparison_form
        #[some arity, some bindings, some position, some original, some equivalent]
      return ⟨form, normalized, specified⟩
  | .constant value => do
      let form ← mkAppOptM ``Sparse.constant #[some (mkConst ``Purelib.Data.Gaussian.Basic.Canonical),
        none, none, none, some arity, some value]
      return ⟨form, ← mkAppM ``Gaussian.Normalized.constant #[bindings, value],
        ← mkAppM ``Gaussian.Normalized.constant_form #[bindings, value]⟩
  | .neg input => do
      let child ← certify arity bindings input
      return ⟨← mkAppM ``Sparse.neg #[child.form],
        ← withDefaultCache ``Gaussian.Normalized.neg #[child.normalized],
        ← mkEqTrans (← withDefaultCache ``Gaussian.Normalized.neg_form #[child.normalized])
          (← unaryForm ``Sparse.neg child)⟩
  | .add left right => do
      let first ← certify arity bindings left
      let second ← certify arity bindings right
      return ⟨← mkAppM ``Sparse.add #[first.form, second.form],
        ← withDefaultCache ``Gaussian.Normalized.add #[first.normalized, second.normalized],
        ← mkEqTrans (← withDefaultCache ``Gaussian.Normalized.add_form #[first.normalized, second.normalized])
          (← binaryForm ``Sparse.add first second)⟩
  | .mul left right => do
      let first ← certify arity bindings left
      let second ← certify arity bindings right
      return ⟨← mkAppM ``Sparse.mul #[first.form, second.form],
        ← withDefaultCache ``Gaussian.Normalized.mul #[first.normalized, second.normalized],
        ← mkEqTrans (← withDefaultCache ``Gaussian.Normalized.mul_form #[first.normalized, second.normalized])
          (← binaryForm ``Sparse.mul first second)⟩

  | .related original equivalent input => do
      let child ← certify arity bindings input
      let denotation ← mkAppM ``Gaussian.Normalized.denotation #[child.normalized]
      let channel ← mkAppM ``Gaussian.Normalized.channel #[child.normalized]
      let denotationEq ← mkAppM ``Gaussian.Normalized.denotation_eq #[child.normalized]
      let channelEq ← mkAppM ``Gaussian.Normalized.channel_eq #[child.normalized]
      let childEquivalent ← mkAppM ``Gaussian.Normalized.equivalent #[child.normalized]
      let combined ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.trans
        #[equivalent, childEquivalent]
      let normalized ← mkAppOptM ``Gaussian.Normalized.mk
        #[some arity, some bindings, some original, some child.form, some denotation,
          some channel, some denotationEq, some channelEq, some combined]
      return ⟨child.form, normalized, ← mkEqRefl child.form⟩
  | .power input exponent => do
      let child ← certify arity bindings input
      let exponent := mkNatLit exponent
      return ⟨← mkAppM ``Sparse.pow #[child.form, exponent],
        ← withDefaultCache ``Gaussian.Normalized.pow #[child.normalized, exponent],
        ← mkEqTrans (← withDefaultCache ``Gaussian.Normalized.pow_form #[child.normalized, exponent])
          (← unaryForm ``Sparse.pow child #[exponent])⟩

/-- Reduce both actual normalization certificates through retained equations at justified original binding positions. -/
private def reducePowers (arity : Expr) (atoms : Array Expr) (evidence : Array Evidence)
    (powers : Array PowerRelation) (first second : Certificate) : MetaM (Certificate × Certificate) := do
  let mut first := first
  let mut second := second
  for relation in powers do
    if let some (index, comparison) ← findAtomComparison relation.generator evidence atoms then
      let bound ← mkAppM ``LT.lt #[mkNatLit index, arity]
      let position ← mkAppM ``Fin.mk #[mkNatLit index, ← mkDecideProof bound]
      let reverse ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.symm #[comparison]
      let transported ← mkAppM ``Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity.transport
        #[relation.identity, reverse]
      let firstEq ← mkAppM ``Gaussian.Normalized.reduceAt_form
        #[first.normalized, position, relation.degree, relation.parameter, transported]
      let secondEq ← mkAppM ``Gaussian.Normalized.reduceAt_form
        #[second.normalized, position, relation.degree, relation.parameter, transported]
      let firstReadback ← mkEqTrans firstEq
        (← unaryForm ``Sparse.reduceAt first #[position, relation.degree, relation.parameter])
      let secondReadback ← mkEqTrans secondEq
        (← unaryForm ``Sparse.reduceAt second #[position, relation.degree, relation.parameter])
      first := ⟨← mkAppM ``Sparse.reduceAt #[first.form, position, relation.degree, relation.parameter],
        ← mkAppM ``Gaussian.Normalized.reduceAt
          #[first.normalized, position, relation.degree, relation.parameter, transported], firstReadback⟩
      second := ⟨← mkAppM ``Sparse.reduceAt #[second.form, position, relation.degree, relation.parameter],
        ← mkAppM ``Gaussian.Normalized.reduceAt
          #[second.normalized, position, relation.degree, relation.parameter, transported], secondReadback⟩
  return (first, second)

/-- Reduce finite forms through intrinsic original equations using the same retained checked compiler operation. -/
private def reduceSidecars (arity : Expr) (atoms : Array Expr) (evidence : Array Evidence)
    (sidecars : Array (Expr × Expr)) (first second : Certificate) : MetaM (Certificate × Certificate) := do
  let mut first := first
  let mut second := second
  for (channel, sidecar) in sidecars do
    if let some (index, comparison) ← findAtomComparison channel evidence atoms then
      let bound ← mkAppM ``LT.lt #[mkNatLit index, arity]
      let position ← mkAppM ``Fin.mk #[mkNatLit index, ← mkDecideProof bound]
      let reverse ← mkAppM ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent.symm #[comparison]
      let actual ← mkAppM ``Algebraic.Sidecar.transport #[sidecar, reverse]
      let inspection ← inspectSidecar actual
      let firstType ← inferType first.normalized
      let secondType ← inferType second.normalized
      let firstArguments := firstType.getAppArgs
      let secondArguments := secondType.getAppArgs
      let firstRequest ← mkAppOptM ``Base.Reduction.prepare
        #[some arity, some firstArguments[1]!, some firstArguments[2]!, some position,
          some actual, some inspection, some first.normalized]
      let secondRequest ← mkAppOptM ``Base.Reduction.prepare
        #[some arity, some secondArguments[1]!, some secondArguments[2]!, some position,
          some actual, some inspection, some second.normalized]
      let firstOutput ← mkAppM ``Base.Reduction.output #[firstRequest]
      let secondOutput ← mkAppM ``Base.Reduction.output #[secondRequest]
      let polynomial ← reduce (← mkAppM ``Algebraic.Sidecar.polynomial #[actual])
      let recognized := inspection.getAppArgs[2]!.getAppFn.isConstOf
        ``Purelib.Polynomial.Approximation.Gaussian.Residual.PowerForm.recognized
      let scalarForm (input : Expr) : MetaM Expr := do
        if recognized then
          let degree ← mkAppM ``Purelib.Polynomial.Dense.Basic.DensePolynomial.natDegree #[polynomial]
          let zero ← mkAppM ``Purelib.Data.Gaussian.Basic.Canonical.mk
            #[mkConst ``Purelib.Data.Rat.Fraction.zero, mkConst ``Purelib.Data.Rat.Fraction.zero]
          let parameter ← mkAppM ``Neg.neg #[← mkAppM
            ``Purelib.Polynomial.Dense.Basic.DensePolynomial.eval #[polynomial, zero]]
          mkAppM ``Sparse.reduceAt #[input, position, degree, parameter]
        else
          let division ← mkAppM ``Sparse.DivisionAt.prepare #[input, position, polynomial]
          mkAppM ``Sparse.DivisionAt.remainder #[division]
      let firstReadback ← mkAppOptM ``Base.Reduction.prepare_form
        #[some arity, some firstArguments[1]!, some firstArguments[2]!, some position, some actual,
          some inspection, some first.normalized, some first.form, some first.formEq]
      let secondReadback ← mkAppOptM ``Base.Reduction.prepare_form
        #[some arity, some secondArguments[1]!, some secondArguments[2]!, some position, some actual,
          some inspection, some second.normalized, some second.form, some second.formEq]
      first := ⟨← scalarForm first.form, firstOutput, firstReadback⟩
      second := ⟨← scalarForm second.form, secondOutput, secondReadback⟩
  return (first, second)

/-- Produce an ordinary comparison from recognized syntax and a kernel-checked finite coefficient equality. -/
private def comparison (evidence : Array Evidence) (powers : Array PowerRelation)
    (sidecars : Array (Expr × Expr)) (rewrites : Array Evidence) (compared : Array Expr)
    (left right : Expr) : MetaM Expr := do
  if !sidecars.isEmpty then
    let mut equations := evidence
    for (_, sidecar) in sidecars do
      let equation ← mkAppM ``Algebraic.Sidecar.equation #[sidecar]
      let relationType ← inferType equation
      let arguments := relationType.getAppArgs
      equations := equations.push ⟨← channelOfName arguments[0]!, ← channelOfName arguments[1]!, equation⟩
    if let some (_, equivalent) ← findAtomComparison left equations #[right] then
      return equivalent
  if !compared.isEmpty then
    if let some (_, equivalent) ← findAtomComparison left evidence #[right] then
      return equivalent
  let mut supplied : Option Expr := none
  for retained in compared do
    let arguments := (← inferType retained).getAppArgs
    if (← isDefEq arguments[0]! left) && (← isDefEq arguments[1]! right) then
      supplied := some (← mkAppM ``Algebraic.Sidecar.Compared.comparison #[retained])
      break
  let checked := !sidecars.isEmpty || !rewrites.isEmpty
  let ((first, second), atoms) ← (do
    let first ← reify evidence rewrites checked left
    let second ← reify evidence rewrites checked right
    pure (first, second)).run #[]
  let firstTree := first
  let secondTree := second
  match firstTree, secondTree with
  | .atom firstIndex _ _, .atom secondIndex _ _ =>
      if firstIndex != secondIndex then
        if let some actual ← algebraicComparison evidence sidecars compared rewrites left right
            (some (firstTree, secondTree)) then
          return ← comparisonCertificate actual false
  | _, _ => pure ()
  let arity := mkNatLit atoms.size
  let retained ← mkListLit (mkConst ``CoherentNamed) atoms.toList
  let indexType ← mkAppM ``Fin #[arity]
  withLocalDeclD `index indexType fun index => do
    let entry ← mkAppM ``List.get #[retained, index]
    let bindings ← mkLambdaFVars #[index] entry
    let first ← certify arity bindings first
    let second ← certify arity bindings second
    let (first, second) ← reducePowers arity atoms evidence powers first second
    let (first, second) ← reduceSidecars arity atoms evidence sidecars first second
    let firstTerms ← mkAppM ``Sparse.terms #[first.form]
    let secondTerms ← mkAppM ``Sparse.terms #[second.form]
    let equality ← mkEq firstTerms secondTerms
    let decision ← mkDecide equality
    unless ← isDefEq decision (mkConst ``Bool.true) do
      if let some actual ← algebraicComparison evidence sidecars compared rewrites left right
          (some (firstTree, secondTree)) then
        return ← comparisonCertificate actual false
      throwError "ccl_equiv: coefficient forms differ; operational comparison remains unresolved.\n\
        Original opaque channels: {atoms.toList}\n\
        Missing input may be an atom comparison, generator equation or prepared domain.\n\
        First form: {firstTerms}\nSecond form: {secondTerms}"
    let mut same ← mkDecideProof equality
    let formType ← inferType first.form
    let terms ← withLocalDeclD `form formType fun form => do
      mkLambdaFVars #[form] (← mkAppM ``Sparse.terms #[form])
    if !sidecars.isEmpty then
      same ← mkEqTrans (← mkCongrArg terms first.formEq) same
      same ← mkEqTrans same (← mkEqSymm (← mkCongrArg terms second.formEq))
    let known ← mkAppM ``Gaussian.Normalized.compare #[first.normalized, second.normalized, same]
    match supplied with
    | some actual => pure (mkAppN (mkConst ``Algebraic.Comparison.equivalent) #[left, right, actual, known])
    | none => pure known

/-- Inspect original supplied checked runs before any coefficient normalization, retaining their actual result cache. -/
private def checkedInputs (admitted : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut inputs := #[]
  for actual in admitted do
    let outcome ← mkAppM ``Admitted.run #[actual]
    let selected ← whnf outcome
    if selected.getAppFn.isConstOf ``Outcome.completed then
      let result := selected.getAppArgs.back!
      let completed ← mkAppM ``Construction.Result.materialize #[result]
      let sidecar ← mkAppM ``Completed.sidecar #[completed]
      let type ← inferType sidecar
      inputs := inputs.push (type.getAppArgs[0]!, sidecar)
    else if selected.getAppFn.isConstOf ``Outcome.invalid then
      let invalid := selected.getAppArgs.back!
      let denominator ← mkAppM ``Invalid.denominator #[invalid]
      let preceding ← mkAppM ``Invalid.prefix #[invalid]
      throwError "ccl_equiv: the original checked run has a first zero reciprocal.\n\
        Original denominator and zero certificate: {denominator}\n\
        Retained completed prefix: {preceding}"
    else
      throwError "ccl_equiv: the original checked run cannot be reduced to a retained completed constructor.\n\
        Keep its typed CheckedResult for execution; coefficient normalization has not run.\n\
        Original run: {outcome}"
  return inputs

/-- Introduce actual local binders and consume original comparison, bit-law or checked-construction goals. -/
private partial def solve (goal : MVarId) (hints : Array Syntax) : TacticM Unit := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let separationGoal := target.isAppOfArity ``Not 1 ||
    match target with
    | .forallE _ _ body _ => body.isConstOf ``False
    | _ => false
  if target.isForall && !separationGoal then
    let (_, next) ← goal.intro1P
    solve next hints
  else
    let (evidence, powers, sidecars, rewrites, admitted, compared) ← readEvidence hints
    let arguments := target.getAppArgs
    let proof ← if target.isAppOfArity ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent 2 then do
        let actual ← checkedInputs admitted
        comparison evidence powers (sidecars ++ actual) rewrites compared
          (← channelOfName arguments[0]!) (← channelOfName arguments[1]!)
      else if target.isAppOfArity ``Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic.BitLaw 2 then do
        let actual ← checkedInputs admitted
        mkAppM ``Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic.BitLaw.ofEquivalent
          #[← comparison evidence powers (sidecars ++ actual) rewrites compared arguments[0]! arguments[1]!]
      else if target.isAppOfArity ``Algebraic.Comparison 2 then do
        let actual ← checkedInputs admitted
        let some comparison ← algebraicComparison evidence (sidecars ++ actual) compared rewrites
            arguments[0]! arguments[1]! |
          throwError "ccl_equiv: an original intrinsic Sidecar is missing for this algebraic comparison"
        pure comparison
      else if separationGoal then do
        let unavailable ← if target.isAppOfArity ``Not 1 then pure arguments[0]! else
          match target with
          | .forallE _ premise _ _ => pure premise
          | _ => throwError "ccl_equiv: malformed original separation goal"
        unless unavailable.isAppOfArity ``Nonempty 1 do
          throwError "ccl_equiv: separation expects not Nonempty of an original NamedEquivalent"
        let relation := unavailable.getAppArgs[0]!
        unless relation.isAppOfArity ``Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent 2 do
          throwError "ccl_equiv: separation expects not Nonempty of an original NamedEquivalent"
        let endpoints := relation.getAppArgs
        let actual ← checkedInputs admitted
        let some comparison ← algebraicComparison evidence (sidecars ++ actual) compared rewrites
            (← channelOfName endpoints[0]!) (← channelOfName endpoints[1]!) |
          throwError "ccl_equiv: an original intrinsic Sidecar is missing for this separation"
        comparisonCertificate comparison true
      else if target.isAppOfArity ``CheckedResult 3 then do
        let some actual ← admitted.findSomeM? (fun actual => do
          let actualType ← inferType actual
          return if ← isDefEq actualType (mkAppN (mkConst ``Admitted) arguments) then
            some actual else none) |
          throwError "ccl_equiv: this checked construction needs intrinsic admissions at its original \
            environment/syntax"
        mkAppM ``Admitted.check #[actual]
      else if target.isAppOfArity ``Outcome.Resolved 4 then do
        let some actual ← admitted.findSomeM? (fun actual => do
          let certificate ← mkAppM ``Admitted.complete #[actual]
          return if ← isDefEq (← inferType certificate) target then some certificate else none) |
          throwError "ccl_equiv: no supplied original admission tree proves this exact \
            checked outcome resolved"
        pure actual
      else throwError "ccl_equiv: expected NamedEquivalent, BitLaw, an original algebraic \
        comparison/separation or an admitted checked result, received {target}"
    unless ← isDefEq (← inferType proof) target do
      throwError "ccl_equiv: reified arithmetic does not preserve the original target channel"
    let proof ← instantiateMVars proof
    let locals := (← getLCtx).foldl (fun retained declaration => retained.push declaration.toExpr)
      (#[] : Array Expr)
    let closed ← mkLambdaFVars locals proof
    checkWithKernel (← instantiateMVars closed)
    goal.assign proof

/-- Restore all elaboration state when a checked original-channel comparison cannot be produced. -/
private def runComparison (hints : Array Syntax) : TacticM Unit := do
  let saved ← saveState
  try
    solve (← getMainGoal) hints
    replaceMainGoal []
  catch error =>
    saved.restore
    throw error

/-- Prove a supported finite polynomial identity without changing the original coherent evaluators. -/
elab "ccl_equiv" : tactic => runComparison #[]

/-- Prove an original-channel identity or separation, or retain its original typed comparison/checked outcome. -/
elab "ccl_equiv" "[" hints:term,* "]" : tactic =>
  runComparison (hints.getElems.map (·.raw))

end Purelib.Tactic.OperationalEquivalence

end

-- The whole module is an elaboration tool, including generated datatype,
-- projection and matching auxiliaries. Imported mathematical APIs keep their phase.
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  for (name, _) in environment.constants.map₂.toList do
    modifyEnv fun current => markMeta (setDeclMeta current name) name
