module
import Purelib.Integration.Program.Gaussian.Cached.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Comparison
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Apart.Preparation
public import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Division
public import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
public import Purelib.Approximation.Gaussian.Process.Recipe.Request
public import Purelib.Approximation.Gaussian.Process.Translation
import Purelib.Approximation.Rational.Request.Common
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Computation
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Query.Recipe
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Computation.Query.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction

/-!
# Exact process representations over cached integration recipes

A representation retains the original cached program, numerical recipe and
certified process together with their state-index map. Its equations compare
center bounds, exact retained ball readings and refinement indices. The six
original constructors transport these same owners through source, based,
translated, scaled, apartness-prepared and divided processes.
-/

namespace Purelib.Integration.Program.Gaussian.Query.Representation

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Integration.Program.Gaussian.Cached in
set_option genInjectivity false in
/-- An exact representation of an approximation process by a recipe over one retained cached integration program.

The state-index map preserves the original center bound, ball readings and refinement indices, keeping both process and
program owners fixed. -/
public structure Represents (program : Basic.CachedProgram) (recipe : Approximation.Gaussian.Process.Recipe) (process :
  Approximation.Gaussian.Process) where
  /-- The retained map from exact process states to original program stage indices. -/ index : process.State → Nat
  /-- The original process center bound equals the recipe's retained control bound. -/ bound_eq : process.centerBound =
    recipe.centerBound (IntegrationReplay.control program)
  /-- Every original process ball equals the recipe transform of the exact indexed source reading. -/ ball_eq : ∀ state,
    Enclosure.Ball.Data.BallData.ofBall (process.ball state) =
    recipe.transform (Enclosure.Ball.Data.BallData.ofBall (IntegrationReplay.reading (IntegrationReplay.control program)
      (index state) (program.stage (index state))).ball)
  /-- Original process refinement maps to the exact recipe-refined source index. -/ refine_eq : ∀ state target positive,
    index (process.refine state target positive) =
    recipe.refine (IntegrationReplay.control program) (index state) target

constructive_injectivity Represents

namespace Represents

open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Represent the original program approximation process by its exact source recipe and stage index.

The same retained cached program supplies the source process, original
stage-index identity, center bound and refinement equations. -/
@[expose] public def source (program : Basic.CachedProgram) : Represents program .source program.approximation.toProcess
  where
  index := fun index => index
  bound_eq := rfl
  ball_eq := fun _ => rfl
  refine_eq := fun _ _ _ => rfl

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Running the retained recipe against the original program stages returns the exact represented process ball.

The recipe queries the retained program stage at the represented state
index. Its exact source reading and original transformation return the
same process ball, without replacing the stage or its cache. -/
public theorem ball_run {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe} {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (state : process.State) :
    ((recipe.ball (IntegrationReplay.control program) (representation.index state)).run program.stage).value =
      .ok (Enclosure.Ball.Data.BallData.ofBall (process.ball state)) := by
  rw [Approximation.Gaussian.Process.Recipe.ball, Computation.Query.Protocol.map_run_value,
      IntegrationReplay.read_stage_value]
  change (Except.ok (recipe.transform _) : Except IntegrationReplay.InvalidReply Enclosure.Ball.Data.BallData) =
    Except.ok (Enclosure.Ball.Data.BallData.ofBall (process.ball state))
  rw [representation.ball_eq]

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Transport the representation to the process based at its retained original state.

Each based state retains its exact source state. The index, center
bound, ball identity and refinement equation are inherited from those
original states and the same program. -/
@[expose] public def based {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe} {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (base : process.State) :
    Represents program recipe (Process.Based.based process base) where
  index state := representation.index state.source
  bound_eq := representation.bound_eq
  ball_eq state := representation.ball_eq state.source
  refine_eq state target positive := representation.refine_eq state.source target positive

section
open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.Cached
/-- Retain the exact representation after subtracting the supplied Gaussian shift from the original process and recipe.

The supplied shift is retained by both the original process translation
and numerical recipe. Their center bound and target refinement use the
same scalar formulas and original source-index map. -/
@[expose] public def translated {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe}
    {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (shift : Basic.Canonical) :
    Represents program (recipe.translated (IntegrationReplay.control program) shift)
      (Process.Translation.translate process shift) where
  index := representation.index
  bound_eq := by
    simp only [Approximation.Gaussian.Process.Recipe.translated, Approximation.Gaussian.Process.Recipe.centerBound,
      Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    change 2 * (process.centerBound + Data.Gaussian.Norm.Basic.normSq shift) = 2 * (_ + Data.Gaussian.Norm.Basic.normSq
      shift)
    rw [representation.bound_eq]
  ball_eq := by
    intro state
    change Enclosure.Ball.Data.BallData.ofBall ((process.ball state).sub (Enclosure.Ball.point shift)) = _
    rw [← Enclosure.Ball.Data.BallData.translate_ofBall, representation.ball_eq]
    rfl
  refine_eq := by
    intro state target positive
    change representation.index (process.refine state (target / 4) _) = _
    rw [representation.refine_eq]
    rfl

/-- Retain the exact representation after multiplying the original process and recipe by the supplied Gaussian factor.

The supplied factor is retained by the exact-factor process and the
scaled recipe. Their cached center bounds, ball transforms and propagated
accuracy targets agree at the same original process states. -/
@[expose] public def scaled {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe} {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (factor : Basic.Canonical) :
    Represents program (recipe.scaled (IntegrationReplay.control program) factor)
      (Approximation.Gaussian.Process.mul (Approximation.Gaussian.Process.exact factor) process) where
  index state := representation.index state.2
  bound_eq := by
    simp only [Approximation.Gaussian.Process.Recipe.scaled, Approximation.Gaussian.Process.Recipe.centerBound,
      Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    change Data.Gaussian.Norm.Basic.normSq factor * process.centerBound = Data.Gaussian.Norm.Basic.normSq factor * _
    rw [representation.bound_eq]
  ball_eq := by
    intro state
    change Enclosure.Ball.Data.BallData.ofBall ((Enclosure.Ball.point factor).mul (process.ball state.2)) = _
    rw [← Enclosure.Ball.Data.BallData.scale_ofBall, representation.ball_eq]
    rfl
  refine_eq := by
    intro state target positive
    change representation.index (process.refine state.2
      (target / (target + (4 * (Data.Gaussian.Norm.Basic.normSq factor + process.centerBound) + 2))) _) = _
    rw [representation.refine_eq, representation.bound_eq]
    dsimp only [Approximation.Gaussian.Process.Recipe.refine, Approximation.Gaussian.Process.Recipe.sourceTarget,
      Approximation.Gaussian.Process.Recipe.scaled]
    rw [Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]

end

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Retain the exact representation through nonzero preparation using the original possible-reading lower bound.

The supplied possible-apartness certificate retains its original process
and lower squared bound. Preparation refines the same source states at
the corresponding common target and preserves their ball readings. -/
@[expose] public def apartified {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe}
    {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (apart : Process.Apart.Possible.PossibleApart process) :
    Represents program (.apart recipe apart.lowerSq) (Process.Apart.Preparation.apartify apart) where
  index state := representation.index state.source
  bound_eq := representation.bound_eq
  ball_eq state := representation.ball_eq state.source
  refine_eq := by
    intro state target positive
    change representation.index (process.refine state.source
      (Request.Common.commonTarget target (apart.lowerSq / 12)) _) = _
    rw [representation.refine_eq]
    rfl

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- The prepared nonzero state's index equals recipe refinement at one twelfth of the original lower squared bound.

The original possible-apartness lower bound determines the preparation
target. Applying the retained representation refinement equation gives
the exact source stage selected by the same recipe. -/
public theorem prepared_index {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe} {process
    :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (apart : Process.Apart.Possible.PossibleApart process)
    (state : process.State) :
    representation.index (Process.Apart.Preparation.prepareApartState apart state).source =
      recipe.refine (IntegrationReplay.control program) (representation.index state) (apart.lowerSq / 12) := by
  change representation.index (process.refine state (apart.lowerSq / 12) _) = _
  exact representation.refine_eq _ _ _

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Retain the exact representation after dividing the supplied numerator by the original process with its nonzero
certificate.

The denominator remains the original process with its supplied apartness
certificate. Both constructions retain the same numerator, lower squared
bound, cached center bound and original refinement-target formula. -/
@[expose] public def divided {program : Basic.CachedProgram} {recipe : Approximation.Gaussian.Process.Recipe} {process :
  Approximation.Gaussian.Process}
    (representation : Represents program recipe process) (numerator : Basic.Canonical)
    (apart : Approximation.Gaussian.Process.Apart process) :
    Represents program (recipe.divided numerator apart.lowerSq)
      (Approximation.Gaussian.Process.div (Approximation.Gaussian.Process.exact numerator) process apart) where
  index state := representation.index state.2
  bound_eq := by
    simp only [Approximation.Gaussian.Process.Recipe.divided, Approximation.Gaussian.Process.Recipe.centerBound,
      Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]
    rfl
  ball_eq := by
    intro state
    change Enclosure.Ball.Data.BallData.ofBall ((Enclosure.Ball.point numerator).div
      (process.ball state.2) ((Approximation.Gaussian.Process.Apart.atState apart) state.2)) = _
    rw [← Enclosure.Ball.Data.BallData.divide_ofBall, representation.ball_eq]
    rfl
  refine_eq := by
    intro state target positive
    change representation.index (process.refine state.2
      ((target * (apart.lowerSq * apart.lowerSq)) / (4 * (Data.Gaussian.Norm.Basic.normSq numerator +
        process.centerBound +
        1))) _) = _
    rw [representation.refine_eq, representation.bound_eq]
    dsimp only [Approximation.Gaussian.Process.Recipe.refine, Approximation.Gaussian.Process.Recipe.sourceTarget,
      Approximation.Gaussian.Process.Recipe.divided]
    rw [Basic.Canonical.Norm.Comparison.normSqFromReduced_eq]

end Represents

end Purelib.Integration.Program.Gaussian.Query.Representation
