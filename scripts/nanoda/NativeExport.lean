/-
Adapted from leanprover/lean4export at 05d43a2bc773b40ecfdebb32294192a5ef756951.
The upstream Apache 2.0 license is retained in lean4export.LICENSE.
Repository changes add private artifact import, audit root selection, global
metadata-removal reuse, mutual-group recursor collection and hard missing/unsafe failures.
-/
module

-- The public meta entrypoint exposes its complete compiled Lean reflection dependencies.
public meta import Lean
import Std.Data.HashMap.Basic
meta import Lean.Compiler.CSimpAttr

meta section

namespace Nanoda.Export

open Lean
open Std (HashMap)

/-- Encode the retained binder visibility without changing its value. -/
private def binderInfoJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

/-- Encode the complete retained definition reducibility hint. -/
private def hintsJson : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular n => .mkObj [("regular", n.toNat)]

/-- Encode the retained quotient declaration kind. -/
private def quotKindJson : QuotKind → Json
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

/-- Encode the original definition execution safety. -/
private def safetyJson : DefinitionSafety → Json
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

/-- Render annotation values for diagnostic expression handling. -/
private def metadataJson (kvs : Lean.KVMap) : Json :=
  .mkObj <| kvs.entries.map (fun (k, v) => (k.toString, reprStr v))

/-- Retain the complete private import environment for serialization. -/
private structure Context where
  env : Environment

/-- Share names, universes, expressions and complete declaration groups within one stream. -/
private structure State where
  visitedNames : HashMap Name Nat := HashMap.emptyWithCapacity 200000 |>.insert .anonymous 0
  visitedLevels : HashMap Level Nat := HashMap.emptyWithCapacity 1000 |>.insert .zero 0
  visitedExprs : HashMap Expr Nat := HashMap.emptyWithCapacity 262144
  visitedConstants : NameHashSet := {}
  noMDataExprs : HashMap Expr Expr := HashMap.emptyWithCapacity 100000
  /-- Maps the name of an inductive type to a list of names of corresponding recursors.
  This is used to facilitate exporting of related inductives, constructors, and recursors as a unit. -/
  recursorMap : NameMap NameSet := {}

/-- Serialize one shared environment with state and checked IO failures. -/
private abbrev M := ReaderT Context <| StateT State IO

/-- Initialize one shared serialization state for a complete environment. -/
private def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

/--
Initialize the exporter state from an environment and cli options.
The `recursorMap` maps each inductive declaration's name to the list
of relevant recursors, which is used to ensure that for any inductive
declaration, the inductives, constructors, and recursors are exported
together in that order.
-/
private def initState (env : Environment) : M Unit := do
  let mut recursorMap : NameMap NameSet := {}
  for (_, constInfo) in env.constants do
    if let .recInfo recVal := constInfo then
      for indName in recVal.all do
        recursorMap := recursorMap.alter indName <|
          fun
          | none => some <| NameSet.empty.insert recVal.name
          | some recNames => some <| recNames.insert recVal.name
  modify fun st => { st with
    recursorMap
  }

/--
For a given primitive (name, level, expr) to be exported:
IFF it's been seen before, return its index within the export file
IFF it has not been seen before, add it to the cache, print it into the export, and return its cache index.
-/
@[inline]
private def getIdx [Hashable α] [BEq α] (x : α) (namespaced : String)
    (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M Json) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println (s.setObjVal! namespaced idx).compress
  modify fun st => setM st ((getM st).insert x idx)
  return idx

/-- Emit a structural name once after its retained parent name. -/
private def dumpName (n : Name) : M Nat := getIdx n "in" (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s =>
    return .mkObj [
      ("str", .mkObj [
        ("pre", ← dumpName n),
        ("str", s)
      ])
    ]
  | .num n i =>
    return .mkObj [
      ("num", .mkObj [
        ("pre", ← dumpName n),
        ("i", i)
      ])
    ]

/-- Emit a universe level once after its retained dependencies. -/
private def dumpLevel (l : Level) : M Nat := getIdx l "il" (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return .mkObj [("succ", ← dumpLevel l)]
  | .max l1 l2 => return .mkObj [("max", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .imax l1 l2 => return .mkObj [("imax", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .param n => return .mkObj [("param", ← dumpName n)]

/-- Retain universe parameter names and their corresponding level nodes. -/
private def dumpUparams (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  let _ ← (uparams.map (Level.param)).mapM dumpLevel
  pure nameIdxs.toJson

/-- Emit an ordered list of retained declaration names. -/
private def dumpNames (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  return nameIdxs.toJson

/-- Remove annotations and normalize only the let dependency optimization hint. -/
private def removeMData (e : Expr) : M Expr := do
  if let some x := (← get).noMDataExprs[e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => removeMData e'
  | .fvar .. | .mvar ..=> unreachable!
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a =>
    pure <| e.updateApp! (← removeMData f) (← removeMData a)
  | .lam _ d b _ =>
    pure <| e.updateLambdaE! (← removeMData d) (← removeMData b)
  | .letE _ d v b _ =>
    -- Normalize `nonDep` to `false` to avoid duplicate expression indices.
    -- Lean's `BEq` for `Expr` considers the `nonDep` flag, but external type checkers
    -- (e.g., nanoda_lib) treat expressions as identical regardless of this optimization hint.
    -- Without normalization, the same expression can get different indices, causing parse errors.
    -- See: https://github.com/ammkrn/lean4export/commit/eb023e5
    pure <| e.updateLet! (← removeMData d) (← removeMData v) (← removeMData b) false
  | .forallE _ d b _ =>
    pure <| e.updateForallE! (← removeMData d) (← removeMData b)
  | .proj _ _ e2 =>
    pure <| e.updateProj! (← removeMData e2)
  modify (fun st => { st with noMDataExprs := st.noMDataExprs.insert e e' })
  pure e'

mutual

/-- Emit the complete expression DAG with literal dependency declarations. -/
private partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e "ie" (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .fvar .. | .mvar .. => panic! "cannot export free variables or metavariables"
    | .mdata a e' =>
      return .mkObj [
        ("mdata", .mkObj [
            ("data", metadataJson a),
            ("expr", ← dumpExprAux e')
        ])
      ]
    | .bvar i => return .mkObj [("bvar", i)]
    | .lit (.natVal i) => dumpNatDeps; return .mkObj [("natVal", s!"{i}")]
    | .lit (.strVal s) => dumpStrDeps; return .mkObj [("strVal", s)]
    | .sort l => return .mkObj [("sort", ← dumpLevel l)]
    | .const n us => return .mkObj [
      ("const", .mkObj [
        ("name", ← dumpName n),
        ("us", (← us.mapM dumpLevel).toJson)
      ])
    ]
    | .app f a => return .mkObj [
      ("app", .mkObj [
        ("fn", ← dumpExprAux f),
        ("arg", ← dumpExprAux a)
      ])
    ]
    | .lam n d b bi => return .mkObj [
      ("lam", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", binderInfoJson bi)
      ])
    ]
    | .forallE n d b bi => return .mkObj [
      ("forallE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", binderInfoJson bi)
      ])
    ]
    | .letE n d v b nondep => return .mkObj [
      ("letE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("value", ← dumpExprAux v),
        ("body", ← dumpExprAux b),
        ("nondep", nondep)
      ])
    ]
    | .proj s i e => return .mkObj [
      ("proj", .mkObj [
        ("typeName", ← dumpName s),
        ("idx", i),
        ("struct", ← dumpExprAux e)
      ])
    ]
where
  dumpNatDeps : M Unit := do
    let nat := ``Nat
    if (!(← get).visitedConstants.contains nat) && ((← read).env.find? nat).isSome
    then dumpConstant nat
  dumpStrDeps : M Unit := do
    let charOfNat := ``Char.ofNat
    if (!(← get).visitedConstants.contains charOfNat) && ((← read).env.find? charOfNat).isSome
    then dumpConstant charOfNat
    let stringOfList := ``String.ofList
    if (!(← get).visitedConstants.contains stringOfList) && ((← read).env.find? stringOfList).isSome
    then dumpConstant stringOfList

/-- Remove expression annotations once across the complete shared stream. -/
private partial def dumpExpr (e : Expr) : M Nat := do
  dumpExprAux (← removeMData e)

/-- Emit a complete retained declaration and its transitive proof dependencies. -/
private partial def dumpConstant (c : Name) : M Unit := do
  let some declar := (← read).env.find? c
    | throw <| IO.userError s!"Constant {c} not found in environment."
  if declar.isUnsafe then throw <| IO.userError s!"unsafe proof dependency: {c}"
  if (← get).visitedConstants.contains c then return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match declar with
  | .axiomInfo val => do
    dumpDeps val.type
    dumpObj [
      ("axiom", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("def", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("hints", hintsJson val.hints),
        ("safety", safetyJson val.safety),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("opaque", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("thm", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .quotInfo _ =>
    -- Always dump full Quot package in the sensible order
    dumpConstant ``Eq
    for c in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo val) := (← read).env.find? c
        | throw <| IO.userError s!"Constant {c} not found in environment."
      modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
      dumpObj [
        ("quot", .mkObj [
          ("name", ← dumpName val.name),
          ("levelParams", ← dumpUparams val.levelParams),
          ("type", ← dumpExpr val.type),
          ("kind", quotKindJson val.kind)
        ])
      ]
  | .inductInfo baseIndVal => do
    let mut indVals := #[]
    let mut ctorVals := #[]
    let mut recursorNames := NameSet.empty
    for indName in baseIndVal.all do
      let val := ((← read).env.find? indName |>.get!).inductiveVal!
      if val.isUnsafe then throw <| IO.userError s!"unsafe inductive dependency: {val.name}"
      indVals := indVals.push val
      for ctor in val.ctors do
        match ((← read).env.find? ctor |>.get!) with
        | .ctorInfo ctorVal =>
          if ctorVal.isUnsafe then throw <| IO.userError s!"unsafe constructor dependency: {ctorVal.name}"
          ctorVals := ctorVals.push ctorVal
        | _ => panic! "Expected a `ConstantInfo.ctorInfo`."
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert indName }
      dumpDeps val.type
      if let .some names := (← get).recursorMap.get? indName
      then recursorNames := recursorNames.union names
      else assert! ctorVals.size == 0

    /- We dump the constructor dependencies (which will not include the inductives in this block since we've
    added the names to `visitedConstants`) before actually outputting anything in this inductive block to
    ensure e.g. the `LT` in `Fin.mk` is dumped before this inductive block appears in the export file. -/
    for ctorVal in ctorVals do
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert ctorVal.name }
      dumpDeps ctorVal.type

    let mut recursorVals := #[]
    for recursorName in recursorNames do
      match ((← read).env.find? recursorName |>.get!) with
      | .recInfo recVal =>
        if recVal.isUnsafe then throw <| IO.userError s!"unsafe recursor dependency: {recVal.name}"
        recursorVals := recursorVals.push recVal
      | _ => panic! "expected a `constantinfo.recinfo`."
    for recursorVal in recursorVals do
      modify fun st => { st with visitedConstants:= st.visitedConstants.insert recursorVal.name }
      dumpDeps recursorVal.type

    /- We only dump these after we've already dumped the `recursorVal` type and added the name
    to `visitedConstants` so that `dumpDeps` does not retry dumping the appearance of `Foo.rec` -/
    for recursorVal in recursorVals do
      for rule in recursorVal.rules do
        dumpDeps rule.rhs

    let inductiveValsJson ← indVals.mapM <| fun indVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName indVal.name),
          ("levelParams", ← dumpUparams indVal.levelParams),
          ("type", ← dumpExpr indVal.type),
          ("numParams", indVal.numParams),
          ("numIndices", indVal.numIndices),
          ("all", ← dumpNames indVal.all),
          ("ctors", ← dumpNames indVal.ctors),
          ("numNested", indVal.numNested),
          ("isRec", indVal.isRec),
          ("isReflexive", indVal.isReflexive),
          ("isUnsafe", indVal.isUnsafe),
      ]
    let ctorValsJson ← ctorVals.mapM <| fun ctorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName ctorVal.name),
          ("levelParams", ← dumpUparams ctorVal.levelParams),
          ("type", ← dumpExpr ctorVal.type),
          ("induct", ← dumpName ctorVal.induct),
          ("cidx", ctorVal.cidx),
          ("numParams", ctorVal.numParams),
          ("numFields", ctorVal.numFields),
          ("isUnsafe", ctorVal.isUnsafe)
      ]
    let recursorValsJson ← recursorVals.mapM <| fun recursorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName recursorVal.name),
          ("levelParams", ← dumpUparams recursorVal.levelParams),
          ("type", ← dumpExpr recursorVal.type),
          ("all", ← dumpNames recursorVal.all),
          ("numParams", recursorVal.numParams),
          ("numIndices", recursorVal.numIndices),
          ("numMotives", recursorVal.numMotives),
          ("numMinors", recursorVal.numMinors),
          ("rules", (← recursorVal.rules.mapM dumpRecRule).toJson),
          ("k", recursorVal.k),
          ("isUnsafe", recursorVal.isUnsafe),
      ]
    dumpObj [
      ("inductive", Json.mkObj [
        ("types", inductiveValsJson.toJson),
        ("ctors", ctorValsJson.toJson),
        ("recs", recursorValsJson.toJson),
      ])
    ]
  | .ctorInfo val => dumpConstant val.induct
  | .recInfo val =>
    for indName in val.all do
      dumpConstant indName
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  /- Return these for inclusion inline with the exported `recInfo`. -/
  dumpRecRule (rule : RecursorRule) : M Json := do
    return Json.mkObj [
      ("ctor", ← dumpName rule.ctor),
      ("nfields", rule.nfields),
      ("rhs", ← dumpExpr rule.rhs),
    ]
  dumpObj (fields : List (String × Json)) : M Unit :=
    IO.println <| Json.mkObj fields |>.compress

end

/-- Identify the pinned Lean and lean4export-compatible stream format. -/
private def exportMetadata : Json :=
  let leanMeta := Json.mkObj [
    ("version", versionString),
    ("githash", githash)
  ]
  let exporterMeta := Json.mkObj [
    ("name", "lean4export"),
    ("version", "3.1.0")
  ]
  let formatMeta := Json.mkObj [
    ("version", "3.1.0")
  ]

  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", exporterMeta),
      ("lean", leanMeta),
      ("format", formatMeta)
    ])
  ]

/-- Emit the version header before any stream identifiers. -/
private def dumpMetadata : M Unit := do
  IO.println exportMetadata.compress

/-- Recognize generated name components after removing the private owner prefix. -/
private def internalName : Name → Bool
  | .anonymous => false
  | .str parent text => text.startsWith "_" || internalName parent
  | .num parent _ => internalName parent

/-- Observe persisted source ranges without invoking extension callbacks. -/
private def hasRange (env : Environment) (name : Name) : Bool :=
  (declRangeExt.find? env name).isSome || (declRangeExt.find? (level := .server) env name).isSome

/-- Select the original source-facing predicate and registered global compiler rewrites. -/
private def auditRoot (env : Environment) (rewrites : NameHashSet) (info : ConstantInfo) : Bool := Id.run do
  let name := info.name
  let text := name.toString
  let constructorApi :=
    if text.endsWith ".inj" || text.endsWith ".injEq" then
      match env.find? name.getPrefix with
      | some (.ctorInfo ctor) => hasRange env ctor.induct
      | _ => false
    else false
  let excluded := (internalName (privateToUserName name) && !hasRange env name && !constructorApi) ||
    text.endsWith ".congr_simp" || text.endsWith ".eq_def" || text.endsWith ".induct_unfolding" ||
    info.isUnsafe || isMarkedMeta env name
  return !excluded || rewrites.contains name

/-- Parse a complete nonempty module inventory before importing any artifacts. -/
private def readModules (path : System.FilePath) : IO (Array Name) := do
  let contents ← IO.FS.readFile path
  let mut modules := #[]
  let mut seen : NameHashSet := {}
  for line in contents.splitOn "\n" do
    let text := line.trimAscii.toString
    if text.isEmpty then continue
    let some name := Syntax.decodeNameLit ("`" ++ text)
      | throw <| IO.userError s!"invalid selected module: {text}"
    if seen.contains name then
      throw <| IO.userError s!"repeated selected module: {name}"
    seen := seen.insert name
    modules := modules.push name
  if modules.isEmpty then throw <| IO.userError "selected module inventory is empty"
  return modules

/-- Retain each scanned module, first defining owner and kernel execution phase. -/
private def selectRoots (env : Environment) (modules : Array Name) : IO (Array Name × Json) := do
  let mut indices : NameMap Nat := {}
  let mut rewrites : NameHashSet := {}
  for index in [:env.header.moduleData.size] do
    indices := indices.insert env.header.modules[index]!.module index
    for entry in Compiler.CSimp.ext.ext.getModuleEntries env index do
      if let .global rewrite := entry then
        rewrites := rewrites.insert rewrite.thmName
  let mut roots := #[]
  let mut rows := #[]
  for selected in modules do
    let some index := indices.get? selected
      | throw <| IO.userError s!"selected module missing: {selected}"
    let data := env.header.moduleData[index]!
    if data.constNames.size != data.constants.size then
      throw <| IO.userError s!"incomplete private declaration inventory: {selected}"
    for name in data.constNames do
      unless (env.find? name).isSome do
        throw <| IO.userError s!"missing private kernel declaration: {selected}: {name}"
    let mut seen : NameHashSet := {}
    for name in data.constNames ++ data.extraConstNames do
      if seen.contains name then continue
      seen := seen.insert name
      -- IR-only extra names have no kernel declaration and make no proof claim.
      let some info := env.find? name | continue
      if auditRoot env rewrites info then
        let some ownerIndex := env.getModuleIdxFor? name
          | throw <| IO.userError s!"missing declaration owner: {name}"
        roots := roots.push name
        rows := rows.push <| Json.mkObj [
          ("scanned_module", toJson selected.toString),
          ("owner", toJson env.header.modules[ownerIndex]!.module.toString),
          ("name", toJson name.toString), ("phase", "kernel")]
  return (roots, Json.mkObj [("schema", 2), ("selected_modules", toJson (modules.map Name.toString)),
    ("roots", .arr rows)])

/-- Import complete private artifacts without target initializers, callbacks or plugins. -/
private def exportModules (manifest inventory : System.FilePath) : IO UInt32 := do
  let modules ← readModules manifest
  initSearchPath (← findSysroot)
  let before ← IO.monoMsNow
  let env ← importModules (modules.map fun name => { module := name }) {}
    (plugins := #[]) (loadExts := false) (level := .private)
  let after ← IO.monoMsNow
  let stderr ← IO.getStderr
  stderr.putStrLn s!"native nanoda: import_ms={after - before}"
  let (roots, record) ← selectRoots env modules
  IO.FS.writeFile inventory record.compress
  stderr.putStrLn s!"native nanoda: roots_ms={(← IO.monoMsNow) - after}"
  let started ← IO.monoMsNow
  M.run env do
    initState env
    dumpMetadata
    for root in roots do
      dumpConstant root
    let state ← get
    stderr.putStrLn s!"native nanoda: roots={roots.size} declarations={state.visitedConstants.size}"
    stderr.putStrLn s!"native nanoda: expressions={state.visitedExprs.size} export_ms={(← IO.monoMsNow) - started}"
  return 0

/-- Dispatch explicit metadata and artifact export requests. -/
private def runArgs (args : List String) : IO UInt32 := do
  match args with
  | ["--metadata"] => IO.println exportMetadata.compress; return 0
  | ["--export", manifest, inventory] => exportModules manifest inventory
  | _ => throw <| IO.userError "usage: nanoda-export --metadata | --export MANIFEST INVENTORY"

end Nanoda.Export

/-- Export a selected compiled environment as one complete lean4export-compatible stream. -/
public def main (args : List String) : IO UInt32 := Nanoda.Export.runArgs args

-- This entire module is an artifact-inspection tool. Lean 4.32 tags authored
-- declarations in `meta section`, but not all generated recursors, projections
-- and match functions. Retain the same meta phase for every local auxiliary.
-- Imported declarations are untouched; strict helper audits still select these.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.map₂.toList do
    modifyEnv fun current => markMeta (setDeclMeta current name) name
