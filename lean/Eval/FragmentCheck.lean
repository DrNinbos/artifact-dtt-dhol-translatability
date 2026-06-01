import Lean.Environment
import Lean.CoreM
import Lean.Meta.Basic
import Lean.ProjFns
import Lean.Server.Utils
import Std.Time.DateTime.Timestamp
import Eval.tt

namespace EvalFragment

open Lean Lean.Expr Lean.Meta

def mathlibModules : CoreM (Array Name) := do
  let u := (← getEnv).header.moduleNames
  return u.filter (fun name => name.components[0]? == .some `Mathlib)

def Name.isTheorem (name : Name) : CoreM Bool := do
  let .some ci := (← getEnv).find? name
    | throwError "Name.isTheorem :: Cannot find name {name}"
  let .thmInfo _ := ci
    | return false
  return true

def Name.isHumanTheorem (name : Name) : CoreM Bool := do
  let hasDeclRange := (← Lean.findDeclarationRanges? name).isSome
  let isTheorem ← Name.isTheorem name
  let notProjFn := !(← isProjectionFn name)
  return hasDeclRange && isTheorem && notProjFn

def allHumanTheorems : CoreM (Array ConstantInfo) := do
  let FullList := (← getEnv).constants.toList
  let (allConsts, _) := FullList.unzip
  let allHumanTheorems ← allConsts.filterM Name.isHumanTheorem
  let allInfos := (FullList.filter (fun (n,_) => allHumanTheorems.contains n)).map Prod.snd
  return Array.mk allInfos

def Name.isFromPackage (name : Name) (pkgPrefix : Name) : CoreM Bool := do
  let .some mod ← Lean.findModuleOf? name
    | return false
  return pkgPrefix.isPrefixOf mod

def allHumanTheoremsFromPackage (pkgPrefix : Name) :
  CoreM (Array (ConstantInfo × (Array ConstantInfo))) := do
  let allConsts := (← getEnv).constants.toList
  let allHumanTheoremsFromPackage ← allConsts.filterM (fun (n,_) =>
    return (← Name.isHumanTheorem n) && (← Name.isFromPackage n pkgPrefix))
  let thms := (allHumanTheoremsFromPackage.unzip.snd)
  let mut usedConstantLists := #[]
  for thm in thms do
    let cs := thm.type.getUsedConstants
    let mut tys := #[]
    for c in cs do
      let .some ci := (← getEnv).find? c
        | throwError "Name.isTheorem :: Cannot find name {c}"
      tys := tys.append #[ci]
    usedConstantLists := usedConstantLists.append #[tys]
  return (Array.mk thms).zip usedConstantLists

def printAllHumanTheoremsFromPackage (pkgPrefix : Name) : CoreM Unit := do
  let theorems ← allHumanTheoremsFromPackage pkgPrefix
  let theoremNames := theorems.map (fun (i, _) => i.name)
  logInfo m!"Found {theorems.size} theorem(s) in package {pkgPrefix}:\n{theoremNames}"

--#eval printAllHumanTheoremsFromPackage "Mathlib.Data.Vector.Basic"

inductive ExpTranslatable : Expr → Expr → Prop
  | const : ExpTranslatable _ (Expr.const _ _)
  | bvar : ExpTranslatable _ (Expr.bvar _)
  | fvar : ExpTranslatable _ (Expr.fvar _)
  | mvar : ExpTranslatable _ (Expr.mvar _)
  | prop : ExpTranslatable _ (Expr.sort 0)
  | app : ExpTranslatable (Expr.forallE x α β b) e1 → ExpTranslatable α2 e2 → ExpTranslatable (Expr.app (Expr.lam x α β b) α2) (Expr.app e1 e2)
  -- | lam : "Conds" → ExpTranslatable (Expr.forallE x α β bi') (Expr.lam x α e bi)
  -- | forall : "Conds" → ExpTranslatable (Expr.sort ?) (Expr.forallE x α β bi')

partial def checkInFragmentPre : Expr → MetaM (String ⊕ Unit)
  | .const _ _ => return Sum.inr ()
  | .bvar _ => return Sum.inr ()
  | .fvar _ => return Sum.inr ()
  | .mvar _ => return Sum.inr ()
  | .lit _ => return .inr ()
  | .sort ℓ => match ℓ.toNat with
    | none => return .inl s!"Weird sort {ℓ} not supported"
    | some 0 => return .inr ()
    | some n => return .inl s!"Sort of level {n} too large"
  -- | .app (.app (.app (.const (``Eq) _) α) a) b => do
  --   match ← inferType α with
  --     | .sort ℓ =>
  --       match ℓ.toNat with
  --         | none => return .inl s!"Weird sort {ℓ} not supported"
  --         | some 0 => return .inr false
  --         | some 1 => return .inr ()
  --         | some _ =>
  --           let ac ← checkInFragmentPre a
  --           let bc ← checkInFragmentPre b
  --           match ← checkInFragmentPre α with
  --             | .inl sα => match ac with
  --               | .inl sa => match bc with
  --                 | .inl sb => return .inl s!"Eq[{sα}, {sa}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{sα}, {sa}, {b} is {bb}]"
  --               | .inr ba => match bc with
  --                 | .inl sb => return .inl s!"Eq[{sα}, {a} is {ba}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{sα}, {a} is {ba}, {b} is {bb}]"
  --             | .inr bα => match ac with
  --               | .inl sa => match bc with
  --                 | .inl sb => return .inl s!"Eq[{α} is {bα}, {sa}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{α} is {bα}, {sa}, {b} is {bb}]"
  --               | .inr ba => match bc with
  --                 | .inl sb => return .inl s!"Eq[{α} is {bα}, {a} is {ba}, {sb}]"
  --                 | .inr bb => return .inr (bα && ba && bb)
  --     | _ =>
  --           let ac ← checkInFragmentPre a
  --           let bc ← checkInFragmentPre b
  --           match ← checkInFragmentPre α with
  --             | .inl sα => match ac with
  --               | .inl sa => match bc with
  --                 | .inl sb => return .inl s!"Eq[{sα}, {sa}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{sα}, {sa}, {b} is {bb}]"
  --               | .inr ba => match bc with
  --                 | .inl sb => return .inl s!"Eq[{sα}, {a} is {ba}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{sα}, {a} is {ba}, {b} is {bb}]"
  --             | .inr bα => match ac with
  --               | .inl sa => match bc with
  --                 | .inl sb => return .inl s!"Eq[{α} is {bα}, {sa}, {sb}]"
  --                 | .inr bb => return .inl s!"Eq[{α} is {bα}, {sa}, {b} is {bb}]"
  --               | .inr ba => match bc with
  --                 | .inl sb => return .inl s!"Eq[{α} is {bα}, {a} is {ba}, {sb}]"
  --                 | .inr bb => return .inr (bα && ba && bb)
  | .app e1 e2 => do
    let e1c ← checkInFragmentPre e1
    let e2c ← checkInFragmentPre e2
    match e1c with
      | .inl s => match e2c with
        | .inl s' => return .inl s!"App[{s}, {s'}]"
        | .inr _ => return .inl s!"App[{s}, {e2} is true]"
      | .inr _ => match e2c with
        | .inl s => return .inl s!"App[{e1} is true, {s}]"
        | .inr _ => return .inr ()
  | .lam x α e b => do
    let ety ← withLocalDecl x b α fun fvar =>
      inferType (e.instantiate1 fvar)
    let βty ← inferType ety
    let αty ← inferType α
    let αtr ← checkInFragmentPre α
    let etr ← withLocalDecl x b α fun fvar =>
      checkInFragmentPre (e.instantiate1 fvar)
    match αtr with
      | .inl s => match etr with
        | .inl s' => return .inl s!"λ[{s}, {s'}]"
        | .inr _ => return .inl s!"λ[{s}, {e} is true]"
      | .inr _ => match etr with
        | .inl s => return .inl s!"λ[{α} is true, {s}]"
        | .inr _ =>
          let ret : Bool :=
            -- b -- α translatable
            -- && b' -- e translatable
            (βty.equal (.sort 0)
              || (βty.equal (.sort 1)
                && (αty.equal (.sort 0)
                  || αty.equal (.sort 1)))) -- type of type of lambda expression is not U_2
            && (αty.equal (.sort 1)
              || αty.equal (.sort 2)) -- α not of type Prop
            if ret
              then return .inr ()
              else return .inl s!"{αty} and {βty} are not correct sorts regarding lambdas"
  | .forallE x α β b => do
    let αty ← inferType α
    let ty ← inferType (.forallE x α β b)
    let αtr ← checkInFragmentPre α
    let βtr ← withLocalDecl x b α fun fvar =>
      checkInFragmentPre (β.instantiate1 fvar)
    match αtr with
      | .inl s => match βtr with
        | .inl s' => return .inl s!"∀[{s}, {s'}]"
        | .inr _ => return .inl s!"∀[{s}, {β} is true]"
      | .inr _ => match βtr with
        | .inl s => return .inl s!"∀[{α} is true, {s}]"
        | .inr _ =>
          let ret : Bool :=
            -- b -- α translatable
            -- && b' -- β translatable
            (ty.equal (.sort 0)
              || ty.equal (.sort 1)) -- ∀ x : α , β not of type U_2
            && ((ty.equal (.sort 0)
                && (αty.equal (.sort 0)
                  || αty.equal (.sort 1)
                  || αty.equal (.sort 2)))
              || (ty.equal (.sort 1)
                || ty.equal (.sort 2))) -- If ∀ x : α , β : Prop, then not α of type Prop
            if ret
              then return .inr ()
              else return .inl s!"{ty} and {αty} are not correct sorts regarding functiontypes"
  | (proj _ _ _) => return .inl "proj not supported"
  | (mdata _ e) => checkInFragmentPre e
  | (letE x α t e _) => do
    let αtr ← checkInFragmentPre α
    let ttr ← checkInFragmentPre t
    let etr ← withLocalDecl x .default α fun fvar =>
      checkInFragmentPre (e.instantiate1 fvar)
    match αtr with
    | .inl s1 =>
      match ttr with
      | .inl s2 =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{s1}, {s2}, {s3}]"
        | .inr _ =>
          return .inl s!"Let[{s1}, {s2}, {e} is true]"
      | .inr _ =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{s1}, {t} is true, {s3}]"
        | .inr _ =>
          return .inl s!"Let[{s1}, {t} is true, {e} is true]"
    | .inr _ =>
      match ttr with
      | .inl s2 =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{α} is true, {s2}, {s3}]"
        | .inr _ =>
          return .inl s!"Let[{α} is true, {s2}, {e} is true]"
      | .inr _ =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{α} is true, {t} is true, {s3}]"
        | .inr _ =>
          return .inr ()
--  decreasing_by
--    · grind
--    · grind
--    · grind
--    · sorry
--    · grind
--    · sorry

partial def checkInFragmentPreCtx : Expr → MetaM (String ⊕ Unit)
  | .forallE x (.sort ℓ) β b =>
    match ℓ.toNat with
    | none => return .inl s!"Weird sort {ℓ} not supported"
    | some 0 => withLocalDecl x b (.sort 0) fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
    | some 1 => withLocalDecl x b (.sort 1) fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
    | some n => return .inl s!"Sort of level {n} too large"
  | .forallE x α β b => do
    match (← checkInFragmentPre α) with
    | .inl s =>
      return .inl s
    | .inr () => withLocalDecl x b α fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
  | _ => return .inr ()

partial def checkInFragmentPreSig (e : Expr) : MetaM (String ⊕ Unit) := do
  match (← checkInFragmentPre e) with
  | .inr _ =>
    return .inr ()
  | .inl _ =>
    checkInFragmentPreSigRest e
  where
    checkInFragmentPreSigRest : Expr → MetaM (String ⊕ Unit)
    | .forallE x (.sort ℓ) β b =>
      match ℓ.toNat with
      | none => return .inl s!"Weird sort {ℓ} not supported"
      | some 0 => withLocalDecl x b (.sort 0) fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
      | some 1 => withLocalDecl x b (.sort 1) fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
      | some n => return .inl s!"Sort of level {n} too large"
    | .forallE x α β b => do
      match (← checkInFragmentPre α) with
      | .inl s =>
        return .inl s
      | .inr _ => withLocalDecl x b α fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
    | .sort ℓ =>
      match ℓ.toNat with
      | none => return .inl s!"Weird sort {ℓ} not supported"
      | some 0 => return .inr ()
      | some 1 => return .inr ()
      | some n => return .inl s!"Sort of level {n} too large"
    | e => checkInFragmentPre e

partial def checkInFragmentPreUnderCtx :
  Expr → MetaM (String ⊕ Unit)
  | .forallE x α β b => withLocalDecl x b α fun fvar =>
      checkInFragmentPreUnderCtx (β.instantiate1 fvar)
  | e => checkInFragmentPre e

def fetchMathlibTheorems (moduleName : Name) : IO Unit := do
  let env ← Lean.importModules #[{ module := moduleName, importAll := true }] {}
  let some testIdx := env.getModuleIdx? moduleName
    | .throw (.userError s!"{moduleName} not found")
  for (name, info) in env.constants do
    if info matches .thmInfo _ ∧ env.getModuleIdxFor? name == some testIdx then
      let univParams := info.levelParams
      let concreteLevels := List.replicate univParams.length (Lean.Level.ofNat 0)
      let univMonomorphicType := (info.type.instantiateLevelParams univParams concreteLevels)
      let result ←
        (checkInFragmentPre univMonomorphicType).run {}
        |>.run { fileName := "", fileMap := default } {env := env}
        |>.toIO'
      match result with
        | .error e =>
          let str ← e.toMessageData.toString.toIO
          IO.println str
        | .ok ((res, _), _) =>
          match res with
            | .inl s =>
              IO.println s!"{name} has error {s}"
            | .inr b =>
              IO.println s!"{name} is {b}"

partial def splitIntros (e : Expr) : ((List (Name × Expr × BinderInfo)) × Expr) :=
  splitIntrosImpl e []
  where
    splitIntrosImpl :
      Expr → List (Name × Expr × BinderInfo) → ((List (Name × Expr × BinderInfo)) × Expr)
    | .forallE x α β b, xs => splitIntrosImpl β ((x,α,b) :: xs)
    | e, xs =>
      (xs, e)

def fetchMathlibTheorems' (moduleName : Name) (logFile : String) (resultFile : String) : MetaM Unit := do
  let logFileHandle? : IO.FS.Handle ← IO.FS.Handle.mk logFile .write
  let resultFileHandle? : IO.FS.Handle ← IO.FS.Handle.mk resultFile .write
  logFileHandle?.putStrLn s!"Start time : {← Std.Time.Timestamp.now}"
  logFileHandle?.putStrLn s!"Eval Module : {moduleName}"
  logFileHandle?.flush
  let infos ← allHumanTheoremsFromPackage moduleName
  for (info, tys) in infos do
    let mut signature := List.map (Lean.ToExpr.toExpr) info.type.getUsedConstants.toList
    let mut tyExprs := (tys.map (fun i => i.type)).toList
    let univParams := info.levelParams
    let concreteLevels := List.replicate univParams.length (Lean.Level.ofNat 0)
    let univMonomorphicType := (info.type.instantiateLevelParams univParams concreteLevels)
    let ctxResult ← checkInFragmentPreCtx univMonomorphicType
    let result ← checkInFragmentPreUnderCtx univMonomorphicType
    let mut tyLogs := #[]
    let mut sigBool := true
    let mut reasons := #[]
    for ty in tys do
      let univParamsTy := ty.levelParams
      let concreteLevelsTy := List.replicate univParamsTy.length (Lean.Level.ofNat 0)
      let univMonomorphicType := (ty.type.instantiateLevelParams univParamsTy concreteLevelsTy)
      let sigRes ← checkInFragmentPreSig univMonomorphicType
      match sigRes with
        | .inl s =>
          tyLogs := tyLogs.append #[s!"{ty.name} has error {s}"]
          sigBool := false
          reasons := reasons.append #[s!"{ty.name}"]
        | .inr _ =>
          tyLogs := tyLogs.append #[s!"{ty.name} is true"]
      if ty.isInductive then
        let recName := (ty.name.append `rec)
        let .some tyRec := (← getEnv).find? recName
          | throwError "Name.isTheorem :: Cannot find name {recName}"
        signature := Expr.const tyRec.name [] :: signature
        tyExprs := tyRec.type :: tyExprs
        let univParamsRec := tyRec.levelParams
        let concreteLevelsRec := List.replicate univParamsRec.length (Lean.Level.ofNat 0)
        let univMonomorphicTypeRec :=
          (tyRec.type.instantiateLevelParams univParamsRec concreteLevelsRec)
        let recRes ← checkInFragmentPreSig univMonomorphicTypeRec
        match recRes with
          | .inl s =>
            tyLogs := tyLogs.append #[s!"{tyRec.name} has error {s}"]
            reasons := reasons.append #[s!"{ty.name}"]
            sigBool := false
          | .inr _ =>
            tyLogs := tyLogs.append #[s!"{tyRec.name} is true"]
    match ctxResult, result with
      | .inl s, .inl s' =>
        logFileHandle?.putStrLn s!"{info.name} has error {s} in context and error {s'} in body \
          and has signature {signature} with types {tyExprs} where {tyLogs}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false, signature : {sigBool} {reasons}"
        resultFileHandle?.flush
      | .inl s, .inr _ =>
        logFileHandle?.putStrLn s!"{info.name} has error {s} in context, body is true \
          and has signature {signature} with types {tyExprs} where {tyLogs}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false, signature : {sigBool} {reasons}"
        resultFileHandle?.flush
      | .inr _, .inl s =>
        logFileHandle?.putStrLn s!"{info.name}'s context is true and has error {s} in body \
          and has signature {signature} with types {tyExprs} where {tyLogs}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false, signature : {sigBool} {reasons}"
        resultFileHandle?.flush
      | .inr _, .inr _ =>
        logFileHandle?.putStrLn s!"{info.name} : {univMonomorphicType} is true ⊢ true \
          and has signature {signature} with types {tyExprs} where {tyLogs}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : true, signature : {sigBool} {reasons}"
        resultFileHandle?.flush

end EvalFragment
