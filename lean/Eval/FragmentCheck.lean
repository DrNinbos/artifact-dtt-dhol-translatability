import Lean.Environment
import Lean.CoreM
import Lean.Meta.Basic
import Lean.ProjFns
import Lean.Server.Utils
import Std.Time.DateTime.Timestamp

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

partial def checkInFragmentPre : Expr → MetaM (String ⊕ Bool)
  | .const _ _ => return Sum.inr true
  | .bvar _ => return Sum.inr true
  | .fvar _ => return Sum.inr true
  | .mvar _ => return Sum.inr true
  | .lit _ => return .inr true
  | .sort ℓ => match ℓ.toNat with
    | none => return .inl s!"Weird sort {ℓ} not supported"
    | some 0 => return .inr true
    | some _ => return .inr false
  | .app e1 e2 => do
    let e1c ← checkInFragmentPre e1
    let e2c ← checkInFragmentPre e2
    match e1c with
      | .inl s => match e2c with
        | .inl s' => return .inl s!"App[{s}, {s'}]"
        | .inr b => return .inl s!"App[{s}, {e2} is {b}]"
      | .inr b => match e2c with
        | .inl s => return .inl s!"App[{e1} is {b}, {s}]"
        | .inr b' => return .inr (b && b')
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
        | .inr b => return .inl s!"λ[{s}, {e} is {b}]"
      | .inr b => match etr with
        | .inl s => return .inl s!"λ[{α} is {b}, {s}]"
        | .inr b' =>
          let ret : Bool :=
            b -- α translatable
            && b' -- e translatable
            && (βty.equal (.sort 0)
              || (βty.equal (.sort 1)
                && (αty.equal (.sort 0)
                  || αty.equal (.sort 1)))) -- type of type of lambda expression is not U_2
            && (αty.equal (.sort 1)
              || αty.equal (.sort 2)) -- α not of type Propreturn .inr (b && b')
            return .inr ret
  | .forallE x α β b => do
    let αty ← inferType α
    let ty ← inferType (.forallE x α β b)
    let αtr ← checkInFragmentPre α
    let βtr ← withLocalDecl x b α fun fvar =>
      checkInFragmentPre (β.instantiate1 fvar)
    match αtr with
      | .inl s => match βtr with
        | .inl s' => return .inl s!"∀[{s}, {s'}]"
        | .inr b => return .inl s!"∀[{s}, {β} is {b}]"
      | .inr b => match βtr with
        | .inl s => return .inl s!"∀[{α} is {b}, {s}]"
        | .inr b' =>
          let ret : Bool :=
            b -- α translatable
            && b' -- β translatable
            && (ty.equal (.sort 0)
              || ty.equal (.sort 1)) -- ∀ x : α , β not of type U_2
            && ((ty.equal (.sort 0)
                && (αty.equal (.sort 0)
                  || αty.equal (.sort 1)
                  || αty.equal (.sort 2)))
              || (ty.equal (.sort 1)
                || ty.equal (.sort 2))) -- If ∀ x : α , β : Prop, then not α of type Prop
            return .inr ret
  | (proj _ _ _) => return .inl "proj not supported"
  | (mdata (KVMap.mk _) _) => return .inl "mdata not supported"
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
        | .inr b3 =>
          return .inl s!"Let[{s1}, {s2}, {e} is {b3}]"
      | .inr b2 =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{s1}, {t} is {b2}, {s3}]"
        | .inr b3 =>
          return .inl s!"Let[{s1}, {t} is {b2}, {e} is {b3}]"
    | .inr b1 =>
      match ttr with
      | .inl s2 =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{α} is {b1}, {s2}, {s3}]"
        | .inr b3 =>
          return .inl s!"Let[{α} is {b1}, {s2}, {e} is {b3}]"
      | .inr b2 =>
        match etr with
        | .inl s3 =>
          return .inl s!"Let[{α} is {b1}, {t} is {b2}, {s3}]"
        | .inr b3 =>
          return .inr (b1 && b2 && b3)
--  decreasing_by
--    · grind
--    · grind
--    · grind
--    · sorry
--    · grind
--    · sorry

partial def checkInFragmentPreCtx : Expr → MetaM (String ⊕ Bool)
  | .forallE x (.sort ℓ) β b =>
    match ℓ.toNat with
    | none => return .inl s!"Weird sort {ℓ} not supported"
    | some 0 => withLocalDecl x b (.sort 0) fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
    | some 1 => withLocalDecl x b (.sort 1) fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
    | some _ => return .inr false
  | .forallE x α β b => do
    match (← checkInFragmentPre α) with
    | .inl s =>
      return .inl s
    | .inr false =>
      return .inr false
    | .inr true => withLocalDecl x b α fun fvar =>
      checkInFragmentPreCtx (β.instantiate1 fvar)
  | _ => return .inr true

partial def checkInFragmentPreSig (e : Expr) : MetaM (String ⊕ Bool) := do
  match (← checkInFragmentPre e) with
  | .inl s =>
    return .inl s
  | .inr true =>
    return .inr true
  | .inr false =>
    checkInFragmentPreSigRest e
  where
    checkInFragmentPreSigRest : Expr → MetaM (String ⊕ Bool)
    | .forallE x (.sort ℓ) β b =>
      match ℓ.toNat with
      | none => return .inl s!"Weird sort {ℓ} not supported"
      | some 0 => withLocalDecl x b (.sort 0) fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
      | some 1 => withLocalDecl x b (.sort 1) fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
      | some _ => return .inr false
    | .forallE x α β b => do
      match (← checkInFragmentPre α) with
      | .inl s =>
        return .inl s
      | .inr false =>
        return .inr false
      | .inr true => withLocalDecl x b α fun fvar =>
        checkInFragmentPreSigRest (β.instantiate1 fvar)
    | .sort ℓ =>
      match ℓ.toNat with
      | none => return .inl s!"Weird sort {ℓ} not supported"
      | some 0 => return .inr true
      | some 1 => return .inr true
      | some _ => return .inr false
    | e => checkInFragmentPre e

partial def checkInFragmentPreUnderCtx :
  Expr → MetaM (String ⊕ Bool)
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
        | .inl s => tyLogs := tyLogs.append #[s!"{ty.name} has error {s}"]
        | .inr b =>
          tyLogs := tyLogs.append #[s!"{ty.name} is {b}"]
          sigBool := sigBool && b
          if !b then
            reasons := reasons.append #[s!"{ty.name}"]
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
          | .inl s => tyLogs := tyLogs.append #[s!"{tyRec.name} has error {s}"]
          | .inr b =>
            tyLogs := tyLogs.append #[s!"{tyRec.name} is {b}"]
            sigBool := sigBool && b
    match ctxResult, result with
      | .inl s, .inl s' =>
        logFileHandle?.putStrLn s!"{info.name} has error {s} in context and error {s'} in body"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false"
        resultFileHandle?.flush
      | .inl s, .inr b =>
        logFileHandle?.putStrLn s!"{info.name} has error {s} in context, body is {b}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false"
        resultFileHandle?.flush
      | .inr b, .inl s =>
        logFileHandle?.putStrLn s!"{info.name}'s context is {b} and has error {s} in body"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : false"
        resultFileHandle?.flush
      | .inr b, .inr b' =>
        logFileHandle?.putStrLn s!"{info.name} : {univMonomorphicType} is {b} ⊢ {b'} \
          and has signature {signature} with types {tyExprs} where {tyLogs}"
        logFileHandle?.flush
        resultFileHandle?.putStrLn s!"{info.name} : {b && b'}, signature : {sigBool} {reasons}"
        resultFileHandle?.flush

end EvalFragment
