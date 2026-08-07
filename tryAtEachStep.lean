/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Lean

/-!
Tool to try running a tactic (like `exact?` or `rw_search`) at every
proof step in a given file.
-/

open Lean Elab System


/--
Like `Lean.Elab.ContextInfo.runCoreM`, but forwards the filemap.
-/
def Lean.Elab.ContextInfo.runCoreM' {α : Type} (info : ContextInfo) (x : CoreM α) : IO α := do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and `FVarId`s that
    have been used in `lctx` and `info.mctx`.
  -/
  (·.1) <$>
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := "<InfoTree>", fileMap := info.fileMap }
      { env, ngen := info.ngen }

/--
Like `Lean.Elab.ContextInfo.runMetaM`, but forwards the filemap.
-/
def Lean.Elab.ContextInfo.runMetaM' {α : Type}
    (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : IO α := do
  (·.1) <$> info.runCoreM' (x.run { lctx := lctx } { mctx := info.mctx })


namespace Lean.Elab.TacticInfo

-- We borrow some stuff from
-- https://github.com/semorrison/lean-training-data/blob/master/TrainingData/InfoTree/Basic.lean
-- and
-- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

/-- Find the name for the outermost `Syntax` in this `TacticInfo`. -/
def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none


/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Tactic.inductionAlt => false
  | some ``Lean.Parser.Tactic.case => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.tacticSeqBracketed => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | _ => true

end Lean.Elab.TacticInfo

namespace TryAtEachStep

structure Config where
  help : Bool := false
  tac : String := "exact?"
  infile : FilePath := "."
  outfile : Option FilePath := .none
  summaryfile : Option FilePath := .none
  doneIfOutfileAlreadyExists : Bool := false
  additionalImports : List String := []
  additionalDynlibs : List FilePath := []

instance : Lean.ToJson String.Pos.Raw where
  toJson x := x.1

structure Span where
  startPos: String.Pos.Raw
  endPos: String.Pos.Raw
deriving BEq, Hashable, Lean.ToJson

instance : Ord Span where
 compare sp1 sp2 := match sp1, sp2 with
 | ⟨s1, e1⟩, ⟨s2, e2⟩ =>
   match Ord.compare s1.1 s2.1 with
   | .lt => .lt
   | .gt => .gt
   | .eq =>
     -- we want bigger spans to come first
     match Ord.compare e1.1 e2.1 with
     | .lt => .gt
     | .gt => .lt
     | .eq => .eq

def Span.ofSyntax (stx: Syntax) : Option Span := do
  -- On seq nodes, canonicalOnly := true sometimes gives us `none`.
  let startPos ← stx.getPos? (canonicalOnly := false)

  -- We set canonicalOnly := true here to get the full extent of seq nodes. Otherwise
  -- sometimes we only get `by` without the body.
  let endPos ← stx.getTailPos? (canonicalOnly := true)
  return ⟨startPos, endPos⟩

/-- An individual execution of a tactic. -/
structure FocusedStep where
  ci: ContextInfo
  ti: TacticInfo

/--
A textual tactic step in a proof. May represent multiple actual
executions of the tactic, e.g. after `all_goals` or `<;>`.
-/
structure Step where
  /-- environment from before the current command -/
  env: Environment

  stx: Syntax

  /-- Syntax of the enclosing tacticSeq1Indented or tacticSeqBracketed node,
      if there is one. -/
  seqStx : Option Syntax

  focused_steps: List FocusedStep

abbrev StepMap := RBMap Span Step Ord.compare
abbrev SpanSet := RBMap Span Unit Ord.compare

def StepMap.empty : StepMap := RBMap.empty

def StepMap.maybe_add (sm : StepMap) (env : Environment)
    (ci : ContextInfo) (ti : TacticInfo) (seqStx : Option Syntax) : StepMap := Id.run do
  let some span := Span.ofSyntax ti.stx | return sm
  let fs : FocusedStep := ⟨ci, ti⟩
  match sm.find? span with
  | some step =>
    let step' := {step with focused_steps := step.focused_steps ++ [fs]}
    return sm.insert span step'
  | none => return sm.insert span {
      env
      stx := ti.stx
      seqStx := seqStx
      focused_steps := [fs]
    }

def visitTacticInfo (env : Environment) (ci : ContextInfo)
    (ti : TacticInfo) (seqStx : Option Syntax) (step_map: StepMap) :
    StepMap := Id.run do
  if not ti.isSubstantive then return step_map
  if let .some (.synthetic ..) := ti.stx.getHeadInfo? then
     -- Not actual concrete syntax the user wrote. Ignore.
     return step_map
  return StepMap.maybe_add step_map env ci ti seqStx

def visitInfo (env : Environment) (ci : ContextInfo)
    (info : Info) (seqStx : Option Syntax) (step_map : StepMap)
    : StepMap :=
  match info with
  | .ofTacticInfo ti => visitTacticInfo env ci ti seqStx step_map
  | _ => step_map

partial def InfoTree.foldInfo' {α : Type} (f : ContextInfo → Info → (Option Syntax) → α → α)
    (init : α) : InfoTree → α :=
  go none none init
where go ctx? seqStx a
  | .context ctx t => go (ctx.mergeIntoOuter? ctx?) seqStx a t
  | .node i ts =>
    let a := match ctx? with
      | none => a
      | some ctx => f ctx i seqStx a
    let newSeqStx : Option Syntax := match i with
    | .ofTacticInfo ti =>
      match ti.name? with
      | some ``Lean.Parser.Tactic.tacticSeq1Indented => ti.stx
      | some ``Lean.Parser.Tactic.tacticSeqBracketed => ti.stx
      | _ => seqStx
    | _ => seqStx
    ts.foldl (init := a) (go (i.updateContext? ctx?) newSeqStx)
  | .hole _ => a

/-- Collect the tactic steps recorded in the info trees of a single command. -/
def traverseTrees (env : Environment) (infoState : InfoState) : StepMap := Id.run do
  let mut step_map := StepMap.empty
  for t in infoState.trees.toList do
    step_map := InfoTree.foldInfo' (visitInfo env) step_map t
  return step_map

/-- The result of trying a new tactic at a tactic step.
-/
structure TryTacticResult where
  filepath : String

  /-- The position in the file where the tactic step occurs. -/
  startLine : Nat
  startCol : Nat

  /-- The original tactic syntax as a string. -/
  oldText : String

  /-- The name of the declaration that is being elaborated. -/
  parentName : String

  /-- True if the goal is a proposition. -/
  goalIsProp : Bool

  /-- The number of steps the proof is shortened by. -/
  shortenedStepsCount: Nat := 0

  /-- Whether the tactic succeeded at closing the goal -/
  tacticSucceeded : Bool

  /-- Message logged by the new tactic (e.g. 'try this ...'). -/
  message : Option String
deriving Lean.ToJson, Inhabited

def stringOfTerm (e : Expr) (mctx : MetavarContext) (g : MVarId) : CoreM String := do
  let mnd : MetaM String := g.withContext do
        let pe ← PrettyPrinter.ppExpr e
        return Std.Format.pretty pe
  let (s, _) ← mnd.run {} { mctx := mctx }
  return s

/-- Returns true if the goal has unassigned mvars in its hypothesis or its target type. -/
def hasUnassignedMVars (mctx : MetavarContext) (g : MVarId) : MetaM Bool := do
  let go : MetaM Bool := g.withContext  do
    let a ← Lean.Meta.getMVars (← g.getType)
    if a.size > 0 then
      return true
    for d in ← getLCtx do
      if !d.isImplementationDetail then
        let a ← Lean.Meta.getMVars d.type
        if a.size > 0 then
          return true
    return false
  let (b, _) ← go.run {} { mctx := mctx }
  return b

def tryTactic (config : Config) (tryTacticStx : Syntax) (span : Span) (step : Step) :
    IO (Option TryTacticResult) := do
  -- For now, we ignore cases where a tactic applies to multiple goals simultaneously.
  let [{ci, ti}] := step.focused_steps | do IO.eprint "_"; return none

  let some parentName := ci.parentDecl? | return none

  ci.runMetaM' default do

  setEnv step.env
  let src := ci.fileMap.source

  let startPosition := ci.fileMap.toPosition span.startPos
  let s := Substring.Raw.mk src span.startPos span.endPos
  let [g] := ti.goalsBefore | return none
  if ← hasUnassignedMVars ti.mctxBefore g then return none

  let mut newResult : Option TryTacticResult := .none
  IO.eprint "."
  (← IO.getStderr).flush
  let mctx := ti.mctxBefore
  let goalIsProp : MetaM Bool := do
     g.withContext do
     try
       let ty ← g.getType
       let ty ← instantiateMVars ty
       Meta.isProp ty
     catch _ =>
       return false
  let goalIsProp ← goalIsProp.run' (s := { mctx := mctx })
  let oldText := s!"{s}"
  let mkResult (tacticSucceeded : Bool) (message : Option String) : TryTacticResult := {
    filepath := config.infile.toString
    parentName := parentName.toString
    goalIsProp
    startLine := startPosition.line
    startCol := startPosition.column
    oldText
    tacticSucceeded
    message
  }
  let dotac := Term.TermElabM.run' (ctx := {declName? := ci.parentDecl?})
                    <| Tactic.run g (Tactic.evalTactic tryTacticStx)
  let (mvars, _after_state) ← try
      dotac.run {} { mctx := mctx }
     catch _e =>
      --println! "caught: {←e.toMessageData.toString}"
      return some (mkResult false none)
  let msgs := (← liftM (m := CoreM) get).messages
  if msgs.hasErrors then
    IO.eprint "X"
    return some (mkResult false none)

  if mvars.length == 0 then
    IO.eprintln s!"\nline {startPosition.line}, col {startPosition.column}:\n{s}"
    let mut message := ""
    for msg in msgs.toList do
      IO.eprintln s!"* {←msg.data.toString}"
      message := message ++ s!"{←msg.data.toString}"
    let fewerSteps := 0 < ti.goalsAfter.length
    if fewerSteps then
      IO.eprintln "shortened proof!"

    newResult := mkResult true (some message)
  else
    newResult := mkResult false none
  let traceState := (← liftM (m := CoreM) get).traceState
  for t in traceState.traces.toList do
    IO.eprintln s!"> {←t.msg.toString}"

  return newResult

/--
Process the commands of the file one at a time, calling `handleCommand` on
each command's `InfoState` (paired with the environment from before the
command) as soon as that command has been elaborated.

Handling each command's info trees immediately — instead of accumulating the
info trees of the whole file and only acting on them at the end — means that
at most one command's elaboration data needs to be retained at a time. On
large files, accumulating everything at once can exhaust memory and cause the
process to be OOM-killed.
-/
partial def processCommands (handleCommand : Environment → InfoState → IO Unit) :
    Frontend.FrontendM Unit := do
  let env := (←get).commandState.env
  let done ← Frontend.processCommand
  let st := ← get
  let infoState := st.commandState.infoState
  set {st with commandState := {st.commandState with infoState := {}}}
  handleCommand env infoState
  if !done then
    processCommands handleCommand

def parseTactic (env : Environment) (str : String) : IO Syntax := do
  let inputCtx := Parser.mkInputContext str "<argument>"
  let tokens := Parser.Module.updateTokens (Parser.getTokenTable env)
  let s := Parser.tacticParser.fn.run
              inputCtx {env := env, options := {}} tokens (Parser.mkParserState inputCtx.inputString)
  match s.errorMsg with
  | some errorMsg =>
    IO.eprintln s!"failed to parse {str}: {errorMsg}"
    panic! "parse error"
  | none =>
    pure (if s.stxStack.isEmpty then .missing else s.stxStack.back)

def tryTacticAtSteps (config : Config) (tryTacticStx : Syntax) (step_map : StepMap) :
    IO (List TryTacticResult) := do
  let mut resultsDict := Std.HashMap.emptyWithCapacity 300
  let mut failures : List TryTacticResult := []
  for (span, step) in step_map do
    let seqSpan := if let .some seqStx := step.seqStx
                   then Span.ofSyntax seqStx
                   else none

    if let .some sp := seqSpan
    then
      -- Determine whether we've already proven a branch that subsumes this one.
      -- TODO: do this in a more efficient way.
      let mut skipThisOne := false
      for k in resultsDict.keys do
        if k.startPos ≤ sp.startPos ∧ sp.endPos ≤ k.endPos then
          resultsDict := resultsDict.insert k
            {(resultsDict.get! k) with
            shortenedStepsCount := (resultsDict.get! k).shortenedStepsCount + 1 }
          skipThisOne := true
          -- keep going to count, even if we already determined to skip this one
      if skipThisOne then
        continue -- we've already proved this branch

    try
      if let .some res ← tryTactic config tryTacticStx span step then
         if !res.tacticSucceeded then
           -- Failures must not enter `resultsDict`: entries there mark branches as
           -- already proved, which would skip the remaining steps of the branch.
           failures := res :: failures
         else if let .some sp := seqSpan then
           resultsDict := resultsDict.insert sp {res with shortenedStepsCount := 0}
         else
           IO.eprintln "WARNING: no seqSpan; failed to record result"

    catch e =>
      IO.eprintln s!"{e}"

  return resultsDict.values ++ failures.reverse


/--
Add imports to the end of header to ensure they come after the `module` and `prelude` keywords.
-/
def addImports (input : String) (bodyStart : String.Pos.Raw) (imports : List String) : String :=
  let header := String.Pos.Raw.extract input ⟨0⟩ bodyStart
  let body := String.Pos.Raw.extract input bodyStart input.rawEndPos
  header ++ String.join (imports.map (fun im => s!"import {im}\n")) ++ body

/--
If we are inside a Lake workspace, ask Lake for the file's setup (via `lake setup-file`, like the
language server does) and load the dynlibs of precompiled dependencies into this process.
Without this, tactics backed by FFI code (e.g. `hammer`, whose cvc5 bindings are `@[extern]`
declarations living in precompiled shared libraries) fail in the interpreter because their
native implementations were never loaded.

Returns the `ModuleSetup` when Lake provided one; `none` when running outside a Lake workspace.
-/
def runLakeSetup (config : Config) (input : String) (header : Elab.HeaderSyntax)
    (mainModuleName : Name) : IO (Option ModuleSetup) := do
  let docMeta : Server.DocumentMeta := {
    uri := System.Uri.pathToUri config.infile
    mod := mainModuleName
    version := 0
    text := FileMap.ofString input
    dependencyBuildMode := .always
  }
  let result ← Server.FileWorker.setupFile docMeta header.toModuleHeader
    (fun line => IO.eprint line)
  match result with
  | .success setup => return some setup
  | .noLakefile => return none
  | .importsOutOfDate =>
    throw $ IO.userError "`lake setup-file` reports imports are out of date; try `lake build` first"
  | .error msg =>
    throw $ IO.userError s!"`lake setup-file` failed:\n{msg}"

/--
Write `results` as JSON to `outfile` (if provided), and write summary
statistics to the summary file (if provided).
-/
def writeResults (outfile : Option FilePath) (summaryfile : Option FilePath)
    (results : Array TryTacticResult) : IO Unit := do
  if let .some outfile := outfile then
    IO.FS.writeFile outfile s!"{Lean.toJson results}\n"
  if let .some summaryfile := summaryfile then
    let successCount := (results.filter (fun x => x.tacticSucceeded)).size
    IO.FS.writeFile summaryfile <|
      s!"Total number of results: {results.size}\n" ++
      s!"Total number of successes: {successCount}\n"

unsafe def processFile (config : Config) : IO Unit := do
  if let .some outfile := config.outfile then
    if (← outfile.pathExists) ∧ config.doneIfOutfileAlreadyExists then
      IO.eprintln s!"Already done because outfile {outfile} already exists."
      return ()

  initSearchPath (← findSysroot)
  for dynlib in config.additionalDynlibs do
    Lean.loadDynlib dynlib
  let mut input ← IO.FS.readFile config.infile
  unless config.additionalImports.isEmpty do
    let preCtx := Parser.mkInputContext input config.infile.toString
    let (_, preState, _) ← Parser.parseHeader preCtx
    input := addImports input preState.pos config.additionalImports
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input config.infile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let mainModuleName ← moduleNameOfFileName config.infile none

  let setup? ← runLakeSetup config input header mainModuleName
  let plugins := (setup?.map (·.plugins)).getD #[]

  let (env, messages) ← processHeader header {} messages inputCtx (plugins := plugins)

  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        IO.eprintln s!"ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"

  let tryTacticStx ← parseTactic env config.tac

  let env := env.setMainModule mainModuleName
  let baseOpts := (setup?.map (·.options.toOptions)).getD {}
  -- let opts : Options := baseOpts.insert `maxHeartbeats (DataValue.ofNat 1000000)
  let opts := baseOpts -- Increasing maxHeartbeats would lead to an unfairly generous evaluation
  let commandState := { Command.mkState env messages opts with infoState.enabled := true }

  -- While the run is in progress, results are flushed to `<outfile>.partial`
  -- after each command, so that partial results survive if the process dies
  -- before finishing (e.g. gets OOM-killed). Only a completed run writes
  -- `outfile` itself, which keeps `--done-if-outfile-already-exists` sound.
  let partialFile := config.outfile.map (·.addExtension "partial")
  let resultsRef ← IO.mkRef (#[] : Array TryTacticResult)
  let handleCommand (env : Environment) (infoState : InfoState) : IO Unit := do
    let stepMap := traverseTrees env infoState
    if stepMap.isEmpty then return ()
    let newResults ← tryTacticAtSteps config tryTacticStx stepMap
    if newResults.isEmpty then return ()
    let results := (← resultsRef.get) ++ newResults.toArray
    resultsRef.set results
    writeResults partialFile config.summaryfile results

  let ((), _frontendState) ← ((processCommands handleCommand).run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }

  writeResults config.outfile config.summaryfile (← resultsRef.get)
  if let .some partialFile := partialFile then
    if ← partialFile.pathExists then
      IO.FS.removeFile partialFile
  pure ()

def pathOfProbId (probId : String) : IO FilePath := do
  let path := FilePath.mk ("./Compfiles/" ++ probId ++ ".lean")
  let cwd ← IO.currentDir
  pure $ cwd / path

/--
Convert the path `path` to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path


def parseArgs (args : Array String) : IO Config := do
  let mut cfg : Config := {}
  let mut idx := 0
  let mut positional_count := 0
  while idx < args.size do
    if args[idx]! == "--help"
    then
      return {cfg with help := true}
    else if args[idx]! == "--imports"
    then
      idx := idx + 1
      let imports := args[idx]!.splitOn ","
      cfg := {cfg with additionalImports := imports}
    else if args[idx]! == "--load-dynlib"
    then
      idx := idx + 1
      cfg := {cfg with additionalDynlibs := cfg.additionalDynlibs ++ [⟨args[idx]!⟩]}
    else if args[idx]! == "--outfile"
    then
      idx := idx + 1
      cfg := {cfg with outfile := args[idx]!}
    else if args[idx]! == "--summaryfile"
    then
      idx := idx + 1
      cfg := {cfg with summaryfile := args[idx]!}
    else if args[idx]! == "--done-if-outfile-already-exists"
    then
      idx := idx + 1
      let v ← match args[idx]! with
      | "true" => pure true
      | "false" => pure false
      | _ => throw $ IO.userError s!"failed to parse bool from {args[idx]!}"
      cfg := {cfg with doneIfOutfileAlreadyExists := v}
    else if positional_count == 0
    then
      let tac := args[idx]!
      cfg := {cfg with tac := tac}
      positional_count := positional_count + 1
    else if positional_count == 1
    then
      let infile := (← toAbsolute ⟨args[idx]!⟩)
      cfg := {cfg with infile := infile}
      positional_count := positional_count + 1
    else
      throw $ IO.userError "too many positional arguments!"

    idx := idx + 1
    pure ()

  if positional_count != 2
  then
    throw $ IO.userError "usage: tryAtEachStep [OPTIONS] TACTIC LEAN_FILE"
  return cfg

def helpMessage : String :=
"tryAtEachStep: run a tactic at each proof step in a .lean file

  tryAtEachStep [OPTIONS] TACTIC LEAN_FILE

  Options:
    --outfile OUTFILE                   output JSON file
    --summaryfile SUMMARYFILE           output file for summary statistics
                                        (number of successes and total attempts)
    --done-if-outfile-already-exists    exit early if outfile already exists
    --imports IMPORTS                   inject import statements for modules from this comma-separated list
    --load-dynlib PATH                  load a shared library before processing the file
                                        (may be repeated); inside a Lake workspace the
                                        dynlibs reported by `lake setup-file` are loaded
                                        automatically

"

end TryAtEachStep

unsafe def main (args : List String) : IO Unit := do
  let cfg ← TryAtEachStep.parseArgs args.toArray
  if cfg.help then
    IO.eprintln TryAtEachStep.helpMessage
    return
  -- Exit explicitly instead of returning: after `main` returns, the runtime's
  -- `lean_finalize_task_manager` waits for all outstanding tasks, so any background
  -- task leaked by elaboration or by the tried tactic keeps the process alive.
  try
    TryAtEachStep.processFile cfg
    IO.Process.exit 0
  catch e =>
    IO.eprintln s!"uncaught exception: {e}"
    IO.Process.exit 1
