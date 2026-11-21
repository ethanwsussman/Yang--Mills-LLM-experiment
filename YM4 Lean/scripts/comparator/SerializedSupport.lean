import Lake.Check.Compare
import Lake.Check.Axioms
import LeanExport.Parse
import Lean.Data.Json

/-
Trusted adapter around the shipped upstream comparison and axiom algorithms.
It reads serialized data only. It does not import project modules, replay a
kernel, compile project source, load project oleans, or spawn child processes.
The production Python runner separately binds the scope to the accepted original
canonical dump and the trusted Init supplement; small controls use this same API.
-/
open Lean

namespace SerializedComparison

def fail {α : Type} (s : String) : Except String α := .error s

def taggedName (j : Json) : Except String Name := do
  let mut n := Name.anonymous
  for component in ← j.getArr? do
    let a ← component.getArr?
    if a.size != 2 then fail "Name component must have exactly two entries"
    match ← a[0]!.getStr? with
    | "s" => n := .str n (← a[1]!.getStr?)
    | "n" => n := .num n (← a[1]!.getNat?)
    | _ => fail "Unknown tagged Name component"
  return n

def nameArray (j : Json) (field : String) : Except String (Array Name) := do
  (← (← j.getObjVal? field).getArr?).mapM taggedName

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient_builtin"

def uniqueSet (xs : Array Name) (label : String) : Except String (Std.HashSet Name) := do
  let mut result := {}
  for n in xs do
    if result.contains n then fail s!"Duplicate {label}: {n}"
    result := result.insert n
  return result

structure Scope where
  canonicalNames : Array Name
  allNames : Array Name
  kinds : Std.HashMap Name String
  theoremTargets : Array Name
  roots : Array Name
  primitives : Array Name
  legalAxioms : Array Name

def parseScope (j : Json) : Except String Scope := do
  if (← (← j.getObjVal? "schemaVersion").getNat?) != 1 then fail "Unsupported scope schema"
  let canonical ← (← j.getObjVal? "canonicalDeclarations").getArr?
  let supplement ← (← j.getObjVal? "supplementDeclarations").getArr?
  let mut names := #[]
  let mut kinds : Std.HashMap Name String := {}
  for d in canonical ++ supplement do
    let n ← taggedName (← d.getObjVal? "name")
    let k ← (← d.getObjVal? "kind").getStr?
    if kinds.contains n then fail s!"Duplicate challenge declaration in scope: {n}"
    kinds := kinds.insert n k
    names := names.push n
  let theoremTargets ← nameArray j "theoremTargets"
  let theoremSet ← uniqueSet theoremTargets "theorem target"
  let expectedTheorems := names.filter fun n => kinds[n]? == some "theorem"
  if theoremTargets.size != expectedTheorems.size ||
      !(expectedTheorems.all theoremSet.contains) then
    fail "Theorem targets must be exactly all scoped theorem declarations"
  let roots ← nameArray j "rootTargets"
  let _ ← uniqueSet roots "root"
  if roots.isEmpty || !(roots.all theoremSet.contains) then fail "Roots must be nonempty scoped theorems"
  let primitives ← nameArray j "primitiveTargets"
  let _ ← uniqueSet primitives "primitive"
  for n in primitives do
    if !kinds.contains n then fail s!"Primitive omitted from challenge scope: {n}"
  let legalAxioms ← nameArray j "legalAxioms"
  let _ ← uniqueSet legalAxioms "legal axiom"
  for n in legalAxioms do
    if kinds[n]? != some "axiom" then fail s!"Legal axiom missing/wrong kind: {n}"
  return {canonicalNames := names.extract 0 canonical.size, allNames := names,
          kinds, theoremTargets, roots, primitives, legalAxioms}

/- Normalize only explicitly excluded nonsemantic fields. The exporter already
strips mdata and sets let nondep=false (Export.lean removeMData). Binder names,
binder annotations and all expression constructors/operands are retained. The
upstream Expr BEq separately performs alpha comparison. Only selected declaration
types, definition/opaque bodies and recursor rules are traversed, never the whole
solution proof DAG. Structural inductive/recursor `all` lists are untouched. -/
abbrev NormM := StateM (Std.HashMap Expr Expr)

partial def normExpr (e : Expr) : NormM Expr := do
  if let some result := (← get)[e]? then return result
  let result ← match e with
    | .mdata _ body => normExpr body
    | .app f a => return e.updateApp! (← normExpr f) (← normExpr a)
    | .lam _ d b _ => return e.updateLambdaE! (← normExpr d) (← normExpr b)
    | .forallE _ d b _ => return e.updateForallE! (← normExpr d) (← normExpr b)
    | .letE _ t v b _ => return e.updateLet! (← normExpr t) (← normExpr v) (← normExpr b) false
    | .proj _ _ b => return e.updateProj! (← normExpr b)
    | _ => pure e
  modify (·.insert e result)
  return result

def normInfo (ci : ConstantInfo) : NormM ConstantInfo := do
  let type ← normExpr ci.type
  match ci with
  | .axiomInfo v => return .axiomInfo {v with type}
  | .defnInfo v =>
    let value ← normExpr v.value
    return .defnInfo {v with type, value, hints := .opaque, all := [v.name]}
  | .opaqueInfo v =>
    let value ← normExpr v.value
    return .opaqueInfo {v with type, value, all := [v.name]}
  | .thmInfo v => return .thmInfo {v with type, all := [v.name]}
  | .inductInfo v => return .inductInfo {v with type}
  | .ctorInfo v => return .ctorInfo {v with type}
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do return {r with rhs := ← normExpr r.rhs}
    return .recInfo {v with type, rules}
  | .quotInfo v => return .quotInfo {v with type}

def normalizeSelected (env : LeanExport.ExportedEnv) (names : Array Name) : LeanExport.ExportedEnv := Id.run do
  let mut constMap := env.constMap
  let mut cache : Std.HashMap Expr Expr := {}
  for n in names do
    if let some ci := constMap[n]? then
      let (ci, next) := (normInfo ci).run cache
      cache := next
      constMap := constMap.insert n ci
  return {env with constMap}

structure Coverage where
  activeNames : Array Name
  absentOptionalSupplement : Array Name

def validateCoverage (scope : Scope) (challenge solution : LeanExport.ExportedEnv) : Except String Coverage := do
  if challenge.constMap.size != scope.allNames.size then fail "Challenge declaration set size differs from exact scope"
  let mandatory := Std.HashSet.ofArray (scope.canonicalNames ++ scope.legalAxioms)
  let mut activeNames := #[]
  let mut absentOptionalSupplement := #[]
  for n in scope.allNames do
    let some c := challenge.constMap[n]? | fail s!"Challenge omitted scoped declaration: {n}"
    if scope.kinds[n]? != some (kind c) then fail s!"Challenge declaration kind differs from scope: {n}"
    let some s := solution.constMap[n]? | do
      if mandatory.contains n then fail s!"Solution omitted scoped declaration: {n}"
      absentOptionalSupplement := absentOptionalSupplement.push n
      continue
    if kind c != kind s then fail s!"Solution declaration kind differs: {n}"
    if c.isUnsafe != s.isUnsafe || c.isPartial != s.isPartial then
      fail s!"Solution declaration safety differs: {n}"
    activeNames := activeNames.push n
  return {activeNames, absentOptionalSupplement}

def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str pre s => (nameComponents pre).push (Json.arr #[toJson "s", toJson s])
  | .num pre n => (nameComponents pre).push (Json.arr #[toJson "n", toJson n])

def run (challengePath solutionPath scopePath : String) : IO Unit := do
  let scopeJson ← IO.ofExcept (Json.parse (← IO.FS.readFile scopePath))
  let scope ← IO.ofExcept (parseScope scopeJson)
  IO.println "Parsing trusted challenge serialization"
  let challenge ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk challengePath .read))
  IO.println "Parsing solution serialization (no project code execution)"
  let solution ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk solutionPath .read))
  let coverage ← IO.ofExcept (validateCoverage scope challenge solution)
  let activeTheorems := scope.theoremTargets.filter solution.constMap.contains
  IO.println ("comparison coverage: " ++ (Json.mkObj [
    ("canonicalDeclarationCount", toJson scope.canonicalNames.size),
    ("referenceDeclarationCount", toJson scope.allNames.size),
    ("comparedDeclarationCount", toJson coverage.activeNames.size),
    ("absentOptionalSupplementNames", Json.arr (coverage.absentOptionalSupplement.map (Json.arr ∘ nameComponents))),
    ("allCanonicalDeclarationsPresent", toJson true),
    ("allLegalAxiomsPresent", toJson true)]).compress)
  let challenge := normalizeSelected challenge coverage.activeNames
  let solution := normalizeSelected solution coverage.activeNames
  IO.println s!"Comparing {coverage.activeNames.size} present scoped declarations with upstream Lake.Check.compareAt"
  -- Missing optional support is not seeded. Any such name reached from a
  -- compared type/body/structural dependency still fails in upstream Compare.loop.
  IO.ofExcept (Lake.Check.compareAt challenge solution activeTheorems #[] coverage.activeNames)
  IO.println "Checking root proof axiom closure with upstream Lake.Check.checkAxioms"
  IO.ofExcept (Lake.Check.checkAxioms solution scope.roots #[] scope.legalAxioms)
  IO.println s!"serialized comparison passed: {scope.canonicalNames.size} canonical declarations, {coverage.activeNames.size} compared declarations, {coverage.absentOptionalSupplement.size} absent optional supplement declarations, {scope.roots.size} roots"

end SerializedComparison

