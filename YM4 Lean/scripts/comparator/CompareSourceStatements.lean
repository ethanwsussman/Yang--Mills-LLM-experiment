import SerializedSupport

/- Data-only comparison using the unmodified upstream algorithms. The challenge
has real helper proofs and explicit source root holes. Theorems are compared by
their types; definitions, opaque values and structural data remain strict.
This adapter is not a kernel proof checker. -/
open Lean SerializedComparison

namespace SourceStatementComparison

def coverage (scope : Scope) (challenge solution : LeanExport.ExportedEnv) : Except String Coverage := do
  let mandatory := Std.HashSet.ofArray (scope.canonicalNames ++ scope.legalAxioms)
  let mut activeNames := #[]
  let mut absentOptionalSupplement := #[]
  for n in scope.allNames do
    let some c := challenge.constMap[n]? | fail s!"Challenge omitted scoped declaration: {n}"
    if scope.kinds[n]? != some (kind c) then fail s!"Challenge declaration kind differs: {n}"
    let some s := solution.constMap[n]? | do
      if mandatory.contains n then fail s!"Solution omitted scoped declaration: {n}"
      absentOptionalSupplement := absentOptionalSupplement.push n
      continue
    if kind c != kind s then fail s!"Solution declaration kind differs: {n}"
    if c.isUnsafe != s.isUnsafe || c.isPartial != s.isPartial then fail s!"Declaration safety differs: {n}"
    activeNames := activeNames.push n
  return {activeNames, absentOptionalSupplement}

def run (challengePath solutionPath scopePath : String) : IO Unit := do
  let scope ← IO.ofExcept (parseScope (← IO.ofExcept (Json.parse (← IO.FS.readFile scopePath))))
  IO.println "Parsing fresh challenge export (actual helper proofs retained)"
  let challenge ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk challengePath .read))
  IO.println "Parsing solution export (data only; no project code execution)"
  let solution ← LeanExport.parseStream (.ofHandle (← IO.FS.Handle.mk solutionPath .read))
  let c ← IO.ofExcept (coverage scope challenge solution)
  let activeTheorems := scope.theoremTargets.filter solution.constMap.contains
  let helperTheorems := scope.theoremTargets.filter fun n => !scope.roots.contains n
  let challengeDefinitions := scope.allNames.filter fun n => scope.kinds[n]? == some "definition"
  let solutionDefinitions := c.activeNames.filter fun n => scope.kinds[n]? == some "definition"
  IO.println ("source statement coverage: " ++ (Json.mkObj [
    ("canonicalDeclarationCount", toJson scope.canonicalNames.size),
    ("referenceDeclarationCount", toJson scope.allNames.size),
    ("comparedSeedCount", toJson c.activeNames.size),
    ("referenceTheoremTypeCount", toJson scope.theoremTargets.size),
    ("comparedTheoremTypeCount", toJson activeTheorems.size),
    ("canonicalTheoremTypeCount", toJson (scope.canonicalNames.filter fun n => scope.kinds[n]? == some "theorem").size),
    ("challengeHelperAxiomCheckCount", toJson helperTheorems.size),
    ("sourceRootProofHoles", Json.arr (scope.roots.map (Json.arr ∘ nameComponents))),
    ("definitionHoles", Json.arr #[]),
    ("absentOptionalSupplementNames", Json.arr (c.absentOptionalSupplement.map (Json.arr ∘ nameComponents)))
  ]).compress)
  -- Check original, unnormalized helper proof closures. Following a source root
  -- hole reaches sorryAx and is rejected by the same official axiom walker.
  IO.println "Checking challenge helper and definition axiom closures"
  IO.ofExcept (Lake.Check.checkAxioms challenge helperTheorems challengeDefinitions scope.legalAxioms)
  let challenge := normalizeSelected challenge c.activeNames
  let solution := normalizeSelected solution c.activeNames
  IO.ofExcept (Lake.Check.compareAt challenge solution activeTheorems #[] c.activeNames)
  IO.println "Checking all compared solution theorem and definition axiom closures"
  IO.ofExcept (Lake.Check.checkAxioms solution activeTheorems solutionDefinitions scope.legalAxioms)
  IO.println "source statement comparison passed: all present scoped theorem types; strict non-theorem bodies; checked helper and solution axiom closures"

end SourceStatementComparison

def main (args : List String) : IO UInt32 := do
  match args with
  | [challenge, solution, scope] =>
    try SourceStatementComparison.run challenge solution scope; return 0
    catch e => IO.eprintln s!"source statement comparison failed: {e}"; return 1
  | _ => IO.eprintln "usage: CompareSourceStatements CHALLENGE.ndjson SOLUTION.ndjson SCOPE.json"; return 2
