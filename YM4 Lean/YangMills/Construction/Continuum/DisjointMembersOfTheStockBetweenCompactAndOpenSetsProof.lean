import YangMills.Construction.Continuum.DisjointMembersOfTheStockBetweenCompactAndOpenSets
import YangMills.Construction.Continuum.RationalBoxUnionsBetweenCompactAndOpenSets
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.Continuum.RationalBoxes
theorem mem_boxUnions_of_mem_ratBoxUnions {U : Set (Fin 4 → ℝ)}
    (hU : U ∈ TestFunctions.ratBoxUnions) : U ∈ boxUnions := by
  obtain ⟨𝓑, hfin, hbox, rfl⟩ := hU
  obtain ⟨r, b, -, rfl⟩ := hfin.fin_param
  exact ⟨r, b, fun i => hbox (b i) ⟨i, rfl⟩, sUnion_range b⟩
theorem disjointUnionsBetweenCompactAndOpen_of_separation
    (hsep : RatBoxSeparation.separationClaim) : DisjointUnionsBetweenCompactAndOpen := by
  obtain ⟨-, hb, -⟩ := hsep
  intro k hk K V hK hdisj hV hKV
  obtain ⟨U, hU, hUd, hUs⟩ := hb k hk K V hK hdisj hV hKV
  exact ⟨U, fun i => mem_boxUnions_of_mem_ratBoxUnions (hU i), hUd, hUs⟩
end YangMills.Construction.Continuum.RationalBoxes
