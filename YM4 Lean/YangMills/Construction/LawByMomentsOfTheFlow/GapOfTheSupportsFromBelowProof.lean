import YangMills.Construction.LawByMomentsOfTheFlow.DistanceOfTheSitesOfTwoSupports
import YangMills.Construction.LawByMomentsOfTheFlow.GapOfTheSupportsFromBelow
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
private theorem mem_thickening_two {N : ℕ} [NeZero N] {A : Finset (TorusSite N)} {w : TorusSite N} (hw : w ∈ A) :
    w ∈ thickening 2 A := by
  simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨w, hw, by rw [supDist_self]; exact Nat.zero_le _⟩
private theorem exists_two_distinct_fin {k : ℕ} (hk : 2 ≤ k) : ∃ i j : Fin k, i ≠ j :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
theorem separationLowerBound_of_support_bounds (hLoc : supportSitesLocationStatement)
    (hDist : SupportSiteDistanceBounds) : separationLowerBoundStatement := by
  intro L _ hL hL3 k hk R d hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨d / (2 * L), by positivity, fun P hF u hu => ?_⟩
  have hne : {e | ∃ i j, i ≠ j ∧ ∃ y ∈ thickening 2 (P.supportSites L (u + 1) i), ∃ y' ∈ thickening 2 (P.supportSites L (u + 1) j),
      supDist y y' = e}.Nonempty := by
    obtain ⟨i, j, hij⟩ := exists_two_distinct_fin hk
    obtain ⟨w, hw⟩ := (hLoc L hL k P (u + 1) hu i).2 (hF.exists_ne_zero i)
    obtain ⟨w', hw'⟩ := (hLoc L hL k P (u + 1) hu j).2 (hF.exists_ne_zero j)
    exact ⟨_, i, j, hij, w, mem_thickening_two hw, w', mem_thickening_two hw', rfl⟩
  obtain ⟨i, j, hij, y, hy, y', hy', he⟩ := Nat.sInf_mem hne
  have hsep : supDist y y' = P.separation L u := he
  simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨x', hx', hxy'⟩ := hy'
  have h := (hDist L hL k R d hd P hF (u + 1) hu i j x hx x' hx').2 hij
  have ht : supDist x x' ≤ P.separation L u + 4 := by
    have h1 := supDist_triangle x y x'
    have h2 := supDist_triangle y y' x'
    rw [supDist_comm x y] at h1
    omega
  have htr : (supDist x x' : ℝ) ≤ (P.separation L u : ℝ) + 4 := by exact_mod_cast ht
  have hz : (L : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) = (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L := by
    push_cast
    rw [← sub_sub, zpow_sub₀ (ne_of_gt hLpos), zpow_one]
  rw [hz] at h
  have he2 : d / (2 * L) * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) = d / 2 * ((L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L) := by
    field_simp
  rw [he2]
  linarith
end YangMills.Construction.LevelTestFunctions
end
