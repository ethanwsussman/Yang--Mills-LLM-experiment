import YangMills.Construction.LawByMomentsOfTheFlow.DistanceOfTheSitesOfTwoSupports
import YangMills.Construction.LawByMomentsOfTheFlow.GapOfTheSupportsFromAbove
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open TorusFields TorusLumps
private theorem mem_thickening_two {N : ℕ} [NeZero N] {A : Finset (TorusSite N)} {w : TorusSite N}
    (hw : w ∈ A) : w ∈ thickening 2 A := by
  simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨w, hw, by rw [supDist_self]; exact Nat.zero_le _⟩
private theorem exists_fin_ne_of_two_le {k : ℕ} (hk : 2 ≤ k) : ∃ i j : Fin k, i ≠ j :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
theorem separationUpperBound_holds (hP : supportSitesLocationStatement)
    (hD : SupportSiteDistanceBounds) : separationUpperBoundStatement := by
  intro L _ hL hL3 k hk R d hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨2 * |R| / L, by positivity, fun P hF u hu => ?_⟩
  obtain ⟨i, j, hij⟩ := exists_fin_ne_of_two_le hk
  obtain ⟨w, hw⟩ := (hP L hL k P (u + 1) hu i).2 (hF.exists_ne_zero i)
  obtain ⟨w', hw'⟩ := (hP L hL k P (u + 1) hu j).2 (hF.exists_ne_zero j)
  have hle : P.separation L u ≤ supDist w w' :=
    Nat.sInf_le ⟨i, j, hij, w, mem_thickening_two hw, w', mem_thickening_two hw', rfl⟩
  have h := (hD L hL k R d hd P hF (u + 1) hu i j w hw w' hw').1
  have hler : (P.separation L u : ℝ) ≤ (supDist w w' : ℝ) := by exact_mod_cast hle
  have hz : (L : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) =
      (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L := by
    push_cast
    rw [← sub_sub, zpow_sub₀ (ne_of_gt hLpos), zpow_one]
  rw [hz] at h
  have h2 : 2 * R * ((L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L) ≤
      2 * |R| / L * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) := by
    have : 2 * |R| / L * (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) =
        2 * |R| * ((L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L) := by
      field_simp
    rw [this]
    have h3 : 0 < (L : ℝ) ^ ((P.scaleLevel : ℤ) - (u : ℤ)) / L := by positivity
    nlinarith [le_abs_self R]
  linarith
end YangMills.Construction.LevelTestFunctions
end
