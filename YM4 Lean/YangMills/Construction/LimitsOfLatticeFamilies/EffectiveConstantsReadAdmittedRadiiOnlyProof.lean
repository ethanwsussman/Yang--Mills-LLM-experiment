import YangMills.Construction.LimitsOfLatticeFamilies.EffectiveConstantsReadAdmittedRadiiOnly
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeLimits.EffConstValue
open ModelSpace
theorem pos_of_mem_admissibleRadii (s : Conventions.StandingParameters) (Y : ModelSpace) {r : ℝ}
    (hr : r ∈ admissibleRadii s Y) : 0 < r := by
  cases Y with
  | euclidean => exact Set.mem_Ioi.1 hr
  | torus => exact (Set.mem_Ioo.1 hr).1
theorem refRadius_mem_admissibleRadii (s : Conventions.StandingParameters) (Y : ModelSpace) :
    refRadius s Y ∈ admissibleRadii s Y := by
  cases Y with
  | euclidean =>
    show (1 : ℝ) ∈ Set.Ioi 0
    exact Set.mem_Ioi.2 one_pos
  | torus =>
    have hL : 0 < s.L := by
      have h := s.isAdmissible.2
      omega
    have hp : (0 : ℝ) < (s.L : ℝ) ^ (s.m : ℕ) := pow_pos (by exact_mod_cast hL) _
    show (s.L : ℝ) ^ (s.m : ℕ) / 4 ∈ Set.Ioo 0 ((s.L : ℝ) ^ (s.m : ℕ) / 2)
    exact Set.mem_Ioo.2 ⟨by linarith, by linarith⟩
theorem one_le_costFactor (M : ℕ) (Y : ModelSpace) : 1 ≤ costFactor M Y := by
  cases Y with
  | euclidean => exact le_refl _
  | torus =>
    have hx : (0 : ℝ) ≤ 320 * Real.pi * M := by positivity
    show (1 : ℝ) ≤ 16 ^ 4 * (1 + 320 * Real.pi * M)
    linarith
theorem effConstOf_spec (s : Conventions.StandingParameters) (Y : ModelSpace) (C : SeparationBound)
    {n : ℕ} (hn : 2 ≤ n) {d R r Θ : ℝ} (hd : 0 < d) (hR : 0 < R) (hr : r ∈ admissibleRadii s Y)
    (hΘ : 1 ≤ Θ) :
    flatRadiusOf s Y r R ∈ admissibleRadii s Y ∧
      0 ≤ effConstOf s Y r Θ C n d R ∧
      (R ∈ admissibleRadii s Y →
        effConstOf s Y r Θ C n d R = C.val n d (flatRadiusOf s Y r R)) ∧
      (R ∉ admissibleRadii s Y →
        effConstOf s Y r Θ C n d R =
          Θ ^ n * C.val n d (flatRadiusOf s Y r R)) ∧
      (Y = euclidean →
        flatRadiusOf s Y r R = R ∧ effConstOf s Y r Θ C n d R = C.val n d R) := by
  have hE : Y = euclidean → R ∈ admissibleRadii s Y := by
    rintro rfl
    exact Set.mem_Ioi.2 hR
  by_cases h : R ∈ admissibleRadii s Y
  · have hf : flatRadiusOf s Y r R = R := by
      unfold flatRadiusOf
      exact if_pos h
    have he : effConstOf s Y r Θ C n d R = C.val n d R := by
      unfold effConstOf
      exact if_pos h
    rw [hf, he]
    exact ⟨h, C.val_nonneg n hn d R hd hR, fun _ => rfl, fun h' => absurd h h', fun _ => ⟨rfl, rfl⟩⟩
  · have hf : flatRadiusOf s Y r R = r := by
      unfold flatRadiusOf
      exact if_neg h
    have he : effConstOf s Y r Θ C n d R = Θ ^ n * C.val n d r := by
      unfold effConstOf
      exact if_neg h
    rw [hf, he]
    have hΘ0 : 0 ≤ Θ := by linarith
    exact ⟨hr, mul_nonneg (pow_nonneg hΘ0 n)
      (C.val_nonneg n hn d r hd (pos_of_mem_admissibleRadii s Y hr)),
      fun h' => absurd h' h, fun _ => rfl, fun hY => absurd (hE hY) h⟩
theorem effConstReadsAdmissibleRadii_holds : EffConstReadsAdmissibleRadii := by
  unfold EffConstReadsAdmissibleRadii
  refine ⟨fun s M Y => ⟨refRadius_mem_admissibleRadii s Y, one_le_costFactor M.1 Y,
    fun C n hn d R hd hR => ⟨?_, fun r hr Θ hΘ => effConstOf_spec s Y C hn hd hR hr hΘ⟩⟩,
    fun M => rfl⟩
  exact effConstOf_spec s Y C hn hd hR (refRadius_mem_admissibleRadii s Y) (one_le_costFactor M.1 Y)
end YangMills.Construction.LatticeLimits.EffConstValue
end
