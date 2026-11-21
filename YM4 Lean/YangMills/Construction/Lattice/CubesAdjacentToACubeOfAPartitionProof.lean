import YangMills.Construction.Lattice.AdjacentCubesWithThreeCubesInEachDirectionProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.PartitionCubeNeighbours
open EdgeGraphCubeProperties CubeLifts
variable (S : LevelUnitPartition)
theorem proj_eq_iff_isPointLift (x : S.Points) (w : Fin 4 → ℝ) :
    S.proj w = x ↔ S.IsPointLift x w := by apply _root_.YangMills.Construction.PeriodicLattice.ThreeWideNeighbours.proj_eq_iff_isPointLift <;> assumption
theorem int_eq_of_abs_mul_sub_le_half {M : ℝ} (hM : 0 < M) {a b : ℤ}
    (h : |M * (a : ℝ) - M * (b : ℝ)| ≤ M / 2) : a = b := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 h
  rcases lt_trichotomy a b with hab | hab | hab
  · have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    nlinarith
  · exact hab
  · have : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hab
    nlinarith
theorem int_eq_or_eq_add_of_abs_le_half {M : ℝ} (hM : 0 < M) {a b : ℤ} {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (h : |M * (a : ℝ) + ε * M / 2 - M * (b : ℝ)| ≤ M / 2) :
    b = a ∨ (b : ℝ) = (a : ℝ) + ε := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 h
  rcases hε with rfl | rfl
  · have hl : a ≤ b := by
      by_contra hc
      have : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast not_le.1 hc
      nlinarith
    have hu : b ≤ a + 1 := by
      by_contra hc
      have : (a : ℝ) + 1 + 1 ≤ (b : ℝ) := by exact_mod_cast not_le.1 hc
      nlinarith
    rcases (by omega : b = a ∨ b = a + 1) with hb | hb
    · exact Or.inl hb
    · exact Or.inr (by rw [hb]; push_cast; ring)
  · have hl : b ≤ a := by
      by_contra hc
      have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast not_le.1 hc
      nlinarith
    have hu : a - 1 ≤ b := by
      by_contra hc
      have : (b : ℝ) + 1 + 1 ≤ (a : ℝ) := by
        have : b + 1 + 1 ≤ a := by omega
        exact_mod_cast this
      nlinarith
    rcases (by omega : b = a ∨ b = a - 1) with hb | hb
    · exact Or.inl hb
    · exact Or.inr (by rw [hb]; push_cast; ring)
theorem torusSide_eq_and_meshSize_ne_zero (hT : TorusInCubeUnits S) :
    torusSide S.params.L S.params.m =
        (S.cubeCount : ℝ) * meshSize S.params.L S.index ∧
      meshSize S.params.L S.index ≠ 0 := by
  obtain ⟨-, -, -, hunitM, hunitS, hsideN, -, -, -, -, hM⟩ := hT
  have hMr : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hM
  have hL : (S.params.L : ℝ) ≠ 0 := by
    have := S.params.isAdmissible.2
    have h0 : S.params.L ≠ 0 := by omega
    exact_mod_cast h0
  have hpow : (S.params.L : ℝ) ^ levelDepth S.params.K S.level ≠ 0 := zpow_ne_zero _ hL
  simp only [toLevelUnits] at hunitM hunitS
  refine ⟨?_, ?_⟩
  · have hunitS' : (S.params.L : ℝ) ^ levelDepth S.params.K S.level *
        torusSide S.params.L S.params.m = scaledTorusSide S := hunitS
    apply mul_left_cancel₀ hpow
    rw [hunitS', hsideN, ← hunitM]
    ring
  · intro h0
    rw [h0, mul_zero] at hunitM
    exact hMr.ne hunitM
theorem signed_half_meshSize_ne_zero (hT : TorusInCubeUnits S) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ((ε * meshSize S.params.L S.index / 2 : ℝ) : AddCircle (torusSide S.params.L S.params.m)) ≠
      0 := by
  intro h0
  obtain ⟨hside, ha⟩ := torusSide_eq_and_meshSize_ne_zero S hT
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
  rw [hside, zsmul_eq_mul] at hn
  have hr : 2 * (n : ℝ) * (S.cubeCount : ℝ) = ε := by
    apply mul_right_cancel₀ ha
    linear_combination 2 * hn
  have hz : 2 * (n * (S.cubeCount : ℤ)) = 1 ∨ 2 * (n * (S.cubeCount : ℤ)) = -1 := by
    rcases hε with rfl | rfl
    · left
      have : ((2 * (n * (S.cubeCount : ℤ)) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    · right
      have : ((2 * (n * (S.cubeCount : ℤ)) : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
  omega
theorem exists_pointLift_of_shareFace (hT : TorusInCubeUnits S) (hC : SiteAndCubeLifts S)
    (y y' : Site S.params.L S.params.m S.index) {c : Fin 4 → ℝ}
    (hc : S.IsPointLift (y : S.Points) c) (hcen : IsCubeCentre S c)
    (hadj : CubesShareFace S.index (cubeAround y) (cubeAround y')) :
    ∃ (ν : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
      S.IsPointLift (y' : S.Points) (c + EdgeGraphCubeProperties.signedStep S ν σ) := by
  have hhalf := fun {ε : ℝ} (hε : ε = 1 ∨ ε = -1) => signed_half_meshSize_ne_zero S hT hε
  obtain ⟨-, hsp, -, -, -, -, hlift, hper, -, -, hM⟩ := hT
  obtain ⟨hcentres, hcube, hinj, -⟩ := hC
  have hMr : (0 : ℝ) < (S.side : ℝ) := by exact_mod_cast hM
  obtain ⟨⟨y₁, hy₁, μ, ε, hε, hwall⟩, -⟩ := hadj
  have hyy : y₁ = y := by
    by_contra h
    exact hinj y₁ y h hy₁.symm
  subst hyy
  have hcov : S.proj c = (y₁ : S.Points) := (proj_eq_iff_isPointLift S _ _).2 hc
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → ℝ,
      w = c + (ε * (S.side : ℝ) / 2) • coordVec μ := ⟨_, rfl⟩
  have hwμ : w μ = c μ + ε * (S.side : ℝ) / 2 := by
    simp [hw, coordVec]
  have hwk : ∀ k, k ≠ μ → w k = c k := by
    intro k hk
    simp [hw, coordVec, Pi.single_eq_of_ne hk]
  have hwQ : w ∈ S.closedBox c := by
    intro k
    by_cases hk : k = μ
    · subst hk
      rw [hwμ]
      rcases hε with rfl | rfl <;> constructor <;> linarith
    · rw [hwk k hk]
      constructor <;> linarith
  have hpΔ : S.proj w ∈ cubeAround y₁ := by
    rw [hcube y₁ c hc]
    exact ⟨w, hwQ, rfl⟩
  have hpμ : S.proj w μ = (y₁ : S.Points) μ +
      ((ε * meshSize S.params.L S.index / 2 : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) := by
    rw [← hcov]
    change ((meshSize S.params.L (levelDepth S.params.K S.level) * w μ : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) =
      ((meshSize S.params.L (levelDepth S.params.K S.level) * c μ : ℝ) :
        AddCircle (torusSide S.params.L S.params.m)) + _
    rw [← AddCircle.coe_add, hwμ, ← hsp]
    congr 1
    ring
  have hpF : S.proj w ∈ cubeAround y₁ ∩ cubeAround y' := by
    rw [hwall]
    exact ⟨hpΔ, hpμ⟩
  obtain ⟨c', hc'⟩ := hlift (y' : S.Points)
  have hp' := hpF.2
  rw [hcube y' c' hc'] at hp'
  obtain ⟨x, hxQ, hxw⟩ := hp'
  have hperiod : IsPeriodVector S (w - x) :=
    (hper w x).1 ⟨S.proj w, (proj_eq_iff_isPointLift S _ _).1 rfl,
      (proj_eq_iff_isPointLift S _ _).1 hxw⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Fin 4 → ℝ, c₂ = c' + (w - x) := ⟨_, rfl⟩
  have hper₂ : IsPeriodVector S (c₂ - c') := by
    rw [hc₂, add_sub_cancel_left]
    exact hperiod
  obtain ⟨pt, h₁, h₂⟩ := (hper c₂ c').2 hper₂
  have hpt : pt = (y' : S.Points) :=
    ((proj_eq_iff_isPointLift S _ _).2 h₂).symm.trans ((proj_eq_iff_isPointLift S _ _).2 hc')
  rw [hpt] at h₁
  have hcen₂ : IsCubeCentre S c₂ := (hcentres c₂).1 ⟨y', h₁⟩
  have hclose : ∀ k, |w k - c₂ k| ≤ (S.side : ℝ) / 2 := by
    intro k
    have hk := hxQ k
    have : w k - c₂ k = x k - c' k := by
      rw [hc₂]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [this, abs_le]
    constructor <;> linarith [hk.1, hk.2]
  have hother : ∀ k, k ≠ μ → c₂ k = c k := by
    intro k hk
    obtain ⟨a, ha⟩ := hcen k
    obtain ⟨b, hb⟩ := hcen₂ k
    have h := hclose k
    rw [hwk k hk, ha, hb] at h
    rw [ha, hb, int_eq_of_abs_mul_sub_le_half hMr h]
  obtain ⟨a, ha⟩ := hcen μ
  obtain ⟨b, hb⟩ := hcen₂ μ
  have hμ := hclose μ
  rw [hwμ, ha, hb] at hμ
  rcases int_eq_or_eq_add_of_abs_le_half hMr hε hμ with hab | hab
  · exfalso
    have hcc : c₂ = c := by
      funext k
      by_cases hk : k = μ
      · subst hk
        rw [ha, hb, hab]
      · exact hother k hk
    rw [hcc] at h₁
    have hsame : cubeAround y' = cubeAround y₁ := by
      rw [hcube y' c h₁, hcube y₁ c hc]
    have hcentre : S.proj c ∈ cubeAround y₁ := by
      rw [hcube y₁ c hc]
      refine ⟨c, fun k => ?_, rfl⟩
      constructor <;> linarith
    have hin : S.proj c ∈ cubeAround y₁ ∩ cubeAround y' := ⟨hcentre, hsame ▸ hcentre⟩
    rw [hwall] at hin
    have hz := hin.2
    rw [hcov] at hz
    exact hhalf hε (left_eq_add.1 hz)
  · refine ⟨μ, ε, hε, ?_⟩
    have hcc : c₂ = c + EdgeGraphCubeProperties.signedStep S μ ε := by
      funext k
      by_cases hk : k = μ
      · subst hk
        simp only [EdgeGraphCubeProperties.signedStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          coordVec]
        rw [ha, hb, hab]
        simp
        ring
      · simp only [EdgeGraphCubeProperties.signedStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          coordVec]
        rw [hother k hk, Pi.single_eq_of_ne hk]
        simp
    rw [← hcc]
    exact h₁
theorem of_cubeLifts (hLifts : CubeLifts.Statement) : PartitionCubeNeighbours := by
  intro S
  obtain ⟨-, -, hS⟩ := hLifts
  obtain ⟨hT, -, hC, -, -, -⟩ := hS S
  have hlift : ∀ x : S.Points, ∃ w, S.IsPointLift x w := hT.2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rintro c hc Δ Δ' ⟨y, hy, rfl⟩ hΔ' hadj
    obtain ⟨y', rfl⟩ : ∃ y' : Site S.params.L S.params.m S.index, cubeAround y' = Δ' := hΔ'
    obtain ⟨ν, σ, hσ, h⟩ :=
      exists_pointLift_of_shareFace S hT hC y y' ((proj_eq_iff_isPointLift S _ _).1 hy.symm) hc
        hadj
    exact ⟨ν, σ, hσ, y', (proj_eq_iff_isPointLift S _ _).2 h |>.symm, rfl⟩
  · intro Δ hΔ
    obtain ⟨y, rfl⟩ : ∃ y : Site S.params.L S.params.m S.index, cubeAround y = Δ := hΔ
    obtain ⟨c, hc⟩ := hlift (y : S.Points)
    have hcen : IsCubeCentre S c := (hC.1 c).1 ⟨y, hc⟩
    have hsub : neighbourCubes S (cubeAround y) ⊆
        range (fun p : Fin 4 × Bool =>
          projectedBox S (c + EdgeGraphCubeProperties.signedStep S p.1 (if p.2 then 1 else -1))) := by
      rintro Δ' ⟨hΔ', hadj⟩
      obtain ⟨y', rfl⟩ : ∃ y' : Site S.params.L S.params.m S.index, cubeAround y' = Δ' := hΔ'
      obtain ⟨ν, σ, hσ, h⟩ := exists_pointLift_of_shareFace S hT hC y y' hc hcen hadj
      rcases hσ with rfl | rfl
      · exact ⟨(ν, true), by simpa [projectedBox] using (hC.2.1 y' _ h).symm⟩
      · exact ⟨(ν, false), by simpa [projectedBox] using (hC.2.1 y' _ h).symm⟩
    refine (encard_le_encard hsub).trans ?_
    rw [← image_univ]
    refine (encard_image_le _ _).trans ?_
    rw [encard_univ, ENat.card_eq_coe_fintype_card]
    simp
end YangMills.Construction.PeriodicLattice.PartitionCubeNeighbours
end
