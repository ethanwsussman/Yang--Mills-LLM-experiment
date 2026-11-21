import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusMirror
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages hiding unitStep
variable {n : ℕ}
def triangleFold (m : ℕ) (c : ℤ) : ℤ :=
  if |c| ≤ (m : ℤ) then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c
def foldSite (m : ℕ) (z : TorusSite (4 * m)) : Fin 4 → ℤ := fun l => triangleFold m ((z l).valMinAbs)
def mirrorField (m : ℕ) (y : TorusSite n) (W : TorusField n) : TorusField (4 * m) := fun z i =>
  if foldSite m (z + unitStep (4 * m) i) i = foldSite m z i + 1 then W (y + siteOfInt (foldSite m z)) i
  else (W (y + siteOfInt (foldSite m (z + unitStep (4 * m) i))) i)⁻¹
theorem triangleFold_eq_ite (m : ℕ) (c : ℤ) : triangleFold m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by
  unfold triangleFold
  simp only [abs_le]
theorem valMinAbs_mem_range {m : ℕ} (hm : 0 < m) (a : ZMod (4 * m)) :
    -(2 * (m : ℤ)) < a.valMinAbs ∧ a.valMinAbs ≤ 2 * (m : ℤ) := by
  have : NeZero (4 * m) := ⟨by omega⟩
  have h := ZMod.valMinAbs_mem_Ioc a
  have h1 := h.1
  have h2 := h.2
  push_cast at h1 h2
  constructor <;> omega
theorem triangleFold_valMinAbs_add_one {m : ℕ} (hm : 0 < m) (a : ZMod (4 * m)) :
    triangleFold m ((a + 1).valMinAbs) = triangleFold m (a.valMinAbs + 1) := by
  have : NeZero (4 * m) := ⟨by omega⟩
  obtain ⟨h1, h2⟩ := valMinAbs_mem_range hm a
  obtain ⟨h3, h4⟩ := valMinAbs_mem_range hm (a + 1)
  have hc : (((a + 1).valMinAbs : ℤ) : ZMod (4 * m)) = ((a.valMinAbs + 1 : ℤ) : ZMod (4 * m)) := by
    simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨k, hk⟩ := hc
  push_cast at hk
  have hk' : k = 0 ∨ k = 1 ∨ k = -1 := by
    have e1 : 4 * (m : ℤ) * k < 4 * (m : ℤ) * 2 := by nlinarith
    have e2 : 4 * (m : ℤ) * (-2) < 4 * (m : ℤ) * k := by nlinarith
    have l1 : k < 2 := lt_of_mul_lt_mul_left e1 (by positivity)
    have l2 : -2 < k := lt_of_mul_lt_mul_left e2 (by positivity)
    omega
  rw [triangleFold_eq_ite, triangleFold_eq_ite]
  rcases hk' with rfl | rfl | rfl
  · have : a.valMinAbs + 1 = (a + 1).valMinAbs := by linarith
    rw [this]
  · split_ifs <;> omega
  · split_ifs <;> omega
theorem triangleFold_add_one (m : ℕ) (c : ℤ) :
    triangleFold m (c + 1) = triangleFold m c + 1 ∨
      triangleFold m (c + 1) = triangleFold m c - 1 := by
  rw [triangleFold_eq_ite, triangleFold_eq_ite]
  split_ifs <;> omega
theorem abs_triangleFold_le {m : ℕ} (hm : 0 < m) (a : ZMod (4 * m)) :
    |triangleFold m a.valMinAbs| ≤ (m : ℤ) := by
  obtain ⟨h1, h2⟩ := valMinAbs_mem_range hm a
  rw [triangleFold_eq_ite, abs_le]
  split_ifs <;> omega
theorem foldSite_inBox {m : ℕ} (hm : 0 < m) (z : TorusSite (4 * m)) : OffsetInBox m (foldSite m z) :=
  fun l => abs_triangleFold_le hm (z l)
theorem foldSite_add_unitStep_of_ne {m : ℕ} (z : TorusSite (4 * m)) (i l : Fin 4) (h : l ≠ i) :
    foldSite m (z + unitStep (4 * m) i) l = foldSite m z l := by
  simp [foldSite, unitStep, h]
theorem foldSite_add_unitStep_self {m : ℕ} (hm : 0 < m) (z : TorusSite (4 * m)) (i : Fin 4) :
    foldSite m (z + unitStep (4 * m) i) i = triangleFold m ((z i).valMinAbs + 1) := by
  have : (z + unitStep (4 * m) i) i = z i + 1 := by simp [unitStep]
  simp only [foldSite, this]
  exact triangleFold_valMinAbs_add_one hm (z i)
section Plaquettes
variable {m : ℕ}
theorem foldSite_of_up {z : TorusSite (4 * m)} {i : Fin 4}
    (h : foldSite m (z + unitStep (4 * m) i) i = foldSite m z i + 1) :
    foldSite m (z + unitStep (4 * m) i) = foldSite m z + Pi.single i 1 := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [h]
  · simp [foldSite_add_unitStep_of_ne z i l hl, hl]
theorem foldSite_of_down {z : TorusSite (4 * m)} {i : Fin 4}
    (h : foldSite m (z + unitStep (4 * m) i) i = foldSite m z i - 1) :
    foldSite m z = foldSite m (z + unitStep (4 * m) i) + Pi.single i 1 := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [h]
  · simp [foldSite_add_unitStep_of_ne z i l hl, hl]
theorem mirrorField_of_up (y : TorusSite n) (W : TorusField n) {z : TorusSite (4 * m)} {i : Fin 4}
    (h : foldSite m (z + unitStep (4 * m) i) i = foldSite m z i + 1) :
    mirrorField m y W z i = W (y + siteOfInt (foldSite m z)) i := by
  unfold mirrorField
  rw [if_pos h]
theorem mirrorField_of_down (y : TorusSite n) (W : TorusField n) {z : TorusSite (4 * m)} {i : Fin 4}
    (h : foldSite m (z + unitStep (4 * m) i) i = foldSite m z i - 1) :
    mirrorField m y W z i = (W (y + siteOfInt (foldSite m (z + unitStep (4 * m) i))) i)⁻¹ := by
  unfold mirrorField
  rw [if_neg (by omega)]
theorem foldSite_slope_of_ne (z : TorusSite (4 * m)) {i j : Fin 4} (hij : i ≠ j) (e : ℤ)
    (h : foldSite m (z + unitStep (4 * m) i) i = foldSite m z i + e) :
    foldSite m (z + unitStep (4 * m) j + unitStep (4 * m) i) i = foldSite m (z + unitStep (4 * m) j) i + e := by
  have h1 : (z + unitStep (4 * m) j + unitStep (4 * m) i) i = (z + unitStep (4 * m) i) i := by simp [unitStep, hij]
  have h2 : (z + unitStep (4 * m) j) i = z i := by simp [unitStep, hij]
  simp only [foldSite, h1, h2]
  exact h
theorem exists_plaquetteEnergy_mirrorField [NeZero n] (hm : 0 < m) (y : TorusSite n) (W : TorusField n)
    (z : TorusSite (4 * m)) {μ ν : Fin 4}
    (hne : μ ≠ ν) : ∃ a' : Fin 4 → ℤ, (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a' + d)) ∧
      plaquetteEnergy (mirrorField m y W) z μ ν = plaquetteEnergy W (y + siteOfInt a') μ ν := by
  have : NeZero (4 * m) := ⟨by omega⟩
  have hslope : ∀ (u : TorusSite (4 * m)) (i : Fin 4),
      foldSite m (u + unitStep (4 * m) i) i = foldSite m u i + 1 ∨
        foldSite m (u + unitStep (4 * m) i) i = foldSite m u i - 1 := by
    intro u i
    rw [foldSite_add_unitStep_self hm]
    exact triangleFold_add_one m _
  have hsw : z + unitStep (4 * m) ν + unitStep (4 * m) μ = z + unitStep (4 * m) μ + unitStep (4 * m) ν := by abel
  have hboxAll : ∀ u : TorusSite (4 * m), OffsetInBox m (foldSite m u) := foldSite_inBox hm
  set p0 := foldSite m z with hp0
  set p1 := foldSite m (z + unitStep (4 * m) μ) with hp1
  set p2 := foldSite m (z + unitStep (4 * m) ν) with hp2
  set p3 := foldSite m (z + unitStep (4 * m) μ + unitStep (4 * m) ν) with hp3
  have b0 : OffsetInBox m p0 := hboxAll _
  have b1 : OffsetInBox m p1 := hboxAll _
  have b2 : OffsetInBox m p2 := hboxAll _
  have b3 : OffsetInBox m p3 := hboxAll _
  have hev : ∀ (b : Fin 4 → ℤ) (i : Fin 4),
      y + siteOfInt b + unitStep n i = y + siteOfInt (b + Pi.single i 1) := by
    intro b i
    rw [add_siteOfInt_add, unitStep_eq_siteOfInt]
  have ecorners : ∀ (a' : Fin 4 → ℤ), OffsetInBox m a' → OffsetInBox m (a' + Pi.single μ 1) →
      OffsetInBox m (a' + Pi.single ν 1) → OffsetInBox m (a' + Pi.single μ 1 + Pi.single ν 1) →
      ∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a' + d) := by
    intro a' h0 h1 h2 h3 d hd
    simp only [plaquetteOffsets, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · simpa using h0
    · exact h1
    · exact h2
    · rwa [← add_assoc]
  unfold plaquetteEnergy holonomy
  rcases hslope z μ with sμ | sμ <;> rcases hslope z ν with sν | sν
  · have q1 : p1 = p0 + Pi.single μ 1 := foldSite_of_up sμ
    have q2 : p2 = p0 + Pi.single ν 1 := foldSite_of_up sν
    have sν' := foldSite_slope_of_ne z hne.symm 1 sν
    have q3 : p3 = p1 + Pi.single ν 1 := foldSite_of_up sν'
    refine ⟨p0, ecorners p0 b0 (q1 ▸ b1) (q2 ▸ b2) (by rw [← q1, ← q3]; exact b3), ?_⟩
    rw [mirrorField_of_up y W sμ, mirrorField_of_up y W sν, mirrorField_of_up y W sν',
      mirrorField_of_up y W (foldSite_slope_of_ne z hne 1 sμ),
      ← hp0, ← hp1, ← hp2, hev, hev, q1, q2]
  · have q1 : p1 = p0 + Pi.single μ 1 := foldSite_of_up sμ
    have q2 : p0 = p2 + Pi.single ν 1 := foldSite_of_down sν
    have sν' : foldSite m (z + unitStep (4 * m) μ + unitStep (4 * m) ν) ν =
        foldSite m (z + unitStep (4 * m) μ) ν - 1 := by
      simpa [sub_eq_add_neg] using
        foldSite_slope_of_ne z hne.symm (-1) (by simpa [sub_eq_add_neg] using sν)
    have q3 : p1 = p3 + Pi.single ν 1 := foldSite_of_down sν'
    have sμ' := foldSite_slope_of_ne z hne 1 sμ
    have q4 : p3 = p2 + Pi.single μ 1 := by
      have := foldSite_of_up sμ'
      rwa [hsw] at this
    refine ⟨p2, ecorners p2 b2 (q4 ▸ b3) (q2 ▸ b0) (by rw [← q4, ← q3]; exact b1), ?_⟩
    rw [mirrorField_of_up y W sμ, mirrorField_of_down y W sν, mirrorField_of_down y W sν',
      mirrorField_of_up y W sμ', ← hp0, ← hp2, ← hp3, hev, hev, ← q2, ← q4, inv_inv]
    congr 1
    exact re_reversed_word_right _ _ _ _
  · have q1 : p0 = p1 + Pi.single μ 1 := foldSite_of_down sμ
    have q2 : p2 = p0 + Pi.single ν 1 := foldSite_of_up sν
    have sν' := foldSite_slope_of_ne z hne.symm 1 sν
    have q3 : p3 = p1 + Pi.single ν 1 := foldSite_of_up sν'
    have sμ' : foldSite m (z + unitStep (4 * m) ν + unitStep (4 * m) μ) μ =
        foldSite m (z + unitStep (4 * m) ν) μ - 1 := by
      simpa [sub_eq_add_neg] using
        foldSite_slope_of_ne z hne (-1) (by simpa [sub_eq_add_neg] using sμ)
    refine ⟨p1, ecorners p1 b1 (q1 ▸ b0) (q3 ▸ b3) (by rw [← q1, ← q2]; exact b2), ?_⟩
    rw [mirrorField_of_down y W sμ, mirrorField_of_up y W sν, mirrorField_of_up y W sν',
      mirrorField_of_down y W sμ', hsw, ← hp0, ← hp1, ← hp3, hev, hev, ← q1, ← q3, inv_inv]
    congr 1
    exact re_reversed_word_left _ _ _ _
  · have q1 : p0 = p1 + Pi.single μ 1 := foldSite_of_down sμ
    have q2 : p0 = p2 + Pi.single ν 1 := foldSite_of_down sν
    have sν' : foldSite m (z + unitStep (4 * m) μ + unitStep (4 * m) ν) ν =
        foldSite m (z + unitStep (4 * m) μ) ν - 1 := by
      simpa [sub_eq_add_neg] using
        foldSite_slope_of_ne z hne.symm (-1) (by simpa [sub_eq_add_neg] using sν)
    have q3 : p1 = p3 + Pi.single ν 1 := foldSite_of_down sν'
    have sμ' : foldSite m (z + unitStep (4 * m) ν + unitStep (4 * m) μ) μ =
        foldSite m (z + unitStep (4 * m) ν) μ - 1 := by
      simpa [sub_eq_add_neg] using
        foldSite_slope_of_ne z hne (-1) (by simpa [sub_eq_add_neg] using sμ)
    have q4 : p2 = p3 + Pi.single μ 1 := by
      have := foldSite_of_down sμ'
      rwa [hsw] at this
    refine ⟨p3, ecorners p3 b3 (q4 ▸ b2) (q3 ▸ b1) (by rw [← q4, ← q2]; exact b0), ?_⟩
    rw [mirrorField_of_down y W sμ, mirrorField_of_down y W sν, mirrorField_of_down y W sν',
      mirrorField_of_down y W sμ', hsw, ← hp1, ← hp2, ← hp3, hev, hev, ← q3, ← q4, inv_inv, inv_inv]
    congr 1
    exact re_cyclic_word _ _ _ _
theorem isCold_mirrorField [NeZero n] (hm : 0 < m) (y : TorusSite n) (W : TorusField n) {s : ℝ} (hs : 0 < s)
    (hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν → (∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d)) →
      curvature W (y + siteOfInt a) μ ν < s) : IsCold s (mirrorField m y W) := by
  intro z μ ν hlt
  obtain ⟨a, ha, he⟩ := exists_plaquetteEnergy_mirrorField hm y W z hlt.ne
  have h1 := hcold a μ ν hlt ha
  rw [plaquetteEnergy_eq_curvature_sq, plaquetteEnergy_eq_curvature_sq] at he
  have h2 : curvature (mirrorField m y W) z μ ν ^ 2 = curvature W (y + siteOfInt a) μ ν ^ 2 := by linarith
  have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  rw [show curvature (mirrorField m y W) z μ ν = curvature W (y + siteOfInt a) μ ν from h3]
  exact h1
theorem mirrorField_siteOfInt [NeZero n] (hm : 2 ≤ m) (y : TorusSite n) (W : TorusField n)
    (b : (Fin 4 → ℤ) × Fin 4) (hb : BondOffsetInBox m b) :
    mirrorField m y W (siteOfInt b.1) b.2 = W (y + siteOfInt b.1) b.2 := by
  have : NeZero (4 * m) := ⟨by omega⟩
  have hval : ∀ c : ℤ, |c| ≤ (m : ℤ) → ((c : ZMod (4 * m))).valMinAbs = c := by
    intro c hc
    rw [abs_le] at hc
    have h := ZMod.valMinAbs_spec ((c : ZMod (4 * m))) c
    refine h.mpr ⟨rfl, ?_⟩
    push_cast
    constructor <;> omega
  have hfold : ∀ h : Fin 4 → ℤ, OffsetInBox m h → foldSite m (siteOfInt h) = h := by
    intro h hh
    funext l
    simp only [foldSite, siteOfInt]
    rw [hval _ (hh l), triangleFold_eq_ite, if_pos (abs_le.mp (hh l))]
  have h1 : (siteOfInt b.1 : TorusSite (4 * m)) + unitStep (4 * m) b.2 = siteOfInt (b.1 + Pi.single b.2 1) := by
    rw [siteOfInt_add, unitStep_eq_siteOfInt]
  unfold mirrorField
  rw [h1, hfold _ hb.1, hfold _ hb.2, if_pos (by simp)]
end Plaquettes
end TorusMirror
end YangMills.Construction
end
