import YangMills.Construction.ColdChainAtEveryLevel.HomotopyFormulaProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.PinnedQuarticGaugeProof
import YangMills.Construction.HoleBesideASecondHole.AShellIsFilledProof
import YangMills.Construction.HoleBesideASecondHole.GaugesOnTwoPartsAreGlued
import YangMills.Construction.HoleBesideASecondHole.OscillationInAFlatBox
import YangMills.Construction.HoleBesideASecondHole.OscillationOnAPlaneOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.OrthantGluing
open LatticeFractionalIntegration BlockAverages ShellOrthant ShellFilling FlatBoxes
abbrev Site : Type := Lattice4
theorem norm_unitQuaternion_coe (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
def distOne (g : UnitQuaternion) : ℝ := ‖(g : ℍ[ℝ]) - 1‖
theorem distOne_nonneg (g : UnitQuaternion) : 0 ≤ distOne g := norm_nonneg _
theorem coe_mul_coe_inv (a : UnitQuaternion) : (a : ℍ[ℝ]) * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem distOne_mul_mul_inv_le (a a' y : UnitQuaternion) :
    distOne (a * y * a'⁻¹) ≤ distOne y + ‖(a : ℍ[ℝ]) - (a' : ℍ[ℝ])‖ := by
  unfold distOne
  have e : ((a * y * a'⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 =
      (a : ℍ[ℝ]) * ((y : ℍ[ℝ]) - 1) * ((a'⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        ((a : ℍ[ℝ]) - (a' : ℍ[ℝ])) * ((a'⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [Submonoid.coe_mul]
    have := coe_mul_coe_inv a'
    rw [mul_sub, sub_mul, sub_mul, mul_one, this]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_unitQuaternion_coe, one_mul, mul_one]
  exact le_rfl
theorem distOne_conj (a g : UnitQuaternion) : distOne (a * g * a⁻¹) = distOne g := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
def transitionGauge (γp γm : Site → UnitQuaternion) (x : Site) : UnitQuaternion := γp x * (γm x)⁻¹
theorem norm_transitionGauge_step_le (X : Site → Fin 4 → UnitQuaternion) (γp γm : Site → UnitQuaternion)
    (x : Site) (j : Fin 4) :
    ‖((transitionGauge γp γm (x + basisVector j) : UnitQuaternion) : ℍ[ℝ]) -
        ((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ])‖ ≤
      distOne (latticeGaugeTransform γp X x j) + distOne (latticeGaugeTransform γm X x j) := by
  set g := transitionGauge γp γm x with hg
  set g' := transitionGauge γp γm (x + basisVector j) with hg'
  set Yp := latticeGaugeTransform γp X x j with hYp
  set Ym := latticeGaugeTransform γm X x j with hYm
  have hrel : g * Ym = Yp * g' := by
    rw [hg, hg', hYp, hYm]
    unfold transitionGauge latticeGaugeTransform
    group
  have hrel' : (g : ℍ[ℝ]) * (Ym : ℍ[ℝ]) = (Yp : ℍ[ℝ]) * (g' : ℍ[ℝ]) := by
    rw [← Submonoid.coe_mul, ← Submonoid.coe_mul, hrel]
  have e : (g' : ℍ[ℝ]) - (g : ℍ[ℝ]) =
      (g : ℍ[ℝ]) * ((Ym : ℍ[ℝ]) - 1) - ((Yp : ℍ[ℝ]) - 1) * (g' : ℍ[ℝ]) := by
    rw [mul_sub, sub_mul, hrel']
    simp
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_unitQuaternion_coe, norm_unitQuaternion_coe]
  unfold distOne
  simp only [one_mul, mul_one]
  linarith
theorem mem_bondsOf {P : Finset Site} {b : Site × Fin 4} :
    b ∈ bondsOf P ↔ b.1 ∈ P ∧ b.1 + basisVector b.2 ∈ P := by apply _root_.YangMills.Construction.LeastQuarticGauge.mem_bondsOf <;> assumption
theorem mem_orientedPlaquettesOf {P : Finset Site} {p : Site × Fin 4 × Fin 4} :
    p ∈ orientedPlaquettesOf P ↔ p.1 ∈ P ∧ p.2.1 ≠ p.2.2 ∧ p.1 + basisVector p.2.1 ∈ P ∧
      p.1 + basisVector p.2.2 ∈ P ∧ p.1 + basisVector p.2.1 + basisVector p.2.2 ∈ P := by
  simp [orientedPlaquettesOf]
theorem basisVector_apply (j k : Fin 4) : basisVector j k = if k = j then 1 else 0 := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.StaircaseHomotopy.basisVector_apply <;> assumption
theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem sum_pow_four_le {α : Type} (s : Finset α) (g : α → ℝ) :
    (∑ x ∈ s, g x) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ x ∈ s, g x ^ 4 := by apply _root_.YangMills.Construction.PinnedGauge.sum_pow_four_le <;> assumption
theorem orthantLower_zero (l : ℝ) : orthantLower l 0 = -(1.9 * l) := by simp [orthantLower]
theorem orthantUpper_zero (l : ℝ) : orthantUpper l 0 = 1.9 * l := by simp [orthantUpper]
theorem orthantLower_one (l : ℝ) : orthantLower l 1 = -(l / 2) := by simp [orthantLower]
theorem orthantUpper_one (l : ℝ) : orthantUpper l 1 = 1.9 * l := by norm_num [orthantUpper]
theorem orthantLower_neg_one (l : ℝ) : orthantLower l (-1) = -(1.9 * l) := by norm_num [orthantLower]
theorem orthantUpper_neg_one (l : ℝ) : orthantUpper l (-1) = l / 2 := by simp [orthantUpper]
def slicePoint (i : Fin 4) (τ : ℤ) (x : Site) : Site := Function.update x i τ
theorem slicePoint_apply_self (i : Fin 4) (τ : ℤ) (x : Site) : slicePoint i τ x i = τ := by simp [slicePoint]
theorem slicePoint_apply_of_ne {i k : Fin 4} (τ : ℤ) (x : Site) (h : k ≠ i) : slicePoint i τ x k = x k := by
  simp [slicePoint, Function.update_of_ne h]
theorem slicePoint_add_basisVector_self (i : Fin 4) (τ : ℤ) (x : Site) :
    slicePoint i τ (x + basisVector i) = slicePoint i τ x := by
  funext k
  by_cases h : k = i
  · subst h
    simp [slicePoint_apply_self]
  · simp [slicePoint_apply_of_ne τ _ h, basisVector_apply, h]
theorem slicePoint_add_basisVector_of_ne {i j : Fin 4} (τ : ℤ) (x : Site) (hj : j ≠ i) :
    slicePoint i τ (x + basisVector j) = slicePoint i τ x + basisVector j := by
  funext k
  by_cases h : k = i
  · subst h
    simp [slicePoint_apply_self, basisVector_apply, hj.symm]
  · simp [slicePoint_apply_of_ne τ _ h]
theorem slicePoint_self (i : Fin 4) (x : Site) : slicePoint i (x i) x = x := by
  simp [slicePoint]
theorem isInShellOrthant_slicePoint (l : ℝ) (hl : 0 < l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4)
    (hsi : s i = 0) (τ : ℤ) (hτ : |(τ : ℝ) - o i| ≤ l / 2) (x : Site) (hx : IsInShellOrthant o l s x)
    (hxi : |(x i : ℝ) - o i| ≤ l / 2) :
    IsInShellOrthant o l s (slicePoint i τ x) := by
  obtain ⟨h1, j, hj⟩ := hx
  refine ⟨fun k => ?_, j, ?_⟩
  · by_cases hk : k = i
    · subst hk
      rw [slicePoint_apply_self, hsi, orthantLower_zero, orthantUpper_zero]
      have := abs_le.1 hτ
      constructor <;> linarith [this.1, this.2]
    · rw [slicePoint_apply_of_ne τ x hk]
      exact h1 k
  · have hji : j ≠ i := by
      rintro rfl
      linarith
    rw [slicePoint_apply_of_ne τ x hji]
    exact hj
theorem isInShellOrthant_update_one (l : ℝ) (hl : 0 < l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4)
    (hsi : s i = 0) (x : Site) (hx : IsInShellOrthant o l s x) (hxi : -(l / 2) ≤ (x i : ℝ) - o i) :
    IsInShellOrthant o l (Function.update s i 1) x := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun k => ?_, h2⟩
  by_cases hk : k = i
  · subst hk
    have := (h1 k).2
    rw [hsi, orthantUpper_zero] at this
    rw [Function.update_self, orthantLower_one, orthantUpper_one]
    exact ⟨hxi, this⟩
  · rw [Function.update_of_ne hk]
    exact h1 k
theorem isInShellOrthant_update_neg_one (l : ℝ) (hl : 0 < l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4)
    (hsi : s i = 0) (x : Site) (hx : IsInShellOrthant o l s x) (hxi : (x i : ℝ) - o i ≤ l / 2) :
    IsInShellOrthant o l (Function.update s i (-1)) x := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun k => ?_, h2⟩
  by_cases hk : k = i
  · subst hk
    have := (h1 k).1
    rw [hsi, orthantLower_zero] at this
    rw [Function.update_self, orthantLower_neg_one, orthantUpper_neg_one]
    exact ⟨this, hxi⟩
  · rw [Function.update_of_ne hk]
    exact h1 k
theorem isInShellOrthant_of_update_one (l : ℝ) (hl : 0 < l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4)
    (hsi : s i = 0) (x : Site) (hx : IsInShellOrthant o l (Function.update s i 1) x) :
    IsInShellOrthant o l s x := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun k => ?_, h2⟩
  by_cases hk : k = i
  · subst hk
    have := h1 k
    rw [Function.update_self, orthantLower_one, orthantUpper_one] at this
    rw [hsi, orthantLower_zero, orthantUpper_zero]
    exact ⟨by linarith [this.1], this.2⟩
  · have := h1 k
    rwa [Function.update_of_ne hk] at this
theorem isInShellOrthant_of_update_neg_one (l : ℝ) (hl : 0 < l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ)
    (i : Fin 4) (hsi : s i = 0) (x : Site) (hx : IsInShellOrthant o l (Function.update s i (-1)) x) :
    IsInShellOrthant o l s x := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun k => ?_, h2⟩
  by_cases hk : k = i
  · subst hk
    have := h1 k
    rw [Function.update_self, orthantLower_neg_one, orthantUpper_neg_one] at this
    rw [hsi, orthantLower_zero, orthantUpper_zero]
    exact ⟨this.1, by linarith [this.2]⟩
  · have := h1 k
    rwa [Function.update_of_ne hk] at this
theorem sum_comp_slicePoint_le (i : Fin 4) (τ : ℤ) (h : ℕ) (S Y : Finset Site) (F : Site → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hS : ∀ x ∈ S, τ - h ≤ x i ∧ x i ≤ τ) (hY : ∀ x ∈ S, slicePoint i τ x ∈ Y) :
    ∑ x ∈ S, F (slicePoint i τ x) ≤ ((h : ℝ) + 1) * ∑ y ∈ Y, F y := by
  classical
  have hmaps : ∀ x ∈ S, x i ∈ Finset.Icc (τ - h) τ := fun x hx => Finset.mem_Icc.2 (hS x hx)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ t ∈ Finset.Icc (τ - h) τ,
      ∑ x ∈ S with x i = t, F (slicePoint i τ x) ≤ ∑ y ∈ Y, F y := by
    intro t _
    have hinj : Set.InjOn (slicePoint i τ) (S.filter fun x => x i = t : Finset Site) := by
      intro a ha b hb hab
      have h1 := (Finset.mem_filter.1 ha).2
      have h2 := (Finset.mem_filter.1 hb).2
      funext k
      by_cases hk : k = i
      · subst hk
        omega
      · have := congrFun hab k
        rwa [slicePoint_apply_of_ne τ a hk, slicePoint_apply_of_ne τ b hk] at this
    rw [← Finset.sum_image (f := F) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hF x
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hY x (Finset.mem_filter.1 hx).1
  calc _ ≤ ∑ _t ∈ Finset.Icc (τ - h) τ, ∑ y ∈ Y, F y := Finset.sum_le_sum hinner
    _ = ((h : ℝ) + 1) * ∑ y ∈ Y, F y := by
      rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
      congr 1
      have : (τ + 1 - (τ - (h : ℤ))).toNat = h + 1 := by omega
      rw [this]
      push_cast
      ring
def slabWeight (τ : ℤ) (h : ℕ) (t : ℝ) : ℝ := max 0 (1 - ((τ : ℝ) - t) / h)
theorem slabWeight_nonneg (τ : ℤ) (h : ℕ) (t : ℝ) : 0 ≤ slabWeight τ h t := le_max_left _ _
theorem slabWeight_le_one (τ : ℤ) (h : ℕ) (hh : 0 < h) (t : ℝ) (ht : t ≤ τ) : slabWeight τ h t ≤ 1 := by
  unfold slabWeight
  refine max_le zero_le_one ?_
  have : 0 ≤ ((τ : ℝ) - t) / h := div_nonneg (by linarith) (by positivity)
  linarith
theorem slabWeight_self (τ : ℤ) (h : ℕ) : slabWeight τ h τ = 1 := by
  simp [slabWeight]
theorem slabWeight_eq_zero (τ : ℤ) (h : ℕ) (hh : 0 < h) (t : ℝ) (ht : t ≤ τ - h) : slabWeight τ h t = 0 := by
  unfold slabWeight
  refine max_eq_left ?_
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have : 1 ≤ ((τ : ℝ) - t) / h := by
    rw [le_div_iff₀ hh']
    linarith
  linarith
theorem abs_slabWeight_sub_le (τ : ℤ) (h : ℕ) (hh : 0 < h) (t t' : ℝ) :
    |slabWeight τ h t - slabWeight τ h t'| ≤ |t - t'| / h := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold slabWeight
  have := abs_max_sub_max_le_abs (1 - ((τ : ℝ) - t) / h) (1 - ((τ : ℝ) - t') / h) 0
  rw [max_comm 0, max_comm 0]
  refine this.trans (le_of_eq ?_)
  have e : 1 - ((τ : ℝ) - t) / h - (1 - ((τ : ℝ) - t') / h) = (t - t') / h := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hh']
theorem sum_indicator_le {α : Type} [DecidableEq α] (R B : Finset α) (f : α → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ R, (if b ∈ B then f b else 0) ≤ ∑ b ∈ B, f b := by apply _root_.YangMills.Construction.ShellFilling.Interpolation.sum_indicator_le <;> assumption
theorem add_basisVector_apply (x : Site) (j i : Fin 4) :
    (x + basisVector j) i = x i + if i = j then 1 else 0 := by
  simp [basisVector_apply]
theorem exists_glued_gauge_of_slab (Φ : ℝ → UnitQuaternion → UnitQuaternion) (hΦ0 : ∀ q, Φ 0 q = 1)
    (hΦ1 : ∀ q, Φ 1 q = q)
    (hΦL : ∀ (t t' : ℝ) (q q' : UnitQuaternion), 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 →
      distOne q ≤ 1 / 2 → distOne q' ≤ 1 / 2 →
      ‖((Φ t q : UnitQuaternion) : ℍ[ℝ]) - ((Φ t' q' : UnitQuaternion) : ℍ[ℝ])‖ ≤
        4 * (|t - t'| * distOne q + ‖(q : ℍ[ℝ]) - (q' : ℍ[ℝ])‖))
    (l : ℝ) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (i : Fin 4) (P Pp Pm : Finset Site) (hl : 100 ≤ l)
    (hsi : s i = 0)
    (hP : ∀ x, x ∈ P ↔ IsInShellOrthant o l s x)
    (hPp : ∀ x, x ∈ Pp ↔ IsInShellOrthant o l (Function.update s i 1) x)
    (hPm : ∀ x, x ∈ Pm ↔ IsInShellOrthant o l (Function.update s i (-1)) x)
    (X : Site → Fin 4 → UnitQuaternion) (γp γm : Site → UnitQuaternion) (τ : ℤ) (h : ℕ) (A Bd W0 : ℝ)
    (hτ : |(τ : ℝ) - o i| ≤ l / 4) (hh1 : l / 8 ≤ h) (hh2 : (h : ℝ) ≤ l / 8 + 1)
    (hp : ∑ b ∈ bondsOf Pp, distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4 ≤ A ^ 4)
    (hm : ∑ b ∈ bondsOf Pm, distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4 ≤ A ^ 4)
    (hBd : Bd ≤ 1 / 2) (hBd0 : 0 ≤ Bd)
    (hbd : ∀ x ∈ P, x i = τ → distOne (transitionGauge γp γm x) ≤ Bd)
    (w : Site → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hwb : ∀ x ∈ P, x i = τ → ∀ j, j ≠ i → x + basisVector j ∈ P →
      ‖((transitionGauge γp γm (x + basisVector j) : UnitQuaternion) : ℍ[ℝ]) -
        ((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ])‖ ≤ w x)
    (hW : ∑ x ∈ P.filter (fun x => x i = τ), w x ^ 4 ≤ W0) :
    ∃ γ : Site → UnitQuaternion, ∑ b ∈ bondsOf P, distOne (latticeGaugeTransform γ X b.1 b.2) ^ 4 ≤
      9 * A ^ 4 + 256 * (P.card : ℝ) * (4 * Bd / h) ^ 4 + 65536 * ((h : ℝ) + 1) * W0 := by
  classical
  have hl0 : 0 < l := by linarith
  have hhR : (0 : ℝ) < h := by linarith
  have hhpos : 0 < h := by exact_mod_cast hhR
  have hτ' := abs_le.1 hτ
  set D : ℝ := 4 * Bd / h with hD
  set At : Site → UnitQuaternion :=
    fun x => Φ (slabWeight τ h (x i)) (transitionGauge γp γm (slicePoint i τ x)) with hAt
  set G : Site → UnitQuaternion := fun x => if τ ≤ x i then γp x else At x * γm x with hG
  have G_low : ∀ x : Site, x i ≤ τ → G x = At x * γm x := by
    intro x hx
    by_cases hxe : x i = τ
    · have e1 : slicePoint i τ x = x := by
        rw [← hxe]
        exact slicePoint_self i x
      simp only [hG, hAt, hxe, le_refl, if_true, slabWeight_self, hΦ1, e1]
      unfold transitionGauge
      group
    · have : ¬ τ ≤ x i := by omega
      simp only [hG, this, if_false]
  have G_bot : ∀ x : Site, x i ≤ τ - h → G x = γm x := by
    intro x hx
    have hx2 : x i ≤ τ := by omega
    rw [G_low x hx2]
    have h3 : ((x i : ℤ) : ℝ) ≤ (τ : ℝ) - h := by exact_mod_cast hx
    simp only [hAt, slabWeight_eq_zero τ h hhpos _ h3, hΦ0, one_mul]
  have G_top : ∀ x : Site, τ ≤ x i → G x = γp x := by
    intro x hx
    simp only [hG, hx, if_true]
  set F1 : Site × Fin 4 → ℝ := fun b =>
    if b ∈ bondsOf Pp then distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4 else 0 with hF1
  set F2 : Site × Fin 4 → ℝ := fun b =>
    if b ∈ bondsOf Pm then distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4 else 0 with hF2
  set v : Site → ℝ := fun x => 64 * D ^ 4 + 16384 * w (slicePoint i τ x) ^ 4 with hv
  have hv0 : ∀ x, 0 ≤ v x := fun x => by
    have := hw (slicePoint i τ x)
    positivity
  set cond : Site → Prop := fun x => τ - h ≤ x i ∧ x i ≤ τ with hcond
  set F3 : Site × Fin 4 → ℝ := fun b => if cond b.1 then v b.1 else 0 with hF3
  have hF1n : ∀ b, 0 ≤ F1 b := fun b => by
    simp only [hF1]
    split_ifs <;> positivity
  have hF2n : ∀ b, 0 ≤ F2 b := fun b => by
    simp only [hF2]
    split_ifs <;> positivity
  have hF3n : ∀ b, 0 ≤ F3 b := fun b => by
    simp only [hF3]
    split_ifs
    · exact hv0 _
    · exact le_rfl
  have point : ∀ b ∈ bondsOf P,
      distOne (latticeGaugeTransform G X b.1 b.2) ^ 4 ≤ F1 b + 8 * F2 b + F3 b := by
    rintro ⟨x, j⟩ hb
    obtain ⟨hx, hx'⟩ := mem_bondsOf.1 hb
    simp only at hx hx' ⊢
    have n1 := hF1n (x, j)
    have n2 := hF2n (x, j)
    have n3 := hF3n (x, j)
    have hxs := (hP x).1 hx
    have hxs' := (hP _).1 hx'
    have hstep : (x + basisVector j) i = x i + if i = j then 1 else 0 := add_basisVector_apply x j i
    by_cases c1 : τ ≤ x i ∧ τ ≤ (x + basisVector j) i
    · have e : latticeGaugeTransform G X x j = latticeGaugeTransform γp X x j := by
        unfold latticeGaugeTransform
        rw [G_top x c1.1, G_top _ c1.2]
      have m1 : (τ : ℝ) ≤ x i := by exact_mod_cast c1.1
      have m2 : (τ : ℝ) ≤ ((x + basisVector j) i : ℤ) := by exact_mod_cast c1.2
      have hbp : (x, j) ∈ bondsOf Pp := mem_bondsOf.2
        ⟨(hPp _).2 (isInShellOrthant_update_one l hl0 o s i hsi x hxs (by linarith [hτ'.1])),
          (hPp _).2 (isInShellOrthant_update_one l hl0 o s i hsi _ hxs' (by linarith [hτ'.1]))⟩
      have : F1 (x, j) = distOne (latticeGaugeTransform γp X x j) ^ 4 := by simp [hF1, hbp]
      rw [e, ← this]
      linarith
    · by_cases c2 : x i ≤ τ - h ∧ (x + basisVector j) i ≤ τ - h
      · have e : latticeGaugeTransform G X x j = latticeGaugeTransform γm X x j := by
          unfold latticeGaugeTransform
          rw [G_bot x c2.1, G_bot _ c2.2]
        have m1 : (x i : ℝ) ≤ (τ : ℝ) - h := by exact_mod_cast c2.1
        have m2 : (((x + basisVector j) i : ℤ) : ℝ) ≤ (τ : ℝ) - h := by exact_mod_cast c2.2
        have hbp : (x, j) ∈ bondsOf Pm := mem_bondsOf.2
          ⟨(hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi x hxs (by linarith [hτ'.2])),
            (hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi _ hxs' (by linarith [hτ'.2]))⟩
        have : F2 (x, j) = distOne (latticeGaugeTransform γm X x j) ^ 4 := by simp [hF2, hbp]
        rw [e, ← this]
        linarith
      · have hst : (x + basisVector j) i = x i ∨ (x + basisVector j) i = x i + 1 := by
          rw [hstep]
          split_ifs
          · right; rfl
          · left; simp
        have b1 : x i ≤ τ := by omega
        have b2 : (x + basisVector j) i ≤ τ := by omega
        have b3 : τ - h ≤ x i := by omega
        have b4 : τ - h ≤ (x + basisVector j) i := by omega
        have r1 : (x i : ℝ) ≤ τ := by exact_mod_cast b1
        have r2 : (((x + basisVector j) i : ℤ) : ℝ) ≤ τ := by exact_mod_cast b2
        have r3 : (τ : ℝ) - h ≤ x i := by exact_mod_cast b3
        have r4 : (τ : ℝ) - h ≤ ((x + basisVector j) i : ℤ) := by exact_mod_cast b4
        have u1 : |(x i : ℝ) - o i| ≤ l / 2 := abs_le.2 ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
        have u2 : |(((x + basisVector j) i : ℤ) : ℝ) - o i| ≤ l / 2 :=
          abs_le.2 ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
        have hτ2 : |(τ : ℝ) - o i| ≤ l / 2 := by linarith
        have p1 : slicePoint i τ x ∈ P :=
          (hP _).2 (isInShellOrthant_slicePoint l hl0 o s i hsi τ hτ2 x hxs u1)
        have p2 : slicePoint i τ (x + basisVector j) ∈ P :=
          (hP _).2 (isInShellOrthant_slicePoint l hl0 o s i hsi τ hτ2 _ hxs' u2)
        have q1 := hbd _ p1 (slicePoint_apply_self i τ x)
        have q2 := hbd _ p2 (slicePoint_apply_self i τ _)
        have t1 := slabWeight_nonneg τ h (x i)
        have t2 := slabWeight_le_one τ h hhpos (x i) r1
        have t3 := slabWeight_nonneg τ h ((x + basisVector j) i)
        have t4 := slabWeight_le_one τ h hhpos _ r2
        have hA := hΦL _ _ _ _ t1 t2 t3 t4 (q1.trans hBd) (q2.trans hBd)
        have hbm : (x, j) ∈ bondsOf Pm := mem_bondsOf.2
          ⟨(hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi x hxs (by linarith [hτ'.2])),
            (hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi _ hxs' (by linarith [hτ'.2]))⟩
        have e : latticeGaugeTransform G X x j =
            At x * latticeGaugeTransform γm X x j * (At (x + basisVector j))⁻¹ := by
          unfold latticeGaugeTransform
          rw [G_low x b1, G_low _ b2]
          group
        have hZ := distOne_mul_mul_inv_le (At x) (At (x + basisVector j)) (latticeGaugeTransform γm X x j)
        rw [← e] at hZ
        have hcl : |slabWeight τ h (x i) - slabWeight τ h ((x + basisVector j) i)| *
              distOne (transitionGauge γp γm (slicePoint i τ x)) +
            ‖((transitionGauge γp γm (slicePoint i τ x) : UnitQuaternion) : ℍ[ℝ]) -
              ((transitionGauge γp γm (slicePoint i τ (x + basisVector j)) : UnitQuaternion) : ℍ[ℝ])‖ ≤
            Bd / h + w (slicePoint i τ x) := by
          by_cases hj : j = i
          · subst hj
            rw [slicePoint_add_basisVector_self, sub_self, norm_zero, add_zero]
            have h5 := abs_slabWeight_sub_le τ h hhpos (x j) ((x + basisVector j) j)
            have h6 : (((x + basisVector j) j : ℤ) : ℝ) = (x j : ℝ) + 1 := by
              rw [hstep]
              simp
            rw [h6] at h5
            have h7 : |(x j : ℝ) - ((x j : ℝ) + 1)| = 1 := by
              rw [show (x j : ℝ) - ((x j : ℝ) + 1) = -1 by ring]
              simp
            rw [h7] at h5
            have h8 := hw (slicePoint j τ x)
            rw [h6]
            calc _ ≤ 1 / (h : ℝ) * Bd := by
                  refine mul_le_mul ?_ q1 (distOne_nonneg _) (by positivity)
                  exact h5
              _ ≤ Bd / h + w (slicePoint j τ x) := by
                  have : 1 / (h : ℝ) * Bd = Bd / h := by ring
                  linarith
          · have hij : i ≠ j := fun h => hj h.symm
            have e1 : (x + basisVector j) i = x i := by
              rw [hstep]
              simp [hij]
            rw [e1, sub_self, abs_zero, zero_mul, zero_add, slicePoint_add_basisVector_of_ne τ x hj,
              norm_sub_rev]
            rw [slicePoint_add_basisVector_of_ne τ x hj] at p2
            have := hwb _ p1 (slicePoint_apply_self i τ x) j hj p2
            have h9 : 0 ≤ Bd / h := by positivity
            linarith
        have hAx : ‖((At x : UnitQuaternion) : ℍ[ℝ]) - ((At (x + basisVector j) : UnitQuaternion) : ℍ[ℝ])‖ ≤
            D + 4 * w (slicePoint i τ x) := by
          calc _ ≤ _ := hA
            _ ≤ 4 * (Bd / h + w (slicePoint i τ x)) := by linarith
            _ = _ := by
              rw [hD]
              ring
        set a := distOne (latticeGaugeTransform γm X x j) with ha
        have hZ2 : distOne (latticeGaugeTransform G X x j) ≤ a + (D + 4 * w (slicePoint i τ x)) := by
          linarith
        have hf2 : F2 (x, j) = a ^ 4 := by simp [hF2, hbm, ha]
        have hf3 : F3 (x, j) = v x := by
          have : cond x := ⟨b3, b1⟩
          simp [hF3, this]
        rw [hf2, hf3]
        have s1 := add_pow_four_le a (D + 4 * w (slicePoint i τ x))
        have s2 := add_pow_four_le D (4 * w (slicePoint i τ x))
        have s3 : distOne (latticeGaugeTransform G X x j) ^ 4 ≤ (a + (D + 4 * w (slicePoint i τ x))) ^ 4 :=
          pow_le_pow_left₀ (distOne_nonneg _) hZ2 4
        have s4 : (4 * w (slicePoint i τ x)) ^ 4 = 256 * w (slicePoint i τ x) ^ 4 := by ring
        simp only [hv]
        rw [s4] at s2
        linarith
  refine ⟨G, ?_⟩
  have hS1 : ∑ b ∈ bondsOf P, F1 b ≤ A ^ 4 :=
    (sum_indicator_le (bondsOf P) (bondsOf Pp) (fun b => distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4)
      (fun b => by have := distOne_nonneg (latticeGaugeTransform γp X b.1 b.2); positivity)).trans hp
  have hS2 : ∑ b ∈ bondsOf P, F2 b ≤ A ^ 4 :=
    (sum_indicator_le (bondsOf P) (bondsOf Pm) (fun b => distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4)
      (fun b => by have := distOne_nonneg (latticeGaugeTransform γm X b.1 b.2); positivity)).trans hm
  have hS3 : ∑ b ∈ bondsOf P, F3 b ≤ 256 * (P.card : ℝ) * D ^ 4 + 65536 * ((h : ℝ) + 1) * W0 := by
    have hsub : bondsOf P ⊆ P ×ˢ (Finset.univ : Finset (Fin 4)) := by
      intro b hb
      simp [(mem_bondsOf.1 hb).1]
    set S := P.filter cond with hSdef
    have h1 : ∑ b ∈ bondsOf P, F3 b ≤ ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), F3 b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hF3n b
    have h2 : ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), F3 b = 4 * ∑ x ∈ S, v x := by
      rw [Finset.sum_product]
      simp only [hF3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, hSdef, Finset.sum_filter]
      simp only [Nat.cast_ofNat]
      refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
      split_ifs <;> rfl
    have h3 : ∑ x ∈ S, v x = (S.card : ℝ) * (64 * D ^ 4) + 16384 * ∑ x ∈ S, w (slicePoint i τ x) ^ 4 := by
      simp only [hv]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have h4 : ∑ x ∈ S, w (slicePoint i τ x) ^ 4 ≤ ((h : ℝ) + 1) * W0 := by
      have hf := sum_comp_slicePoint_le i τ h S (P.filter fun x => x i = τ) (fun x => w x ^ 4)
        (fun x => by have := hw x; positivity)
        (fun x hx => (Finset.mem_filter.1 hx).2)
        (by
          intro x hx
          obtain ⟨hxP, hc1, hc2⟩ := Finset.mem_filter.1 hx
          have r1 : (x i : ℝ) ≤ τ := by exact_mod_cast hc2
          have r3 : (τ : ℝ) - h ≤ x i := by exact_mod_cast hc1
          have u1 : |(x i : ℝ) - o i| ≤ l / 2 := abs_le.2 ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩
          have hτ2 : |(τ : ℝ) - o i| ≤ l / 2 := by linarith
          exact Finset.mem_filter.2
            ⟨(hP _).2 (isInShellOrthant_slicePoint l hl0 o s i hsi τ hτ2 x ((hP x).1 hxP) u1),
              slicePoint_apply_self i τ x⟩)
      exact hf.trans (mul_le_mul_of_nonneg_left hW (by positivity))
    have h5 : (S.card : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have hD4 : 0 ≤ D ^ 4 := by positivity
    have h6 : (S.card : ℝ) * D ^ 4 ≤ (P.card : ℝ) * D ^ 4 := mul_le_mul_of_nonneg_right h5 hD4
    rw [h2, h3] at h1
    linarith
  calc ∑ b ∈ bondsOf P, distOne (latticeGaugeTransform G X b.1 b.2) ^ 4
      ≤ ∑ b ∈ bondsOf P, (F1 b + 8 * F2 b + F3 b) := Finset.sum_le_sum point
    _ = ∑ b ∈ bondsOf P, F1 b + 8 * ∑ b ∈ bondsOf P, F2 b + ∑ b ∈ bondsOf P, F3 b := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith
theorem distOne_mul_inv (g κ : UnitQuaternion) : distOne (g * κ⁻¹) = ‖(g : ℍ[ℝ]) - (κ : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem norm_mul_inv_sub_mul_inv (g g' κ : UnitQuaternion) :
    ‖((g' * κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g * κ⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ =
      ‖(g' : ℍ[ℝ]) - (g : ℍ[ℝ])‖ := by
  have e : ((g' * κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g * κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      ((g' : ℍ[ℝ]) - (g : ℍ[ℝ])) * ((κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [Submonoid.coe_mul]
    rw [sub_mul]
  rw [e, norm_mul, norm_unitQuaternion_coe, mul_one]
theorem orthant_bounds (l : ℝ) (hl : 0 < l) (t : ℤ) :
    -(1.9 * l) ≤ orthantLower l t ∧ orthantUpper l t ≤ 1.9 * l := by
  unfold orthantLower orthantUpper
  split_ifs with h1 h2 h2
  · omega
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
theorem card_le_of_isInShellOrthant (l : ℝ) (hl : 100 ≤ l) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ) (P : Finset Site)
    (hP : ∀ x, x ∈ P ↔ IsInShellOrthant o l s x) : (P.card : ℝ) ≤ (4 * l) ^ 4 := by
  classical
  have hl0 : 0 < l := by linarith
  set lo : Site := fun k => ⌈o k - 1.9 * l⌉ with hlo
  set hi : Site := fun k => ⌊o k + 1.9 * l⌋ with hhi
  have hsub : P ⊆ boxBetween lo hi := by
    intro x hx
    obtain ⟨h1, -⟩ := (hP x).1 hx
    simp only [boxBetween, Fintype.mem_piFinset, Finset.mem_Icc]
    intro k
    have h2 := h1 k
    have h3 := orthant_bounds l hl0 (s k)
    exact ⟨Int.ceil_le.2 (by linarith [h2.1, h3.1]), Int.le_floor.2 (by linarith [h2.2, h3.2])⟩
  have h1 : (P.card : ℝ) ≤ ((boxBetween lo hi).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ?_
  have h2 : ((boxBetween lo hi).card : ℝ) = ∏ k, (((Finset.Icc (lo k) (hi k)).card : ℕ) : ℝ) := by
    simp [boxBetween, Fintype.card_piFinset]
  rw [h2]
  have h3 : ∀ k ∈ (Finset.univ : Finset (Fin 4)), (((Finset.Icc (lo k) (hi k)).card : ℕ) : ℝ) ≤ 4 * l := by
    intro k _
    rw [Int.card_Icc]
    by_cases hz : 0 ≤ hi k + 1 - lo k
    · have e : (((hi k + 1 - lo k).toNat : ℕ) : ℝ) = ((hi k + 1 - lo k : ℤ) : ℝ) := by
        have := Int.toNat_of_nonneg hz
        exact_mod_cast this
      rw [e]
      push_cast
      have a1 : (hi k : ℝ) ≤ o k + 1.9 * l := Int.floor_le _
      have a2 : o k - 1.9 * l ≤ (lo k : ℝ) := Int.le_ceil _
      linarith
    · have : (hi k + 1 - lo k).toNat = 0 := by omega
      rw [this]
      push_cast
      linarith
  calc ∏ k, (((Finset.Icc (lo k) (hi k)).card : ℕ) : ℝ) ≤ ∏ _k : Fin 4, 4 * l :=
        Finset.prod_le_prod (fun _ _ => by positivity) h3
    _ = (4 * l) ^ 4 := by simp
theorem glued_bound_le (l : ℝ) (hl : 100 ≤ l) (h : ℕ) (hh1 : l / 8 ≤ (h : ℝ)) (hh2 : (h : ℝ) ≤ l / 8 + 1)
    (A C1 : ℝ) (hA0 : 0 ≤ A) (hC1p : 1 ≤ C1) (Pc : ℕ) (hcard : (Pc : ℝ) ≤ (4 * l) ^ 4) (E4 : ℝ)
    (hE4 : E4 = 4096 * A ^ 4 / l) :
    9 * A ^ 4 + 256 * (Pc : ℝ) * (4 * (C1 * A) / h) ^ 4 + 65536 * ((h : ℝ) + 1) * E4 ≤
      ((1 + (9 + 256 * (128 * C1) ^ 4 + 65536 * 4096)) * A) ^ 4 := by
  have hl0 : 0 < l := by linarith
  set Q : ℝ := 9 + 256 * (128 * C1) ^ 4 + 65536 * 4096 with hQ
  have hQ0 : 0 < Q := by positivity
  have hhR : (0 : ℝ) < h := by linarith
  have hBd : 4 * (C1 * A) / h ≤ 32 * C1 * A / l := by
    rw [div_le_div_iff₀ hhR hl0]
    have h0 : 0 ≤ C1 * A := by positivity
    nlinarith
  have hB0 : 0 ≤ 4 * (C1 * A) / h := by positivity
  have hD4 : (4 * (C1 * A) / h) ^ 4 ≤ (32 * C1 * A / l) ^ 4 := pow_le_pow_left₀ hB0 hBd 4
  have t1 : 256 * (Pc : ℝ) * (4 * (C1 * A) / h) ^ 4 ≤ 256 * (128 * C1) ^ 4 * A ^ 4 := by
    calc 256 * (Pc : ℝ) * (4 * (C1 * A) / h) ^ 4
        ≤ 256 * (4 * l) ^ 4 * (32 * C1 * A / l) ^ 4 := by
          refine mul_le_mul ?_ hD4 (by positivity) (by positivity)
          linarith
      _ = 256 * (128 * C1) ^ 4 * A ^ 4 := by
          field_simp
          ring
  have t2 : 65536 * ((h : ℝ) + 1) * E4 ≤ 65536 * 4096 * A ^ 4 := by
    rw [hE4]
    have e : 65536 * ((h : ℝ) + 1) * (4096 * A ^ 4 / l) =
        65536 * 4096 * A ^ 4 * (((h : ℝ) + 1) / l) := by
      ring
    rw [e]
    have h3 : ((h : ℝ) + 1) / l ≤ 1 := by
      rw [div_le_one hl0]
      linarith
    have h4 : 0 ≤ 65536 * 4096 * A ^ 4 := by positivity
    calc _ ≤ 65536 * 4096 * A ^ 4 * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ = _ := by ring
  rw [mul_pow]
  have h5 : 1 + Q ≤ (1 + Q) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h6 : 0 ≤ A ^ 4 := by positivity
  have h7 : Q * A ^ 4 ≤ (1 + Q) ^ 4 * A ^ 4 := mul_le_mul_of_nonneg_right (by linarith) h6
  have e : 9 * A ^ 4 + 256 * (128 * C1) ^ 4 * A ^ 4 + 65536 * 4096 * A ^ 4 = Q * A ^ 4 := by
    rw [hQ]
    ring
  linarith
set_option maxHeartbeats 1000000 in
theorem orthantGaugeGluing (hPl : ShellSlices.shellSliceOscillationStatement)
    (hSeg : GroupPaths.ExistsPathFromOne) : ShellOrthant.orthantGaugeGluingStatement := by
  classical
  obtain ⟨Cp, hCp, hplane⟩ := hPl
  obtain ⟨Φ, hΦ0, hΦ1, -, hΦL⟩ := hSeg
  intro c K hc hK
  set C1 : ℝ := 1 + 4096 * Cp with hC1
  have hC1p : 1 ≤ C1 := by
    rw [hC1]
    linarith
  set Q : ℝ := 9 + 256 * (128 * C1) ^ 4 + 65536 * 4096 with hQ
  refine ⟨min c (1 / (2 * C1 * K)), (1 + Q) * K, lt_min hc (by positivity), by positivity, ?_⟩
  intro l o s i P Pp Pm hl hs hsi hP hPp hPm gp gm X ε h0 h1 h2
  have hl0 : 0 < l := by linarith
  have hεc : ε ≤ c := h1.trans (min_le_left _ _)
  set A : ℝ := K * ε with hA
  have hA0 : 0 ≤ A := by positivity
  have hC1A : C1 * A ≤ 1 / 2 := by
    have h3 := h1.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h3
    have e : C1 * A = ε * (2 * C1 * K) / 2 := by
      rw [hA]
      ring
    rw [e]
    linarith
  have hsubp : ∀ x ∈ Pp, x ∈ P := fun x hx =>
    (hP x).2 (isInShellOrthant_of_update_one l hl0 o s i hsi x ((hPp x).1 hx))
  have hsubm : ∀ x ∈ Pm, x ∈ P := fun x hx =>
    (hP x).2 (isInShellOrthant_of_update_neg_one l hl0 o s i hsi x ((hPm x).1 hx))
  have hmono : ∀ Q' : Finset Site, (∀ x ∈ Q', x ∈ P) → _root_.YangMills.Construction.ShellFilling.plaquetteDefect Q' X ≤ _root_.YangMills.Construction.ShellFilling.plaquetteDefect P X := by
    intro Q' hQ'
    unfold _root_.YangMills.Construction.ShellFilling.plaquetteDefect
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro p hp
    rw [mem_orientedPlaquettesOf] at hp ⊢
    obtain ⟨a1, a2, a3, a4, a5⟩ := hp
    exact ⟨hQ' _ a1, a2, hQ' _ a3, hQ' _ a4, hQ' _ a5⟩
  obtain ⟨γp, hγp⟩ := gp X ε h0 hεc ((hmono _ hsubp).trans h2)
  obtain ⟨γm, hγm⟩ := gm X ε h0 hεc ((hmono _ hsubm).trans h2)
  have hp : ∑ b ∈ bondsOf Pp, distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4 ≤ A ^ 4 := hγp
  have hm : ∑ b ∈ bondsOf Pm, distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4 ≤ A ^ 4 := hγm
  set gg : Site × Fin 4 → ℝ := fun b => if b ∈ bondsOf Pp ∧ b ∈ bondsOf Pm then
    distOne (latticeGaugeTransform γp X b.1 b.2) + distOne (latticeGaugeTransform γm X b.1 b.2) else 0
    with hgg
  have hgg0 : ∀ b, 0 ≤ gg b := fun b => by
    simp only [hgg]
    split_ifs
    · exact add_nonneg (distOne_nonneg _) (distOne_nonneg _)
    · exact le_rfl
  set w : Site → ℝ := fun x => ∑ j, gg (x, j) with hwdef
  have hw : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun j _ => hgg0 (x, j)
  set Fp : Site × Fin 4 → ℝ := fun b =>
    if b ∈ bondsOf Pp then distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4 else 0 with hFp
  set Fm : Site × Fin 4 → ℝ := fun b =>
    if b ∈ bondsOf Pm then distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4 else 0 with hFm
  have hFpn : ∀ b, 0 ≤ Fp b := fun b => by
    simp only [hFp]
    split_ifs <;> positivity
  have hFmn : ∀ b, 0 ≤ Fm b := fun b => by
    simp only [hFm]
    split_ifs <;> positivity
  have hgg4 : ∀ b, gg b ^ 4 ≤ 8 * (Fp b + Fm b) := by
    intro b
    by_cases hb : b ∈ bondsOf Pp ∧ b ∈ bondsOf Pm
    · have e1 : gg b = distOne (latticeGaugeTransform γp X b.1 b.2) +
          distOne (latticeGaugeTransform γm X b.1 b.2) := by simp [hgg, hb]
      have e2 : Fp b = distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4 := by simp [hFp, hb.1]
      have e3 : Fm b = distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4 := by simp [hFm, hb.2]
      rw [e1, e2, e3]
      exact add_pow_four_le _ _
    · have e1 : gg b = 0 := by simp only [hgg, hb, if_false]
      rw [e1]
      have := hFpn b
      have := hFmn b
      norm_num
      linarith
  have hS0 : ∑ x ∈ P, w x ^ 4 ≤ 1024 * A ^ 4 := by
    have e1 : ∀ x, w x ^ 4 ≤ 64 * ∑ j, gg (x, j) ^ 4 := by
      intro x
      have := sum_pow_four_le Finset.univ (fun j => gg (x, j))
      simp only [Finset.card_univ, Fintype.card_fin] at this
      norm_num at this
      exact this
    have e2 : ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), Fp b ≤ A ^ 4 :=
      (sum_indicator_le _ (bondsOf Pp) (fun b => distOne (latticeGaugeTransform γp X b.1 b.2) ^ 4)
        (fun b => by have := distOne_nonneg (latticeGaugeTransform γp X b.1 b.2); positivity)).trans hp
    have e3 : ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), Fm b ≤ A ^ 4 :=
      (sum_indicator_le _ (bondsOf Pm) (fun b => distOne (latticeGaugeTransform γm X b.1 b.2) ^ 4)
        (fun b => by have := distOne_nonneg (latticeGaugeTransform γm X b.1 b.2); positivity)).trans hm
    calc ∑ x ∈ P, w x ^ 4 ≤ ∑ x ∈ P, 64 * ∑ j, gg (x, j) ^ 4 := Finset.sum_le_sum fun x _ => e1 x
      _ = 64 * ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), gg b ^ 4 := by
          rw [← Finset.mul_sum, Finset.sum_product]
      _ ≤ 64 * ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), 8 * (Fp b + Fm b) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hgg4 b) (by norm_num)
      _ = 512 * (∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), Fp b +
            ∑ b ∈ P ×ˢ (Finset.univ : Finset (Fin 4)), Fm b) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          ring
      _ ≤ 1024 * A ^ 4 := by linarith
  set T : Finset ℤ := Finset.Icc ⌈o i - l / 4⌉ ⌊o i + l / 4⌋ with hT
  have hTcard : l / 4 ≤ (T.card : ℝ) := by
    rw [hT, Int.card_Icc]
    have a1 := Int.lt_floor_add_one (o i + l / 4)
    have a2 := Int.ceil_lt_add_one (o i - l / 4)
    have hz : (l / 4 : ℝ) ≤ ((⌊o i + l / 4⌋ + 1 - ⌈o i - l / 4⌉ : ℤ) : ℝ) := by
      push_cast
      linarith
    have hz0 : 0 ≤ ⌊o i + l / 4⌋ + 1 - ⌈o i - l / 4⌉ := by
      have : (0 : ℝ) ≤ ((⌊o i + l / 4⌋ + 1 - ⌈o i - l / 4⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    have e : (((⌊o i + l / 4⌋ + 1 - ⌈o i - l / 4⌉).toNat : ℕ) : ℝ) =
        ((⌊o i + l / 4⌋ + 1 - ⌈o i - l / 4⌉ : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hz0
      exact_mod_cast this
    rw [e]
    exact hz
  have hTpos : (0 : ℝ) < T.card := by linarith
  have hTne : T.Nonempty := by
    apply Finset.card_pos.1
    exact_mod_cast hTpos
  set sT : Finset Site := P.filter fun x => x i ∈ T with hsT
  have hmaps : ∀ x ∈ sT, x i ∈ T := fun x hx => (Finset.mem_filter.1 hx).2
  have hsumT : ∑ t ∈ T, ∑ x ∈ sT with x i = t, w x ^ 4 ≤ 1024 * A ^ 4 := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => ?_) hS0
    have := hw x
    positivity
  obtain ⟨τ, hτT, hτ⟩ := Finset.exists_le_of_sum_le hTne
    (f := fun t => ∑ x ∈ sT with x i = t, w x ^ 4) (g := fun _ => 1024 * A ^ 4 / T.card) (by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hTpos.ne']
      exact hsumT)
  have hτabs : |(τ : ℝ) - o i| ≤ l / 4 := by
    obtain ⟨b1, b2⟩ := Finset.mem_Icc.1 hτT
    have c1 := Int.ceil_le.1 b1
    have c2 := Int.le_floor.1 b2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hτ' := abs_le.1 hτabs
  set Y : Finset Site := P.filter fun x => x i = τ with hY
  have hYe : (sT.filter fun x => x i = τ) = Y := by
    ext x
    simp only [hsT, hY, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a, _⟩, b⟩
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      exact ⟨⟨a, b ▸ hτT⟩, b⟩
  obtain ⟨lam, hlam0, hlam4⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ^ 4 = l := by
    refine ⟨Real.sqrt (Real.sqrt l), Real.sqrt_pos.2 (Real.sqrt_pos.2 hl0), ?_⟩
    have h3 : Real.sqrt (Real.sqrt l) ^ 2 = Real.sqrt l := Real.sq_sqrt (Real.sqrt_nonneg l)
    have h4 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl0.le
    calc Real.sqrt (Real.sqrt l) ^ 4 = (Real.sqrt (Real.sqrt l) ^ 2) ^ 2 := by ring
      _ = l := by rw [h3, h4]
  set E : ℝ := 8 * A / lam with hE
  have hE0 : 0 ≤ E := by positivity
  have hE4 : E ^ 4 = 4096 * A ^ 4 / l := by
    rw [hE, div_pow, mul_pow, hlam4]
    norm_num
  have hWE : ∑ x ∈ Y, w x ^ 4 ≤ E ^ 4 := by
    rw [← hYe, hE4]
    refine le_trans hτ ?_
    have hA4 : 0 ≤ 1024 * A ^ 4 := by positivity
    calc 1024 * A ^ 4 / T.card ≤ 1024 * A ^ 4 / (l / 4) :=
          div_le_div_of_nonneg_left hA4 (by positivity) hTcard
      _ = 4096 * A ^ 4 / l := by
          field_simp
          ring
  have hYmem : ∀ x, x ∈ Y ↔ IsInShellOrthant o l s x ∧ x i = τ := by
    intro x
    rw [hY, Finset.mem_filter, hP]
  have hbond : ∀ x ∈ Y, ∀ j, x + basisVector j ∈ Y →
      ‖((transitionGauge γp γm (x + basisVector j) : UnitQuaternion) : ℍ[ℝ]) -
        ((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ])‖ ≤ w x := by
    intro x hx j hxj
    obtain ⟨a1, a2⟩ := (hYmem x).1 hx
    obtain ⟨b1, b2⟩ := (hYmem _).1 hxj
    have r1 : ((x i : ℤ) : ℝ) = τ := by exact_mod_cast a2
    have r2 : (((x + basisVector j) i : ℤ) : ℝ) = τ := by exact_mod_cast b2
    have hbp : (x, j) ∈ bondsOf Pp := mem_bondsOf.2
      ⟨(hPp _).2 (isInShellOrthant_update_one l hl0 o s i hsi x a1 (by rw [r1]; linarith [hτ'.1])),
        (hPp _).2 (isInShellOrthant_update_one l hl0 o s i hsi _ b1 (by rw [r2]; linarith [hτ'.1]))⟩
    have hbm : (x, j) ∈ bondsOf Pm := mem_bondsOf.2
      ⟨(hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi x a1 (by rw [r1]; linarith [hτ'.2])),
        (hPm _).2 (isInShellOrthant_update_neg_one l hl0 o s i hsi _ b1 (by rw [r2]; linarith [hτ'.2]))⟩
    have e1 : gg (x, j) = distOne (latticeGaugeTransform γp X x j) +
        distOne (latticeGaugeTransform γm X x j) := by
      simp [hgg, hbp, hbm]
    have e2 : gg (x, j) ≤ w x :=
      Finset.single_le_sum (f := fun j => gg (x, j)) (fun j _ => hgg0 (x, j)) (Finset.mem_univ j)
    have := norm_transitionGauge_step_le X γp γm x j
    linarith
  have hosc := hplane l o s i τ Y (fun x => ((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ])) w E hl hs hsi
    (by linarith) hYmem hE0 hw hbond hWE
  have hdiff : ∀ x ∈ Y, ∀ y ∈ Y,
      ‖((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ]) -
        ((transitionGauge γp γm y : UnitQuaternion) : ℍ[ℝ])‖ ≤ C1 * A := by
    intro x hx y hy
    have h3 := hosc x hx y hy
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) (h3.trans ?_)
    rw [hE4]
    have e : Cp * l * (4096 * A ^ 4 / l) = 4096 * Cp * A ^ 4 := by
      field_simp
    have e2 : (C1 * A) ^ 4 = C1 ^ 4 * A ^ 4 := by ring
    rw [e, e2]
    have hA4 : 0 ≤ A ^ 4 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hA4
    have h4 : C1 ≤ C1 ^ 4 := le_self_pow₀ hC1p (by norm_num)
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : UnitQuaternion, ∀ x ∈ Y,
      ‖((transitionGauge γp γm x : UnitQuaternion) : ℍ[ℝ]) - (κ : ℍ[ℝ])‖ ≤ C1 * A := by
    by_cases hne : Y.Nonempty
    · obtain ⟨y0, hy0⟩ := hne
      exact ⟨transitionGauge γp γm y0, fun x hx => hdiff x hx y0 hy0⟩
    · refine ⟨1, fun x hx => ?_⟩
      exact absurd ⟨x, hx⟩ hne
  set γm' : Site → UnitQuaternion := fun x => κ * γm x with hγm'
  have hgauged : ∀ x j, latticeGaugeTransform γm' X x j = κ * latticeGaugeTransform γm X x j * κ⁻¹ := by
    intro x j
    simp only [hγm']
    unfold latticeGaugeTransform
    group
  have hm' : ∑ b ∈ bondsOf Pm, distOne (latticeGaugeTransform γm' X b.1 b.2) ^ 4 ≤ A ^ 4 := by
    simp only [hgauged, distOne_conj]
    exact hm
  have hgam : ∀ x, transitionGauge γp γm' x = transitionGauge γp γm x * κ⁻¹ := by
    intro x
    simp only [hγm']
    unfold transitionGauge
    group
  obtain ⟨γ, hγ⟩ := exists_glued_gauge_of_slab Φ hΦ0 hΦ1
    (fun t t' q q' a b c' d e f => hΦL t t' q q' a b c' d e f)
    l o s i P Pp Pm hl hsi hP hPp hPm X γp γm' τ ⌈l / 8⌉₊ A (C1 * A) (E ^ 4) hτabs
    (Nat.le_ceil _) (Nat.ceil_lt_add_one (by positivity)).le hp hm' hC1A (by positivity)
    (by
      intro x hx hxτ
      rw [hgam, distOne_mul_inv]
      exact hκ x (Finset.mem_filter.2 ⟨hx, hxτ⟩))
    w hw
    (by
      intro x hx hxτ j hj hxj
      rw [hgam, hgam, norm_mul_inv_sub_mul_inv]
      have hij : i ≠ j := fun h => hj h.symm
      have e1 : (x + basisVector j) i = τ := by
        rw [add_basisVector_apply]
        simp [hij, hxτ]
      exact hbond x (Finset.mem_filter.2 ⟨hx, hxτ⟩) j (Finset.mem_filter.2 ⟨hxj, e1⟩))
    hWE
  refine ⟨γ, le_trans hγ ?_⟩
  have hfin : ((1 + Q) * K * ε) = (1 + Q) * A := by
    rw [hA]
    ring
  rw [hfin]
  have hc8 : (0 : ℝ) ≤ l / 8 := by positivity
  exact glued_bound_le l hl ⌈l / 8⌉₊ (Nat.le_ceil _) (Nat.ceil_lt_add_one hc8).le A C1 hA0 hC1p P.card
    (card_le_of_isInShellOrthant l hl o s P hP) (E ^ 4) hE4
end YangMills.Construction.OrthantGluing
end
