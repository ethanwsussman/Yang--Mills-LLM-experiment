import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.TransferPrinciple
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.DensityTransfer
open TestSpaceFacts
variable {n : ℕ}
theorem norm_apply_le_of_bounded {c ε : ℝ} {k : ℕ} {T : flatSchwartzSet n → ℂ} (hc : 0 ≤ c)
    (hε : 0 ≤ ε) (hT : IsBoundedByWeighted c k T) (φ : flatSchwartzSet n)
    (hφ : weightedSeminorm k φ.1 ≤ ENNReal.ofReal ε) : ‖T φ‖ ≤ c * ε := by
  have hle : ENNReal.ofReal ‖T φ‖ ≤ ENNReal.ofReal c * ENNReal.ofReal ε :=
    (hT φ).trans (by gcongr)
  rw [← ENNReal.ofReal_mul hc] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hε)).1 hle
theorem apply_add_of_isCLinear {T : flatSchwartzSet n → ℂ} (hT : IsCLinearOnFlat T)
    (φ ψ χ : flatSchwartzSet n) (hsum : χ.1 = φ.1 + ψ.1) : T χ = T φ + T ψ := by
  have e := hT 1 1 φ ψ χ (by simpa using hsum)
  simpa using e
def eqLocus (W : Submodule ℂ (PointTuple n → ℂ))
    (hW : (W : Set (PointTuple n → ℂ)) = flatSchwartzSet n)
    (T₁ T₂ : flatSchwartzSet n → ℂ) (h₁ : IsCLinearOnFlat T₁) (h₂ : IsCLinearOnFlat T₂) :
    Submodule ℂ (PointTuple n → ℂ) where
  carrier := {g | ∃ hg : g ∈ flatSchwartzSet n, T₁ ⟨g, hg⟩ = T₂ ⟨g, hg⟩}
  add_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    have hab : a + b ∈ flatSchwartzSet n := by
      rw [← hW] at ha hb ⊢
      exact W.add_mem ha hb
    refine ⟨hab, ?_⟩
    rw [apply_add_of_isCLinear h₁ ⟨a, ha⟩ ⟨b, hb⟩ ⟨a + b, hab⟩ rfl,
      apply_add_of_isCLinear h₂ ⟨a, ha⟩ ⟨b, hb⟩ ⟨a + b, hab⟩ rfl, ea, eb]
  zero_mem' := by
    have h0 : (0 : PointTuple n → ℂ) ∈ flatSchwartzSet n := by
      rw [← hW]
      exact W.zero_mem
    refine ⟨h0, ?_⟩
    have e₁ := h₁ 0 0 ⟨0, h0⟩ ⟨0, h0⟩ ⟨0, h0⟩ (by simp)
    have e₂ := h₂ 0 0 ⟨0, h0⟩ ⟨0, h0⟩ ⟨0, h0⟩ (by simp)
    rw [e₁, e₂]
    simp
  smul_mem' := by
    rintro c g ⟨hg, eg⟩
    have hcg : c • g ∈ flatSchwartzSet n := by
      rw [← hW] at hg ⊢
      exact W.smul_mem c hg
    refine ⟨hcg, ?_⟩
    have e₁ := h₁ c 0 ⟨g, hg⟩ ⟨g, hg⟩ ⟨c • g, hcg⟩ (by simp)
    have e₂ := h₂ c 0 ⟨g, hg⟩ ⟨g, hg⟩ ⟨c • g, hcg⟩ (by simp)
    rw [e₁, e₂, eg]
theorem eq_of_eqOnSmoothTensors (hBasic : Elementary.BasicProperties)
    (hFacts : TestSpaceFacts.Statement) {k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {T₁ T₂ : flatSchwartzSet n → ℂ} (h₁ : IsCLinearOnFlat T₁) (h₂ : IsCLinearOnFlat T₂)
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hb₁ : IsBoundedByWeighted c₁ k T₁)
    (hb₂ : IsBoundedByWeighted c₂ k T₂) (hag : EqOnSmoothTensors T₁ T₂) :
    T₁ = T₂ := by
  obtain ⟨hOps, hOpen, -, hTens, -⟩ := hBasic n hn
  obtain ⟨hO, -, -, -, -, -, hEq, -⟩ := hOpen
  obtain ⟨-, -, -, hDense⟩ := hFacts
  obtain ⟨W, hW⟩ := hOps.2 (distinctLocus n) hO
  have hWflat : (W : Set (PointTuple n → ℂ)) = flatSchwartzSet n := hW.trans hEq.symm
  have hmem : ∀ g, g ∈ W ↔ g ∈ flatSchwartzSet n := fun g => by
    rw [← hWflat]
    rfl
  have htensor : ∀ f, f ∈ disjointSupportTuples Set.univ n → HasSmoothComponents Set.univ f →
      tensorProdComplex f ∈ eqLocus W hWflat T₁ T₂ h₁ h₂ := fun f hf hs => by
    have hf' : tensorProdComplex f ∈ flatSchwartzSet n :=
      ((hTens Set.univ isOpen_univ f hf).2 hs).2.1
    exact ⟨hf', hag ⟨f, hf⟩ hs hf'⟩
  have hsmall : ∀ φ : flatSchwartzSet n, ∀ ε : ℝ, 0 < ε →
      ‖T₁ φ - T₂ φ‖ ≤ (c₁ + c₂) * ε := by
    intro φ ε hε
    have hflat := ((Set.ext_iff.1 hEq φ.1).1 φ.2).2
    obtain ⟨⟨m, c, f, -, hf, hclose⟩, -⟩ := (hDense n k hn hk).1 φ.1 φ.2.1 hflat ε hε
    have hF : tensorCombination c f ∈ eqLocus W hWflat T₁ T₂ h₁ h₂ := by
      have e : tensorCombination c f = ∑ ι, c ι • tensorProdComplex (f ι) := by
        funext x
        simp [tensorCombination, tensorProdComplex, Finset.sum_apply]
      rw [e]
      exact Submodule.sum_mem _ fun ι _ =>
        Submodule.smul_mem _ _ (htensor _ (hf ι).1 (hf ι).2)
    obtain ⟨hFm, hFe⟩ := hF
    have hd : φ.1 - tensorCombination c f ∈ flatSchwartzSet n :=
      (hmem _).1 (W.sub_mem ((hmem _).2 φ.2) ((hmem _).2 hFm))
    have e₁ := apply_add_of_isCLinear h₁ ⟨_, hd⟩ ⟨_, hFm⟩ φ (by simp)
    have e₂ := apply_add_of_isCLinear h₂ ⟨_, hd⟩ ⟨_, hFm⟩ φ (by simp)
    have b₁ := norm_apply_le_of_bounded hc₁ hε.le hb₁ ⟨_, hd⟩ hclose
    have b₂ := norm_apply_le_of_bounded hc₂ hε.le hb₂ ⟨_, hd⟩ hclose
    rw [e₁, e₂, hFe, add_sub_add_right_eq_sub, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add b₁ b₂)
  funext φ
  have hpos : 0 < c₁ + c₂ + 1 := by linarith
  by_contra hne
  have hD : 0 < ‖T₁ φ - T₂ φ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hb := hsmall φ (‖T₁ φ - T₂ φ‖ / (c₁ + c₂ + 1)) (div_pos hD hpos)
  have hlt : (c₁ + c₂) * (‖T₁ φ - T₂ φ‖ / (c₁ + c₂ + 1)) < ‖T₁ φ - T₂ φ‖ := by
    rw [mul_div_assoc', div_lt_iff₀ hpos]
    nlinarith
  exact absurd hb (not_le.2 hlt)
theorem isBoundedByWeighted_mono (hBasic : Elementary.BasicProperties) {k k' : ℕ} (hn : 0 < n)
    (hk : 0 < k) (hkk' : k ≤ k') {T : flatSchwartzSet n → ℂ} {c : ℝ}
    (hb : IsBoundedByWeighted c k T) : IsBoundedByWeighted c k' T := by
  obtain ⟨hOps, -⟩ := hBasic n hn
  intro φ
  have hmono : weightedSeminorm k φ.1 ≤ weightedSeminorm k' φ.1 :=
    ((hOps.1 φ.1 φ.2.1 φ.1 φ.2.1 0 0).2.1 k k' hk hkk').1
  exact (hb φ).trans (by gcongr)
theorem statement_holds (hBasic : Elementary.BasicProperties)
    (hFacts : TestSpaceFacts.Statement) :
    DensityTransfer.Statement := by
  refine ⟨?_, ?_⟩
  · rintro n k hn hk T₁ T₂ h₁ h₂ ⟨c₁, c₂, hc₁, hc₂, hb₁, hb₂⟩ hag
    exact eq_of_eqOnSmoothTensors hBasic hFacts hn hk h₁ h₂ hc₁ hc₂ hb₁ hb₂ hag
  · intro n k k' hn hk hk' T₁ T₂ c₁ c₂ _ _ _ _ hb₁ hb₂
    exact ⟨isBoundedByWeighted_mono hBasic hn hk (le_max_left k k') hb₁,
      isBoundedByWeighted_mono hBasic hn hk' (le_max_right k k') hb₂⟩
end YangMills.Construction.TestSpaces.DensityTransfer
end
