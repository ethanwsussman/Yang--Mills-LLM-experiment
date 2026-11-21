import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.MixedDerivativeAlongFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem iteratedFDeriv_comp_continuousLinearMap_at_zero {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : A →L[ℝ] B) (f : B → E) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (v : Fin k → A) :
    iteratedFDeriv ℝ k (f ∘ g) 0 v = iteratedFDeriv ℝ k f 0 (fun l => g (v l)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_comp_clm_zero <;> assumption
theorem mixedDerivAlongDirectionFields_holds : MixedDerivAlongDirectionFields := by
  classical
  intro F j k E _ _ G W J ξ hξ hG
  let ι : Type := Σ l : Fin k, ↥(J l)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let n := Fintype.card ι
  let c' : Fin n → F.Site j × Fin 4 := fun q => ((e.symm q).2 : F.Site j × Fin 4)
  let X' : Fin n → imaginaryQuaternions := fun q => ξ (e.symm q).1 (c' q).1 (c' q).2
  let h : (Fin n → ℝ) → E := fun σ => G (leftTranslate (bondSpread c' X' σ) W)
  have hh : ContDiffAt ℝ k h 0 := hG n c' X'
  let B : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (e.symm q).1
  have hB : ∀ τ q, B τ q = τ (e.symm q).1 := fun τ q => rfl
  have hc' : ∀ x : ι, c' (e x) = x.2 := fun x => by
    change ((e.symm (e x)).2 : F.Site j × Fin 4) = x.2
    rw [Equiv.symm_apply_apply]
  have hX' : ∀ x : ι, X' (e x) = ξ x.1 (x.2 : F.Site j × Fin 4).1 (x.2 : F.Site j × Fin 4).2 :=
    fun x => by
      change ξ (e.symm (e x)).1 (c' (e x)).1 (c' (e x)).2 = _
      rw [hc', Equiv.symm_apply_apply]
  have hB' : ∀ (τ : Fin k → ℝ) (x : ι), B τ (e x) = τ x.1 := fun τ x => by simp [hB]
  have hspread : ∀ τ : Fin k → ℝ, bondSpread c' X' (B τ) = fun z i => ∑ l, τ l • ξ l z i := by
    intro τ
    funext z i
    simp only [bondSpread]
    rw [← e.sum_comp]
    simp only [hc', hX', hB']
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hz : (z, i) ∈ J l
    · rw [Finset.sum_eq_single (⟨(z, i), hz⟩ : ↥(J l))]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro hc
        exact hp (Subtype.ext hc)
      · simp
    · rw [hξ l z i hz, smul_zero]
      refine Finset.sum_eq_zero fun p _ => ?_
      split_ifs with hc
      · exact absurd (hc ▸ p.2) hz
      · rfl
  have hcomp : (fun τ : Fin k → ℝ => G (leftTranslate (fun z i => ∑ l, τ l • ξ l z i) W)) = h ∘ B := by
    funext τ
    simp only [Function.comp, h, hspread]
  rw [hcomp, iteratedFDeriv_comp_continuousLinearMap_at_zero B h k hh]
  have hBe : ∀ l : Fin k, B (Pi.single l 1) = ∑ p ∈ (J l).attach, Pi.single (e ⟨l, p⟩) (1 : ℝ) := by
    intro l
    funext q
    rw [Finset.sum_apply]
    obtain ⟨⟨l', p'⟩, rfl⟩ := e.surjective q
    rw [hB']
    by_cases hl : l' = l
    · subst hl
      rw [Finset.sum_eq_single p']
      · simp
      · intro b _ hb
        rw [Pi.single_apply, if_neg]
        intro hc
        exact hb (sigma_mk_injective (e.injective hc)).symm
      · intro hc
        exact absurd (Finset.mem_attach _ _) hc
    · rw [Pi.single_apply, if_neg hl]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      rw [Pi.single_apply, if_neg]
      intro hc
      exact hl (congrArg Sigma.fst (e.injective hc))
  simp only [hBe]
  rw [ContinuousMultilinearMap.map_sum_finset]
  refine Finset.sum_bij' (fun r _ l => ((r l : ↥(J l)) : F.Site j × Fin 4))
    (fun r hr l => ⟨r l, Fintype.mem_piFinset.mp hr l⟩) ?_ ?_ ?_ ?_ ?_
  · intro r _
    exact Fintype.mem_piFinset.mpr fun l => (r l).2
  · intro r _
    exact Fintype.mem_piFinset.mpr fun l => Finset.mem_attach _ _
  · intro r _
    rfl
  · intro r _
    rfl
  · intro r _
    let q : Fin k → Fin n := fun l => e ⟨l, r l⟩
    let R : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) :=
      ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (q l) (1 : ℝ))
    have hR : ∀ (σ : Fin k → ℝ) (p : Fin n), R σ p = ∑ l, σ l * (Pi.single (q l) (1 : ℝ) : Fin n → ℝ) p := by
      intro σ p
      simp [R, Finset.sum_apply]
    have hRe : ∀ l, R (Pi.single l 1) = Pi.single (q l) 1 := by
      intro l
      funext p
      rw [hR, Finset.sum_eq_single l]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    have hrest : (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread (fun l => ((r l : ↥(J l)) : F.Site j × Fin 4))
        (fun l => ξ l ((r l : ↥(J l)) : F.Site j × Fin 4).1 ((r l : ↥(J l)) : F.Site j × Fin 4).2) τ) W)) =
        h ∘ R := by
      funext σ
      simp only [Function.comp, h]
      congr 2
      funext z i
      simp only [bondSpread]
      have step : ∀ p : Fin n, (if c' p = (z, i) then R σ p • X' p else 0) =
          ∑ l, (if c' p = (z, i) then (σ l * (Pi.single (q l) (1 : ℝ) : Fin n → ℝ) p) • X' p else 0) := by
        intro p
        split_ifs with hp
        · rw [hR, Finset.sum_smul]
        · simp
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single (q l)]
      · have e1 : c' (q l) = ((r l : ↥(J l)) : F.Site j × Fin 4) := hc' _
        have e2 : X' (q l) = ξ l ((r l : ↥(J l)) : F.Site j × Fin 4).1 ((r l : ↥(J l)) : F.Site j × Fin 4).2 := hX' _
        rw [e1, e2]
        simp
      · intro p _ hp
        split_ifs
        · simp [hp]
        · rfl
      · simp
    unfold bondDeriv
    rw [hrest, iteratedFDeriv_comp_continuousLinearMap_at_zero R h k hh]
    simp only [hRe, q]
end YangMills.Construction.ColdStepAtMirrorFrames
end
