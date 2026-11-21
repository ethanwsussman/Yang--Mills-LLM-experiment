import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel RowFinite
  CompSummable HasFiniteSupport)
open YangMills.Construction.Tower.RescaledConditions (complementProj gaugeFixedKernel)
namespace RescaledKernelAlgebra
section Kernels
variable {N₀ N₁ N₂ : Type}
theorem compKernel_sub_right (T : KernelMatrix N₁ N₀) (A B : KernelMatrix N₂ N₁)
    (hA : CompSummable T A) (hB : CompSummable T B) :
    compKernel T (A - B) = compKernel T A - compKernel T B := by
  funext i k
  simp only [compKernel, Pi.sub_apply, mul_sub]
  exact (hA i k).of_norm.tsum_sub (hB i k).of_norm
theorem compKernel_sub_left (A B : KernelMatrix N₁ N₀) (C : KernelMatrix N₂ N₁)
    (hA : CompSummable A C) (hB : CompSummable B C) :
    compKernel (A - B) C = compKernel A C - compKernel B C := by
  funext i k
  simp only [compKernel, Pi.sub_apply, sub_mul]
  exact (hA i k).of_norm.tsum_sub (hB i k).of_norm
theorem rowFinite_sub {A B : KernelMatrix N₁ N₀} (hA : RowFinite A) (hB : RowFinite B) :
    RowFinite (A - B) := by
  intro i
  refine ((hA i).union (hB i)).subset fun k hk => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hk (by simp [hn.1, hn.2])
theorem wPairing_add_right (w : N₀ → ℝ) {c : N₀ → ℂ} (hc : HasFiniteSupport c) (f g : N₀ → ℂ) :
    PeriodicOperators.wPairing w c (f + g) =
      PeriodicOperators.wPairing w c f + PeriodicOperators.wPairing w c g := by
  have hsum : ∀ h : N₀ → ℂ, Summable fun i => (w i : ℂ) * (c i * h i) := fun h =>
    summable_of_hasFiniteSupport (hc.subset fun i hi hz => hi (by simp [hz]))
  simp only [PeriodicOperators.wPairing, Pi.add_apply, mul_add]
  exact (hsum f).tsum_add (hsum g)
theorem wPairing_applyKernel_wTranspose
    (hT : PeriodicOperators.RowFiniteKernels.TransposeDuality)
    (T : KernelMatrix N₁ N₀) (w₀ : N₀ → ℝ) (w₁ : N₁ → ℝ) (hr : RowFinite T)
    (h₀ : ∀ i, 0 < w₀ i) (h₁ : ∀ i, 0 < w₁ i) (g : N₀ → ℂ) (hg : HasFiniteSupport g)
    (f : N₁ → ℂ) :
    PeriodicOperators.wPairing w₁ (applyKernel (PeriodicOperators.wTranspose w₁ w₀ T) g) f =
      PeriodicOperators.wPairing w₀ g (applyKernel T f) := by
  obtain ⟨-, -, -, s₁, s₀, e⟩ := hT N₀ N₁ T w₀ w₁ hr h₀ h₁ g hg f
  simp only [PeriodicOperators.wPairing]
  rw [tsum_eq_finsum s₁, tsum_eq_finsum s₀]
  exact e
end Kernels
theorem claim_of_rowFiniteKernels (hK : PeriodicOperators.RowFiniteKernels.Claim) : Claim := by
  obtain ⟨hAP, hAs, hU, hT⟩ := hK
  intro S₀ B₀ S B p heta htop hf hRRt
  have hprod : ∀ {M₀ M₁ M₂ : Type} (T : KernelMatrix M₁ M₀) (U : KernelMatrix M₂ M₁),
      RowFinite T → RowFinite U →
        CompSummable T U ∧ RowFinite (compKernel T U) :=
    fun T U hTr hUr => ⟨((hAP _ _ U hUr).2 _ T hTr).1, ((hAP _ _ U hUr).2 _ T hTr).2.1⟩
  have hact : ∀ {M₀ M₁ M₂ : Type} (T : KernelMatrix M₁ M₀) (U : KernelMatrix M₂ M₁)
      (f : M₂ → ℂ), RowFinite T → RowFinite U →
        applyKernel (compKernel T U) f = applyKernel T (applyKernel U f) :=
    fun T U f hTr hUr => (((hAP _ _ U hUr).2 _ T hTr).2.2 f).2.2
  have hassoc : ∀ {M₀ M₁ M₂ M₃ : Type} (T : KernelMatrix M₁ M₀) (U : KernelMatrix M₂ M₁)
      (V : KernelMatrix M₃ M₂), RowFinite T → RowFinite U →
        compKernel (compKernel T U) V = compKernel T (compKernel U V) :=
    fun T U V hTr hUr => (hAs _ _ _ _ T U V hTr hUr).2.2.2
  have hD := hf.D
  have hDt := hf.Dt
  have hR := hf.R
  have hRt := hf.Rt
  have hH := hf.H
  have hone : RowFinite (unitKernel (Fin 3 × S₀)) := (hU _).1
  obtain ⟨hPf, hPr⟩ := hprod p.Rt p.R hRt hR
  have hPr' : RowFinite (gaugeProjection p) := hPr
  have hidem : compKernel (gaugeProjection p) (gaugeProjection p) = gaugeProjection p := by
    show compKernel (compKernel p.Rt p.R) (compKernel p.Rt p.R) = compKernel p.Rt p.R
    rw [hassoc p.Rt p.R _ hRt hR, ← hassoc p.R p.Rt p.R hR hRt, hRRt, ((hU _).2.2 _ p.R).2]
  have hsym : ∀ ι ι', gaugeProjection p ι ι' = gaugeProjection p ι' ι := by
    intro ι ι'
    refine tsum_congr fun κ => ?_
    simp only [RescaledOperators.Rt, meshTranspose, PeriodicOperators.wTranspose, meshWeight]
    ring
  have hMr : RowFinite (complementProj p) := rowFinite_sub hone hPr
  have hMdef : complementProj p = unitKernel (Fin 3 × S₀) - gaugeProjection p := rfl
  have hMsym : ∀ a b, complementProj p a b = complementProj p b a := by
    intro a b
    have hu : unitKernel (Fin 3 × S₀) a b = unitKernel (Fin 3 × S₀) b a := by
      by_cases h : a = b
      · rw [h]
      · simp [unitKernel, h, Ne.symm h]
    simp only [hMdef, Pi.sub_apply, hu, hsym a b]
  have heta4 : (p.eta ^ 4) ≠ 0 := (pow_pos heta 4).ne'
  have hDte : ∀ κ ι, p.Dt κ ι = p.D ι κ := by
    intro κ ι
    simp [RescaledOperators.Dt, meshTranspose, PeriodicOperators.wTranspose, meshWeight, heta4]
  have hbr : gaugeCorrection p = compKernel p.D (compKernel (complementProj p) p.Dt) :=
    hassoc p.D _ p.Dt hD hMr
  have hX : p.X = gaugeFixedKernel p := by
    have e₁ : compKernel p.D (complementProj p) =
        p.D - compKernel p.D (gaugeProjection p) := by
      rw [hMdef, compKernel_sub_right _ _ _ ((hU _).2.1 _ p.D).1 (hprod p.D _ hD hPr').1,
        ((hU _).2.1 _ p.D).2]
    have e₃ : compKernel (compKernel p.D (gaugeProjection p)) p.Dt =
        compKernel (compKernel p.D p.Rt) (compKernel p.R p.Dt) := by
      show compKernel (compKernel p.D (compKernel p.Rt p.R)) p.Dt = _
      rw [← hassoc p.D p.Rt p.R hD hRt, hassoc _ p.R p.Dt (hprod p.D p.Rt hD hRt).2 hR]
    have e₂ : compKernel (compKernel p.D (complementProj p)) p.Dt =
        compKernel p.D p.Dt -
          compKernel (compKernel p.D p.Rt) (compKernel p.R p.Dt) := by
      rw [e₁, compKernel_sub_left _ _ _ (hprod p.D p.Dt hD hDt).1
        (hprod _ p.Dt (hprod p.D _ hD hPr').2 hDt).1, e₃]
    simp only [RescaledOperators.X, RescaledOperators.Xi, RescaledOperators.K, gaugeFixedKernel, e₂]
    abel
  have hMM : compKernel (complementProj p) (complementProj p) = complementProj p := by
    have e₁ : compKernel (gaugeProjection p) (complementProj p) = 0 := by
      rw [hMdef, compKernel_sub_right _ _ _ ((hU _).2.1 _ _).1 (hprod _ _ hPr' hPr').1,
        ((hU _).2.1 _ _).2, hidem, sub_self]
    nth_rewrite 1 [hMdef]
    rw [compKernel_sub_left _ _ _ ((hU _).2.2 _ _).1 (hprod _ _ hPr' hMr).1, ((hU _).2.2 _ _).2, e₁,
      sub_zero]
  have hMt : PeriodicOperators.wTranspose (meshWeight p.eta) (meshWeight p.eta)
      (complementProj p) = complementProj p := by
    funext a b
    simp [PeriodicOperators.wTranspose, meshWeight, heta4, hMsym b a]
  have hwS : ∀ i : Fin 3 × S₀, 0 < meshWeight p.eta i := fun _ => pow_pos heta 4
  have hwB : ∀ i : Fin 3 × B₀, 0 < meshWeight p.eta i := fun _ => pow_pos heta 4
  refine
    { proj_summable := hPf
      proj_row_finite := hPr
      proj_idem := hidem
      proj_symm := hsym
      complementProj_row_finite := hMr
      comp_assoc := hbr
      X_eq := hX
      correction_symm := ?_
      correction_row_finite := (hprod _ p.Dt (hprod p.D _ hD hMr).2 hDt).2
      pairing_eq := ?_ }
  · intro ι ι'
    calc gaugeCorrection p ι ι'
        = compKernel p.D (compKernel (complementProj p) p.Dt) ι ι' :=
          congrFun (congrFun hbr ι) ι'
      _ = gaugeCorrection p ι' ι := by
          refine tsum_congr fun κ => ?_
          rw [hDte κ ι, mul_comm]
          congr 1
          refine tsum_congr fun a => ?_
          rw [hDte a ι', hMsym κ a, mul_comm]
  · intro c hc
    have hv : HasFiniteSupport (applyKernel p.Dt c) :=
      (hT _ _ p.D (meshWeight p.eta) (meshWeight p.eta) hD hwB hwS c hc 0).2.2.1
    have hsplit : applyKernel (gaugeFixedKernel p) c =
        applyKernel p.H c + applyKernel (gaugeCorrection p) c := by
      funext ι
      have a := ((hAP _ _ p.H hH).1 c ι).of_norm
      have b := ((hAP _ _ _ (hprod _ p.Dt (hprod p.D _ hD hMr).2 hDt).2).1 c ι).of_norm
      simp only [applyKernel, gaugeFixedKernel, Pi.add_apply, add_mul]
      exact a.tsum_add b
    have hG : applyKernel (gaugeCorrection p) c =
        applyKernel p.D (applyKernel (complementProj p) (applyKernel p.Dt c)) := by
      show applyKernel (compKernel (compKernel p.D (complementProj p)) p.Dt) c = _
      rw [hact _ p.Dt c (hprod p.D _ hD hMr).2 hDt, hact p.D _ _ hD hMr]
    have d₁ := wPairing_applyKernel_wTranspose hT p.D (meshWeight p.eta) (meshWeight p.eta) hD hwB
      hwS c hc (applyKernel (complementProj p) (applyKernel p.Dt c))
    have d₂ := wPairing_applyKernel_wTranspose hT (complementProj p) (meshWeight p.eta)
      (meshWeight p.eta) hMr hwS hwS _ hv
      (applyKernel (complementProj p) (applyKernel p.Dt c))
    rw [hMt, ← hact _ _ _ hMr hMr, hMM] at d₂
    rw [hsplit, wPairing_add_right _ hc, hG, ← d₁]
    exact congrArg _ d₂.symm
end RescaledKernelAlgebra
end YangMills.Construction.Tower
end
