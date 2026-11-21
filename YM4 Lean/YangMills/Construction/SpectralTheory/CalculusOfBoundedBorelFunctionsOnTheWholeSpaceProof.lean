import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.CalculusOfBoundedBorelFunctionsOnTheWholeSpace
import YangMills.Construction.SpectralTheory.SpectralMeasurePushforwardTheorem
import YangMills.Construction.SpectralTheory.StrongConvergenceOfBoundedIntegrals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.WholeSpaceCalculus
open YangMills.Construction.BorelSpectral
open YangMills.Construction.WholeSpaceSpectral
open YangMills.Construction.BorelCalculus
variable {n : ℕ} {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
def onUniv (f : (Fin n → ℝ) → ℂ) : ↥(univ : Set (Fin n → ℝ)) → ℂ := fun y => f y.1
def extendFromSet (C : BorelSubsets (Fin n → ℝ)) (φ : C.1 → ℂ) : ↥(univ : Set (Fin n → ℝ)) → ℂ :=
  zeroExtend (restrictToUniv C).1 fun y => φ ⟨y.1.1, y.2⟩
theorem extendFromSet_of_mem (C : BorelSubsets (Fin n → ℝ)) (φ : C.1 → ℂ)
    {y : ↥(univ : Set (Fin n → ℝ))} (hy : y.1 ∈ C.1) : extendFromSet C φ y = φ ⟨y.1, hy⟩ := by
  have h : y ∈ (restrictToUniv C).1 := hy
  simp only [extendFromSet, zeroExtend, dif_pos h]
theorem extendFromSet_of_notMem (C : BorelSubsets (Fin n → ℝ)) (φ : C.1 → ℂ)
    {y : ↥(univ : Set (Fin n → ℝ))} (hy : y.1 ∉ C.1) : extendFromSet C φ y = 0 := by
  have h : y ∉ (restrictToUniv C).1 := hy
  simp only [extendFromSet, zeroExtend, dif_neg h]
theorem measurable_extendFromSet (C : BorelSubsets (Fin n → ℝ)) {φ : C.1 → ℂ} (hφ : Measurable φ) :
    Measurable (extendFromSet C φ) :=
  measurable_zeroExtend (restrictToUniv C).2
    (hφ.comp (Measurable.subtype_mk (measurable_subtype_coe.comp measurable_subtype_coe)))
theorem norm_extendFromSet_le (C : BorelSubsets (Fin n → ℝ)) {φ : C.1 → ℂ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, ‖φ x‖ ≤ c) (y : ↥(univ : Set (Fin n → ℝ))) : ‖extendFromSet C φ y‖ ≤ c := by
  by_cases hy : y.1 ∈ C.1
  · rw [extendFromSet_of_mem C φ hy]
    exact hc _
  · rw [extendFromSet_of_notMem C φ hy, norm_zero]
    exact hc0
theorem isBoundedFn_extendFromSet (C : BorelSubsets (Fin n → ℝ)) {φ : C.1 → ℂ}
    (hφ : IsBoundedFn φ) : IsBoundedFn (extendFromSet C φ) := by
  obtain ⟨c, hc⟩ := hφ
  exact ⟨max c 0, norm_extendFromSet_le C (le_max_right _ _) fun x => (hc x).trans (le_max_left _ _)⟩
theorem extendFromSet_add (C : BorelSubsets (Fin n → ℝ)) (φ χ : C.1 → ℂ) :
    extendFromSet C (φ + χ) = extendFromSet C φ + extendFromSet C χ := by
  funext y
  by_cases hy : y.1 ∈ C.1
  · simp only [Pi.add_apply, extendFromSet_of_mem _ _ hy]
  · simp only [Pi.add_apply, extendFromSet_of_notMem _ _ hy, add_zero]
theorem extendFromSet_smul (C : BorelSubsets (Fin n → ℝ)) (c : ℂ) (φ : C.1 → ℂ) :
    extendFromSet C (c • φ) = c • extendFromSet C φ := by
  funext y
  by_cases hy : y.1 ∈ C.1
  · simp only [Pi.smul_apply, extendFromSet_of_mem _ _ hy]
  · simp only [Pi.smul_apply, extendFromSet_of_notMem _ _ hy, smul_zero]
theorem extendFromSet_mul (C : BorelSubsets (Fin n → ℝ)) (φ χ : C.1 → ℂ) :
    extendFromSet C (φ * χ) = extendFromSet C φ * extendFromSet C χ := by
  funext y
  by_cases hy : y.1 ∈ C.1
  · simp only [Pi.mul_apply, extendFromSet_of_mem _ _ hy]
  · simp only [Pi.mul_apply, extendFromSet_of_notMem _ _ hy, mul_zero]
theorem extendFromSet_conjFn (C : BorelSubsets (Fin n → ℝ)) (φ : C.1 → ℂ) :
    extendFromSet C (conjFn φ) = conjFn (extendFromSet C φ) := by
  funext y
  by_cases hy : y.1 ∈ C.1
  · simp only [conjFn, extendFromSet_of_mem _ _ hy]
  · simp only [conjFn, extendFromSet_of_notMem _ _ hy, map_zero]
theorem extendFromSet_one (C : BorelSubsets (Fin n → ℝ)) :
    extendFromSet C (fun _ => 1) = (restrictToUniv C).1.indicator 1 := by
  funext y
  by_cases hy : y.1 ∈ C.1
  · have h : y ∈ (restrictToUniv C).1 := hy
    rw [extendFromSet_of_mem _ _ hy, indicator_of_mem h]
    rfl
  · have h : y ∉ (restrictToUniv C).1 := hy
    rw [extendFromSet_of_notMem _ _ hy, indicator_of_notMem h]
theorem measurable_onUniv {f : (Fin n → ℝ) → ℂ} (hf : Measurable f) : Measurable (onUniv f) :=
  hf.comp measurable_subtype_coe
theorem isBoundedFn_onUniv {f : (Fin n → ℝ) → ℂ} (hf : IsBoundedFn f) :
    IsBoundedFn (onUniv f) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun y => hc y.1⟩
theorem isBoundedFn_indicator {X : Type*} (Δ : Set X) : IsBoundedFn (Δ.indicator (1 : X → ℂ)) :=
  ⟨1, fun y => by
    by_cases h : y ∈ Δ
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]⟩
section Support
variable {E : SpectralMeasureOnSpace n 𝒦} (hE : BoundedFunctionalCalculus E) {C : BorelSubsets (Fin n → ℝ)}
include hE
theorem apply_support_eq_one (hC : IsSupportedOn E C) : E (restrictToUniv C) = 1 := by
  have hC' : E ⟨(restrictToUniv C).1ᶜ, (restrictToUniv C).2.compl⟩ = 0 := hC
  have hadd : (restrictToUniv C).1.indicator (1 : ↥(univ : Set (Fin n → ℝ)) → ℂ) +
      (restrictToUniv C).1ᶜ.indicator 1 = (univ : Set ↥(univ : Set (Fin n → ℝ))).indicator 1 := by
    funext y
    by_cases h : y ∈ (restrictToUniv C).1
    · simp [indicator_of_mem h, indicator_of_notMem (notMem_compl_iff.mpr h)]
    · simp [indicator_of_notMem h, indicator_of_mem (mem_compl h)]
  have h := hE.add _ _ (measurable_one.indicator (restrictToUniv C).2) (isBoundedFn_indicator _)
    (measurable_one.indicator (restrictToUniv C).2.compl) (isBoundedFn_indicator _)
  rw [hadd, hE.indicator ⟨univ, MeasurableSet.univ⟩, hE.indicator (restrictToUniv C),
    hE.indicator ⟨(restrictToUniv C).1ᶜ, (restrictToUniv C).2.compl⟩, E.map_univ, hC', add_zero] at h
  exact h.symm
theorem integralOp_mul_indicator (hC : IsSupportedOn E C) {g : ↥(univ : Set (Fin n → ℝ)) → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) :
    E.integralOp (g * (restrictToUniv C).1.indicator 1) = E.integralOp g := by
  rw [hE.mul _ _ hg hgb (measurable_one.indicator (restrictToUniv C).2) (isBoundedFn_indicator _),
    hE.indicator (restrictToUniv C), apply_support_eq_one hE hC, mul_one]
theorem integralOp_congr_on_support (hC : IsSupportedOn E C) {g h : ↥(univ : Set (Fin n → ℝ)) → ℂ}
    (hg : Measurable g) (hgb : IsBoundedFn g) (hh : Measurable h)
    (hhb : IsBoundedFn h) (hgh : ∀ y, y.1 ∈ C.1 → g y = h y) :
    E.integralOp g = E.integralOp h := by
  rw [← integralOp_mul_indicator hE hC hg hgb, ← integralOp_mul_indicator hE hC hh hhb]
  congr 1
  funext y
  by_cases hy : y ∈ (restrictToUniv C).1
  · simp only [Pi.mul_apply, indicator_of_mem hy, hgh y hy]
  · simp only [Pi.mul_apply, indicator_of_notMem hy, mul_zero]
omit hE in
theorem measurable_and_isBoundedFn_restrict (f : (Fin n → ℝ) → ℂ) (hf : IsBoundedMeasurableFn f) :
    Measurable (fun x : C.1 => f x) ∧ IsBoundedFn (fun x : C.1 => f x) := by
  obtain ⟨hm, c, hc⟩ := hf
  exact ⟨hm.comp measurable_subtype_coe, c, fun x => hc x⟩
theorem norm_integralOp_extendFromSet_apply_le {φ : C.1 → ℂ} (hφ : Measurable φ)
    (hφb : IsBoundedFn φ) (ψ : 𝒦) :
    ‖E.integralOp (extendFromSet C φ) ψ‖ ≤ (⨆ x, ‖φ x‖) * ‖ψ‖ := by
  have hS : 0 ≤ ⨆ x, ‖φ x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hbdd : BddAbove (range fun x => ‖φ x‖) := by
    obtain ⟨c, hc⟩ := hφb
    exact ⟨c, by rintro _ ⟨x, rfl⟩; exact hc x⟩
  have hne : Nonempty ↥(univ : Set (Fin n → ℝ)) := ⟨⟨0, mem_univ _⟩⟩
  have hsup : (⨆ y, ‖extendFromSet C φ y‖) ≤ ⨆ x, ‖φ x‖ :=
    ciSup_le (norm_extendFromSet_le C hS fun x => le_ciSup hbdd x)
  have hsup0 : 0 ≤ ⨆ y, ‖extendFromSet C φ y‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hm := measurable_extendFromSet C hφ
  have hb := isBoundedFn_extendFromSet C hφb
  have h₁ : ‖E.integralOp (extendFromSet C φ) ψ‖ ^ 2 ≤ ((⨆ x, ‖φ x‖) * ‖ψ‖) ^ 2 := by
    rw [hE.norm_sq _ hm hb ψ, mul_pow]
    refine (hE.integral_le _ hm hb ψ).trans ?_
    gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h₁
end Support
theorem boundedCalculusLaws {E : SpectralMeasureOnSpace n 𝒦} (hE : BoundedFunctionalCalculus E) :
    BoundedCalculusLaws E where
  add_smul f g hf hg c := by
    have h₁ := hE.smul c _ (measurable_onUniv hg.1) (isBoundedFn_onUniv hg.2)
    have hcg : IsBoundedFn (c • onUniv g) := by
      obtain ⟨b, hb⟩ := isBoundedFn_onUniv hg.2
      exact ⟨‖c‖ * b, fun y => by
        rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _)⟩
    have h₂ := hE.add _ _ (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2)
      ((measurable_onUniv hg.1).const_smul c) hcg
    rw [h₁] at h₂
    exact h₂
  mul f g hf hg :=
    hE.mul _ _ (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2) (measurable_onUniv hg.1)
      (isBoundedFn_onUniv hg.2)
  indicator Δ := by
    have h : (fun y : ↥(univ : Set (Fin n → ℝ)) => Δ.1.indicator (fun _ => (1 : ℂ)) y.1) =
        (restrictToUniv Δ).1.indicator 1 := by
      funext y
      by_cases hy : y.1 ∈ Δ.1
      · have h' : y ∈ (restrictToUniv Δ).1 := hy
        rw [indicator_of_mem hy, indicator_of_mem h']
        rfl
      · have h' : y ∉ (restrictToUniv Δ).1 := hy
        rw [indicator_of_notMem hy, indicator_of_notMem h']
    unfold integralOpOf
    rw [h]
    exact hE.indicator (restrictToUniv Δ)
  one := by
    have h : (fun _ : ↥(univ : Set (Fin n → ℝ)) => (1 : ℂ)) =
        (univ : Set ↥(univ : Set (Fin n → ℝ))).indicator 1 := by
      funext y
      simp
    unfold integralOpOf
    rw [h, hE.indicator ⟨univ, MeasurableSet.univ⟩, E.map_univ]
  adjoint f hf :=
    (hE.star_eq _ (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2)).symm
  norm_sq f hf ψ := hE.norm_sq _ (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2) ψ
theorem supportLaws {E : SpectralMeasureOnSpace n 𝒦} (hE : BoundedFunctionalCalculus E)
    {C : BorelSubsets (Fin n → ℝ)} (hC : IsSupportedOn E C) : SupportLaws E C where
  opAt_support := apply_support_eq_one hE hC
  diagSetFn_compl ψ := by
    rw [diagSetFn_apply, (isSupportedOn_iff E C).mp hC]
    simp
  congr f g hf hg hfg :=
    integralOp_congr_on_support hE hC (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2)
      (measurable_onUniv hg.1) (isBoundedFn_onUniv hg.2) fun y hy => hfg y.1 hy
  eq_integralOpOver f hf := by
    obtain ⟨hm, hb⟩ := measurable_and_isBoundedFn_restrict (C := C) f hf
    refine integralOp_congr_on_support hE hC (measurable_onUniv hf.1) (isBoundedFn_onUniv hf.2)
      (measurable_extendFromSet C hm) (isBoundedFn_extendFromSet C hb) fun y hy => ?_
    exact (extendFromSet_of_mem C (fun x => f x) hy).symm
  norm_sq f hf ψ := by
    obtain ⟨hm, hb⟩ := measurable_and_isBoundedFn_restrict (C := C) f hf
    change ‖E.integralOp (extendFromSet C fun x => f x) ψ‖ ^ 2 = _
    rw [hE.norm_sq _ (measurable_extendFromSet C hm) (isBoundedFn_extendFromSet C hb) ψ,
      ← integral_indicator (restrictToUniv C).2]
    congr 1
    funext y
    by_cases hy : y ∈ (restrictToUniv C).1
    · rw [indicator_of_mem hy, extendFromSet_of_mem C _ hy]
    · rw [indicator_of_notMem hy, extendFromSet_of_notMem C _ hy]
      simp
  opNorm_le f hf := by
    obtain ⟨hm, hb⟩ := measurable_and_isBoundedFn_restrict (C := C) f hf
    exact ContinuousLinearMap.opNorm_le_bound _ (Real.iSup_nonneg fun _ => norm_nonneg _)
      (norm_integralOp_extendFromSet_apply_le hE hm hb)
  over_add φ χ hφ hχ := by
    change E.integralOp (extendFromSet C (φ + χ)) = E.integralOp (extendFromSet C φ) +
      E.integralOp (extendFromSet C χ)
    rw [extendFromSet_add]
    exact hE.add _ _ (measurable_extendFromSet C hφ.1) (isBoundedFn_extendFromSet C hφ.2)
      (measurable_extendFromSet C hχ.1) (isBoundedFn_extendFromSet C hχ.2)
  over_smul c φ hφ := by
    change E.integralOp (extendFromSet C (c • φ)) = c • E.integralOp (extendFromSet C φ)
    rw [extendFromSet_smul]
    exact hE.smul c _ (measurable_extendFromSet C hφ.1) (isBoundedFn_extendFromSet C hφ.2)
  over_mul φ χ hφ hχ := by
    change E.integralOp (extendFromSet C (φ * χ)) = E.integralOp (extendFromSet C φ) *
      E.integralOp (extendFromSet C χ)
    rw [extendFromSet_mul]
    exact hE.mul _ _ (measurable_extendFromSet C hφ.1) (isBoundedFn_extendFromSet C hφ.2)
      (measurable_extendFromSet C hχ.1) (isBoundedFn_extendFromSet C hχ.2)
  over_one := by
    change E.integralOp (extendFromSet C fun _ => 1) = 1
    rw [extendFromSet_one, hE.indicator (restrictToUniv C)]
    exact apply_support_eq_one hE hC
  over_conj φ hφ := by
    change E.integralOp (extendFromSet C (conjFn φ)) =
      star (E.integralOp (extendFromSet C φ))
    rw [extendFromSet_conjFn]
    exact hE.star_eq _ (measurable_extendFromSet C hφ.1) (isBoundedFn_extendFromSet C hφ.2)
  support_empty hempty := by
    have hone : opAt E ⟨univ, MeasurableSet.univ⟩ = 1 := by
      have h : restrictToUniv (⟨univ, MeasurableSet.univ⟩ : BorelSubsets (Fin n → ℝ)) =
          ⟨univ, MeasurableSet.univ⟩ := Subtype.ext (by simp [restrictToUniv])
      unfold opAt
      rw [h]
      exact E.map_univ
    have hzero : opAt E ⟨univ, MeasurableSet.univ⟩ = 0 := by
      have h := (isSupportedOn_iff E C).mp hC
      have hs : (⟨univ \ C.1, MeasurableSet.univ.diff C.2⟩ : BorelSubsets (Fin n → ℝ)) =
          ⟨univ, MeasurableSet.univ⟩ := Subtype.ext (by simp [hempty])
      rwa [hs] at h
    refine ⟨hone.symm, hzero, fun ψ => ?_⟩
    have h : (1 : 𝒦 →L[ℂ] 𝒦) ψ = (0 : 𝒦 →L[ℂ] 𝒦) ψ := by
      rw [← hone, hzero]
    simpa using h
theorem strongConvergenceOver {E : SpectralMeasureOnSpace n 𝒦} (hS : StrongConvergence E)
    {C : BorelSubsets (Fin n → ℝ)} (hC : IsSupportedOn E C) : StrongConvergenceOver E C := by
  rintro fs φ hm ⟨c, hc⟩ hlim ψ
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  have hbd : ∀ r x, ‖fs (r + 1) x‖ ≤ max c 0 := fun r x =>
    (hc (r + 1) (by omega) x).trans (le_max_left _ _)
  have hm' : ∀ r, Measurable (fs (r + 1)) := fun r => hm _ (by omega)
  have hlim' : ∀ x, Tendsto (fun r => fs (r + 1) x) atTop (𝓝 (φ x)) := fun x =>
    (hlim x).comp (tendsto_add_atTop_nat 1)
  have hφ : Measurable φ :=
    measurable_of_tendsto_metrizable hm' (tendsto_pi_nhds.mpr hlim')
  have hφb : ∀ x, ‖φ x‖ ≤ max c 0 := fun x =>
    le_of_tendsto' (hlim' x).norm fun r => hbd r x
  have h := (hS (fun r => extendFromSet C (fs (r + 1))) (extendFromSet C φ) (max c 0) (restrictToUniv C)
    (fun r => measurable_extendFromSet C (hm' r)) (measurable_extendFromSet C hφ)
    (fun r => norm_extendFromSet_le C hc0 (hbd r)) hC (fun y hy => by
      have hy' : y.1 ∈ C.1 := hy
      simp only [extendFromSet_of_mem C _ hy']
      exact hlim' _)).2 ψ
  rw [E.integralApply_eq_integralOp (norm_extendFromSet_le C hc0 hφb)] at h
  exact (tendsto_add_atTop_iff_nat 1).mp h
theorem pushforwardLaws {E : SpectralMeasureOnSpace n 𝒦} (hI : PushforwardProperties E) :
    PushforwardLaws E where
  diagMeasure_mapBy hn' p hp ψ :=
    hI.diagMeasure_pushforward hn' MeasurableSet.univ (liftMap p)
      ((hp.comp measurable_subtype_coe).subtype_mk) ψ
  integralOpOf_mapBy {n'} hn' p hp h hh := by
    obtain ⟨c, hc⟩ := hh.2
    have hbd : ∀ y : ↥(univ : Set (Fin n' → ℝ)), ‖onUniv h y‖ ≤ c := fun y => hc y.1
    have hbd' : ∀ y : ↥(univ : Set (Fin n → ℝ)), ‖(onUniv h ∘ liftMap p) y‖ ≤ c :=
      fun y => hc (p y.1)
    obtain ⟨-, hv⟩ := hI.integral_pushforward hn' MeasurableSet.univ (liftMap p)
      ((hp.comp measurable_subtype_coe).subtype_mk) (onUniv h) (measurable_onUniv hh.1)
    ext ψ
    have hψ : ψ ∈ E.integralDom (onUniv h ∘ liftMap p) := by
      rw [E.integralDom_eq_univ hbd']
      exact mem_univ _
    have h₁ := hv ψ hψ
    rw [SpectralMeasure.integralApply_eq_integralOp _ hbd,
      E.integralApply_eq_integralOp hbd'] at h₁
    exact h₁
theorem boundedCalculusTheorem_holds
    (hB : YangMills.Construction.SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds)
    (hI : SpectralPushforwardTheorem)
    (hS : StrongConvergenceHolds) : BoundedCalculusTheorem := by
  intro 𝒦 _ _ _ n E
  have hE := hB 𝒦 n univ E
  exact ⟨boundedCalculusLaws hE,
    fun C hC => ⟨supportLaws hE hC, strongConvergenceOver (hS 𝒦 n univ E) hC⟩,
    pushforwardLaws (hI 𝒦 n univ E)⟩
end YangMills.Construction.WholeSpaceCalculus
