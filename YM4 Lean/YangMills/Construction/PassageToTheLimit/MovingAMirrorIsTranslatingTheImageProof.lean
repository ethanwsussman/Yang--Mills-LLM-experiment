import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImage
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
namespace MirrorTranslation
open YangMills.Construction.TorusMetric (euclidNormVec)
variable (s : Conventions.StandingParameters)
theorem reflectR4_sub_smul_stdBasisVec (μ : Fin 4) (c c' : ℝ) (y : Fin 4 → ℝ) :
    reflectR4 μ c (y - (2 * (c' - c)) • stdBasisVec μ) = reflectR4 μ c' y := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [reflectR4, stdBasisVec]
    ring
  · simp [reflectR4, stdBasisVec, h]
theorem reflectR4_sub (μ : Fin 4) (c : ℝ) (w y : Fin 4 → ℝ) :
    reflectR4 μ c (y - w) = reflectR4 μ (c + w μ) y - w := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [reflectR4, stdBasisVec]
    ring
  · simp [reflectR4, stdBasisVec, h]
theorem proj_sub_eq (E : Ambient) (x y : Fin 4 → ℝ) :
    E.proj s (x - y) = E.proj s x - E.proj s y := by
  rw [sub_eq_add_neg, E.proj_add, E.proj_neg, sub_eq_add_neg]
theorem proj_zero_eq (E : Ambient) : E.proj s 0 = 0 := by
  have h := proj_sub_eq s E 0 0
  simpa using h
theorem reflect_proj_apply (E : Ambient) (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    E.reflect s μ c (E.proj s y) = E.proj s (reflectR4 μ c y) :=
  congrFun (E.reflect_comp_proj s μ c) y
theorem reflect_sub_proj_smul (E : Ambient) (μ : Fin 4) (c c' : ℝ) (x : E.Carrier s) :
    E.reflect s μ c (x - E.proj s ((2 * (c' - c)) • stdBasisVec μ)) =
      E.reflect s μ c' x := by
  obtain ⟨y, rfl⟩ := E.proj_surjective s x
  rw [← proj_sub_eq, reflect_proj_apply, reflect_proj_apply, reflectR4_sub_smul_stdBasisVec]
theorem reflect_sub_of_lift (E : Ambient) (μ : Fin 4) (c : ℝ) (v : E.Carrier s) (w : Fin 4 → ℝ)
    (hw : E.IsLiftOf s v w) (x : E.Carrier s) :
    E.reflect s μ c (x - v) = E.reflect s μ (c + w μ) x - v := by
  obtain ⟨y, rfl⟩ := E.proj_surjective s x
  have hv : E.proj s w = v := hw
  subst hv
  rw [← proj_sub_eq, reflect_proj_apply, reflect_proj_apply, reflectR4_sub, proj_sub_eq]
theorem reflectTranslateIdentities_holds (E : Ambient) (μ : Fin 4) (Z : Type) :
    ReflectTranslateIdentities s E μ Z := by
  intro c c' v f
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Ambient.reflectFun, Ambient.translateFunVec, Ambient.translateFun,
      Function.comp_apply]
    rw [reflect_sub_proj_smul]
  · intro w hw
    funext x
    simp only [Ambient.reflectFun, Ambient.translateFun, Function.comp_apply]
    rw [reflect_sub_of_lift s E μ c v w hw x]
theorem reflectLiftInvariant_holds
    (hT : AmbientMetric.PeriodicReflectHalfPeriod s)
    (E : Ambient) (μ : Fin 4) : ReflectLiftInvariant s E μ := by
  intro c v w w' hw hw'
  have hk := E.sub_mem_periodGroup s (hw.trans hw'.symm)
  cases E with
  | euclidean =>
    have h0 : w - w' = 0 := hk
    rw [sub_eq_zero.mp h0]
  | periodic =>
    have h0 := (Ambient.periodic.mem_periodGroup_iff s _).mp hk
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n • s.side = (w - w') μ :=
      (AddCircle.coe_eq_zero_iff _).mp (congrFun h0 μ)
    refine hT μ (c + w' μ) (c + w μ) ⟨2 * n, ?_⟩
    have hn' : (n : ℝ) * s.side = w μ - w' μ := by simpa using hn
    push_cast
    linarith
theorem euclidNormVec_coordFlip_mulVec (μ : Fin 4) (z : Fin 4 → ℝ) :
    euclidNormVec ((coordFlipMatrix μ).mulVec z) = euclidNormVec z := by
  unfold euclidNormVec
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : ν = μ <;> simp [coordFlipMatrix, Matrix.mulVec_diagonal, h]
theorem euclidNormVec_smul_stdBasisVec (a : ℝ) (μ : Fin 4) :
    euclidNormVec (a • stdBasisVec μ) = |a| := by
  unfold euclidNormVec
  have h : ∑ ν, (a • stdBasisVec μ) ν ^ 2 = a ^ 2 := by
    simp [stdBasisVec, Pi.single_apply]
  rw [h, Real.sqrt_sq_eq_abs]
theorem euclidNormVec_sub_le_two_mul {a b : Fin 4 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : euclidNormVec a ≤ C) (hb : euclidNormVec b ≤ C) : euclidNormVec (a - b) ≤ 2 * C := by
  have ha' := (Real.sqrt_le_iff.mp ha).2
  have hb' := (Real.sqrt_le_iff.mp hb).2
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have h : ∑ ν, (a - b) ν ^ 2 ≤ ∑ ν, (2 * a ν ^ 2 + 2 * b ν ^ 2) := by
    refine Finset.sum_le_sum fun ν _ => ?_
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a ν + b ν)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  nlinarith
theorem normSharp_eq_max (M : SharpParameter) (E : Ambient) (g : E.Carrier s → ℝ) :
    E.normSharp s M g = max (TestFunctions.uniformNorm g) (40 * (M : ℝ) * E.lipConst s g) := by
  cases E <;> rfl
theorem norm_sub_le_bestLipschitzConstant_mul {X : Type*} {d : X → X → ℝ} {f : X → ℝ}
    (hf : TestFunctions.IsLipschitzFor d f) (hd : ∀ x y, 0 ≤ d x y) (x y : X) :
    ‖f x - f y‖ ≤ TestFunctions.bestLipschitzConstant d f * d x y := by
  obtain ⟨C, hC, h⟩ := hf
  rcases (hd x y).eq_or_lt with h0 | h0
  · have hxy := h x y
    rw [← h0, mul_zero] at hxy
    rw [← h0, mul_zero]
    exact hxy
  · have hle : ‖f x - f y‖ / d x y ≤ TestFunctions.bestLipschitzConstant d f :=
      le_csInf ⟨C, hC, h⟩ fun b hb => (div_le_iff₀ h0).mpr (hb.2 x y)
    exact (div_le_iff₀ h0).mp hle
theorem norm_sub_le_lipConst_mul (E : Ambient) (hd : ∀ x y : E.Carrier s, 0 ≤ E.pointDist s x y)
    (f : E.Carrier s → ℝ) (hf : E.IsLip s f) (x y : E.Carrier s) :
    ‖f x - f y‖ ≤ E.lipConst s f * E.pointDist s x y := by
  cases E with
  | euclidean =>
    exact norm_sub_le_bestLipschitzConstant_mul (d := TestFunctions.euclidDistR4) hf hd x y
  | periodic =>
    exact norm_sub_le_bestLipschitzConstant_mul (d := TestFunctions.euclidDistTorus) hf hd x y
variable {s}
theorem gradModulus_mono {E : Ambient} (f : E.c1Compact s) {δ δ' : ℝ≥0}
    (h : δ ≤ δ') : Ambient.gradModulus f δ ≤ Ambient.gradModulus f δ' := by
  unfold Ambient.gradModulus
  exact iSup_mono fun x => iSup_mono fun y => iSup_mono' fun hxy =>
    ⟨hxy.trans (NNReal.coe_le_coe.mpr h), le_rfl⟩
theorem continuityModulus_mono (M : SharpParameter) {E : Ambient} (f : E.c1Compact s)
    {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    Ambient.continuityModulus M f δ ≤ Ambient.continuityModulus M f δ' :=
  max_le_max (mul_le_mul' le_rfl (ENNReal.coe_le_coe.mpr h))
    (mul_le_mul' le_rfl (gradModulus_mono f h))
theorem continuityModulus_eq_of_isometry (M : SharpParameter) {E : Ambient}
    (f h : E.c1Compact s) (t : E.Carrier s → E.Carrier s) (ht : Function.Surjective t)
    (hiso : AmbientMetric.IsDistPreserving s E t)
    (hnorm : ∀ x, euclidNormVec (E.grad s h.1 x) = euclidNormVec (E.grad s f.1 (t x)))
    (hdiff : ∀ x y, euclidNormVec (E.grad s h.1 x - E.grad s h.1 y) =
      euclidNormVec (E.grad s f.1 (t x) - E.grad s f.1 (t y)))
    (δ : ℝ≥0) : Ambient.continuityModulus M h δ = Ambient.continuityModulus M f δ := by
  have hsup : E.gradSup s h.1 = E.gradSup s f.1 := by
    unfold Ambient.gradSup
    simp only [hnorm]
    exact ht.iSup_comp fun y => ENNReal.ofReal (euclidNormVec (E.grad s f.1 y))
  have hmod : Ambient.gradModulus h δ = Ambient.gradModulus f δ := by
    unfold Ambient.gradModulus
    apply le_antisymm
    · refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
      rw [hdiff]
      exact le_iSup_of_le (t x) (le_iSup_of_le (t y)
        (le_iSup_of_le (by rw [hiso]; exact hxy) le_rfl))
    · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
      obtain ⟨x, rfl⟩ := ht a
      obtain ⟨y, rfl⟩ := ht b
      rw [← hdiff]
      exact le_iSup_of_le x (le_iSup_of_le y
        (le_iSup_of_le (by rw [← hiso]; exact hab) le_rfl))
  unfold Ambient.continuityModulus
  rw [hsup, hmod]
variable (s)
theorem translateModulusBound_holds (hyp : AmbientMetric.Claim) (M : SharpParameter)
    (E : Ambient) : TranslateModulusBound s M E := by
  obtain ⟨hE, -, hC, hComb, hT, -, -⟩ := hyp s E
  obtain ⟨-, hdist, hinv, -, -⟩ := hE
  intro f u v
  have hd0 : 0 ≤ E.pointDist s u v := hdist.nonneg u v
  have hshift : ∀ x : E.Carrier s, E.pointDist s (x - u) (x - v) = E.pointDist s u v := by
    intro x
    have h := hinv (x - u) (x - v) (u + v - x)
    rw [show x - u + (u + v - x) = v by abel, show x - v + (u + v - x) = u by abel] at h
    rw [← h, hdist.symm]
  obtain ⟨hu, hgu⟩ := (hT u).2.2.2 f.1 f.2
  obtain ⟨hv, hgv⟩ := (hT v).2.2.2 f.1 f.2
  obtain ⟨hmem, hgrad, -, -, -⟩ :=
    hComb _ hu _ hv 1 (-1) f.1 f.2.1
  have heq : (fun x => (1 : ℝ) * E.translateFun s u f.1 x + (-1) * E.translateFun s v f.1 x) =
      E.translateFun s u f.1 - E.translateFun s v f.1 := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [heq] at hmem hgrad
  obtain ⟨-, -, -, -, -, -, -, hLiph, -⟩ := hC _ hmem
  obtain ⟨-, -, -, -, -, -, hLipf, hLipfG, hGfin⟩ := hC f.1 f.2
  have hLipfr : E.lipConst s f.1 ≤ (E.gradSup s f.1).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hGfin.ne).mp hLipfG
  have : Nonempty (E.Carrier s) := ⟨0⟩
  have hsup : TestFunctions.uniformNorm (E.translateFun s u f.1 - E.translateFun s v f.1) ≤
      (E.gradSup s f.1).toReal * E.pointDist s u v := by
    refine ciSup_le fun x => ?_
    have h := norm_sub_le_lipConst_mul s E hdist.nonneg f.1 hLipf (x - u) (x - v)
    rw [hshift] at h
    exact h.trans (mul_le_mul_of_nonneg_right hLipfr hd0)
  have hlip : ENNReal.ofReal (E.lipConst s (E.translateFun s u f.1 - E.translateFun s v f.1)) ≤
      Ambient.gradModulus f (E.pointDist s u v).toNNReal := by
    refine hLiph.trans (iSup_le fun x => ?_)
    have hx : E.grad s (E.translateFun s u f.1 - E.translateFun s v f.1) x =
        E.grad s f.1 (x - u) - E.grad s f.1 (x - v) := by
      rw [hgrad]
      simp only [Pi.add_apply, Pi.neg_apply, hgu, hgv, one_smul, neg_smul, sub_eq_add_neg]
    rw [hx]
    unfold Ambient.gradModulus
    refine le_iSup_of_le (x - u) (le_iSup_of_le (x - v) (le_iSup_of_le ?_ le_rfl))
    rw [hshift, Real.coe_toNNReal _ hd0]
  have h40 : (0 : ℝ) ≤ 40 * (M : ℝ) := by
    have := Set.mem_Ici.mp M.2
    linarith
  have h1 : ENNReal.ofReal
        (TestFunctions.uniformNorm (E.translateFun s u f.1 - E.translateFun s v f.1)) ≤
      E.gradSup s f.1 * ((E.pointDist s u v).toNNReal : ℝ≥0∞) := by
    refine (ENNReal.ofReal_le_ofReal hsup).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hGfin.ne]
    exact le_rfl
  have h2 : ENNReal.ofReal
        (40 * (M : ℝ) * E.lipConst s (E.translateFun s u f.1 - E.translateFun s v f.1)) ≤
      ENNReal.ofReal (40 * (M : ℝ)) *
        Ambient.gradModulus f (E.pointDist s u v).toNNReal := by
    rw [ENNReal.ofReal_mul h40]
    exact mul_le_mul' le_rfl hlip
  rw [normSharp_eq_max]
  unfold Ambient.continuityModulus
  rcases le_total (TestFunctions.uniformNorm (E.translateFun s u f.1 - E.translateFun s v f.1))
    (40 * (M : ℝ) * E.lipConst s (E.translateFun s u f.1 - E.translateFun s v f.1)) with h | h
  · rw [max_eq_right h]
    exact le_max_of_le_right h2
  · rw [max_eq_left h]
    exact le_max_of_le_left h1
theorem reflectModulusBound_holds (hyp : AmbientMetric.Claim) (M : SharpParameter)
    (E : Ambient) (μ : Fin 4) : ReflectModulusBound s M E μ := by
  obtain ⟨hE, -, -, -, -, hR, -⟩ := hyp s E
  obtain ⟨hproj, hdist, -, -, -⟩ := hE
  intro f c c'
  obtain ⟨hbij, hiso, -, hfun⟩ := hR μ c
  obtain ⟨hmem, hgrad⟩ := hfun f.1 f.2
  have hmod : ∀ δ : ℝ≥0, Ambient.continuityModulus M (⟨_, hmem⟩ : E.c1Compact s) δ =
      Ambient.continuityModulus M f δ := by
    refine continuityModulus_eq_of_isometry M f _ (E.reflect s μ c) hbij.2 hiso ?_ ?_
    · intro x
      simp only [hgrad, euclidNormVec_coordFlip_mulVec]
    · intro x y
      simp only [hgrad]
      rw [← Matrix.mulVec_sub, euclidNormVec_coordFlip_mulVec]
  set w : Fin 4 → ℝ := (2 * (c' - c)) • stdBasisVec μ with hw
  set u : E.Carrier s := E.proj s w with hu
  have hident := (reflectTranslateIdentities_holds s E μ ℝ c c' 0 f.1).1
  have htr0 : E.translateFun s 0 (E.reflectFun s μ c f.1) = E.reflectFun s μ c f.1 := by
    funext x
    simp [Ambient.translateFun]
  have hclose := translateModulusBound_holds s hyp M E ⟨_, hmem⟩ u 0
  have hdiff : E.reflectFun s μ c' f.1 - E.reflectFun s μ c f.1 =
      E.translateFun s u (E.reflectFun s μ c f.1) -
        E.translateFun s 0 (E.reflectFun s μ c f.1) := by
    rw [htr0, hident]
    rfl
  have hlen : E.pointDist s u 0 ≤ 2 * |c' - c| := by
    have h := (hproj w 0).2
    rw [proj_zero_eq, sub_zero, euclidNormVec_smul_stdBasisVec, abs_mul, abs_two] at h
    exact h
  rw [hdiff]
  refine hclose.trans ?_
  rw [hmod]
  exact continuityModulus_mono M f (Real.toNNReal_le_toNNReal hlen)
theorem modulusFiniteTendsZero_holds (hyp : AmbientMetric.Claim) (M : SharpParameter)
    (E : Ambient) : ModulusFiniteTendsZero s M E := by
  obtain ⟨-, -, hC, -, -, -, -⟩ := hyp s E
  intro f
  obtain ⟨-, -, -, -, -, hunif, -, -, hGfin⟩ := hC f.1 f.2
  have hG : ∀ x, euclidNormVec (E.grad s f.1 x) ≤ (E.gradSup s f.1).toReal := by
    intro x
    refine (ENNReal.ofReal_le_iff_le_toReal hGfin.ne).mp ?_
    exact le_iSup (fun x => ENNReal.ofReal (euclidNormVec (E.grad s f.1 x))) x
  have hGr : 0 ≤ (E.gradSup s f.1).toReal := ENNReal.toReal_nonneg
  have hM : (0 : ℝ) < 40 * (M : ℝ) := by
    have := Set.mem_Ici.mp M.2
    linarith
  refine ⟨fun δ => ?_, ?_⟩
  · have hbound : Ambient.gradModulus f δ ≤
        ENNReal.ofReal (2 * (E.gradSup s f.1).toReal) := by
      refine iSup_le fun x => iSup_le fun y => iSup_le fun _ => ?_
      exact ENNReal.ofReal_le_ofReal (euclidNormVec_sub_le_two_mul hGr (hG x) (hG y))
    exact max_lt (ENNReal.mul_lt_top hGfin ENNReal.coe_lt_top)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hbound.trans_lt ENNReal.ofReal_lt_top))
  · refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have he : (0 : ℝ) < r := NNReal.coe_pos.mpr (ENNReal.coe_pos.mp hr0)
    obtain ⟨δ₀, hδ₀, hu⟩ := hunif ((r : ℝ) / (40 * (M : ℝ))) (div_pos he hM)
    have hδ₁ : 0 < min δ₀ ((r : ℝ) / (1 + (E.gradSup s f.1).toReal)) :=
      lt_min hδ₀ (div_pos he (by linarith))
    filter_upwards [Iio_mem_nhds (Real.toNNReal_pos.mpr hδ₁)] with δ hδ
    have hδr : (δ : ℝ) < min δ₀ ((r : ℝ) / (1 + (E.gradSup s f.1).toReal)) :=
      Real.lt_toNNReal_iff_coe_lt.mp hδ
    have hδa : (δ : ℝ) ≤ δ₀ := (hδr.trans_le (min_le_left _ _)).le
    have hδb : (δ : ℝ) ≤ (r : ℝ) / (1 + (E.gradSup s f.1).toReal) :=
      (hδr.trans_le (min_le_right _ _)).le
    refine le_trans ?_ hrε.le
    unfold Ambient.continuityModulus
    refine max_le ?_ ?_
    · have hprod : (E.gradSup s f.1).toReal * (δ : ℝ) ≤ (r : ℝ) := by
        have hpos : (0 : ℝ) < 1 + (E.gradSup s f.1).toReal := by linarith
        have h1 := (le_div_iff₀ hpos).mp hδb
        nlinarith [δ.2]
      calc E.gradSup s f.1 * (δ : ℝ≥0∞)
          = ENNReal.ofReal ((E.gradSup s f.1).toReal * (δ : ℝ)) := by
            rw [ENNReal.ofReal_mul hGr, ENNReal.ofReal_toReal hGfin.ne, ENNReal.ofReal_coe_nnreal]
        _ ≤ ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_le_ofReal hprod
        _ = (r : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    · have hbound : Ambient.gradModulus f δ ≤ ENNReal.ofReal ((r : ℝ) / (40 * (M : ℝ))) := by
        refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
        exact ENNReal.ofReal_le_ofReal (hu x y (hxy.trans hδa))
      calc ENNReal.ofReal (40 * (M : ℝ)) * Ambient.gradModulus f δ
          ≤ ENNReal.ofReal (40 * (M : ℝ)) * ENNReal.ofReal ((r : ℝ) / (40 * (M : ℝ))) :=
            mul_le_mul' le_rfl hbound
        _ = ENNReal.ofReal (r : ℝ) := by
            rw [← ENNReal.ofReal_mul hM.le, mul_div_cancel₀ _ hM.ne']
        _ = (r : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
theorem claim_holds (hyp : AmbientMetric.Claim) : Claim := by
  intro s M E μ
  have hT : AmbientMetric.PeriodicReflectHalfPeriod s :=
    (hyp s E).2.2.2.2.2.2
  exact ⟨reflectTranslateIdentities_holds s E μ ℝ, reflectTranslateIdentities_holds s E μ ℂ, hT μ,
    reflectLiftInvariant_holds s hT E μ, translateModulusBound_holds s hyp M E,
    reflectModulusBound_holds s hyp M E μ, modulusFiniteTendsZero_holds s hyp M E⟩
end MirrorTranslation
end LimitSpaces
end YangMills.Construction
