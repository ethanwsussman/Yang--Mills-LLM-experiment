import YangMills.Construction.FourPointCondition.ConnectedLawOfAPairProof
import YangMills.Construction.ResponseInTheExpansion.TheFreeKernelAtAPairIsPositive
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace YangMills.Construction.LinearResponse
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
variable {S : ℝ}
private theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
private theorem torusProj_sub (v w : Fin 4 → ℝ) :
    torusProj S (v - w) = torusProj S v - torusProj S w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
private theorem torusEuclidNorm_nonneg (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private theorem torusEuclidNorm_torusProj_le (v : Fin 4 → ℝ) :
    torusEuclidNorm (torusProj S v) ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SourcesAndGluing.torusEuclidNorm_torusProj_le <;> assumption
private theorem torusEuclidNorm_add_le (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusEuclidNorm_sub_comm (x y : Torus4 S) :
    torusEuclidNorm (x - y) = torusEuclidNorm (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_sub_comm <;> assumption
private theorem torusEuclidNorm_sub_le_add (a b c : Torus4 S) :
    torusEuclidNorm (a - c) ≤ torusEuclidNorm (a - b) + torusEuclidNorm (b - c) := by
  simpa using torusEuclidNorm_add_le (a - b) (b - c)
private theorem torusEuclidNorm_torusProj_eq (hS : 0 < S) {v : Fin 4 → ℝ} (hv : ∀ μ, |v μ| ≤ S / 2) :
    torusEuclidNorm (torusProj S v) = euclidNormVec v := by apply _root_.YangMills.SharedProofs.p44320 <;> assumption
private theorem continuous_comp_torusProj {f : Torus4 S → ℝ} (hf : IsLipschitzFor euclidDistTorus f) :
    Continuous (f ∘ torusProj S) := by
  obtain ⟨C, -, hL⟩ := hf
  have hC : ∀ x y, ‖f x - f y‖ ≤ |C| * euclidDistTorus x y := fun x y =>
    (hL x y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (torusEuclidNorm_nonneg _))
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun w => |C| * euclidNormVec (w - v)) (𝓝 v) (𝓝 0) := by
    have hc : Continuous fun w : Fin 4 → ℝ => |C| * euclidNormVec (w - v) :=
      continuous_const.mul (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
    simpa [euclidNormVec] using hc.tendsto v
  refine squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h0
  calc ‖(f ∘ torusProj S) w - (f ∘ torusProj S) v‖
        ≤ |C| * euclidDistTorus (torusProj S w) (torusProj S v) := hC _ _
    _ ≤ |C| * euclidNormVec (w - v) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
      unfold euclidDistTorus
      rw [← torusProj_sub]
      exact torusEuclidNorm_torusProj_le _
abbrev _root_.YangMills.SharedProofs.p54921 := @continuous_comp_torusProj
private def latticeTranslateHom (S : ℝ) : (Fin 4 → ℤ) →+ (Fin 4 → ℝ) where
  toFun := latticeTranslate S
  map_zero' := by
    funext μ
    simp [latticeTranslate]
  map_add' := latticeTranslate_add S
private abbrev latticeSubgroup (S : ℝ) : AddSubgroup (Fin 4 → ℝ) := (latticeTranslateHom S).range
private instance (S : ℝ) : Countable (latticeSubgroup S) :=
  (latticeTranslateHom S).rangeRestrict_surjective.countable
private theorem isAddFundamentalDomain_cube (hS : 0 < S) (a : Fin 4 → ℝ) :
    IsAddFundamentalDomain (latticeSubgroup S) (Set.pi univ fun μ => Ico (a μ) (a μ + S)) volume := by
  refine IsAddFundamentalDomain.mk' ?_ ?_
  · exact (MeasurableSet.univ_pi fun μ => measurableSet_Ico).nullMeasurableSet
  · intro x
    have hex := fun μ => existsUnique_add_zsmul_mem_Ico hS (x μ) (a μ)
    choose k hk using fun μ => (hex μ).exists
    refine ⟨⟨latticeTranslate S k, k, rfl⟩, ?_, ?_⟩
    · intro μ _
      have h := hk μ
      have e : (k μ) • S = S * (k μ : ℝ) := by simp [mul_comm]
      rw [e] at h
      simpa [latticeTranslate, AddSubgroup.vadd_def, add_comm] using h
    · rintro ⟨_, k', rfl⟩ h
      have hk' : k' = k := by
        funext μ
        refine (hex μ).unique ?_ (hk μ)
        have h1 := h μ (mem_univ μ)
        have e : (k' μ) • S = S * (k' μ : ℝ) := by simp [mul_comm]
        rw [e]
        simpa [latticeTranslateHom, latticeTranslate, AddSubgroup.vadd_def, add_comm] using h1
      subst hk'
      rfl
private theorem setIntegral_cube_eq (hS : 0 < S) (a b : Fin 4 → ℝ) {g : (Fin 4 → ℝ) → ℝ}
    (hg : ∀ k v, g (v + latticeTranslate S k) = g v) :
    ∫ v in Set.pi univ (fun μ => Ico (a μ) (a μ + S)), g v =
      ∫ v in Set.pi univ (fun μ => Ico (b μ) (b μ + S)), g v := by
  refine (isAddFundamentalDomain_cube hS a).setIntegral_eq (isAddFundamentalDomain_cube hS b) ?_
  rintro ⟨_, k, rfl⟩ x
  change g (latticeTranslate S k + x) = g x
  rw [add_comm]
  exact hg k x
private theorem integral_liftToBall (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ} (hr : r ≤ S / 4)
    {f : Torus4 S → ℝ} (hf : tsupport f ⊆ closedBallTorus (torusProj S c) r) :
    ∫ v, liftToBall S c r f v = torusVolumeIntegral S f := by
  set Q : Set (Fin 4 → ℝ) := Set.pi univ fun μ => Ico (c μ - S / 2) (c μ - S / 2 + S) with hQ
  have hB : closedBallR4 c r ⊆ Q := by
    intro v hv μ _
    have h1 : |(v - c) μ| ≤ r := (abs_le_euclidNormVec (v - c) μ).trans hv
    have h2 := abs_le.mp h1
    simp only [Pi.sub_apply] at h2
    constructor <;> linarith [h2.1, h2.2]
  have hBm : MeasurableSet (closedBallR4 c r) :=
    (isClosed_le (continuous_euclidNormVec.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  have hQm : MeasurableSet Q := MeasurableSet.univ_pi fun μ => measurableSet_Ico
  have hper : ∀ k v, (f ∘ torusProj S) (v + latticeTranslate S k) = (f ∘ torusProj S) v := by
    intro k v
    simp [torusProj_add_latticeTranslate]
  have h1 : torusVolumeIntegral S f = ∫ v in Q, f (torusProj S v) := by
    have h := setIntegral_cube_eq hS (fun _ => 0) (fun μ => c μ - S / 2) hper
    change (∫ v in Set.pi univ fun _ : Fin 4 => Ico (0 : ℝ) S, f (torusProj S v)) = _
    simpa [hQ] using h
  have hzero : ∀ v ∈ Q \ closedBallR4 c r, f (torusProj S v) = 0 := by
    rintro v ⟨hvQ, hvB⟩
    by_contra hne
    refine hvB ?_
    have hm : torusProj S v ∈ closedBallTorus (torusProj S c) r := hf (subset_tsupport _ hne)
    have hm' : torusEuclidNorm (torusProj S v - torusProj S c) ≤ r := hm
    rw [← torusProj_sub, torusEuclidNorm_torusProj_eq hS] at hm'
    · exact hm'
    · intro μ
      have h2 := hvQ μ (mem_univ μ)
      simp only [Pi.sub_apply]
      rw [abs_le]
      constructor <;> linarith [h2.1, h2.2]
  rw [h1]
  unfold liftToBall
  rw [integral_indicator hBm]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm hB hzero).symm
abbrev _root_.YangMills.SharedProofs.p83706 := @integral_liftToBall
private theorem zpow_neg_eight (a : ℝ) : a ^ (-8 : ℤ) = (a ^ 8)⁻¹ := by
  rw [zpow_neg]
  norm_cast
private theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
private theorem kernel_lower_bound_on_ball {n : ℝ} (hn : 0 < n) (hS : 0 < S) {c : Fin 4 → ℝ} {r : ℝ}
    (hr : r ≤ S / 4) {f h : Torus4 S → ℝ}
    (hcf : Continuous (f ∘ torusProj S)) (hch : Continuous (h ∘ torusProj S))
    (hf0 : ∀ y, 0 ≤ f y) (hh0 : ∀ y, 0 ≤ h y)
    (hsf : tsupport f ⊆ closedBallTorus (torusProj S c) r)
    (hsh : tsupport h ⊆ closedBallTorus (torusProj S c) r)
    (hsep : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, n ≤ torusEuclidNorm (p - q))
    (hfar : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, torusEuclidNorm (p - q) ≤ 10 * n) :
    ((10 * n) ^ 8)⁻¹ * (torusVolumeIntegral S f * torusVolumeIntegral S h) ≤
      inverseEighthKernel (liftToBall S c r f) (liftToBall S c r h) := by
  set F : (Fin 4 → ℝ) → ℝ := liftToBall S c r f with hF
  set G : (Fin 4 → ℝ) → ℝ := liftToBall S c r h with hG
  have hK := isCompact_closedBallR4 c r
  have hBm : MeasurableSet (closedBallR4 c r) := hK.isClosed.measurableSet
  have hFi : Integrable F :=
    (hcf.continuousOn.integrableOn_compact hK).integrable_indicator hBm
  have hGi : Integrable G :=
    (hch.continuousOn.integrableOn_compact hK).integrable_indicator hBm
  have hFm : Measurable F := hcf.measurable.indicator hBm
  have hGm : Measurable G := hch.measurable.indicator hBm
  have hF0 : ∀ x, 0 ≤ F x := fun x => indicator_nonneg (fun y _ => hf0 _) x
  have hG0 : ∀ x, 0 ≤ G x := fun x => indicator_nonneg (fun y _ => hh0 _) x
  have hP : Integrable (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F z.1 * G z.2) := hFi.mul_prod hGi
  have hdist : ∀ x y, F x ≠ 0 → G y ≠ 0 →
      n ≤ euclidNormVec (x - y) ∧ euclidNormVec (x - y) ≤ 10 * n := by
    intro x y hx hy
    have hxB : x ∈ closedBallR4 c r := by
      by_contra hb
      exact hx (indicator_of_notMem hb _)
    have hyB : y ∈ closedBallR4 c r := by
      by_contra hb
      exact hy (indicator_of_notMem hb _)
    have hfx : f (torusProj S x) ≠ 0 := by
      intro h0
      apply hx
      rw [hF]
      unfold liftToBall
      rw [indicator_of_mem hxB]
      exact h0
    have hhy : h (torusProj S y) ≠ 0 := by
      intro h0
      apply hy
      rw [hG]
      unfold liftToBall
      rw [indicator_of_mem hyB]
      exact h0
    have hcoord : ∀ μ, |(x - y) μ| ≤ S / 2 := by
      intro μ
      have h1 : |(x - c) μ| ≤ r := (abs_le_euclidNormVec (x - c) μ).trans hxB
      have h2 : |(y - c) μ| ≤ r := (abs_le_euclidNormVec (y - c) μ).trans hyB
      have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      simp only [Pi.sub_apply] at h1' h2' ⊢
      rw [abs_le]
      constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
    have he : torusEuclidNorm (torusProj S x - torusProj S y) = euclidNormVec (x - y) := by
      rw [← torusProj_sub]
      exact torusEuclidNorm_torusProj_eq hS hcoord
    rw [← he]
    exact ⟨hsep _ (subset_tsupport _ hfx) _ (subset_tsupport _ hhy),
      hfar _ (subset_tsupport _ hfx) _ (subset_tsupport _ hhy)⟩
  have hn8 : 0 < n ^ 8 := by positivity
  set I : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ :=
    fun z => F z.1 * G z.2 * euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) with hI
  have hkm : Measurable fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) := by
    simp only [zpow_neg_eight]
    exact ((continuous_euclidNormVec.comp (continuous_fst.sub continuous_snd)).measurable.pow_const 8).inv
  have hIm : Measurable I :=
    ((hFm.comp measurable_fst).mul (hGm.comp measurable_snd)).mul hkm
  have hlow : ∀ z, F z.1 * G z.2 * ((10 * n) ^ 8)⁻¹ ≤ I z := by
    intro z
    have hPz : 0 ≤ F z.1 * G z.2 := mul_nonneg (hF0 _) (hG0 _)
    by_cases h1 : F z.1 = 0
    · simp [hI, h1]
    by_cases h2 : G z.2 = 0
    · simp [hI, h2]
    obtain ⟨hd1, hd2⟩ := hdist z.1 z.2 h1 h2
    have hd0 : 0 < euclidNormVec (z.1 - z.2) := lt_of_lt_of_le hn hd1
    simp only [hI, zpow_neg_eight]
    refine mul_le_mul_of_nonneg_left ?_ hPz
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hd0.le hd2 8)
  have hhigh : ∀ z, ‖I z‖ ≤ F z.1 * G z.2 * (n ^ 8)⁻¹ := by
    intro z
    have hPz : 0 ≤ F z.1 * G z.2 := mul_nonneg (hF0 _) (hG0 _)
    by_cases h1 : F z.1 = 0
    · simp [hI, h1]
    by_cases h2 : G z.2 = 0
    · simp [hI, h2]
    obtain ⟨hd1, -⟩ := hdist z.1 z.2 h1 h2
    have hd0 : 0 < euclidNormVec (z.1 - z.2) := lt_of_lt_of_le hn hd1
    simp only [hI, zpow_neg_eight]
    rw [Real.norm_of_nonneg (mul_nonneg hPz (by positivity))]
    refine mul_le_mul_of_nonneg_left ?_ hPz
    exact inv_anti₀ hn8 (pow_le_pow_left₀ hn.le hd1 8)
  have hIi : Integrable I :=
    (hP.mul_const ((n ^ 8)⁻¹)).mono' hIm.aestronglyMeasurable (Eventually.of_forall hhigh)
  have hprod : ∫ z : (Fin 4 → ℝ) × (Fin 4 → ℝ), F z.1 * G z.2 = (∫ x, F x) * ∫ y, G y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul F G
  have hkernel : inverseEighthKernel F G = ∫ z, I z := by
    simp only [inverseEighthKernel, hI, RCLike.ofReal_real_eq_id, id]
  rw [hkernel, ← integral_liftToBall hS hr hsf, ← integral_liftToBall hS hr hsh, ← hF, ← hG, ← hprod,
    mul_comm, ← integral_mul_const]
  exact integral_mono (hP.mul_const _) hIi hlow
private theorem kernel_lower_bound_on_torus {n vt : ℝ} (hn : 0 < n) (hvt : 0 < vt) (hS : 40 * n ≤ S)
    {f h : Torus4 S → ℝ} (hp : (f, h) ∈ separatedPairsTorus S n vt)
    (hf1 : uniformNorm f = 1) (hh1 : uniformNorm h = 1) :
    1 / 10 ^ 8 * vt ^ 2 ≤ inverseEighthKernelTorus f h := by
  have hS0 : 0 < S := by linarith
  obtain ⟨x₁, x₂, hbf, hbh, hlo, hhi⟩ := hp
  obtain ⟨hLf, hf0, -, hsf, hif, -⟩ := hbf
  obtain ⟨hLh, hh0, -, hsh, hih, -⟩ := hbh
  simp only at hLf hf0 hsf hif hLh hh0 hsh hih hlo hhi
  have hsep : ∀ p ∈ tsupport f, ∀ q ∈ tsupport h, n ≤ torusEuclidNorm (p - q) := by
    intro p hp q hq
    have h1 : setEuclidDist (tsupport f) (tsupport h) ≤ ENNReal.ofReal (torusEuclidNorm (p - q)) :=
      iInf₂_le_of_le p hp (iInf₂_le q hq)
    exact (ENNReal.ofReal_le_ofReal_iff (torusEuclidNorm_nonneg _)).mp (hlo.trans h1)
  have hnear : ∀ ε, 0 < ε → ∃ p ∈ tsupport f, ∃ q ∈ tsupport h,
      torusEuclidNorm (p - q) ≤ 6 * n + ε := by
    intro ε hε
    by_contra hno
    push Not at hno
    have h1 : ENNReal.ofReal (6 * n + ε) ≤ setEuclidDist (tsupport f) (tsupport h) :=
      le_iInf₂ fun p hp => le_iInf₂ fun q hq =>
        ENNReal.ofReal_le_ofReal (hno p hp q hq).le
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (h1.trans hhi)
    linarith
  have hinf : ∀ u ∈ tsupport f, torusEuclidNorm (u - x₁) ≤ n := fun u hu => hsf hu
  have hinh : ∀ w ∈ tsupport h, torusEuclidNorm (w - x₂) ≤ n := fun w hw => hsh hw
  have hfar : ∀ u ∈ tsupport f, ∀ w ∈ tsupport h, torusEuclidNorm (u - w) ≤ 10 * n := by
    intro u hu w hw
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨p, hp, q, hq, hpq⟩ := hnear ε hε
    have t1 := torusEuclidNorm_sub_le_add u x₁ w
    have t2 := torusEuclidNorm_sub_le_add x₁ p w
    have t3 := torusEuclidNorm_sub_le_add p q w
    have t4 := torusEuclidNorm_sub_le_add q x₂ w
    have e1 := hinf u hu
    have e2 := hinf p hp
    have e3 := hinh q hq
    have e4 := hinh w hw
    rw [torusEuclidNorm_sub_comm x₁ p] at t2
    rw [torusEuclidNorm_sub_comm x₂ w] at t4
    linarith
  have hwx : ∀ w ∈ tsupport h, torusEuclidNorm (w - x₁) ≤ 10 * n := by
    intro w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := hnear n hn
    have t1 := torusEuclidNorm_sub_le_add w x₂ x₁
    have t2 := torusEuclidNorm_sub_le_add x₂ q x₁
    have t3 := torusEuclidNorm_sub_le_add q p x₁
    have e2 := hinf p hp
    have e3 := hinh q hq
    have e4 := hinh w hw
    rw [torusEuclidNorm_sub_comm x₂ q] at t2
    rw [torusEuclidNorm_sub_comm q p] at t3
    linarith
  have hpos : 0 < setEuclidDist (tsupport f) (tsupport h) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hn) hlo
  have H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2 := by
    refine ⟨(liftPoint x₁, 10 * n), hpos, by simpa using hn, ?_, ?_, ?_⟩
    · simp only
      linarith
    · intro u hu
      change torusEuclidNorm (u - torusProj S (liftPoint x₁)) ≤ 10 * n
      rw [torusProj_liftPoint]
      linarith [hinf u hu]
    · intro w hw
      change torusEuclidNorm (w - torusProj S (liftPoint x₁)) ≤ 10 * n
      rw [torusProj_liftPoint]
      exact hwx w hw
  unfold inverseEighthKernelTorus
  rw [dif_pos H]
  obtain ⟨-, -, hr, hbf', hbh'⟩ := H.choose_spec
  have hmain := kernel_lower_bound_on_ball hn hS0 hr (continuous_comp_torusProj hLf)
    (continuous_comp_torusProj hLh) hf0 hh0 hbf' hbh' hsep hfar
  rw [hf1] at hif
  rw [hh1] at hih
  have hv : 0 < vt * 1 * n ^ 4 := by positivity
  have hprod : (vt * 1 * n ^ 4) * (vt * 1 * n ^ 4) ≤ torusVolumeIntegral S f * torusVolumeIntegral S h :=
    mul_le_mul hif hih hv.le (hv.le.trans hif)
  have hi : 0 ≤ ((10 * n) ^ 8)⁻¹ := by positivity
  have hval : 1 / 10 ^ 8 * vt ^ 2 = ((10 * n) ^ 8)⁻¹ * ((vt * 1 * n ^ 4) * (vt * 1 * n ^ 4)) := by
    field_simp
  rw [hval]
  exact (mul_le_mul_of_nonneg_left hprod hi).trans hmain
theorem freeKernelPositiveOnSeparatedPairs_holds : FreeKernelPositiveOnSeparatedPairs := by
  intro L m n vt hn hvt _ hside f h hp hf1 hh1
  exact kernel_lower_bound_on_torus hn hvt hside hp hf1 hh1
end YangMills.Construction.LinearResponse
end
