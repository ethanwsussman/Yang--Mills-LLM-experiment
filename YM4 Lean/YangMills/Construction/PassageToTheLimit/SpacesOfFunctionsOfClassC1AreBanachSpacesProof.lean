import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpaces
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction
open MetricNotions TestFunctions FamilyTopology
namespace LimitSpaces.Ambient.C1Banach
section Metric
variable {X : Type*} {d : X → X → ℝ}
theorem isOpenWrt_compl_closureWrt (hd : IsMetricFunction d) (Z : Set X) :
    IsOpenWrt d (closureWrt d Z)ᶜ := by
  intro x hx
  have hsep : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z, r ≤ d x y := by
    by_contra hcon
    push Not at hcon
    exact hx hcon
  obtain ⟨r, hr, h⟩ := hsep
  refine ⟨r / 2, by positivity, fun z hz hzc => ?_⟩
  obtain ⟨y, hy, hzy⟩ := hzc (r / 2) (by positivity)
  have h1 := h y hy
  have h2 := hd.triangle x z y
  linarith
theorem isCompactWrt_closureWrt (hd : IsMetricFunction d) {W Z : Set X} (hW : IsCompactWrt d W)
    (hZ : closureWrt d Z ⊆ W) : IsCompactWrt d (closureWrt d Z) := by
  intro 𝒰 h𝒰 hcov
  obtain ⟨𝒱, h𝒱, hfin, hcov'⟩ := hW (insert (closureWrt d Z)ᶜ 𝒰)
    (by
      rintro U (rfl | hU)
      · exact isOpenWrt_compl_closureWrt hd Z
      · exact h𝒰 U hU)
    (fun x _ => by
      by_cases h : x ∈ closureWrt d Z
      · obtain ⟨U, hU, hxU⟩ := hcov h
        exact ⟨U, Or.inr hU, hxU⟩
      · exact ⟨_, Or.inl rfl, h⟩)
  refine ⟨𝒱 ∩ 𝒰, inter_subset_right, hfin.inter_of_left _, fun x hx => ?_⟩
  obtain ⟨U, hU, hxU⟩ := hcov' (hZ hx)
  rcases h𝒱 hU with rfl | hU'
  · exact absurd hx hxU
  · exact ⟨U, ⟨hU, hU'⟩, hxU⟩
theorem closureWrt_subset_of_isCompactWrt (hd : IsMetricFunction d) {W Z : Set X}
    (hW : IsCompactWrt d W) (hZ : Z ⊆ W) : closureWrt d Z ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨𝒰', h𝒰', hfin, hcov⟩ := hW {U | ∃ r : ℝ, 0 < r ∧ U = {y | r < d x y}}
    (by
      rintro U ⟨r, -, rfl⟩ y hy
      refine ⟨d x y - r, sub_pos.mpr hy, fun z hz => ?_⟩
      have h1 := hd.triangle x z y
      have h2 := hd.symm y z
      show r < d x z
      linarith)
    (fun w hw => by
      have hne : d x w ≠ 0 := fun h => hxW (((hd.eq_zero_iff x w).mp h) ▸ hw)
      have hpos : 0 < d x w := lt_of_le_of_ne (hd.nonneg x w) (Ne.symm hne)
      exact ⟨{y | d x w / 2 < d x y}, ⟨d x w / 2, by positivity, rfl⟩, by
        show d x w / 2 < d x w
        linarith⟩)
  have key : ∀ T : Finset (Set X), (∀ U ∈ T, ∃ r : ℝ, 0 < r ∧ U = {y | r < d x y}) →
      ∃ r : ℝ, 0 < r ∧ ∀ U ∈ T, U ⊆ {y | r < d x y} := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | insert a T ha ih =>
      intro h
      obtain ⟨r, hr, hrT⟩ := ih (fun U hU => h U (Finset.mem_insert_of_mem hU))
      obtain ⟨r', hr', ha'⟩ := h a (Finset.mem_insert_self _ _)
      refine ⟨min r r', lt_min hr hr', fun U hU y hy => ?_⟩
      rcases Finset.mem_insert.mp hU with rfl | hU
      · rw [ha'] at hy
        have hy' : r' < d x y := hy
        exact lt_of_le_of_lt (min_le_right _ _) hy'
      · have hy' : r < d x y := hrT U hU hy
        exact lt_of_le_of_lt (min_le_left _ _) hy'
  obtain ⟨r, hr, hrU⟩ := key hfin.toFinset (fun U hU => h𝒰' (hfin.mem_toFinset.mp hU))
  obtain ⟨y, hy, hxy⟩ := hx r hr
  obtain ⟨U, hU, hyU⟩ := hcov (hZ hy)
  have h1 : r < d x y := hrU U (hfin.mem_toFinset.mpr hU) hyU
  linarith
end Metric
section UniformLimits
theorem exists_uniformLimit_of_uniformCauchy {α β : Type*} [NormedAddCommGroup β] [CompleteSpace β]
    (g : ℕ → α → β)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N, ∀ x, ‖g a x - g b x‖ ≤ ε) :
    ∃ l : α → β, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ x, ‖g a x - l x‖ ≤ ε := by
  have hc : ∀ x, CauchySeq (fun k => g k x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hg (ε / 2) (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hN a ha b hb x) (by linarith)
  choose l hl using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨l, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hg ε hε
  refine ⟨N, fun a ha x => ?_⟩
  have ht : Tendsto (fun b => ‖g a x - g b x‖) atTop (𝓝 ‖g a x - l x‖) :=
    (tendsto_const_nhds.sub (hl x)).norm
  exact le_of_tendsto ht (eventually_atTop.mpr ⟨N, fun b hb => hN a ha b hb x⟩)
theorem tendstoUniformly_of_norm_bound {α β : Type*} [NormedAddCommGroup β] (g : ℕ → α → β)
    (l : α → β) (h : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ x, ‖g a x - l x‖ ≤ ε) :
    TendstoUniformly g l atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N] with a ha x
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt (hN a ha x) (by linarith)
end UniformLimits
section Derivatives
theorem partialDerivR4_eq_fderiv {G : (Fin 4 → ℝ) → ℝ} {y : Fin 4 → ℝ}
    (h : DifferentiableAt ℝ G y) (μ : Fin 4) :
    partialDerivR4 μ G y = fderiv ℝ G y (Pi.single μ 1) := by
  have hline : HasDerivAt (fun t : ℝ => y + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single μ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add y
  have hG : HasFDerivAt G (fderiv ℝ G y)
      (y + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by
    simpa using h.hasFDerivAt
  exact (hG.comp_hasDerivAt (0 : ℝ) hline).deriv
theorem norm_single_one_le (μ : Fin 4) : ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun ν => ?_
  by_cases h : ν = μ
  · subst h
    simp
  · simp [h]
theorem opNorm_le_sum_abs_single (L : (Fin 4 → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ μ, |L (Pi.single μ 1)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  have hv : L v = ∑ μ, v μ * L (Pi.single μ 1) := by
    have hsum : v = ∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
      funext ν
      simp [Finset.sum_apply, Pi.single_apply]
    calc L v = L (∑ μ, v μ • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by rw [← hsum]
      _ = _ := by simp [map_sum]
  rw [hv]
  calc ‖∑ μ, v μ * L (Pi.single μ 1)‖ ≤ ∑ μ, ‖v μ * L (Pi.single μ 1)‖ := norm_sum_le _ _
    _ ≤ ∑ μ, ‖v‖ * |L (Pi.single μ 1)| := Finset.sum_le_sum fun μ _ => by
        rw [norm_mul, Real.norm_eq_abs (L _)]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v μ) (abs_nonneg _)
    _ = (∑ μ, |L (Pi.single μ 1)|) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
end Derivatives
section Norm
variable {s : Conventions.StandingParameters} {E : Ambient}
theorem abs_le_normC1 {f : E.Carrier s → ℝ} (hb : IsBoundedFun f) (x : E.Carrier s) :
    |f x| ≤ E.normC1 s f := by
  obtain ⟨C, hC⟩ := hb
  refine le_max_of_le_left (le_ciSup (f := fun x => ‖f x‖) ⟨C, ?_⟩ x)
  rintro _ ⟨x, rfl⟩
  exact hC x
theorem abs_partialDeriv_le_normC1 {f : E.Carrier s → ℝ}
    (hb : ∃ C : ℝ, ∀ x, TorusMetric.euclidNormVec (E.grad s f x) ≤ C) (μ : Fin 4)
    (x : E.Carrier s) : |E.partialDeriv s μ f x| ≤ E.normC1 s f := by
  obtain ⟨C, hC⟩ := hb
  have h1 : ∀ x, |E.partialDeriv s μ f x| ≤ C :=
    fun x => (abs_apply_le_euclidNormVec _ μ).trans (hC x)
  refine le_max_of_le_right ?_
  refine (le_ciSup (f := fun x => ‖E.partialDeriv s μ f x‖) ⟨C, ?_⟩ x).trans ?_
  · rintro _ ⟨x, rfl⟩
    exact h1 x
  · exact le_ciSup (f := fun μ : Fin 4 => uniformNorm (E.partialDeriv s μ f))
      (Set.finite_range _).bddAbove μ
theorem normC1_le_of_forall {f : E.Carrier s → ℝ} {ε : ℝ} (h0 : ∀ x, |f x| ≤ ε)
    (h1 : ∀ μ x, |E.partialDeriv s μ f x| ≤ ε) : E.normC1 s f ≤ ε := by
  have : Nonempty (E.Carrier s) := ⟨0⟩
  exact max_le (ciSup_le h0) (ciSup_le fun μ => ciSup_le (h1 μ))
theorem partialDerivR4_liftFun (f : E.Carrier s → ℝ) (μ : Fin 4) (y : Fin 4 → ℝ) :
    partialDerivR4 μ (E.liftFun s f) y = E.partialDeriv s μ f (E.proj s y) :=
  (congrFun (congrFun (E.grad_comp_proj s f) y) μ).symm
theorem cauchySeq_tendsto_c1Within {W : Set (E.Carrier s)} (hd : IsMetricFunction (E.pointDist s))
    (hW : E.IsCompactSubset s W)
    (hDesc : E.c1Within s W = {f | E.IsC1 s f ∧ E.closedSupport s f ⊆ W})
    (hsub : ∀ f ∈ E.c1Within s W, ∀ g ∈ E.c1Within s W, f - g ∈ E.c1Within s W)
    (hbd : ∀ f ∈ E.c1Within s W, IsBoundedFun f ∧
      ∃ C : ℝ, ∀ x, TorusMetric.euclidNormVec (E.grad s f x) ≤ C)
    (u : ℕ → E.Carrier s → ℝ) (hu : ∀ k, u k ∈ E.c1Within s W)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ b ≥ N, E.normC1 s (u a - u b) < ε) :
    ∃ f ∈ E.c1Within s W, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, E.normC1 s (u a - f) < ε := by
  let F : ℕ → (Fin 4 → ℝ) → ℝ := fun k => E.liftFun s (u k)
  have hF : ∀ k, ContDiff ℝ 1 (F k) := fun k => (hu k).1.1
  have hFd : ∀ k y, DifferentiableAt ℝ (F k) y :=
    fun k y => ((hF k).differentiable (by norm_num)) y
  have hw := fun a b => hsub _ (hu a) _ (hu b)
  have hD : ∀ a b y, ‖fderiv ℝ (F a) y - fderiv ℝ (F b) y‖ ≤ 4 * E.normC1 s (u a - u b) := by
    intro a b y
    refine (opNorm_le_sum_abs_single _).trans ?_
    have hμ : ∀ μ : Fin 4, |(fderiv ℝ (F a) y - fderiv ℝ (F b) y) (Pi.single μ 1)| ≤
        E.normC1 s (u a - u b) := by
      intro μ
      have hder : HasFDerivAt (E.liftFun s (u a - u b)) (fderiv ℝ (F a) y - fderiv ℝ (F b) y) y :=
        (hFd a y).hasFDerivAt.sub (hFd b y).hasFDerivAt
      rw [← hder.fderiv, ← partialDerivR4_eq_fderiv hder.differentiableAt, partialDerivR4_liftFun]
      exact abs_partialDeriv_le_normC1 (hbd _ (hw a b)).2 μ _
    calc _ ≤ ∑ _μ : Fin 4, E.normC1 s (u a - u b) := Finset.sum_le_sum fun μ _ => hμ μ
      _ = _ := by simp
  obtain ⟨f, hf⟩ := exists_uniformLimit_of_uniformCauchy u (fun ε hε => by
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun a ha b hb x =>
      (abs_le_normC1 (hbd _ (hw a b)).1 x).trans (hN a ha b hb).le⟩)
  obtain ⟨L, hL⟩ := exists_uniformLimit_of_uniformCauchy (fun k y => fderiv ℝ (F k) y)
    (fun ε hε => by
      obtain ⟨N, hN⟩ := hC (ε / 4) (by positivity)
      refine ⟨N, fun a ha b hb y => (hD a b y).trans ?_⟩
      have h := (hN a ha b hb).le
      linarith)
  have tf := tendstoUniformly_of_norm_bound u f hf
  have tL := tendstoUniformly_of_norm_bound _ L hL
  have hpt : ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (f x)) := fun x => tf.tendsto_at x
  have hφ : ∀ y, HasFDerivAt (E.liftFun s f) (L y) y := fun y =>
    hasFDerivAt_of_tendstoUniformlyOn isOpen_univ (tendstoUniformlyOn_univ.mpr tL)
      (fun k x _ => (hFd k x).hasFDerivAt) (fun x _ => hpt (E.proj s x)) (mem_univ y)
  have hLc : Continuous L :=
    tL.continuous (Frequently.of_forall fun k => (hF k).continuous_fderiv (by norm_num))
  have hC1 : E.IsC1 s f := by
    have hfd : fderiv ℝ (E.liftFun s f) = L := funext fun y => (hφ y).fderiv
    exact contDiff_one_iff_fderiv.mpr ⟨fun y => (hφ y).differentiableAt, hfd ▸ hLc⟩
  have hsupp : E.closedSupport s f ⊆ W := by
    refine closureWrt_subset_of_isCompactWrt hd hW ?_
    intro x hx
    by_contra hxW
    have h0 : ∀ k, u k x = 0 := by
      intro k
      by_contra hk
      refine hxW ((hu k).2.2 fun r hr => ⟨x, hk, ?_⟩)
      rw [(hd.eq_zero_iff x x).mpr rfl]
      exact hr
    have hlim : Tendsto (fun k => u k x) atTop (𝓝 0) := by
      simp [h0]
    exact hx (tendsto_nhds_unique (hpt x) hlim)
  have hfV : f ∈ E.c1Within s W := by
    rw [hDesc]
    exact ⟨hC1, hsupp⟩
  refine ⟨f, hfV, fun ε hε => ?_⟩
  obtain ⟨N1, h1⟩ := hf (ε / 2) (by positivity)
  obtain ⟨N2, h2⟩ := hL (ε / 2) (by positivity)
  refine ⟨max N1 N2, fun a ha => ?_⟩
  have hle : E.normC1 s (u a - f) ≤ ε / 2 := by
    refine normC1_le_of_forall (fun x => h1 a ((le_max_left _ _).trans ha) x) (fun μ x => ?_)
    have hdiff : HasFDerivAt (E.liftFun s (u a - f))
        (fderiv ℝ (F a) (E.someLift s x) - L (E.someLift s x)) (E.someLift s x) :=
      (hFd a _).hasFDerivAt.sub (hφ _)
    have hval : E.partialDeriv s μ (u a - f) x =
        (fderiv ℝ (F a) (E.someLift s x) - L (E.someLift s x)) (Pi.single μ 1) := by
      show partialDerivR4 μ (E.liftFun s (u a - f)) (E.someLift s x) = _
      rw [partialDerivR4_eq_fderiv hdiff.differentiableAt, hdiff.fderiv]
    rw [hval]
    calc _ ≤ ‖fderiv ℝ (F a) (E.someLift s x) - L (E.someLift s x)‖ *
          ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε / 2 * 1 := mul_le_mul (h2 a ((le_max_right _ _).trans ha) _) (norm_single_one_le μ)
          (norm_nonneg _) (by positivity)
      _ = ε / 2 := mul_one _
  linarith
end Norm
theorem c1WithinComplete_holds (hSpace : AmbientMetric.Claim)
    (hProd : testSpacesAndSepTuples) : c1WithinComplete := by
  intro s E W hW
  have hd : IsMetricFunction (E.pointDist s) := (hSpace s E).1.2.1
  have hDesc : E.c1Within s W = {f | E.IsC1 s f ∧ E.closedSupport s f ⊆ W} := by
    ext f
    constructor
    · rintro ⟨⟨h1, -⟩, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      have hc : E.IsCompactSubset s (E.closedSupport s f) := isCompactWrt_closureWrt hd hW h2
      exact ⟨⟨h1, hc⟩, hc, h2⟩
  obtain ⟨-, -, ⟨S, hS⟩, -, -, hN0, hN1, hN2, hN3⟩ :=
    (hProd s E ⟨1, Set.mem_Ici.mpr le_rfl⟩ W W 1 le_rfl).1
  have hbd : ∀ f ∈ E.c1Within s W, IsBoundedFun f ∧
      ∃ C : ℝ, ∀ x, TorusMetric.euclidNormVec (E.grad s f x) ≤ C := by
    intro f hf
    obtain ⟨-, h2, -, h4, -⟩ := (hSpace s E).2.2.1 f hf.1
    exact ⟨h2, h4⟩
  have hmem : ∀ f, f ∈ E.c1Within s W ↔ f ∈ S := fun f => by
    rw [← hS]
    rfl
  refine ⟨hDesc, ?_⟩
  exact
    { zero_mem := (hmem 0).mpr S.zero_mem
      lincomb_mem := fun f hf g hg a b => (hmem _).mpr
        (S.add_mem (S.smul_mem a ((hmem f).mp hf)) (S.smul_mem b ((hmem g).mp hg)))
      norm_eq_zero_iff := fun f hf => ⟨hN1 f hf, fun h => by
        subst h
        simpa using hN2 0 0 hf⟩
      norm_smul := fun f hf a => hN2 a f hf
      norm_add_le := hN3
      cauchy_tendsto := fun u hu hC => cauchySeq_tendsto_c1Within hd hW hDesc
        (fun f hf g hg => (hmem _).mpr (S.sub_mem ((hmem f).mp hf) ((hmem g).mp hg)))
        hbd u hu hC }
end LimitSpaces.Ambient.C1Banach
end YangMills.Construction
end
