import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfAMovedExponentialProof
import YangMills.Construction.SummableBoundsOfTheFlow.GaugeOfAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Estimates
namespace YangMills.Construction.GaugeAlongMotion
section calculus
variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]
theorem exists_isOpen_contDiffOn_of_contDiffAt {f : E₁ → E₂} {x : E₁} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) :
    ∃ U : Set E₁, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ n f U := by
  obtain ⟨u, hu, h⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U, hUu, hU, hxU⟩ := mem_nhds_iff.1 hu
  exact ⟨U, hU, hxU, h.mono hUu⟩
theorem iteratedFDeriv_comp_eq_sum_orderedFinpartition {E₃ : Type*} [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] {g : E₂ → E₃} {β : E₁ → E₂} {x : E₁} {n : ℕ}
    (hg : ContDiffAt ℝ n g (β x)) (hβ : ContDiffAt ℝ n β x) (v : Fin n → E₁) :
    iteratedFDeriv ℝ n (g ∘ β) x v = ∑ c : OrderedFinpartition n,
      iteratedFDeriv ℝ c.length g (β x)
        (c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x) v) := by
  obtain ⟨U, hU, hxU, hgU⟩ := exists_isOpen_contDiffOn_of_contDiffAt hg
  obtain ⟨S₀, hS₀, hxS₀, hβS⟩ := exists_isOpen_contDiffOn_of_contDiffAt hβ
  have hcont : ContinuousAt β x := hβ.continuousAt
  obtain ⟨S, hSS, hS, hxS⟩ := mem_nhds_iff.1
    (Filter.inter_mem (hS₀.mem_nhds hxS₀) (hcont (hU.mem_nhds hxU)))
  have hβ' : ContDiffOn ℝ n β S := hβS.mono fun y hy => (hSS hy).1
  have hmaps : Set.MapsTo β S U := fun y hy => (hSS hy).2
  have hTg := hgU.ftaylorSeriesWithin hU.uniqueDiffOn
  have hTβ := hβ'.ftaylorSeriesWithin hS.uniqueDiffOn
  have hT := hTg.comp hTβ hmaps
  have he := hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) le_rfl hS.uniqueDiffOn hxS
  rw [iteratedFDerivWithin_of_isOpen n hS hxS] at he
  rw [← he]
  simp only [FormalMultilinearSeries.taylorComp, _root_.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ftaylorSeriesWithin]
  rw [iteratedFDerivWithin_of_isOpen _ hU (hmaps hxS)]
  congr 1
  ext m
  simp only [OrderedFinpartition.applyOrderedFinpartition_apply]
  rw [iteratedFDerivWithin_of_isOpen _ hS hxS]
theorem norm_iteratedFDeriv_comp_single_le {p n : ℕ} {g : E₁ → E₂} {β : (Fin p → ℝ) → E₁}
    {x : Fin p → ℝ} (hg : ContDiffAt ℝ n g (β x)) (hβ : ContDiffAt ℝ n β x) (ω : Fin p → ℝ)
    (h0 : ∀ i, 0 ≤ ω i) (h1 : ∀ i, ω i ≤ 1) (A : ℕ → ℝ) (hA : ∀ r, 0 ≤ A r)
    (hpart : ∀ (r : ℕ) (J : Fin r → Fin p) (l : Fin r), r ≤ n →
      ‖iteratedFDeriv ℝ r β x fun q => Pi.single (J q) 1‖ ≤ A r * ω (J l))
    {r : ℕ} (J : Fin r → Fin p) (l : Fin r) (hr : r ≤ n) :
    ‖iteratedFDeriv ℝ r (g ∘ β) x fun q => Pi.single (J q) 1‖ ≤
      (∑ c : OrderedFinpartition r, ‖iteratedFDeriv ℝ c.length g (β x)‖ * ∏ m, A (c.partSize m)) *
        ω (J l) := by
  have hr' : ((r : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hr
  rw [iteratedFDeriv_comp_eq_sum_orderedFinpartition (hg.of_le hr') (hβ.of_le hr'),
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  set m₀ := c.index l with hm₀
  have hl : c.emb m₀ (c.invEmbedding l) = l := c.emb_invEmbedding l
  have hpm : ∀ m, c.partSize m ≤ n := fun m => (c.partSize_le m).trans hr
  have hbound : ∀ m, ‖c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x)
      (fun q => (Pi.single (J q) 1 : Fin p → ℝ)) m‖ ≤
        A (c.partSize m) * (if m = m₀ then ω (J l) else 1) := by
    intro m
    simp only [OrderedFinpartition.applyOrderedFinpartition_apply]
    have hcomp : ((fun q => (Pi.single (J q) 1 : Fin p → ℝ)) ∘ c.emb m) =
        fun q => Pi.single ((J ∘ c.emb m) q) 1 := rfl
    rw [hcomp]
    split_ifs with hm
    · subst hm
      have h := hpart (c.partSize (c.index l)) (J ∘ c.emb (c.index l)) (c.invEmbedding l) (hpm _)
      simpa [hl] using h
    · have h := hpart (c.partSize m) (J ∘ c.emb m) ⟨0, c.partSize_pos m⟩ (hpm _)
      refine h.trans ?_
      rw [mul_one]
      exact mul_le_of_le_one_right (hA _) (h1 _)
  calc ∏ m, ‖c.applyOrderedFinpartition (fun m => iteratedFDeriv ℝ (c.partSize m) β x)
        (fun q => (Pi.single (J q) 1 : Fin p → ℝ)) m‖
      ≤ ∏ m, (A (c.partSize m) * (if m = m₀ then ω (J l) else 1)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m _ => hbound m
    _ = (∏ m, A (c.partSize m)) * ω (J l) := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ m₀ (fun _ => ω (J l))]
        simp
end calculus
section quaternion
def imaginaryPart : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ⟨q - ((q.re : ℝ) : ℍ[ℝ]), by
        show (q - ((q.re : ℝ) : ℍ[ℝ])).re = 0
        simp⟩
      map_add' := fun q q' => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Quaternion.re_add, Quaternion.coe_add]
        abel
      map_smul' := fun u q => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        apply Quaternion.ext <;> simp [mul_sub] }
theorem coe_imaginaryPart_of_re_eq_zero {q : ℍ[ℝ]} (h : q.re = 0) :
    ((imaginaryPart q : imaginaryQuaternions) : ℍ[ℝ]) = q := by
  show q - ((q.re : ℝ) : ℍ[ℝ]) = q
  simp [h]
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem contDiff_quaternionExp (n : ℕ) : ContDiff ℝ n (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem exists_local_logarithm (n : ℕ) : ∃ (Lg : ℍ[ℝ] → imaginaryQuaternions) (U : Set ℍ[ℝ]),
    U ∈ 𝓝 (1 : ℍ[ℝ]) ∧ ContDiffAt ℝ n Lg 1 ∧ Lg 1 = 0 ∧
    ∀ g ∈ U, ‖g‖ = 1 → NormedSpace.exp ((Lg g : imaginaryQuaternions) : ℍ[ℝ]) = g := by
  have hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) 0 :=
    (contDiff_quaternionExp (n + 1)).contDiffAt
  have hf' : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
      ((ContinuousLinearEquiv.refl ℝ ℍ[ℝ] : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])
  have hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  let e := hf.toOpenPartialHomeomorph NormedSpace.exp hf' hn
  have h0 : NormedSpace.exp (0 : ℍ[ℝ]) = 1 := NormedSpace.exp_zero
  have hL := hf.to_localInverse hf' hn
  rw [h0] at hL
  have hmem : (1 : ℍ[ℝ]) ∈ e.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target hf' hn
    rwa [h0] at this
  refine ⟨fun g => imaginaryPart (hf.localInverse hf' hn g), e.target,
    e.open_target.mem_nhds hmem, ?_, ?_, ?_⟩
  · exact (imaginaryPart.contDiff.contDiffAt.comp 1 (hL.of_le (by exact_mod_cast Nat.le_succ n)))
  · have := hf.localInverse_apply_image hf' hn
    rw [h0] at this
    show imaginaryPart (hf.localInverse hf' hn 1) = 0
    rw [this, map_zero]
  · intro g hg hu
    set q := hf.localInverse hf' hn g with hq
    have he : NormedSpace.exp q = g := e.right_inv hg
    have hre : q.re = 0 := by
      have h1 : ‖NormedSpace.exp q‖ = Real.exp q.re := by
        rw [Quaternion.norm_exp, ← Real.exp_eq_exp_ℝ, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [he, hu] at h1
      have := Real.exp_eq_one_iff q.re
      exact this.1 h1.symm
    simp only
    rw [coe_imaginaryPart_of_re_eq_zero hre, he]
end quaternion
section bond
def tripleExp (z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) : ℍ[ℝ] :=
  NormedSpace.exp (z.1 : ℍ[ℝ]) * NormedSpace.exp (z.2.1 : ℍ[ℝ]) *
    NormedSpace.exp (-(z.2.2 : ℍ[ℝ]))
theorem contDiff_tripleExp (n : ℕ) : ContDiff ℝ n tripleExp := by
  have h1 : ContDiff ℝ n
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions =>
        (z.1 : ℍ[ℝ])) :=
    (imaginaryQuaternions.subtypeL.contDiff).comp contDiff_fst
  have h2 : ContDiff ℝ n
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions =>
        (z.2.1 : ℍ[ℝ])) :=
    (imaginaryQuaternions.subtypeL.contDiff).comp (contDiff_fst.comp contDiff_snd)
  have h3 : ContDiff ℝ n
      (fun z : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions =>
        -(z.2.2 : ℍ[ℝ])) :=
    ((imaginaryQuaternions.subtypeL.contDiff).comp (contDiff_snd.comp contDiff_snd)).neg
  exact (((contDiff_quaternionExp n).comp h1).mul ((contDiff_quaternionExp n).comp h2)).mul
    ((contDiff_quaternionExp n).comp h3)
theorem iteratedFDeriv_const_add_clm_of_two_le {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂) (v₀ : E₂)
    {r : ℕ} (hr : 2 ≤ r) (x : E₁) : iteratedFDeriv ℝ r (fun τ => v₀ + L τ) x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have hfd : fderiv ℝ (fun τ => v₀ + L τ) = fun _ => L := by
    funext y
    exact ((L.hasFDerivAt).const_add v₀).fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, hfd]
  simp only [Function.comp_apply, iteratedFDeriv_const_of_ne hm, Pi.zero_apply]
  exact (continuousMultilinearCurryRightEquiv' ℝ m E₁ E₂).symm.map_zero
theorem iteratedFDeriv_one_const_add_clm {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (L : E₁ →L[ℝ] E₂) (v₀ : E₂)
    (x : E₁) (v : Fin 1 → E₁) : iteratedFDeriv ℝ 1 (fun τ => v₀ + L τ) x v = L (v 0) := by
  rw [iteratedFDeriv_one_apply, ((L.hasFDerivAt).const_add v₀).fderiv]
theorem iteratedFDeriv_prodMk_apply {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] {f : E₁ → E₂} {g : E₁ → E₃} {x : E₁} {q : ℕ} (hf : ContDiffAt ℝ q f x)
    (hg : ContDiffAt ℝ q g x) (v : Fin q → E₁) :
    iteratedFDeriv ℝ q (fun τ => (f τ, g τ)) x v =
      (iteratedFDeriv ℝ q f x v, iteratedFDeriv ℝ q g x v) := by
  have hβ : ContDiffAt ℝ q (fun τ => (f τ, g τ)) x := hf.prodMk hg
  have h1 := (ContinuousLinearMap.fst ℝ E₂ E₃).iteratedFDeriv_comp_left hβ (i := q) le_rfl
  have h2 := (ContinuousLinearMap.snd ℝ E₂ E₃).iteratedFDeriv_comp_left hβ (i := q) le_rfl
  have e1 := congrArg (fun M => M v) h1
  have e2 := congrArg (fun M => M v) h2
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at e1 e2
  exact Prod.ext e1.symm e2.symm
theorem norm_iteratedFDeriv_linear_single_le {p : ℕ} (Lm : (Fin p → ℝ) →L[ℝ] imaginaryQuaternions)
    (ω : Fin p → ℝ) {B : ℝ} (h0 : ∀ l, 0 ≤ ω l) (hB : 0 ≤ B)
    (hL : ∀ l, ‖Lm (Pi.single l 1)‖ ≤ B * ω l) {q : ℕ} (J : Fin q → Fin p) (l : Fin q) :
    ‖iteratedFDeriv ℝ q (fun τ => (0 : imaginaryQuaternions) + Lm τ) 0
      fun e => Pi.single (J e) 1‖ ≤ B * ω (J l) := by
  by_cases h2 : 2 ≤ q
  · rw [iteratedFDeriv_const_add_clm_of_two_le _ _ h2]
    simpa using mul_nonneg hB (h0 _)
  · have hq : q = 1 := by
      have : q ≠ 0 := fun e => by subst e; exact l.elim0
      omega
    subst hq
    rw [iteratedFDeriv_one_const_add_clm]
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    exact hL _
theorem expUnit_neg (w : imaginaryQuaternions) : expUnit (-w) = (expUnit w)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.expUnit_neg <;> assumption
theorem expUnit_adjointAction (g : UnitQuaternion) (v : imaginaryQuaternions) :
    expUnit (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g v) = g * expUnit v * g⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.expUnit_adjointAction <;> assumption
theorem hasFDerivAt_exp_comp_of_eq_zero {p : ℕ} {h : (Fin p → ℝ) → imaginaryQuaternions}
    {h' : (Fin p → ℝ) →L[ℝ] imaginaryQuaternions} (hd : HasFDerivAt h h' 0) (h0 : h 0 = 0) :
    HasFDerivAt (fun τ => NormedSpace.exp ((h τ : imaginaryQuaternions) : ℍ[ℝ]))
      (imaginaryQuaternions.subtypeL.comp h') 0 := by
  have h1 : HasFDerivAt (fun τ => ((h τ : imaginaryQuaternions) : ℍ[ℝ]))
      (imaginaryQuaternions.subtypeL.comp h') 0 :=
    imaginaryQuaternions.subtypeL.hasFDerivAt.comp 0 hd
  have h2 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      (((h 0 : imaginaryQuaternions)) : ℍ[ℝ]) := by
    rw [h0]
    exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])
  have h3 := h2.comp (0 : Fin p → ℝ) h1
  exact h3.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
end bond
def coordinateCombination {p : ℕ} (g : Fin p → imaginaryQuaternions) :
    (Fin p → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ).smulRight (g l)
theorem coordinateCombination_apply {p : ℕ} (g : Fin p → imaginaryQuaternions) (τ : Fin p → ℝ) :
    coordinateCombination g τ = ∑ l, τ l • g l := by
  simp [coordinateCombination]
theorem coordinateCombination_single {p : ℕ} (g : Fin p → imaginaryQuaternions) (l : Fin p) :
    coordinateCombination g (Pi.single l 1) = g l := by
  rw [coordinateCombination_apply]
  simp [Pi.single_apply]
theorem coordinateCombination_adjointAction {p : ℕ} (W : UnitQuaternion)
    (g : Fin p → imaginaryQuaternions) (τ : Fin p → ℝ) :
    coordinateCombination (fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction W (g l)) τ =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction W (coordinateCombination g τ) := by
  rw [coordinateCombination_apply, coordinateCombination_apply]
  apply Subtype.ext
  show ((∑ l, τ l • _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction W (g l) : imaginaryQuaternions) : ℍ[ℝ]) =
    (W : ℍ[ℝ]) * ((∑ l, τ l • g l : imaginaryQuaternions) : ℍ[ℝ]) *
      ((W⁻¹ : UnitQuaternion) : ℍ[ℝ])
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show τ l • ((W : ℍ[ℝ]) * (g l : ℍ[ℝ]) * ((W⁻¹ : UnitQuaternion) : ℍ[ℝ])) = _
  simp [mul_smul_comm, smul_mul_assoc]
theorem gaugeAlongMotionStatement_holds : gaugeAlongMotionStatement := by
  intro n A B hA hB
  obtain ⟨Lg, U, hU, hLg, hL1, hexp⟩ := exists_local_logarithm n
  let A₀ : ℕ → ℝ := fun q => A q + B
  have hA₀ : ∀ q, 0 ≤ A₀ q := fun q => add_nonneg (hA q) hB
  let A₁ : ℕ → ℝ := fun r => ∑ c : OrderedFinpartition r,
    ‖iteratedFDeriv ℝ c.length tripleExp 0‖ * ∏ m, A₀ (c.partSize m)
  have hA₁ : ∀ q, 0 ≤ A₁ q := fun q => Finset.sum_nonneg fun c _ =>
    mul_nonneg (ContinuousMultilinearMap.opNorm_nonneg _) (Finset.prod_nonneg fun m _ => hA₀ _)
  let M : ℕ → ℝ := fun q => ∑ c : OrderedFinpartition q,
    ‖iteratedFDeriv ℝ c.length Lg 1‖ * ∏ m, A₁ (c.partSize m)
  have hM : ∀ q, 0 ≤ M q := fun q => Finset.sum_nonneg fun c _ =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun m _ => hA₁ _)
  refine ⟨M, hM, ?_⟩
  intro F j p W α ψ ω hper hα0 hαs hω0 hω1 hαp hψ
  classical
  have hne : ∀ i, NeZero (F.period j i) := fun i => ⟨hper i⟩
  let a₁ : F.Site j → (Fin p → ℝ) →L[ℝ] imaginaryQuaternions := fun x =>
    coordinateCombination fun l => ψ l x
  let a₃ : F.Site j → Fin 4 → (Fin p → ℝ) →L[ℝ] imaginaryQuaternions := fun x i =>
    coordinateCombination fun l => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (W x i) (ψ l (x + unitStep j i))
  let β : F.Site j → Fin 4 → (Fin p → ℝ) →
      imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions := fun x i τ =>
    (0 + a₁ x τ, α τ x i, 0 + a₃ x i τ)
  let Θ : F.Site j → Fin 4 → (Fin p → ℝ) → ℍ[ℝ] := fun x i => tripleExp ∘ β x i
  have hβ0 : ∀ x i, β x i 0 = 0 := fun x i => by
    simp only [β, map_zero, add_zero, hα0]
    rfl
  have hΘ0 : ∀ x i, Θ x i 0 = 1 := fun x i => by
    simp only [Θ, Function.comp, hβ0, tripleExp]
    simp
  have hβs : ∀ (N : ℕ), (N : WithTop ℕ∞) ≤ n → ∀ x i, ContDiffAt ℝ N (β x i) 0 := fun N hN x i =>
    (contDiffAt_const.add (a₁ x).contDiff.contDiffAt).prodMk
      (((hαs x i).of_le hN).prodMk (contDiffAt_const.add (a₃ x i).contDiff.contDiffAt))
  have hpart : ∀ x i (q : ℕ) (J : Fin q → Fin p) (l : Fin q), q ≤ n →
      ‖iteratedFDeriv ℝ q (β x i) 0 fun e => Pi.single (J e) 1‖ ≤ A₀ q * ω x i (J l) := by
    intro x i q J l hq
    have hq' : (q : WithTop ℕ∞) ≤ n := by exact_mod_cast hq
    set v : Fin q → Fin p → ℝ := fun e => Pi.single (J e) 1 with hv
    have h1 := norm_iteratedFDeriv_linear_single_le (a₁ x) (ω x i) (B := B) (hω0 x i) hB
      (fun l' => by
        simp only [a₁, coordinateCombination_single]
        exact (hψ x i l').1) J l
    have h3 := norm_iteratedFDeriv_linear_single_le (a₃ x i) (ω x i) (B := B) (hω0 x i) hB
      (fun l' => by
        simp only [a₃, coordinateCombination_single]
        have : ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (W x i) (ψ l' (x + unitStep j i))‖ = ‖ψ l' (x + unitStep j i)‖ := by
          show ‖((W x i : ℍ[ℝ]) * (ψ l' (x + unitStep j i) : ℍ[ℝ]) *
              ((W x i)⁻¹ : UnitQuaternion))‖ = ‖(ψ l' (x + unitStep j i) : ℍ[ℝ])‖
          rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion]
          simp
        rw [this]
        exact (hψ x i l').2) J l
    have h2 := hαp q J x i l hq
    have c1 : ContDiffAt ℝ q (fun τ => (0 : imaginaryQuaternions) + a₁ x τ) (0 : Fin p → ℝ) :=
      contDiffAt_const.add (a₁ x).contDiff.contDiffAt
    have c3 : ContDiffAt ℝ q (fun τ => (0 : imaginaryQuaternions) + a₃ x i τ) (0 : Fin p → ℝ) :=
      contDiffAt_const.add (a₃ x i).contDiff.contDiffAt
    have c2 : ContDiffAt ℝ q (fun τ => α τ x i) (0 : Fin p → ℝ) := (hαs x i).of_le hq'
    have hβe : iteratedFDeriv ℝ q (β x i) 0 v =
        (iteratedFDeriv ℝ q (fun τ => (0 : imaginaryQuaternions) + a₁ x τ) 0 v,
          iteratedFDeriv ℝ q (fun τ => α τ x i) 0 v,
          iteratedFDeriv ℝ q (fun τ => (0 : imaginaryQuaternions) + a₃ x i τ) 0 v) := by
      have e1 := iteratedFDeriv_prodMk_apply c1 (c2.prodMk c3) v
      have e2 := iteratedFDeriv_prodMk_apply c2 c3 v
      rw [e2] at e1
      exact e1
    rw [hβe]
    have hω := hω0 x i (J l)
    have hA' : A q * ω x i (J l) ≤ A₀ q * ω x i (J l) :=
      mul_le_mul_of_nonneg_right (by simp only [A₀]; linarith) hω
    have hB' : B * ω x i (J l) ≤ A₀ q * ω x i (J l) :=
      mul_le_mul_of_nonneg_right (by simp only [A₀]; linarith [hA q]) hω
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le (h1.trans hB') (max_le (h2.trans hA') (h3.trans hB'))
  have hΘs : ∀ x i, ContDiffAt ℝ n (Θ x i) 0 := fun x i =>
    ((contDiff_tripleExp n).contDiffAt).comp (0 : Fin p → ℝ) (hβs n le_rfl x i)
  have hpartΘ : ∀ x i (q : ℕ) (J : Fin q → Fin p) (l : Fin q), q ≤ n →
      ‖iteratedFDeriv ℝ q (Θ x i) 0 fun e => Pi.single (J e) 1‖ ≤ A₁ q * ω x i (J l) := by
    intro x i q J l hq
    have h1 := norm_iteratedFDeriv_comp_single_le (g := tripleExp) (β := β x i) (x := 0) (n := n)
      (contDiff_tripleExp n).contDiffAt (hβs n le_rfl x i) (ω x i) (hω0 x i) (hω1 x i) A₀ hA₀
      (hpart x i) J l hq
    simpa only [hβ0] using h1
  let α' : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions := fun τ x i => Lg (Θ x i τ)
  have hfun : ∀ x i, (fun τ => α' τ x i) = Lg ∘ Θ x i := fun x i => rfl
  have hα's : ∀ x i, ContDiffAt ℝ n (fun τ => α' τ x i) 0 := fun x i => by
    rw [hfun]
    exact ContDiffAt.comp (0 : Fin p → ℝ) (by rw [hΘ0]; exact hLg) (hΘs x i)
  have hunit : ∀ x i τ, ‖Θ x i τ‖ = 1 := fun x i τ => by
    have : Θ x i τ = ((expUnit (0 + a₁ x τ) * expUnit (α τ x i) * expUnit (-(0 + a₃ x i τ)) :
        UnitQuaternion) : ℍ[ℝ]) := by
      show tripleExp (β x i τ) = _
      simp only [tripleExp, β]
      rfl
    rw [this]
    exact norm_coe_unitQuaternion _
  have hev : ∀ᶠ τ in 𝓝 (0 : Fin p → ℝ), ∀ x i, Θ x i τ ∈ U := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (Θ x i) 0 := (hΘs x i).continuousAt
    exact hc.preimage_mem_nhds (by rw [hΘ0]; exact hU)
  have hgroup : ∀ τ x i, Θ x i τ ∈ U →
      expUnit (α' τ x i) = expUnit (a₁ x τ) * expUnit (α τ x i) * expUnit (-(a₃ x i τ)) := by
    intro τ x i hτ
    apply Subtype.ext
    show NormedSpace.exp ((Lg (Θ x i τ) : imaginaryQuaternions) : ℍ[ℝ]) = _
    rw [hexp _ hτ (hunit x i τ)]
    show tripleExp (β x i τ) = _
    simp only [tripleExp, β, zero_add]
    rfl
  refine ⟨α', fun x i => ?_, hα's, ?_, ?_, ?_⟩
  · show Lg (Θ x i 0) = 0
    rw [hΘ0, hL1]
  · filter_upwards [hev] with τ hτ
    funext x i
    show gaugeExponential ψ τ x * (expUnit (α τ x i) * W x i) *
        (gaugeExponential ψ τ (x + unitStep j i))⁻¹ = expUnit (α' τ x i) * W x i
    rw [hgroup τ x i (hτ x i)]
    have h1 : gaugeExponential ψ τ x = expUnit (a₁ x τ) := by
      simp only [gaugeExponential, a₁, coordinateCombination_apply]
    have h2 : expUnit (-(a₃ x i τ)) =
        (W x i * gaugeExponential ψ τ (x + unitStep j i) * (W x i)⁻¹)⁻¹ := by
      rw [expUnit_neg]
      congr 1
      simp only [a₃]
      rw [coordinateCombination_adjointAction, expUnit_adjointAction]
      simp only [gaugeExponential, coordinateCombination_apply]
    rw [h1, h2]
    group
  · intro hn1 l x i
    have hn0 : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    set h : (Fin p → ℝ) → imaginaryQuaternions := fun τ => α' τ x i with hh
    have h0 : h 0 = 0 := by
      show Lg (Θ x i 0) = 0
      rw [hΘ0, hL1]
    have hd : DifferentiableAt ℝ h 0 := (hα's x i).differentiableAt hn0
    have hd2 : DifferentiableAt ℝ (fun τ => α τ x i) 0 := (hαs x i).differentiableAt hn0
    have D1 := hasFDerivAt_exp_comp_of_eq_zero hd.hasFDerivAt h0
    have G1 : HasFDerivAt (fun τ => (0 : imaginaryQuaternions) + a₁ x τ) (a₁ x)
        (0 : Fin p → ℝ) :=
      ((a₁ x).hasFDerivAt).const_add 0
    have G3 : HasFDerivAt (fun τ => -((0 : imaginaryQuaternions) + a₃ x i τ)) (-(a₃ x i))
        (0 : Fin p → ℝ) :=
      (((a₃ x i).hasFDerivAt).const_add 0).neg
    have E1 := hasFDerivAt_exp_comp_of_eq_zero G1 (by simp)
    have E2 := hasFDerivAt_exp_comp_of_eq_zero hd2.hasFDerivAt (hα0 x i)
    have E3 := hasFDerivAt_exp_comp_of_eq_zero G3 (by simp)
    have P := (E1.mul' E2).mul' E3
    have hΘ : Θ x i =
        (fun τ => NormedSpace.exp (((0 : imaginaryQuaternions) + a₁ x τ : imaginaryQuaternions) :
          ℍ[ℝ])) *
        (fun τ => NormedSpace.exp ((α τ x i : imaginaryQuaternions) : ℍ[ℝ])) *
        fun τ => NormedSpace.exp ((-((0 : imaginaryQuaternions) + a₃ x i τ) :
          imaginaryQuaternions) : ℍ[ℝ]) := by
      funext τ
      show tripleExp (β x i τ) = _
      simp only [tripleExp, β, Pi.mul_apply, Submodule.coe_neg]
    have Q : HasFDerivAt (Θ x i) (imaginaryQuaternions.subtypeL.comp (fderiv ℝ h 0)) 0 := by
      refine D1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with τ hτ
      exact (hexp _ (hτ x i) (hunit x i τ)).symm
    rw [hΘ] at Q
    have R := Q.unique P
    have R' := congrArg (fun Lm : (Fin p → ℝ) →L[ℝ] ℍ[ℝ] => Lm (Pi.single l 1)) R
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Pi.mul_apply, map_zero, add_zero, hα0, neg_zero,
      ZeroMemClass.coe_zero, NormedSpace.exp_zero, one_mul, mul_one, one_smul,
      MulOpposite.op_one] at R'
    have hm : ∀ (g : (Fin p → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions),
        motionComponent g (fun _ : Fin 1 => l) x i =
          fderiv ℝ (fun τ => g τ x i) 0 (Pi.single l 1) := fun g => by
      simp only [motionComponent]
      rw [iteratedFDeriv_one_apply]
    rw [hm α', hm α]
    apply Subtype.ext
    have e1 : (a₁ x) (Pi.single l 1) = ψ l x := coordinateCombination_single _ l
    have e3 : (a₃ x i) (Pi.single l 1) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (W x i) (ψ l (x + unitStep j i)) :=
      coordinateCombination_single _ l
    have hneg : (-a₃ x i) (Pi.single l 1) = -(a₃ x i) (Pi.single l 1) := rfl
    rw [hneg, e3, e1] at R'
    have R2 : (((fderiv ℝ h 0) (Pi.single l 1) : imaginaryQuaternions) : ℍ[ℝ]) =
        ((-_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (W x i) (ψ l (x + unitStep j i)) : imaginaryQuaternions) : ℍ[ℝ]) +
          ((((fderiv ℝ (fun τ => α τ x i) 0) (Pi.single l 1) : imaginaryQuaternions) : ℍ[ℝ]) +
            ((ψ l x : imaginaryQuaternions) : ℍ[ℝ])) := R'
    rw [Submodule.coe_sub, Submodule.coe_add]
    show (((fderiv ℝ h 0) (Pi.single l 1) : imaginaryQuaternions) : ℍ[ℝ]) = _
    rw [R2, Submodule.coe_neg]
    abel
  · intro q e x i l hq
    simp only [motionComponent]
    rw [hfun]
    have h1 := norm_iteratedFDeriv_comp_single_le (g := Lg) (β := Θ x i) (x := 0) (n := n)
      (by rw [hΘ0]; exact hLg) (hΘs x i) (ω x i) (hω0 x i) (hω1 x i) A₁ hA₁ (hpartΘ x i) e l hq
    rw [hΘ0] at h1
    exact h1
end YangMills.Construction.GaugeAlongMotion
end
