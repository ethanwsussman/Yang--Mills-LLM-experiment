import YangMills.Construction.Torus.CoveringMapOpenAndCompactSetsAndDerivativesOfTuples
import YangMills.Construction.Torus.DistancesAndLiftsOfTorusOrFourSpace
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.TorusMetric (euclidNormVec)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.GradientC1Bounds
variable {s : Conventions.StandingParameters} {E : Ambient}
abbrev flatIndex (μ : Fin 4) : Fin (4 * 1) := Fin.cast (by norm_num) μ
theorem sum_flatIndex {M : Type} [AddCommMonoid M] (f : Fin (4 * 1) → M) :
    ∑ j, f j = ∑ μ, f (flatIndex μ) :=
  (Equiv.sum_comp (finCongr (by norm_num : 4 = 4 * 1)) f).symm
def liftFun (g : Pt s E → ℂ) : (Fin (4 * 1) → ℝ) → ℂ :=
  ofSinglePoint g ∘ tupleProj s E 1
def embedFour (a : Fin 4 → ℝ) : Fin (4 * 1) → ℝ := flattenCoords 1 fun _ => a
theorem embedFour_flatIndex (a : Fin 4 → ℝ) (μ : Fin 4) : embedFour a (flatIndex μ) = a μ := by
  have h : 4 * ((0 : Fin 1) : ℕ) + (μ : ℕ) < 4 * 1 := by
    have := μ.2
    simp only [Fin.val_zero]
    omega
  have e : flatIndex μ = ⟨4 * ((0 : Fin 1) : ℕ) + (μ : ℕ), h⟩ := by
    ext
    simp [flatIndex]
  rw [e]
  exact flattenCoords_apply (fun _ => a) 0 μ h
theorem liftFun_embedFour (g : Pt s E → ℂ) (a : Fin 4 → ℝ) :
    liftFun g (embedFour a) = g (proj s E a) := by
  change g (tupleProj s E 1 (flattenCoords 1 fun _ => a) 0) = _
  rw [tupleProj_flattenCoords]
theorem iteratedPartial_single {D : ℕ} (j : Fin D) (G : (Fin D → ℝ) → ℂ) :
    iteratedPartial (Pi.single j 1 : PowerSeries.MultiIndex D) G = partialDeriv j G := by
  have key : ∀ l : List (Fin D), l.Nodup →
      l.foldr (fun i H => (partialDeriv i)^[(Pi.single j 1 : PowerSeries.MultiIndex D) i] H) G =
        if j ∈ l then partialDeriv j G else G := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      have hl' := List.nodup_cons.mp hl
      rw [List.foldr_cons, ih hl'.2]
      by_cases ha : a = j
      · subst ha
        simp [hl'.1]
      · have hj : j ≠ a := fun h => ha h.symm
        simp [ha, hj]
  rw [iteratedPartial, key _ (List.nodup_finRange D)]
  simp
theorem isCnOn_univ_one_iff_contDiff
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (G : (Fin (4 * 1) → ℝ) → ℂ) : IsCnOn univ 1 G ↔ ContDiff ℝ 1 G := by
  have h := hC 1 1 G
  rw [Nat.cast_one] at h
  refine Iff.trans ?_ h
  have h1 : IsCnOn univ (1 : ℕ∞) G ↔ IsCnOn univ ((1 : ℕ) : ℕ∞) G := by
    rw [Nat.cast_one]
  rw [h1, isCnOn_coe_iff]
  constructor
  · rintro ⟨-, h0, hj⟩
    refine ⟨continuousOn_univ.mp h0, fun j => ⟨fun x => (hj j).1 x (mem_univ x), ?_⟩⟩
    exact continuousOn_univ.mp (hj j).2
  · rintro ⟨h0, hj⟩
    refine ⟨isOpen_univ, h0.continuousOn, fun j => ⟨fun x _ => (hj j).1 x, ?_⟩⟩
    exact (hj j).2.continuousOn
theorem isCnAtPoint_one_iff_contDiff
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (g : Pt s E → ℂ) : IsCnAtPoint 1 g ↔ ContDiff ℝ 1 (liftFun g) :=
  isCnOn_univ_one_iff_contDiff hC _
theorem partialDeriv_eq_fderiv {G : (Fin (4 * 1) → ℝ) → ℂ} (hG : ContDiff ℝ 1 G)
    (j : Fin (4 * 1)) (w : Fin (4 * 1) → ℝ) :
    partialDeriv j G w = fderiv ℝ G w (Pi.single j 1) :=
  ((hG.differentiable (by norm_num)) w).lineDeriv_eq_fderiv
theorem partialAt_eq_partialDeriv_liftFun (hT : TupleDerivProps s E 1) {g : Pt s E → ℂ}
    (hg : IsCnAtPoint 1 g) (μ : Fin 4) (w : Fin (4 * 1) → ℝ) :
    partialAt μ g (tupleProj s E 1 w 0) =
      partialDeriv (flatIndex μ) (liftFun g) w := by
  have hsize : (((basisMultiIndex μ).order : ℕ) : ℕ∞) ≤ 1 := by
    rw [basisMultiIndex_order]
    simp
  obtain ⟨H, hH, -⟩ := ((hT 1 (ofSinglePoint g) hg).1 (basisMultiIndex μ) hsize).1
  have hd := multiDeriv_comp_tupleProj (α := basisMultiIndex μ) (F := ofSinglePoint g) ⟨H, hH⟩
  have hw := congrFun hd w
  have ht : (fun _ : Fin 1 => tupleProj s E 1 w 0) = tupleProj s E 1 w := by
    funext i
    rw [Subsingleton.elim i 0]
  rw [partialAt, ht]
  refine hw.trans ?_
  exact congrFun (iteratedPartial_single _ _) w
theorem exists_tupleProj_eq (x : Pt s E) : ∃ w, tupleProj s E 1 w 0 = x := by
  obtain ⟨w, hw⟩ := tupleProj_surjective s E 1 (fun _ => x)
  exact ⟨w, congrFun hw 0⟩
theorem partialAt_comp_clm (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (L : ℂ →L[ℝ] ℂ) {g : Pt s E → ℂ} (hg : IsCnAtPoint 1 g) :
    IsCnAtPoint 1 (fun x => L (g x)) ∧
      ∀ μ x, partialAt μ (fun x => L (g x)) x = L (partialAt μ g x) := by
  have hG := (isCnAtPoint_one_iff_contDiff hC g).mp hg
  have hL : ContDiff ℝ 1 (liftFun fun x => L (g x)) := L.contDiff.comp hG
  have hcl := (isCnAtPoint_one_iff_contDiff hC _).mpr hL
  refine ⟨hcl, fun μ x => ?_⟩
  obtain ⟨w, rfl⟩ := exists_tupleProj_eq x
  rw [partialAt_eq_partialDeriv_liftFun hT hcl, partialAt_eq_partialDeriv_liftFun hT hg,
    partialDeriv_eq_fderiv hL, partialDeriv_eq_fderiv hG]
  have hd : HasFDerivAt (liftFun fun x => L (g x)) (L.comp (fderiv ℝ (liftFun g) w)) w :=
    L.hasFDerivAt.comp w ((hG.differentiable (by norm_num)) w).hasFDerivAt
  rw [hd.fderiv]
  rfl
theorem partialAt_mul (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    {g h : Pt s E → ℂ} (hg : IsCnAtPoint 1 g) (hh : IsCnAtPoint 1 h) :
    IsCnAtPoint 1 (fun x => g x * h x) ∧
      ∀ μ x, partialAt μ (fun x => g x * h x) x =
        g x * partialAt μ h x + h x * partialAt μ g x := by
  have hG := (isCnAtPoint_one_iff_contDiff hC g).mp hg
  have hH := (isCnAtPoint_one_iff_contDiff hC h).mp hh
  have hM : ContDiff ℝ 1 (liftFun fun x => g x * h x) := hG.mul hH
  have hcl := (isCnAtPoint_one_iff_contDiff hC _).mpr hM
  refine ⟨hcl, fun μ x => ?_⟩
  obtain ⟨w, rfl⟩ := exists_tupleProj_eq x
  rw [partialAt_eq_partialDeriv_liftFun hT hcl, partialAt_eq_partialDeriv_liftFun hT hg,
    partialAt_eq_partialDeriv_liftFun hT hh,
    partialDeriv_eq_fderiv hM, partialDeriv_eq_fderiv hG, partialDeriv_eq_fderiv hH]
  have hd := (((hG.differentiable (by norm_num)) w).hasFDerivAt).mul
    (((hH.differentiable (by norm_num)) w).hasFDerivAt)
  have hd' : HasFDerivAt (liftFun fun x => g x * h x)
      (liftFun g w • fderiv ℝ (liftFun h) w + liftFun h w • fderiv ℝ (liftFun g) w) w := hd
  rw [hd'.fderiv]
  have e1 : liftFun g w = g (tupleProj s E 1 w 0) := rfl
  have e2 : liftFun h w = h (tupleProj s E 1 w 0) := rfl
  rw [← e1, ← e2]
  simp
def reToComplex : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
def imToComplex : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
theorem norm_reToComplex_le (z : ℂ) : ‖reToComplex z‖ ≤ ‖z‖ := by
  simpa [reToComplex] using Complex.abs_re_le_norm z
theorem norm_imToComplex_le (z : ℂ) : ‖imToComplex z‖ ≤ ‖z‖ := by
  simpa [imToComplex] using Complex.abs_im_le_norm z
theorem gradNorm_eq_norm_euclidean (g : Pt s E → ℂ) (x : Pt s E) :
    gradNorm g x = ‖(WithLp.toLp 2 (gradient g x) : EuclideanSpace ℂ (Fin 4))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl
theorem gradNorm_le_two_mul_iSup (g : Pt s E → ℂ) (x : Pt s E) :
    gradNorm g x ≤ 2 * ⨆ μ, ‖partialAt μ g x‖ := by
  have hm : ∀ μ, ‖partialAt μ g x‖ ≤ ⨆ μ, ‖partialAt μ g x‖ := fun μ =>
    le_ciSup (f := fun μ => ‖partialAt μ g x‖) (Set.finite_range _).bddAbove μ
  have h0 : 0 ≤ ⨆ μ, ‖partialAt μ g x‖ := (norm_nonneg _).trans (hm 0)
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑ μ, ‖gradient g x μ‖ ^ 2
      ≤ ∑ _μ : Fin 4, (⨆ μ, ‖partialAt μ g x‖) ^ 2 :=
        Finset.sum_le_sum fun μ _ => pow_le_pow_left₀ (norm_nonneg _) (hm μ) 2
    _ = (2 * ⨆ μ, ‖partialAt μ g x‖) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem gradNorm_mul_le (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    {g h : Pt s E → ℂ} (hg : IsCnAtPoint 1 g) (hh : IsCnAtPoint 1 h)
    (x : Pt s E) :
    gradNorm (fun y => g y * h y) x ≤ ‖g x‖ * gradNorm h x + ‖h x‖ * gradNorm g x := by
  have hv : (WithLp.toLp 2 (gradient (fun y => g y * h y) x) : EuclideanSpace ℂ (Fin 4)) =
      g x • (WithLp.toLp 2 (gradient h x) : EuclideanSpace ℂ (Fin 4)) +
        h x • (WithLp.toLp 2 (gradient g x) : EuclideanSpace ℂ (Fin 4)) := by
    ext μ
    simp [gradient, (partialAt_mul hT hC hg hh).2 μ x]
  rw [gradNorm_eq_norm_euclidean, gradNorm_eq_norm_euclidean h, gradNorm_eq_norm_euclidean g, hv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
theorem c1GradNorm_comp_clm_le (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (L : ℂ →L[ℝ] ℂ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) {g : Pt s E → ℂ}
    (hg : IsCnAtPoint 1 g) :
    c1GradNorm (fun x => L (g x)) ≤ c1GradNorm g := by
  have hp := (partialAt_comp_clm hT hC L hg).2
  refine max_le_max ?_ ?_
  · rw [tupleSupNorm_ofSinglePoint, tupleSupNorm_ofSinglePoint]
    exact iSup_mono fun x => ENNReal.ofReal_le_ofReal (hL _)
  · refine iSup_mono fun x => ENNReal.ofReal_le_ofReal ?_
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
    simp only [gradient]
    rw [hp μ x]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
theorem c1GradNorm_lt_top (hT : TupleDerivProps s E 1) {U : Pt s E → ℂ}
    (hU : IsCnAtPoint 1 U) (hc : IsCompact (closedSupport (ofSinglePoint U))) :
    c1GradNorm U < ⊤ := by
  have hN : cnNorm 1 (ofSinglePoint U) < ⊤ :=
    (hT 1 (ofSinglePoint U) hU).2 1 (by simp) hc
  have hsup : tupleSupNorm (ofSinglePoint U) ≤ cnNorm 1 (ofSinglePoint U) := by
    refine iSup_le fun y => ?_
    refine le_iSup_of_le (0 : PowerSeries.MultiIndex (4 * 1))
      (le_iSup_of_le (by simp [PowerSeries.MultiIndex.order]) ?_)
    rw [multiDeriv_zero]
    exact le_iSup (fun y => ENNReal.ofReal ‖ofSinglePoint U y‖) y
  have hpart : ∀ μ x, ‖partialAt μ U x‖ ≤ (cnNorm 1 (ofSinglePoint U)).toReal := by
    intro μ x
    have h1 : ENNReal.ofReal ‖partialAt μ U x‖ ≤ cnNorm 1 (ofSinglePoint U) :=
      le_iSup_of_le (basisMultiIndex μ) (le_iSup_of_le (by rw [basisMultiIndex_order])
        (le_iSup (fun y => ENNReal.ofReal ‖multiDeriv (basisMultiIndex μ) (ofSinglePoint U) y‖)
          (fun _ => x)))
    exact (ENNReal.ofReal_le_iff_le_toReal hN.ne).mp h1
  have hgrad : gradSupNorm U ≤
      ENNReal.ofReal (2 * (cnNorm 1 (ofSinglePoint U)).toReal) := by
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    refine (gradNorm_le_two_mul_iSup U x).trans ?_
    have := Real.iSup_le (fun μ => hpart μ x) ENNReal.toReal_nonneg
    linarith
  exact max_lt (hsup.trans_lt hN) (hgrad.trans_lt ENNReal.ofReal_lt_top)
theorem norm_sub_le_of_gradNorm_le (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    {U : Pt s E → ℂ} (hU : IsCnAtPoint 1 U) {K : ℝ}
    (hK : ∀ x, gradNorm U x ≤ K) (a b : Fin 4 → ℝ) :
    ‖U (proj s E a) - U (proj s E b)‖ ≤ K * euclidNormVec (a - b) := by
  have hG := (isCnAtPoint_one_iff_contDiff hC U).mp hU
  obtain ⟨v, hv⟩ : ∃ v, v = embedFour a - embedFour b := ⟨_, rfl⟩
  have hseg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => liftFun U (embedFour b + t • v))
      (fderiv ℝ (liftFun U) (embedFour b + t • v) v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => embedFour b + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add (embedFour b)
    exact ((hG.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t h1
  have hbound : ∀ t : ℝ, ‖fderiv ℝ (liftFun U) (embedFour b + t • v) v‖ ≤ K * euclidNormVec (a - b) := by
    intro t
    obtain ⟨z, hz⟩ : ∃ z, z = embedFour b + t • v := ⟨_, rfl⟩
    rw [← hz]
    have hexp : fderiv ℝ (liftFun U) z v = ∑ j, v j • partialDeriv j (liftFun U) z := by
      have hvs : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin (4 * 1) → ℝ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hvs]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, partialDeriv_eq_fderiv hG]
    have hlen : Real.sqrt (∑ j, ‖partialDeriv j (liftFun U) z‖ ^ 2) =
        gradNorm U (tupleProj s E 1 z 0) := by
      rw [sum_flatIndex]
      simp only [gradNorm, gradient]
      congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [partialAt_eq_partialDeriv_liftFun hT hU]
    have hvec : Real.sqrt (∑ j, |v j| ^ 2) = euclidNormVec (a - b) := by
      rw [sum_flatIndex]
      simp only [euclidNormVec]
      congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [sq_abs, hv, Pi.sub_apply, embedFour_flatIndex, embedFour_flatIndex, Pi.sub_apply]
    rw [hexp]
    calc ‖∑ j, v j • partialDeriv j (liftFun U) z‖
        ≤ ∑ j, ‖v j • partialDeriv j (liftFun U) z‖ := norm_sum_le _ _
      _ = ∑ j, |v j| * ‖partialDeriv j (liftFun U) z‖ := by
          simp
      _ ≤ Real.sqrt (∑ j, |v j| ^ 2) * Real.sqrt (∑ j, ‖partialDeriv j (liftFun U) z‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = gradNorm U (tupleProj s E 1 z 0) * euclidNormVec (a - b) := by
          rw [hlen, hvec, mul_comm]
      _ ≤ K * euclidNormVec (a - b) :=
          mul_le_mul_of_nonneg_right (hK _) (Real.sqrt_nonneg _)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => liftFun U (embedFour b + t • v))
    (f' := fun t : ℝ => fderiv ℝ (liftFun U) (embedFour b + t • v) v)
    (fun t _ => (hseg t).hasDerivWithinAt) (fun t _ => hbound t)
  have e1 : embedFour b + (1 : ℝ) • v = embedFour a := by
    rw [hv]
    simp
  have e0 : embedFour b + (0 : ℝ) • v = embedFour b := by simp
  simp only [e1, e0, liftFun_embedFour] at hmv
  exact hmv
theorem ambientSharpNorm_eq (M : Set.Ici (1 : ℝ)) (E : Ambient) (u : Pt s E → ℝ) :
    ambientSharpNorm s M E u =
      max (TestFunctions.uniformNorm u) (40 * (M : ℝ) * lipConst E u) := by
  cases E <;> rfl
theorem real_valued_bounds (hT : TupleDerivProps s E 1)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (hF : DistanceFacts.MetricFacts s E) (M : Set.Ici (1 : ℝ)) {u : Pt s E → ℝ}
    {U : Pt s E → ℂ} (hUu : ∀ x, U x = (u x : ℂ)) (hU : IsCnAtPoint 1 U)
    (hc : IsCompact (closedSupport (ofSinglePoint U))) :
    c1GradNorm U < ⊤ ∧ TestFunctions.IsLipschitzFor (pointDist s E) u ∧
      ENNReal.ofReal (lipConst E u) ≤ gradSupNorm U ∧
      ENNReal.ofReal (ambientSharpNorm s M E u) ≤ ENNReal.ofReal (40 * (M : ℝ)) * c1GradNorm U := by
  have hfin := c1GradNorm_lt_top hT hU hc
  have hS : gradSupNorm U < ⊤ := lt_of_le_of_lt (le_max_right _ _) hfin
  have hK : ∀ x, gradNorm U x ≤ (gradSupNorm U).toReal := fun x =>
    (ENNReal.ofReal_le_iff_le_toReal hS.ne).mp
      (le_iSup (fun x => ENNReal.ofReal (gradNorm U x)) x)
  have hK0 : 0 ≤ (gradSupNorm U).toReal := ENNReal.toReal_nonneg
  have hlip : ∀ y y', ‖u y - u y'‖ ≤ (gradSupNorm U).toReal * pointDist s E y y' := by
    intro y y'
    obtain ⟨b, hb, -⟩ := hF.exists_lift_pointDist 0 y'
    obtain ⟨a, ha, hab⟩ := hF.exists_lift_pointDist b y
    have hb' : proj s E b = y' := hb
    have ha' : proj s E a = y := ha
    have hm := norm_sub_le_of_gradNorm_le hT hC hU hK a b
    have hd : euclidNormVec (a - b) = pointDist s E y y' := by
      rw [euclidNormVec_sub_comm, hab, hb', pointDist_comm]
    rw [ha', hb', hd, hUu, hUu, ← Complex.ofReal_sub, Complex.norm_real] at hm
    exact hm
  have hLipN : lipConst E u ≤ (gradSupNorm U).toReal := by
    rw [lipConst_eq_bestLipschitzConstant]
    exact csInf_le ⟨0, fun C hC => hC.1⟩ ⟨hK0, hlip⟩
  refine ⟨hfin, ⟨_, hK0, hlip⟩, ?_, ?_⟩
  · calc ENNReal.ofReal (lipConst E u) ≤ ENNReal.ofReal (gradSupNorm U).toReal :=
          ENNReal.ofReal_le_ofReal hLipN
      _ = gradSupNorm U := ENNReal.ofReal_toReal hS.ne
  · have hC0 : 0 ≤ (c1GradNorm U).toReal := ENNReal.toReal_nonneg
    have hKC : (gradSupNorm U).toReal ≤ (c1GradNorm U).toReal :=
      ENNReal.toReal_mono hfin.ne (le_max_right _ _)
    have hA : ∀ x, ‖u x‖ ≤ (c1GradNorm U).toReal := by
      intro x
      have h1 : ENNReal.ofReal ‖U x‖ ≤ c1GradNorm U :=
        (le_iSup (fun x => ENNReal.ofReal ‖U x‖) x).trans
          ((tupleSupNorm_ofSinglePoint U).symm.le.trans (le_max_left _ _))
      have h2 := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp h1
      rwa [hUu, Complex.norm_real] at h2
    have hM : (1 : ℝ) ≤ (M : ℝ) := M.2
    have hsharp : ambientSharpNorm s M E u ≤ 40 * (M : ℝ) * (c1GradNorm U).toReal := by
      rw [ambientSharpNorm_eq]
      refine max_le ?_ ?_
      · refine (Real.iSup_le hA hC0).trans ?_
        nlinarith
      · exact mul_le_mul_of_nonneg_left (hLipN.trans hKC) (by positivity)
    calc ENNReal.ofReal (ambientSharpNorm s M E u)
        ≤ ENNReal.ofReal (40 * (M : ℝ) * (c1GradNorm U).toReal) :=
          ENNReal.ofReal_le_ofReal hsharp
      _ = ENNReal.ofReal (40 * (M : ℝ)) * ENNReal.ofReal (c1GradNorm U).toReal :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (40 * (M : ℝ)) * c1GradNorm U := by
          rw [ENNReal.ofReal_toReal hfin.ne]
theorem holds (hT : TupleTopology.Holds) (hL : DistanceFacts.MetricFactsClaim)
    (hC : PeriodicSpace.ContPartialsIffContDiff) :
    Statement := by
  intro s E
  have hD : TupleDerivProps s E 1 := ((hT s E).1 1 le_rfl).2.2.2.2
  refine ⟨fun g h hg hh => ⟨gradNorm_le_two_mul_iSup g, (partialAt_mul hD hC hg hh).1,
    gradNorm_mul_le hD hC hg hh, (partialAt_comp_clm hD hC reToComplex hg).1,
    (partialAt_comp_clm hD hC imToComplex hg).1,
    c1GradNorm_comp_clm_le hD hC reToComplex norm_reToComplex_le hg,
    c1GradNorm_comp_clm_le hD hC imToComplex norm_imToComplex_le hg⟩, ?_⟩
  intro M u hu hc
  exact real_valued_bounds hD hC (hL s E) M (fun _ => rfl) hu hc
end YangMills.Construction.AmbientPoints.GradientC1Bounds
