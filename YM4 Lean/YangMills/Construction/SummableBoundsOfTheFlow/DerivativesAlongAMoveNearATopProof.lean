import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongAMoveNearATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Set Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FiniteDifferences
namespace ParameterBallBounds
open QuaternionLog GaugeMotions
section Calculus
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private theorem iteratedFDeriv_comp_affine {n : ℕ} {f : E → H} (A : G →ᴬ[ℝ] E) {x : G}
    (hf : ContDiffAt ℝ n f (A x)) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ A) x =
      (iteratedFDeriv ℝ i f (A x)).compContinuousLinearMap fun _ => A.contLinear := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U, hUu, hUo, hxU⟩ := mem_nhds_iff.1 hu
  have hcU : ContDiffOn ℝ n f U := hc.mono hUu
  have ht := (hcU.ftaylorSeriesWithin hUo.uniqueDiffOn).comp_continuousAffineMap A
  have hopen : IsOpen (A ⁻¹' U) := hUo.preimage A.continuous
  have h1 := ht.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hi) hopen.uniqueDiffOn
    (show x ∈ A ⁻¹' U from hxU)
  rw [iteratedFDerivWithin_of_isOpen i hopen (show x ∈ A ⁻¹' U from hxU)] at h1
  rw [← h1]
  simp only [ftaylorSeriesWithin]
  rw [iteratedFDerivWithin_of_isOpen i hUo hxU]
abbrev _root_.YangMills.SharedProofs.p8585 := @iteratedFDeriv_comp_affine
private def affineMapOf (L : G →L[ℝ] E) (a : E) : G →ᴬ[ℝ] E :=
  ⟨⟨fun z => L z + a, L.toLinearMap, fun p w => by simp [vadd_eq_add, add_assoc]⟩, by
    show Continuous fun z => L z + a
    fun_prop⟩
private theorem iteratedFDeriv_comp_add_apply {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by
  have h := iteratedFDeriv_comp_affine (affineMapOf L a) (x := x) hf hi
  have h2 := congrArg (fun T => T v) h
  exact h2
abbrev _root_.YangMills.SharedProofs.p13665 := @iteratedFDeriv_comp_add_apply
private theorem norm_iteratedFDeriv_comp_add_le {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1) (a : E)
    {x : G} (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (fun z => f (L z + a)) x‖ ≤ ‖iteratedFDeriv ℝ i f (L x + a)‖ := by
  have h := iteratedFDeriv_comp_affine (affineMapOf L a) (x := x) hf hi
  have e : (fun z => f (L z + a)) = f ∘ affineMapOf L a := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _j : Fin i, ‖(affineMapOf L a).contLinear‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ?_
    exact hL
  calc _ ≤ ‖iteratedFDeriv ℝ i f ((affineMapOf L a) x)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := by rw [mul_one]; rfl
private theorem norm_iteratedFDeriv_comp_le_at {n : ℕ} {f : E → G} {g : G → H} {x : E}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x)) {C D : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by
  obtain ⟨u, hu, hcf⟩ := hf.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨w, hw, hcg⟩ := hg.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨U₀, hU₀u, hU₀o, hxU₀⟩ := mem_nhds_iff.1 hu
  obtain ⟨W, hWw, hWo, hxW⟩ := mem_nhds_iff.1 hw
  have hcf' : ContDiffOn ℝ n f U₀ := hcf.mono hU₀u
  have hcg' : ContDiffOn ℝ n g W := hcg.mono hWw
  have hUo : IsOpen (U₀ ∩ f ⁻¹' W) := hcf'.continuousOn.isOpen_inter_preimage hU₀o hWo
  have hxU : x ∈ U₀ ∩ f ⁻¹' W := ⟨hxU₀, hxW⟩
  have hf' : ContDiffOn ℝ n f (U₀ ∩ f ⁻¹' W) := hcf'.mono inter_subset_left
  have h := norm_iteratedFDerivWithin_comp_le hcg' hf' (n := n) le_rfl hWo.uniqueDiffOn hUo.uniqueDiffOn
    (fun y hy => hy.2) hxU (C := C) (D := D)
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen i hWo hxW]; exact hC i hi)
    (fun i h1 hi => by rw [iteratedFDerivWithin_of_isOpen i hUo hxU]; exact hD i h1 hi)
  rwa [iteratedFDerivWithin_of_isOpen n hUo hxU] at h
abbrev _root_.YangMills.SharedProofs.p37475 := @norm_iteratedFDeriv_comp_le_at
private theorem norm_le_of_basis_values {q i : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin i => Fin q → ℝ) ℝ)
    {D : ℝ} (hD : 0 ≤ D) (h : ∀ σ : Fin i → Fin q, |M fun l => Pi.single (σ l) 1| ≤ D) :
    ‖M‖ ≤ (q : ℝ) ^ i * D := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun ξ => ?_
  have hξ : ξ = fun l => ∑ a, ξ l a • (Pi.single a 1 : Fin q → ℝ) := by
    funext l
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : M ξ = ∑ σ : Fin i → Fin q, (∏ l, ξ l (σ l)) * M fun l => Pi.single (σ l) 1 := by
    conv_lhs => rw [hξ]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    rfl
  rw [h1, Real.norm_eq_abs]
  calc |∑ σ : Fin i → Fin q, (∏ l, ξ l (σ l)) * M fun l => Pi.single (σ l) 1|
      ≤ ∑ σ : Fin i → Fin q, |(∏ l, ξ l (σ l)) * M fun l => Pi.single (σ l) 1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Fin i → Fin q, D * ∏ l, ‖ξ l‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul, Finset.abs_prod, mul_comm]
        refine mul_le_mul (h σ) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hD
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun l _ => norm_le_pi_norm (ξ l) (σ l)
    _ = (q : ℝ) ^ i * D * ∏ l, ‖ξ l‖ := by
        simp [Finset.card_univ, mul_assoc]
abbrev _root_.YangMills.SharedProofs.p82038 := @norm_le_of_basis_values
end Calculus
private def imagUnit (i : Fin 3) : imaginaryQuaternions :=
  ⟨⟨0, if i = 0 then 1 else 0, if i = 1 then 1 else 0, if i = 2 then 1 else 0⟩, rfl⟩
private theorem norm_imagUnit (i : Fin 3) : ‖imagUnit i‖ = 1 := by
  exact show ‖((imagUnit i : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 from by
    have h2 : ‖((imagUnit i : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 = 1 := by
      rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
      fin_cases i <;> simp [imagUnit]
    nlinarith [norm_nonneg ((imagUnit i : imaginaryQuaternions) : ℍ[ℝ])]
private def imagCoord (i : Fin 3) (w : imaginaryQuaternions) : ℝ :=
  if i = 0 then (w : ℍ[ℝ]).imI else if i = 1 then (w : ℍ[ℝ]).imJ else (w : ℍ[ℝ]).imK
private theorem sum_imagCoord_smul (w : imaginaryQuaternions) : ∑ i, imagCoord i w • imagUnit i = w := by
  apply Subtype.ext
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  rw [Fin.sum_univ_three]
  ext <;> simp [imagCoord, imagUnit, hw]
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = 0
    ring
  · show (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
private def imagCoordCLM (i : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ :=
  ⟨{ toFun := imagCoord i
     map_add' := fun a b => by
       simp only [imagCoord]
       split_ifs <;> rfl
     map_smul' := fun r a => by
       simp only [imagCoord, RingHom.id_apply]
       split_ifs <;> rfl }, by
    show Continuous (imagCoord i)
    unfold imagCoord
    split_ifs
    · exact Quaternion.continuous_imI.comp continuous_subtype_val
    · exact Quaternion.continuous_imJ.comp continuous_subtype_val
    · exact Quaternion.continuous_imK.comp continuous_subtype_val⟩
private theorem imagCoordCLM_apply (i : Fin 3) (w : imaginaryQuaternions) :
    imagCoordCLM i w = imagCoord i w := rfl
private def quaternionStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  ⟨{ toFun := star
     map_add' := star_add
     map_smul' := fun r a => Quaternion.star_smul r a }, continuous_star⟩
section Move
variable {F : BlockFrame} {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
private def listedBonds : Finset (F.Site j × Fin 4) := Finset.univ.image c
private abbrev BondCoord : Type := ↥(listedBonds c) × Fin 3
private def bondCoordCount : ℕ := Fintype.card (BondCoord c)
private def bondCoordEquiv : Fin (bondCoordCount c) ≃ BondCoord c := (Fintype.equivFin (BondCoord c)).symm
private def expandedBonds (a : Fin (bondCoordCount c)) : F.Site j × Fin 4 := (bondCoordEquiv c a).1.1
private def expandedUnits (a : Fin (bondCoordCount c)) : imaginaryQuaternions := imagUnit (bondCoordEquiv c a).2
private theorem expandedUnits_areUnitVectors : AreUnitVectors (expandedUnits c) := fun _ => norm_imagUnit _
private def expRatio (b : F.Site j × Fin 4) (p : (Fin k → ℝ) × (Fin k → ℝ)) : UnitQuaternion :=
  expUnit (bondSpread c X p.2 b.1 b.2) * (expUnit (bondSpread c X p.1 b.1 b.2))⁻¹
private def logRatioCoords (p : (Fin k → ℝ) × (Fin k → ℝ)) : Fin (bondCoordCount c) → ℝ :=
  fun a => imagCoord (bondCoordEquiv c a).2 (logUnit (expRatio c X (expandedBonds c a) p))
private theorem bondSpread_expanded (s : Fin (bondCoordCount c) → ℝ) (b : ↥(listedBonds c)) :
    bondSpread (expandedBonds c) (expandedUnits c) s b.1.1 b.1.2 =
      ∑ i, s ((bondCoordEquiv c).symm (b, i)) • imagUnit i := by
  set φ : BondCoord c → imaginaryQuaternions := fun p =>
    if p.1.1 = (b.1.1, b.1.2) then s ((bondCoordEquiv c).symm p) • imagUnit p.2 else 0 with hφ
  calc bondSpread (expandedBonds c) (expandedUnits c) s b.1.1 b.1.2
      = ∑ a, φ (bondCoordEquiv c a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp [hφ, expandedBonds, expandedUnits]
    _ = ∑ p, φ p := Equiv.sum_comp (bondCoordEquiv c) φ
    _ = ∑ β, ∑ i, φ (β, i) := Fintype.sum_prod_type _
    _ = ∑ i, φ (b, i) := by
        refine Finset.sum_eq_single b (fun β _ hβ => ?_) (by simp)
        refine Finset.sum_eq_zero fun i _ => ?_
        have : β.1 ≠ (b.1.1, b.1.2) := fun h => hβ (Subtype.ext h)
        exact if_neg this
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [hφ]
private theorem bondSpread_of_not_mem {y : F.Site j} {i : Fin 4} (h : (y, i) ∉ listedBonds c)
    (τ : Fin k → ℝ) : bondSpread c X τ y i = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  have : c l ≠ (y, i) := fun e => h (e ▸ Finset.mem_image_of_mem c (Finset.mem_univ l))
  simp [this]
private theorem bondSpread_expanded_of_not_mem {y : F.Site j} {i : Fin 4} (h : (y, i) ∉ listedBonds c)
    (s : Fin (bondCoordCount c) → ℝ) : bondSpread (expandedBonds c) (expandedUnits c) s y i = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : expandedBonds c a ≠ (y, i) := fun e => h (e ▸ (bondCoordEquiv c a).1.2)
  simp [this]
private theorem leftTranslate_logRatio (V : F.GaugeField j) {p : (Fin k → ℝ) × (Fin k → ℝ)}
    (h : ∀ b : ↥(listedBonds c), ‖((expRatio c X b.1 p : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius) :
    leftTranslate (bondSpread (expandedBonds c) (expandedUnits c) (logRatioCoords c X p))
        (leftTranslate (bondSpread c X p.1) V) =
      leftTranslate (bondSpread c X p.2) V := by
  funext y i
  by_cases hb : (y, i) ∈ listedBonds c
  · have e₁ : bondSpread (expandedBonds c) (expandedUnits c) (logRatioCoords c X p) y i =
        logUnit (expRatio c X (y, i) p) := by
      have := bondSpread_expanded c (logRatioCoords c X p) ⟨(y, i), hb⟩
      simp only at this
      rw [this]
      conv_rhs => rw [← sum_imagCoord_smul (logUnit (expRatio c X (y, i) p))]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [logRatioCoords, expandedBonds]
    simp only [leftTranslate]
    rw [e₁, expUnit_logUnit (h ⟨(y, i), hb⟩), expRatio]
    simp [mul_assoc]
  · simp only [leftTranslate]
    rw [bondSpread_expanded_of_not_mem c hb, bondSpread_of_not_mem c X hb, bondSpread_of_not_mem c X hb,
      expUnit_zero]
    simp
private theorem contDiff_bondSpread (y : F.Site j) (i : Fin 4) :
    ContDiff ℝ 3 fun τ : Fin k → ℝ => ((bondSpread c X τ y i : imaginaryQuaternions) : ℍ[ℝ]) := by
  have h : ContDiff ℝ 3 fun τ : Fin k → ℝ => bondSpread c X τ y i := by
    unfold ColdStepAtMirrorFrames.bondSpread
    refine ContDiff.sum fun l _ => ?_
    split_ifs
    · exact (contDiff_apply ℝ ℝ l).smul contDiff_const
    · exact contDiff_const
  exact imaginaryQuaternions.subtypeL.contDiff.comp h
private theorem bondSpread_zero (y : F.Site j) (i : Fin 4) : bondSpread c X 0 y i = 0 := by
  simp [ColdStepAtMirrorFrames.bondSpread]
private theorem coe_expRatio (b : F.Site j × Fin 4) (p : (Fin k → ℝ) × (Fin k → ℝ)) :
    ((expRatio c X b p : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp ((bondSpread c X p.2 b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) *
        star (NormedSpace.exp ((bondSpread c X p.1 b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])) := by
  rw [expRatio, Submonoid.coe_mul, coe_unitQuaternion_inv]
  rfl
private theorem contDiffAt_expRatio (b : F.Site j × Fin 4) :
    ContDiffAt ℝ 3 (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ((expRatio c X b p : UnitQuaternion) : ℍ[ℝ]))
      (0, 0) := by
  have h0 : ((bondSpread c X (0 : Fin k → ℝ) b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) = 0 := by
    rw [bondSpread_zero]
    rfl
  have e : ∀ g : (Fin k → ℝ) × (Fin k → ℝ) → Fin k → ℝ, ContDiff ℝ 3 g → g (0, 0) = 0 →
      ContDiffAt ℝ 3
        (fun p => NormedSpace.exp ((bondSpread c X (g p) b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ])) (0, 0) := by
    intro g hg hg0
    have h1 : ContDiffAt ℝ 3 (fun p => ((bondSpread c X (g p) b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))
        (0, 0) :=
      ((contDiff_bondSpread c X b.1 b.2).comp hg).contDiffAt
    have h2 : ContDiffAt ℝ 3 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ])
        ((bondSpread c X (g (0, 0)) b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
      rw [hg0, h0]
      exact contDiffAt_exp_zero
    exact ContDiffAt.comp (0, 0) h2 h1
  have h₁ := e Prod.snd contDiff_snd rfl
  have h₂ := e Prod.fst contDiff_fst rfl
  have h₃ : ContDiffAt ℝ 3
      (fun p : (Fin k → ℝ) × (Fin k → ℝ) => star (NormedSpace.exp
        ((bondSpread c X p.1 b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]))) (0, 0) :=
    quaternionStarCLM.contDiff.contDiffAt.comp (0, 0) h₂
  have h₄ := h₁.mul h₃
  refine h₄.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  exact coe_expRatio c X b p
private theorem expRatio_zero (b : F.Site j × Fin 4) :
    ((expRatio c X b (0, 0) : UnitQuaternion) : ℍ[ℝ]) = 1 := by
  simp [expRatio, bondSpread_zero, expUnit_zero]
private theorem contDiffAt_logRatioCoords : ContDiffAt ℝ 3 (logRatioCoords c X) (0, 0) := by
  refine contDiffAt_pi.2 fun a => ?_
  have h1 : ContDiffAt ℝ 3 qlog ((expRatio c X (expandedBonds c a) (0, 0) : UnitQuaternion) : ℍ[ℝ]) := by
    rw [expRatio_zero]
    exact contDiffAt_qlog_one
  have h2 := ContDiffAt.comp (0, 0) h1 (contDiffAt_expRatio c X (expandedBonds c a))
  have h3 := ((imagCoordCLM (bondCoordEquiv c a).2).comp pureComponentCLM).contDiff.contDiffAt.comp (0, 0) h2
  exact h3
private theorem logRatioCoords_diag (τ : Fin k → ℝ) : logRatioCoords c X (τ, τ) = 0 := by
  funext a
  have h : expRatio c X (expandedBonds c a) (τ, τ) = 1 := by simp [expRatio]
  have h2 : logUnit (1 : UnitQuaternion) = 0 := by
    rw [logUnit]
    have : ((1 : UnitQuaternion) : ℍ[ℝ]) = 1 := rfl
    rw [this, qlog_one, map_zero]
  simp only [logRatioCoords, h, h2, Pi.zero_apply]
  rw [← imagCoordCLM_apply, map_zero]
private theorem bondSpread_sum_single {q i : ℕ} (c₂ : Fin q → F.Site j × Fin 4) (X₂ : Fin q → imaginaryQuaternions)
    (σ : Fin i → Fin q) (t : Fin i → ℝ) :
    bondSpread c₂ X₂ (∑ l, t l • (Pi.single (σ l) (1 : ℝ) : Fin q → ℝ)) =
      bondSpread (c₂ ∘ σ) (X₂ ∘ σ) t := by
  funext y i'
  have h : ∀ a, (∑ l, t l • (Pi.single (σ l) (1 : ℝ) : Fin q → ℝ)) a =
      ∑ l, if a = σ l then t l else 0 := by
    intro a
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [ColdStepAtMirrorFrames.bondSpread, h]
  calc ∑ a, (if c₂ a = (y, i') then (∑ l, if a = σ l then t l else 0) • X₂ a else 0)
      = ∑ a, ∑ l, if a = σ l then (if c₂ a = (y, i') then t l • X₂ a else 0) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hc : c₂ a = (y, i')
        · simp only [hc, if_true, Finset.sum_smul]
          refine Finset.sum_congr rfl fun l _ => ?_
          split_ifs <;> simp
        · simp [hc]
    _ = ∑ l, ∑ a, if a = σ l then (if c₂ a = (y, i') then t l • X₂ a else 0) else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp
private theorem iteratedFDeriv_basis_eq_bondDeriv {q i : ℕ} (c₂ : Fin q → F.Site j × Fin 4)
    (X₂ : Fin q → imaginaryQuaternions) (σ : Fin i → Fin q)
    (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (hi : i ≤ 3)
    (h : ContDiffAt ℝ 3 (fun s : Fin q → ℝ => G (leftTranslate (bondSpread c₂ X₂ s) W)) 0) :
    iteratedFDeriv ℝ i (fun s : Fin q → ℝ => G (leftTranslate (bondSpread c₂ X₂ s) W)) 0
        (fun l => Pi.single (σ l) 1) = bondDeriv G W (c₂ ∘ σ) (X₂ ∘ σ) := by
  set L : (Fin i → ℝ) →L[ℝ] Fin q → ℝ :=
    ∑ l, (ContinuousLinearMap.proj l : (Fin i → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (σ l) (1 : ℝ)) with hL
  have hLa : ∀ t, L t = ∑ l, t l • (Pi.single (σ l) (1 : ℝ) : Fin q → ℝ) := by
    intro t
    simp [hL]
  have hs : ∀ l, L (Pi.single l 1) = Pi.single (σ l) 1 := by
    intro l
    rw [hLa]
    simp [Pi.single_apply]
  have h3 : ContDiffAt ℝ (3 : ℕ) (fun s : Fin q → ℝ => G (leftTranslate (bondSpread c₂ X₂ s) W))
      (L 0 + 0) := by
    simpa using h
  have h1 := iteratedFDeriv_comp_add_apply L 0 (x := (0 : Fin i → ℝ)) h3 hi (fun l => Pi.single l 1)
  have e₀ : L 0 + 0 = 0 := by simp
  rw [e₀] at h1
  simp only [hs] at h1
  have e : (fun z => G (leftTranslate (bondSpread c₂ X₂ (L z + 0)) W)) =
      fun τ => G (leftTranslate (bondSpread (c₂ ∘ σ) (X₂ ∘ σ) τ) W) := by
    funext t
    rw [add_zero, hLa, bondSpread_sum_single]
  rw [← h1, bondDeriv, e]
end Move
private theorem isOpen_setOf_contDiffAt {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (f : P → Q) : IsOpen {z | ContDiffAt ℝ 3 f z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact (show ContDiffAt ℝ 3 f z from hz).eventually (by simp)
end ParameterBallBounds
open ParameterBallBounds QuaternionLog GaugeMotions in
theorem Estimates.contDiffBoundOnParameterBall_holds : Estimates.ContDiffBoundOnParameterBall := by
  intro F j k c X
  set Ψ := logRatioCoords c X with hΨ
  set U : Set ((Fin k → ℝ) × (Fin k → ℝ)) := {z | ContDiffAt ℝ 3 Ψ z} with hU
  have hUo : IsOpen U := isOpen_setOf_contDiffAt Ψ
  have hΨU : ContDiffOn ℝ 3 Ψ U := fun z hz => (show ContDiffAt ℝ 3 Ψ z from hz).contDiffWithinAt
  have hr₀ : 0 < rightRadius := qlogRadii_spec.right_pos
  have hnear : ∀ᶠ p : (Fin k → ℝ) × (Fin k → ℝ) in 𝓝 (0, 0), p ∈ U ∧
      ∀ b : ↥(listedBonds c), ‖((expRatio c X b.1 p : UnitQuaternion) : ℍ[ℝ]) - 1‖ < rightRadius := by
    have hU0 : ∀ᶠ p : (Fin k → ℝ) × (Fin k → ℝ) in 𝓝 (0, 0), p ∈ U :=
      hUo.mem_nhds (contDiffAt_logRatioCoords c X)
    refine hU0.and ?_
    refine eventually_all.2 fun b => ?_
    have h1 : Tendsto (fun p : (Fin k → ℝ) × (Fin k → ℝ) => ((expRatio c X b.1 p : UnitQuaternion) : ℍ[ℝ]) - 1)
        (𝓝 (0, 0)) (𝓝 0) := by
      have := ((contDiffAt_expRatio c X b.1).continuousAt.tendsto).sub_const 1
      rwa [expRatio_zero, sub_self] at this
    have := h1.norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds hr₀)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hin : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), p.1 ∈ Metric.closedBall (0 : Fin k → ℝ) r →
      p.2 ∈ Metric.closedBall (0 : Fin k → ℝ) r → p ∈ Metric.ball ((0 : Fin k → ℝ), (0 : Fin k → ℝ)) ε := by
    intro p h1 h2
    rw [Metric.mem_ball, Prod.dist_eq]
    rw [Metric.mem_closedBall] at h1 h2
    have : max (dist p.1 (0 : Fin k → ℝ)) (dist p.2 (0 : Fin k → ℝ)) ≤ r := max_le h1 h2
    show max (dist p.1 (0 : Fin k → ℝ)) (dist p.2 (0 : Fin k → ℝ)) < ε
    linarith
  have hK : IsCompact ((Metric.closedBall (0 : Fin k → ℝ) r) ×ˢ (Metric.closedBall (0 : Fin k → ℝ) r)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKU : (Metric.closedBall (0 : Fin k → ℝ) r) ×ˢ (Metric.closedBall (0 : Fin k → ℝ) r) ⊆ U :=
    fun p hp => (hball p (hin p hp.1 hp.2)).1
  have hbd : ∀ i : ℕ, i ≤ 3 → ∃ M : ℝ, ∀ p ∈ (Metric.closedBall (0 : Fin k → ℝ) r) ×ˢ
      (Metric.closedBall (0 : Fin k → ℝ) r), ‖iteratedFDeriv ℝ i Ψ p‖ ≤ M := by
    intro i hi
    have hc : ContinuousOn (iteratedFDeriv ℝ i Ψ) U :=
      (hΨU.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast hi)
        hUo.uniqueDiffOn).congr (fun z hz => (iteratedFDerivWithin_of_isOpen i hUo hz).symm)
    exact hK.exists_bound_of_continuousOn (hc.mono hKU)
  choose! M hM using hbd
  set D₀ : ℝ := 1 + |M 1| + |M 2| + |M 3| with hD₀
  have hD₀1 : 1 ≤ D₀ := by
    have := abs_nonneg (M 1)
    have := abs_nonneg (M 2)
    have := abs_nonneg (M 3)
    linarith
  refine ⟨r, 6 * (((bondCoordCount c : ℝ) + 1) ^ 3 * D₀ ^ 3), hrpos, by positivity,
    fun r' hr' hle V G D hD hs hb => ?_⟩
  set φ : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) V) with hφ
  have hsub : ∀ τ, τ ∈ Metric.ball (0 : Fin k → ℝ) r' → τ ∈ Metric.closedBall (0 : Fin k → ℝ) r :=
    fun τ h => Metric.closedBall_subset_closedBall hle (Metric.ball_subset_closedBall h)
  have key : ∀ τ₀ ∈ Metric.ball (0 : Fin k → ℝ) r',
      ContDiffAt ℝ 3 φ τ₀ ∧ ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i φ τ₀‖ ≤
        6 * (((bondCoordCount c : ℝ) + 1) ^ 3 * D₀ ^ 3) * D := by
    intro τ₀ hτ₀
    set W : F.GaugeField j := leftTranslate (bondSpread c X τ₀) V with hW
    set h : (Fin (bondCoordCount c) → ℝ) → ℝ :=
      fun s => G (leftTranslate (bondSpread (expandedBonds c) (expandedUnits c) s) W) with hh
    set f : (Fin k → ℝ) → Fin (bondCoordCount c) → ℝ := fun τ => Ψ (τ₀, τ) with hf
    have hf0 : f τ₀ = 0 := logRatioCoords_diag c X τ₀
    have hP : (τ₀, τ₀) ∈ U := hKU ⟨hsub _ hτ₀, hsub _ hτ₀⟩
    have hfs : ContDiffAt ℝ 3 f τ₀ := by
      have h2 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => (τ₀, τ)) τ₀ := by fun_prop
      exact ContDiffAt.comp τ₀ (show ContDiffAt ℝ 3 Ψ (τ₀, τ₀) from hP) h2
    have hhs : ContDiffAt ℝ 3 h (f τ₀) := by
      rw [hf0]
      exact hs τ₀ hτ₀ (bondCoordCount c) (expandedBonds c) (expandedUnits c) (expandedUnits_areUnitVectors c)
    have hgerm : φ =ᶠ[𝓝 τ₀] h ∘ f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hτ₀] with τ hτ
      have := leftTranslate_logRatio c X V (p := (τ₀, τ)) (hball _ (hin _ (hsub _ hτ₀) (hsub _ hτ))).2
      simp only [hφ, hh, hf, Function.comp, hΨ]
      rw [this]
    refine ⟨(ContDiffAt.comp τ₀ hhs hfs).congr_of_eventuallyEq hgerm, fun i hi => ?_⟩
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hgerm i).eq_of_nhds]
    have hC : ∀ i', i' ≤ i → ‖iteratedFDeriv ℝ i' h (f τ₀)‖ ≤ ((bondCoordCount c : ℝ) + 1) ^ 3 * D := by
      intro i' hi'
      rw [hf0]
      have h1 : ‖iteratedFDeriv ℝ i' h 0‖ ≤ (bondCoordCount c : ℝ) ^ i' * D := by
        refine norm_le_of_basis_values _ hD fun σ => ?_
        rw [iteratedFDeriv_basis_eq_bondDeriv _ _ σ G W (by omega)
          (hs τ₀ hτ₀ (bondCoordCount c) (expandedBonds c) (expandedUnits c) (expandedUnits_areUnitVectors c))]
        exact hb τ₀ hτ₀ i' _ _ (by omega) fun l => norm_imagUnit _
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hD)
      calc (bondCoordCount c : ℝ) ^ i' ≤ ((bondCoordCount c : ℝ) + 1) ^ i' := by gcongr; linarith
        _ ≤ ((bondCoordCount c : ℝ) + 1) ^ 3 :=
          pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (bondCoordCount c)]) (by omega)
    have hDi : ∀ i', 1 ≤ i' → i' ≤ i → ‖iteratedFDeriv ℝ i' f τ₀‖ ≤ D₀ ^ i' := by
      intro i' h1 hi'
      have hL : ‖(ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ))‖ ≤ 1 :=
        ContinuousLinearMap.norm_inr_le_one ℝ _ _
      have e : (fun τ => f τ) =
          fun z => Ψ ((ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ)) z + (τ₀, 0)) := by
        funext z
        simp [hf]
      have hpt : (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ)) τ₀ + (τ₀, 0) = (τ₀, τ₀) := by simp
      have h2 := norm_iteratedFDeriv_comp_add_le (n := 3) (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ))
        hL (τ₀, 0) (x := τ₀) (f := Ψ) (by rw [hpt]; exact_mod_cast hP) (i := i') (by omega)
      rw [← e, hpt] at h2
      have h3 := hM i' (by omega) (τ₀, τ₀) ⟨hsub _ hτ₀, hsub _ hτ₀⟩
      have h4 : M i' ≤ D₀ := by
        have a1 := abs_nonneg (M 1)
        have a2 := abs_nonneg (M 2)
        have a3 := abs_nonneg (M 3)
        have : i' = 1 ∨ i' = 2 ∨ i' = 3 := by omega
        rcases this with rfl | rfl | rfl
        · linarith [le_abs_self (M 1)]
        · linarith [le_abs_self (M 2)]
        · linarith [le_abs_self (M 3)]
      calc _ ≤ M i' := h2.trans h3
        _ ≤ D₀ := h4
        _ = D₀ ^ 1 := (pow_one _).symm
        _ ≤ D₀ ^ i' := pow_le_pow_right₀ hD₀1 h1
    have hcb := norm_iteratedFDeriv_comp_le_at (n := i) (hfs.of_le (by exact_mod_cast hi))
      (hhs.of_le (by exact_mod_cast hi)) hC hDi
    refine hcb.trans ?_
    have hfac : ((i.factorial : ℕ) : ℝ) ≤ 6 := by
      have : i.factorial ≤ Nat.factorial 3 := Nat.factorial_le hi
      have h6 : Nat.factorial 3 = 6 := rfl
      rw [h6] at this
      exact_mod_cast this
    have hpow : D₀ ^ i ≤ D₀ ^ 3 := pow_le_pow_right₀ hD₀1 hi
    calc ((i.factorial : ℕ) : ℝ) * (((bondCoordCount c : ℝ) + 1) ^ 3 * D) * D₀ ^ i
        ≤ 6 * (((bondCoordCount c : ℝ) + 1) ^ 3 * D) * D₀ ^ 3 := by gcongr
      _ = _ := by ring
  exact ⟨fun τ hτ => (key τ hτ).1.contDiffWithinAt, fun τ hτ i hi => (key τ hτ).2 i hi⟩
end YangMills.Construction
end
