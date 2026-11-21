import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAHolonomyProof
import YangMills.Construction.ColdStepAtMirrorFrames.FitsAlongMovesProof
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.MovedBondsOfAChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open YangMills.Construction.BlockAverages NormedSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace TranslatedChartBounds
def leibnizMajorant (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i)
theorem leibnizMajorant_nonneg {a b : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    0 ≤ leibnizMajorant a b j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.leibnizConvolution_nonneg <;> assumption
theorem norm_iteratedFDeriv_mul_le_leibnizMajorant {k : ℕ} {u v : (Fin k → ℝ) → ℍ[ℝ]} {a b : ℕ → ℝ}
    (hu : ContDiff ℝ ω u) (hv : ContDiff ℝ ω v) (ha : ∀ j, ‖iteratedFDeriv ℝ j u 0‖ ≤ a j)
    (hb : ∀ j, ‖iteratedFDeriv ℝ j v 0‖ ≤ b j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun τ => u τ * v τ) 0‖ ≤ leibnizMajorant a b j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FitAlongTranslates.norm_iteratedFDeriv_mul_le_leibnizBound <;> assumption
def unitMajorant (j : ℕ) : ℝ := if j = 0 then 1 else 0
theorem unitMajorant_nonneg (j : ℕ) : 0 ≤ unitMajorant j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.constantBound_nonneg <;> assumption
theorem norm_iteratedFDeriv_const_le_unitMajorant {k : ℕ} {g : ℍ[ℝ]} (hg : ‖g‖ = 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : Fin k → ℝ => g) 0‖ ≤ unitMajorant j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HolonomyDerivatives.norm_iteratedFDeriv_const_le <;> assumption
theorem contDiff_quaternion_exp : ContDiff ℝ ω (exp : ℍ[ℝ] → ℍ[ℝ]) := by apply _root_.YangMills.SharedProofs.p23558 <;> assumption
theorem exists_bound_iteratedFDeriv_exp (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℍ[ℝ], ‖v‖ ≤ 1 → ‖iteratedFDeriv ℝ j (exp : ℍ[ℝ] → ℍ[ℝ]) v‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ j (exp : ℍ[ℝ] → ℍ[ℝ])) :=
    contDiff_quaternion_exp.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℍ[ℝ]) 1).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun v hv =>
    (hC v (by simpa using hv)).trans (le_max_left _ _)⟩
def expDerivBound (j : ℕ) : ℝ := (exists_bound_iteratedFDeriv_exp j).choose
theorem expDerivBound_nonneg (j : ℕ) : 0 ≤ expDerivBound j :=
  (exists_bound_iteratedFDeriv_exp j).choose_spec.1
theorem norm_iteratedFDeriv_exp_le (j : ℕ) {v : ℍ[ℝ]} (hv : ‖v‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (exp : ℍ[ℝ] → ℍ[ℝ]) v‖ ≤ expDerivBound j :=
  (exists_bound_iteratedFDeriv_exp j).choose_spec.2 v hv
def affineExpMajorant (k j : ℕ) : ℝ := expDerivBound j * (k : ℝ) ^ j
theorem affineExpMajorant_nonneg (k j : ℕ) : 0 ≤ affineExpMajorant k j :=
  mul_nonneg (expDerivBound_nonneg j) (by positivity)
theorem contDiff_exp_affine {k : ℕ} (A : (Fin k → ℝ) →L[ℝ] ℍ[ℝ]) (v : ℍ[ℝ]) :
    ContDiff ℝ ω (fun σ => exp (v + A σ)) :=
  contDiff_quaternion_exp.comp (contDiff_const.add A.contDiff)
theorem norm_iteratedFDeriv_exp_affine_le {k : ℕ} (A : (Fin k → ℝ) →L[ℝ] ℍ[ℝ]) (hA : ‖A‖ ≤ k)
    {v : ℍ[ℝ]} (hv : ‖v‖ ≤ 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun σ => exp (v + A σ)) 0‖ ≤ affineExpMajorant k j := by
  have hs : ContDiff ℝ ω (fun u : ℍ[ℝ] => exp (v + u)) :=
    contDiff_quaternion_exp.comp (contDiff_const.add contDiff_id)
  have h1 : iteratedFDeriv ℝ j ((fun u : ℍ[ℝ] => exp (v + u)) ∘ A) 0 =
      (iteratedFDeriv ℝ j (fun u : ℍ[ℝ] => exp (v + u)) (A 0)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right hs 0 le_top
  have h2 : (fun σ => exp (v + A σ)) = (fun u : ℍ[ℝ] => exp (v + u)) ∘ A := rfl
  rw [h2, h1, map_zero]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_comp_add_left j v (0 : ℍ[ℝ]) (f := (exp : ℍ[ℝ] → ℍ[ℝ])), add_zero]
  unfold affineExpMajorant
  refine mul_le_mul (norm_iteratedFDeriv_exp_le j hv) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (expDerivBound_nonneg j)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) hA j
variable {F : BlockFrame} {k : ℕ}
def paramLinear (ν : Fin k → imaginaryQuaternions) : (Fin k → ℝ) →L[ℝ] ℍ[ℝ] :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).smulRight (ν l : ℍ[ℝ])
theorem paramLinear_apply (ν : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    paramLinear ν σ = ((∑ l, σ l • ν l : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold paramLinear
  rw [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by simp
theorem norm_paramLinear_le (ν : Fin k → imaginaryQuaternions) (hν : ∀ l, ‖ν l‖ ≤ 1) :
    ‖paramLinear ν‖ ≤ k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg k) fun σ => ?_
  rw [paramLinear_apply]
  have h2 : ‖((∑ l, σ l • ν l : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(∑ l, σ l • ν l : imaginaryQuaternions)‖ := rfl
  rw [h2]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin k)), ‖σ l • ν l‖ ≤ ‖σ‖ := by
    intro l _
    rw [norm_smul]
    calc ‖σ l‖ * ‖ν l‖ ≤ ‖σ‖ * 1 :=
          mul_le_mul (norm_le_pi_norm σ l) (hν l) (norm_nonneg _) (norm_nonneg _)
      _ = ‖σ‖ := mul_one _
  simpa using Finset.sum_le_sum this
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem translatedTop_coe (V : F.GaugeField F.top) (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions)
    (σ : Fin k → ℝ) (y : F.Site F.top) (i : Fin 4) :
    ((translatedTop V μ σ y i : UnitQuaternion) : ℍ[ℝ]) =
      exp ((0 : ℍ[ℝ]) + paramLinear (fun l => μ l y i) σ) * (V y i : ℍ[ℝ]) := by
  rw [paramLinear_apply, zero_add]
  rfl
open Classical in
theorem translatedChart_coe (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (σ : Fin k → ℝ) (x : F.Site F.depth) (i : Fin 4) :
    ((translatedChart w V ξ μ σ x i : UnitQuaternion) : ℍ[ℝ]) =
      if IsCrossingBond (x, i) then
        exp ((w x i : ℍ[ℝ]) + paramLinear (fun l => ξ l x i) σ) *
          (exp ((0 : ℍ[ℝ]) + paramLinear (fun l => μ l (enclosingCell x) i) σ) *
            (V (enclosingCell x) i : ℍ[ℝ]))
      else if IsAxialTreeBond (x, i) then 1 else exp ((w x i : ℍ[ℝ]) + paramLinear (fun l => ξ l x i) σ) := by
  unfold translatedChart chartedField shiftedCoords
  split_ifs with h1 h2
  · rw [paramLinear_apply, ← translatedTop_coe]
    rfl
  · rfl
  · rw [paramLinear_apply]
    rfl
theorem sum_smul_congr_of_support (ν : Fin k → imaginaryQuaternions) {σ σ' : Fin k → ℝ}
    (h : ∀ l, ν l ≠ 0 → σ l = σ' l) :
    ∑ l, σ l • ν l = ∑ l, σ' l • ν l :=
  Finset.sum_congr rfl fun l _ => by
    by_cases hl : ν l = 0
    · simp [hl]
    · rw [h l hl]
end TranslatedChartBounds
open TranslatedChartBounds in
theorem translatedChartAnalytic_holds : TranslatedChartAnalytic := by
  classical
  refine ⟨fun k j => leibnizMajorant (affineExpMajorant k) (leibnizMajorant (affineExpMajorant k) unitMajorant) j +
    affineExpMajorant k j + unitMajorant j + leibnizMajorant (affineExpMajorant k) unitMajorant j,
    fun k j => ?_, ?_⟩
  · have := leibnizMajorant_nonneg (affineExpMajorant_nonneg k)
      (leibnizMajorant_nonneg (affineExpMajorant_nonneg k) unitMajorant_nonneg) j
    have := leibnizMajorant_nonneg (affineExpMajorant_nonneg k) unitMajorant_nonneg j
    have := affineExpMajorant_nonneg k j
    have := unitMajorant_nonneg j
    positivity
  intro F w V k ξ μ
  have hE : ∀ (ν : Fin k → imaginaryQuaternions) (v : ℍ[ℝ]), ContDiff ℝ ω (fun σ => exp (v + paramLinear ν σ)) :=
    fun ν v => contDiff_exp_affine _ _
  have hC : ∀ g : ℍ[ℝ], ContDiff ℝ ω (fun _ : Fin k → ℝ => g) := fun g => contDiff_const
  have hzero : ‖(0 : ℍ[ℝ])‖ ≤ 1 := by simp
  have hcT : ∀ (ν : Fin k → imaginaryQuaternions) (g : ℍ[ℝ]),
      ContDiff ℝ ω (fun σ : Fin k → ℝ => exp ((0 : ℍ[ℝ]) + paramLinear ν σ) * g) :=
    fun ν g => (hE _ _).mul (hC _)
  have bT : ∀ (ν : Fin k → imaginaryQuaternions) (g : UnitQuaternion), (∀ l, ‖ν l‖ ≤ 1) → ∀ j, ‖iteratedFDeriv ℝ j
      (fun σ : Fin k → ℝ => exp ((0 : ℍ[ℝ]) + paramLinear ν σ) * (g : ℍ[ℝ])) 0‖ ≤
        leibnizMajorant (affineExpMajorant k) unitMajorant j :=
    fun ν g h j => norm_iteratedFDeriv_mul_le_leibnizMajorant (hE _ _) (hC _)
      (norm_iteratedFDeriv_exp_affine_le _ (norm_paramLinear_le _ h) hzero)
      (norm_iteratedFDeriv_const_le_unitMajorant (_root_.YangMills.Construction.ColdStepAtMirrorFrames.TranslatedChartBounds.norm_coe_unitQuaternion _)) j
  refine ⟨fun y i => ?_, fun x i => ?_⟩
  · have htop : (fun σ : Fin k → ℝ => ((translatedTop V μ σ y i : UnitQuaternion) : ℍ[ℝ])) =
        fun σ => exp ((0 : ℍ[ℝ]) + paramLinear (fun l => μ l y i) σ) * (V y i : ℍ[ℝ]) :=
      funext fun σ => translatedTop_coe V μ σ _ i
    rw [htop]
    refine ⟨hcT _ _, fun h j => ?_⟩
    have e0 := affineExpMajorant_nonneg k j
    have c0 := unitMajorant_nonneg j
    have k1 := leibnizMajorant_nonneg (affineExpMajorant_nonneg k)
      (leibnizMajorant_nonneg (affineExpMajorant_nonneg k) unitMajorant_nonneg) j
    have := bT _ (V y i) h j
    linarith
  set ν₁ : Fin k → imaginaryQuaternions := fun l => ξ l x i with hν₁
  set ν₂ : Fin k → imaginaryQuaternions := fun l => μ l (enclosingCell x) i with hν₂
  have hv := fun σ => translatedChart_coe w V ξ μ σ x i
  have hfun : (fun σ : Fin k → ℝ => ((translatedChart w V ξ μ σ x i : UnitQuaternion) : ℍ[ℝ])) =
      if IsCrossingBond (x, i) then
        fun σ => exp ((w x i : ℍ[ℝ]) + paramLinear ν₁ σ) *
          (exp ((0 : ℍ[ℝ]) + paramLinear ν₂ σ) * (V (enclosingCell x) i : ℍ[ℝ]))
      else if IsAxialTreeBond (x, i) then fun _ => 1 else fun σ => exp ((w x i : ℍ[ℝ]) + paramLinear ν₁ σ) := by
    funext σ
    rw [hv σ]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    split_ifs
    · exact (hE _ _).mul (hcT _ _)
    · exact contDiff_const
    · exact hE _ _
  · intro hw h1 h2 j
    have hA : ‖paramLinear ν₁‖ ≤ k := norm_paramLinear_le _ h1
    have e0 := affineExpMajorant_nonneg k j
    have c0 := unitMajorant_nonneg j
    have k0 := leibnizMajorant_nonneg (affineExpMajorant_nonneg k) unitMajorant_nonneg j
    have k1 := leibnizMajorant_nonneg (affineExpMajorant_nonneg k)
      (leibnizMajorant_nonneg (affineExpMajorant_nonneg k) unitMajorant_nonneg) j
    rw [hfun]
    split_ifs with hc ht
    · have hw' : ‖(w x i : ℍ[ℝ])‖ ≤ 1 := by
        rcases hw with hw | ht
        · exact hw
        · exact absurd hc ht.1
      have := norm_iteratedFDeriv_mul_le_leibnizMajorant (hE ν₁ (w x i : ℍ[ℝ])) (hcT ν₂ _)
        (norm_iteratedFDeriv_exp_affine_le _ hA hw') (bT ν₂ (V (enclosingCell x) i) h2) j
      linarith
    · have := norm_iteratedFDeriv_const_le_unitMajorant (k := k) (g := (1 : ℍ[ℝ])) (by simp) j
      linarith
    · have hw' : ‖(w x i : ℍ[ℝ])‖ ≤ 1 := by
        rcases hw with hw | ht'
        · exact hw
        · exact absurd ht' ht
      have := norm_iteratedFDeriv_exp_affine_le _ hA hw' j
      linarith
  · intro σ σ' h
    have e1 : ∑ l, σ l • ν₁ l = ∑ l, σ' l • ν₁ l :=
      sum_smul_congr_of_support _ fun l hl => h l (Or.inl hl)
    apply Subtype.ext
    rw [hv σ, hv σ']
    by_cases hc : IsCrossingBond (x, i)
    · have e2 : ∑ l, σ l • ν₂ l = ∑ l, σ' l • ν₂ l :=
        sum_smul_congr_of_support _ fun l hl => h l (Or.inr ⟨hc, hl⟩)
      simp only [if_pos hc]
      rw [paramLinear_apply ν₁ σ, paramLinear_apply ν₁ σ', paramLinear_apply ν₂ σ, paramLinear_apply ν₂ σ', e1, e2]
    · simp only [if_neg hc]
      rw [paramLinear_apply ν₁ σ, paramLinear_apply ν₁ σ', e1]
end YangMills.Construction.ColdStepAtMirrorFrames
end
