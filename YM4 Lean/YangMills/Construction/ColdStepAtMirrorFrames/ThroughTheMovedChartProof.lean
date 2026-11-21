import YangMills.Construction.ClusterExpansionOfAStep.PlainFitsAlongMoves
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmNearOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.ThroughTheMovedChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Calculus NormedSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace TranslatedChart
instance : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
def imBasis : Fin 3 → imaginaryQuaternions :=
  ![⟨⟨0, 1, 0, 0⟩, rfl⟩, ⟨⟨0, 0, 1, 0⟩, rfl⟩, ⟨⟨0, 0, 0, 1⟩, rfl⟩]
def quatImCoord (d : Fin 3) (q : ℍ[ℝ]) : ℝ := ![q.imI, q.imJ, q.imK] d
def imCoordLinear (d : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun v := quatImCoord d (v : ℍ[ℝ])
  map_add' a b := by fin_cases d <;> simp [quatImCoord]
  map_smul' c a := by fin_cases d <;> simp [quatImCoord]
def imCoord (d : Fin 3) : imaginaryQuaternions →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (imCoordLinear d)
theorem imCoord_apply (d : Fin 3) (v : imaginaryQuaternions) : imCoord d v = quatImCoord d (v : ℍ[ℝ]) := rfl
theorem sum_imCoord_smul_imBasis (v : imaginaryQuaternions) : ∑ d, imCoord d v • imBasis d = v := by
  apply Subtype.ext
  have h : (v : ℍ[ℝ]).re = 0 := v.2
  rw [Fin.sum_univ_three, Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    Submodule.coe_smul]
  simp only [imCoord_apply, quatImCoord, imBasis]
  ext
  · show (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 0 = (v : ℍ[ℝ]).re
    simp [h]
  · show (v : ℍ[ℝ]).imI * 1 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 0 = (v : ℍ[ℝ]).imI
    simp
  · show (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 1 + (v : ℍ[ℝ]).imK * 0 = (v : ℍ[ℝ]).imJ
    simp
  · show (v : ℍ[ℝ]).imI * 0 + (v : ℍ[ℝ]).imJ * 0 + (v : ℍ[ℝ]).imK * 1 = (v : ℍ[ℝ]).imK
    simp
theorem norm_imBasis (d : Fin 3) : ‖imBasis d‖ = 1 := by
  have h : ‖((imBasis d : imaginaryQuaternions) : ℍ[ℝ])‖ * ‖((imBasis d : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    fin_cases d <;> simp [imBasis]
  have h2 : ‖imBasis d‖ = ‖((imBasis d : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
  rw [h2]
  nlinarith [norm_nonneg ((imBasis d : imaginaryQuaternions) : ℍ[ℝ])]
theorem norm_piSingle_one_le {k : ℕ} (l : Fin k) : ‖(Pi.single l (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.PlainAlignment.norm_single_le_one <;> assumption
theorem expUnit_at_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {F : BlockFrame} {k : ℕ}
theorem translatedChart_at_zero (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) : translatedChart w V ξ μ 0 = chartedField w V := by
  have e1 : shiftedCoords w ξ 0 = w := by
    funext x i
    simp [shiftedCoords]
  have e2 : translatedTop V μ 0 = V := by
    funext y i
    simp [translatedTop, leftTranslate, expUnit_at_zero]
  unfold translatedChart
  rw [e1, e2]
def bondQuat (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4) (σ : Fin k → ℝ) : ℍ[ℝ] :=
  ((translatedChart w V ξ μ σ b.1 b.2 : UnitQuaternion) : ℍ[ℝ])
def rightMulImCLM (c : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  imPartCLM.comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip c)
theorem rightMulImCLM_apply (c q : ℍ[ℝ]) : rightMulImCLM c q = imPartCLM (q * c) := rfl
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_rightMulImCLM_le {c : ℍ[ℝ]} (hc : ‖c‖ = 1) : ‖rightMulImCLM c‖ ≤ ‖imPartCLM‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun q => ?_
  rw [rightMulImCLM_apply]
  refine (imPartCLM.le_opNorm _).trans ?_
  rw [norm_mul, hc, mul_one]
def relBondIm (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4) (σ : Fin k → ℝ) :
    imaginaryQuaternions :=
  rightMulImCLM (star (bondQuat w V ξ μ b 0)) (bondQuat w V ξ μ b σ)
theorem imPartCLM_one : imPartCLM (1 : ℍ[ℝ]) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AnalyticLog.imPartCLM_one <;> assumption
theorem bondQuat_zero_mul_star (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4) :
    bondQuat w V ξ μ b 0 * star (bondQuat w V ξ μ b 0) = 1 :=
  Unitary.mul_star_self_of_mem (translatedChart w V ξ μ 0 b.1 b.2).2
theorem relBondIm_zero (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4) :
    relBondIm w V ξ μ b 0 = 0 := by
  unfold relBondIm
  rw [rightMulImCLM_apply, bondQuat_zero_mul_star, imPartCLM_one]
abbrev bondDirPairs (B : Finset (F.Site F.depth × Fin 4)) : Finset ((F.Site F.depth × Fin 4) × Fin 3) :=
  B ×ˢ (Finset.univ : Finset (Fin 3))
def bondDirPair (B : Finset (F.Site F.depth × Fin 4)) (r : Fin (bondDirPairs B).card) :
    (F.Site F.depth × Fin 4) × Fin 3 :=
  (((bondDirPairs B).equivFin.symm r : ↥(bondDirPairs B)) : (F.Site F.depth × Fin 4) × Fin 3)
theorem bondSpread_bondDirPairs (B : Finset (F.Site F.depth × Fin 4)) (θ : F.Site F.depth × Fin 4 → imaginaryQuaternions)
    (y : F.Site F.depth) (i : Fin 4) :
    bondSpread (fun r => (bondDirPair B r).1) (fun r => imBasis (bondDirPair B r).2)
      (fun r => imCoord (bondDirPair B r).2 (θ (bondDirPair B r).1)) y i =
      if (y, i) ∈ B then θ (y, i) else 0 := by
  classical
  unfold bondSpread
  have h1 := Equiv.sum_comp (bondDirPairs B).equivFin.symm (fun a : ↥(bondDirPairs B) =>
    if a.1.1 = (y, i) then imCoord a.1.2 (θ a.1.1) • imBasis a.1.2 else (0 : imaginaryQuaternions))
  have h2 : ∑ r : Fin (bondDirPairs B).card, (if (bondDirPair B r).1 = (y, i) then
      imCoord (bondDirPair B r).2 (θ (bondDirPair B r).1) • imBasis (bondDirPair B r).2
        else (0 : imaginaryQuaternions)) =
      ∑ a : ↥(bondDirPairs B), if a.1.1 = (y, i) then imCoord a.1.2 (θ a.1.1) • imBasis a.1.2
        else (0 : imaginaryQuaternions) := h1
  rw [h2, Finset.sum_coe_sort (bondDirPairs B) (fun a =>
    if a.1 = (y, i) then imCoord a.2 (θ a.1) • imBasis a.2 else (0 : imaginaryQuaternions)), Finset.sum_product]
  split_ifs with hb
  · rw [Finset.sum_eq_single (y, i)]
    · simp only [if_true, sum_imCoord_smul_imBasis]
    · intro b _ hne
      simp [hne]
    · intro hn
      exact absurd hb hn
  · refine Finset.sum_eq_zero fun b hbB => ?_
    have hne : b ≠ (y, i) := fun e => hb (e ▸ hbB)
    simp [hne]
theorem bondSpread_comp_index {n p : ℕ} (bd : Fin n → F.Site F.depth × Fin 4) (X : Fin n → imaginaryQuaternions)
    (r : Fin p → Fin n) (τ : Fin p → ℝ) :
    bondSpread (fun m => bd (r m)) (fun m => X (r m)) τ =
      bondSpread bd X (fun q => ∑ m, τ m * (Pi.single (r m) (1 : ℝ) : Fin n → ℝ) q) := by
  classical
  funext y i
  unfold bondSpread
  have e : ∀ q : Fin n, (if bd q = (y, i) then (∑ m, τ m * (Pi.single (r m) (1 : ℝ) : Fin n → ℝ) q) • X q else 0) =
      ∑ m, if r m = q then (if bd (r m) = (y, i) then τ m • X (r m) else 0) else 0 := by
    intro q
    split_ifs with hq
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : r m = q
      · subst hm
        simp [hq]
      · simp [hm, Pi.single_apply, Ne.symm hm, fun h : q = r m => hm h.symm]
    · symm
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : r m = q
      · subst hm
        simp [hq]
      · simp [hm]
  rw [Finset.sum_congr rfl fun q _ => e q, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp
def indexSumCLM {n p : ℕ} (r : Fin p → Fin n) : (Fin p → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑ m, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) m).smulRight (Pi.single (r m) (1 : ℝ))
theorem indexSumCLM_apply {n p : ℕ} (r : Fin p → Fin n) (τ : Fin p → ℝ) (q : Fin n) :
    indexSumCLM r τ q = ∑ m, τ m * (Pi.single (r m) (1 : ℝ) : Fin n → ℝ) q := by
  unfold indexSumCLM
  rw [ContinuousLinearMap.sum_apply, Finset.sum_apply]
  simp
theorem indexSumCLM_single {n p : ℕ} (r : Fin p → Fin n) (m : Fin p) :
    indexSumCLM r (Pi.single m 1) = Pi.single (r m) 1 := by
  classical
  funext q
  rw [indexSumCLM_apply, Finset.sum_eq_single m]
  · simp
  · intro m' _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp
theorem compositeCoordBound_le_of_le {k n n' : ℕ} {D N : ℝ} (hD : 0 ≤ D) (hN : 0 ≤ N) (h : n ≤ n') :
    compositeCoordBound k n D N ≤ compositeCoordBound k n' D 1 * N := by
  unfold compositeCoordBound
  have h1 : ((n : ℝ) + 1) ^ k ≤ ((n' : ℝ) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1) _
  calc (Fintype.card (OrderedFinpartition k) : ℝ) * ((n : ℝ) + 1) ^ k * (D + 1) ^ k * N
      ≤ (Fintype.card (OrderedFinpartition k) : ℝ) * ((n' : ℝ) + 1) ^ k * (D + 1) ^ k * N := by
        gcongr
    _ = _ := by ring
theorem relBondIm_contDiff (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (hu : ContDiff ℝ ω (bondQuat w V ξ μ b)) :
    ContDiff ℝ ω (relBondIm w V ξ μ b) :=
  (rightMulImCLM (star (bondQuat w V ξ μ b 0))).contDiff.comp hu
theorem norm_iteratedFDeriv_relBondIm_le (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (hu : ContDiff ℝ ω (bondQuat w V ξ μ b)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (relBondIm w V ξ μ b) 0‖ ≤ ‖imPartCLM‖ * ‖iteratedFDeriv ℝ j (bondQuat w V ξ μ b) 0‖ := by
  have hc : ‖star (bondQuat w V ξ μ b 0)‖ = 1 := by
    rw [norm_star]
    exact norm_unitQuaternion _
  have h1 := (rightMulImCLM (star (bondQuat w V ξ μ b 0))).iteratedFDeriv_comp_left (f := bondQuat w V ξ μ b)
    (x := 0) (n := ω) hu.contDiffAt (i := j) le_top
  have h2 : relBondIm w V ξ μ b = (rightMulImCLM (star (bondQuat w V ξ μ b 0))) ∘ bondQuat w V ξ μ b := rfl
  rw [h2, h1]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_rightMulImCLM_le hc) (norm_nonneg _)
theorem eventually_expUnit_relBondIm_mul (Ψ : imaginaryQuaternions → imaginaryQuaternions) {ε : ℝ} (hε : 0 < ε)
    (hΨ : ∀ g : UnitQuaternion, ‖(g : ℍ[ℝ]) - 1‖ < ε → expUnit (Ψ (imPartCLM (g : ℍ[ℝ]))) = g)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (ξ : Fin k → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (μ : Fin k → F.Site F.top → Fin 4 → imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (hu : ContDiff ℝ ω (bondQuat w V ξ μ b)) :
    ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ),
      expUnit (Ψ (relBondIm w V ξ μ b σ)) * chartedField w V b.1 b.2 = translatedChart w V ξ μ σ b.1 b.2 := by
  have hcont : ContinuousAt (fun σ : Fin k → ℝ => ‖bondQuat w V ξ μ b σ * star (bondQuat w V ξ μ b 0) - 1‖) 0 :=
    (((hu.continuous.mul continuous_const).sub continuous_const).norm).continuousAt
  have h0 : ‖bondQuat w V ξ μ b 0 * star (bondQuat w V ξ μ b 0) - 1‖ < ε := by
    rw [bondQuat_zero_mul_star]
    simpa using hε
  filter_upwards [hcont.eventually (gt_mem_nhds h0)] with σ hσ
  set g : UnitQuaternion := translatedChart w V ξ μ σ b.1 b.2 * (chartedField w V b.1 b.2)⁻¹ with hg
  have hgc : (g : ℍ[ℝ]) = bondQuat w V ξ μ b σ * star (bondQuat w V ξ μ b 0) := by
    have e0 : bondQuat w V ξ μ b 0 = ((chartedField w V b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) := by
      unfold bondQuat
      rw [translatedChart_at_zero]
    rw [e0]
    rfl
  have h1 := hΨ g (by rw [hgc]; exact hσ)
  have e1 : relBondIm w V ξ μ b σ = imPartCLM (g : ℍ[ℝ]) := by
    rw [hgc]
    rfl
  rw [e1, h1, hg]
  group
end TranslatedChart
open TranslatedChart in
theorem TranslatedChart.compositeBound_holds (hB : TranslatedChartAnalytic) (hL : AnalyticLogarithmNearOne)
    (hC : CompositeDerivativesAtPoint) : TranslatedChartCompositeBound := by
  classical
  obtain ⟨D, hD0, hD⟩ := hB
  obtain ⟨Ψ, ε, hε, hΨa, hΨ0, hΨ⟩ := hL
  obtain ⟨hLin, hNot, hComp, hInner⟩ := hC
  set gOut : Fin 3 → imaginaryQuaternions → ℝ := fun d v => imCoord d (Ψ v) with hgOut
  have hgA : ∀ d, AnalyticAt ℝ (gOut d) 0 := fun d =>
    ((imCoord d).analyticAt (Ψ 0)).comp hΨa
  set P : ℕ → ℝ := fun j => ∑ d, ∑ p ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ p (gOut d) 0‖ with hP
  have hP0 : ∀ j, 0 ≤ P j := fun j => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set Dφ : ℕ → ℝ := fun k => ‖imPartCLM‖ * ∑ s ∈ Finset.range (k + 1), D k s with hDφ
  have hDφ0 : ∀ k, 0 ≤ Dφ k := fun k =>
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Finset.sum_nonneg fun s _ => hD0 k s)
  set DT : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 1),
    (Fintype.card (OrderedFinpartition j) : ℝ) * P j * (Dφ k + 1) ^ j with hDT
  have hDT0 : ∀ k, 0 ≤ DT k := fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP0 j)) (pow_nonneg (by linarith [hDφ0 k]) _)
  refine ⟨fun k M => compositeCoordBound k (k * M * 3) (DT k) 1, fun k M => ?_, ?_⟩
  · unfold compositeCoordBound
    have := hDT0 k
    positivity
  intro F f w V k ξ μ J M N hJ hAna
  set W₀ := chartedField w V with hW₀
  set B : Finset (F.Site F.depth × Fin 4) := Finset.univ.biUnion J with hBdef
  set n : ℕ := (bondDirPairs B).card with hn
  set bd : Fin n → F.Site F.depth × Fin 4 := fun r => (bondDirPair B r).1 with hbd
  set dd : Fin n → Fin 3 := fun r => (bondDirPair B r).2 with hdd
  set X : Fin n → imaginaryQuaternions := fun r => imBasis (dd r) with hX
  have hDb := (hD F w V k ξ μ).2
  have hU : ∀ b, ContDiff ℝ ω (bondQuat w V ξ μ b) := fun b => (hDb b.1 b.2).1
  set T : (Fin k → ℝ) → Fin n → ℝ := fun σ r => gOut (dd r) (relBondIm w V ξ μ (bd r) σ) with hT
  set G : (Fin n → ℝ) → ℝ := fun τ => f (leftTranslate (bondSpread bd X τ) W₀) with hG
  have hφA : ∀ b, AnalyticAt ℝ (relBondIm w V ξ μ b) 0 := fun b =>
    ((relBondIm_contDiff w V ξ μ b (hU b)).contDiffAt).analyticAt
  have hTr : ∀ r, AnalyticAt ℝ (fun σ => T σ r) 0 := fun r => by
    have h1 : AnalyticAt ℝ (gOut (dd r)) (relBondIm w V ξ μ (bd r) 0) := by
      rw [relBondIm_zero]
      exact hgA _
    exact h1.comp (hφA (bd r))
  have hTa : AnalyticAt ℝ T 0 := AnalyticAt.pi hTr
  have hT0 : T 0 = 0 := by
    funext r
    simp [hT, hgOut, relBondIm_zero, hΨ0]
  have hGa : AnalyticAt ℝ G 0 := hAna n bd X
  have hGa' : AnalyticAt ℝ G (T 0) := by
    rw [hT0]
    exact hGa
  have hev : (fun σ : Fin k → ℝ => G (T σ)) =ᶠ[𝓝 0] fun σ => f (translatedChart w V ξ μ σ) := by
    have hall : ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ), ∀ b ∈ B,
        expUnit (Ψ (relBondIm w V ξ μ b σ)) * W₀ b.1 b.2 = translatedChart w V ξ μ σ b.1 b.2 :=
      (Filter.eventually_all_finset B).2 fun b _ => eventually_expUnit_relBondIm_mul Ψ hε hΨ w V ξ μ b (hU b)
    filter_upwards [hall] with σ hσ
    have e : leftTranslate (bondSpread bd X (T σ)) W₀ = translatedChart w V ξ μ σ := by
      funext y i
      have h1 := bondSpread_bondDirPairs B (fun b => Ψ (relBondIm w V ξ μ b σ)) y i
      have h2 : bondSpread bd X (T σ) y i = if (y, i) ∈ B then Ψ (relBondIm w V ξ μ (y, i) σ) else 0 := h1
      show expUnit (bondSpread bd X (T σ) y i) * W₀ y i = _
      rw [h2]
      split_ifs with hb
      · exact hσ (y, i) hb
      · rw [expUnit_at_zero, one_mul, hW₀, ← translatedChart_at_zero w V ξ μ]
        refine ((hDb y i).2.2 σ 0 fun l hl => ?_).symm
        exact absurd (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hJ l _ hl⟩) hb
    show f _ = _
    rw [e]
  refine ⟨(AnalyticAt.comp hGa' hTa).congr hev, ?_⟩
  intro hw hξ hμ hM hN hk hbound
  have hcard : n ≤ k * M * 3 := by
    have h1 : B.card ≤ k * M := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ l, (J l).card ≤ ∑ _l : Fin k, M := Finset.sum_le_sum fun l _ => hM l
        _ = k * M := by simp
    have h2 : n = B.card * 3 := by
      simp [hn, bondDirPairs, Finset.card_product]
    rw [h2]
    exact Nat.mul_le_mul_right 3 h1
  have hbu : ∀ (b : F.Site F.depth × Fin 4) (j : ℕ), ‖iteratedFDeriv ℝ j (bondQuat w V ξ μ b) 0‖ ≤ D k j :=
    fun b j => (hDb b.1 b.2).2.1 (hw b) (fun l => hξ l b) (fun l => hμ l _ _) j
  have hrow : ∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n),
      iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r =
        iteratedFDeriv ℝ j (fun σ => T σ r) 0 (fun m => Pi.single (v m) 1) := by
    intro j v r
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r).iteratedFDeriv_comp_left
      (f := T) (x := 0) (n := ω) hTa.contDiffAt (i := j) le_top
    have h2 : (fun σ => T σ r) = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) r) ∘ T := rfl
    rw [h2, h1]
    rfl
  have bT : ∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n), 1 ≤ j → j ≤ k →
      |iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r| ≤ DT k := by
    intro j v r hj1 hjk
    rw [hrow]
    have h1 := hComp j (Fin k → ℝ) imaginaryQuaternions ℝ (gOut (dd r)) (relBondIm w V ξ μ (bd r)) 0 (P j) (Dφ k)
      (hP0 j) (hDφ0 k) (hφA _) (by rw [relBondIm_zero]; exact hgA _) (fun p hp => by
        rw [relBondIm_zero]
        have a1 : ‖iteratedFDeriv ℝ p (gOut (dd r)) 0‖ ≤
            ∑ p ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ p (gOut (dd r)) 0‖ :=
          Finset.single_le_sum (f := fun p => ‖iteratedFDeriv ℝ p (gOut (dd r)) 0‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
        have a2 : ∑ p ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ p (gOut (dd r)) 0‖ ≤ P j :=
          Finset.single_le_sum (f := fun d => ∑ p ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ p (gOut d) 0‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (dd r))
        exact a1.trans a2)
      (fun s _ hs => by
        refine (norm_iteratedFDeriv_relBondIm_le w V ξ μ (bd r) (hU _) s).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
        refine (hbu _ s).trans ?_
        exact Finset.single_le_sum (f := fun s => D k s) (fun s _ => hD0 k s)
          (Finset.mem_range.mpr (by omega)))
      (fun m => Pi.single (v m) 1) (fun m => norm_piSingle_one_le (v m))
    have h2 : (Fintype.card (OrderedFinpartition j) : ℝ) * P j * (Dφ k + 1) ^ j ≤ DT k :=
      Finset.single_le_sum (f := fun j => (Fintype.card (OrderedFinpartition j) : ℝ) * P j * (Dφ k + 1) ^ j)
        (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP0 j)) (pow_nonneg (by linarith [hDφ0 k]) _))
        (Finset.mem_range.mpr (by omega))
    have h3 : |iteratedFDeriv ℝ j (fun σ => T σ r) 0 (fun m => Pi.single (v m) 1)| =
        ‖iteratedFDeriv ℝ j (gOut (dd r) ∘ relBondIm w V ξ μ (bd r)) 0 (fun m => Pi.single (v m) 1)‖ := rfl
    rw [h3]
    exact h1.trans h2
  have zT : ∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n) (m : Fin j), ¬ ParameterMovesBond ξ μ (v m) (bd r) →
      iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r = 0 := by
    intro j v r m hnr
    rw [hrow]
    refine hNot k j ℝ (fun σ => T σ r) (v m) (fun m => Pi.single (v m) 1) m (hTr r) (fun σ s => ?_) rfl
    have e : translatedChart w V ξ μ (Function.update σ (v m) s) (bd r).1 (bd r).2 =
        translatedChart w V ξ μ σ (bd r).1 (bd r).2 := by
      refine (hDb (bd r).1 (bd r).2).2.2 _ _ fun l hl => ?_
      have hne : l ≠ v m := fun e => hnr (e ▸ hl)
      simp [Function.update_of_ne hne]
    have e2 : bondQuat w V ξ μ (bd r) (Function.update σ (v m) s) = bondQuat w V ξ μ (bd r) σ := by
      unfold bondQuat
      rw [e]
    show gOut (dd r) (rightMulImCLM _ (bondQuat w V ξ μ (bd r) (Function.update σ (v m) s))) =
      gOut (dd r) (rightMulImCLM _ (bondQuat w V ξ μ (bd r) σ))
    rw [e2]
  have bG : ∀ (p : ℕ) (r : Fin p → Fin n), 1 ≤ p → p ≤ k → (∀ l, ∃ m, ParameterMovesBond ξ μ l (bd (r m))) →
      |iteratedFDeriv ℝ p G 0 (fun m => Pi.single (r m) 1)| ≤ N := by
    intro p r hp hpk hcomp
    have e1 : (fun τ' : Fin p → ℝ => f (leftTranslate (bondSpread (fun m => bd (r m)) (fun m => X (r m)) τ') W₀)) =
        G ∘ indexSumCLM r := by
      funext τ'
      have e2 : (fun q => ∑ m, τ' m * (Pi.single (r m) (1 : ℝ) : Fin n → ℝ) q) = indexSumCLM r τ' :=
        funext fun q => (indexSumCLM_apply r τ' q).symm
      show f _ = f _
      rw [bondSpread_comp_index, e2]
    have h1 := hLin p (Fin p → ℝ) (Fin n → ℝ) ℝ (indexSumCLM r) G 0 (by rw [map_zero]; exact hGa)
      (fun m => Pi.single m 1)
    rw [← e1, map_zero] at h1
    have h2 : (fun m => indexSumCLM r (Pi.single m 1)) = fun m => (Pi.single (r m) 1 : Fin n → ℝ) :=
      funext fun m => indexSumCLM_single r m
    rw [h2] at h1
    rw [← h1]
    exact hbound p (fun m => bd (r m)) (fun m => X (r m)) hp hpk (fun m => norm_imBasis _)
      (fun l => (hcomp l).imp fun m hm => hJ l _ hm)
  have hfin := hInner k n G T (fun l r => ParameterMovesBond ξ μ l (bd r)) (DT k) N hk (hDT0 k) hN hTa hT0 hGa bT zT bG
  have e3 : iteratedFDeriv ℝ k (G ∘ T) 0 =
      iteratedFDeriv ℝ k (fun σ : Fin k → ℝ => f (translatedChart w V ξ μ σ)) 0 :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  rw [← e3]
  exact hfin.trans (compositeCoordBound_le_of_le (hDT0 k) hN hcard)
end YangMills.Construction.ColdStepAtMirrorFrames
end
