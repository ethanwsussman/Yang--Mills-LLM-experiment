import YangMills.Construction.ColdChainAtEveryLevel.CutsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.DifferencesAreNearlyFlat
import YangMills.Construction.ColdChainAtEveryLevel.EveryFormSplitsAlongTheSlice
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapOnDifferences
import YangMills.Construction.ColdChainAtEveryLevel.SliceProjectionOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SliceProjection
open BlockAverages CoordinateSeminorms CoordinateCutoffs GaugeMap
variable {F : BlockFrame}
theorem nonneg_cellwiseL4Norm (S : Finset F.Cell) (w : F.Site 0 → ℝ) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    0 ≤ cellwiseL4Norm S w f := Real.sqrt_nonneg _
theorem cellwiseL4Norm_le_add_of_bond_le (S : Finset F.Cell) (w : F.Site 0 → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f g h : F.Site 0 → Fin 4 → ℍ[ℝ])
    (hb : ∀ b ∈ innerBonds S 0, ‖f b.1 b.2‖ ≤ ‖g b.1 b.2‖ + ‖h b.1 b.2‖) :
    cellwiseL4Norm S w f ≤ cellwiseL4Norm S w g + cellwiseL4Norm S w h := by
  set G : (F.Site 0 → Fin 4 → ℍ[ℝ]) → F.Cell → ℝ := fun q z =>
    Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S {z} 0, (w b.1 * ‖q b.1 b.2‖) ^ 4)) with hG
  have hs : ∀ q : F.Site 0 → Fin 4 → ℍ[ℝ], cellwiseL4Norm S w q = Real.sqrt (∑ z ∈ S, G q z ^ 2) :=
    fun q => congrArg Real.sqrt (Finset.sum_congr rfl fun z _ => (Real.sq_sqrt (Real.sqrt_nonneg _)).symm)
  rw [hs f, hs g, hs h]
  refine sqrt_sum_sq_le_add S (G f) (G g) (G h) (fun _ _ => Real.sqrt_nonneg _) fun z _ => ?_
  exact sqrt_sqrt_sum_pow_four_le_add (bondsOver S {z} 0) (fun b => w b.1 * ‖f b.1 b.2‖)
    (fun b => w b.1 * ‖g b.1 b.2‖)
    (fun b => w b.1 * ‖h b.1 b.2‖) (fun b _ => mul_nonneg (hw _) (norm_nonneg _))
    (fun b _ => mul_nonneg (hw _) (norm_nonneg _)) (fun b _ => mul_nonneg (hw _) (norm_nonneg _)) fun b hb' => by
      have := mul_le_mul_of_nonneg_left (hb b (mem_bondsOver.1 hb').1) (hw b.1)
      linarith
theorem weightedNorm_baseOnlyChart_sq_le (S : Finset F.Cell) (R : F.FieldChain)
    (v : F.Site 0 → Fin 4 → imaginaryQuaternions) (w : F.SiteWeights) :
    weightedNorm S R (baseOnlyChart v) w ^ 2 ≤ ((2 * 3 + 1 : ℕ) : ℝ) ^ 4 *
      (cellwiseL4Norm S (w 0) (fun x i => v x i) ^ 2 +
        ∑ q ∈ plaquettesOver S S 0, (w 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2) := by
  classical
  rw [weightedNorm_sq]
  set f : F.Cell → ℝ := fun y => localNormSq S {y} R (baseOnlyChart v) w with hf
  have h1 := sum_sum_cellBall_le S 3 f (fun y => localNormSq_nonneg _ _ _ _ _)
  refine (Finset.sum_le_sum fun z _ => localNormSq_le_sum_singletons S _ R _ w).trans (h1.trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e : ∀ y, f y = Real.sqrt (∑ b ∈ bondsOver S {y} 0, (w 0 b.1 * ‖(v b.1 b.2 : ℍ[ℝ])‖) ^ 4) +
      ∑ q ∈ plaquettesOver S {y} 0, (w 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2 := by
    intro y
    simp only [hf]
    unfold localNormSq
    simp [baseOnlyChart]
  simp only [e, Finset.sum_add_distrib]
  have h2 : ∑ y ∈ S, Real.sqrt (∑ b ∈ bondsOver S {y} 0, (w 0 b.1 * ‖(v b.1 b.2 : ℍ[ℝ])‖) ^ 4) =
      cellwiseL4Norm S (w 0) (fun x i => v x i) ^ 2 := by
    unfold cellwiseL4Norm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)]
  rw [h2]
  have h3 : ∑ y ∈ S, ∑ q ∈ plaquettesOver S {y} 0, (w 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2 ≤
      ∑ q ∈ plaquettesOver S S 0, (w 0 q.1 * ‖linearizedCurl (R 0) v q‖) ^ 2 := by
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity
      obtain ⟨y, hy, hq'⟩ := Finset.mem_biUnion.1 hq
      obtain ⟨h4, h5⟩ := mem_plaquettesOver.1 hq'
      rw [Finset.mem_singleton] at h5
      exact mem_plaquettesOver.2 ⟨h4, h5 ▸ hy⟩
    · intro y _ y' _ hne
      refine Finset.disjoint_left.2 fun q h1 h2 => hne ?_
      have a := (mem_plaquettesOver.1 h1).2
      have b := (mem_plaquettesOver.1 h2).2
      rw [Finset.mem_singleton] at a b
      exact a.symm.trans b
  linarith
theorem sliceProjectionStatement_holds (hE : sliceDecompositionStatement)
    (hG : gaugeMapOnDifferencesStatement) (hD : covariantDiffNearlyFlatStatement) :
    sliceProjectionStatement := by
  obtain ⟨c₁, L₁, hc₁, hE'⟩ := hE
  obtain ⟨c₂, C₂, L₂, hc₂, hC₂, hG'⟩ := hG
  obtain ⟨L₃, hD'⟩ := hD
  refine ⟨max (max L₁ L₂) L₃, fun L hL hLge => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLge
  have hL3 : L₃ ≤ L := le_trans (le_max_right _ _) hLge
  obtain ⟨c₃, C₃, hc₃, hC₃, hDL⟩ := hD' L hL hL3
  refine ⟨min (min c₁ c₂) (min c₃ (min 1 (1 / (2 * C₂)))), 98 * (1 + C₃), lt_min (lt_min hc₁ hc₂)
    (lt_min hc₃ (lt_min one_pos (by positivity))), by positivity, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsle hcold u
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hs1 : s ≤ c₁ := hsle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : s ≤ c₂ := hsle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : s ≤ c₃ := hsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : s ≤ 1 := hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs5 : s ≤ 1 / (2 * C₂) :=
    hsle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCs : C₂ * s ≤ 1 / 2 := by
    have h0 : 0 < 2 * C₂ := by positivity
    have := (le_div_iff₀ h0).1 hs5
    linarith
  obtain ⟨u₁, ξ, hsl, hmf, -, hsplit⟩ := hE' F m S hLF (hFL ▸ hL1) hamb hm hreg s V hs hs1 hcold u
  obtain ⟨-, hrest⟩ := hG' F m S hLF (hFL ▸ hL2) hamb hm hreg s V hs hs2 hcold
  obtain ⟨-, hsm, -, -⟩ := hrest ξ hmf
  set R0 := referenceFieldChain S V 0 with hR0
  have hv : ∀ x i, ((u x i - u₁ x i : imaginaryQuaternions) : ℍ[ℝ]) = covariantDiff R0 ξ x i := by
    intro x i
    rw [Submodule.coe_sub, hsplit x i]
    abel
  refine ⟨fun x i => u x i - u₁ x i, ?_, fun φ δ p hδ hδ8 hφ => ?_⟩
  · have e : (fun x i => u x i - (u x i - u₁ x i)) = u₁ := by
      funext x i
      abel
    rw [e]
    exact hsl
  set w := classWeight F φ 0 p with hw
  have hw0 : ∀ x, 0 ≤ w 0 x := fun x => by
    rw [hw, CoordinateCutoffs.classWeight_zero]
    exact (Real.exp_pos _).le
  set ga := gaugeMap S V R0 fun x i => (u x i : ℍ[ℝ]) with hga
  have hgm : ∀ x ∈ sitesOfCells S 0, ga x = gaugeMap S V R0 (covariantDiff R0 ξ) x := by
    intro x hx
    have h1 := gaugeMap_add_smul S V R0 (fun y k => (u₁ y k : ℍ[ℝ])) (covariantDiff R0 ξ) 1 x
    simp only [one_smul] at h1
    have h2 : (fun y k => (u₁ y k : ℍ[ℝ]) + covariantDiff R0 ξ y k) = fun y k => (u y k : ℍ[ℝ]) := by
      funext y k
      rw [hsplit]
    rw [h2, hsl x hx, zero_add] at h1
    exact h1
  have hbond : ∀ b ∈ innerBonds S 0, ‖covariantDiff R0 ξ b.1 b.2‖ ≤
      ‖covariantDiff R0 (gaugeRemainder S V ξ) b.1 b.2‖ + ‖covariantDiff R0 ga b.1 b.2‖ := by
    intro b hb
    have hb' := Finset.mem_filter.1 hb
    have h1 : b.1 ∈ sitesOfCells S 0 := (Finset.mem_product.1 hb'.1).1
    have h2 : b.1 + unitStep 0 b.2 ∈ sitesOfCells S 0 := hb'.2
    have e : covariantDiff R0 ξ b.1 b.2 =
        covariantDiff R0 (gaugeRemainder S V ξ) b.1 b.2 - covariantDiff R0 ga b.1 b.2 := by
      simp only [covariantDiff, gaugeRemainder]
      rw [hgm _ h1, hgm _ h2, ← hR0]
      simp only [adjointAction]
      noncomm_ring
    rw [e]
    exact norm_sub_le _ _
  have hX := cellwiseL4Norm_le_add_of_bond_le S (w 0) hw0 _ _ _ hbond
  have hφ' : ∀ y y', |φ y - φ y'| ≤ |δ| * cellSupDist y y' := fun y y' => by
    rw [abs_of_nonneg hδ]
    exact hφ y y'
  have habs : |δ| ≤ 1 / 8 := by
    rw [abs_of_nonneg hδ]
    exact hδ8
  obtain ⟨h1, -⟩ := hsm φ 0 δ p (by norm_num) habs hφ'
  set Xd := cellwiseL4Norm S (w 0) (covariantDiff R0 ξ) with hXd
  set Yd := cellwiseL4Norm S (w 0) (covariantDiff R0 ga) with hYd
  have hXd0 : 0 ≤ Xd := nonneg_cellwiseL4Norm _ _ _
  have hYd0 : 0 ≤ Yd := nonneg_cellwiseL4Norm _ _ _
  have h2 : Xd ≤ 2 * Yd := by
    have h3 : C₂ * s * Xd ≤ 1 / 2 * Xd := mul_le_mul_of_nonneg_right hCs hXd0
    linarith
  have hflat := hDL F m S hFL hamb hm hreg s V hs hs3 hcold φ 0 δ p (by norm_num) habs hφ' ξ
    (fun x i => u x i - u₁ x i) hmf hv
  have hcs : cellwiseL4Norm S (w 0) (fun x i => ((u x i - u₁ x i : imaginaryQuaternions) : ℍ[ℝ])) = Xd := by
    rw [hXd]
    congr 1
    funext x i
    exact hv x i
  rw [hcs] at hflat
  have hcurl : Real.sqrt (∑ q ∈ plaquettesOver S S 0, (w 0 q.1 *
      ‖linearizedCurl R0 (fun x i => u x i - u₁ x i) q‖) ^ 2) ≤ C₃ * Xd := by
    have h3 := Real.sqrt_nonneg (∑ c ∈ innerBonds S F.top, (classWeight F φ 0 p F.top c.1 *
      ‖linearPart (referenceFieldChain S V) (baseOnlyChart fun x i => u x i - u₁ x i) F.top c.1 c.2‖) ^ 2)
    have h4 : C₃ * s * Xd ≤ C₃ * Xd := by
      have : s * Xd ≤ 1 * Xd := mul_le_mul_of_nonneg_right hs4 hXd0
      nlinarith
    linarith
  have hnorm := weightedNorm_baseOnlyChart_sq_le S (referenceFieldChain S V) (fun x i => u x i - u₁ x i) w
  rw [hcs] at hnorm
  have hsumc : ∑ q ∈ plaquettesOver S S 0, (w 0 q.1 *
      ‖linearizedCurl (referenceFieldChain S V 0) (fun x i => u x i - u₁ x i) q‖) ^ 2 ≤ (C₃ * Xd) ^ 2 := by
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hcurl 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)] at h3
  have hfin : weightedNorm S (referenceFieldChain S V) (baseOnlyChart fun x i => u x i - u₁ x i) w ^ 2 ≤
      (49 * (1 + C₃) * Xd) ^ 2 := by
    refine hnorm.trans ?_
    have e7 : (((2 * 3 + 1 : ℕ) : ℝ)) ^ 4 = 2401 := by norm_num
    rw [e7]
    have : Xd ^ 2 + (C₃ * Xd) ^ 2 ≤ (1 + C₃) ^ 2 * Xd ^ 2 := by nlinarith [mul_nonneg hC₃.le (sq_nonneg Xd)]
    nlinarith
  have hfin' : weightedNorm S (referenceFieldChain S V) (baseOnlyChart fun x i => u x i - u₁ x i) w ≤
      49 * (1 + C₃) * Xd :=
    (pow_le_pow_iff_left₀ (weightedNorm_nonneg _ _ _ _) (by positivity) (by norm_num)).1 hfin
  refine hfin'.trans ?_
  have : 49 * (1 + C₃) * Xd ≤ 49 * (1 + C₃) * (2 * Yd) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine this.trans (le_of_eq ?_)
  ring
end YangMills.Construction.SliceProjection
end
