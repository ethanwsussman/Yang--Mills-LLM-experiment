import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.IsometriesOfTheEnergy
import YangMills.Construction.HullsInEveryVolume.EvenTranslatesBoundACopy
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChessboardGrids
open TorusFields WeightedResponses
variable {N : ℕ}
private def reflectionIsometry (g : MirrorGrid) (τ : Fin 4 → Bool) : TorusIsometry where
  axisPerm := 1
  axisSign := fun i => if τ i then -1 else 1
  offset := fun i => if τ i then 2 * g.offset i + 2 * (g.side : ℤ) + 1 else 0
  axisSign_unit := fun i => by by_cases h : τ i <;> simp [h]
private theorem mapSite_reflectionIsometry (g : MirrorGrid) (τ : Fin 4 → Bool) (x : TorusSite N) :
    (reflectionIsometry g τ).mapSite x = g.reflectSite τ x := by
  funext i
  by_cases h : τ i
  · simp only [TorusIsometry.mapSite, reflectionIsometry, MirrorGrid.reflectSite, h, if_true,
      Equiv.Perm.coe_one, id]
    push_cast
    ring
  · simp [TorusIsometry.mapSite, reflectionIsometry, MirrorGrid.reflectSite, h]
private theorem reflectField_of_transports (g : MirrorGrid) (τ : Fin 4 → Bool) {U U' : TorusField N}
    (h : (reflectionIsometry g τ).Transports U U') : g.reflectField τ U' = U := by
  funext x k
  have hk := h x k
  have hp : (reflectionIsometry g τ).axisPerm.symm k = k := rfl
  rw [hp, mapSite_reflectionIsometry] at hk
  by_cases hτ : τ k
  · have hs : (reflectionIsometry g τ).axisSign k ≠ 1 := by simp [reflectionIsometry, hτ]
    rw [if_neg hs] at hk
    simpa only [MirrorGrid.reflectField, hτ, if_true] using hk
  · have hs : (reflectionIsometry g τ).axisSign k = 1 := by simp [reflectionIsometry, hτ]
    rw [if_pos hs] at hk
    simpa only [MirrorGrid.reflectField, hτ, Bool.false_eq_true, if_false] using hk
private theorem measurable_link (x : TorusSite N) (b : Fin 4) :
    Measurable fun U : TorusField N => U x b :=
  (measurable_pi_apply b).comp (measurable_pi_apply x)
private theorem measurable_reflectField (g : MirrorGrid) (τ : Fin 4 → Bool) :
    Measurable (g.reflectField τ : TorusField N → TorusField N) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun k => ?_
  unfold MirrorGrid.reflectField
  by_cases h : τ k
  · simp only [h, if_true]
    exact (measurable_link _ _).inv
  · simp only [h, Bool.false_eq_true, if_false]
    exact measurable_link _ _
private theorem measurable_translate (u : TorusSite N) :
    Measurable (TorusFields.translate u : TorusField N → TorusField N) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => measurable_link _ _
private theorem wilsonLaw_isProbability [NeZero N] (β : ℝ) : IsProbabilityMeasure (wilsonLaw β N) := by apply _root_.YangMills.SharedProofs.p2076 <;> assumption
private theorem integral_reflectField (hH : FieldHaar.HaarInvariantUnderSymmetries) [NeZero N] (β : ℝ)
    (g : MirrorGrid) (τ : Fin 4 → Bool) {G : TorusField N → ℝ} (hG : Measurable G) :
    ∫ U, G (g.reflectField τ U) ∂(wilsonLaw β N) = ∫ U, G U ∂(wilsonLaw β N) := by
  obtain ⟨Ψ, hΨ, hc⟩ := (hH N).2 (reflectionIsometry g τ)
  set Z := ∫ U', Real.exp (-β * wilsonAction Finset.univ U') ∂(fieldHaar N) with hZ
  let ρ : TorusField N → NNReal := fun U => Real.toNNReal (Real.exp (-β * wilsonAction Finset.univ U) / Z)
  have hρc : Continuous ρ :=
    continuous_real_toNNReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonAction _))).div_const _)
  have hlaw : wilsonLaw β N = (fieldHaar N).withDensity fun U => (ρ U : ENNReal) := rfl
  have hρΨ : ∀ U, ρ (Ψ U) = ρ U := by
    intro U
    simp only [ρ, wilsonAction_of_transports (hc U)]
  have hh : Measurable fun U => ρ U • G (g.reflectField τ U) :=
    hρc.measurable.smul (hG.comp (measurable_reflectField g τ))
  have hchange := integral_map (μ := fieldHaar N) hΨ.measurable.aemeasurable
    (f := fun U => ρ U • G (g.reflectField τ U)) (by rw [hΨ.map_eq]; exact hh.aestronglyMeasurable)
  rw [hΨ.map_eq] at hchange
  rw [hlaw, integral_withDensity_eq_integral_smul hρc.measurable,
    integral_withDensity_eq_integral_smul hρc.measurable, hchange]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [hρΨ, reflectField_of_transports g τ (hc U)]
private def cellOf (τ : Fin 4 → Bool) (e : Fin 4 → ℕ) : Fin 4 → ℕ := fun i => 2 * e i + (τ i).toNat
private theorem cellParity_cellOf (τ : Fin 4 → Bool) (e : Fin 4 → ℕ) :
    MirrorGrid.cellParity (cellOf τ e) = τ := by
  funext i
  cases h : τ i <;> simp [MirrorGrid.cellParity, cellOf, h]
private theorem prod_cellIndices (g : MirrorGrid) {k : ℕ} (h1 : N / g.side = 2 * k)
    (h2 : N / (2 * g.side) = k) (f : (Fin 4 → ℕ) → ℝ) :
    ∏ c ∈ g.cellIndices N, f c = ∏ τ : Fin 4 → Bool, ∏ e ∈ g.evenTranslations N, f (cellOf τ e) := by
  rw [← Finset.prod_product' Finset.univ (g.evenTranslations N) (fun τ e => f (cellOf τ e))]
  have hinv : ∀ c : Fin 4 → ℕ, cellOf (MirrorGrid.cellParity c) (fun i => c i / 2) = c := by
    intro c
    funext i
    rcases Nat.mod_two_eq_zero_or_one (c i) with h | h <;> simp [cellOf, MirrorGrid.cellParity, h] <;> omega
  refine Finset.prod_nbij' (fun c => (MirrorGrid.cellParity c, fun i => c i / 2)) (fun x => cellOf x.1 x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range, h1] at hc
    simp only [Finset.mem_product, Finset.mem_univ, true_and, MirrorGrid.evenTranslations,
      Fintype.mem_piFinset, Finset.mem_range, h2]
    intro i
    have := hc i
    omega
  · rintro ⟨τ, e⟩ hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, MirrorGrid.evenTranslations,
      Fintype.mem_piFinset, Finset.mem_range, h2] at hx
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range, h1]
    intro i
    have := hx i
    cases h : τ i <;> simp [cellOf, h] <;> omega
  · intro c _
    exact hinv c
  · rintro ⟨τ, e⟩ _
    refine Prod.ext (cellParity_cellOf τ e) ?_
    funext i
    cases h : τ i <;> simp [cellOf, h] <;> omega
  · intro c _
    simp only [hinv]
private theorem evenShift_cellOf (g : MirrorGrid) (τ : Fin 4 → Bool) (e : Fin 4 → ℕ) :
    (g.evenShift (cellOf τ e) : TorusSite N) = siteOfInt fun i => 2 * (g.side : ℤ) * (e i : ℤ) := by
  funext i
  have h : cellOf τ e i - cellOf τ e i % 2 = 2 * e i := by
    cases h : τ i <;> simp [cellOf, h]
  simp only [MirrorGrid.evenShift, siteOfInt, h]
  push_cast
  ring
private def negAxes (τ : Fin 4 → Bool) (v : TorusSite N) : TorusSite N :=
  fun i => if τ i then -v i else v i
private theorem reflectSite_add_negAxes (g : MirrorGrid) (τ : Fin 4 → Bool) (v x : TorusSite N) :
    g.reflectSite τ (x + negAxes τ v) = g.reflectSite τ x + v := by
  funext i
  by_cases h : τ i
  · simp only [MirrorGrid.reflectSite, negAxes, h, if_true, Pi.add_apply]
    ring
  · simp [MirrorGrid.reflectSite, negAxes, h]
private theorem reflectField_translate (g : MirrorGrid) (τ : Fin 4 → Bool) (v : TorusSite N)
    (U : TorusField N) :
    g.reflectField τ (TorusFields.translate v U) =
      TorusFields.translate (negAxes τ v) (g.reflectField τ U) := by
  funext x k
  have h2 : g.reflectSite τ x - unitStep N k + v = g.reflectSite τ x + v - unitStep N k := by abel
  simp only [MirrorGrid.reflectField, TorusFields.translate, reflectSite_add_negAxes, h2]
private def flipIndex (k : ℕ) (τ : Fin 4 → Bool) (e : Fin 4 → ℕ) : Fin 4 → ℕ :=
  fun i => if τ i = true ∧ e i ≠ 0 then k - e i else e i
private theorem flipIndex_lt {k : ℕ} (τ : Fin 4 → Bool) {e : Fin 4 → ℕ} (he : ∀ i, e i < k)
    (i : Fin 4) : flipIndex k τ e i < k := by
  have := he i
  by_cases h : τ i = true ∧ e i ≠ 0
  · simp only [flipIndex, if_pos h]
    omega
  · simpa only [flipIndex, if_neg h] using this
private theorem flipIndex_flipIndex {k : ℕ} (τ : Fin 4 → Bool) {e : Fin 4 → ℕ} (he : ∀ i, e i < k) :
    flipIndex k τ (flipIndex k τ e) = e := by
  funext i
  have := he i
  by_cases hτ : τ i = true
  · by_cases h0 : e i = 0
    · simp [flipIndex, hτ, h0]
    · have h1 : k - e i ≠ 0 := by omega
      simp only [flipIndex, hτ, h0, h1, true_and, ne_eq, not_false_eq_true, if_true]
      omega
  · simp [flipIndex, hτ]
private theorem siteOfInt_flipIndex (g : MirrorGrid) {k : ℕ} (hN : 2 * g.side * k = N)
    (τ : Fin 4 → Bool) {e : Fin 4 → ℕ} (he : ∀ i, e i < k) :
    (siteOfInt fun i => 2 * (g.side : ℤ) * (flipIndex k τ e i : ℤ) : TorusSite N) =
      negAxes τ (siteOfInt fun i => 2 * (g.side : ℤ) * (e i : ℤ)) := by
  funext i
  have hz : (2 * (g.side : ZMod N) * (k : ZMod N)) = 0 := by
    have : ((2 * g.side * k : ℕ) : ZMod N) = 0 := by rw [hN]; exact ZMod.natCast_self N
    exact_mod_cast this
  by_cases hτ : τ i = true
  · by_cases h0 : e i = 0
    · simp [siteOfInt, negAxes, flipIndex, hτ, h0]
    · have hle : e i ≤ k := (he i).le
      simp only [siteOfInt, negAxes, flipIndex, hτ, h0, true_and, ne_eq, not_false_eq_true, if_true]
      push_cast [Nat.cast_sub hle]
      linear_combination hz
  · simp [siteOfInt, negAxes, flipIndex, hτ]
private theorem copies_of_cellParity (g : MirrorGrid) {k : ℕ} (hN : 2 * g.side * k = N)
    (h2 : N / (2 * g.side) = k) (F : TorusField N → ℝ) (τ : Fin 4 → Bool) (U : TorusField N) :
    ∏ e ∈ g.evenTranslations N, g.cellCopy F (cellOf τ e) U =
      ∏ e ∈ g.evenTranslations N,
        F (TorusFields.translate (siteOfInt fun i => 2 * (g.side : ℤ) * (e i : ℤ)) (g.reflectField τ U)) := by
  have hmem : ∀ e : Fin 4 → ℕ, e ∈ g.evenTranslations N ↔ ∀ i, e i < k := by
    intro e
    simp only [MirrorGrid.evenTranslations, Fintype.mem_piFinset, Finset.mem_range, h2]
  refine Finset.prod_nbij' (flipIndex k τ) (flipIndex k τ) ?_ ?_ ?_ ?_ ?_
  · intro e he
    exact (hmem _).2 (flipIndex_lt τ ((hmem e).1 he))
  · intro e he
    exact (hmem _).2 (flipIndex_lt τ ((hmem e).1 he))
  · intro e he
    exact flipIndex_flipIndex τ ((hmem e).1 he)
  · intro e he
    exact flipIndex_flipIndex τ ((hmem e).1 he)
  · intro e he
    simp only [MirrorGrid.cellCopy]
    rw [cellParity_cellOf, evenShift_cellOf, reflectField_translate,
      siteOfInt_flipIndex g hN τ ((hmem e).1 he)]
private theorem prod_le_mean_pow (y : (Fin 4 → Bool) → ℝ) (hy : ∀ τ, 0 ≤ y τ) :
    ∏ τ, y τ ≤ ∑ τ, ((16 : ℕ) : ℝ)⁻¹ * y τ ^ 16 := by
  have hcard : (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by simp
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin 4 → Bool => ((16 : ℕ) : ℝ)⁻¹)
    (fun τ => y τ ^ 16) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, hcard]; norm_num) (fun τ _ => pow_nonneg (hy τ) 16)
  simpa only [Real.pow_rpow_inv_natCast (hy _) (by norm_num : (16 : ℕ) ≠ 0)] using h
private theorem norm_prod_le_prod_bound {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ) {C : ℝ}
    (h : ∀ i a, |f i a| ≤ C) (a : α) : ‖∏ i ∈ s, f i a‖ ≤ ∏ _i ∈ s, C := by
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => h i a
theorem evenTranslatesBound_holds (hH : FieldHaar.HaarInvariantUnderSymmetries) :
    evenTranslatesBoundStatement := by
  intro L M N _ β g _ hL _ hN hg _ F hF
  obtain ⟨p, _, hpM, hside⟩ := hg
  have := wilsonLaw_isProbability (N := N) β
  obtain ⟨C, hC⟩ := hF.bounded
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hl : 0 < g.side := by rw [hside]; exact pow_pos hLpos p
  obtain ⟨k, hk⟩ : ∃ k, k = L ^ (M - p) := ⟨_, rfl⟩
  have hkpos : 0 < k := by rw [hk]; exact pow_pos hLpos _
  have hNk : 2 * g.side * k = N := by
    rw [hN, hside, hk, mul_assoc, ← pow_add, Nat.add_sub_cancel' hpM]
  have h1 : N / g.side = 2 * k := by
    rw [← hNk, mul_comm 2 g.side, mul_assoc]
    exact Nat.mul_div_cancel_left _ hl
  have h2 : N / (2 * g.side) = k := by
    rw [← hNk]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hcard : (g.cellIndices N).card ≠ 0 := by
    refine Finset.card_ne_zero_of_mem (a := fun _ => 0) ?_
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range, h1]
    intro _
    omega
  set a : (Fin 4 → ℕ) → TorusSite N := fun e => siteOfInt fun i => 2 * (g.side : ℤ) * (e i : ℤ) with ha
  set Y : TorusField N → ℝ := fun U => ∏ e ∈ g.evenTranslations N, F (TorusFields.translate (a e) U) ^ 16 with hY
  have hFs : ∀ u : TorusSite N, Measurable fun U => F (TorusFields.translate u U) :=
    fun u => hF.measurable.comp (measurable_translate u)
  have hYm : Measurable Y := Finset.measurable_fun_prod _ fun e _ => (hFs (a e)).pow_const 16
  have hC16 : ∀ (e : Fin 4 → ℕ) (U : TorusField N), |F (TorusFields.translate (a e) U) ^ 16| ≤ C ^ 16 := by
    intro e U
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 16
  have hYi : ∀ τ : Fin 4 → Bool, Integrable (fun U => Y (g.reflectField τ U)) (wilsonLaw β N) := by
    intro τ
    refine Integrable.of_bound (hYm.comp (measurable_reflectField g τ)).aestronglyMeasurable
      (∏ _e ∈ g.evenTranslations N, C ^ 16) (ae_of_all _ fun U => ?_)
    exact norm_prod_le_prod_bound (g.evenTranslations N) (fun e U => F (TorusFields.translate (a e) U) ^ 16) hC16
      (g.reflectField τ U)
  have hcm : ∀ c : Fin 4 → ℕ, Measurable (g.cellCopy F c) := fun c =>
    hF.measurable.comp ((measurable_reflectField g _).comp (measurable_translate _))
  have hI1 : Integrable (fun U => ∏ c ∈ g.cellIndices N, g.cellCopy F c U) (wilsonLaw β N) := by
    refine Integrable.of_bound (Finset.measurable_fun_prod _ fun c _ => hcm c).aestronglyMeasurable
      (∏ _c ∈ g.cellIndices N, C) (ae_of_all _ fun U => ?_)
    exact norm_prod_le_prod_bound (g.cellIndices N) (fun c U => g.cellCopy F c U) (fun _ _ => hC _) U
  have hI0 : 0 ≤ ∫ U, ∏ c ∈ g.cellIndices N, g.cellCopy F c U ∂(wilsonLaw β N) :=
    integral_nonneg fun U => Finset.prod_nonneg fun _ _ => hF.nonneg _
  have hnorm : g.chessboardNorm β N F ^ (g.cellIndices N).card =
      ∫ U, ∏ c ∈ g.cellIndices N, g.cellCopy F c U ∂(wilsonLaw β N) := by
    unfold MirrorGrid.chessboardNorm
    rw [one_div]
    exact Real.rpow_inv_natCast_pow hI0 hcard
  have hpt : ∀ U, ∏ c ∈ g.cellIndices N, g.cellCopy F c U ≤
      ∑ τ : Fin 4 → Bool, ((16 : ℕ) : ℝ)⁻¹ * Y (g.reflectField τ U) := by
    intro U
    rw [prod_cellIndices g h1 h2]
    simp only [copies_of_cellParity g hNk h2 F]
    refine (prod_le_mean_pow _ fun τ => Finset.prod_nonneg fun _ _ => hF.nonneg _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hY, Finset.prod_pow, ha]
  have hcard16 : (Finset.univ : Finset (Fin 4 → Bool)).card = 16 := by simp
  rw [hnorm]
  calc ∫ U, ∏ c ∈ g.cellIndices N, g.cellCopy F c U ∂(wilsonLaw β N)
      ≤ ∫ U, ∑ τ : Fin 4 → Bool, ((16 : ℕ) : ℝ)⁻¹ * Y (g.reflectField τ U) ∂(wilsonLaw β N) :=
        integral_mono hI1 (integrable_finsetSum _ fun τ _ => (hYi τ).const_mul _) hpt
    _ = ∑ _τ : Fin 4 → Bool, ((16 : ℕ) : ℝ)⁻¹ * ∫ U, Y U ∂(wilsonLaw β N) := by
        rw [integral_finsetSum _ fun τ _ => (hYi τ).const_mul _]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [integral_const_mul, integral_reflectField hH β g τ hYm]
    _ = ∫ U, Y U ∂(wilsonLaw β N) := by
        rw [Finset.sum_const, hcard16, nsmul_eq_mul, ← mul_assoc]
        norm_num
end YangMills.Construction.ChessboardGrids
end
