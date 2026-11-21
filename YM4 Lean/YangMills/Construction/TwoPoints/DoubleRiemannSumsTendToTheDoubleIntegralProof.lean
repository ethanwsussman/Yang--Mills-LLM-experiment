import YangMills.Construction.TwoPoints.DoubleRiemannSumsTendToTheDoubleIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace PairedGridSumLimit
def gridIndex (δ : ℝ) (z : AmbientSpace) : Fin 4 → ℤ := fun i => ⌊z i / δ⌋
theorem mem_gridCube_gridIndex {δ : ℝ} (hpos : 0 < δ) (z : AmbientSpace) :
    z ∈ gridCube δ (gridIndex δ z) := by
  intro i
  have below := Int.floor_le (z i / δ)
  have above := Int.lt_floor_add_one (z i / δ)
  rw [le_div_iff₀ hpos] at below
  rw [div_lt_iff₀ hpos] at above
  simp only [gridIndex]
  constructor <;> linarith
theorem gridIndex_eq_of_mem {δ : ℝ} (hpos : 0 < δ) {z : AmbientSpace} {j : Fin 4 → ℤ}
    (hz : z ∈ gridCube δ j) : gridIndex δ z = j :=
  (existsUnique_mem_gridCube hpos z).unique (mem_gridCube_gridIndex hpos z) hz
theorem measurable_gridIndex (δ : ℝ) : Measurable (gridIndex δ) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hq : Measurable fun z : AmbientSpace => z i / δ := by fun_prop
  exact Int.measurable_floor.comp hq
theorem measurableSet_gridCube (δ : ℝ) (j : Fin 4 → ℤ) : MeasurableSet (gridCube δ j) := by
  have hcube : gridCube δ j =
      ⋂ i, (fun z : AmbientSpace => z i) ⁻¹' Ico (δ * (j i : ℝ)) (δ * ((j i : ℝ) + 1)) := by
    ext z
    simp [gridCube]
  rw [hcube]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ico
theorem norm_gridCenter_sub_le {δ : ℝ} (hpos : 0 < δ) (z : AmbientSpace) :
    ‖gridCenter δ (gridIndex δ z) - z‖ ≤ δ := by
  rw [pi_norm_le_iff_of_nonneg hpos.le]
  intro i
  obtain ⟨lo, hi⟩ := mem_gridCube_gridIndex hpos z i
  have hc : (gridCenter δ (gridIndex δ z) - z) i = δ * ((gridIndex δ z i : ℝ) + 1 / 2) - z i := rfl
  have half : δ * ((gridIndex δ z i : ℝ) + 1 / 2) = δ * (gridIndex δ z i : ℝ) + δ / 2 := by ring
  have whole : δ * ((gridIndex δ z i : ℝ) + 1) = δ * (gridIndex δ z i : ℝ) + δ := by ring
  rw [whole] at hi
  rw [hc, half, Real.norm_eq_abs, abs_le]
  constructor <;> linarith
theorem tendsto_gridCenter (z : AmbientSpace) :
    Tendsto (fun δ => gridCenter δ (gridIndex δ z)) (𝓝[>] 0) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hδ
  filter_upwards [self_mem_nhdsWithin] with δ hpos
  exact norm_gridCenter_sub_le hpos z
theorem finite_setOf_gridCube_meets {δ : ℝ} (hpos : 0 < δ) {K : Set AmbientSpace}
    (hK : IsCompact K) : {j : Fin 4 → ℤ | ∃ z ∈ K, z ∈ gridCube δ j}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : AmbientSpace)
  refine (Set.finite_Icc (fun _ => ⌊-R / δ⌋) (fun _ => ⌊R / δ⌋)).subset ?_
  rintro j ⟨z, hzK, hzj⟩
  have hzR : ‖z‖ ≤ R := by simpa using hR hzK
  have coord : ∀ i, -R ≤ z i ∧ z i ≤ R := fun i => abs_le.1 ((norm_le_pi_norm z i).trans hzR)
  rw [← gridIndex_eq_of_mem hpos hzj]
  exact ⟨fun i => Int.floor_le_floor (div_le_div_of_nonneg_right (coord i).1 hpos.le),
    fun i => Int.floor_le_floor (div_le_div_of_nonneg_right (coord i).2 hpos.le)⟩
theorem setIntegralOf_eq_zero {Q : Set AmbientSpace} {k : AmbientSpace → ℂ}
    (h : ¬ ∃ z ∈ tsupport k, z ∈ Q) : setIntegralOf Q k = 0 := by
  show ∫ x in Q, k x = 0
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hxQ => ?_
  by_contra hkx
  exact h ⟨x, subset_tsupport k hkx, hxQ⟩
theorem setIntegralOf_gridCube_eq (δ : ℝ) (j : Fin 4 → ℤ) (k : AmbientSpace → ℂ) :
    setIntegralOf (gridCube δ j) k = ∫ x, (gridCube δ j).indicator k x :=
  (integral_indicator (measurableSet_gridCube δ j)).symm
def gridIntegrand (δ : ℝ) (k₁ k₂ V : AmbientSpace → ℂ) (w : AmbientSpace × AmbientSpace) : ℂ :=
  k₁ w.2 * k₂ w.1 * V (gridCenter δ (gridIndex δ w.1) - gridCenter δ (gridIndex δ w.2))
theorem measurable_gridIntegrand_factor (δ : ℝ) (V : AmbientSpace → ℂ) :
    Measurable fun w : AmbientSpace × AmbientSpace =>
      V (gridCenter δ (gridIndex δ w.1) - gridCenter δ (gridIndex δ w.2)) := by
  let cells : AmbientSpace × AmbientSpace → (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
    fun w => (gridIndex δ w.1, gridIndex δ w.2)
  have hcells : Measurable cells :=
    ((measurable_gridIndex δ).comp measurable_fst).prodMk
      ((measurable_gridIndex δ).comp measurable_snd)
  exact (Measurable.of_discrete (f := fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
    V (gridCenter δ p.1 - gridCenter δ p.2))).comp hcells
theorem pairedGridSum_eq_integral {δ : ℝ} (hpos : 0 < δ) {φ ψ : AmbientSpace → ℂ}
    (hφ : Continuous φ) (sφ : IsCompact (tsupport φ))
    (hψ : Continuous ψ) (sψ : IsCompact (tsupport ψ)) (W : AmbientSpace → ℂ) :
    pairedGridSum δ φ ψ W =
      ∫ w : AmbientSpace × AmbientSpace, gridIntegrand δ φ ψ W w ∂(volume.prod volume) := by
  classical
  set S₁ := (finite_setOf_gridCube_meets hpos sφ).toFinset with hS₁
  set S₂ := (finite_setOf_gridCube_meets hpos sψ).toFinset with hS₂
  have mem₁ : ∀ j, j ∈ S₁ ↔ ∃ z ∈ tsupport φ, z ∈ gridCube δ j := fun j => by simp [hS₁]
  have mem₂ : ∀ j, j ∈ S₂ ↔ ∃ z ∈ tsupport ψ, z ∈ gridCube δ j := fun j => by simp [hS₂]
  have cellIntegrable : ∀ (k : AmbientSpace → ℂ), Continuous k → IsCompact (tsupport k) → ∀ j,
      Integrable ((gridCube δ j).indicator k) := fun k hk sk j =>
    (hk.integrable_of_hasCompactSupport sk).indicator (measurableSet_gridCube δ j)
  have finiteSum : pairedGridSum δ φ ψ W =
      ∑ q ∈ S₁ ×ˢ S₂, setIntegralOf (gridCube δ q.1) φ * setIntegralOf (gridCube δ q.2) ψ *
        W (gridCenter δ q.2 - gridCenter δ q.1) := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    have hne : setIntegralOf (gridCube δ q.1) φ * setIntegralOf (gridCube δ q.2) ψ *
        W (gridCenter δ q.2 - gridCenter δ q.1) ≠ 0 := hq
    have ne₁ : setIntegralOf (gridCube δ q.1) φ ≠ 0 := fun h0 => hne (by simp [h0])
    have ne₂ : setIntegralOf (gridCube δ q.2) ψ ≠ 0 := fun h0 => hne (by simp [h0])
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem₁, mem₂]
    exact ⟨not_not.1 fun h0 => ne₁ (setIntegralOf_eq_zero h0),
      not_not.1 fun h0 => ne₂ (setIntegralOf_eq_zero h0)⟩
  have pointwise : ∀ w : AmbientSpace × AmbientSpace, gridIntegrand δ φ ψ W w =
      ∑ q ∈ S₁ ×ˢ S₂, ((gridCube δ q.2).indicator ψ w.1 * (gridCube δ q.1).indicator φ w.2) *
        W (gridCenter δ q.2 - gridCenter δ q.1) := by
    intro w
    have c₂ := mem_gridCube_gridIndex hpos w.2
    have c₁ := mem_gridCube_gridIndex hpos w.1
    rw [Finset.sum_eq_single (gridIndex δ w.2, gridIndex δ w.1)]
    · simp only [gridIntegrand, indicator_of_mem c₁, indicator_of_mem c₂]
      ring
    · rintro ⟨a, b⟩ _ hab
      by_cases ha : a = gridIndex δ w.2
      · have hb : b ≠ gridIndex δ w.1 := fun hb => hab (by rw [ha, hb])
        have out : w.1 ∉ gridCube δ b := fun hm => hb (gridIndex_eq_of_mem hpos hm).symm
        simp [indicator_of_notMem out]
      · have out : w.2 ∉ gridCube δ a := fun hm => ha (gridIndex_eq_of_mem hpos hm).symm
        simp [indicator_of_notMem out]
    · intro hq
      simp only [Finset.mem_product, mem₁, mem₂, not_and_or] at hq
      rcases hq with h0 | h0
      · have vanish : φ w.2 = 0 := not_not.1 fun hz => h0 ⟨w.2, subset_tsupport φ hz, c₂⟩
        simp [indicator_of_mem c₂, vanish]
      · have vanish : ψ w.1 = 0 := not_not.1 fun hz => h0 ⟨w.1, subset_tsupport ψ hz, c₁⟩
        simp [indicator_of_mem c₁, vanish]
  rw [finiteSum, integral_congr_ae (Eventually.of_forall pointwise), integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_mul_const, integral_prod_mul ((gridCube δ q.2).indicator ψ)
      ((gridCube δ q.1).indicator φ), setIntegralOf_gridCube_eq, setIntegralOf_gridCube_eq]
    ring
  · intro q _
    exact ((cellIntegrable ψ hψ sψ q.2).mul_prod (cellIntegrable φ hφ sφ q.1)).mul_const _
end PairedGridSumLimit
open PairedGridSumLimit in
theorem PairedGridSumLimit.holds : PairedGridSumLimit.Statement := by
  intro ε _ W hW φ hφmem ψ hψmem hfar
  obtain ⟨hφ, sφ, -⟩ := (mem_ccIn_iff _ _).1 hφmem
  obtain ⟨hψ, sψ, -⟩ := (mem_ccIn_iff _ _).1 hψmem
  have normCont : Continuous (euclidNorm : AmbientSpace → ℝ) := by
    unfold euclidNorm
    fun_prop
  set Far : Set AmbientSpace := {z | 2 * ε < euclidNorm z} with hFar
  have farOpen : IsOpen Far := isOpen_lt continuous_const normCont
  set D : Set AmbientSpace :=
    (fun w : AmbientSpace × AmbientSpace => w.1 - w.2) '' (tsupport ψ ×ˢ tsupport φ) with hD
  have diffCont : Continuous fun w : AmbientSpace × AmbientSpace => w.1 - w.2 :=
    continuous_fst.sub continuous_snd
  have Dcpt : IsCompact D := (sψ.prod sφ).image diffCont
  have DFar : D ⊆ Far := by
    rintro _ ⟨w, ⟨m₂, m₁⟩, rfl⟩
    exact hfar _ m₁ _ m₂
  obtain ⟨ρ, hρ, thickFar⟩ := Dcpt.exists_cthickening_subset_open farOpen DFar
  have thickCpt : IsCompact (Metric.cthickening ρ D) := Dcpt.cthickening
  obtain ⟨B, hB⟩ := thickCpt.exists_bound_of_continuousOn (hW.mono thickFar)
  set B₀ : ℝ := max B 0 with hB₀
  have B₀nonneg : 0 ≤ B₀ := le_max_right _ _
  set F : AmbientSpace × AmbientSpace → ℂ := fun w => φ w.2 * ψ w.1 * W (w.1 - w.2) with hF
  have offSupport : ∀ w : AmbientSpace × AmbientSpace, w ∉ tsupport ψ ×ˢ tsupport φ →
      φ w.2 * ψ w.1 = 0 := by
    intro w hw
    rw [Set.mem_prod, not_and_or] at hw
    rcases hw with h0 | h0
    · rw [image_eq_zero_of_notMem_tsupport h0, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h0, zero_mul]
  have weightCont : Continuous fun w : AmbientSpace × AmbientSpace => φ w.2 * ψ w.1 :=
    (hφ.comp continuous_snd).mul (hψ.comp continuous_fst)
  have WAt : ∀ w ∈ tsupport ψ ×ˢ tsupport φ, ContinuousAt W (w.1 - w.2) := fun w hw =>
    hW.continuousAt (farOpen.mem_nhds (DFar ⟨w, hw, rfl⟩))
  have Fcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hw : w ∈ tsupport ψ ×ˢ tsupport φ
    · exact weightCont.continuousAt.mul
        (ContinuousAt.comp (f := fun w : AmbientSpace × AmbientSpace => w.1 - w.2)
          (WAt w hw) diffCont.continuousAt)
    · have closedSupp : IsClosed (tsupport ψ ×ˢ tsupport φ) := (sψ.prod sφ).isClosed
      have nearZero : F =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [closedSupp.isOpen_compl.mem_nhds hw] with x hx
        simp [hF, offSupport x hx]
      exact nearZero.continuousAt
  have Fsupp : HasCompactSupport F :=
    HasCompactSupport.intro (sψ.prod sφ) fun x hx => by simp [hF, offSupport x hx]
  have Fint : Integrable F (volume.prod volume) := Fcont.integrable_of_hasCompactSupport Fsupp
  have iterated : (lebesgueIntegral fun y : AmbientSpace =>
      lebesgueIntegral fun x : AmbientSpace => φ x * ψ y * W (y - x)) =
      ∫ w, F w ∂(volume.prod volume) :=
    (integral_prod F Fint).symm
  rw [iterated]
  have gridLimit : Tendsto (fun δ => ∫ w, gridIntegrand δ φ ψ W w ∂(volume.prod volume))
      (𝓝[>] 0) (𝓝 (∫ w, F w ∂(volume.prod volume))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun w => B₀ * (‖ψ w.1‖ * ‖φ w.2‖)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ =>
        (weightCont.measurable.mul (measurable_gridIntegrand_factor δ W)).aestronglyMeasurable
    · have fine : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo 0 (ρ / 2) := Ioo_mem_nhdsGT (half_pos hρ)
      filter_upwards [fine] with δ hδ
      refine Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ tsupport ψ ×ˢ tsupport φ
      · set c₁ := gridCenter δ (gridIndex δ w.1)
        set c₂ := gridCenter δ (gridIndex δ w.2)
        have near₁ : ‖c₁ - w.1‖ ≤ δ := norm_gridCenter_sub_le hδ.1 w.1
        have near₂ : ‖c₂ - w.2‖ ≤ δ := norm_gridCenter_sub_le hδ.1 w.2
        have shift : c₁ - c₂ - (w.1 - w.2) = (c₁ - w.1) - (c₂ - w.2) := by abel
        have close : dist (c₁ - c₂) (w.1 - w.2) ≤ ρ := by
          rw [dist_eq_norm, shift]
          linarith [norm_sub_le (c₁ - w.1) (c₂ - w.2), hδ.2]
        have inThick : c₁ - c₂ ∈ Metric.cthickening ρ D :=
          Metric.mem_cthickening_of_dist_le _ _ _ _ (show w.1 - w.2 ∈ D from ⟨w, hw, rfl⟩) close
        have bound : ‖W (c₁ - c₂)‖ ≤ B₀ := (hB _ inThick).trans (le_max_left _ _)
        rw [gridIntegrand, norm_mul, norm_mul, mul_comm (‖ψ w.1‖) (‖φ w.2‖), mul_comm B₀]
        exact mul_le_mul_of_nonneg_left bound (by positivity)
      · rw [gridIntegrand, offSupport w hw, zero_mul, norm_zero]
        exact mul_nonneg B₀nonneg (by positivity)
    · have int₁ : Integrable (fun x : AmbientSpace => ‖ψ x‖) :=
        (hψ.integrable_of_hasCompactSupport sψ).norm
      have int₂ : Integrable (fun x : AmbientSpace => ‖φ x‖) :=
        (hφ.integrable_of_hasCompactSupport sφ).norm
      exact (int₁.mul_prod int₂).const_mul B₀
    · refine Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ tsupport ψ ×ˢ tsupport φ
      · have centers := (tendsto_gridCenter w.1).sub (tendsto_gridCenter w.2)
        exact ((WAt w hw).tendsto.comp centers).const_mul (φ w.2 * ψ w.1)
      · have vanish : ∀ δ, gridIntegrand δ φ ψ W w = 0 := fun δ => by
          rw [gridIntegrand, offSupport w hw, zero_mul]
        simp only [vanish, hF, offSupport w hw, zero_mul]
        exact tendsto_const_nhds
  refine gridLimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hpos
  exact (pairedGridSum_eq_integral hpos hφ sφ hψ sψ W).symm
end YangMills.Construction.TwoPoints
end
