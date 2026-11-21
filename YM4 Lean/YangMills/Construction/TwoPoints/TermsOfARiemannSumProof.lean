import YangMills.Construction.TwoPoints.DoubleRiemannSumsTendToTheDoubleIntegralProof
import YangMills.Construction.TwoPoints.TermsOfARiemannSum
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace RiemannSumTermProperties
theorem measurableSet_gridCube (δ : ℝ) (j : Fin 4 → ℤ) : MeasurableSet (gridCube δ j) := by apply _root_.YangMills.Construction.TwoPoints.PairedGridSumLimit.measurableSet_gridCube <;> assumption
theorem euclidNorm_sub_gridCenter_le {δ : ℝ} (hδ : 0 < δ) {j : Fin 4 → ℤ} {z : AmbientSpace}
    (hz : z ∈ gridCube δ j) : euclidNorm (z - gridCenter δ j) ≤ δ := by
  refine Real.sqrt_le_iff.2 ⟨hδ.le, ?_⟩
  have hcoord : ∀ μ, (z - gridCenter δ j) μ ^ 2 ≤ δ ^ 2 / 4 := by
    intro μ
    obtain ⟨hlo, hhi⟩ := hz μ
    have hval : (z - gridCenter δ j) μ = z μ - δ * ((j μ : ℝ) + 1 / 2) := rfl
    have hmid : δ * ((j μ : ℝ) + 1 / 2) = δ * (j μ : ℝ) + δ / 2 := by ring
    have htop : δ * ((j μ : ℝ) + 1) = δ * (j μ : ℝ) + δ := by ring
    rw [hval, hmid]
    rw [htop] at hhi
    have hsq := sq_le_sq' (a := z μ - (δ * (j μ : ℝ) + δ / 2)) (b := δ / 2) (by linarith)
      (by linarith)
    nlinarith
  calc ∑ μ, (z - gridCenter δ j) μ ^ 2 ≤ ∑ _μ : Fin 4, δ ^ 2 / 4 :=
        Finset.sum_le_sum fun μ _ => hcoord μ
    _ = δ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem exists_mem_tsupport_of_setIntegralOf_ne_zero {Q : Set AmbientSpace}
    {k : AmbientSpace → ℂ} (hQ : setIntegralOf Q k ≠ 0) : ∃ z ∈ tsupport k, z ∈ Q := by
  by_contra hnone
  apply hQ
  show ∫ x in Q, k x = 0
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  by_contra hkx
  exact hnone ⟨x, subset_tsupport k hkx, hx⟩
theorem finite_setOf_gridCube_meets {δ : ℝ} (hδ : 0 < δ) {C : Set AmbientSpace}
    (hC : IsCompact C) : {j : Fin 4 → ℤ | ∃ z ∈ C, z ∈ gridCube δ j}.Finite := by apply _root_.YangMills.Construction.TwoPoints.PairedGridSumLimit.finite_setOf_gridCube_meets <;> assumption
theorem translateFun_mem_compactC1Complex (v : AmbientSpace) {φ : AmbientSpace → ℂ}
    (hφ : φ ∈ compactC1Complex) : translateFun v φ ∈ compactC1Complex := by
  have hφ' : ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ univ := hφ
  have hts : tsupport (translateFun v φ) = (Homeomorph.subRight v) ⁻¹' tsupport φ :=
    tsupport_comp_eq_preimage φ (Homeomorph.subRight v)
  show ContDiff ℝ 1 (translateFun v φ) ∧ IsCompact (tsupport (translateFun v φ)) ∧
    tsupport (translateFun v φ) ⊆ univ
  refine ⟨hφ'.1.comp (contDiff_id.sub contDiff_const), ?_, subset_univ _⟩
  rw [hts]
  exact (Homeomorph.subRight v).isCompact_preimage.2 hφ'.2.1
theorem isCompact_euclidClosedBall_zero {δ : ℝ} (hδ : 0 ≤ δ) :
    IsCompact (euclidClosedBall (0 : AmbientSpace) δ) := by
  have hclosed : IsClosed (euclidClosedBall (0 : AmbientSpace) δ) := by
    have hcont : Continuous fun y : AmbientSpace => euclidNorm (y - 0) := by
      unfold euclidNorm
      fun_prop
    exact isClosed_le hcont continuous_const
  refine (isCompact_closedBall (0 : AmbientSpace) δ).of_isClosed_subset hclosed fun y hy => ?_
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg hδ).2 fun μ => ?_
  have hy' : Real.sqrt (∑ ν, (y - 0) ν ^ 2) ≤ δ := hy
  have hsingle : y μ ^ 2 ≤ ∑ ν, (y - 0) ν ^ 2 := by
    simpa using Finset.single_le_sum (f := fun ν => y ν ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ μ)
  exact (Real.abs_le_sqrt hsingle).trans hy'
theorem isCompact_minkowskiSum {A B : Set AmbientSpace} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (minkowskiSum A B) := by
  have himage : minkowskiSum A B = (fun p : AmbientSpace × AmbientSpace => p.1 + p.2) '' (A ×ˢ B) := by
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  rw [himage]
  exact (hA.prod hB).image continuous_add
theorem holds : Statement := by
  intro k hk φ hφ δ hδ
  have hk' : ContDiff ℝ 0 k ∧ IsCompact (tsupport k) ∧ tsupport k ⊆ univ := hk
  have hφ' : ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ univ := hφ
  have hfin : {j : Fin 4 → ℤ |
      setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ ≠ 0}.Finite := by
    refine (finite_setOf_gridCube_meets hδ hk'.2.1).subset fun j hj => ?_
    apply exists_mem_tsupport_of_setIntegralOf_ne_zero
    intro hzero
    apply hj
    rw [hzero, zero_smul]
  have hsum : cubeRiemannSum δ k φ = ∑ j ∈ hfin.toFinset,
      setIntegralOf (gridCube δ j) k • translateFun (gridCenter δ j) φ :=
    finsum_eq_sum_of_support_subset _ fun j hj => Finset.mem_coe.2 (hfin.mem_toFinset.2 hj)
  refine ⟨measurableSet_gridCube δ, fun j z hz => euclidNorm_sub_gridCenter_le hδ hz,
    fun j hj => exists_mem_tsupport_of_setIntegralOf_ne_zero hj, hfin, ?_, ?_⟩
  · rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (translateFun_mem_compactC1Complex _ hφ)
  · refine closure_minimal ?_ (isCompact_minkowskiSum (isCompact_minkowskiSum hk'.2.1
      (isCompact_euclidClosedBall_zero hδ.le)) hφ'.2.1).isClosed
    intro x hx
    have hne : cubeRiemannSum δ k φ x ≠ 0 := hx
    rw [hsum, Finset.sum_apply] at hne
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hcoef : setIntegralOf (gridCube δ j) k ≠ 0 := by
      intro hzero
      apply hj
      simp [hzero]
    have hφx : φ (x - gridCenter δ j) ≠ 0 := by
      intro hzero
      apply hj
      simp [translateFun, hzero]
    obtain ⟨z, hzk, hz⟩ := exists_mem_tsupport_of_setIntegralOf_ne_zero hcoef
    refine ⟨z + (gridCenter δ j - z), ⟨z, hzk, gridCenter δ j - z, ?_, rfl⟩,
      x - gridCenter δ j, subset_tsupport φ hφx, ?_⟩
    · have hdist := euclidNorm_sub_gridCenter_le hδ hz
      show euclidNorm (gridCenter δ j - z - 0) ≤ δ
      rw [sub_zero]
      have hsymm : euclidNorm (gridCenter δ j - z) = euclidNorm (z - gridCenter δ j) := by
        unfold euclidNorm
        congr 1
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [Pi.sub_apply]
        ring
      rwa [hsymm]
    · abel
end RiemannSumTermProperties
end YangMills.Construction.TwoPoints
end
