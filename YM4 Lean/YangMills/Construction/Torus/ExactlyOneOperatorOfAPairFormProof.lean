import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePairProof
import YangMills.Construction.Torus.ExactlyOneOperatorOfAPairForm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace AdmissibleOp
instance instFintypeBareSite (D : TorusData) : Fintype D.BareSite :=
  @Fintype.ofFinite _ D.bareSite_finite
theorem bond_finite (D : TorusData) : Finite D.Bond := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bond_finite <;> assumption
instance instFintypeBond (D : TorusData) : Fintype D.Bond :=
  @Fintype.ofFinite _ (bond_finite D)
theorem finsum_mem_eq_sum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ x ∈ s, f x = ∑ x, s.indicator f x := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
variable {D : TorusData} (C : SeparatedChain D)
theorem allSites_finite : C.allSites.Finite := by
  have := D.bareSite_finite
  have hsub : C.allSites ⊆ Subtype.val '' (univ : Set D.BareSite) := by
    intro y hy
    simp only [SeparatedChain.allSites, mem_iUnion] at hy
    obtain ⟨n, _, hy⟩ := hy
    obtain ⟨k, hk⟩ := hy.1
    refine ⟨⟨y, ⟨fun μ => (D.L : ℤ) ^ n * k μ, ?_⟩⟩, trivial, rfl⟩
    rw [hk]
    congr 1
    funext μ
    simp only [TorusData.scale]
    push_cast
    ring
  exact (toFinite _).subset hsub
open Classical in
theorem bareInner_eq_sum (u v : D.BareSite → ℝ) :
    C.bareInner u v = D.scale 0 ^ 4 *
      ∑ x ∈ Finset.univ.filter (· ∈ D.bareSites (C.stage 0)), u x * v x := by
  unfold SeparatedChain.bareInner
  rw [finsum_mem_eq_sum_indicator, Finset.sum_filter]
  congr 1
theorem bareInner_congr {u v u' v' : D.BareSite → ℝ}
    (h : ∀ x ∈ D.bareSites (C.stage 0), u x * v x = u' x * v' x) :
    C.bareInner u v = C.bareInner u' v' := by
  unfold SeparatedChain.bareInner
  congr 1
  exact finsum_mem_congr rfl h
theorem bareInner_comm (u v : D.BareSite → ℝ) : C.bareInner u v = C.bareInner v u := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_add_left (u u' v : D.BareSite → ℝ) :
    C.bareInner (u + u') v = C.bareInner u v + C.bareInner u' v := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_add_left <;> assumption
theorem bareInner_smul_left (c : ℝ) (u v : D.BareSite → ℝ) :
    C.bareInner (c • u) v = c * C.bareInner u v := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_smul_left <;> assumption
theorem bareInner_sub_right (w u u' : D.BareSite → ℝ) :
    C.bareInner w (fun x => u x - u' x) = C.bareInner w u - C.bareInner w u' := by
  simp only [bareInner_eq_sum, mul_sub, Finset.sum_sub_distrib]
theorem eq_zero_of_bareInner_self {u : D.BareSite → ℝ}
    (hu : ∀ x, x ∉ D.bareSites (C.stage 0) → u x = 0) (h : C.bareInner u u = 0) : u = 0 := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.eq_zero_of_bareInner_self <;> assumption
theorem bondGrad_add (u u' : D.BareSite → ℝ) (e : D.Bond) :
    TorusData.bondGrad (u + u') e = TorusData.bondGrad u e + TorusData.bondGrad u' e := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bondGrad_add <;> assumption
theorem bondGrad_smul (c : ℝ) (u : D.BareSite → ℝ) (e : D.Bond) :
    TorusData.bondGrad (c • u) e = c * TorusData.bondGrad u e := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bondGrad_smul <;> assumption
theorem sitesIn_finite (W : Set D.Space) : (C.sitesIn W).Finite :=
  (allSites_finite C).subset fun _ hy => hy.1
theorem admissibleForm_eq_sum (W : Set D.Space) (𝔟 : Set D.Bond) (u v : ↥(C.bareSpaceOn W)) :
    C.admissibleForm W 𝔟 u v =
      D.scale 0 ^ 4 * ∑ e ∈ (toFinite 𝔟).toFinset,
          TorusData.bondGrad (u : D.BareSite → ℝ) e * TorusData.bondGrad (v : D.BareSite → ℝ) e +
        ∑ y ∈ (sitesIn_finite C W).toFinset,
          avgWeight D.L (C.level y) * C.siteScale y ^ 2 *
            (C.layerEval (C.avgOp (C.bareSpaceOnIncl W u)) y *
              C.layerEval (C.avgOp (C.bareSpaceOnIncl W v)) y) := by
  unfold SeparatedChain.admissibleForm
  rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite 𝔟),
    finsum_mem_eq_finite_toFinset_sum _ (sitesIn_finite C W)]
theorem admissibleForm_comm (W : Set D.Space) (𝔟 : Set D.Bond) (u v : ↥(C.bareSpaceOn W)) :
    C.admissibleForm W 𝔟 u v = C.admissibleForm W 𝔟 v u := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.admissibleForm_comm <;> assumption
theorem admissibleForm_add_left (W : Set D.Space) (𝔟 : Set D.Bond)
    (u u' v : ↥(C.bareSpaceOn W)) :
    C.admissibleForm W 𝔟 (u + u') v = C.admissibleForm W 𝔟 u v + C.admissibleForm W 𝔟 u' v := by
  simp only [admissibleForm_eq_sum C, map_add, Submodule.coe_add, bondGrad_add, add_mul,
    Finset.sum_add_distrib, mul_add, Pi.add_apply]
  ring
theorem admissibleForm_smul_left (W : Set D.Space) (𝔟 : Set D.Bond) (c : ℝ)
    (u v : ↥(C.bareSpaceOn W)) :
    C.admissibleForm W 𝔟 (c • u) v = c * C.admissibleForm W 𝔟 u v := by
  simp only [admissibleForm_eq_sum C, map_smul, Submodule.coe_smul, bondGrad_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_add]
  congr 1
  · rw [mul_left_comm, Finset.mul_sum (a := c)]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
def admissibleBilin (W : Set D.Space) (𝔟 : Set D.Bond) :
    LinearMap.BilinForm ℝ ↥(C.bareSpaceOn W) :=
  LinearMap.mk₂ ℝ (C.admissibleForm W 𝔟) (admissibleForm_add_left C W 𝔟)
    (fun c u v => by rw [admissibleForm_smul_left C, smul_eq_mul])
    (fun u v v' => by
      rw [admissibleForm_comm C W 𝔟 u, admissibleForm_add_left C, admissibleForm_comm C W 𝔟 v,
        admissibleForm_comm C W 𝔟 v'])
    (fun c u v => by
      rw [admissibleForm_comm C W 𝔟 u, admissibleForm_smul_left C, admissibleForm_comm C W 𝔟 v,
        smul_eq_mul])
def innerBilin (W : Set D.Space) : LinearMap.BilinForm ℝ ↥(C.bareSpaceOn W) :=
  LinearMap.mk₂ ℝ (fun u v => C.bareInner u v)
    (fun u u' v => by
      simpa only [Submodule.coe_add] using bareInner_add_left C u u' v)
    (fun c u v => by
      simp only [Submodule.coe_smul, smul_eq_mul]
      exact bareInner_smul_left C c u v)
    (fun u v v' => by
      simp only [Submodule.coe_add]
      rw [bareInner_comm, bareInner_add_left, bareInner_comm C v, bareInner_comm C v'])
    (fun c u v => by
      simp only [Submodule.coe_smul]
      rw [bareInner_comm, bareInner_smul_left, bareInner_comm C v, smul_eq_mul])
theorem innerBilin_nondegenerate (W : Set D.Space) : (innerBilin C W).Nondegenerate := by
  have key : ∀ u : ↥(C.bareSpaceOn W), C.bareInner u u = 0 → u = 0 := fun u h =>
    Subtype.ext (eq_zero_of_bareInner_self C u.2.1 h)
  exact ⟨fun u h => key u (h u), fun u h => key u (h u)⟩
theorem exists_admissibleFormOp (W : Set D.Space) (𝔟 : Set D.Bond) :
    ∃ T, C.IsAdmissibleFormOp W 𝔟 T := by
  have := D.bareSite_finite
  have hT : ∀ u v : ↥(C.bareSpaceOn W), C.bareInner
      (LinearMap.BilinForm.symmCompOfNondegenerate (admissibleBilin C W 𝔟) (innerBilin C W)
        (innerBilin_nondegenerate C W) u : ↥(C.bareSpaceOn W)) v =
      C.admissibleForm W 𝔟 u v := fun u v =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (admissibleBilin C W 𝔟)
      (innerBilin_nondegenerate C W) v u
  refine ⟨LinearMap.BilinForm.symmCompOfNondegenerate (admissibleBilin C W 𝔟) (innerBilin C W)
    (innerBilin_nondegenerate C W), fun u v => ?_, fun u v => ?_⟩
  · rw [hT, bareInner_comm, hT, admissibleForm_comm]
  · rw [bareInner_comm, hT, admissibleForm_comm]
theorem admissibleFormOp_unique {W : Set D.Space} {𝔟 : Set D.Bond}
    {T T' : Module.End ℝ ↥(C.bareSpaceOn W)} (hT : C.IsAdmissibleFormOp W 𝔟 T)
    (hT' : C.IsAdmissibleFormOp W 𝔟 T') : T = T' := by
  refine LinearMap.ext fun v => ?_
  have h1 : C.bareInner (T v - T' v : ↥(C.bareSpaceOn W)) (T v) =
      C.bareInner (T v - T' v : ↥(C.bareSpaceOn W)) (T' v) :=
    (hT.2 _ v).trans (hT'.2 _ v).symm
  have h2 := bareInner_sub_right C (T v - T' v : ↥(C.bareSpaceOn W)) (T v) (T' v)
  rw [h1, sub_self] at h2
  exact sub_eq_zero.1 (Subtype.ext (eq_zero_of_bareInner_self C (T v - T' v).2.1 h2))
end AdmissibleOp
theorem AdmissibleOp.statement_holds : UniqueAdmissibleFormOpStatement := by
  intro D C W 𝔟 _
  obtain ⟨T, hT⟩ := exists_admissibleFormOp C W 𝔟
  exact ⟨T, hT, fun T' hT' => admissibleFormOp_unique C hT' hT⟩
end YangMills.Construction.Weighted
