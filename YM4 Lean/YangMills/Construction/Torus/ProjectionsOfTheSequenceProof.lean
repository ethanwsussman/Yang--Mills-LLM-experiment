import YangMills.Construction.Torus.BoundOnTheScaledRemainderBlocksProof
import YangMills.Construction.Torus.KernelCalculusOnTheLayersProof
import YangMills.Construction.Torus.LowerBoundOnTheAveragedGreenSquareProof
import YangMills.Construction.Torus.PointwiseBoundsOnTheGreenOperator
import YangMills.Construction.Torus.ProjectionsOfTheSequence
import YangMills.Construction.Torus.TestFunctionsOfTheBlocksProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
open TorusMetric
namespace ProjectionProof
namespace ProjAlg
variable {H K : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K]
variable {G : Module.End ℝ H} {Q : H →ₗ[ℝ] K} {Qt : K →ₗ[ℝ] H} {Ti : Module.End ℝ K}
end ProjAlg
open SeparatedChain
variable {D : TorusData}
theorem scale_zero_pos (D : TorusData) : 0 < D.scale 0 := by apply _root_.YangMills.Construction.Weighted.BlockBumps.scale_zero_pos <;> assumption
theorem three_le_blockFactor (D : TorusData) : 3 ≤ D.L := D.blocking.three_le_factor
theorem supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
theorem torusSupNorm_proj_le (S : ℝ) (v : Fin 4 → ℝ) :
    torusSupNorm (torusProj S v) ≤ supNormVec v := by
  refine csInf_le ⟨0, ?_⟩ ⟨v, rfl, rfl⟩
  rintro _ ⟨w, _, rfl⟩
  exact supNormVec_nonneg w
theorem supNormVec_single_le {ξ : ℝ} (hξ : 0 ≤ ξ) (μ : Fin 4) :
    supNormVec (Pi.single μ ξ) ≤ ξ := by
  refine Finset.sup'_le _ _ fun ν _ => ?_
  by_cases h : ν = μ
  · subst h
    simp [abs_of_nonneg hξ]
  · simp [Pi.single_eq_of_ne h, hξ]
theorem torusProj_neg (S : ℝ) (v : Fin 4 → ℝ) : torusProj S (-v) = -torusProj S v := by
  funext μ
  simp [torusProj]
theorem adjacent_symm {x x' : D.BareSite} (h : TorusData.Adjacent x x') :
    TorusData.Adjacent x' x := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqLowerBound.adjacent_symm <;> assumption
theorem level_eq (B : SeparatedChain D)
    (h3 : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) {n : ℕ} {y : D.Space}
    (hy : y ∈ B.layerSites n) : B.level y = n := by
  obtain ⟨-, -, -, h4, -⟩ := h3 n y hy
  have hs : B.siteScale y = D.scale (B.level y) := rfl
  rw [hs] at h4
  have hq : D.scale (B.level y) / D.scale 0 = (D.L : ℝ) ^ B.level y := by
    have := D.bareSpacing_pos.ne'
    simp only [TorusData.scale, pow_zero, one_mul]
    field_simp
  rw [hq, ← pow_mul] at h4
  have h5 : D.L ^ (n * 4) = D.L ^ (B.level y * 4) := by exact_mod_cast h4
  have h6 := Nat.pow_right_injective (by have := three_le_blockFactor D; omega : 2 ≤ D.L) h5
  omega
theorem bareInner_eq_sum [Fintype D.BareSite] (B : SeparatedChain D) (a b : D.BareSite → ℝ)
    (hb : ∀ x, x ∉ D.bareSites (B.stage 0) → b x = 0) :
    B.bareInner a b = D.scale 0 ^ 4 * ∑ x, a x * b x := by
  rw [bareInner, ← finsum_eq_sum_of_fintype, ← finsum_mem_univ (fun x => a x * b x)]
  congr 1
  apply finsum_mem_inter_support_eq
  ext x
  simp only [mem_inter_iff, Function.mem_support, mem_univ, true_and, and_iff_right_iff_imp]
  intro h
  by_contra hx
  exact h (by rw [hb x hx, mul_zero])
theorem bareInner_comm (B : SeparatedChain D) (a b : D.BareSite → ℝ) :
    B.bareInner a b = B.bareInner b a := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem layerInner_comm (B : SeparatedChain D) (w w' : B.LayerFn) :
    B.layerInner w w' = B.layerInner w' w := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.layerInner_comm <;> assumption
theorem bareInner_sub_left (B : SeparatedChain D) (a a' : D.BareSite → ℝ)
    (b : ↥B.bareSpace) :
    B.bareInner (a - a') b = B.bareInner a b - B.bareInner a' b := by
  classical
  have := D.bareSite_finite
  let _ : Fintype D.BareSite := Fintype.ofFinite _
  rw [bareInner_eq_sum B _ _ b.2, bareInner_eq_sum B _ _ b.2, bareInner_eq_sum B _ _ b.2,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Pi.sub_apply]
  ring
theorem mem_layerSites_zero (B : SeparatedChain D) {x : D.BareSite}
    (h : x ∈ D.bareSites (B.stage 0)) (hx : x ∉ D.bareSites (B.stage 1)) :
    (x : D.Space) ∈ B.layerSites 0 := by
  refine ⟨x.2, ?_⟩
  by_cases htop : 0 < D.top
  · simp only [layer, htop, if_true]
    exact subset_closure ⟨h, hx⟩
  · have h0 : D.top = 0 := by omega
    simp only [layer, h0, lt_irrefl, if_false, if_true]
    exact h
theorem mem_allSites_of_mem_layerSites (B : SeparatedChain D) {n : ℕ} {y : D.Space}
    (hn : n ≤ D.top) (hy : y ∈ B.layerSites n) : y ∈ B.allSites := by
  simp only [allSites, mem_iUnion, Finset.mem_range, exists_prop]
  exact ⟨n, by omega, hy⟩
theorem avgKernel_vanishes (B : SeparatedChain D) (hav : B.AvgAndAdjointFormulas)
    (f : ↥B.bareSpace) (hf : f ∈ B.avgKernel) (x : D.BareSite)
    (hx : x ∉ D.bareSites (B.stage 1)) : (f : D.BareSite → ℝ) x = 0 := by
  by_cases h : x ∈ D.bareSites (B.stage 0)
  · have hlay : (x : D.Space) ∈ B.layerSites 0 := mem_layerSites_zero B h hx
    have hall : (x : D.Space) ∈ B.allSites :=
      mem_allSites_of_mem_layerSites B (Nat.zero_le _) hlay
    rw [← hav.2.1 f ⟨x, hall⟩ x hlay rfl]
    have hf' : B.avgOp f = 0 := hf
    rw [hf']
    rfl
  · exact f.2 x h
theorem allSites_finite (B : SeparatedChain D)
    (hb : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) : Finite ↥B.allSites := by
  have := D.bareSite_finite
  refine Set.Finite.to_subtype ((Set.finite_range (Subtype.val : D.BareSite → D.Space)).subset ?_)
  intro y hy
  simp only [allSites, mem_iUnion, Finset.mem_range, exists_prop] at hy
  obtain ⟨n, -, hyn⟩ := hy
  obtain ⟨-, -, -, -, ⟨x, -, rfl⟩, -⟩ := hb n y hyn
  exact ⟨x, rfl⟩
def blockFn (B : SeparatedChain D) (hpart : B.BlocksPartition) (y : ↥B.allSites) :
    ↥B.bareSpace :=
  ⟨B.blockIndicator y, fun _ hx => indicator_of_notMem
    (fun hxy => hx (hpart.2 ▸ mem_iUnion₂.2 ⟨y, y.2, hxy⟩)) _⟩
theorem avgOpAdjoint_eq_sum (B : SeparatedChain D) [Fintype ↥B.allSites]
    (hav : B.AvgAndAdjointFormulas) (hpart : B.BlocksPartition)
    (w : B.LayerFn) : B.avgOpAdjoint w = ∑ y, w y • blockFn B hpart y := by
  apply Subtype.ext
  have h := hav.2.2.2.2.1 w
  rw [h]
  funext x
  rw [finsum_eq_sum_of_fintype]
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rfl
theorem abs_double_sum_le {ι : Type*} [Fintype ι] (t e₂ : ι → ι → ℝ) (e₁ : ι → ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c) (he₁ : ∀ i, 0 ≤ e₁ i) (ht : ∀ i j, |t i j| ≤ C * (e₁ i * e₂ i j))
    (hs₂ : ∀ i, ∑ j, e₂ i j ≤ c) (hs₁ : ∑ i, e₁ i ≤ c) : |∑ i, ∑ j, t i j| ≤ C * c ^ 2 := by
  calc |∑ i, ∑ j, t i j| ≤ ∑ i, ∑ j, |t i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, C * (e₁ i * e₂ i j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = ∑ i, C * e₁ i * ∑ j, e₂ i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ∑ i, C * e₁ i * c :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hs₂ i) (mul_nonneg hC (he₁ i))
    _ = C * (∑ i, e₁ i) * c := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * c * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs₁ hC) hc
    _ = C * c ^ 2 := by ring
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem siteScale_pos (B : SeparatedChain D) (y : D.Space) : 0 < B.siteScale y := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.siteScale_pos <;> assumption
theorem block_subset_bareSites (B : SeparatedChain D) (hpart : B.BlocksPartition)
    (y : ↥B.allSites) : B.block y ⊆ D.bareSites (B.stage 0) := fun _ hx =>
  hpart.2 ▸ mem_iUnion₂.2 ⟨y, y.2, hx⟩
end ProjectionProof
end YangMills.Construction.Weighted
