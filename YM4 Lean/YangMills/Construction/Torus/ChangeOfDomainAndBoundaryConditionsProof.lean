import YangMills.Construction.Torus.BoundsOnTheAveragedSquareProof
import YangMills.Construction.Torus.ExactlyOneOperatorOfAPairFormProof
import YangMills.Construction.Torus.OperatorsOfAnAdmissiblePair
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace DomainChange
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
instance instFintypeBareSite (D : TorusData) : Fintype D.BareSite :=
  @Fintype.ofFinite _ D.bareSite_finite
theorem bond_finite (D : TorusData) : Finite D.Bond := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bond_finite <;> assumption
instance instFintypeBond (D : TorusData) : Fintype D.Bond :=
  @Fintype.ofFinite _ (bond_finite D)
theorem finsum_mem_eq_sum_indicator {α : Type*} [Fintype α] (s : Set α) (f : α → ℝ) :
    ∑ᶠ x ∈ s, f x = ∑ x, s.indicator f x := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
def bondDir {D : TorusData} (b : D.Bond) : Fin 4 := Classical.choose b.isPositive
theorem bondDir_spec {D : TorusData} (b : D.Bond) :
    (b.target : D.Space) - (b.source : D.Space) = D.unitStep (bondDir b) :=
  Classical.choose_spec b.isPositive
theorem source_dir_injective {D : TorusData} :
    Function.Injective fun b : D.Bond => (b.source, bondDir b) := by
  intro b b' h
  have h1 : b.source = b'.source := congrArg Prod.fst h
  have h2 : bondDir b = bondDir b' := congrArg Prod.snd h
  refine TorusData.Bond.ext h1 (Subtype.ext ?_)
  have e1 := bondDir_spec b
  have e2 := bondDir_spec b'
  rw [← h2, ← h1] at e2
  have := e1.trans e2.symm
  exact sub_left_injective this
theorem target_dir_injective {D : TorusData} :
    Function.Injective fun b : D.Bond => (b.target, bondDir b) := by
  intro b b' h
  have h1 : b.target = b'.target := congrArg Prod.fst h
  have h2 : bondDir b = bondDir b' := congrArg Prod.snd h
  refine TorusData.Bond.ext (Subtype.ext ?_) h1
  have e1 := bondDir_spec b
  have e2 := bondDir_spec b'
  rw [← h2, ← h1] at e2
  have := e1.trans e2.symm
  exact sub_right_injective this
end DomainChange
namespace DomainChange
variable {D : TorusData} (B : SeparatedChain D)
theorem bondNorm_mono {S S' : Set D.Bond} (h : S ⊆ S') (q : D.Bond → ℝ) :
    TorusData.bondNorm S q ≤ TorusData.bondNorm S' q := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bondNorm_mono <;> assumption
end DomainChange
namespace DomainChange
variable {D : TorusData} (B : SeparatedChain D)
theorem blockCenter_spec (hc : B.SiteCubesTile) {x : D.BareSite}
    (hx : x ∈ D.bareSites (B.stage 0)) :
    B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
  obtain ⟨y, hy, hint, -⟩ := hc.2.2 x hx
  have h : ∃ y, y ∈ B.allSites ∧ x ∈ B.block y :=
    ⟨y, hy, (interior_subset hint : (x : D.Space) ∈ B.siteCube y)⟩
  exact Classical.epsilon_spec h
theorem block_subset_bareSites (hb : B.BlocksPartition) {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by
  intro x hx
  rw [← hb.2]
  exact mem_iUnion₂.2 ⟨y, hy, hx⟩
theorem allSites_finite (hs : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) :
    B.allSites.Finite := by apply _root_.YangMills.Construction.Weighted.AvgGreenSqBounds.allSites_finite <;> assumption
open Classical in
theorem bareInner_eq_sum (f f' : D.BareSite → ℝ) :
    B.bareInner f f' = D.scale 0 ^ 4 *
      ∑ x ∈ Finset.univ.filter (· ∈ D.bareSites (B.stage 0)), f x * f' x := by apply _root_.YangMills.Construction.Weighted.AdmissibleOp.bareInner_eq_sum <;> assumption
theorem bareInner_congr {f f' g g' : D.BareSite → ℝ}
    (h : ∀ x ∈ D.bareSites (B.stage 0), f x * f' x = g x * g' x) :
    B.bareInner f f' = B.bareInner g g' := by apply _root_.YangMills.Construction.Weighted.AdmissibleOp.bareInner_congr <;> assumption
theorem bareInner_comm (f f' : D.BareSite → ℝ) : B.bareInner f f' = B.bareInner f' f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_sub_right (g f f' : D.BareSite → ℝ) :
    B.bareInner g (fun x => f x - f' x) = B.bareInner g f - B.bareInner g f' := by
  simp only [bareInner_eq_sum, mul_sub, Finset.sum_sub_distrib]
theorem admissibleForm_comm (W : Set D.Space) (𝔟 : Set D.Bond) (f f' : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 f f' = B.admissibleForm W 𝔟 f' f := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.admissibleForm_comm <;> assumption
theorem exists_admissibleFormOp (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond) :
    ∃ T, B.IsAdmissibleFormOp W 𝔟 T := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.exists_admissibleFormOp <;> assumption
theorem admissibleOp_spec (hfin : B.allSites.Finite) (W : Set D.Space) (𝔟 : Set D.Bond) :
    B.IsAdmissibleFormOp W 𝔟 (B.admissibleOp W 𝔟) :=
  Classical.epsilon_spec (exists_admissibleFormOp B hfin W 𝔟)
theorem admissibleForm_green_right (hfin : B.allSites.Finite) {W : Set D.Space}
    {𝔟 : Set D.Bond} (hu : IsUnit (B.admissibleOp W 𝔟)) (v h : ↥(B.bareSpaceOn W)) :
    B.admissibleForm W 𝔟 v (B.admissibleGreen W 𝔟 h) = B.bareInner v h := by
  rw [← (admissibleOp_spec B hfin W 𝔟).2]
  have : B.admissibleOp W 𝔟 * B.admissibleGreen W 𝔟 = 1 := Ring.mul_inverse_cancel _ hu
  have h1 : B.admissibleOp W 𝔟 (B.admissibleGreen W 𝔟 h) = h := by
    rw [← Module.End.mul_apply, this, Module.End.one_apply]
  rw [h1]
def mulOp (m : D.BareSite → ℝ) : ↥B.bareSpace →ₗ[ℝ] ↥B.bareSpace where
  toFun f := ⟨fun x => m x * (f : D.BareSite → ℝ) x, fun x hx => by
    have h : (f : D.BareSite → ℝ) x = 0 := f.2 x hx
    simp [h]⟩
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem mulOp_apply (m : D.BareSite → ℝ) (f : ↥B.bareSpace) (x : D.BareSite) :
    (mulOp B m f : D.BareSite → ℝ) x = m x * (f : D.BareSite → ℝ) x := rfl
theorem weightedDistance_comm (x x' : D.Space) :
    B.weightedDistance x x' = B.weightedDistance x' x := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedDistance_comm <;> assumption
theorem siteNorm_le_mul {E : Set D.BareSite} {f g : D.BareSite → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ x ∈ E, |f x| ≤ τ * |g x|) : TorusData.siteNorm E f ≤ τ * TorusData.siteNorm E g := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.siteNorm_le_mul <;> assumption
end DomainChange
namespace DomainChange
variable {D : TorusData} (B : SeparatedChain D)
theorem avgWeight_bounds (hW : Dirichlet.WeightRecursionBounds) (L : ℕ) (h3 : 3 ≤ L)
    (hodd : Odd L) (n : ℕ) : 0 < avgWeight L n ∧ avgWeight L n ≤ 1 := by
  have hrec : ∀ n : ℕ, 1 ≤ n → avgWeight L (n + 1) =
      avgWeight L n / ((L : ℝ) ^ (-2 : ℤ) + avgWeight L n) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have : ((L : ℝ) ^ (-2 : ℤ)) = ((L : ℝ) ^ 2)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [this]
    rfl
  have h := (hW L h3 hodd (avgWeight L) rfl rfl hrec).2 n
  refine ⟨lt_of_le_of_lt ?_ h.1, h.2⟩
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast h3
  have h1 : (L : ℝ) ^ (-2 : ℤ) = ((L : ℝ) ^ 2)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [h1, sub_nonneg]
  exact inv_le_one_of_one_le₀ (by nlinarith)
theorem layerEval_of_mem {y : D.Space} (hy : y ∈ B.allSites) (w : B.LayerFn) :
    B.layerEval w y = w ⟨y, hy⟩ := dif_pos hy
end DomainChange
namespace DomainChange
variable {D : TorusData} (B : SeparatedChain D)
end DomainChange
end YangMills.Construction.Weighted
