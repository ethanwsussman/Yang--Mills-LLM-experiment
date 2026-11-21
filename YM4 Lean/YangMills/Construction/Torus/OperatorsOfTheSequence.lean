import YangMills.Construction.Weighted.FunctionSpaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Weighted
open Set TorusMetric
def avgWeight (L : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => avgWeight L (n + 1) / (((L : ℝ) ^ 2)⁻¹ + avgWeight L (n + 1))
theorem TorusData.bareSite_finite (D : TorusData) : Finite D.BareSite := by
  obtain ⟨k, hk, hside⟩ := D.side_multiple
  have hL : 0 < D.L := by
    have := D.blocking.three_le_factor
    omega
  have hM : 0 < D.blockNumber := hL.trans_le D.le_blockNumber
  have hcount : 0 < 2 * k * (D.blockNumber * D.L ^ D.top) := by positivity
  let N : ℤ := ((2 * k * (D.blockNumber * D.L ^ D.top) : ℕ) : ℤ)
  have hNpos : 0 < N := Int.natCast_pos.2 hcount
  have hperiod : D.side = (N : ℝ) * D.scale 0 := by
    simp only [N, hside, TorusData.scale, pow_zero, one_mul]
    push_cast
    ring
  let φ : (Fin 4 → ℤ) → D.Space := fun m => torusProj D.side fun μ => D.scale 0 * (m μ : ℝ)
  have hreduce : ∀ m : Fin 4 → ℤ, φ m = φ fun μ => m μ % N := by
    intro m
    funext μ
    simp only [φ, torusProj]
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨m μ / N, ?_⟩
    have hsplit : ((m μ : ℤ) : ℝ) = ((m μ % N : ℤ) : ℝ) + (N : ℝ) * ((m μ / N : ℤ) : ℝ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (m μ) N).symm
    rw [zsmul_eq_mul, hperiod, hsplit]
    ring
  have hcover : D.latticeAt (D.scale 0) ⊆ φ '' {m | ∀ μ, m μ ∈ Ico 0 N} := by
    rintro x ⟨m, rfl⟩
    exact ⟨fun μ => m μ % N,
      fun μ => ⟨Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos⟩, (hreduce m).symm⟩
  exact (((Set.Finite.pi' fun _ => finite_Ico 0 N).image φ).subset hcover).to_subtype
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
open Classical in
def layerEval : B.LayerFn →ₗ[ℝ] (D.Space → ℝ) where
  toFun w y := if h : y ∈ B.allSites then w ⟨y, h⟩ else 0
  map_add' w w' := by
    funext y
    by_cases h : y ∈ B.allSites <;> simp [h]
  map_smul' c w := by
    funext y
    by_cases h : y ∈ B.allSites <;> simp [h]
def avgOp : ↥B.bareSpace →ₗ[ℝ] B.LayerFn where
  toFun f y :=
    ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x
  map_add' f g := by
    have := D.bareSite_finite
    funext y
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [finsum_mem_add_distrib (toFinite _), mul_add]
  map_smul' c f := by
    have := D.bareSite_finite
    funext y
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_finsum_mem]
    ring
def avgOpAdjoint : B.LayerFn →ₗ[ℝ] ↥B.bareSpace where
  toFun w :=
    ⟨(D.bareSites (B.stage 0)).indicator fun x => B.layerEval w (B.blockCenter x),
      fun _ hx => indicator_of_notMem hx _⟩
  map_add' w w' := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0) <;> simp [h]
  map_smul' c w := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0) <;> simp [h]
def weightedAvg : Module.End ℝ ↥B.bareSpace where
  toFun f :=
    ⟨(D.bareSites (B.stage 0)).indicator fun x =>
        avgWeight D.L (B.bareLevel x) * (B.bareScale x ^ 2)⁻¹ *
          B.layerEval (B.avgOp f) (B.blockCenter x),
      fun _ hx => indicator_of_notMem hx _⟩
  map_add' f g := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0) <;> simp [h, mul_add]
  map_smul' c f := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0)
    · simp [h]
      ring
    · simp [h]
def IsDirichletLap (T : Module.End ℝ ↥B.bareSpace) : Prop :=
  (∀ f g : ↥B.bareSpace, B.bareInner (T f) g = B.bareInner f (T g)) ∧
    ∀ f : ↥B.bareSpace,
      B.bareInner f (T f) =
        TorusData.bondNorm (TorusData.bondsMeeting (D.bareSites (B.stage 0)))
          (TorusData.bondGrad (f : D.BareSite → ℝ)) ^ 2
def dirichletLap : Module.End ℝ ↥B.bareSpace :=
  Classical.epsilon B.IsDirichletLap
def weightedLap : Module.End ℝ ↥B.bareSpace :=
  B.dirichletLap + B.weightedAvg
def greenOp : Module.End ℝ ↥B.bareSpace := Ring.inverse B.weightedLap
def avgGreenSq : Module.End ℝ B.LayerFn :=
  B.avgOp ∘ₗ (B.greenOp * B.greenOp) ∘ₗ B.avgOpAdjoint
def avgProj : Module.End ℝ ↥B.bareSpace :=
  B.greenOp ∘ₗ B.avgOpAdjoint ∘ₗ Ring.inverse B.avgGreenSq ∘ₗ
    B.avgOp ∘ₗ B.greenOp
def complProj : Module.End ℝ ↥B.bareSpace := 1 - B.avgProj
end SeparatedChain
end Weighted
end YangMills.Construction
