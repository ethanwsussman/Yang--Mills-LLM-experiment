import YangMills.Construction.DirichletOperator.BoundsOfTheLocalOperatorsOnEnlargedCubesProof
import YangMills.Construction.DirichletOperator.FactsOfTheCellsOfACube
import YangMills.Construction.DirichletOperator.SourcesOfATermOfACubeAtTheCells
import YangMills.Construction.DirichletOperator.TermOfACubeInNorm
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
open YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (torusSetting levelSpacing)
open YangMills.Construction.CubeOperators (RegularityConstants IsCubeScale)
open YangMills.Construction.ApproxInverseScales
open YangMills.Construction.CellSources (termAtCell CellDecomposition)
noncomputable section
namespace YangMills.Construction.CubeTermNorms
structure IsSubadditiveNorm {V : Type} [AddCommMonoid V] (N : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ N v
  map_zero_le : N 0 ≤ 0
  map_add_le : ∀ v w, N (v + w) ≤ N v + N w
theorem IsSubadditiveNorm.comp {V W : Type} [AddCommMonoid V] [AddCommMonoid W] {N : W → ℝ}
    (h : IsSubadditiveNorm N) {T : V → W} (h₀ : T 0 = 0) (ha : ∀ v w, T (v + w) = T v + T w) :
    IsSubadditiveNorm fun v => N (T v) :=
  ⟨fun _ => h.nonneg _, by simpa [h₀] using h.map_zero_le, fun v w => by
    rw [ha]
    exact h.map_add_le _ _⟩
variable {𝒯 : NestedRegions}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem nablaOne_add (A B : 𝒯.FineBond → ℝ) : nablaOne (A + B) = nablaOne A + nablaOne B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.nablaOne_add <;> assumption
theorem nablaTwo_add (J K : 𝒯.Tensor 1) :
    nablaTwo (J + K) = nablaTwo J + nablaTwo K := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.nablaTwo_add <;> assumption
theorem ltwoBond_eq [Fintype 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) :
    ltwoBond f = √(∑ b, (𝒯.ξ ^ 2 * f b) * (𝒯.ξ ^ 2 * f b)) := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.ltwoBond_eq_sqrt <;> assumption
theorem ltwoTensor_eq [Fintype 𝒯.FineBond] {r : ℕ} (J : 𝒯.Tensor r) :
    ltwoTensor J =
      √(∑ i : (Fin r → Fin 4) × 𝒯.FineBond, (𝒯.ξ ^ 2 * J i.1 i.2) * (𝒯.ξ ^ 2 * J i.1 i.2)) := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.ltwoTensor_eq_sqrt <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
structure ScaledNorms (Q : LevelCube 𝒮 M) (ζ' : Q.system.setting.FineSite → ℝ)
    (u : Q.system.setting.FineBond → ℝ) (a : ℝ) : Prop where
  value_le : ltwoBond (smulSiteBond ζ' u) ≤ levelSpacing Q ^ 2 * a
  nabla_le : ltwoTensor (smulSiteTensor ζ' (nablaOne u)) ≤ levelSpacing Q * a
  nabla_nabla_le : ltwoTensor (smulSiteTensor ζ' (nablaTwo (nablaOne u))) ≤ a
theorem ScaledNorms.mono {Q : LevelCube 𝒮 M} {ζ' : Q.system.setting.FineSite → ℝ}
    {u : Q.system.setting.FineBond → ℝ} {a a' : ℝ} (h : ScaledNorms Q ζ' u a)
    (hx : 0 ≤ levelSpacing Q) (ha : a ≤ a') : ScaledNorms Q ζ' u a' where
  value_le := h.value_le.trans (mul_le_mul_of_nonneg_left ha (pow_nonneg hx 2))
  nabla_le := h.nabla_le.trans (mul_le_mul_of_nonneg_left ha hx)
  nabla_nabla_le := h.nabla_nabla_le.trans ha
theorem supSite_nonneg (ζ : 𝒯.FineSite → ℝ) : 0 ≤ supSite ζ :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem mul_four_le {B s e j Z d n : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (hsZ : s ≤ Z) (he : 0 ≤ e)
    (hed : e ≤ d) (hj : 0 ≤ j) (hjn : j ≤ n) : B * s * e * j ≤ B * Z * (d * n) := by
  have hZ : 0 ≤ Z := hs.trans hsZ
  have hd : 0 ≤ d := he.trans hed
  have h₁ : e * j ≤ d * n := mul_le_mul hed hjn hj hd
  have h₂ : s * (e * j) ≤ Z * (d * n) := mul_le_mul hsZ h₁ (mul_nonneg he hj) hZ
  calc B * s * e * j = B * (s * (e * j)) := by ring
    _ ≤ B * (Z * (d * n)) := mul_le_mul_of_nonneg_left h₂ hB
    _ = B * Z * (d * n) := by ring
theorem expWeight_nonneg (y z : 𝒮.Point) : 0 ≤ expWeight y z := (Real.exp_pos _).le
theorem levelSpacing_pos (Q : LevelCube 𝒮 M) : 0 < levelSpacing Q := by apply _root_.YangMills.Construction.EnlargedCubeBounds.Assembly.levelSpacing_pos <;> assumption
end YangMills.Construction.CubeTermNorms
