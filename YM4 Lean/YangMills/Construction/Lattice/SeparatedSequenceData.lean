import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SeparatedSequences
open PeriodicLattice
structure BaseParameters where
  L : ℕ
  odd_L : Odd L
  three_le_L : 3 ≤ L
  K : ℕ
  K_pos : 0 < K
  m : ℕ
  m_pos : 0 < m
  t : ℕ
  t_le_K : t ≤ K
  blockExp : ℕ
  gapExp : ℕ
  L_le_pow_gapExp : L ≤ L ^ gapExp
  a : ℝ
  a_pos : 0 < a
namespace BaseParameters
abbrev dimension : ℕ := 4
variable (D : BaseParameters)
def gapSize : ℕ := D.L ^ D.gapExp
abbrev scales : ScaleData :=
  ⟨D.K, D.t, D.t, D.blockExp, D.t_le_K, D.t_le_K⟩
abbrev Torus : Type := PeriodicLattice.FourTorus D.L D.m
abbrev LatticeSite (n : ℕ) : Type := SiteAtLevel D.L D.m D.K n
def lengthInUnits (r : ℝ) : ℝ := D.scales.toUnits D.L r
def levelMeshRatio (n : ℕ) : ℝ := D.scales.levelMesh D.L n
theorem lengthInUnits_meshSize (n : ℕ) :
    D.lengthInUnits (meshSize D.L (levelDepth D.K n)) = D.levelMeshRatio n := by
  have hL : (D.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.three_le_L; omega)
  simp only [lengthInUnits, levelMeshRatio, ScaleData.toUnits,
    ScaleData.levelMesh, toLevelUnits, meshSize]
  rw [← zpow_add₀ hL]
  congr 1
  simp only [levelDepth]
  ring
theorem levelMeshRatio_zero : D.levelMeshRatio 0 = finestMeshInLevelUnits D.L D.t := by
  simp [levelMeshRatio, ScaleData.levelMesh, finestMeshInLevelUnits]
def memberAt (Ω : ℕ → Set D.Torus) (n : ℕ) : Set D.Torus := truncatedMember D.scales Ω n
def layerSites (Ω : ℕ → Set D.Torus) (n : ℕ) : Set (D.LatticeSite n) :=
  layerLatticeSites D.scales Ω n
def allLayerPoints (Ω : ℕ → Set D.Torus) : Set D.Torus :=
  layerPoints D.scales Ω
def withWholeTorus (Ω : ℕ → Set D.Torus) : ℕ → Set D.Torus := Function.update Ω 0 univ
variable {D} {n : ℕ}
def cube (y : D.LatticeSite n) : Set D.Torus := siteBlock D.scales y
def fineBlock (y : D.LatticeSite n) : Set D.Torus :=
  cube y ∩ (sublattice D.L D.m (levelDepth D.K 0) : Set D.Torus)
def coarseBlock (y : D.LatticeSite (n + 1)) : Set D.Torus :=
  cube y ∩ (sublattice D.L D.m (levelDepth D.K n) : Set D.Torus)
end BaseParameters
structure SequenceDatum extends BaseParameters where
  region : ℕ → Set toBaseParameters.Torus
  separated : IsSeparatedSequence toBaseParameters.scales
    (toBaseParameters.gapSize : ℝ) region
  region_zero_nonempty : (region 0).Nonempty
end SeparatedSequences
namespace FiniteDimReal
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
def IsAdjointFor (ipV : V → V → ℝ) (ipW : W → W → ℝ) (T : V →ₗ[ℝ] W) (T' : W →ₗ[ℝ] V) : Prop :=
  ∀ f g, ipW g (T f) = ipV (T' g) f
def adjointFor (ipV : V → V → ℝ) (ipW : W → W → ℝ) (T : V →ₗ[ℝ] W) : W →ₗ[ℝ] V :=
  Classical.epsilon (IsAdjointFor ipV ipW T)
def IsSymmetricFor (ip : V → V → ℝ) (X : V →ₗ[ℝ] V) : Prop := ∀ f g, ip f (X g) = ip (X f) g
def IsPosDefFor (ip : V → V → ℝ) (X : V →ₗ[ℝ] V) : Prop :=
  IsSymmetricFor ip X ∧ ∀ f, f ≠ 0 → 0 < ip f (X f)
end FiniteDimReal
end YangMills.Construction
end
