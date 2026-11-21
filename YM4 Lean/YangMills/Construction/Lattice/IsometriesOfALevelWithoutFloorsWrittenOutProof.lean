import YangMills.Construction.Lattice.IsometriesOfALevelAndTheirCubesProof
import YangMills.Construction.Lattice.IsometriesOfALevelWithoutFloorsWrittenOut
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LevelIsometry
theorem permutesCubes_of_mem_latticeIsometries (isoGroups : LatticeIsometryGroupActionStatement)
    {L m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i k : ℤ}
    (hi : -(m : ℤ) ≤ i) (hik : i ≤ k)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    PermutesCubes σ k := by
  obtain ⟨-, -, -, -, h⟩ := isoGroups L m i hL hm hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hp⟩ := (h σ hσ k hik).1
  refine ⟨fun Q hQ => ?_, (image_injective.2 σ.injective).injOn, hp.ge⟩
  have : σ '' Q ∈ (fun Q => σ '' Q) '' standardCubePartition L m k := ⟨Q, hQ, rfl⟩
  rwa [hp] at this
theorem mem_meshVectors_of_torusProj_mem {L m : ℕ} (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {v : Fin 4 → ℝ} (h : TorusMetric.torusProj (torusSide L m) v ∈ sublattice L m i) :
    v ∈ meshVectors L i := by apply _root_.YangMills.Construction.PeriodicLattice.LevelIsometryProof.mem_meshVectors_of_torusProj_mem <;> assumption
theorem levelIsometryPropertiesExpanded_holds (groups : LevelIsometryProperties)
    (ball : SupBallDeterminesCentre)
    (cov : LatticeIsometryCovariance) : LevelIsometryPropertiesExpanded := by
  refine ⟨groups, ?_⟩
  intro L m K t u hL hm hK ht hu
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hL0 : (L : ℝ) ≠ 0 := hLr.ne'
  have : Fact (0 < torusSide L m) := ⟨by unfold torusSide; positivity⟩
  have isoGroups := cov.1
  obtain ⟨hunit, hcube, hi, hisom, -⟩ := groups L m K t u hL hm hK ht hu
  have hdepth : -(m : ℤ) ≤ levelDepth K t := by
    simp only [levelDepth]
    omega
  have hlevel : RegionChains.meshAtLevel L t t = 1 := by
    simp only [RegionChains.meshAtLevel, finestMeshInLevelUnits]
    rw [← zpow_natCast, ← zpow_add₀ hL0, add_neg_cancel, zpow_zero]
  rw [hlevel, mul_one] at hcube
  refine ⟨hlevel, hisom, fun σ hσ =>
    ⟨fun h => permutesCubes_of_mem_latticeIsometries isoGroups hL hm hi le_rfl h, ?_⟩,
    fun σ hσ n ν hn hν => ?_⟩
  · intro hy'
    have hσ' := hσ
    obtain ⟨r, v, hv, hind⟩ := hσ
    have hpres := ((isoGroups L m _ hL hm hdepth).2.1 σ hσ').1.1
    obtain ⟨y, hy⟩ := hy'
    have hball : ∀ x, x ∈ cubeAround y ↔
        TorusMetric.torusSupNorm (x - σ 0) ≤ meshSize L (scaledCubeIndex K t u) / 2 := by
      intro x
      rw [hy]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hpres]
        simpa [cubeAround] using hz
      · intro hx
        refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
        have h1 := hpres (σ.symm x) 0
        rw [σ.apply_symm_apply] at h1
        rw [h1] at hx
        simpa [cubeAround] using hx
    have hscale : (0 : ℝ) < (L : ℝ) ^ levelDepth K t := zpow_pos hLr _
    have hhalf : toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) = (L : ℝ) ^ u / 2 := by
      simp only [toLevelUnits] at hcube ⊢
      rw [← mul_div_assoc, hcube]
    have hρ : toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) ≤
        sideInLevelUnits L m K t / 4 := by
      rw [hhalf]
      have h1 : (L : ℝ) ^ u ≤ (L : ℝ) ^ ((m : ℤ) + (K : ℤ) - (t : ℤ)) := by
        rw [← zpow_natCast]
        refine zpow_le_zpow_right₀ (by exact_mod_cast hLpos) ?_
        simp only [levelDepth] at hu
        omega
      simp only [sideInLevelUnits]
      linarith
    have hρ0 : 0 ≤ toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) := by
      rw [hhalf]
      positivity
    have hle : ∀ a c : ℝ, toLevelUnits L K t a ≤ toLevelUnits L K t c ↔ a ≤ c := fun a c =>
      ⟨fun h' => le_of_mul_le_mul_left h' hscale, fun h' => mul_le_mul_of_nonneg_left h' hscale.le⟩
    have hcentre : (y : FourTorus L m) = σ 0 :=
      ball L m K hL hm hK t ht _ hρ0 hρ y (σ 0) (Set.ext fun x => by
        show toLevelUnits L K t _ ≤ _ ↔ toLevelUnits L K t _ ≤ _
        rw [hle, hle]
        exact hball x)
    have hproj : TorusMetric.torusProj (torusSide L m) v = σ 0 := by
      have h1 := hind 0
      have h2 : toFourTorus L m 0 = 0 := by
        funext μ
        simp [toFourTorus]
      have h3 : r.actOnVector 0 = 0 := by
        funext μ
        simp [SignedFrame.actOnVector]
      rw [h2, h3, zero_add] at h1
      exact h1.symm
    have hmem : TorusMetric.torusProj (torusSide L m) v ∈ sublattice L m (scaledCubeIndex K t u) := by
      rw [hproj, ← hcentre]
      exact y.2
    exact ⟨r, v, mem_meshVectors_of_torusProj_mem hLpos hi hmem, hind⟩
  · have hnK : n ≤ K := hn.trans ht
    have hνle : (ν : ℤ) ≤ (m : ℤ) + levelDepth K n := by
      simp only [levelDepth] at hu ⊢
      omega
    refine ⟨hnK, hνle, permutesCubes_of_mem_latticeIsometries isoGroups hL hm hi ?_ hσ⟩
    simp only [scaledCubeIndex, levelDepth]
    omega
end YangMills.Construction.PeriodicLattice.LevelIsometry
