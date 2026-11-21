import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.LatticeCalculus.Identities
import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Dirichlet.Forms
open scoped Classical
section Neighbors
variable {d : ℕ} {S ξ : ℝ}
theorem innerEnd_mem {W : Set (PeriodicTorus d S)} {b : LatticeBond d S ξ}
    (hb : IsBoundaryBond W b) : (innerEnd W b : PeriodicTorus d S) ∈ W := by
  unfold innerEnd
  by_cases ht : (b.source : PeriodicTorus d S) ∈ W
  · simp [ht]
  · rcases hb with ⟨h₁, _⟩ | ⟨h₁, _⟩
    · exact absurd h₁ ht
    · simpa [ht] using h₁
end Neighbors
section Averages
variable {ι : Type*} (s : Finset ι) (f : ι → ℝ) {ξ η : ℝ} {N d : ℕ}
end Averages
section Cells
variable {d L : ℕ} {S aMinus aPlus : ℝ}
theorem finite_latticeSite {ξ : ℝ} {k : ℕ} (hk : 0 < k) (hS : S = k * ξ) :
    Finite (LatticeSite d S ξ) := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  refine Finite.of_surjective (fun c : Fin d → Fin k =>
    (⟨torusProj d S fun i => ((c i : ℕ) : ℝ) * ξ, ⟨fun i => ((c i : ℕ) : ℤ), by simp⟩⟩ :
      LatticeSite d S ξ)) ?_
  rintro ⟨y, n, rfl⟩
  refine ⟨fun i => ⟨(n i % k).toNat, ?_⟩, ?_⟩
  · have h₁ := Int.emod_nonneg (n i) hkz.ne'
    have h₂ := Int.emod_lt_of_pos (n i) hkz
    omega
  · apply Subtype.ext
    funext i
    have h₀ := Int.emod_nonneg (n i) hkz.ne'
    have h : ((n i % k : ℤ) : ℝ) + (k : ℝ) * ((n i / k : ℤ) : ℝ) = (n i : ℝ) := by
      exact_mod_cast Int.emod_add_mul_ediv (n i) k
    have h' : (((n i % k).toNat : ℕ) : ℝ) = ((n i % k : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h₀
    have hm : (n i : ℝ) * ξ = (((n i % k).toNat : ℕ) : ℝ) * ξ + (n i / k : ℤ) • S := by
      rw [h', zsmul_eq_mul, hS, ← h]
      ring
    simp only [torusProj]
    rw [hm, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]
theorem mem_spacingLattice_of_scale {ξ : ℝ} {n : ℕ} {y : PeriodicTorus d S}
    (hy : y ∈ spacingLattice d S (scaleSpacing L ξ n)) : y ∈ spacingLattice d S ξ := by
  obtain ⟨k, rfl⟩ := hy
  refine ⟨fun μ => k μ * (L : ℤ) ^ n, ?_⟩
  funext μ
  simp only [torusProj, scaleSpacing]
  push_cast
  congr 1
  rw [zpow_natCast]
  ring
structure CellData (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  finite_latticeSite : Finite (LatticeSite d S 𝒮.ξ)
  finite_centres : 𝒮.centres.Finite
  ξ_pos : 0 < 𝒮.ξ
  centreSpacing_pos : ∀ y, 0 < 𝒮.centreSpacing y
  card_cell : ∀ y ∈ 𝒮.centres, ∃ N : ℕ, 0 < N ∧ (N : ℝ) = 𝒮.centreSpacing y / 𝒮.ξ ∧
    Nat.card {x : LatticeSite d S 𝒮.ξ // (x : PeriodicTorus d S) ∈ 𝒮.cell y} = N ^ d
  centreOf_spec : ∀ x : LatticeSite d S 𝒮.ξ, (x : PeriodicTorus d S) ∈ 𝒮.Ω 0 →
    𝒮.centreOf x ∈ 𝒮.centres ∧ (x : PeriodicTorus d S) ∈ 𝒮.cell (𝒮.centreOf x) ∧
      ∀ y ∈ 𝒮.centres, (x : PeriodicTorus d S) ∈ 𝒮.cell y → y = 𝒮.centreOf x
  cell_subset : ∀ y ∈ 𝒮.centres, 𝒮.cell y ⊆ 𝒮.Ω 0
  Ω_zero_eq : 𝒮.Ω 0 = ⋃ y ∈ 𝒮.centres, 𝒮.cell y
  centreIndex_le : ∀ y ∈ 𝒮.centres, 𝒮.centreIndex y ≤ 𝒮.t
  ncard_neighbors : ∀ x : LatticeSite d S 𝒮.ξ, {y | IsNeighbor x y}.ncard = 2 * d
end Cells
section Regions
variable {d : ℕ} {S ξ : ℝ}
end Regions
section Averaging
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def cellSites [Fintype (LatticeSite d S 𝒮.ξ)] (y : PeriodicTorus d S) :
    Finset (LatticeSite d S 𝒮.ξ) :=
  Finset.univ.filter fun x => (x : PeriodicTorus d S) ∈ 𝒮.cell y
theorem card_cellSites [Fintype (LatticeSite d S 𝒮.ξ)] (hb : CellData 𝒮)
    {y : PeriodicTorus d S} (hy : y ∈ 𝒮.centres) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) = 𝒮.centreSpacing y / 𝒮.ξ ∧ (cellSites 𝒮 y).card = N ^ d := by
  obtain ⟨N, h0, h1, h2⟩ := hb.card_cell y hy
  refine ⟨N, h0, h1, ?_⟩
  rw [← h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl
theorem innerSum_comm {ξ : ℝ} (f g : LatticeSite d S ξ → ℝ) :
    innerSum f g = innerSum g f := by
  unfold innerSum
  simp only [mul_comm (f _)]
theorem rpow_neg_half_sq {t : ℝ} (ht : 0 < t) (d : ℕ) :
    (t ^ (-(d : ℝ) / 2)) ^ 2 = (t ^ d)⁻¹ := by
  rw [← Real.rpow_mul_natCast ht.le, ← Real.rpow_natCast, ← Real.rpow_neg ht.le]
  congr 1
  push_cast
  ring
end Averaging
end YangMills.Construction.Dirichlet.Forms
