import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace IsometryCells
variable {L m : ℕ} {j : ℤ}
theorem coe_siteImage {σ : FourTorus L m ≃ FourTorus L m}
    (hσL : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j) (y : Site L m j) :
    ((siteImage σ y : Site L m j) : FourTorus L m) = σ y := by
  have hmem : σ y ∈ (sublattice L m j : Set (FourTorus L m)) := by
    rw [← hσL]
    exact mem_image_of_mem _ y.2
  have hex : ∃ x : Site L m j, (x : FourTorus L m) = σ.symm.symm y := ⟨⟨σ y, hmem⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem exists_int_mul_meshSize_of_coe_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {s : ℝ} {n : ℤ}
    (h : (s : AddCircle (torusSide L m)) =
      (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) :
    ∃ N : ℤ, s = (N : ℝ) * meshSize L j := by
  have hzero : ((s - (n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 hzero
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + j by omega)
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsideEq : torusSide L m = (2 * (L : ℝ) ^ d) * meshSize L j := by
    have hm : (m : ℤ) = (d : ℤ) + -j := by omega
    rw [torusSide, meshSize, ← zpow_natCast (L : ℝ) m, hm, zpow_add₀ hLne, zpow_natCast]
    ring
  refine ⟨n + k * (2 * (L : ℤ) ^ d), ?_⟩
  rw [zsmul_eq_mul, hsideEq] at hk
  push_cast
  linarith
theorem coe_unitStep (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) = pointOnAxis L m μ (meshSize L j) := rfl
theorem pointOnAxis_zero (μ : Fin 4) : pointOnAxis L m μ 0 = 0 := by
  simp [pointOnAxis]
theorem eq_zero_or_eq_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {μ ν : Fin 4} (hμν : μ ≠ ν)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) (meshSize L j))
    (hmem : pointOnAxis L m μ s + pointOnAxis L m ν t ∈ sublattice L m j) :
    s = 0 ∨ s = meshSize L j := by
  obtain ⟨n, hn⟩ := hmem
  have hcoe : (s : AddCircle (torusSide L m)) =
      (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    have := hn μ
    simpa [pointOnAxis, Pi.single_eq_of_ne hμν] using this
  obtain ⟨N, hN⟩ := exists_int_mul_meshSize_of_coe_eq hL hj hcoe
  have hpos : 0 < meshSize L j := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    exact zpow_pos this _
  have hNnonneg : (0 : ℝ) ≤ N := by
    by_contra hneg
    have hlt : (N : ℝ) < 0 := not_le.mp hneg
    have := mul_neg_of_neg_of_pos hlt hpos
    linarith [hs.1]
  have hNle : (N : ℝ) ≤ 1 := by
    by_contra hgt
    have hlt : (1 : ℝ) < N := not_le.mp hgt
    nlinarith [hs.2]
  have hNnonneg' : 0 ≤ N := by exact_mod_cast hNnonneg
  have hNle' : N ≤ 1 := by exact_mod_cast hNle
  obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
  · left
    simpa using hN
  · right
    simpa using hN
theorem coe_vertices_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (p : Plaquette L m j) :
    (fun x : Site L m j => (x : FourTorus L m)) '' p.vertices =
      p.face ∩ (sublattice L m j : Set (FourTorus L m)) := by
  have hnonneg : 0 ≤ meshSize L j := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    exact (zpow_pos this _).le
  have hlow : (0 : ℝ) ∈ Icc (0 : ℝ) (meshSize L j) := ⟨le_rfl, hnonneg⟩
  have hhigh : meshSize L j ∈ Icc (0 : ℝ) (meshSize L j) := ⟨hnonneg, le_rfl⟩
  have hne : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, v.2⟩
    simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨0, hlow, 0, hlow, by simp [pointOnAxis_zero]⟩
    · exact ⟨_, hhigh, 0, hlow, by simp [pointOnAxis_zero, coe_unitStep]⟩
    · exact ⟨_, hhigh, _, hhigh, by simp [coe_unitStep]⟩
    · exact ⟨0, hlow, _, hhigh, by simp [pointOnAxis_zero, coe_unitStep]⟩
  · rintro q ⟨⟨s, hs, t, ht, rfl⟩, hq⟩
    have hsum : pointOnAxis L m p.firstAxis s + pointOnAxis L m p.secondAxis t ∈
        sublattice L m j := by
      have := (sublattice L m j).sub_mem hq p.origin.2
      have e : (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis s +
          pointOnAxis L m p.secondAxis t - p.origin =
            pointOnAxis L m p.firstAxis s + pointOnAxis L m p.secondAxis t := by abel
      rwa [e] at this
    have hsum' : pointOnAxis L m p.secondAxis t + pointOnAxis L m p.firstAxis s ∈
        sublattice L m j := by
      rwa [add_comm]
    have hs' := eq_zero_or_eq_meshSize hL hj hne hs hsum
    have ht' := eq_zero_or_eq_meshSize hL hj hne.symm ht hsum'
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl
    · exact ⟨p.origin, by simp [Plaquette.vertices], by simp [pointOnAxis_zero]⟩
    · exact ⟨p.origin + unitStep L m j p.secondAxis, by simp [Plaquette.vertices],
        by simp [pointOnAxis_zero, coe_unitStep]⟩
    · exact ⟨p.origin + unitStep L m j p.firstAxis, by simp [Plaquette.vertices],
        by simp [pointOnAxis_zero, coe_unitStep]⟩
    · exact ⟨p.origin + unitStep L m j p.firstAxis + unitStep L m j p.secondAxis,
        by simp [Plaquette.vertices], by simp [coe_unitStep]⟩
theorem eq_image_of_surjective_of_mem_iff {α : Type*} {f : α → α} (hf : Function.Surjective f)
    {A B : Set α} (H : ∀ a, f a ∈ A ↔ a ∈ B) : A = f '' B := by
  ext y
  obtain ⟨a, rfl⟩ := hf y
  constructor
  · intro h
    exact ⟨a, (H a).1 h, rfl⟩
  · rintro ⟨a', h', e⟩
    rw [← e]
    exact (H a').2 h'
end IsometryCells
open IsometryCells in
theorem isometriesPreserveCells_of_groupAction (h : LatticeIsometryGroupActionStatement) :
    IsometriesPreserveCells := by
  intro L m i j σ hL hm hi hσ hij
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hj : -(m : ℤ) ≤ j := hi.trans hij
  obtain ⟨⟨⟨G, hG⟩, -⟩, -, -, -, hact⟩ := h L m i hL hm hi
  have hsymm : σ.symm ∈ latticeIsometries L m i := by
    have h1 : σ ∈ (G : Set (Equiv.Perm (FourTorus L m))) := by
      rw [hG]
      exact hσ
    have h2 : σ⁻¹ ∈ G := G.inv_mem h1
    have h3 : σ⁻¹ ∈ (G : Set (Equiv.Perm (FourTorus L m))) := h2
    rw [hG] at h3
    exact h3
  obtain ⟨hσL, -, -, hbond, -, hplaq, -⟩ := (hact σ hσ j hij).1
  obtain ⟨-, -, -, hbond', -⟩ := (hact σ.symm hsymm j hij).1
  have hsite : ∀ y : Site L m j, ((siteImage σ y : Site L m j) : FourTorus L m) = σ y :=
    coe_siteImage hσL
  have hsiteSurj : Function.Surjective (siteImage σ : Site L m j → Site L m j) := by
    intro y
    have hy : (y : FourTorus L m) ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := by
      rw [hσL]
      exact y.2
    obtain ⟨x, hx, e⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext ((hsite _).trans e)⟩
  have hbondSurj : Function.Surjective (bondImage σ : Bond L m j → Bond L m j) := by
    intro b
    refine ⟨bondImage σ.symm b, Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · rw [(hbond _).1, (hbond' b).1]
      exact σ.apply_symm_apply _
    · rw [(hbond _).2, (hbond' b).2]
      exact σ.apply_symm_apply _
  refine ⟨hsite, ⟨?_, hsiteSurj⟩, ⟨?_, hbondSurj⟩, ?_, ?_, ?_, ?_⟩
  · intro y y' e
    refine Subtype.ext (σ.injective ?_)
    rw [← hsite y, ← hsite y', e]
  · intro b b' e
    refine Bond.ext (Subtype.ext (σ.injective ?_)) (Subtype.ext (σ.injective ?_))
    · rw [← (hbond b).1, ← (hbond b').1, e]
    · rw [← (hbond b).2, ← (hbond b').2, e]
  · intro b
    exact ⟨Subtype.ext ((hbond b).1.trans (hsite b.source).symm),
      Subtype.ext ((hbond b).2.trans (hsite b.target).symm)⟩
  · intro b
    exact Bond.ext (Subtype.ext ((hbond b.opposite).1.trans (hbond b).2.symm))
      (Subtype.ext ((hbond b.opposite).2.trans (hbond b).1.symm))
  · intro p
    rw [coe_vertices_eq hLpos hj, coe_vertices_eq hLpos hj, hplaq p, image_inter σ.injective, hσL]
  · intro X
    refine ⟨eq_image_of_surjective_of_mem_iff hsiteSurj fun a => ?_,
      eq_image_of_surjective_of_mem_iff hbondSurj fun b => ?_,
      eq_image_of_surjective_of_mem_iff hbondSurj fun b => ?_⟩
    · simp only [sitesIn, mem_ofPred_eq]
      rw [hsite a]
      exact σ.injective.mem_set_image
    · simp only [bondsMeeting, mem_ofPred_eq]
      rw [(hbond b).1, (hbond b).2, σ.injective.mem_set_image, σ.injective.mem_set_image]
    · simp only [bondsInside, mem_ofPred_eq]
      rw [(hbond b).1, (hbond b).2, σ.injective.mem_set_image, σ.injective.mem_set_image]
end PeriodicLattice
end YangMills.Construction
