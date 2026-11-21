import YangMills.Construction.Lattice.GeometryOfASeparatedSequence
import YangMills.Construction.Lattice.MassiveDirichletOperatorIdentityFacts
import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace AveragesDifference
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.SeparatedSequences YangMills.Construction.SeparatedSequences.BaseParameters
variable {S : SequenceDatum}
theorem memberAt_of_le {n : ℕ} (h : n ≤ S.t) : S.memberAt S.region n = S.region n :=
  if_pos h
theorem region_subset_of_le {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ S.t) : S.region k ⊆ S.region j := by
  induction k, hjk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k hjk ih =>
    exact ((S.separated.2 k (by simpa using hk)).1).trans (ih (by omega))
theorem mem_layerSites_iff (hcub : LatticeCubeStatement) {n : ℕ} (hn : n ≤ S.t)
    (y : S.LatticeSite n) :
    y ∈ S.layerSites S.region n ↔
      (y : S.Torus) ∈ S.memberAt S.region n ∧ (y : S.Torus) ∉ S.memberAt S.region (n + 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlay⟩ := hcub S (S.m + S.K) 0 (Nat.zero_le _) le_rfl
  rw [(hlay n hn).2.2.1]
  rfl
theorem coe_ne_of_layerSites (hcub : LatticeCubeStatement) {j k : ℕ} (hjk : j < k)
    (hk : k ≤ S.t) {z : S.LatticeSite j} {w : S.LatticeSite k} (hz : z ∈ S.layerSites S.region j)
    (hw : w ∈ S.layerSites S.region k) : (z : S.Torus) ≠ w := by
  intro hzw
  have hz' := ((mem_layerSites_iff hcub (by omega) z).mp hz).2
  have hw' := ((mem_layerSites_iff hcub hk w).mp hw).1
  rw [memberAt_of_le hk] at hw'
  apply hz'
  rw [memberAt_of_le (by omega : j + 1 ≤ S.t), hzw]
  exact region_subset_of_le (by omega) hk hw'
theorem levelSite_eq (hcub : LatticeCubeStatement) {n : ℕ} (hn : n ≤ S.t)
    {y : S.LatticeSite n} (hy : y ∈ S.layerSites S.region n)
    (h : (y : S.Torus) ∈ S.allLayerPoints S.region) : S.levelSite S.region ⟨y, h⟩ = ⟨n, y⟩ := by
  have hspec := (S.exists_levelSite S.region ⟨y, h⟩).choose_spec
  change (S.exists_levelSite S.region ⟨y, h⟩).choose = _
  generalize (S.exists_levelSite S.region ⟨y, h⟩).choose = p at hspec
  obtain ⟨k, z⟩ := p
  obtain ⟨hk, hz, hzy⟩ := hspec
  have hkn : k = n := by
    rcases lt_trichotomy k n with hlt | heq | hgt
    · exact absurd hzy (coe_ne_of_layerSites hcub hlt hn hz hy)
    · exact heq
    · exact absurd hzy.symm (coe_ne_of_layerSites hcub hgt hk hy hz)
  subst hkn
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy']
theorem lineSum_congr {L m K : ℕ} {A B : OneForms L m K} {Γ : List (BareOrientedBond L m K)}
    (h : ∀ b ∈ Γ, orientedValue A b = orientedValue B b) : lineSum A Γ = lineSum B Γ := by
  simp only [lineSum]
  rw [List.map_congr_left h]
end AveragesDifference
end YangMills.Construction
end
