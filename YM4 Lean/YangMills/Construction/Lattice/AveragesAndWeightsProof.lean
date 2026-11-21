import YangMills.Construction.Lattice.DecompositionOfTheFormGreenOperatorProof
import YangMills.Construction.Lattice.FactsOfTheFormExtensionProof
import YangMills.Construction.Lattice.LatticesAndCubesOfOrder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedSequences
namespace BlockAverages
open BaseParameters
variable {L m K : ℕ}
theorem coe_toSublattice {j j' : ℤ} (hL : 0 < L) (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono hL m h y.2⟩, rfl⟩
theorem unitStep_injective (hL : 0 < L) {j : ℤ} (hj : 0 ≤ j) :
    Function.Injective (unitStep L m j) := by
  intro μ ν h
  by_contra hne
  have h1 : ((unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      ((unitStep L m j ν : Site L m j) : FourTorus L m) μ :=
    congrFun (congrArg Subtype.val h) μ
  simp only [unitStep, pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hside : 2 ≤ torusSide L m := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ hL1
    simp only [torusSide]
    linarith
  obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hs1 : meshSize L (d : ℤ) ≤ 1 := by
    simp only [meshSize, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hs0 : 0 < meshSize L (d : ℤ) := by
    simp only [meshSize]
    exact zpow_pos (by linarith) _
  rw [zsmul_eq_mul] at hk
  rcases le_or_gt k 0 with hk0 | hk0
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    nlinarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
theorem levelMeshRatio_eq (E : BaseParameters) (n : ℕ) :
    E.levelMeshRatio n = (E.L : ℝ) ^ n * E.levelMeshRatio 0 := by
  have hL : (E.L : ℝ) ≠ 0 := by
    have := E.three_le_L
    exact_mod_cast (by omega : E.L ≠ 0)
  simp only [levelMeshRatio, ScaleData.levelMesh]
  rw [← zpow_natCast, ← zpow_add₀ hL]
  congr 1
  push_cast
  ring
theorem levelMeshRatio_pos (E : BaseParameters) (n : ℕ) : 0 < E.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
theorem latticeInner_comm {ι : Type} (L t : ℕ) (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.GreenDecomposition.latticeInner_comm <;> assumption
variable (E : BaseParameters) (Ω : ℕ → Set E.Torus) (φ : BondFrame)
theorem principalBondValue_add {E : BaseParameters} {Ω : ℕ → Set E.Torus} {φ : BondFrame}
    (B B' : E.CoarseOneForms Ω φ) (c : Σ n : ℕ, E.LevelBond n) :
    principalBondValue (B + B') c = principalBondValue B c + principalBondValue B' c := by apply _root_.YangMills.Construction.SeparatedSequences.BaseParameters.principalBondValue_add <;> assumption
theorem principalBondValue_smul {E : BaseParameters} {Ω : ℕ → Set E.Torus} {φ : BondFrame}
    (r : ℝ) (B : E.CoarseOneForms Ω φ) (c : Σ n : ℕ, E.LevelBond n) :
    principalBondValue (r • B) c = r * principalBondValue B c := by apply _root_.YangMills.Construction.SeparatedSequences.BaseParameters.principalBondValue_smul <;> assumption
theorem memberAt_of_le {E : BaseParameters} (Ω : ℕ → Set E.Torus) {n : ℕ} (h : n ≤ E.t) :
    E.memberAt Ω n = Ω n :=
  if_pos h
theorem levelSite_eq (D : SequenceDatum) (hLay : D.ShellCubeStructure D.region) :
    ∀ n ≤ D.t, ∀ y ∈ D.layerSites D.region n,
      ∀ h : (y : D.Torus) ∈ D.allLayerPoints D.region,
        D.levelSite D.region ⟨y, h⟩ = ⟨n, y⟩ := by
  intro n hn y hy h
  have hanti : ∀ j k, j ≤ k → k ≤ D.t → D.region k ⊆ D.region j := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact fun _ => subset_rfl
    | succ k hjk ih =>
      intro hk
      exact ((D.separated.2 k (by omega : k < D.t)).1).trans (ih (by omega))
  have hsep : ∀ (j k : ℕ), j < k → k ≤ D.t → ∀ (z : D.LatticeSite j) (w : D.LatticeSite k),
      z ∈ D.layerSites D.region j → w ∈ D.layerSites D.region k → (z : D.Torus) ≠ w := by
    intro j k hjk hk z w hz hw hzw
    have hz' : z ∈ {y : D.LatticeSite j | (y : D.Torus) ∈ D.memberAt D.region j ∧
        (y : D.Torus) ∉ D.memberAt D.region (j + 1)} := (hLay j (by omega)).2.2.1 ▸ hz
    have hw' : w ∈ {y : D.LatticeSite k | (y : D.Torus) ∈ D.memberAt D.region k ∧
        (y : D.Torus) ∉ D.memberAt D.region (k + 1)} := (hLay k hk).2.2.1 ▸ hw
    apply hz'.2
    rw [memberAt_of_le _ (by omega : j + 1 ≤ D.t), hzw]
    have := hw'.1
    rw [memberAt_of_le _ hk] at this
    exact hanti (j + 1) k (by omega) hk this
  have hspec := (D.exists_levelSite D.region ⟨y, h⟩).choose_spec
  show (D.exists_levelSite D.region ⟨y, h⟩).choose = _
  generalize (D.exists_levelSite D.region ⟨y, h⟩).choose = p at hspec
  obtain ⟨k, z⟩ := p
  obtain ⟨hk, hz, hzy⟩ := hspec
  have hkn : k = n := by
    rcases lt_trichotomy k n with hlt | heq | hgt
    · exact absurd hzy (hsep k n hlt hn z y hz hy)
    · exact heq
    · exact absurd hzy.symm (hsep n k hgt hk y z hy hz)
  subst hkn
  have : z = y := Subtype.ext hzy
  rw [this]
end BlockAverages
end SeparatedSequences
end YangMills.Construction
end
