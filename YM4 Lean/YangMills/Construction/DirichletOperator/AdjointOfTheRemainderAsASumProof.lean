import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeAsItsSourcesProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
noncomputable section
namespace YangMills.Construction.RemainderAdjointSum
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem cornerSet_finite (hl : Torus.TorusLengthsStatement) (n : ℕ)
    (hσ : 0 < cubeSide 𝒮 M n) (hk : ∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)) :
    (cornerSet 𝒮 M n).Finite := by
  obtain ⟨k, hk⟩ := hk
  have hS := 𝒮.side_pos
  have hq : 0 < 𝒮.side / cubeSide 𝒮 M n := div_pos hS hσ
  have hk0 : 0 < k := by
    by_contra h
    have h' : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h
    rw [hk] at hq
    linarith
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk0.le
  have hside : 𝒮.side = ((2 * j : ℕ) : ℝ) * cubeSide 𝒮 M n := by
    have := (div_eq_iff hσ.ne').mp hk
    rw [this]
    push_cast
    ring
  have hlat := ((hl 4 𝒮.side hS).2 (cubeSide 𝒮 M n) (2 * j) hσ (by omega) hside).finite
  have hε : {ε : Fin 4 → ℝ | ∀ μ, ε μ = 1 ∨ ε μ = -1}.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin 4 => ({1, -1} : Set ℝ))
      fun _ => Set.toFinite _).subset ?_
    intro ε h μ _
    simpa using h μ
  refine (hlat.image2 (fun (c : 𝒮.Point) (ε : Fin 4 → ℝ) =>
    c + torusProj 4 𝒮.side fun μ => ε μ * (cubeSide 𝒮 M n / 2)) hε).subset ?_
  rintro z ⟨c, hc, ε, hε', rfl⟩
  exact ⟨c, hc, ε, hε', rfl⟩
theorem finite_levelCube (hc : ∀ n ≤ topLevel 𝒮, (cornerSet 𝒮 M n).Finite) :
    Finite (LevelCube 𝒮 M) := by
  have hS : (⋃ n ∈ Set.Iic (topLevel 𝒮), cornerSet 𝒮 M n).Finite :=
    (Set.finite_Iic _).biUnion fun n hn => hc n hn
  have := hS.to_subtype
  refine Finite.of_injective (fun Q : LevelCube 𝒮 M =>
    (((⟨Q.level, Nat.lt_succ_of_le Q.level_le⟩ : Fin (topLevel 𝒮 + 1))),
      (⟨Q.centre, Set.mem_biUnion (show Q.level ∈ Set.Iic (topLevel 𝒮) from Q.level_le) Q.centre_mem⟩ :
        ↥(⋃ n ∈ Set.Iic (topLevel 𝒮), cornerSet 𝒮 M n)))) ?_
  intro Q Q' h
  simp only [Prod.mk.injEq, Fin.mk.injEq, Subtype.mk.injEq] at h
  exact LevelCube.ext h.1 h.2
theorem bondInner_comm {𝒯 : RegionSequence.NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_finset_sum [Finite 𝒮.FineBond] {ι : Type*} (F : Finset ι)
    (f : ι → 𝒮.FineBond → ℝ) (g : 𝒮.FineBond → ℝ) :
    bondInner (∑ i ∈ F, f i) g = ∑ i ∈ F, bondInner (f i) g := by
  have := Fintype.ofFinite 𝒮.FineBond
  simp only [bondInner, finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.sum_mul,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]
theorem bondInner_sub [Finite 𝒮.FineBond] (A B g : 𝒮.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self [Finite 𝒮.FineBond] (D : 𝒮.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
theorem supNorm_source_sub_target (b : 𝒮.FineBond) :
    supNorm ((b.source : 𝒮.Point) - (b.target : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.supNorm_source_sub_target <;> assumption
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_le_cast (hM : 𝒮.L ^ 5 ≤ M) : (13 : ℝ) ≤ M := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_le_cast <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem mem_Ω_zero_of_near (hl : Torus.TorusLengthsStatement) {X : Set 𝒮.Point} (hM : (1 : ℝ) ≤ M)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < supSetDist X (𝒮.cubeComplementAt 0 (𝒮.Ω 0)))
    (x y : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ X)
    (hd : supNorm ((x : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mem_Ω_zero_of_near <;> assumption
theorem tsupport_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M) (ς : ℝ) :
    tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond b = b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mapBond_secondType <;> assumption
theorem inv_spec (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) :
    𝔏.inv u ∈ 𝔏.forms ∧ 𝔏.op (𝔏.inv u) = u := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.cubeInv_spec <;> assumption
end YangMills.Construction.RemainderAdjointSum
