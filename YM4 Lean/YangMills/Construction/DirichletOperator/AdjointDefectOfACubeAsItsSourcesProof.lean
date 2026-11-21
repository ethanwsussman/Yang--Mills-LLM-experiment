import YangMills.Construction.DirichletOperator.ChangeOfTheLongitudinalOperatorInNorm
import YangMills.Construction.DirichletOperator.SourcesOfTheAdjointDefectOfACube
import YangMills.Construction.DirichletOperator.TermsOfTheRemainder
import YangMills.Construction.DirichletOperator.DifferenceOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.RegionSequence.AnchorCutIdentities
import YangMills.Construction.RegionSequence.BaseOperatorPositivityProof
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
namespace CubeAdjointDefect.AsSources
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
section InnerProducts
variable {𝒯 : RegionSequence.NestedRegions}
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_sub_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by
  have := Fintype.ofFinite 𝒯.FineBond
  simp only [bondInner, finsum_eq_sum_of_fintype, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
    mul_sub]
theorem bondInner_add_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_zero_of_bondInner_self [Finite 𝒯.FineBond] (D : 𝒯.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by
  have := Fintype.ofFinite 𝒯.FineBond
  simp only [bondInner, finsum_eq_sum_of_fintype] at h
  have hs : ∑ b, D b * D b = 0 := (mul_eq_zero.mp h).resolve_left (pow_pos 𝒯.ξ_pos 4).ne'
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => mul_self_nonneg (D b)).mp hs
  funext b
  exact mul_self_eq_zero.mp (hz b (Finset.mem_univ b))
theorem eq_of_bondInner_eq [Finite 𝒯.FineBond] (X : Submodule ℝ (𝒯.FineBond → ℝ))
    {v v' : 𝒯.FineBond → ℝ} (hv : v ∈ X) (hv' : v' ∈ X)
    (h : ∀ u ∈ X, bondInner v u = bondInner v' u) : v = v' := by
  have hD : bondInner (v - v') (v - v') = 0 := by
    rw [bondInner_sub_left, h _ (X.sub_mem hv hv'), sub_self]
  exact sub_eq_zero.mp (eq_zero_of_bondInner_self _ hD)
end InnerProducts
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem supNorm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem supNorm_source_sub_target (b : 𝒮.FineBond) :
    supNorm ((b.source : 𝒮.Point) - (b.target : 𝒮.Point)) ≤ 𝒮.ξ := by
  have e : (b.source : 𝒮.Point) - (b.target : 𝒮.Point) =
      torusProj 4 𝒮.side (-Pi.single b.dir 𝒮.ξ) := by
    have h : (b.target : 𝒮.Point) =
        (b.source : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single b.dir 𝒮.ξ) := rfl
    rw [h]
    funext μ
    simp [torusProj]
  rw [e]
  exact (supNorm_torusProj_le _).trans (by rw [norm_neg]; exact norm_piSingle_le 𝒮.ξ_pos.le _)
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_le_cast (hM : 𝒮.L ^ 5 ≤ M) : (13 : ℝ) ≤ M := by
  have h : 13 ≤ M := 𝒮.thirteen_le_L.trans ((Nat.le_self_pow (by norm_num) _).trans hM)
  exact_mod_cast h
theorem ξ_le_scale (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  have hn : (1 : ℝ) ≤ (𝒮.L : ℝ) ^ n := one_le_pow₀ hL
  have hξ := 𝒮.ξ_pos
  simp only [RegionSequence.NestedRegions.scale, scaleSpacing, zpow_natCast]
  nlinarith
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by
  have h₁ := thirteen_le_cast hM
  have h₂ := ξ_le_scale (𝒮 := 𝒮) n
  have hξ := 𝒮.ξ_pos
  simp only [cubeSide]
  nlinarith
theorem mem_Ω_zero_of_near (hl : Torus.TorusLengthsStatement) {X : Set 𝒮.Point} (hM : (1 : ℝ) ≤ M)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < supSetDist X (𝒮.cubeComplementAt 0 (𝒮.Ω 0)))
    (x y : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ X)
    (hd : supNorm ((x : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by
  by_contra hy
  have hξ := 𝒮.ξ_pos
  have h0 : 𝒮.scale 0 = 𝒮.ξ := by simp [RegionSequence.NestedRegions.scale, scaleSpacing]
  have hmem : (y : 𝒮.Point) ∈ 𝒮.cubeComplementAt 0 (𝒮.Ω 0) := by
    refine Set.mem_sUnion.2 ⟨cubeAt (y : 𝒮.Point) (𝒮.scale 0),
      ⟨⟨(y : 𝒮.Point), by rw [h0]; exact y.2, rfl⟩, fun hsub => hy (hsub ?_)⟩, ?_⟩ <;>
    · show supNorm ((y : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.scale 0 / 2
      rw [sub_self, (hl 4 𝒮.side 𝒮.side_pos).1.supNorm_zero, h0]
      positivity
  have hle : supSetDist X (𝒮.cubeComplementAt 0 (𝒮.Ω 0)) ≤
      ENNReal.ofReal (supNorm ((x : 𝒮.Point) - (y : 𝒮.Point))) :=
    iInf₂_le_of_le _ hx (iInf₂_le_of_le _ hmem le_rfl)
  have h₂ : ENNReal.ofReal (supNorm ((x : 𝒮.Point) - (y : 𝒮.Point))) ≤
      ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) :=
    ENNReal.ofReal_le_ofReal (hd.trans (by nlinarith))
  exact absurd (hway.trans_le (hle.trans h₂)) (lt_irrefl _)
theorem tsupport_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M) (ς : ℝ) :
    tsupport Q.partitionFn ⊆ Q.thicken ς := by
  intro x hx
  show supSetDist {x} Q.supp ≤ _
  refine iInf₂_le_of_le x rfl (iInf₂_le_of_le x hx ?_)
  rw [sub_self, (hl 4 𝒮.side 𝒮.side_pos).1.supNorm_zero]
  simp
theorem fineBond_ext {b b' : 𝒮.FineBond} (h₁ : b.source = b'.source) (h₂ : b.dir = b'.dir) :
    b = b' := by
  cases b
  cases b'
  simp_all
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by
  unfold CubeSystem.pullBonds
  by_cases h₀ : (b.source : 𝒮.Point) ∈ tsupport φ
  · have : {b' : 𝒮.FineBond | (b'.source : 𝒮.Point) ∈ tsupport φ ∧ 𝔏.mapBond b' = 𝔏.mapBond b} =
        {b} := by
      ext b'
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hu b' h₁ h₂
      · rintro rfl
        exact ⟨h₀, rfl⟩
    rw [this, finsum_mem_singleton]
  · have : {b' : 𝒮.FineBond | (b'.source : 𝒮.Point) ∈ tsupport φ ∧ 𝔏.mapBond b' = 𝔏.mapBond b} =
        ∅ := by
      ext b'
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h₁ h₂
      exact h₀ (hu b' h₁ h₂ ▸ h₁)
    rw [this, finsum_mem_empty, image_eq_zero_of_notMem_tsupport h₀, zero_mul]
structure TransferProps (Q : LevelCube 𝒮 M) (𝔏 : CubeSystem 𝒮) : Prop where
  pull_mem : ∀ A ∈ 𝒮.oneForms, 𝔏.pullBonds Q.partitionFn A ∈ 𝔏.forms
  push_mem : ∀ v ∈ 𝔏.forms, 𝔏.pushBonds Q.partitionFn v ∈ 𝒮.oneForms
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond b = b := by
  have hs : ∀ x : 𝒮.FineSite, Q.secondTypeSystem.mapSite x = x := by
    intro x
    apply Subtype.ext
    exact Classical.epsilon_spec (p := fun y : 𝒮.FineSite => (y : 𝒮.Point) = (x : 𝒮.Point))
      ⟨x, rfl⟩
  exact fineBond_ext (hs b.source) rfl
theorem transferProps_secondType (hl : Torus.TorusLengthsStatement) (hM : 𝒮.L ^ 5 ≤ M)
    (Q : LevelCube 𝒮 M)
    (hnear : Q.thicken (5 / 6) ⊆
      {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}) :
    TransferProps Q Q.secondTypeSystem := by
  refine ⟨fun A hA => ?_, fun v hv => ?_⟩
  · have hval : ∀ c : 𝒮.FineBond,
        Q.secondTypeSystem.pullBonds Q.partitionFn A c = Q.partitionFn (c.source : 𝒮.Point) * A c := by
      intro c
      have h := pullBonds_mapBond Q.secondTypeSystem Q.partitionFn A c fun b' _ e => by
        rwa [mapBond_secondType, mapBond_secondType] at e
      rwa [mapBond_secondType] at h
    have hform : Q.secondTypeSystem.pullBonds Q.partitionFn A ∈ 𝒮.oneForms := by
      intro c hc
      rw [hval, hA c hc, mul_zero]
    refine (⟨hform, fun c hc => ?_⟩ : _ ∧ _)
    rw [hval]
    by_cases h0 : Q.partitionFn (c.source : 𝒮.Point) = 0
    · rw [h0, zero_mul]
    exfalso
    apply hc
    have ht : supNorm ((c.source : 𝒮.Point) - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level :=
      hnear (tsupport_subset_thicken hl Q _ (subset_tsupport _ h0))
    have hB := thirteen_mul_ξ_le_cubeSide hM Q.level
    have hξ := 𝒮.ξ_pos
    have Ls := (hl 4 𝒮.side 𝒮.side_pos).1
    constructor
    · show supNorm ((c.source : 𝒮.Point) - Q.centre) ≤ (1 + ((3 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level
      push_cast
      nlinarith
    · show supNorm ((c.target : 𝒮.Point) - Q.centre) ≤ (1 + ((3 : ℕ) : ℝ)) * cubeSide 𝒮 M Q.level
      have e : (c.target : 𝒮.Point) - Q.centre =
          ((c.source : 𝒮.Point) - Q.centre) + ((c.target : 𝒮.Point) - (c.source : 𝒮.Point)) := by
        abel
      have h₁ := Ls.supNorm_le_lOneNorm ((c.target : 𝒮.Point) - Q.centre)
      have h₂ := Ls.lOneNorm_add_le ((c.source : 𝒮.Point) - Q.centre)
        ((c.target : 𝒮.Point) - (c.source : 𝒮.Point))
      rw [← e] at h₂
      have h₃ := Ls.lOneNorm_le_supNorm ((c.source : 𝒮.Point) - Q.centre)
      have h₄ := Ls.lOneNorm_le_supNorm ((c.target : 𝒮.Point) - (c.source : 𝒮.Point))
      have h₅ := supNorm_target_sub_source c
      push_cast at h₃ h₄ ⊢
      nlinarith
  · intro b hb
    have hv' : v ∈ 𝒮.oneForms ∧ _ := hv
    show Q.partitionFn (b.source : 𝒮.Point) * v (Q.secondTypeSystem.mapBond b) = 0
    rw [mapBond_secondType, hv'.1 b hb, mul_zero]
theorem firstType_mem_forms (Q : LevelCube 𝒮 M) (hsecond : ¬Q.IsSecondType)
    (hF : Q.FirstTypeProperties) :
    (∀ f : Q.system.setting.FineBond → ℝ, f ∈ Q.system.forms) ∧
      ∀ f : Q.system.setting.FineBond → ℝ, f ∈ Q.system.setting.oneForms := by
  have hsys : Q.system = Q.firstTypeSystem := by
    unfold LevelCube.system
    exact if_neg hsecond
  obtain ⟨adm, -⟩ := hF.setting_eq
  have hbonds : ∀ b : Q.firstTypeSetting.FineBond, b ∈ Q.firstTypeSetting.bonds := by
    have key : ∀ 𝒯 : RegionSequence.NestedRegions, 𝒯 = Q.torusSetting adm →
        ∀ b : 𝒯.FineBond, b ∈ 𝒯.bonds := by
      rintro _ rfl b
      exact mem_univ _
    refine key _ ?_
    unfold LevelCube.firstTypeSetting
    exact dif_pos adm
  have hall : ∀ 𝔏 : CubeSystem 𝒮, 𝔏 = Q.firstTypeSystem →
      (∀ f : 𝔏.setting.FineBond → ℝ, f ∈ 𝔏.forms) ∧
        ∀ f : 𝔏.setting.FineBond → ℝ, f ∈ 𝔏.setting.oneForms := by
    rintro _ rfl
    exact ⟨fun f b hb => absurd (hbonds b) hb, fun f b hb => absurd (hbonds b) hb⟩
  exact hall _ hsys
theorem transferProps_firstType (hl : Torus.TorusLengthsStatement) (hM : (1 : ℝ) ≤ M)
    (Q : LevelCube 𝒮 M) (hsecond : ¬Q.IsSecondType) (hF : Q.FirstTypeProperties)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
      supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0))) :
    TransferProps Q Q.system := by
  refine ⟨fun A _ => (firstType_mem_forms Q hsecond hF).1 _, fun v _ b hb => ?_⟩
  show Q.partitionFn (b.source : 𝒮.Point) * v (Q.system.mapBond b) = 0
  by_contra hne
  have h₀ : Q.partitionFn (b.source : 𝒮.Point) ≠ 0 := left_ne_zero_of_mul hne
  have ht : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) :=
    tsupport_subset_thicken hl Q _ (subset_tsupport _ h₀)
  have hz : supNorm ((b.source : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by
    rw [sub_self, (hl 4 𝒮.side 𝒮.side_pos).1.supNorm_zero]
    exact 𝒮.ξ_pos.le
  exact hb (𝒮.mem_bonds_of_mem b (mem_Ω_zero_of_near hl hM hway b.source b.source ht hz)
    (mem_Ω_zero_of_near hl hM hway b.source b.target ht (supNorm_source_sub_target b)))
theorem transferProps (hl : Torus.TorusLengthsStatement) (hM : 𝒮.L ^ 5 ≤ M)
    (hpos : CubeGeometry.Placement 𝒮 M)
    (hfirst : ∀ Q : LevelCube 𝒮 M, Q.IsFirstType → Q.FirstTypeProperties)
    (Q : LevelCube 𝒮 M) (hQ : Q ∈ active 𝒮 M) : TransferProps Q Q.system := by
  by_cases h : Q.IsSecondType
  · have hsys : Q.system = Q.secondTypeSystem := by
      unfold LevelCube.system
      exact if_pos h
    rw [hsys]
    exact transferProps_secondType hl hM Q (hpos.near_centre Q hQ)
  · exact transferProps_firstType hl (by linarith [thirteen_le_cast hM]) Q h (hfirst Q ⟨hQ, h⟩)
      (hpos.first_kind Q ⟨hQ, h⟩).away
theorem cubeInv_spec (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) :
    𝔏.inv u ∈ 𝔏.forms ∧ 𝔏.op (𝔏.inv u) = u := by
  obtain ⟨g, hg, rfl⟩ := hb.surjOn hu
  exact Classical.epsilon_spec
    (p := fun g' => g' ∈ (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) ∧
      𝔏.op g' = 𝔏.op g) ⟨g, hg, rfl⟩
end CubeAdjointDefect.AsSources
end YangMills.Construction
