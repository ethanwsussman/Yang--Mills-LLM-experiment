import YangMills.Construction.DirichletOperator.AdjointOfTheRemainderAsASumProof
import YangMills.Construction.DirichletOperator.DefectAsTheSumOfItsKernels
import YangMills.Construction.DirichletOperator.LawsOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace ApproxInverseLaws
variable {𝒮 : NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem cornerSet_finite (hl : Torus.TorusLengthsStatement) (n : ℕ)
    (hσ : 0 < cubeSide 𝒮 M n) (hk : ∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)) :
    (cornerSet 𝒮 M n).Finite := by apply _root_.YangMills.Construction.RemainderAdjointSum.cornerSet_finite <;> assumption
theorem finite_levelCube (hc : ∀ n ≤ topLevel 𝒮, (cornerSet 𝒮 M n).Finite) :
    Finite (LevelCube 𝒮 M) := by apply _root_.YangMills.Construction.RemainderAdjointSum.finite_levelCube <;> assumption
theorem bondInner_comm {𝒯 : NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_finset_sum_left [Finite 𝒮.FineBond] {ι : Type*} (F : Finset ι)
    (f : ι → 𝒮.FineBond → ℝ) (g : 𝒮.FineBond → ℝ) :
    bondInner (∑ i ∈ F, f i) g = ∑ i ∈ F, bondInner (f i) g := by apply _root_.YangMills.Construction.RemainderAdjointSum.bondInner_finset_sum <;> assumption
theorem bondInner_sub_left [Finite 𝒮.FineBond] (A B g : 𝒮.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self [Finite 𝒮.FineBond] (D : 𝒮.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
theorem map_finset_sum_of_selfAdjointOn [Finite 𝒮.FineBond]
    {T : (𝒮.FineBond → ℝ) → 𝒮.FineBond → ℝ}
    (hT : CellStructure.IsSelfAdjointOn (𝒮.oneForms : Set (𝒮.FineBond → ℝ)) bondInner T)
    {ι : Type*} (F : Finset ι) (f : ι → 𝒮.FineBond → ℝ) (hf : ∀ i ∈ F, f i ∈ 𝒮.oneForms) :
    T (∑ i ∈ F, f i) = ∑ i ∈ F, T (f i) := by
  have hs : ∑ i ∈ F, f i ∈ 𝒮.oneForms := 𝒮.oneForms.sum_mem hf
  have hTs : T (∑ i ∈ F, f i) ∈ 𝒮.oneForms := hT.1 _ hs
  have hTf : ∑ i ∈ F, T (f i) ∈ 𝒮.oneForms := 𝒮.oneForms.sum_mem fun i hi => hT.1 _ (hf i hi)
  have key : ∀ v ∈ 𝒮.oneForms,
      bondInner (T (∑ i ∈ F, f i) - ∑ i ∈ F, T (f i)) v = 0 := by
    intro v hv
    rw [bondInner_sub_left, bondInner_finset_sum_left, hT.2 _ hs _ hv, bondInner_finset_sum_left,
      sub_eq_zero]
    exact Finset.sum_congr rfl fun i hi => (hT.2 _ (hf i hi) _ hv).symm
  exact sub_eq_zero.mp (eq_zero_of_bondInner_self _ (key _ (𝒮.oneForms.sub_mem hTs hTf)))
theorem supNorm_source_sub_target_le (b : 𝒮.FineBond) :
    supNorm ((b.source : 𝒮.Point) - (b.target : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.supNorm_source_sub_target <;> assumption
theorem supNorm_target_sub_source_le (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_le_cast (hM : 𝒮.L ^ 5 ≤ M) : (13 : ℝ) ≤ M := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_le_cast <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) :
    13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem mem_Ω_zero_of_near (hl : Torus.TorusLengthsStatement) {X : Set 𝒮.Point} (hM : (1 : ℝ) ≤ M)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < supSetDist X (𝒮.cubeComplementAt 0 (𝒮.Ω 0)))
    (x y : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ X)
    (hd : supNorm ((x : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mem_Ω_zero_of_near <;> assumption
theorem tsupport_partitionFn_subset_thicken (hl : Torus.TorusLengthsStatement)
    (Q : LevelCube 𝒮 M) (ς : ℝ) : tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem fineBond_ext {b b' : 𝒮.FineBond} (h₁ : b.source = b'.source) (h₂ : b.dir = b'.dir) :
    b = b' := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.fineBond_ext <;> assumption
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
theorem pushBonds_pullBonds (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ)
    (hi : ∀ b b' : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ tsupport φ →
      (b'.source : 𝒮.Point) ∈ tsupport φ → 𝔏.mapBond b' = 𝔏.mapBond b → b' = b)
    (A : 𝒮.FineBond → ℝ) (b : 𝒮.FineBond) :
    𝔏.pushBonds φ (𝔏.pullBonds φ A) b = φ (b.source : 𝒮.Point) ^ 2 * A b := by
  by_cases h : (b.source : 𝒮.Point) ∈ tsupport φ
  · unfold CubeSystem.pushBonds
    rw [pullBonds_mapBond 𝔏 φ A b fun b' h' e => hi b b' h h' e]
    ring
  · simp [CubeSystem.pushBonds, image_eq_zero_of_notMem_tsupport h]
structure TransferProps (Q : LevelCube 𝒮 M) (𝔏 : CubeSystem 𝒮) : Prop where
  injective : ∀ b b' : 𝒮.FineBond, (b.source : 𝒮.Point) ∈ tsupport Q.partitionFn →
    (b'.source : 𝒮.Point) ∈ tsupport Q.partitionFn → 𝔏.mapBond b' = 𝔏.mapBond b → b' = b
  pull_mem : ∀ A ∈ 𝒮.oneForms, 𝔏.pullBonds Q.partitionFn A ∈ 𝔏.forms
  push_mem : ∀ v ∈ 𝔏.forms, 𝔏.pushBonds Q.partitionFn v ∈ 𝒮.oneForms
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (b : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond b = b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mapBond_secondType <;> assumption
theorem transferProps_secondType (hl : Torus.TorusLengthsStatement) (hM : 𝒮.L ^ 5 ≤ M)
    (Q : LevelCube 𝒮 M)
    (hnear : Q.thicken (5 / 6) ⊆
      {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}) :
    TransferProps Q Q.secondTypeSystem := by
  refine ⟨fun b b' _ _ e => ?_, fun A hA => ?_, fun v hv => ?_⟩
  · have e' : Q.secondTypeSystem.mapBond b' = Q.secondTypeSystem.mapBond b := e
    rwa [mapBond_secondType, mapBond_secondType] at e'
  · have hval : ∀ c : 𝒮.FineBond,
        Q.secondTypeSystem.pullBonds Q.partitionFn A c =
          Q.partitionFn (c.source : 𝒮.Point) * A c := by
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
      hnear (tsupport_partitionFn_subset_thicken hl Q _ (subset_tsupport _ h0))
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
      have h₅ := supNorm_target_sub_source_le c
      push_cast at h₃ h₄ ⊢
      nlinarith
  · intro b hb
    have hv' : v ∈ 𝒮.oneForms ∧ _ := hv
    show Q.partitionFn (b.source : 𝒮.Point) * v (Q.secondTypeSystem.mapBond b) = 0
    rw [mapBond_secondType, hv'.1 b hb, mul_zero]
theorem transferProps_firstType (hl : Torus.TorusLengthsStatement) (hM : (1 : ℝ) ≤ M)
    (Q : LevelCube 𝒮 M) (hsecond : ¬Q.IsSecondType) (hF : Q.FirstTypeProperties)
    (hinner : Q.thicken (5 / 6) ⊆ Q.strictPts)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) <
      supSetDist (Q.thicken (5 / 6)) (𝒮.cubeComplementAt 0 (𝒮.Ω 0))) :
    TransferProps Q Q.system := by
  have hsys : Q.system = Q.firstTypeSystem := by
    unfold LevelCube.system
    exact if_neg hsecond
  obtain ⟨adm, hset⟩ := hF.setting_eq
  have hξ : Q.system.setting.ξ = 𝒮.ξ := by
    rw [hset]
    rfl
  have h0 : 𝒮.scale 0 = 𝒮.ξ := by simp [NestedRegions.scale, scaleSpacing]
  have hsub : tsupport Q.partitionFn ⊆ Q.strictPts :=
    (tsupport_partitionFn_subset_thicken hl Q _).trans hinner
  have hsite : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.strictPts →
      ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
        Q.system.embed x := by
    intro x hx
    have him := hF.embed_sites 0 (Or.inl (Nat.zero_le _))
    have hm : Q.system.embed x ∈
        (spacingLattice 4 Q.system.setting.side (𝒮.scale 0) : Set Q.system.setting.Point) ∩
          Q.localProj '' Q.liftedOpenCube := by
      rw [← him]
      exact ⟨x, ⟨by rw [h0]; exact x.2, hx⟩, rfl⟩
    have hm' : Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side Q.system.setting.ξ := by
      have h := hm.1
      rw [h0.trans hξ.symm] at h
      exact h
    exact Classical.epsilon_spec
      (p := fun y : Q.system.setting.FineSite =>
        (y : Q.system.setting.Point) = Q.system.embed x) ⟨⟨_, hm'⟩, rfl⟩
  have hbonds : ∀ b : Q.firstTypeSetting.FineBond, b ∈ Q.firstTypeSetting.bonds := by
    have key : ∀ 𝒯 : NestedRegions, 𝒯 = Q.torusSetting adm →
        ∀ b : 𝒯.FineBond, b ∈ 𝒯.bonds := by
      rintro _ rfl b
      exact mem_univ _
    refine key _ ?_
    unfold LevelCube.firstTypeSetting
    exact dif_pos adm
  have hall : ∀ 𝔏 : CubeSystem 𝒮, 𝔏 = Q.firstTypeSystem →
      ∀ f : 𝔏.setting.FineBond → ℝ, f ∈ 𝔏.forms := by
    rintro _ rfl f b hb
    exact absurd (hbonds b) hb
  refine ⟨fun b b' hb hb' e => ?_, fun A _ => hall _ hsys _, fun v _ b hb => ?_⟩
  · have e₁ : Q.system.mapSite b'.source = Q.system.mapSite b.source :=
      congrArg LatticeBond.source e
    have e₂ : (Q.system.mapBond b').dir = (Q.system.mapBond b).dir :=
      congrArg LatticeBond.dir e
    have e₃ : Q.system.embed (b'.source : 𝒮.Point) = Q.system.embed (b.source : 𝒮.Point) := by
      rw [← hsite _ (hsub hb'), ← hsite _ (hsub hb), e₁]
    exact fineBond_ext (Subtype.ext (hF.embed_bijective.injOn (hsub hb') (hsub hb) e₃)) e₂
  · show Q.partitionFn (b.source : 𝒮.Point) * v (Q.system.mapBond b) = 0
    by_contra hne
    have h₀ : Q.partitionFn (b.source : 𝒮.Point) ≠ 0 := left_ne_zero_of_mul hne
    have ht : (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6) :=
      tsupport_partitionFn_subset_thicken hl Q _ (subset_tsupport _ h₀)
    have hz : supNorm ((b.source : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by
      rw [sub_self, (hl 4 𝒮.side 𝒮.side_pos).1.supNorm_zero]
      exact 𝒮.ξ_pos.le
    exact hb (𝒮.mem_bonds_of_mem b (mem_Ω_zero_of_near hl hM hway b.source b.source ht hz)
      (mem_Ω_zero_of_near hl hM hway b.source b.target ht (supNorm_source_sub_target_le b)))
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
      (hpos.in_interior Q hQ) (hpos.first_kind Q ⟨hQ, h⟩).away
theorem inv_spec (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) :
    𝔏.inv u ∈ 𝔏.forms ∧ 𝔏.op (𝔏.inv u) = u := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.cubeInv_spec <;> assumption
theorem claim_holds (hcell : CellStructure.CellStructureClaim)
    (hmaps : PartitionCubes.cubeFunctionsAndMaps) (hgeom : CubeGeometry.GeometryStatement)
    (hlocal : CubeOperators.RegularityClaim) (hsum : PartitionCubes.DefectEqFinsumKernels)
    (hl : Torus.TorusLengthsStatement) : Claim := by
  intro K m M R₁ 𝒮 hseq hfloor
  have hM5 : 𝒮.L ^ 5 ≤ M := by
    have h : (𝒮.L : ℝ) ^ 5 ≤ M := (le_max_left _ _).trans hfloor
    exact_mod_cast h
  have hgeo := hgeom.2 K m M R₁ 𝒮 hseq hM5
  obtain ⟨hblock, -, -, -, -, hfirst, htrans, -, -⟩ := hmaps.2 𝒮 K m M R₁ hseq
  obtain ⟨-, -, -, -, -, -, -, hP, -⟩ := hcell 𝒮
  have hlocalQ : ∀ Q ∈ active 𝒮 M, (CubeOperators.chosenConstants 𝒮.L).CubeHolds Q :=
    fun Q hQ => (hlocal 𝒮.L 𝒮.odd_L 𝒮.thirteen_le_L).holds K m M R₁ 𝒮 rfl hseq hfloor Q hQ
  have : Finite 𝒮.FineBond := finite_fineBond hl 𝒮
  have hσ : ∀ n, 0 < cubeSide 𝒮 M n := fun n =>
    lt_of_lt_of_le (by have := 𝒮.ξ_pos; positivity) (thirteen_mul_ξ_le_cubeSide hM5 n)
  have : Finite (LevelCube 𝒮 M) :=
    finite_levelCube fun n hn => cornerSet_finite hl n (hσ n) (hblock n hn).side_even
  have hfin : (active 𝒮 M).Finite := Set.toFinite _
  have hF : ∀ {Q}, Q ∈ hfin.toFinset → Q ∈ active 𝒮 M := fun h => hfin.mem_toFinset.1 h
  have hfacts := transferProps hl hM5 hgeo.positions hfirst
  have hform : ∀ Q ∈ active 𝒮 M, ∀ A ∈ 𝒮.oneForms,
      Q.system.inv (Q.system.pullBonds Q.partitionFn A) ∈ Q.system.forms ∧
        Q.system.op (Q.system.inv (Q.system.pullBonds Q.partitionFn A)) =
          Q.system.pullBonds Q.partitionFn A := fun Q hQ A hA =>
    inv_spec _ (hlocalQ Q hQ).invertible ((hfacts Q hQ).pull_mem A hA)
  have hterm : ∀ Q ∈ active 𝒮 M, ∀ A ∈ 𝒮.oneForms, Q.invTerm A ∈ 𝒮.oneForms :=
    fun Q hQ A hA => (hfacts Q hQ).push_mem _ (hform Q hQ A hA).1
  have hsumG : ∀ A, approxInverse 𝒮 M A = ∑ Q ∈ hfin.toFinset, Q.invTerm A := by
    intro A
    funext b
    rw [Finset.sum_apply]
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hsumR : ∀ A b, remainderOp 𝒮 M A b = ∑ Q ∈ hfin.toFinset, Q.remTerm A b := fun A b =>
    finsum_mem_eq_finite_toFinset_sum _ hfin
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    rw [hsumG, map_finset_sum_of_selfAdjointOn hP.basic_symmetric _ _
      fun Q hQ => hterm Q (hF hQ) A hA]
    funext b
    rw [Finset.sum_apply, Pi.sub_apply, hsumR]
    have e : ∀ Q ∈ hfin.toFinset, baseOp (Q.invTerm A) b =
        Q.partitionFn (b.source : 𝒮.Point) ^ 2 * A b - Q.remTerm A b := by
      intro Q hQ
      simp only [LevelCube.remTerm, LevelCube.defectOp, (hform Q (hF hQ) A hA).2, Pi.sub_apply]
      rw [pushBonds_pullBonds _ _ (hfacts Q (hF hQ)).injective]
      simp only [LevelCube.invTerm]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    by_cases hb : b ∈ 𝒮.bonds
    · have h := hgeo.partition.sum_squares_at_bonds b hb
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
      rw [h, one_mul]
    · rw [hA b hb, mul_zero]
  · intro A hA b
    have hprod : active 𝒮 M ×ˢ active 𝒮 M =
        ((hfin.toFinset ×ˢ hfin.toFinset : Finset (LevelCube 𝒮 M × LevelCube 𝒮 M)) :
          Set (LevelCube 𝒮 M × LevelCube 𝒮 M)) := by
      rw [Finset.coe_product, hfin.coe_toFinset]
    rw [hsumR, hprod, finsum_mem_coe_finset, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [LevelCube.remTerm, hsum K m M R₁ 𝒮 hseq hfloor Q (hF hQ) _ (hform Q (hF hQ) A hA).1 b]
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  · intro A hA A' hA'
    rw [hsumG, hsumG, bondInner_finset_sum_left, bondInner_comm A, bondInner_finset_sum_left]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    have hadj := (htrans Q (hF hQ) Q.partitionFn (tsupport_partitionFn_subset_thicken hl Q _)).bonds
    calc bondInner (Q.invTerm A) A'
        = bondInner (Q.system.inv (Q.system.pullBonds Q.partitionFn A))
            (Q.system.pullBonds Q.partitionFn A') := hadj _ (hform Q (hF hQ) A hA).1 A' hA'
      _ = bondInner (Q.system.pullBonds Q.partitionFn A)
            (Q.system.inv (Q.system.pullBonds Q.partitionFn A')) :=
          (hlocalQ Q (hF hQ)).symmetric _ ((hfacts Q (hF hQ)).pull_mem A hA) _
            ((hfacts Q (hF hQ)).pull_mem A' hA')
      _ = bondInner (Q.system.inv (Q.system.pullBonds Q.partitionFn A'))
            (Q.system.pullBonds Q.partitionFn A) := bondInner_comm _ _
      _ = bondInner (Q.invTerm A') A := (hadj _ (hform Q (hF hQ) A' hA').1 A hA).symm
end ApproxInverseLaws
end YangMills.Construction
