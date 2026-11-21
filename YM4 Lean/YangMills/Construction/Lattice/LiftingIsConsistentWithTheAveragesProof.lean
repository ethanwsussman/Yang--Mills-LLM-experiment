import YangMills.Construction.Lattice.AverageOfTheLiftOfOrder
import YangMills.Construction.Lattice.BondsInsideAndOverInTermsOfBlocks
import YangMills.Construction.Lattice.BondwiseAveragesAreTheBlockAverages
import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.Lattice.LiftOfOrderIsAConfiguration
import YangMills.Construction.Lattice.LiftOfOrderOnTheBareLattice
import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAverages
import YangMills.Construction.Lattice.LiftsClassesAndSitesInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace LiftAveragesProof
variable {L m K k : ℕ}
theorem compactGaugeGroup_subset_complexGaugeGroup : compactGaugeGroup ⊆ complexGaugeGroup :=
  fun _ h => (Matrix.mem_specialUnitaryGroup_iff.mp h).2
theorem isGaugeField_complex_of_compact {i : ℤ} {ℬ : Set (Bond L m i)}
    {U : Bond L m i → Matrices.ComplexMatrix2}
    (h : IsGaugeField compactGaugeGroup ℬ U) : IsGaugeField complexGaugeGroup ℬ U :=
  ⟨fun b hb => compactGaugeGroup_subset_complexGaugeGroup (h.1 b hb), h.2⟩
theorem isGaugeField_congr {i : ℤ} {𝒢 : Set Matrices.ComplexMatrix2} {ℬ : Set (Bond L m i)}
    {U U' : Bond L m i → Matrices.ComplexMatrix2} (hcl : IsReversalClosed ℬ)
    (h : ∀ b ∈ ℬ, U b = U' b)
    (hU : IsGaugeField 𝒢 ℬ U) : IsGaugeField 𝒢 ℬ U' :=
  ⟨fun b hb => h b hb ▸ hU.1 b hb, fun b hb => by
    rw [← h b hb, ← h _ (hcl b hb)]
    exact hU.2 b hb⟩
theorem coincides_refl {i : ℤ} (W : PartialGaugeField L m i) : W.Coincides W :=
  ⟨rfl, fun _ _ => rfl⟩
theorem coincides_symm {i : ℤ} {W W' : PartialGaugeField L m i} (h : W.Coincides W') :
    W'.Coincides W :=
  ⟨h.1.symm, fun b hb => (h.2 b (h.1 ▸ hb)).symm⟩
theorem coincides_trans {i : ℤ} {W W' W'' : PartialGaugeField L m i} (h : W.Coincides W')
    (h' : W'.Coincides W'') : W.Coincides W'' :=
  ⟨h.1.trans h'.1, fun b hb => (h.2 b hb).trans (h'.2 b (h.1 ▸ hb))⟩
theorem extendByOne_congr {i : ℤ} {P : Set (Bond L m i)}
    {U U' : Bond L m i → Matrices.ComplexMatrix2}
    (h : ∀ b ∈ P, U b = U' b) : onSetElseOne P U = onSetElseOne P U' := by
  funext b
  unfold onSetElseOne
  split_ifs with hb
  · exact h b hb
  · rfl
theorem partialBlockAverage_congr {i i' : ℤ} (ω : ℝ) {W W' : PartialGaugeField L m i}
    (h : W.Coincides W') :
    (realPartialBlockAverage ω W : PartialGaugeField L m i').Coincides
      (realPartialBlockAverage ω W') := by
  refine ⟨by simp only [realPartialBlockAverage, h.1], fun c hc => ?_⟩
  have hc' : bondsInDoubleBlock c ⊆ W.support := hc
  show blockAverage ω (onSetElseOne (bondsInDoubleBlock c) W.field) c =
    blockAverage ω (onSetElseOne (bondsInDoubleBlock c) W'.field) c
  rw [extendByOne_congr fun b hb => h.2 b (hc' hb)]
theorem complexPartialBlockAverage_congr {i i' : ℤ} {W W' : PartialGaugeField L m i}
    (h : W.Coincides W') :
    (complexPartialBlockAverage W : PartialGaugeField L m i').Coincides
      (complexPartialBlockAverage W') := by
  have key : ∀ c : Bond L m i', bondsInDoubleBlock c ⊆ W.support →
      onSetElseOne (bondsInDoubleBlock c) W.field =
        onSetElseOne (bondsInDoubleBlock c) W'.field :=
    fun c hc => extendByOne_congr fun b hb => h.2 b (hc hb)
  refine ⟨?_, fun c hc => ?_⟩
  · ext c
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h.1 ▸ h1, key c h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩
      have h1' : bondsInDoubleBlock c ⊆ W.support := h.1.symm ▸ h1
      exact ⟨h1', (key c h1').symm ▸ h2⟩
  · show complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) W.field) c =
      complexBlockAverage (onSetElseOne (bondsInDoubleBlock c) W'.field) c
    rw [key c hc.1]
theorem cast_partialBlockAverage {a a' b b' : ℤ} (ω : ℝ) (ha : a = a') (hb : b = b')
    (W : PartialGaugeField L m a)
    (e₁ : PartialGaugeField L m b = PartialGaugeField L m b')
    (e₂ : PartialGaugeField L m a = PartialGaugeField L m a') :
    cast e₁ (realPartialBlockAverage ω W : PartialGaugeField L m b) =
      realPartialBlockAverage ω (cast e₂ W) := by
  subst ha hb
  rfl
theorem cast_complexPartialBlockAverage {a a' b b' : ℤ} (ha : a = a') (hb : b = b')
    (W : PartialGaugeField L m a)
    (e₁ : PartialGaugeField L m b = PartialGaugeField L m b')
    (e₂ : PartialGaugeField L m a = PartialGaugeField L m a') :
    cast e₁ (complexPartialBlockAverage W : PartialGaugeField L m b) =
      complexPartialBlockAverage (cast e₂ W) := by
  subst ha hb
  rfl
theorem cast_isRestriction {a b : ℤ} (h : a = b) {W W' : PartialGaugeField L m a}
    (e : PartialGaugeField L m a = PartialGaugeField L m b)
    (hr : W'.IsRestriction W) : (cast e W').IsRestriction (cast e W) := by
  subst h
  exact hr
theorem barePartialBlockAverageIter_succ (ω : ℝ) (U : PartialGaugeField L m (levelDepth K 0))
    (j : ℕ) :
    barePartialBlockAverageIter (K := K) ω U (j + 1) =
      realPartialBlockAverage ω (barePartialBlockAverageIter (K := K) ω U j) :=
  cast_partialBlockAverage ω (by rw [Nat.zero_add]) (by rw [Nat.zero_add]) _ _ _
theorem bareComplexPartialIter_succ (U : PartialGaugeField L m (levelDepth K 0)) (j : ℕ) :
    bareComplexPartialIter (K := K) U (j + 1) =
      complexPartialBlockAverage (bareComplexPartialIter (K := K) U j) :=
  cast_complexPartialBlockAverage (by rw [Nat.zero_add]) (by rw [Nat.zero_add]) _ _ _
theorem shiftBy_eq {j : ℕ} (hFacts : LiftCosetFacts L m K j) (hL : (L : ℝ) ≠ 0)
    (x : FourTorus L m) (r : Fin 4 → ℝ) :
    shiftBy L m K j x r =
      x + fun μ => ((meshSize L (levelDepth K j) * r μ : ℝ) : AddCircle (torusSide L m)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hFacts
  obtain ⟨w₀, hw₀⟩ := h1 x
  have hw : IsLevelLift L m K j x w₀ := by
    exact show w₀ ∈ liftSetAtLevel L m K j x from by
      rw [hw₀]
      exact ⟨0, fun μ => by simp⟩
  have hr : IsLevelLift L m K j
      (fun μ => ((meshSize L (levelDepth K j) * r μ : ℝ) : AddCircle (torusSide L m))) r := by
    refine ⟨fun μ => meshSize L (levelDepth K j) * r μ, fun μ => rfl, fun μ => ?_⟩
    simp only [toLevelUnits, meshSize]
    rw [← mul_assoc, ← zpow_add₀ hL]
    simp
  rw [h5 x r w₀ hw]
  exact ((h3 _ _).mp (h4 _ _ _ _ hw hr).1).symm
theorem unitStep_coe (i : ℤ) (μ : Fin 4) :
    ((unitStep L m i μ : Site L m i) : FourTorus L m) =
      fun ν => ((((1 : ℝ) * meshSize L i) • coordVec μ) ν : AddCircle (torusSide L m)) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis, coordVec]
  · simp [unitStep, pointOnAxis, coordVec, Pi.single_eq_of_ne h]
theorem neg_unitStep_coe (i : ℤ) (μ : Fin 4) :
    -((unitStep L m i μ : Site L m i) : FourTorus L m) =
      fun ν => ((((-1 : ℝ) * meshSize L i) • coordVec μ) ν : AddCircle (torusSide L m)) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis, coordVec]
  · simp [unitStep, pointOnAxis, coordVec, Pi.single_eq_of_ne h]
theorem exists_sign_axis (s : Conventions.StandingParameters) {i : ℕ} (d : s.BondAt i) :
    ∃ σ : ℝ, s.HasSignAndAxis d σ d.axis := by
  rcases d.isNeighbour.choose_spec with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    have h' := congrArg (fun x : Site s.L s.m (levelDepth s.K i) => (x : FourTorus s.L s.m)) h
    simp only [AddSubgroup.coe_sub] at h'
    rw [h', unitStep_coe]
    rfl
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h' := congrArg (fun x : Site s.L s.m (levelDepth s.K i) => (x : FourTorus s.L s.m)) h
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg] at h'
    rw [h', neg_unitStep_coe]
    rfl
theorem axis_eq_of_hasSignAndAxis (hEnd : BondEndpointsOrientation.Statement)
    (s : Conventions.StandingParameters)
    {i : ℕ} (hi : i ≤ (s.K : ℕ)) (d : s.BondAt i) {σ : ℝ} {μ : Fin 4}
    (h : s.HasSignAndAxis d σ μ) : d.axis = μ := by
  obtain ⟨σ', h'⟩ := exists_sign_axis s d
  obtain ⟨p, -, hu⟩ := (hEnd s i hi).2.2.2 d |>.1
  have e1 := hu (σ, μ) h
  have e2 := hu (σ', d.axis) h'
  exact congrArg Prod.snd (e2.trans e1.symm)
theorem positivelyOriented_isPositivelyOriented {i : ℤ} {c : Bond L m i}
    (hx : Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented) :
    c.positivelyOriented.IsPositivelyOriented := by
  unfold Bond.positivelyOriented
  split_ifs with h
  · exact h
  · rcases hx with ⟨a, -⟩ | ⟨a, -⟩
    · exact absurd a h
    · exact a
theorem positivelyOriented_mem {i : ℤ} {ℬ : Set (Bond L m i)} (hcl : IsReversalClosed ℬ)
    {c : Bond L m i} (hc : c ∈ ℬ) : c.positivelyOriented ∈ ℬ := by
  unfold Bond.positivelyOriented
  split_ifs with h
  · exact hc
  · exact hcl c hc
theorem matchesScaledBond_of_covers
    (hTwo : OrderLiftCases)
    (hEnd : BondEndpointsOrientation.Statement)
    (hBlocks : CoarseCentreProperties)
    (hUnits : RescaledLatticeStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) {j : ℕ}
    (hjk : j ≤ k)
    (hkK : k ≤ K) (b : BondAtLevel L m K j) (c : BondAtLevel L m K k) (hbc : CoversBond c b) :
    MatchesScaledBond j b c := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩
  obtain ⟨-, hFacts, hSites, -, -⟩ := hUnits L m K hL hm hK j j le_rfl (hjk.trans hkK)
  obtain ⟨σ, μ, hσ, hb⟩ := (hSites.2.2.2.2.2.2.1 b.source b.target).mp ⟨b, rfl, rfl⟩
  rw [Nat.sub_self, pow_zero, mul_one] at hb
  have hB := hBlocks L m K hL hm hK j k hjk hkK
  obtain ⟨hct, hch⟩ := ((hTwo L m K hL hm hK).1 j k hjk hkK).1 b c hbc
  have hEndK := (hEnd s k hkK).2.2.2 c
  rcases hB.2.2.2.2.1 b σ μ hσ hb with heq | ⟨hstep, -, c₀, ht, hh, hpos, -⟩
  · exact absurd (hct.trans (heq.symm.trans hch.symm)) hEndK.2.1
  · have hc₀ : c₀ = c := Bond.ext (ht.trans hct.symm) (hh.trans hch.symm)
    subst hc₀
    have hcstep : (c₀.target : FourTorus L m) =
        shiftBy L m K j c₀.source ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) := by
      rw [hh, ht]
      exact hstep
    have hsb : s.HasSignAndAxis (k := j) b σ μ := by
      refine ⟨hσ, ?_⟩
      have h2 : (b.target : FourTorus L m) - b.source =
          fun ν => ((meshSize L (levelDepth K j) * (σ • coordVec μ) ν : ℝ) :
            AddCircle (torusSide L m)) := by
        rw [hb, shiftBy_eq hFacts hL0]
        abel
      refine h2.trans (funext fun ν => ?_)
      show ((meshSize L (levelDepth K j) * (σ • coordVec μ) ν : ℝ) :
          AddCircle (torusSide L m)) =
        (((σ * meshSize L (levelDepth K j)) • coordVec μ) ν : ℝ)
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hsc : s.HasSignAndAxis (k := k) c₀ σ μ := by
      refine ⟨hσ, ?_⟩
      have h2 : (c₀.target : FourTorus L m) - c₀.source =
          fun ν => ((meshSize L (levelDepth K j) *
            ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) ν : ℝ) : AddCircle (torusSide L m)) := by
        rw [hcstep, shiftBy_eq hFacts hL0]
        abel
      refine h2.trans (funext fun ν => ?_)
      show ((meshSize L (levelDepth K j) * ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) ν : ℝ) :
          AddCircle (torusSide L m)) =
        (((σ * meshSize L (levelDepth K k)) • coordVec μ) ν : ℝ)
      congr 1
      have hsp : meshSize L (levelDepth K j) * (L : ℝ) ^ (k - j) =
          meshSize L (levelDepth K k) := by
        simp only [meshSize, levelDepth]
        rw [← zpow_natCast, ← zpow_add₀ hL0, Nat.cast_sub hjk]
        congr 1
        ring
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hsp]
      ring
    refine ⟨⟨σ, μ, hσ, hb, hcstep⟩, ?_, hpos⟩
    exact (axis_eq_of_hasSignAndAxis hEnd s hkK c₀ hsc).trans
      (axis_eq_of_hasSignAndAxis hEnd s (hjk.trans hkK) b hsb).symm
theorem levelLiftsConsistent_of_steps {𝒢 : Set Matrices.ComplexMatrix2}
    (avg : ∀ j : ℕ, PartialGaugeField L m (levelDepth K j) →
      PartialGaugeField L m (levelDepth K (j + 1)))
    (W : ∀ j : ℕ, PartialGaugeField L m (levelDepth K j))
    (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (hClosed : ∀ j ≤ k, IsReversalClosed (bondsInsideOrOverCoarse j 𝒞))
    (hConf : ∀ j ≤ k, IsGaugeField 𝒢 (bondsInsideOrOverCoarse j 𝒞) (orderLift j V))
    (hOverV : ∀ j ≤ k, ∀ (b : BondAtLevel L m K j), ∀ c ∈ 𝒞, CoversBond c b →
      orderLift j V b = V c)
    (hOut : ∀ j ≤ k, ∀ (b : BondAtLevel L m K j) (c : BondAtLevel L m K k), c ∉ 𝒞 →
      CoversBond c b → b ∉ bondsInsideOrOverCoarse j 𝒞)
    (h0 : (W 0).Coincides (bareLiftPartial (K := K) ⟨𝒞, V⟩))
    (hBare : (bareLiftPartial (K := K)
      (⟨𝒞, V⟩ : PartialGaugeField L m (levelDepth K k))).Coincides
      (orderLiftPartial 0 𝒞 V))
    (hTop : (orderLiftPartial k 𝒞 V).Coincides ⟨𝒞, V⟩)
    (hCongr : ∀ j (A B : PartialGaugeField L m (levelDepth K j)), A.Coincides B →
      (avg j A).Coincides (avg j B))
    (hNext : ∀ j, W (j + 1) = avg j (W j))
    (hOne : ∀ j < k, (avg j (orderLiftPartial j 𝒞 V)).Coincides
      (orderLiftPartial (j + 1) 𝒞 V)) :
    (∀ j ≤ k, (W j).Coincides (orderLiftPartial j 𝒞 V)) ∧
      LevelLiftsConsistent 𝒢 avg W 𝒞 V := by
  have hSame : ∀ j ≤ k, (W j).Coincides (orderLiftPartial j 𝒞 V) := by
    intro j
    induction j with
    | zero => exact fun _ => coincides_trans h0 hBare
    | succ j ih =>
      intro hj
      rw [hNext j]
      exact coincides_trans (hCongr j _ _ (ih (by omega))) (hOne j (by omega))
  refine ⟨hSame, fun j hj => ?_, h0, coincides_trans (hSame k le_rfl) hTop, fun j _ => ?_⟩
  · have hS := hSame j hj
    have hb : (W j).support = bondsInsideOrOverCoarse j 𝒞 := hS.1
    have hcl : IsReversalClosed (W j).support := hb ▸ hClosed j hj
    refine ⟨hcl, ?_, hS, fun b => ⟨fun hin => ?_, fun c hc hbc => ?_, fun c hc hbc hmem => ?_⟩⟩
    · exact isGaugeField_congr hcl (fun b hb' => (hS.2 b hb').symm)
        (hb.symm ▸ hConf j hj)
    · have hmem : b ∈ (W j).support := hb ▸ Or.inl hin
      exact ⟨hmem, (hS.2 b hmem).trans (if_pos hin)⟩
    · have hmem : b ∈ (W j).support := hb ▸ Or.inr ⟨c, hc, hbc⟩
      exact ⟨hmem, (hS.2 b hmem).trans (hOverV j hj b c hc hbc)⟩
    · exact hOut j hj b c hc hbc (hb ▸ hmem)
  · rw [hNext j]
    exact coincides_refl _
theorem bareLift_support_and_values (hTwo : OrderLiftCases)
    (hBareLift : BareOrderLiftEqBareLift)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) (hkK : k ≤ K)
    (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (hrev : IsReversalClosed 𝒞) (hVc : IsGaugeField complexGaugeGroup 𝒞 V) :
    bareLiftSupport (K := K) 𝒞 = bondsInsideOrOverCoarse 0 𝒞 ∧
      bareLiftSupport (K := K) 𝒞 = {b | ∀ c : BondAtLevel L m K k, CoversBond c b → c ∈ 𝒞} ∧
      ∀ b ∈ bondsInsideOrOverCoarse 0 𝒞, orderLift 0 V b = bareLiftFromLevel (K := K) V b := by
  cases k with
  | zero =>
    obtain ⟨-, -, hSelf, hC⟩ := (hTwo L m K hL hm hK).2 0 hkK
    obtain ⟨hB, hv⟩ := hC 𝒞 V hrev hVc
    refine ⟨hB.symm, ?_, fun b hb => hv b (hB ▸ hb)⟩
    show 𝒞 = _
    ext b
    constructor
    · intro hb c hc
      rw [(hSelf b c).mp hc]
      exact hb
    · intro h
      exact h b ((hSelf b b).mpr rfl)
  | succ n =>
    obtain ⟨-, -, -, h1, h2, h3⟩ :=
      hBareLift L m K hL hm hK (n + 1) (by omega) hkK 𝒞 V hrev hVc
    exact ⟨h1.symm, h2, h3⟩
end LiftAveragesProof
open LiftAveragesProof in
theorem liftConsistentWithAverages_holds
    (hTwo : OrderLiftCases)
    (hEnd : BondEndpointsOrientation.Statement)
    (hBareLift : BareOrderLiftEqBareLift)
    (hOver : BondPositionByBlocks)
    (hBlocks : CoarseCentreProperties)
    (hBondwise : PartialAveragesAgreeWithBlockAverage.Statement)
    (hConfig : OrderLiftIsGaugeField)
    (hStep : OrderLiftAverageStep)
    (hUnits : RescaledLatticeStatement) :
    LiftConsistentWithAverages := by
  intro L m K hL hm hK k hkK 𝒞 hrev V hVor
  have hVc : IsGaugeField complexGaugeGroup 𝒞 V :=
    hVor.elim isGaugeField_complex_of_compact id
  let s : Conventions.StandingParameters := ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩
  have hCfg := fun (j : ℕ) (hj : j ≤ k) => hConfig L m K hL hm hK j k hj hkK 𝒞 hrev V hVc
  have hT := fun (j : ℕ) (hj : j ≤ k) => (hTwo L m K hL hm hK).1 j k hj hkK
  obtain ⟨hTopB, hTopV⟩ := ((hTwo L m K hL hm hK).2 k hkK).2.2.2 𝒞 V hrev hVc
  obtain ⟨hdom, hdom2, hval⟩ :=
    bareLift_support_and_values hTwo hBareLift hL hm hK hkK 𝒞 V hrev hVc
  have hClosed : ∀ j ≤ k, IsReversalClosed (bondsInsideOrOverCoarse j 𝒞) :=
    fun j hj => (hCfg j hj).2.1.1
  have hConfC : ∀ j ≤ k,
      IsGaugeField complexGaugeGroup (bondsInsideOrOverCoarse j 𝒞) (orderLift j V) :=
    fun j hj => (hCfg j hj).2.1.2.2.1
  have hClosed0 : IsReversalClosed (bareLiftSupport (K := K) 𝒞) := by
    rw [hdom]
    exact hClosed 0 (Nat.zero_le k)
  have hConfBare : ∀ 𝒢 : Set Matrices.ComplexMatrix2,
      IsGaugeField 𝒢 (bondsInsideOrOverCoarse 0 𝒞) (orderLift 0 V) →
      IsGaugeField 𝒢 (bareLiftSupport (K := K) 𝒞) (bareLiftFromLevel (K := K) V) := by
    intro 𝒢 h
    refine isGaugeField_congr hClosed0 (fun b hb => hval b (hdom ▸ hb)) ?_
    rw [hdom]
    exact h
  have hPartA : ∀ j ≤ k, BlocksPartitionLevel L m K j k ∧
      ∀ b : BondAtLevel L m K j, InsideOrCoveringDichotomy j k b := by
    intro j hj
    have hB := hBlocks L m K hL hm hK j k hj hkK
    obtain ⟨hEnds, hUnique, hNone, -⟩ := hT j hj
    have hHalf := (hUnits L m K hL hm hK j k hj hkK).2.2.2.2.2.1
    have hStepOf := fun (b : BondAtLevel L m K j) (c : BondAtLevel L m K k)
      (hbc : CoversBond c b) =>
        matchesScaledBond_of_covers hTwo hEnd hBlocks hUnits hL hm hK hj hkK b c hbc
    refine ⟨⟨fun y => ⟨?_, ?_⟩, hB.2.2.1⟩, fun b => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [(hB.2.1 y).2]
      refine ⟨_, 0, ?_, rfl⟩
      simpa [supNormVec] using hHalf
    · rw [(hB.2.1 y).1]
      rintro z ⟨x, hx, -⟩
      exact ⟨x, hx⟩
    · rcases (hOver L m K hL hm hK j k hj hkK b).2.2 with ⟨y, hy⟩ | ⟨c, hc⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨c, hc, fun c' h' => hUnique b c' c h' hc⟩
    · rintro ⟨⟨y, hy⟩, ⟨c, hc⟩⟩
      exact hNone b ⟨y, hy⟩ c hc
    · intro c hc
      have hr := (hCfg j hj).1.2 b c hc
      exact ⟨hStepOf b c hc, hr, fun c' h' => hUnique b.opposite c' c.opposite h' hr,
        hStepOf b.opposite c.opposite hr⟩
    · exact fun y => (hCfg j hj).1.1 y b
  have hPartB : LiftsAreGaugeFields 𝒞 V :=
    ⟨hdom, hdom2, hClosed0, hConfBare _ (hConfC 0 (Nat.zero_le k)),
      fun hR => hConfBare _ ((hCfg 0 (Nat.zero_le k)).2.1.2.2.2 hR),
      fun j hj => ⟨hClosed j hj, hConfC j hj, (hCfg j hj).2.1.2.2.2⟩, hval, hTopV, hTopB⟩
  have hPartC : ∀ j < k, AverageStepOfLift j 𝒞 V := by
    intro j hj
    obtain ⟨-, -, hC, hR⟩ := hStep L m K hL hm j k hj hkK 𝒞 hrev V hVc
    refine ⟨⟨hC.1, fun b hb => hC.2 b (by rw [← hC.1]; exact hb)⟩, fun c hc => ?_,
      fun hreal => ?_⟩
    · have hmem : c ∈ (complexPartialBlockAverage (orderLiftAsPartialField j 𝒞 V) :
          PartialGaugeField L m (levelDepth K (j + 1))).support := by
        rw [hC.1]
        exact hc
      exact hmem.2
    · obtain ⟨hRb, hRv⟩ := hR hreal
      refine ⟨⟨hRb, fun c hc => (hRv c (by rw [← hRb]; exact hc)).1⟩,
        fun c hc => ⟨(hRv c hc).2, ?_⟩⟩
      have hp : c.positivelyOriented ∈ bondsInsideOrOverCoarse (j + 1) 𝒞 :=
        positivelyOriented_mem (hClosed (j + 1) hj) hc
      have hpos : c.positivelyOriented.IsPositivelyOriented :=
        positivelyOriented_isPositivelyOriented
          ((hEnd s (j + 1) (Nat.succ_le_of_lt (lt_of_lt_of_le hj hkK))).2.2.2 c).2.2.2.2.2
      have hcase := (hRv _ hp).2
      have hpp : c.positivelyOriented.positivelyOriented = c.positivelyOriented := if_pos hpos
      unfold partialBlockAverageCase at hcase
      rw [hpp] at hcase
      show blockAverage (Averaging.smoothingRadius L)
          (onSetElseOne (bondsInDoubleBlock c.positivelyOriented) (orderLift j V))
          c.positivelyOriented = _
      have hmap : ∀ U : BondAtLevel L m K j → Matrices.ComplexMatrix2,
          blockAverage (Averaging.smoothingRadius L) U c.positivelyOriented =
            blockAverageOnPositive (Averaging.smoothingRadius L) U c.positivelyOriented :=
        fun U => if_pos hpos
      rw [hmap, blockAverageOnPositive_eq_byCase, hcase]
  have hOverV : ∀ j ≤ k, ∀ (b : BondAtLevel L m K j), ∀ c ∈ 𝒞, CoversBond c b →
      orderLift j V b = V c := fun j hj b c hc hbc =>
    ((hT j hj).2.2.2 𝒞 V hrev hVc b (Or.inr ⟨c, hc, hbc⟩)).2.2.2.2.1 c hc hbc
  have hOut : ∀ j ≤ k, ∀ (b : BondAtLevel L m K j) (c : BondAtLevel L m K k), c ∉ 𝒞 →
      CoversBond c b → b ∉ bondsInsideOrOverCoarse j 𝒞 := by
    intro j hj b c hc hbc hmem
    rcases hmem with hin | ⟨c', hc', hbc'⟩
    · exact (hT j hj).2.2.1 b hin c hbc
    · exact hc ((hT j hj).2.1 b c c' hbc hbc' ▸ hc')
  have hBareSame : (bareLiftPartial (K := K)
      (⟨𝒞, V⟩ : PartialGaugeField L m (levelDepth K k))).Coincides
        (orderLiftPartial 0 𝒞 V) :=
    ⟨hdom, fun b hb => (hval b (hdom ▸ hb)).symm⟩
  have hTopSame : (orderLiftPartial k 𝒞 V).Coincides ⟨𝒞, V⟩ :=
    ⟨hTopB, fun b hb => hTopV b (hTopB ▸ hb)⟩
  have hCompl := levelLiftsConsistent_of_steps (𝒢 := complexGaugeGroup)
    (fun _ => complexPartialBlockAverage)
    (complexLevelLifts 𝒞 V) 𝒞 V hClosed hConfC hOverV hOut (coincides_refl _) hBareSame
    hTopSame
    (fun j A B h => complexPartialBlockAverage_congr h)
    (fun j => bareComplexPartialIter_succ _ j)
    (fun j hj => (hPartC j hj).1)
  have hRealAll := fun hreal : IsGaugeField compactGaugeGroup 𝒞 V =>
    levelLiftsConsistent_of_steps (𝒢 := compactGaugeGroup)
      (fun _ => realPartialBlockAverage (Averaging.smoothingRadius L))
      (compactLevelLifts 𝒞 V) 𝒞 V hClosed (fun j hj => (hCfg j hj).2.1.2.2.2 hreal) hOverV hOut
      (coincides_refl _) hBareSame hTopSame (fun j A B h => partialBlockAverage_congr _ h)
      (fun j => barePartialBlockAverageIter_succ _ _ j) (fun j hj => ((hPartC j hj).2.2 hreal).1)
  refine ⟨hPartA, hPartB, hPartC, hCompl.2, fun hr => ⟨(hRealAll hr).2, fun j hj =>
    coincides_trans ((hRealAll hr).1 j hj) (coincides_symm (hCompl.1 j hj))⟩, ?_, ?_⟩
  · intro h𝒞 hVr
    subst h𝒞
    have hRA := hRealAll hVr
    have hU := fun (j : ℕ) (hj : j ≤ k) => (hCfg j hj).2.2 rfl
    have hbareEq : bareLiftFromLevel (K := K) V = orderLift 0 V :=
      funext fun b => (hval b (by rw [(hU 0 (Nat.zero_le k)).1]; trivial)).symm
    have hU0 : bareLiftFromLevel (K := K) V ∈ gaugeFieldsAtLevel L m K 0 := by
      rw [hbareEq]
      exact (hU 0 (Nat.zero_le k)).2 hVr
    have hdomU : bareLiftSupport (K := K) (univ : Set (BondAtLevel L m K k)) = univ :=
      hdom.trans (hU 0 (Nat.zero_le k)).1
    refine ⟨hU0, fun j hj => ?_⟩
    have hS := hRA.1 j hj
    have hbU : (compactLevelLifts (K := K) univ V j).support = univ := hS.1.trans (hU j hj).1
    have hvals : (compactLevelLifts (K := K) univ V j).field = orderLift j V :=
      funext fun b => hS.2 b (hbU ▸ mem_univ b)
    refine ⟨hbU, hvals ▸ (hU j hj).2 hVr, ?_⟩
    have hit := ((hBondwise L m K hL hm 0 hK).2.1 _ hU0 j (hj.trans hkK)).1
    have hcfg : bareLiftPartial (K := K)
        (⟨univ, V⟩ : PartialGaugeField L m (levelDepth K k)) =
        ⟨univ, bareLiftFromLevel (K := K) V⟩ := by
      show PartialGaugeField.mk (bareLiftSupport (K := K) univ) _ = _
      rw [hdomU]
    have hlift : compactLevelLifts (K := K) univ V j =
        barePartialBlockAverageIter (Averaging.smoothingRadius L)
          ⟨univ, bareLiftFromLevel (K := K) V⟩ j := by
      rw [← hcfg]
      rfl
    rw [hlift, hit]
  · intro hreal X hX hXC j hj
    have hInnerOver : ∀ i ≤ k, ∀ b ∈ (bondsInside X : Set (BondAtLevel L m K i)),
        ¬EndsInOneBlock k b →
          ∃ c ∈ (bondsInside X : Set (BondAtLevel L m K k)), CoversBond c b := by
      intro i hi b hb hnot
      rcases (hOver L m K hL hm hK i k hi hkK b).2.2 with ⟨y, hy⟩ | ⟨c, hc⟩
      · exact absurd ⟨y, hy⟩ hnot
      · obtain ⟨ht, hh⟩ := (hT i hi).1 b c hc
        have hB6 := (hBlocks L m K hL hm hK i k hi hkK).2.2.2.2.2
        refine ⟨c, ⟨?_, ?_⟩, hc⟩
        · rw [ht]
          exact (hB6 X hX b.source hb.1).2.1
        · rw [hh]
          exact (hB6 X hX b.target hb.2).2.1
    have hInnerIn : ∀ i ≤ k,
        (bondsInside X : Set (BondAtLevel L m K i)) ⊆ bondsInsideOrOverCoarse i 𝒞 := by
      intro i hi b hb
      by_cases hin : EndsInOneBlock k b
      · exact Or.inl hin
      · obtain ⟨c, hc, hbc⟩ := hInnerOver i hi b hb hin
        exact Or.inr ⟨c, hXC hc, hbc⟩
    have hPc : ∀ i < k, ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (i + 1))),
        (bondsInDoubleBlock c : Set (BondAtLevel L m K i)) ⊆ bondsInside X := by
      intro i hi c hc
      have hz : ∀ y' : SiteAtLevel L m K (i + 1), (y' : FourTorus L m) ∈ X →
          unitBlock y' ⊆ X := by
        intro y' hy' z hz
        have hz' : z ∈ blockAtLevel i y' := by
          have e : (i + 1) - i = 1 := by omega
          show z ∈ refinedBlock ((i + 1) - i) y'
          rw [e]
          exact hz
        have h4 := ((hBlocks L m K hL hm hK i k (by omega) hkK).2.2.2.1 (i + 1) (by omega)
          (by omega)).2 y' hz'
        exact ((hBlocks L m K hL hm hK (i + 1) k (by omega) hkK).2.2.2.2.2 X hX y' hy').1 h4.1
      have hD : bondDoubleBlock c ⊆ X := by
        rintro z (h | h)
        · exact hz _ hc.1 h
        · exact hz _ hc.2 h
      intro b hb
      have hb' : b ∈ (bondsInside (bondDoubleBlock c) : Set (BondAtLevel L m K i)) := hb
      exact ⟨hD hb'.1, hD hb'.2⟩
    let UX : PartialGaugeField L m (levelDepth K 0) :=
      ⟨bondsInside X, bareLiftFromLevel (K := K) V⟩
    have hIter : ∀ i ≤ k, (bondsInside X : Set (BondAtLevel L m K i)) ⊆
        (barePartialBlockAverageIter (K := K) (Averaging.smoothingRadius L) UX i).support := by
      intro i
      induction i with
      | zero => exact fun _ _ hb => hb
      | succ i ih =>
        intro hi c hc
        rw [barePartialBlockAverageIter_succ]
        show (bondsInDoubleBlock c : Set (BondAtLevel L m K i)) ⊆ _
        intro b hb
        exact ih (by omega) (hPc i (by omega) c hc hb)
    have hCl : IsReversalClosed (bondsInside X : Set (BondAtLevel L m K 0)) :=
      fun b hb => ⟨hb.2, hb.1⟩
    have hsub : (bondsInside X : Set (BondAtLevel L m K 0)) ⊆ bareLiftSupport (K := K) 𝒞 := by
      rw [hdom]
      exact hInnerIn 0 (Nat.zero_le k)
    have hRes := ((hBondwise L m K hL hm 0 hK).2.2.2.2.2
      (bareLiftPartial (K := K) ⟨𝒞, V⟩) UX hClosed0 hCl ⟨hsub, fun _ _ => rfl⟩).1
      (hConfBare _ ((hCfg 0 (Nat.zero_le k)).2.1.2.2.2 hreal)) j
      (by have := hj.trans hkK; omega)
    have hResc := cast_isRestriction (by rw [Nat.zero_add]) (by rw [Nat.zero_add]) hRes
    exact ⟨hInnerIn j hj, hInnerOver j hj, hIter j hj, fun b hb => hResc.2 b (hIter j hj hb)⟩
end YangMills.Construction.PeriodicLattice
