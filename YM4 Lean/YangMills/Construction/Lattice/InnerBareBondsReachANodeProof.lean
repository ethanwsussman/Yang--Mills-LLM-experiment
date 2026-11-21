import YangMills.Construction.Lattice.InnerBareBondsReachANode
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.Torus.CubeSetsBumpsCutOffsAndProductRuleProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BondsReachEndpoint
open YangMills.Construction.TorusMetric
variable {L m : ℕ}
theorem torusSupNorm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) {a : ℝ} (h : ∀ μ, |v μ| ≤ a) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj S v) ≤ a := by apply _root_.YangMills.Construction.GeneralTorus.CubeBumpCutoff.supNorm_proj_le <;> assumption
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_add_mul_pow (hL : 0 < L) (i : ℤ) (n : ℕ) :
    meshSize L (i + n) * (L : ℝ) ^ n = meshSize L i := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshSize, neg_add, zpow_add₀ hL', zpow_neg, zpow_natCast]
  field_simp
theorem coe_unitStep_eq_torusProj (J : ℤ) (μ : Fin 4) :
    ((unitStep L m J μ : Site L m J) : FourTorus L m) =
      torusProj (torusSide L m) fun ρ => meshSize L J * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ := by
  funext ρ
  by_cases h : ρ = μ
  · subst h
    simp [unitStep, pointOnAxis, torusProj]
  · simp [unitStep, pointOnAxis, torusProj, Pi.single_eq_of_ne h]
theorem torusSupNorm_sub_lt_of_mem_blockAsGrid (hL : 0 < L) {c : ℤ} {n : ℕ} {y : Site L m c}
    {x : FourTorus L m} (hx : x ∈ blockAsGrid n y) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : FourTorus L m)) < meshSize L c / 2 := by
  obtain ⟨p, hp, rfl⟩ := hx
  have ha := meshSize_pos (L := L) hL (c + n)
  have hd : (y : FourTorus L m) + torusProj (torusSide L m) (fun μ => meshSize L (c + n) * (p μ : ℝ)) -
      (y : FourTorus L m) = torusProj (torusSide L m) (fun μ => meshSize L (c + n) * (p μ : ℝ)) := by
    abel
  rw [hd]
  have hle : _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj (torusSide L m) fun μ => meshSize L (c + n) * (p μ : ℝ)) ≤
      meshSize L (c + n) * (((L : ℝ) ^ n - 1) / 2) :=
    _root_.YangMills.Construction.PeriodicLattice.BondsReachEndpoint.torusSupNorm_torusProj_le _ fun μ => by
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (hp μ) ha.le
  refine hle.trans_lt ?_
  rw [← meshSize_add_mul_pow hL c n]
  nlinarith
theorem mem_of_near_centre {c : ℤ} (hc : CubeSupDistanceFacts L m c) {X : Set (FourTorus L m)}
    (hX : IsUnionOfCubesOfIndex c X) {y : Site L m c} {x w : FourTorus L m}
    (hx : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : FourTorus L m)) < meshSize L c / 2) (hxX : x ∈ X)
    (hw : w ∈ cubeAround y) : w ∈ X := by
  obtain ⟨C, hC, rfl⟩ := hX
  obtain ⟨Q, hQ, hxQ⟩ := hxX
  have hQy : Q = cubeAround y := hc.2.2.2.2.2.1 y x hx Q (hC hQ).2 hxQ
  subst hQy
  exact ⟨_, hQ, hw⟩
theorem eq_empty_of_index_lt {c : ℤ} {X : Set (FourTorus L m)} (hX : IsUnionOfCubesOfIndex c X)
    (hc : ¬-(m : ℤ) ≤ c) : X = ∅ := by
  obtain ⟨C, hC, rfl⟩ := hX
  have : C = ∅ := eq_empty_of_forall_notMem fun Q hQ => hc (hC hQ).1
  simp [this]
theorem exists_mem_cubeAround {c' : ℤ} (hc : CubeSupDistanceFacts L m c') (x : FourTorus L m) :
    ∃ y : Site L m c', x ∈ cubeAround y := by
  have hx : x ∈ ⋃₀ standardCubePartition L m c' := by
    rw [hc.2.2.2.2.1]
    trivial
  obtain ⟨Q, ⟨y, rfl⟩, hxQ⟩ := hx
  exact ⟨y, hxQ⟩
theorem step_or_back_not_mem (hcubes : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {c J : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (hJ : J = c + n) {X : Set (FourTorus L m)} (hX : IsUnionOfCubesOfIndex c X) (x : Site L m J)
    (hx : (x : FourTorus L m) ∉ X) (μ : Fin 4) :
    ((x + unitStep L m J μ : Site L m J) : FourTorus L m) ∉ X ∨
      ((x - unitStep L m J μ : Site L m J) : FourTorus L m) ∉ X := by
  subst hJ
  by_cases hcm : -(m : ℤ) ≤ c
  · have hL0 : 0 < L := by have := hL.2; omega
    obtain ⟨hr, hc, -⟩ := hcubes L m hL.1 hL.2 hm c hcm
    obtain ⟨y, hxy⟩ := exists_mem_cubeAround hc (x : FourTorus L m)
    have hB : (1 : ℝ) ≤ ((L : ℝ) ^ n - 1) / 2 := by
      have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
      have hp : (L : ℝ) ≤ (L : ℝ) ^ n := le_self_pow₀ (by linarith) (by omega)
      linarith
    have hxb : (x : FourTorus L m) ∈ blockAsGrid n y := by
      rw [← (hr n).1 y]
      exact ⟨hxy, x.2⟩
    obtain ⟨p, hp, hxp⟩ := hxb
    have hoff : ∀ w ∈ blockAsGrid n y, w ∉ X := fun w hw hwX =>
      hx (mem_of_near_centre hc hX (_root_.YangMills.Construction.PeriodicLattice.BondsReachEndpoint.torusSupNorm_sub_lt_of_mem_blockAsGrid hL0 hw) hwX hxy)
    have hshift : ∀ s : ℤ, (s = 1 ∨ s = -1) →
        |((p μ + s : ℤ) : ℝ)| ≤ ((L : ℝ) ^ n - 1) / 2 →
        (x : FourTorus L m) + torusProj (torusSide L m) (fun ρ => meshSize L (c + n) *
          ((s : ℝ) * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ)) ∈ blockAsGrid n y := by
      intro s hs hb
      refine ⟨Function.update p μ (p μ + s), fun ρ => ?_, ?_⟩
      · by_cases h : ρ = μ
        · subst h
          simpa using hb
        · simpa [Function.update_of_ne h] using hp ρ
      · rw [hxp, add_assoc]
        congr 1
        funext ρ
        by_cases h : ρ = μ
        · subst h
          simp only [Pi.add_apply, torusProj, Function.update_self, Pi.single_eq_same, Int.cast_add,
            mul_one]
          rw [← AddCircle.coe_add]
          congr 1
          ring
        · simp [torusProj, Function.update_of_ne h, Pi.single_eq_of_ne h]
    rcases le_or_gt 0 (p μ) with h0 | h0
    · right
      have hb : |((p μ + (-1) : ℤ) : ℝ)| ≤ ((L : ℝ) ^ n - 1) / 2 := by
        have h1 : (0 : ℝ) ≤ (p μ : ℝ) := by exact_mod_cast h0
        have h2 := hp μ
        rw [abs_of_nonneg h1] at h2
        push_cast
        rw [abs_le]
        constructor <;> linarith
      have := hoff _ (hshift (-1) (Or.inr rfl) hb)
      have he : ((x - unitStep L m (c + n) μ : Site L m (c + n)) : FourTorus L m) =
          (x : FourTorus L m) + torusProj (torusSide L m) (fun ρ => meshSize L (c + n) *
            (((-1 : ℤ) : ℝ) * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ)) := by
        rw [AddSubgroupClass.coe_sub, coe_unitStep_eq_torusProj, sub_eq_add_neg]
        congr 1
        funext ρ
        simp only [Pi.neg_apply, torusProj, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_neg,
          AddCircle.coe_neg]
      rw [he]
      exact this
    · left
      have hb : |((p μ + 1 : ℤ) : ℝ)| ≤ ((L : ℝ) ^ n - 1) / 2 := by
        have h1 : (p μ : ℝ) ≤ -1 := by exact_mod_cast (by omega : p μ ≤ -1)
        have h2 := hp μ
        rw [abs_of_neg (by linarith)] at h2
        push_cast
        rw [abs_le]
        constructor <;> linarith
      have := hoff _ (hshift 1 (Or.inl rfl) hb)
      have he : ((x + unitStep L m (c + n) μ : Site L m (c + n)) : FourTorus L m) =
          (x : FourTorus L m) + torusProj (torusSide L m) (fun ρ => meshSize L (c + n) *
            (((1 : ℤ) : ℝ) * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ)) := by
        rw [AddSubgroup.coe_add, coe_unitStep_eq_torusProj]
        congr 1
        funext ρ
        simp only [torusProj, Int.cast_one, one_mul]
      rw [he]
      exact this
  · have := eq_empty_of_index_lt hX hcm
    subst this
    simp
theorem exists_vec_of_sub_steps (hL : 0 < L) {J : ℤ} {μ ν : Fin 4} (hμν : μ ≠ ν)
    {A B : FourTorus L m}
    (hA : A = (unitStep L m J μ : Site L m J) ∨
      A = -((unitStep L m J μ : Site L m J) : FourTorus L m))
    (hB : B = (unitStep L m J ν : Site L m J) ∨
      B = -((unitStep L m J ν : Site L m J) : FourTorus L m)) :
    ∃ v : Fin 4 → ℝ, A - B = torusProj (torusSide L m) v ∧ ∀ ρ, |v ρ| ≤ meshSize L J := by
  have ha := meshSize_pos (L := L) hL J
  obtain ⟨s, hs, hsA⟩ : ∃ s : ℝ, |s| = 1 ∧ A = torusProj (torusSide L m) fun ρ => meshSize L J *
      (s * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ) := by
    rcases hA with rfl | rfl
    · exact ⟨1, by simp, by rw [coe_unitStep_eq_torusProj]; simp⟩
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_unitStep_eq_torusProj]
      funext ρ
      simp only [Pi.neg_apply, torusProj, neg_mul, one_mul, mul_neg, AddCircle.coe_neg]
  obtain ⟨t, ht, htB⟩ : ∃ t : ℝ, |t| = 1 ∧ B = torusProj (torusSide L m) fun ρ => meshSize L J *
      (t * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) ρ) := by
    rcases hB with rfl | rfl
    · exact ⟨1, by simp, by rw [coe_unitStep_eq_torusProj]; simp⟩
    · refine ⟨-1, by simp, ?_⟩
      rw [coe_unitStep_eq_torusProj]
      funext ρ
      simp only [Pi.neg_apply, torusProj, neg_mul, one_mul, mul_neg, AddCircle.coe_neg]
  refine ⟨fun ρ => meshSize L J * (s * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ) -
    meshSize L J * (t * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) ρ), ?_, fun ρ => ?_⟩
  · rw [hsA, htB]
    funext ρ
    simp only [Pi.sub_apply, torusProj, AddCircle.coe_sub]
  · by_cases h : ρ = μ
    · subst h
      simp [Pi.single_eq_of_ne hμν, abs_mul, hs, abs_of_pos ha]
    · by_cases h' : ρ = ν
      · subst h'
        simp [Pi.single_eq_of_ne h, abs_mul, ht, abs_of_pos ha]
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', ha.le]
theorem false_of_near_outside (hcubes : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K e r k : ℕ}
    {Ω : ℕ → Set (FourTorus L m)} (hk : 1 ≤ k) (hsep : IsSeparatedChain K e r 0 k Ω)
    {w y : FourTorus L m} {v : Fin 4 → ℝ} (hw : w ∉ Ω 0) (hy : y ∈ Ω 1)
    (hwy : w - y = torusProj (torusSide L m) v)
    (hv : ∀ μ, |v μ| ≤ meshSize L (levelDepth K 0)) : False := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL0
  obtain ⟨hsub, hgap⟩ := hsep.2 0 le_rfl (by omega)
  simp only [zero_add] at hsub hgap
  obtain ⟨C, hC, hC0⟩ := hsep.1 0 le_rfl (by omega)
  have hy0 : y ∈ Ω 0 := hsub hy
  have hcm : -(m : ℤ) ≤ scaledCubeIndex K 0 e := by
    rw [hC0] at hy0
    obtain ⟨Q, hQ, -⟩ := hy0
    exact (hC hQ).1
  obtain ⟨-, hc, -⟩ := hcubes L m hL.1 hL.2 hm _ hcm
  obtain ⟨z, hwz⟩ := exists_mem_cubeAround hc w
  have hwA : w ∈ complementRegion (scaledCubeIndex K 0 e) (Ω 0) :=
    ⟨cubeAround z, ⟨⟨z, rfl⟩, fun h => hw (h.2 hwz)⟩, hwz⟩
  have hd : setSupDist (complementRegion (scaledCubeIndex K 0 e) (Ω 0)) (Ω 1) ≤
      ENNReal.ofReal (meshSize L (levelDepth K 0)) := by
    refine (iInf₂_le_of_le w hwA (iInf₂_le_of_le y hy ?_))
    rw [hwy]
    exact ENNReal.ofReal_le_ofReal (_root_.YangMills.Construction.PeriodicLattice.BondsReachEndpoint.torusSupNorm_torusProj_le v hv)
  have hle : supDistInLevelUnits K 0 (complementRegion (scaledCubeIndex K 0 e) (Ω 0)) (Ω 1) ≤
      ENNReal.ofReal 1 := by
    unfold supDistInLevelUnits
    refine (mul_le_mul' le_rfl hd).trans ?_
    rw [← ENNReal.ofReal_mul (zpow_nonneg (by linarith) _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [meshSize, zpow_neg]
    exact mul_inv_cancel₀ (zpow_pos (by linarith) _).ne'
  have hge : ENNReal.ofReal 1 ≤ separationGap L e r 0 0 := by
    unfold separationGap
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ r := one_le_pow₀ hL1
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ e := one_le_pow₀ hL1
    simp only [Nat.cast_zero, sub_self, zpow_zero, mul_one]
    nlinarith
  exact absurd (hgap.trans_le hle) (not_lt.mpr hge)
theorem mem_activeBondSet_of_lt {K k q : ℕ} {Ω : ℕ → Set (FourTorus L m)} (hq : q < k)
    (c : BondAtLevel L m K q) (h0t : (c.source : FourTorus L m) ∈ Ω 0)
    (h0h : (c.target : FourTorus L m) ∈ Ω 0) (ht : (c.source : FourTorus L m) ∈ Ω q)
    (ht' : (c.source : FourTorus L m) ∉ Ω (q + 1))
    (hh' : (c.target : FourTorus L m) ∉ Ω (q + 1)) :
    (⟨q, c⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω := by
  refine ⟨⟨hq.le, Or.inl ?_, ⟨h0t, h0h⟩⟩, fun hin => ?_⟩
  · simp only [annulusSites, if_pos hq]
    exact ⟨ht, ht'⟩
  · rcases hin.2.2 with h | h
    exacts [ht' h, hh' h]
theorem mem_activeBondSet_top {K k : ℕ} {Ω : ℕ → Set (FourTorus L m)} (c : BondAtLevel L m K k)
    (h0t : (c.source : FourTorus L m) ∈ Ω 0) (h0h : (c.target : FourTorus L m) ∈ Ω 0)
    (ht : (c.source : FourTorus L m) ∈ Ω k) :
    (⟨k, c⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ activeBondSet K k Ω := by
  refine ⟨⟨le_rfl, Or.inl ?_, ⟨h0t, h0h⟩⟩, fun hin => lt_irrefl _ hin.1⟩
  simp only [annulusSites, lt_irrefl, if_false]
  exact ht
theorem isEndpointOf_source_of_not_mem_one (hcubes : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K e r k : ℕ}
    {Ω : ℕ → Set (FourTorus L m)} (hk : 1 ≤ k) (hsep : IsSeparatedChain K e r 0 k Ω)
    (c : BondAtLevel L m K 0) (hc : c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)))
    (ht : (c.source : FourTorus L m) ∉ Ω 1) :
    IsEndpointOf (activeBondSet K k Ω) (c.source : FourTorus L m) := by
  have hL0 : 0 < L := by have := hL.2; omega
  by_cases hh : (c.target : FourTorus L m) ∈ Ω 1
  · obtain ⟨ν, hν⟩ := c.isNeighbour
    obtain ⟨μ, hμ⟩ : ∃ μ : Fin 4, μ ≠ ν := by
      have : ∀ ν : Fin 4, ∃ μ : Fin 4, μ ≠ ν := by decide
      exact this ν
    have hX : IsUnionOfCubesOfIndex (scaledCubeIndex K 1 e) (Ω 1) :=
      hsep.1 1 (by omega) (by omega)
    have hJ : levelDepth K 0 = scaledCubeIndex K 1 e + ((e + 1 : ℕ) : ℤ) := by
      simp only [levelDepth, scaledCubeIndex]
      push_cast
      ring
    have hB : ((c.target : FourTorus L m) - (c.source : FourTorus L m)) =
          (unitStep L m (levelDepth K 0) ν : Site L m (levelDepth K 0)) ∨
        ((c.target : FourTorus L m) - (c.source : FourTorus L m)) =
          -((unitStep L m (levelDepth K 0) ν : Site L m (levelDepth K 0)) : FourTorus L m) := by
      rcases hν with h | h
      · exact Or.inl (by rw [← h]; simp)
      · exact Or.inr (by
          have := congrArg (fun s : Site L m (levelDepth K 0) => (s : FourTorus L m)) h
          simpa using this)
    have hfin : ∀ c' : BondAtLevel L m K 0, c'.source = c.source →
        ((c'.target : FourTorus L m) - (c.source : FourTorus L m) =
            (unitStep L m (levelDepth K 0) μ : Site L m (levelDepth K 0)) ∨
          (c'.target : FourTorus L m) - (c.source : FourTorus L m) =
            -((unitStep L m (levelDepth K 0) μ : Site L m (levelDepth K 0)) : FourTorus L m)) →
        (c'.target : FourTorus L m) ∉ Ω 1 →
        IsEndpointOf (activeBondSet K k Ω) (c.source : FourTorus L m) := by
      intro c' hc' hA hoff
      obtain ⟨v, hv, hvb⟩ := exists_vec_of_sub_steps hL0 hμ hA hB
      have h0 : (c'.target : FourTorus L m) ∈ Ω 0 := by
        by_contra hn
        exact false_of_near_outside hcubes hL hm hk hsep hn hh (v := v) (by rw [← hv]; abel) hvb
      refine ⟨⟨0, c'⟩, ?_, Or.inl (by rw [hc'])⟩
      refine mem_activeBondSet_of_lt (by omega) c' (by rw [hc']; exact hc.1) h0
        (by rw [hc']; exact hc.1) (by rw [hc']; exact ht) hoff
    rcases step_or_back_not_mem hcubes hL hm (by omega : 1 ≤ e + 1) hJ hX c.source ht μ with h | h
    · exact hfin (Bond.forwardFrom c.source μ) rfl (Or.inl (by simp [Bond.forwardFrom])) h
    · exact hfin (Bond.backwardFrom c.source μ) rfl
        (Or.inr (by simp [Bond.backwardFrom, sub_eq_add_neg])) h
  · exact ⟨⟨0, c⟩, mem_activeBondSet_of_lt (by omega) c hc.1 hc.2 hc.1 ht hh, Or.inl rfl⟩
theorem mem_of_closed_under_steps {J : ℤ} {S : Set (Site L m J)} {t : Site L m J} (ht : t ∈ S)
    (hp : ∀ x ∈ S, ∀ μ, x + unitStep L m J μ ∈ S) (hn : ∀ x ∈ S, ∀ μ, x - unitStep L m J μ ∈ S)
    (x : Site L m J) : x ∈ S := by
  have hz : ∀ (μ : Fin 4) (n : ℤ) (s : Site L m J), s ∈ S → s + n • unitStep L m J μ ∈ S := by
    intro μ n
    induction n using Int.induction_on with
    | zero => intro s hs; simpa using hs
    | succ i ih =>
      intro s hs
      have := hp _ (ih s hs) μ
      simpa [add_smul, add_assoc] using this
    | pred i ih =>
      intro s hs
      have := hn _ (ih s hs) μ
      rw [sub_smul, one_smul, ← add_sub_assoc]
      exact this
  obtain ⟨n, hn'⟩ := (x - t).2
  have hd : x - t = ∑ μ, n μ • unitStep L m J μ := by
    apply Subtype.ext
    funext ν
    have hs : ((∑ μ, n μ • unitStep L m J μ : Site L m J) : FourTorus L m) =
        ∑ μ, n μ • ((unitStep L m J μ : Site L m J) : FourTorus L m) := by
      simpa using map_sum (sublattice L m J).subtype (fun μ => n μ • unitStep L m J μ)
        Finset.univ
    rw [hn' ν, hs, Finset.sum_apply, Finset.sum_eq_single ν]
    · simp only [Pi.smul_apply]
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
      simp [unitStep, pointOnAxis]
    · intro μ _ h
      simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h.symm]
    · simp
  have hx : x = t + ∑ μ, n μ • unitStep L m J μ := by
    rw [← hd]
    abel
  rw [hx, Fin.sum_univ_four]
  have := hz 3 (n 3) _ (hz 2 (n 2) _ (hz 1 (n 1) _ (hz 0 (n 0) t ht)))
  simpa [add_assoc] using this
theorem exists_vec_of_step (hL : 0 < L) {J : ℤ} {μ : Fin 4} {A : FourTorus L m}
    (hA : A = (unitStep L m J μ : Site L m J) ∨
      A = -((unitStep L m J μ : Site L m J) : FourTorus L m)) :
    ∃ v : Fin 4 → ℝ, A = torusProj (torusSide L m) v ∧ ∀ ρ, |v ρ| ≤ meshSize L J := by
  have ha := meshSize_pos (L := L) hL J
  have hb : ∀ ρ, |meshSize L J * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ| ≤ meshSize L J :=
    fun ρ => by
      by_cases h : ρ = μ
      · subst h
        simp [abs_of_pos ha]
      · simp [Pi.single_eq_of_ne h, ha.le]
  rcases hA with rfl | rfl
  · exact ⟨_, coe_unitStep_eq_torusProj J μ, hb⟩
  · refine ⟨fun ρ => -(meshSize L J * (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) ρ), ?_, fun ρ => ?_⟩
    · rw [coe_unitStep_eq_torusProj]
      funext ρ
      simp only [Pi.neg_apply, torusProj, AddCircle.coe_neg]
    · simpa using hb ρ
theorem exists_endpoint_of_level (hcubes : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K e r k q : ℕ}
    {Ω : ℕ → Set (FourTorus L m)} (hsep : IsSeparatedChain K e r 0 k Ω) (hq : q < k)
    (hP0 : ∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω 0)
    (hPq : ∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω q)
    (hPq' : ¬∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω (q + 1)) :
    ∃ a : SiteAtLevel L m K 0, IsEndpointOf (activeBondSet K k Ω) (a : FourTorus L m) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨w, hw⟩ := not_forall.mp hPq'
  have hX : IsUnionOfCubesOfIndex (scaledCubeIndex K (q + 1) e) (Ω (q + 1)) :=
    hsep.1 (q + 1) (by omega) (by omega)
  have hbare : ∀ x : SiteAtLevel L m K q,
      (x : FourTorus L m) ∈ sublattice L m (levelDepth K 0) := fun x =>
    sublattice_mono hL0 m (by simp only [levelDepth]; omega) x.2
  obtain ⟨p, hp⟩ : ∃ p : SiteAtLevel L m K q, (p : FourTorus L m) ∉ Ω (q + 1) := by
    by_cases hcm : -(m : ℤ) ≤ scaledCubeIndex K (q + 1) e
    · obtain ⟨-, hc, -⟩ := hcubes L m hL.1 hL.2 hm _ hcm
      obtain ⟨z, hwz⟩ := exists_mem_cubeAround hc (w : FourTorus L m)
      refine ⟨⟨z, sublattice_mono hL0 m (by simp only [levelDepth, scaledCubeIndex]; omega) z.2⟩,
        fun hz => hw ?_⟩
      have hnear : _root_.YangMills.Construction.TorusMetric.torusSupNorm ((z : FourTorus L m) - (z : FourTorus L m)) <
          meshSize L (scaledCubeIndex K (q + 1) e) / 2 := by
        have h0 : (z : FourTorus L m) - (z : FourTorus L m) = torusProj (torusSide L m) 0 := by
          rw [sub_self]
          funext ρ
          simp [torusProj]
        rw [h0]
        exact (_root_.YangMills.Construction.PeriodicLattice.BondsReachEndpoint.torusSupNorm_torusProj_le (a := 0) _ (by simp)).trans_lt
          (half_pos (meshSize_pos hL0 _))
      exact mem_of_near_centre hc hX hnear hz hwz
    · refine ⟨0, ?_⟩
      rw [eq_empty_of_index_lt hX hcm]
      simp
  have hfin : ∀ c : BondAtLevel L m K q, c.source = p → (c.target : FourTorus L m) ∉ Ω (q + 1) →
      ∃ a : SiteAtLevel L m K 0, IsEndpointOf (activeBondSet K k Ω) (a : FourTorus L m) := by
    intro c hc hh
    refine ⟨⟨(c.source : FourTorus L m), hbare c.source⟩, ⟨q, c⟩, ?_, Or.inl rfl⟩
    exact mem_activeBondSet_of_lt hq c (hP0 ⟨_, hbare c.source⟩) (hP0 ⟨_, hbare c.target⟩)
      (hPq ⟨_, hbare c.source⟩) (by rw [hc]; exact hp) hh
  have hJ : levelDepth K q = scaledCubeIndex K (q + 1) e + ((e + 1 : ℕ) : ℤ) := by
    simp only [levelDepth, scaledCubeIndex]
    push_cast
    ring
  rcases step_or_back_not_mem hcubes hL hm (by omega : 1 ≤ e + 1) hJ hX p hp 0 with h | h
  · exact hfin (Bond.forwardFrom p 0) rfl h
  · exact hfin (Bond.backwardFrom p 0) rfl h
theorem exists_endpoint (hcubes : StandardPartitionCubeGeometry)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K e r k : ℕ}
    {Ω : ℕ → Set (FourTorus L m)} (hk : 1 ≤ k) (hsep : IsSeparatedChain K e r 0 k Ω)
    (hP1 : ∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω 1)
    (hP0 : ∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω 0) :
    ∃ a : SiteAtLevel L m K 0, IsEndpointOf (activeBondSet K k Ω) (a : FourTorus L m) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have key : ∀ d q : ℕ, q + d = k → (∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω q) →
      ∃ a : SiteAtLevel L m K 0, IsEndpointOf (activeBondSet K k Ω) (a : FourTorus L m) := by
    intro d
    induction d with
    | zero =>
      intro q hq hP
      obtain rfl : q = k := by omega
      have hbare : ∀ x : SiteAtLevel L m K q,
          (x : FourTorus L m) ∈ sublattice L m (levelDepth K 0) := fun x =>
        sublattice_mono hL0 m (by simp only [levelDepth]; omega) x.2
      let c : BondAtLevel L m K q := Bond.forwardFrom 0 0
      refine ⟨⟨(c.source : FourTorus L m), hbare c.source⟩, ⟨q, c⟩, ?_, Or.inl rfl⟩
      exact mem_activeBondSet_top c (hP0 ⟨_, hbare c.source⟩) (hP0 ⟨_, hbare c.target⟩)
        (hP ⟨_, hbare c.source⟩)
    | succ d ih =>
      intro q hq hP
      by_cases h : ∀ w : SiteAtLevel L m K 0, (w : FourTorus L m) ∈ Ω (q + 1)
      · exact ih (q + 1) (by omega) h
      · exact exists_endpoint_of_level hcubes hL hm hsep (by omega) hP0 hP h
  exact key (k - 1) 1 (by omega) hP1
theorem innerBondsReachEndpoint_holds (hcubes : StandardPartitionCubeGeometry) :
    InnerBondsReachEndpoint := by
  intro L m hL hm i K k e r Ω hseq hsep b hb
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := hseq.2.1
  have hdec : Ω 1 ⊆ Ω 0 := hseq.2.2.2.1.1 0 (by omega)
  by_contra hno
  let S : Set (SiteAtLevel L m K 0) := {a | Relation.ReflTransGen
    (fun x y : SiteAtLevel L m K 0 =>
      ∃ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), c.source = x ∧ c.target = y)
    a b.source}
  have hin : ∀ a ∈ S, ∃ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), c.source = a := by
    intro a ha
    rcases Relation.ReflTransGen.cases_head ha with h | ⟨_, ⟨c, hc, ht, -⟩, -⟩
    · exact ⟨b, hb, h.symm⟩
    · exact ⟨c, hc, ht⟩
  have h1 : ∀ a ∈ S, (a : FourTorus L m) ∈ Ω 1 := by
    intro a ha
    by_contra hoff
    obtain ⟨c, hc, rfl⟩ := hin a ha
    exact hno ⟨_, isEndpointOf_source_of_not_mem_one hcubes hL hm hk hsep c hc hoff, ha⟩
  have hp : ∀ x ∈ S, ∀ μ, x + unitStep L m (levelDepth K 0) μ ∈ S := by
    intro a ha μ
    obtain ⟨v, hv, hvb⟩ := exists_vec_of_step (m := m) hL0 (J := levelDepth K 0) (μ := μ)
      (Or.inl rfl)
    have hw : ((a + unitStep L m (levelDepth K 0) μ : SiteAtLevel L m K 0) : FourTorus L m) ∈
        Ω 0 := by
      by_contra hn
      exact false_of_near_outside hcubes hL hm hk hsep hn (h1 a ha) (v := v) (by rw [← hv]; simp)
        hvb
    exact Relation.ReflTransGen.head
      ⟨(Bond.forwardFrom a μ).opposite, ⟨hw, hdec (h1 a ha)⟩, rfl, rfl⟩ ha
  have hn : ∀ x ∈ S, ∀ μ, x - unitStep L m (levelDepth K 0) μ ∈ S := by
    intro a ha μ
    obtain ⟨v, hv, hvb⟩ := exists_vec_of_step (m := m) hL0 (J := levelDepth K 0) (μ := μ)
      (Or.inr rfl)
    have hw : ((a - unitStep L m (levelDepth K 0) μ : SiteAtLevel L m K 0) : FourTorus L m) ∈
        Ω 0 := by
      by_contra hn
      exact false_of_near_outside hcubes hL hm hk hsep hn (h1 a ha) (v := v)
        (by rw [← hv]; simp [sub_eq_add_neg]) hvb
    exact Relation.ReflTransGen.head
      ⟨(Bond.backwardFrom a μ).opposite, ⟨hw, hdec (h1 a ha)⟩, rfl, rfl⟩ ha
  have hall : ∀ x : SiteAtLevel L m K 0, x ∈ S :=
    mem_of_closed_under_steps (t := b.source) Relation.ReflTransGen.refl hp hn
  obtain ⟨a, ha⟩ := exists_endpoint hcubes hL hm hk hsep (fun w => h1 w (hall w))
    (fun w => hdec (h1 w (hall w)))
  exact hno ⟨a, ha, hall a⟩
end YangMills.Construction.PeriodicLattice.BondsReachEndpoint
