import YangMills.Construction.Lattice.LiftsClassesAndSitesInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LevelUnits
def levelScale (L K j : ℕ) : ℝ := (L : ℝ) ^ (K - j)
def levelPoint (L m K j : ℕ) (w : Fin 4 → ℝ) : FourTorus L m :=
  fun μ => (((levelScale L K j)⁻¹ * w μ : ℝ) : AddCircle (torusSide L m))
variable {L m K j k : ℕ}
theorem levelScale_pos (hL : 0 < L) : 0 < levelScale L K j := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  unfold levelScale
  positivity
theorem toLevelUnits_eq_mul (h : j ≤ K) (r : ℝ) : toLevelUnits L K j r = levelScale L K j * r := by
  have e : levelDepth K j = ((K - j : ℕ) : ℤ) := by unfold levelDepth; omega
  rw [toLevelUnits, e, zpow_natCast, levelScale]
theorem sideInLevelUnits_eq_pow (h : j ≤ K) :
    sideInLevelUnits L m K j = 2 * (L : ℝ) ^ (K - j + m) := by
  have e : (m : ℤ) + (K : ℤ) - (j : ℤ) = ((K - j + m : ℕ) : ℤ) := by omega
  rw [sideInLevelUnits, e, zpow_natCast]
theorem sideInLevelUnits_eq_mul (h : j ≤ K) :
    sideInLevelUnits L m K j = levelScale L K j * torusSide L m := by
  rw [sideInLevelUnits_eq_pow h, levelScale, torusSide, pow_add]
  ring
theorem isLevelLift_iff (hL : 0 < L) (h : j ≤ K) (x : FourTorus L m) (w : Fin 4 → ℝ) :
    IsLevelLift L m K j x w ↔ x = levelPoint L m K j w := by
  have hP := (levelScale_pos (K := K) (j := j) hL).ne'
  constructor
  · rintro ⟨v, hv, hw⟩
    funext μ
    simp only [levelPoint]
    rw [hw μ, toLevelUnits_eq_mul h, inv_mul_cancel_left₀ hP, hv μ]
  · rintro rfl
    refine ⟨fun μ => (levelScale L K j)⁻¹ * w μ, fun μ => rfl, fun μ => ?_⟩
    rw [toLevelUnits_eq_mul h, mul_inv_cancel_left₀ hP]
theorem torusClassOf_eq_levelPoint (hL : 0 < L) (h : j ≤ K) (w : Fin 4 → ℝ) :
    torusClassOf L m K j w = levelPoint L m K j w := by
  have hex : ∃ x, IsLevelLift L m K j x w := ⟨_, (isLevelLift_iff hL h _ w).2 rfl⟩
  have hs := Classical.epsilon_spec hex
  exact (isLevelLift_iff hL h _ w).1 hs
theorem levelPoint_add (w w' : Fin 4 → ℝ) :
    levelPoint L m K j (w + w') = levelPoint L m K j w + levelPoint L m K j w' := by
  funext μ
  simp only [levelPoint, Pi.add_apply, mul_add, AddCircle.coe_add]
theorem levelPoint_sub (w w' : Fin 4 → ℝ) :
    levelPoint L m K j (w - w') = levelPoint L m K j w - levelPoint L m K j w' := by
  funext μ
  simp only [levelPoint, Pi.sub_apply, mul_sub, AddCircle.coe_sub]
theorem levelPoint_neg (w : Fin 4 → ℝ) : levelPoint L m K j (-w) = -levelPoint L m K j w := by
  funext μ
  simp only [levelPoint, Pi.neg_apply, mul_neg, AddCircle.coe_neg]
theorem exists_eq_levelPoint (hL : 0 < L) (x : FourTorus L m) : ∃ w, x = levelPoint L m K j w := by
  have hP := (levelScale_pos (K := K) (j := j) hL).ne'
  choose b hb _ using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (x μ)
  refine ⟨fun μ => levelScale L K j * b μ, funext fun μ => ?_⟩
  simp only [levelPoint, inv_mul_cancel_left₀ hP]
  exact (hb μ).symm
theorem levelPoint_eq_iff (hL : 0 < L) (h : j ≤ K) (w w' : Fin 4 → ℝ) :
    levelPoint L m K j w' = levelPoint L m K j w ↔
      w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j) := by
  have hP := (levelScale_pos (K := K) (j := j) hL).ne'
  have key : ∀ μ, (levelPoint L m K j w' μ = levelPoint L m K j w μ ↔
      ∃ n : ℤ, w' μ - w μ = sideInLevelUnits L m K j * (n : ℝ)) := by
    intro μ
    simp only [levelPoint]
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [zsmul_eq_mul, ← mul_sub] at hn
      have e : w' μ - w μ = levelScale L K j * ((levelScale L K j)⁻¹ * (w' μ - w μ)) := by
        rw [mul_inv_cancel_left₀ hP]
      rw [e, ← hn, sideInLevelUnits_eq_mul h]
      ring
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [zsmul_eq_mul, ← mul_sub, hn, sideInLevelUnits_eq_mul h, mul_assoc,
        inv_mul_cancel_left₀ hP]
      ring
  constructor
  · intro he
    choose z hz using fun μ => (key μ).1 (congrFun he μ)
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact funext fun μ => (key μ).2 ⟨z μ, hz μ⟩
theorem liftsOf_levelPoint (hL : 0 < L) (h : j ≤ K) (w : Fin 4 → ℝ) :
    liftSetAtLevel L m K j (levelPoint L m K j w) = cosetMod (sideInLevelUnits L m K j) w := by
  ext w'
  change IsLevelLift L m K j _ w' ↔ w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j)
  rw [isLevelLift_iff hL h, ← levelPoint_eq_iff hL h]
  exact eq_comm
theorem shiftBy_eq_add (hL : 0 < L) (h : j ≤ K) (x : FourTorus L m) (r : Fin 4 → ℝ) :
    shiftBy L m K j x r = x + levelPoint L m K j r := by
  have hex : ∃ w, IsLevelLift L m K j x w := by
    obtain ⟨w, hw⟩ := exists_eq_levelPoint (K := K) (j := j) hL x
    exact ⟨w, (isLevelLift_iff hL h x w).2 hw⟩
  have hs := (isLevelLift_iff hL h x _).1 (Classical.epsilon_spec hex)
  rw [shiftBy, torusClassOf_eq_levelPoint hL h, levelPoint_add, ← hs]
theorem levelSideFacts_of (hL : 13 ≤ L) (hm : 0 < m) (hjk : j ≤ k) (hk : k ≤ K) :
    LevelSideFacts L m K j k := by
  have hj := hjk.trans hk
  have h1 : (1 : ℝ) ≤ L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hint : ∀ i, i ≤ K → ∃ a : ℤ, sideInLevelUnits L m K i = (a : ℝ) := fun i hi =>
    ⟨2 * (L : ℤ) ^ (K - i + m), by rw [sideInLevelUnits_eq_pow hi]; push_cast; ring⟩
  have hsplit : sideInLevelUnits L m K j = (L : ℝ) ^ (k - j) * sideInLevelUnits L m K k := by
    rw [sideInLevelUnits_eq_pow hj, sideInLevelUnits_eq_pow hk,
      show K - j + m = (k - j) + (K - k + m) by omega, pow_add]
    ring
  have hfloor : 2 * (L : ℝ) ≤ sideInLevelUnits L m K k := by
    rw [sideInLevelUnits_eq_pow hk]
    have : (L : ℝ) ≤ (L : ℝ) ^ (K - k + m) := le_self_pow₀ h1 (by omega)
    linarith
  refine ⟨hint j hj, hint k hk, sideInLevelUnits_eq_mul hj, hsplit, ?_, hfloor, ?_⟩
  · rw [hsplit]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ h1)
  · have : (13 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
theorem liftCosetFacts_of (hL : 0 < L) (h : j ≤ K) : LiftCosetFacts L m K j := by
  refine ⟨fun x => ?_, fun w => ?_, fun w x => ?_, fun x x' w w' hw hw' => ?_,
    fun x r w hw => ?_⟩
  · obtain ⟨w, rfl⟩ := exists_eq_levelPoint (K := K) (j := j) hL x
    exact ⟨w, liftsOf_levelPoint hL h w⟩
  · refine ⟨levelPoint L m K j w, liftsOf_levelPoint hL h w, fun y hy => ?_⟩
    have hmem : w ∈ liftSetAtLevel L m K j y := by
      rw [hy]
      exact ⟨0, fun μ => by simp⟩
    exact (isLevelLift_iff hL h y w).1 hmem
  · rw [torusClassOf_eq_levelPoint hL h]
    exact isLevelLift_iff hL h x w
  · rw [isLevelLift_iff hL h] at hw hw'
    subst hw hw'
    exact ⟨(isLevelLift_iff hL h _ _).2 (levelPoint_add _ _).symm,
      (isLevelLift_iff hL h _ _).2 (levelPoint_sub _ _).symm⟩
  · rw [isLevelLift_iff hL h] at hw
    subst hw
    rw [shiftBy_eq_add hL h, torusClassOf_eq_levelPoint hL h, levelPoint_add]
theorem meshSize_eq (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) :
    meshSize L (levelDepth K k) = (levelScale L K j)⁻¹ * (L : ℝ) ^ (k - j) := by
  have e : levelDepth K k = ((K - k : ℕ) : ℤ) := by unfold levelDepth; omega
  rw [meshSize, e, zpow_neg, zpow_natCast, levelScale,
    show K - j = (k - j) + (K - k) by omega, pow_add]
  field_simp
theorem levelPoint_smul_coordVec (c : ℝ) (μ : Fin 4) :
    levelPoint L m K j (c • coordVec μ) =
      pointOnAxis L m μ ((levelScale L K j)⁻¹ * c) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [levelPoint, pointOnAxis, coordVec]
  · simp [levelPoint, pointOnAxis, coordVec, Pi.single_eq_of_ne hν]
theorem coe_unitStep_eq (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) (μ : Fin 4) :
    ((unitStep L m (levelDepth K k) μ : Site L m (levelDepth K k)) : FourTorus L m) =
      levelPoint L m K j ((L : ℝ) ^ (k - j) • coordVec μ) := by
  rw [levelPoint_smul_coordVec, ← meshSize_eq hL h hk]
  rfl
theorem sublattice_eq_image (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) :
    (sublattice L m (levelDepth K k) : Set (FourTorus L m)) =
      levelPoint L m K j '' scaledIntLattice ((L : ℝ) ^ (k - j)) := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨fun μ => (L : ℝ) ^ (k - j) * (n μ : ℝ), ⟨n, fun μ => rfl⟩, funext fun μ => ?_⟩
    simp only [levelPoint]
    rw [hn μ, meshSize_eq hL h hk]
    congr 1
    ring
  · rintro ⟨w, ⟨z, hz⟩, rfl⟩
    refine ⟨z, fun μ => ?_⟩
    simp only [levelPoint]
    rw [hz μ, meshSize_eq hL h hk]
    congr 1
    ring
theorem lift_mem_scaledIntLattice (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) (y : SiteAtLevel L m K k)
    (w : Fin 4 → ℝ) (hw : IsLevelLift L m K j (y : FourTorus L m) w) :
    w ∈ scaledIntLattice ((L : ℝ) ^ (k - j)) := by
  have hj := h.trans hk
  have hy : (y : FourTorus L m) ∈ (sublattice L m (levelDepth K k) : Set (FourTorus L m)) := y.2
  rw [sublattice_eq_image hL h hk] at hy
  obtain ⟨u, ⟨z, hz⟩, hu⟩ := hy
  have hpe : levelPoint L m K j w = levelPoint L m K j u := by
    rw [hu]
    exact ((isLevelLift_iff hL hj _ w).1 hw).symm
  obtain ⟨a, ha⟩ := (levelPoint_eq_iff hL hj u w).1 hpe
  refine ⟨fun μ => z μ + a μ * (2 * (L : ℤ) ^ (K - k + m)), fun μ => ?_⟩
  have e1 : w μ = u μ + sideInLevelUnits L m K j * (a μ : ℝ) := by
    have e2 : w μ - u μ = sideInLevelUnits L m K j * (a μ : ℝ) := ha μ
    linarith
  rw [e1, hz μ, sideInLevelUnits_eq_pow hj, show K - j + m = (k - j) + (K - k + m) by omega,
    pow_add]
  push_cast
  ring
theorem exists_bond_iff (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) (x x' : SiteAtLevel L m K k) :
    (∃ b : BondAtLevel L m K k, b.source = x ∧ b.target = x') ↔
      ∃ (σ : ℝ) (μ : Fin 4), (σ = 1 ∨ σ = -1) ∧
        (x' : FourTorus L m) =
          shiftBy L m K j (x : FourTorus L m) ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) := by
  have hj := h.trans hk
  constructor
  · rintro ⟨b, rfl, rfl⟩
    obtain ⟨μ, hb | hb⟩ := b.isNeighbour
    · refine ⟨1, μ, Or.inl rfl, ?_⟩
      have hb' := congrArg (Subtype.val) hb
      rw [AddSubgroup.coe_sub (H := sublattice L m (levelDepth K k))] at hb'
      rw [shiftBy_eq_add hL hj, one_mul, ← coe_unitStep_eq hL h hk μ, ← hb']
      abel
    · refine ⟨-1, μ, Or.inr rfl, ?_⟩
      have hb' := congrArg (Subtype.val) hb
      rw [AddSubgroup.coe_sub (H := sublattice L m (levelDepth K k)),
        AddSubgroup.coe_neg (H := sublattice L m (levelDepth K k))] at hb'
      rw [shiftBy_eq_add hL hj, neg_one_mul, neg_smul, levelPoint_neg,
        ← coe_unitStep_eq hL h hk μ, ← hb']
      abel
  · rintro ⟨σ, μ, hσ, hx⟩
    rw [shiftBy_eq_add hL hj] at hx
    refine ⟨⟨x, x', μ, ?_⟩, rfl, rfl⟩
    rcases hσ with rfl | rfl
    · left
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, hx, one_mul, ← coe_unitStep_eq hL h hk μ]
      abel
    · right
      apply Subtype.ext
      rw [AddSubgroup.coe_sub, AddSubgroup.coe_neg, hx, neg_one_mul, neg_smul, levelPoint_neg,
        ← coe_unitStep_eq hL h hk μ]
      abel
theorem isPositivelyOriented_iff (hL : 0 < L) (h : j ≤ k) (hk : k ≤ K) (b : BondAtLevel L m K k) :
    b.IsPositivelyOriented ↔ ∃ μ : Fin 4,
      (b.target : FourTorus L m) =
        shiftBy L m K j (b.source : FourTorus L m) ((L : ℝ) ^ (k - j) • coordVec μ) := by
  have hj := h.trans hk
  constructor
  · rintro ⟨μ, hb⟩
    refine ⟨μ, ?_⟩
    have hb' := congrArg (Subtype.val) hb
    rw [AddSubgroup.coe_sub (H := sublattice L m (levelDepth K k))] at hb'
    rw [shiftBy_eq_add hL hj, ← coe_unitStep_eq hL h hk μ, ← hb']
    abel
  · rintro ⟨μ, hx⟩
    refine ⟨μ, ?_⟩
    rw [shiftBy_eq_add hL hj, ← coe_unitStep_eq hL h hk μ] at hx
    apply Subtype.ext
    rw [AddSubgroup.coe_sub, hx]
    abel
theorem sitesAndBondsRescaled_of (hL : 0 < L) (hjk : j ≤ k) (hk : k ≤ K) :
    SitesAndBondsRescaled L m K j k := by
  have hj := hjk.trans hk
  have hP := (levelScale_pos (K := K) (j := j) hL).ne'
  have himage : torusClassOf L m K j = levelPoint L m K j :=
    funext (torusClassOf_eq_levelPoint hL hj)
  refine ⟨?_, ?_, fun y w hw => lift_mem_scaledIntLattice hL hjk hk y w hw,
    sublattice_mono hL m (by unfold levelDepth; omega), ?_, ?_,
    fun x x' => exists_bond_iff hL hjk hk x x', fun b => isPositivelyOriented_iff hL hjk hk b⟩
  · have e := sublattice_eq_image (m := m) hL (le_refl j) hj
    rw [Nat.sub_self, pow_zero] at e
    rw [himage]
    exact e
  · rw [himage]
    exact sublattice_eq_image hL hjk hk
  · rw [toLevelUnits_eq_mul hj, meshSize_eq hL (le_refl j) hj, mul_inv_cancel_left₀ hP,
      Nat.sub_self, pow_zero]
  · rw [toLevelUnits_eq_mul hj, meshSize_eq hL hjk hk, mul_inv_cancel_left₀ hP]
theorem exists_minimal_lift (x : FourTorus L m) : ∃ b : Fin 4 → ℝ,
    TorusMetric.torusProj (torusSide L m) b = x ∧
    TorusMetric.torusSupNorm x = TorusMetric.supNormVec b ∧
    ∀ v, TorusMetric.torusProj (torusSide L m) v = x →
      TorusMetric.supNormVec b ≤ TorusMetric.supNormVec v := by
  choose b hb hb' using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (x μ)
  have hcov : TorusMetric.torusProj (torusSide L m) b = x := funext hb
  have hmin : ∀ v, TorusMetric.torusProj (torusSide L m) v = x →
      TorusMetric.supNormVec b ≤ TorusMetric.supNormVec v := by
    intro v hv
    refine Finset.sup'_le _ _ fun μ _ => ?_
    have e : x μ = (v μ : AddCircle (torusSide L m)) := (congrFun hv μ).symm
    calc |b μ| = ‖x μ‖ := hb' μ
      _ = ‖(v μ : AddCircle (torusSide L m))‖ := by rw [e]
      _ ≤ |v μ| := TorusMetric.addCircle_norm_coe_le_abs _
      _ ≤ _ := Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
  refine ⟨b, hcov, le_antisymm ?_ ?_, hmin⟩
  · refine csInf_le ⟨TorusMetric.supNormVec b, ?_⟩ ⟨b, hcov, rfl⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmin v hv
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hmin v hv
theorem supNormVec_of_scale {P : ℝ} (hP : 0 ≤ P) (v w : Fin 4 → ℝ) (hw : ∀ μ, w μ = P * v μ) :
    supNormVec w = P * TorusMetric.supNormVec v := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [hw μ, abs_mul, abs_of_nonneg hP]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)) hP
  · obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun μ => |v μ|)
    rw [TorusMetric.supNormVec, hμ]
    calc P * |v μ| = |w μ| := by rw [hw μ, abs_mul, abs_of_nonneg hP]
      _ ≤ supNormVec w := Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ μ)
theorem supNormAndCubesRescaled_of (hL : 0 < L) (hjk : j ≤ k) (hk : k ≤ K) :
    SupNormAndCubesRescaled L m K j k := by
  have hj := hjk.trans hk
  have hP := levelScale_pos (K := K) (j := j) hL
  refine ⟨fun x => ?_, fun y => ?_⟩
  · obtain ⟨b, hcov, hs, hmin⟩ := exists_minimal_lift x
    rw [toLevelUnits_eq_mul hj, hs]
    constructor
    · exact ⟨fun μ => levelScale L K j * b μ,
        ⟨b, fun μ => congrFun hcov μ, fun μ => (toLevelUnits_eq_mul hj _).symm⟩,
        supNormVec_of_scale hP.le b _ fun _ => rfl⟩
    · rintro _ ⟨w, ⟨v, hv, hw⟩, rfl⟩
      have hw' : ∀ μ, w μ = levelScale L K j * v μ := fun μ => by
        rw [hw μ, toLevelUnits_eq_mul hj]
      rw [supNormVec_of_scale hP.le v w hw']
      exact mul_le_mul_of_nonneg_left (hmin v (funext hv)) hP.le
  · ext z
    simp only [cubeAround, mem_ofPred_eq]
    rw [toLevelUnits_eq_mul hj, meshSize_eq hL hjk hk, mul_div_assoc, le_inv_mul_iff₀ hP]
theorem halfWidthProperties_of (hodd : Odd L) (n : ℕ) : HalfWidthProperties L n := by
  obtain ⟨c, hc⟩ := hodd.pow (n := n)
  have hc' : (L : ℝ) ^ n = 2 * c + 1 := by exact_mod_cast hc
  have e : halfWidth L n = c := by
    rw [halfWidth, hc']
    ring
  refine ⟨⟨(c : ℤ), by rw [e]; simp⟩, by rw [e]; positivity, by rw [e, hc'], ?_⟩
  simp [halfWidth]
theorem rescaledLatticeStatement_holds : RescaledLatticeStatement := by
  intro L m K hL hm _ j k hjk hk
  have hpos : 0 < L := by
    have := hL.2
    omega
  exact ⟨levelSideFacts_of hL.2 hm hjk hk, liftCosetFacts_of hpos (hjk.trans hk),
    sitesAndBondsRescaled_of hpos hjk hk, supNormAndCubesRescaled_of hpos hjk hk,
    halfWidthProperties_of hL.1 _⟩
end YangMills.Construction.PeriodicLattice.LevelUnits
