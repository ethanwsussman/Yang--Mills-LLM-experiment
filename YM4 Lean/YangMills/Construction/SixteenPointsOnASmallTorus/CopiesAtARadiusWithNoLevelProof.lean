import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAtARadiusWithNoLevel
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadius
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction.SmallTorusCopies
variable {m : ℕ}
private def directionIndicator (a b i : Fin 4) : ℕ := (if i = a then 1 else 0) + (if i = b then 1 else 0)
private theorem directionIndicator_le : ∀ a b : Fin 4, a < b → ∀ i, directionIndicator a b i ≤ 1 := by decide +kernel
private theorem directionIndicator_inj : ∀ a b a' b' : Fin 4, a < b → a' < b' →
    (∀ i, directionIndicator a b i = directionIndicator a' b' i) → a = a' ∧ b = b' := by
  decide +kernel
private theorem doubledBarycentre_val [NeZero m] (p : TorusFields.TorusPlaquette m) (hp : p.2.1 < p.2.2) (i : Fin 4) :
    (WeightedResponses.doubledBarycentre p i).val = 2 * (p.1 i).val + directionIndicator p.2.1 p.2.2 i := by
  have hv := ZMod.val_lt (p.1 i)
  have ha := directionIndicator_le _ _ hp i
  have e : WeightedResponses.doubledBarycentre p i =
      ((2 * (p.1 i).val + directionIndicator p.2.1 p.2.2 i : ℕ) : ZMod (2 * m)) := by
    unfold WeightedResponses.doubledBarycentre directionIndicator
    simp only [add_assoc]
  rw [e, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)
private theorem doubledBarycentre_injective [NeZero m] {p q : TorusFields.TorusPlaquette m}
    (hp : p.2.1 < p.2.2) (hq : q.2.1 < q.2.2)
    (h : WeightedResponses.doubledBarycentre p = WeightedResponses.doubledBarycentre q) : p = q := by
  have hv : ∀ i, 2 * (p.1 i).val + directionIndicator p.2.1 p.2.2 i =
      2 * (q.1 i).val + directionIndicator q.2.1 q.2.2 i := fun i => by
    rw [← doubledBarycentre_val p hp, ← doubledBarycentre_val q hq, h]
  have hval : ∀ i, (p.1 i).val = (q.1 i).val := fun i => by
    have h0 := hv i
    have h1 := directionIndicator_le _ _ hp i
    have h2 := directionIndicator_le _ _ hq i
    omega
  have hdir : ∀ i, directionIndicator p.2.1 p.2.2 i = directionIndicator q.2.1 q.2.2 i := fun i => by
    have h0 := hv i
    have h1 := hval i
    omega
  obtain ⟨h1, h2⟩ := directionIndicator_inj _ _ _ _ hp hq hdir
  have h3 : p.1 = q.1 := funext fun i => ZMod.val_injective m (hval i)
  exact Prod.ext h3 (Prod.ext h1 h2)
abbrev _root_.YangMills.SharedProofs.p2545 := @doubledBarycentre_injective
private def reflectedBarycentre (M : ℕ) (k : Fin 4 → ℕ) (p : TorusFields.TorusPlaquette m) : Fin 4 → ℤ := fun μ =>
  ((-1 : ZMod (2 * m)) ^ k μ *
    (WeightedResponses.doubledBarycentre p μ - 2 * (M : ZMod (2 * m)) * (k μ : ZMod (2 * m)))).valMinAbs
private theorem reflectedPoint_apply (a₀ : ℝ) (M : ℕ) (k : Fin 4 → ℕ) (p : TorusFields.TorusPlaquette m) (μ : Fin 4) :
    reflectedPoint a₀ M k p μ = a₀ / 2 * (reflectedBarycentre M k p μ : ℝ) := rfl
private theorem reflectedBarycentre_injective (M : ℕ) (k : Fin 4 → ℕ) {p q : TorusFields.TorusPlaquette m}
    (h : reflectedBarycentre M k p = reflectedBarycentre M k q) :
    WeightedResponses.doubledBarycentre p = WeightedResponses.doubledBarycentre q := by
  funext μ
  have h2 := congrArg (fun z : ℤ => (z : ZMod (2 * m))) (congrFun h μ)
  simp only [reflectedBarycentre, ZMod.coe_valMinAbs] at h2
  have hu : ((-1 : ZMod (2 * m)) ^ k μ) * ((-1 : ZMod (2 * m)) ^ k μ) = 1 := by
    rw [← mul_pow]
    simp
  have h3 := congrArg (fun z => (-1 : ZMod (2 * m)) ^ k μ * z) h2
  simp only [← mul_assoc, hu, one_mul] at h3
  exact sub_left_inj.mp h3
private theorem abs_coord_sub_le {x c : TestFunctions.EuclideanFourSpace} {ρ : ℝ} (h : dist x c ≤ ρ) (μ : Fin 4) :
    |x μ - c μ| ≤ ρ := by
  have h1 := PiLp.norm_apply_le (x - c) μ
  rw [dist_eq_norm] at h
  have h2 := h1.trans h
  simpa [Real.norm_eq_abs] using h2
private theorem card_support_le [NeZero m] {a₀ ρ : ℝ} (ha : 0 < a₀) (hρ : 0 < ρ) (M : ℕ) (k : Fin 4 → ℕ)
    (h : TestFunctions.EuclideanFourSpace → ℝ) (c : TestFunctions.EuclideanFourSpace)
    (hc : ∀ x, h x ≠ 0 → dist x c ≤ ρ) :
    ((((TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m))).filter
        fun p => h (reflectedPoint a₀ M k p) ≠ 0).card : ℕ) : ℝ) ≤
      (4 * ρ / a₀ + 1) ^ 4 := by
  classical
  set S := (TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m))).filter
    fun p => h (reflectedPoint a₀ M k p) ≠ 0 with hS
  set N : ℤ := ⌊4 * ρ / a₀⌋ with hN
  set e : Fin 4 → ℤ := fun μ => ⌈2 * (c μ - ρ) / a₀⌉ with he
  have hmaps : ∀ p ∈ S, reflectedBarycentre M k p ∈ Fintype.piFinset fun μ => Finset.Icc (e μ) (e μ + N) := by
    intro p hp
    rw [Fintype.mem_piFinset]
    intro μ
    have hp' := (Finset.mem_filter.mp hp).2
    have hd := abs_coord_sub_le (hc _ hp') μ
    rw [reflectedPoint_apply] at hd
    obtain ⟨h1, h2⟩ := abs_le.mp hd
    set d : ℤ := reflectedBarycentre M k p μ with hdd
    have hlow : 2 * (c μ - ρ) / a₀ ≤ (d : ℝ) := by
      rw [div_le_iff₀ ha]
      nlinarith
    have hup : (d : ℝ) ≤ 2 * (c μ + ρ) / a₀ := by
      rw [le_div_iff₀ ha]
      nlinarith
    have hle : e μ ≤ d := Int.ceil_le.mpr hlow
    have hce : 2 * (c μ - ρ) / a₀ ≤ (e μ : ℝ) := Int.le_ceil _
    have hdiff : ((d - e μ : ℤ) : ℝ) ≤ 4 * ρ / a₀ := by
      have e1 : 4 * ρ / a₀ = 2 * (c μ + ρ) / a₀ - 2 * (c μ - ρ) / a₀ := by
        field_simp
        ring
      push_cast
      rw [e1]
      linarith
    have hfl : d - e μ ≤ N := Int.le_floor.mpr hdiff
    exact Finset.mem_Icc.mpr ⟨hle, by omega⟩
  have hinj : Set.InjOn (reflectedBarycentre M k) (S : Set (TorusFields.TorusPlaquette m)) := by
    intro p hp q hq hpq
    have o : p.2.1 < p.2.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have o' : q.2.1 < q.2.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    exact doubledBarycentre_injective o o' (reflectedBarycentre_injective M k hpq)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Fintype.card_piFinset] at hcard
  simp only [Int.card_Icc] at hcard
  have hq : 0 ≤ 4 * ρ / a₀ := by positivity
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr hq
  have hcount : ∀ μ, (e μ + N + 1 - e μ).toNat = (N + 1).toNat := fun μ => by
    congr 1
    ring
  simp only [hcount, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  have hcast : (((N + 1).toNat : ℕ) : ℝ) ≤ 4 * ρ / a₀ + 1 := by
    have e2 : (((N + 1).toNat : ℕ) : ℤ) = N + 1 := Int.toNat_of_nonneg (by omega)
    have e3 : (((N + 1).toNat : ℕ) : ℝ) = (N : ℝ) + 1 := by exact_mod_cast e2
    rw [e3]
    have := Int.floor_le (4 * ρ / a₀)
    linarith
  calc ((S.card : ℕ) : ℝ) ≤ ((((N + 1).toNat ^ 4 : ℕ)) : ℝ) := by exact_mod_cast hcard
    _ = (((N + 1).toNat : ℕ) : ℝ) ^ 4 := by push_cast; rfl
    _ ≤ (4 * ρ / a₀ + 1) ^ 4 := pow_le_pow_left₀ (by positivity) hcast 4
private theorem plaquetteEnergyOf_le_two (W : TorusFields.TorusField m) (p : TorusFields.TorusPlaquette m) :
    WeightedResponses.plaquetteEnergyOf W p ≤ 2 := by
  unfold WeightedResponses.plaquetteEnergyOf TorusFields.plaquetteEnergy
  have h := TorusFrame.abs_re_le_norm
    ((TorusFields.holonomy W p.1 p.2.1 p.2.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ])
  rw [TorusFields.norm_unitQuaternion] at h
  have := (abs_le.mp h).1
  linarith
abbrev _root_.YangMills.SharedProofs.p24501 := @plaquetteEnergyOf_le_two
private theorem abs_curvatureObservable_le [NeZero m] {H : ℝ} (hH : 0 ≤ H) (w : WeightedResponses.PlaquetteWeight m)
    (hw : ∀ p, |w p| ≤ H) (W : TorusFields.TorusField m) :
    |WeightedResponses.curvatureObservable w W| ≤
      (((TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m))).filter
        fun p => w p ≠ 0).card : ℝ) * (2 * H) := by
  classical
  unfold WeightedResponses.curvatureObservable
  calc |∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
          w p * WeightedResponses.plaquetteEnergyOf W p|
      ≤ ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
          |w p * WeightedResponses.plaquetteEnergyOf W p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
          (if w p ≠ 0 then 2 * H else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have e0 : 0 ≤ WeightedResponses.plaquetteEnergyOf W p := TorusFields.plaquetteEnergy_nonneg _ _ _ _
        have e2 := plaquetteEnergyOf_le_two W p
        split_ifs with hp
        · rw [abs_mul, abs_of_nonneg e0]
          nlinarith [hw p, abs_nonneg (w p)]
        · have hp' : w p = 0 := not_not.mp hp
          simp [hp']
    _ = ∑ p ∈ (TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m))).filter
          (fun p => w p ≠ 0), 2 * H := (Finset.sum_filter _ _).symm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
private theorem clusterRange_bounds {β : ℝ} (hβ : 1 ≤ β) :
    1 ≤ (TorusLumps.clusterRange β : ℝ) ∧
      (TorusLumps.clusterRange β : ℝ) ^ 4 ≤ 16 * β ^ ((1 : ℝ) / 25) := by
  set u : ℝ := β ^ ((1 : ℝ) / 100) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hβ (by norm_num)
  have hup : (TorusLumps.clusterRange β : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlow : u ≤ (TorusLumps.clusterRange β : ℝ) := Nat.le_ceil _
  have h4 : u ^ 4 = β ^ ((1 : ℝ) / 25) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h1 : 1 ≤ (TorusLumps.clusterRange β : ℝ) := hu1.trans hlow
  refine ⟨h1, ?_⟩
  have h2 : (TorusLumps.clusterRange β : ℝ) ≤ 2 * u := by linarith
  calc (TorusLumps.clusterRange β : ℝ) ^ 4 ≤ (2 * u) ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
    _ = 16 * β ^ ((1 : ℝ) / 25) := by rw [← h4]; ring
private theorem one_add_logPos_nonneg (t : ℝ) : 0 ≤ 1 + TorusBound.logPos t := by
  have : 0 ≤ TorusBound.logPos t := le_max_right _ _
  linarith
private theorem count_times_bound_le {β ρ a₀ H C₁ G n : ℝ} (hβ : 1 ≤ β) (ha : 0 < a₀) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hC₁ : 0 ≤ C₁) (hG : 0 ≤ 1 + G)
    (hlt : ρ < 2 ^ 11 * (TorusLumps.clusterRange β : ℝ) * a₀) (hcoup : β ≤ C₁ * (1 + G))
    (hn : n ≤ (4 * ρ / a₀ + 1) ^ 4) :
    n * (2 * H) ≤ 2 ^ 61 * C₁ ^ ((1 : ℝ) / 25) * (1 + G) ^ ((1 : ℝ) / 25) * H := by
  obtain ⟨hr1, hr4⟩ := clusterRange_bounds hβ
  set r : ℝ := (TorusLumps.clusterRange β : ℝ) with hr
  have hq : 4 * ρ / a₀ ≤ 2 ^ 13 * r := by
    rw [div_le_iff₀ ha]
    nlinarith
  have hq1 : 4 * ρ / a₀ + 1 ≤ 2 ^ 14 * r := by linarith
  have hq0 : 0 ≤ 4 * ρ / a₀ + 1 := by positivity
  have hp : (4 * ρ / a₀ + 1) ^ 4 ≤ 2 ^ 60 * β ^ ((1 : ℝ) / 25) := by
    calc (4 * ρ / a₀ + 1) ^ 4 ≤ (2 ^ 14 * r) ^ 4 := pow_le_pow_left₀ hq0 hq1 4
      _ = 2 ^ 56 * r ^ 4 := by ring
      _ ≤ 2 ^ 56 * (16 * β ^ ((1 : ℝ) / 25)) := by gcongr
      _ = 2 ^ 60 * β ^ ((1 : ℝ) / 25) := by ring
  have hb : β ^ ((1 : ℝ) / 25) ≤ C₁ ^ ((1 : ℝ) / 25) * (1 + G) ^ ((1 : ℝ) / 25) := by
    rw [← Real.mul_rpow hC₁ hG]
    exact Real.rpow_le_rpow (by linarith) hcoup (by norm_num)
  calc n * (2 * H) ≤ (2 ^ 60 * (C₁ ^ ((1 : ℝ) / 25) * (1 + G) ^ ((1 : ℝ) / 25))) * (2 * H) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact (hn.trans hp).trans (by gcongr)
    _ = _ := by ring
theorem copyBoundWithoutLevel_of_couplingAtRadiusLevel (hc : couplingAtRadiusLevelStatement) :
    copyBoundWithoutLevelStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hT⟩ := hc a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ T hTa hTL hD hCS hCH hrtT hCd => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hT L hL hL₀ T hTa hTL hD hCS hCH hrtT hCd
  refine ⟨max y₀ 1, fun y hy hR hW Ξ hΞ => ?_⟩
  obtain ⟨C₁, hC₁, hcoup⟩ := hy₀ y ((le_max_left _ _).trans hy) hR hW Ξ hΞ
  refine ⟨2 ^ 61 * C₁ ^ ((1 : ℝ) / 25), by positivity, fun β K κ ρ H Λ h hd hκ hρ hρl hs hn k W => ?_⟩
  have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
  have hβy : y ≤ β := hd.coupling_ge 0 (Nat.zero_le _)
  have hβ : 1 ≤ β := hy1.trans hβy
  have ha₀ : 0 < levelSpacing T.side K 0 := by
    unfold levelSpacing
    exact zpow_pos (Nat.cast_pos.mpr (NeZero.pos _)) _
  have hnofit : ¬ FitsAtLevel (T.stepParameters y) β K ρ 0 := by
    intro hf
    unfold radiusLevel at hn
    rw [if_pos ⟨0, Nat.zero_le _, hf⟩] at hn
    exact absurd hn (by simp)
  have hlt : ρ < 2 ^ 11 * (TorusLumps.clusterRange β : ℝ) * levelSpacing T.side K 0 := not_le.mp hnofit
  have hH : 0 ≤ H := (abs_nonneg _).trans (hs.abs_le 0)
  obtain ⟨c, hcb⟩ := hs.exists_ball
  have hb : β ≤ C₁ * (1 + TorusBound.logPos (1 / ρ)) := (hcoup β K ρ hd hρ).2 hn
  have hcount := card_support_le (m := 2 * T.side ^ κ) ha₀ hρ (T.side ^ κ) (fun μ => (k μ : ℕ)) h c hcb
  have hobs := abs_curvatureObservable_le hH
    (reflectedWeight (levelSpacing T.side K 0) (T.side ^ κ) (fun μ => (k μ : ℕ)) h : WeightedResponses.PlaquetteWeight (2 * T.side ^ κ))
    (fun p => hs.abs_le _) W
  exact hobs.trans (count_times_bound_le hβ ha₀ hρ hH hC₁ (one_add_logPos_nonneg _) hlt hb hcount)
end YangMills.Construction.SmallTorusCopies
end
