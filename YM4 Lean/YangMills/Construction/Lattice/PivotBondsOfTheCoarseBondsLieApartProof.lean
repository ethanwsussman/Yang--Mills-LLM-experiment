import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Lattice.ContoursWithinBlocks
import YangMills.Construction.Lattice.DoubleBlockOfACoarseBond
import YangMills.Construction.Lattice.DoubleBlockStraightPathCorridorAndPivotBond
import YangMills.Construction.Lattice.PivotBondsOfTheCoarseBondsLieApart
import Mathlib
open Set
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.PivotPlacement
variable {L m K k : ℕ}
private theorem coe_toSublattice_of_mem {j j' : ℤ} (y : Site L m j)
    (hy : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
private theorem coord_zsmul_unitStep (j : ℤ) (a : ℤ) (μ : Fin 4) :
    ((a • unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      (((a : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  have hcoord : ((a • unitStep L m j μ : Site L m j) : FourTorus L m) μ =
      a • ((meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
    simp [unitStep, pointOnAxis]
  rw [hcoord, ← AddCircle.coe_zsmul, zsmul_eq_mul]
abbrev _root_.YangMills.SharedProofs.p4610 := @coord_zsmul_unitStep
private theorem coord_zsmul_unitStep_of_ne (j : ℤ) (a : ℤ) {μ ν : Fin 4} (hne : μ ≠ ν) :
    ((a • unitStep L m j ν : Site L m j) : FourTorus L m) μ = 0 := by
  simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hne]
private theorem coe_addCircle_ne_zero {t : ℝ} (hs : 0 < torusSide L m) (ht0 : t ≠ 0)
    (ht : |t| < torusSide L m) :
    (t : AddCircle (torusSide L m)) ≠ 0 := by
  intro hz
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hz
  have hn' : (n : ℝ) * torusSide L m = t := by simpa using hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ht0 (by simpa using hn'.symm)
  have hone : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  rw [← hn', abs_mul, abs_of_pos hs] at ht
  nlinarith
private theorem eq_zero_of_zsmul_unitStep_eq_zero {j : ℤ} {a : ℤ} {μ : Fin 4}
    (hs : 0 < torusSide L m) (hmesh : 0 < meshSize L j) (hz : a • unitStep L m j μ = 0)
    (hsmall : |(a : ℝ)| * meshSize L j < torusSide L m) : a = 0 := by
  by_contra ha
  have h0 : (((a : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [← coord_zsmul_unitStep, hz]
    rfl
  refine coe_addCircle_ne_zero hs (mul_ne_zero (by exact_mod_cast ha) hmesh.ne') ?_ h0
  rwa [abs_mul, abs_of_pos hmesh]
private theorem eq_zero_of_zsmul_unitStep_eq {j : ℤ} {a b : ℤ} {μ ν : Fin 4}
    (hs : 0 < torusSide L m) (hmesh : 0 < meshSize L j) (hne : μ ≠ ν)
    (heq : a • unitStep L m j ν = b • unitStep L m j μ)
    (hsmall : |(b : ℝ)| * meshSize L j < torusSide L m) : b = 0 := by
  by_contra hb0
  have h0 : (((b : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [← coord_zsmul_unitStep, ← heq]
    exact coord_zsmul_unitStep_of_ne j a hne
  refine coe_addCircle_ne_zero hs (mul_ne_zero (by exact_mod_cast hb0) hmesh.ne') ?_ h0
  rwa [abs_mul, abs_of_pos hmesh]
private theorem two_mul_le_torusSide (hL : 13 ≤ L) (hm : 0 < m) :
    2 * (L : ℝ) ≤ torusSide L m := by
  have hL' : (1 : ℝ) ≤ L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hpow : (L : ℝ) ≤ (L : ℝ) ^ m := le_self_pow₀ hL' hm.ne'
  rw [torusSide]
  linarith
private theorem meshSize_pos_of_le (hL : 13 ≤ L) (j : ℤ) : 0 < meshSize L j := by
  have : (0 : ℝ) < L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  exact zpow_pos this _
private theorem meshSize_le_one_of_le (hL : 13 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    meshSize L j ≤ 1 := by
  have : (1 : ℝ) ≤ L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  exact zpow_le_one_of_nonpos₀ this (by omega)
private theorem axial_displacement_unique (hL : 13 ≤ L) (hm : 0 < m) {j : ℤ} (hj : 1 ≤ j)
    {ν μ : Fin 4} {n : ℤ} (heq : n • unitStep L m j ν = (L : ℤ) • unitStep L m j μ)
    (hsmall : ((|n| : ℤ) : ℝ) < (L : ℝ) ^ ((m : ℤ) + j)) : ν = μ ∧ n = L := by
  have hmesh := meshSize_pos_of_le (L := L) hL j
  have hmesh1 := meshSize_le_one_of_le (L := L) hL (j := j) (by omega)
  have hside := two_mul_le_torusSide (L := L) (m := m) hL hm
  have hLr : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : 0 < torusSide L m := by linarith
  have hLsmall : |((L : ℤ) : ℝ)| * meshSize L j < torusSide L m := by
    have : |((L : ℤ) : ℝ)| = L := by simp
    rw [this]
    nlinarith
  by_cases hνμ : ν = μ
  · subst hνμ
    refine ⟨rfl, ?_⟩
    have h0 : (n - L) • unitStep L m j ν = 0 := by rw [sub_zsmul, heq, add_neg_cancel]
    have hL0 : (L : ℝ) ≠ 0 := by linarith
    have hnb : ((|n| : ℤ) : ℝ) * meshSize L j < (L : ℝ) ^ m := by
      have hprod : (L : ℝ) ^ ((m : ℤ) + j) * meshSize L j = (L : ℝ) ^ m := by
        rw [meshSize, ← zpow_add₀ hL0]
        simp
      rw [← hprod]
      exact mul_lt_mul_of_pos_right hsmall hmesh
    have hdiff : |((n - L : ℤ) : ℝ)| * meshSize L j < torusSide L m := by
      have htri : |((n - L : ℤ) : ℝ)| ≤ ((|n| : ℤ) : ℝ) + L := by
        push_cast
        exact (abs_sub _ _).trans (by simp)
      have hsideEq : torusSide L m = 2 * (L : ℝ) ^ m := rfl
      nlinarith
    have := eq_zero_of_zsmul_unitStep_eq_zero hs hmesh h0 hdiff
    omega
  · have := eq_zero_of_zsmul_unitStep_eq hs hmesh (Ne.symm hνμ) heq hLsmall
    omega
private theorem axialPath_eq_map_range (hL : 13 ≤ L) (hm : 0 < m) {j : ℤ} (hj : 1 ≤ j)
    (x : Site L m j) (μ : Fin 4) :
    axialPath x (x + (L : ℤ) • unitStep L m j μ) =
      (List.range L).map fun i : ℕ => Bond.forwardFrom (x + (i : ℤ) • unitStep L m j μ) μ := by
  have hLr : (13 : ℝ) ≤ L := by exact_mod_cast hL
  have hex : ∃ q : Fin 4 × ℤ,
      IsAxialDisplacement x (x + (L : ℤ) • unitStep L m j μ) q.1 q.2 := by
    refine ⟨(μ, L), by simp, ?_⟩
    have hlt : (L : ℝ) ^ (1 : ℤ) < (L : ℝ) ^ ((m : ℤ) + j) :=
      zpow_lt_zpow_right₀ (by linarith) (by omega)
    simpa using hlt
  rw [axialPath, dif_pos hex]
  obtain ⟨hq1, hq2⟩ := hex.choose_spec
  obtain ⟨hν, hn⟩ := axial_displacement_unique hL hm hj
    (show hex.choose.2 • unitStep L m j hex.choose.1 = (L : ℤ) • unitStep L m j μ by
      rw [← hq1]; abel) hq2
  rw [hν, hn]
  have hrun : ∀ (n : ℕ) (y : Site L m j), forwardAxisPath y μ n =
      (List.range n).map fun i : ℕ => Bond.forwardFrom (y + (i : ℤ) • unitStep L m j μ) μ := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [forwardAxisPath, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1
        push_cast
        rw [add_zsmul, one_zsmul]
        abel
  simp only [flowAlong, Int.natCast_nonneg, if_true, Int.toNat_natCast]
  exact hrun L x
theorem pivotBondsLieApart_holds (hBlock : CoarseBondDoubleBlock.Statement)
    (hCorridor : DoubleBlockGeometryClaim)
    (hContours : ContoursWithinBlockStatement) :
    PivotBondsLieApart := by
  intro L m K k hL hm hk c₀ μ hc
  obtain ⟨c, hcpos⟩ := c₀
  change c.target - c.source = unitStep L m (levelDepth K (k + 1)) μ at hc
  have hL13 := hL.2
  have hK : 0 < K := by omega
  have hLr : (13 : ℝ) ≤ L := by exact_mod_cast hL13
  have hside := two_mul_le_torusSide (L := L) (m := m) hL13 hm
  have hs : 0 < torusSide L m := by linarith
  have hdepth : 1 ≤ levelDepth K k := by simp only [levelDepth]; omega
  have hdepth' : 0 ≤ levelDepth K (k + 1) := by simp only [levelDepth]; push_cast; omega
  have hmesh := meshSize_pos_of_le (L := L) hL13 (levelDepth K k)
  have hmesh1 := meshSize_le_one_of_le (L := L) hL13 (j := levelDepth K k) (by omega)
  have hmeshc := meshSize_pos_of_le (L := L) hL13 (levelDepth K (k + 1))
  have hmeshc1 := meshSize_le_one_of_le (L := L) hL13 hdepth'
  have hParams : Averaging.LayerwiseParameters 4 2 L K m
      Matrices.ComplexMatrix2.specialUnitary (torusSide L m) :=
    ⟨rfl, rfl, rfl, hL.1, hL13, hK, hm, rfl⟩
  have hAxial : AxialPathCorridorProperties c μ := ((hCorridor L K m hParams).2 k hk).1 c μ hc
  have hDouble : ∀ c' : BondAtLevel L m K (k + 1), c'.IsPositivelyOriented →
      CoarseBondDoubleBlock c' := by
    rintro c' ⟨ν, hν⟩
    exact hBlock L m K k c' ν ⟨hL, hK, hm, hk, hν⟩
  have hDc := hDouble c ⟨μ, hc⟩
  have hnotOpp : ∀ c' : BondAtLevel L m K (k + 1), c'.IsPositivelyOriented →
      ¬c'.opposite.IsPositivelyOriented := by
    rintro c' ⟨ν, hν⟩ ⟨ρ, hρ⟩
    have hρ' : c'.source - c'.target = unitStep L m (levelDepth K (k + 1)) ρ := hρ
    have hsum : unitStep L m (levelDepth K (k + 1)) ρ = -unitStep L m (levelDepth K (k + 1)) ν := by
      rw [← hρ', ← hν]; abel
    by_cases hρν : ρ = ν
    · subst hρν
      have h2 : (2 : ℤ) • unitStep L m (levelDepth K (k + 1)) ρ = 0 := by
        rw [two_zsmul]
        nth_rewrite 1 [hsum]
        abel
      have := eq_zero_of_zsmul_unitStep_eq_zero hs hmeshc h2 (by
        have : |((2 : ℤ) : ℝ)| = 2 := by simp
        rw [this]
        nlinarith)
      omega
    · have h1 : (1 : ℤ) • unitStep L m (levelDepth K (k + 1)) ρ =
          (-1 : ℤ) • unitStep L m (levelDepth K (k + 1)) ν := by
        simpa using hsum
      have := eq_zero_of_zsmul_unitStep_eq hs hmeshc (Ne.symm hρν) h1 (by
        have : |((-1 : ℤ) : ℝ)| = 1 := by simp
        rw [this]
        nlinarith)
      omega
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (h : ℤ) = centreToFaceSteps L :=
    ⟨(centreToFaceSteps L).toNat, Int.toNat_of_nonneg (by unfold centreToFaceSteps; omega)⟩
  have hodd : 2 * (h : ℤ) + 1 = (L : ℤ) := by
    obtain ⟨t, ht⟩ := hL.1
    rw [hh]
    unfold centreToFaceSteps
    omega
  have hnat : (centreToFaceSteps L).toNat = h := by rw [← hh]; simp
  have hpiv : (pivot c : BondAtLevel L m K k) =
      Bond.forwardFrom (c.source.toSublattice (levelDepth K k) +
        (h : ℤ) • unitStep L m (levelDepth K k) μ) μ := by
    rw [hAxial.pivot_eq, hnat]
    rfl
  have hin : ∀ y : SiteAtLevel L m K (k + 1),
      (y : FourTorus L m) ∈ sublattice L m (levelDepth K k) := fun y =>
    sublattice_mono (by omega) m (by simp only [levelDepth]; push_cast; omega) y.2
  have hshift : ∀ x : SiteAtLevel L m K k,
      shiftAcross c x = x + (L : ℤ) • unitStep L m (levelDepth K k) μ := by
    intro x
    have e1 := congrArg (fun z : SiteAtLevel L m K k => (z : FourTorus L m)) hAxial.target_eq
    simp only [AddSubgroup.coe_add, coe_toSublattice_of_mem _ (hin _)] at e1
    rw [shiftAcross]
    congr 1
    apply Subtype.ext
    rw [coe_toSublattice_of_mem _ (hin _), AddSubgroup.coe_sub, e1, add_sub_cancel_left]
  have hcross : ∀ x : SiteAtLevel L m K k, crossingPath c x =
      (List.range L).map fun i : ℕ =>
        Bond.forwardFrom (x + (i : ℤ) • unitStep L m (levelDepth K k) μ) μ := by
    intro x
    rw [crossingPath, hshift]
    exact axialPath_eq_map_range hL13 hm hdepth x μ
  have hmem : ∀ (x : SiteAtLevel L m K k) (b : BondAtLevel L m K k), b ∈ crossingPath c x ↔
      ∃ i : ℕ, i < L ∧ Bond.forwardFrom (x + (i : ℤ) • unitStep L m (levelDepth K k) μ) μ = b := by
    intro x b
    rw [hcross]
    simp
  have hfwd : ∀ y y' : SiteAtLevel L m K k, Bond.forwardFrom y μ = Bond.forwardFrom y' μ → y = y' :=
    fun y y' e => congrArg Bond.source e
  have hsmall : ∀ a : ℤ, |a| < (L : ℤ) → a • unitStep L m (levelDepth K k) μ = 0 → a = 0 := by
    intro a ha h0
    refine eq_zero_of_zsmul_unitStep_eq_zero hs hmesh h0 ?_
    have h1 : |(a : ℝ)| < L := by exact_mod_cast ha
    have h2 : 0 ≤ |(a : ℝ)| := abs_nonneg _
    nlinarith
  have hnodup : ∀ x : SiteAtLevel L m K k, (crossingPath c x).Nodup := by
    intro x
    rw [hcross]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro i hi i' hi' e
    have hi1 : i < L := List.mem_range.1 hi
    have hi2 : i' < L := List.mem_range.1 hi'
    have e1 := add_left_cancel (hfwd _ _ e)
    have h0 : ((i : ℤ) - (i' : ℤ)) • unitStep L m (levelDepth K k) μ = 0 := by
      rw [sub_zsmul, e1, add_neg_cancel]
    have := hsmall _ (by rw [abs_lt]; omega) h0
    omega
  have hiff : ∀ x : SiteAtLevel L m K k,
      (pivot c : BondAtLevel L m K k) ∈ crossingPath c x ↔
        ∃ n : ℤ, 2 * |n| ≤ (L : ℤ) - 1 ∧
          x = c.source.toSublattice (levelDepth K k) + n • unitStep L m (levelDepth K k) μ := by
    intro x
    rw [hmem, hpiv]
    constructor
    · rintro ⟨i, hi, e⟩
      have e1 := hfwd _ _ e
      refine ⟨(h : ℤ) - (i : ℤ), ?_, ?_⟩
      · rcases abs_cases ((h : ℤ) - (i : ℤ)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
      · rw [sub_zsmul, ← add_assoc, ← e1]
        abel
    · rintro ⟨n, hn, rfl⟩
      have hn' : -(h : ℤ) ≤ n ∧ n ≤ (h : ℤ) := by
        rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at hn <;> omega
      refine ⟨((h : ℤ) - n).toNat, by omega, ?_⟩
      have hi : ((((h : ℤ) - n).toNat : ℕ) : ℤ) = (h : ℤ) - n := Int.toNat_of_nonneg (by omega)
      rw [hi, sub_zsmul]
      congr 1
      abel
  have hsite : ∀ n : ℤ, 2 * |n| ≤ (L : ℤ) - 1 →
      c.source.toSublattice (levelDepth K k) + n • unitStep L m (levelDepth K k) μ ∈
        sitesInBlock (levelDepth K k) c.source := by
    intro n hn
    change ((c.source.toSublattice (levelDepth K k) + n • unitStep L m (levelDepth K k) μ :
      SiteAtLevel L m K k) : FourTorus L m) ∈ unitBlock c.source
    rw [hAxial.source_block]
    refine ⟨Pi.single μ n, ?_, ?_⟩
    · intro ν
      by_cases hνμ : ν = μ
      · subst hνμ
        rw [Pi.single_eq_same, ← hh]
        omega
      · rw [Pi.single_eq_of_ne hνμ, abs_zero, ← hh]
        omega
    · have hw : offsetSite (c.source.toSublattice (levelDepth K k)) (Pi.single μ n) =
          c.source.toSublattice (levelDepth K k) + n • unitStep L m (levelDepth K k) μ := by
        unfold offsetSite
        congr 1
        rw [Finset.sum_eq_single μ]
        · simp
        · intro ν _ hνμ
          simp [Pi.single_eq_of_ne hνμ]
        · simp
      rw [hw]
  refine
    { mem := hDc.pivot_mem
      only_pivot := ?_
      positive := fun c' hc' => (hDouble c' hc').pivot_isPositivelyOriented
      injective := ?_
      off_contours := ?_
      opposite_off_crossing := ?_
      on_crossing_iff := fun x _ => hiff x
      crossing_sites := ?_
      crossed_once := ?_ }
  · intro c' hc' hm'
    rcases hDc.eq_or_eq_opposite_of_pivot_mem c' hm' with e | e
    · rw [e]
    · exact absurd (e ▸ hc') (hnotOpp c ⟨μ, hc⟩)
  · intro c' c'' hc' hc'' e
    have hm' : (pivot c' : BondAtLevel L m K k) ∈ (doubleBlockSymmetricSet c'').bonds := by
      rw [e]
      exact (hDouble c'' hc'').pivot_mem
    rcases (hDouble c'' hc'').eq_or_eq_opposite_of_pivot_mem c' hm' with e' | e'
    · exact e'
    · exact absurd (e' ▸ hc') (hnotOpp c'' hc'')
  · intro y x hx σ
    have hin' := (hContours L m K k hL hm hk y x hx (orderedContour y x σ) ⟨σ, rfl⟩).2
    have hne := hDc.ne_pivot_of_mem_unitBlock (pivot c) y
    constructor
    · intro hm'
      obtain ⟨h1, h2⟩ := hin' _ hm'
      exact hne h1 h2 c rfl
    · intro hm'
      obtain ⟨h1, h2⟩ := hin' _ hm'
      exact hne h2 h1 c rfl
  · intro x _ hm'
    obtain ⟨i, _, e⟩ := (hmem x _).1 hm'
    rw [hpiv] at e
    have e1 : x + (i : ℤ) • unitStep L m (levelDepth K k) μ =
        c.source.toSublattice (levelDepth K k) + (h : ℤ) • unitStep L m (levelDepth K k) μ +
          unitStep L m (levelDepth K k) μ := congrArg Bond.source e
    have e2 : x + (i : ℤ) • unitStep L m (levelDepth K k) μ + unitStep L m (levelDepth K k) μ =
        c.source.toSublattice (levelDepth K k) + (h : ℤ) • unitStep L m (levelDepth K k) μ :=
      congrArg Bond.target e
    have h0 : (2 : ℤ) • unitStep L m (levelDepth K k) μ = 0 := by
      rw [e1] at e2
      rw [two_zsmul]
      have := add_assoc (c.source.toSublattice (levelDepth K k) +
          (h : ℤ) • unitStep L m (levelDepth K k) μ)
        (unitStep L m (levelDepth K k) μ) (unitStep L m (levelDepth K k) μ)
      rw [this] at e2
      exact add_eq_left.1 e2
    have := hsmall 2 (by rw [abs_of_pos (by norm_num)]; omega) h0
    omega
  · have hset : {x ∈ sitesInBlock (levelDepth K k) c.source |
        (pivot c : BondAtLevel L m K k) ∈ crossingPath c x} =
        (fun n : ℤ => c.source.toSublattice (levelDepth K k) +
          n • unitStep L m (levelDepth K k) μ) '' Set.Icc (-(h : ℤ)) (h : ℤ) := by
      ext x
      constructor
      · rintro ⟨_, hx⟩
        obtain ⟨n, hn, rfl⟩ := (hiff x).1 hx
        refine ⟨n, ?_, rfl⟩
        rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at hn <;> constructor <;> omega
      · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
        have hn : 2 * |n| ≤ (L : ℤ) - 1 := by
          rcases abs_cases n with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> omega
        exact ⟨hsite n hn, (hiff _).2 ⟨n, hn, rfl⟩⟩
    have hinj : Set.InjOn
        (fun n : ℤ => c.source.toSublattice (levelDepth K k) +
          n • unitStep L m (levelDepth K k) μ)
        (Set.Icc (-(h : ℤ)) (h : ℤ)) := by
      intro n hn n' hn' e
      have e1 := add_left_cancel e
      have h0 : (n - n') • unitStep L m (levelDepth K k) μ = 0 := by
        rw [sub_zsmul, e1, add_neg_cancel]
      obtain ⟨h1, h2⟩ := hn
      obtain ⟨h3, h4⟩ := hn'
      have := hsmall _ (by rw [abs_lt]; omega) h0
      omega
    show {x ∈ sitesInBlock (levelDepth K k) c.source |
      (pivot c : BondAtLevel L m K k) ∈ crossingPath c x}.ncard = L
    rw [hset, hinj.ncard_image, ← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    omega
  · intro x _ hm'
    obtain ⟨i, hi⟩ := List.get_of_mem hm'
    refine ⟨i, hi, ?_⟩
    intro i' hi'
    exact (hnodup x).injective_get (hi'.trans hi.symm)
end YangMills.Construction.PeriodicLattice.PivotPlacement
end
