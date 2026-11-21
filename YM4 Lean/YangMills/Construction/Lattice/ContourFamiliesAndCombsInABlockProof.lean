import YangMills.Construction.Lattice.BoxesOfOrderFromACorner
import YangMills.Construction.Lattice.ContourFamiliesAndCombsInABlock
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockCombs
section AxisOrders
variable {L m : ℕ} {j : ℤ}
theorem stepsThroughAxes_filter_ne_zero (n : Fin 4 → ℤ) (l : List (Fin 4)) (x : Site L m j) :
    stepsThroughAxes n x l = stepsThroughAxes n x (l.filter fun μ => n μ ≠ 0) := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    by_cases h : n μ = 0
    · simpa [stepsThroughAxes, h, flowAlong, forwardAxisPath] using ih x
    · simpa [stepsThroughAxes, h] using ih _
theorem exists_strictAnti_enumeration (S : Finset (Fin 4)) :
    ∃ σ : Fin S.card ≃ S, StrictAnti fun s => ((σ s : S) : Fin 4) := by
  refine ⟨Fin.revPerm.trans (S.orderIsoOfFin rfl).toEquiv, fun s t h => ?_⟩
  exact show (S.orderIsoOfFin rfl) (Fin.rev t) < (S.orderIsoOfFin rfl) (Fin.rev s) from
    (S.orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h)
theorem map_strictAnti_enumeration_eq_filter (n : Fin 4 → ℤ) (S : Finset (Fin 4))
    (hS : ∀ μ, μ ∈ S ↔ n μ ≠ 0)
    (σ : Fin S.card ≃ S) (hσ : StrictAnti fun s => ((σ s : S) : Fin 4)) :
    (List.finRange S.card).map (fun s => ((σ s : S) : Fin 4)) =
      ([3, 2, 1, 0] : List (Fin 4)).filter fun μ => n μ ≠ 0 := by
  have hmem : ∀ μ : Fin 4, μ ∈ ([3, 2, 1, 0] : List (Fin 4)) := by decide
  have hdesc : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (· > ·) := by decide
  refine List.Perm.eq_of_pairwise (le := (· > ·)) (fun _ _ _ _ h h' => absurd h (lt_asymm h')) ?_
    (hdesc.filter _) ?_
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp (fun h => hσ h)
  · refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun μ => ?_
    · exact List.Nodup.map (fun _ _ h => σ.injective (Subtype.ext h)) (List.nodup_finRange _)
    · exact (by decide : ([3, 2, 1, 0] : List (Fin 4)).Nodup).filter _
    · simp only [List.mem_map, List.mem_finRange, true_and, List.mem_filter, hmem,
        decide_eq_true_eq]
      constructor
      · rintro ⟨s, rfl⟩
        exact (hS _).1 (σ s).2
      · intro h
        exact ⟨σ.symm ⟨μ, (hS μ).2 h⟩, by simp⟩
end AxisOrders
section BlockCoordinates
variable {L m K i : ℕ}
theorem two_mul_centreToFaceSteps (hL : Odd L) : 2 * centreToFaceSteps L = (L : ℤ) - 1 := by
  obtain ⟨k, rfl⟩ := hL
  unfold centreToFaceSteps
  push_cast
  omega
theorem mem_blockIndexBox_iff (hL : Odd L) (p : Fin 4 → ℤ) :
    p ∈ blockIndexBox L ↔ ∀ μ, 2 * |p μ| ≤ (L : ℤ) - 1 := by
  have h := two_mul_centreToFaceSteps hL
  change (∀ ν, -centreToFaceSteps L ≤ p ν ∧ p ν ≤ centreToFaceSteps L) ↔ _
  refine forall_congr' fun μ => ?_
  rcases abs_cases (p μ) with ⟨e, _⟩ | ⟨e, _⟩ <;> constructor <;> intro h' <;> omega
theorem coe_toSublattice {j j' : ℤ} (y : Site L m j) (h : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
theorem coe_sum_zsmul_unitStep {j : ℤ} (p : Fin 4 → ℤ) :
    ((∑ μ, p μ • unitStep L m j μ : Site L m j) : FourTorus L m) =
      ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_sum_zsmul_unitStep <;> assumption
theorem isBlockOffset_iff (hL : Odd L)
    (hle : sublattice L m (levelDepth K (i + 1)) ≤ sublattice L m (levelDepth K i))
    (z : SiteAtLevel L m K (i + 1)) (x : SiteAtLevel L m K i) (q : Fin 4 → ℤ) :
    IsBlockOffset z x q ↔
      q ∈ blockIndexBox L ∧ offsetSite (z.toSublattice (levelDepth K i)) q = x := by
  have hw := coe_toSublattice z (hle z.2)
  rw [mem_blockIndexBox_iff hL]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₂, Subtype.ext ?_⟩
    simp only [offsetSite, AddSubgroup.coe_add, hw, coe_sum_zsmul_unitStep]
    rw [← h₁]
    abel
  · rintro ⟨h₂, rfl⟩
    refine ⟨?_, h₂⟩
    simp only [offsetSite, AddSubgroup.coe_add, hw, coe_sum_zsmul_unitStep]
    abel
theorem chart_bound_iff_two_mul_abs_lt {s : ℝ} {N : ℕ} (hs : 0 < s)
    (hN : torusSide L m = (N : ℝ) * s) (d : ℤ) :
    ((|d| : ℤ) : ℝ) * s < torusSide L m / 2 ↔ 2 * |d| < (N : ℤ) := by
  rw [hN]
  constructor
  · intro h
    have h₂ : ((|d| : ℤ) : ℝ) * s < ((N : ℝ) / 2) * s := by linarith
    have h₃ := lt_of_mul_lt_mul_right h₂ hs.le
    have h₄ : ((2 * |d| : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by
      push_cast
      push_cast at h₃
      linarith
    exact_mod_cast h₄
  · intro h
    have h₄ : ((2 * |d| : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h₄
    have h₃ : ((|d| : ℤ) : ℝ) < (N : ℝ) / 2 := by
      push_cast
      linarith
    have h₂ := mul_lt_mul_of_pos_right h₃ hs
    linarith
theorem exists_siteBox_containing_block (hB : OrderBoxesFromCorners)
    (hD : YangMills.Construction.Averaging.LayerwiseParameters 4 2 L K m
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary (torusSide L m))
    (hi : i < K) (z : SiteAtLevel L m K (i + 1)) :
    ∃ P : Set (SiteAtLevel L m K i), IsSiteBox (levelDepth K i) P ∧
      ∀ t ∈ blockIndexBox L, offsetSite (z.toSublattice (levelDepth K i)) t ∈ P := by
  have hbox := ((hB L K m hD (i + 1) (by omega)).2.2.2 i (by omega) z (fun _ => 1)
    (fun _ => by simp)).2.2.2.2
  refine ⟨_, hbox, fun t ht => ⟨t, fun μ _ => ?_, rfl⟩⟩
  have h2 := two_mul_centreToFaceSteps hD.odd_factor
  have e : i + 1 - i = 1 := by omega
  have h₃ := ht μ
  change -(((L ^ (i + 1 - i) : ℕ) : ℤ) - 1) ≤ 2 * t μ ∧
    2 * t μ ≤ 2 * ((((1 : ℕ) : ℤ) - 1) * ((L ^ (i + 1 - i) : ℕ) : ℤ)) +
      (((L ^ (i + 1 - i) : ℕ) : ℤ) - 1)
  rw [e, pow_one]
  push_cast
  omega
end BlockCoordinates
theorem blockContoursAndCombs_holds (hP : BlockPaths.Statement)
    (hC : RefinedBlockCoordinatesHold)
    (hB : OrderBoxesFromCorners) : BlockContoursAndCombs := by
  intro L m K hLs hm i hi z x hx
  obtain ⟨hodd, h13⟩ := hLs
  have hD : YangMills.Construction.Averaging.LayerwiseParameters 4 2 L K m
      YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary (torusSide L m) :=
    ⟨rfl, rfl, rfl, hodd, h13, by omega, hm, rfl⟩
  have hpos : 0 < L := hodd.pos
  have hle : sublattice L m (levelDepth K (i + 1)) ≤ sublattice L m (levelDepth K i) :=
    sublattice_mono hpos m (by simp only [levelDepth]; omega)
  have hwz := coe_toSublattice z (hle z.2)
  obtain ⟨hBlock, -, hAll⟩ := (hP L m K hodd h13 hm i hi).1 z
  set w := z.toSublattice (levelDepth K i) with hw
  have hw0 : offsetSite w (0 : Fin 4 → ℤ) = w := by simp [offsetSite]
  have h0 : (0 : Fin 4 → ℤ) ∈ blockIndexBox L := by
    refine (mem_blockIndexBox_iff hodd _).2 fun μ => ?_
    have := h13
    simp only [Pi.zero_apply, abs_zero]
    omega
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ blockIndexBox L, offsetSite w p = x := by
    have h₁ : (x : FourTorus L m) ∈
        (fun p => (offsetSite w p : FourTorus L m)) '' blockIndexBox L := by
      rw [hBlock.1.2]
      exact hx
    obtain ⟨p, hp, e⟩ := h₁
    exact ⟨p, hp, Subtype.ext e⟩
  have hoff := isBlockOffset_iff hodd hle z x
  have huniq : ∀ q, IsBlockOffset z x q → q = p := fun q hq => by
    obtain ⟨h₁, h₂⟩ := (hoff q).1 hq
    exact hBlock.1.1 h₁ hp (h₂.trans hxp.symm)
  have hpo : IsBlockOffset z x p := (hoff p).2 ⟨hp, hxp⟩
  have hbo : blockOffset z x = p :=
    huniq _ (Classical.epsilon_spec (p := IsBlockOffset z x) ⟨p, hpo⟩)
  have hcont := (hAll p hp).1
  rw [hxp] at hcont
  have hz : (z : FourTorus L m) ∈ unitBlock z := by
    rw [← hBlock.1.2]
    refine ⟨0, h0, ?_⟩
    change ((offsetSite w (0 : Fin 4 → ℤ) : Site L m (levelDepth K i)) : FourTorus L m) = z
    rw [hw0]
    exact hwz
  obtain ⟨-, hlev, -⟩ := hC L K m hD
  obtain ⟨hBC, -, hN, h2L, -, -⟩ := hlev i (i + 1) (by omega) (by omega)
  have e1 : i + 1 - i = 1 := by omega
  rw [e1] at hBC
  obtain ⟨-, hfin, -, -⟩ := hBC
  obtain ⟨-, hside, -, -, hcoord, -⟩ := hfin
  have hs : 0 < meshSize L (levelDepth K i) := zpow_pos (by exact_mod_cast hpos) _
  have hlarge : 2 * (L : ℤ) ≤ (axisSiteCount L m (levelDepth K i) : ℤ) := by
    rw [hN]
    exact_mod_cast h2L
  have hpb := (mem_blockIndexBox_iff hodd p).1 hp
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hpos
  have hchart : IsChartOffset w x p := by
    refine ⟨?_, fun μ => (chart_bound_iff_two_mul_abs_lt hs hside _).2 ?_⟩
    · rw [← hxp]
      simp [offsetSite]
    · have := hpb μ
      omega
  have huc : ∀ d, IsChartOffset w x d → d = p := by
    intro d hd
    funext μ
    have hxd : (x : FourTorus L m) = coordinatePoint (levelDepth K i) (z : FourTorus L m) d := by
      have h₁ : x = w + ∑ μ, d μ • unitStep L m (levelDepth K i) μ := by
        rw [← hd.1]
        abel
      rw [h₁, AddSubgroup.coe_add, hwz, coe_sum_zsmul_unitStep]
      rfl
    have hxq : (x : FourTorus L m) = coordinatePoint (levelDepth K i) (z : FourTorus L m) p := by
      have h₁ := hpo.1
      simp only [coordinatePoint]
      rw [← h₁]
      abel
    have h₃ := (hcoord z x x.2).2.1 d p hxd hxq μ
    have h₄ : (axisSiteCount L m (levelDepth K i) : ℤ) ∣ p μ - d μ := h₃.dvd
    have h₅ := (chart_bound_iff_two_mul_abs_lt hs hside _).1 (hd.2 μ)
    have h₆ := hpb μ
    have h₇ : p μ - d μ = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd h₄ ?_
      rcases abs_cases (p μ - d μ) with ⟨e, _⟩ | ⟨e, _⟩ <;>
        rcases abs_cases (d μ) with ⟨e', _⟩ | ⟨e', _⟩ <;>
        rcases abs_cases (p μ) with ⟨e'', _⟩ | ⟨e'', _⟩ <;> omega
    omega
  have hch : chartOffset w x = p :=
    huc _ (Classical.epsilon_spec (p := IsChartOffset w x) ⟨p, hchart⟩)
  obtain ⟨P, hPbox, hPmem⟩ := exists_siteBox_containing_block hB hD hi z
  obtain ⟨σ, hσ⟩ := exists_strictAnti_enumeration (offsetAxes z x)
  have hS : ∀ μ, μ ∈ offsetAxes z x ↔ p μ ≠ 0 := by
    intro μ
    simp [offsetAxes, hbo]
  refine ⟨⟨p, hpo, huniq⟩, fun Γ hΓ => ?_, ⟨P, hPbox, ?_, ?_⟩, ⟨p, hchart⟩, σ, hσ, ?_⟩
  · obtain ⟨hpath, -, hsteps, -, hbonds⟩ := hcont Γ hΓ
    refine ⟨hpath, hz, fun b hb => hbonds b hb, fun h => ?_⟩
    have hzero : p = 0 := hBlock.1.1 hp h0 (by
      rw [hw0, hxp]
      exact Subtype.ext (h.trans hwz.symm))
    refine List.eq_nil_iff_forall_not_mem.2 fun b hb => ?_
    obtain ⟨ν, hν, -⟩ := hsteps b hb
    exact hν (by simp [hzero])
  · rw [← hw0]
    exact hPmem _ h0
  · rw [← hxp]
    exact hPmem _ hp
  · change stepsThroughAxes (chartOffset w x) w [3, 2, 1, 0] =
      stepsThroughAxes (blockOffset z x) w
        ((List.finRange _).map fun s => ((σ s : offsetAxes z x) : Fin 4))
    rw [hch, hbo, map_strictAnti_enumeration_eq_filter p _ hS σ hσ,
      ← stepsThroughAxes_filter_ne_zero]
end YangMills.Construction.PeriodicLattice.BlockCombs
