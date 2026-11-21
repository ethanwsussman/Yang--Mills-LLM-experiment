import YangMills.Construction.CellOfTheFlow.ChessboardOfABareGrid
import YangMills.Construction.HullsInEveryVolume.ChessboardOnABareGrid
import YangMills.Construction.QuaternionicWilsonModel.TheQuaternionModelIsSUTwoWithWilsonsWeightProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChessboardGrids
open TorusFields WeightedResponses
private def toCellGrid (g : MirrorGrid) : CellWindows.CellGrid := ⟨g.side, fun i => g.offset i + 1⟩
private def natToInt (c : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (c i : ℤ)
private def intToNat (κ : Fin 4 → ℤ) : Fin 4 → ℕ := fun i => (κ i).toNat
set_option linter.unusedSectionVars false
variable {N : ℕ} [NeZero N]
private theorem zmod_intCast_eq_of_dvd {a b : ℤ} (h : (N : ℤ) ∣ a - b) : (a : ZMod N) = (b : ZMod N) := by
  have := (CharP.intCast_eq_zero_iff (ZMod N) N (a - b)).2 h
  push_cast at this
  exact sub_eq_zero.1 this
private theorem numCells_mul_side {G : CellWindows.CellGrid} (h : G.Compatible N) : (N / G.side) * G.side = N :=
  Nat.div_mul_cancel (dvd_trans (Dvd.intro_left 2 rfl) h.two_mul_side_dvd)
private theorem two_dvd_numCells {G : CellWindows.CellGrid} (h : G.Compatible N) : 2 ∣ N / G.side := by
  obtain ⟨t, ht⟩ := h.two_mul_side_dvd
  refine ⟨t, ?_⟩
  rw [ht, show 2 * G.side * t = G.side * (2 * t) by ring, Nat.mul_div_cancel_left _ h.side_pos]
private theorem numCells_pos {G : CellWindows.CellGrid} (h : G.Compatible N) : 0 < N / G.side := by
  have hN : N ≠ 0 := NeZero.ne N
  have := numCells_mul_side h
  rcases Nat.eq_zero_or_pos (N / G.side) with h0 | h0
  · rw [h0] at this
    omega
  · exact h0
private theorem cellCopy_congr_right {G : CellWindows.CellGrid} (h : G.Compatible N) (κ κ₁ κ₂ : Fin 4 → ℤ)
    (hd : ∀ i, ((N / G.side : ℕ) : ℤ) ∣ κ₁ i - κ₂ i) (F : TorusField N → ℝ) :
    CellWindows.cellCopy G κ κ₁ F = CellWindows.cellCopy G κ κ₂ F := by
  have hpar : ∀ i, (Even (κ₁ i - κ i) ↔ Even (κ₂ i - κ i)) := by
    intro i
    obtain ⟨t, ht⟩ := hd i
    obtain ⟨s, hs⟩ := two_dvd_numCells h
    rw [hs] at ht
    have e : κ₁ i - κ i = (κ₂ i - κ i) + 2 * (s * t) := by
      push_cast at ht
      linarith [ht, mul_assoc (2 : ℤ) (s : ℤ) t]
    rw [e, Int.even_add]
    simp
  have hsign : ∀ i, (G.reflectionTo κ κ₁).axisSign i = (G.reflectionTo κ κ₂).axisSign i := by
    intro i
    simp only [CellWindows.CellGrid.reflectionTo, hpar i]
  have hNd : ∀ i, (N : ℤ) ∣ (G.side : ℤ) * (κ₁ i - κ₂ i) := by
    intro i
    obtain ⟨t, ht⟩ := hd i
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc]
    congr 1
    have := numCells_mul_side h
    rw [mul_comm]
    exact_mod_cast this
  have hshift : ∀ i, (((G.reflectionTo κ κ₁).offset i : ℤ) : ZMod N) =
      (((G.reflectionTo κ κ₂).offset i : ℤ) : ZMod N) := by
    intro i
    apply zmod_intCast_eq_of_dvd
    by_cases he : Even (κ₂ i - κ i)
    · simp only [CellWindows.CellGrid.reflectionTo, if_pos ((hpar i).2 he), if_pos he]
      convert hNd i using 1
      ring
    · simp only [CellWindows.CellGrid.reflectionTo, if_neg (fun h' => he ((hpar i).1 h')), if_neg he]
      convert hNd i using 1
      ring
  have hsite : ∀ x : TorusSite N, (G.reflectionTo κ κ₁).mapSite x = (G.reflectionTo κ κ₂).mapSite x := by
    intro x
    funext i
    simp only [TorusIsometry.mapSite]
    rw [hsign i, hshift i]
    rfl
  funext W
  unfold CellWindows.cellCopy
  congr 1
  funext x k
  simp only [CellWindows.pullbackBy]
  have hp : (G.reflectionTo κ κ₁).axisPerm = (G.reflectionTo κ κ₂).axisPerm := rfl
  rw [hp, hsign, hsite]
private theorem not_even_two_mul_add_one (t : ℕ) : ¬ Even ((2 * t + 1 : ℕ) : ℤ) := by
  rintro ⟨r, hr⟩
  omega
private theorem reflectSite_add_evenShift (g : MirrorGrid) (c c' : Fin 4 → ℕ) (x : TorusSite N) :
    (g.recentre c).reflectSite (MirrorGrid.cellParity c') x + (g.recentre c).evenShift c' =
      ((toCellGrid g).reflectionTo (natToInt c) (natToInt c + natToInt c')).mapSite x := by
  funext i
  rcases Nat.even_or_odd' (c' i) with ⟨t, ht | ht⟩
  · have hev : Even (natToInt c i + natToInt c' i - natToInt c i) := ⟨(t : ℤ), by simp [natToInt, ht]; ring⟩
    have hp : MirrorGrid.cellParity c' i = false := by simp [MirrorGrid.cellParity, ht]
    simp only [Pi.add_apply, MirrorGrid.reflectSite, hp, MirrorGrid.evenShift, siteOfInt, TorusIsometry.mapSite,
      CellWindows.CellGrid.reflectionTo, if_pos hev]
    simp [MirrorGrid.recentre, toCellGrid, natToInt, ht]
    ring
  · have hod : ¬ Even (natToInt c i + natToInt c' i - natToInt c i) := by
      simp only [natToInt, add_sub_cancel_left, ht]
      exact not_even_two_mul_add_one t
    have hp : MirrorGrid.cellParity c' i = true := by simp [MirrorGrid.cellParity, ht]
    simp only [Pi.add_apply, MirrorGrid.reflectSite, hp, MirrorGrid.evenShift, siteOfInt, TorusIsometry.mapSite,
      CellWindows.CellGrid.reflectionTo, if_neg hod, if_true, Equiv.Perm.coe_one, id_eq]
    have e : ((c' i - c' i % 2 : ℕ) : ℤ) = 2 * (t : ℤ) := by
      rw [ht]
      omega
    rw [e]
    simp only [MirrorGrid.recentre, toCellGrid, natToInt, ht]
    push_cast
    ring
private theorem cellCopy_recentre_eq (g : MirrorGrid) (c c' : Fin 4 → ℕ) (F : TorusField N → ℝ) :
    (g.recentre c).cellCopy F c' = CellWindows.cellCopy (toCellGrid g) (natToInt c) (natToInt c + natToInt c') F := by
  funext W
  unfold MirrorGrid.cellCopy CellWindows.cellCopy
  congr 1
  funext x k
  have hs := reflectSite_add_evenShift g c c' x
  simp only [MirrorGrid.reflectField, CellWindows.pullbackBy, YangMills.Construction.TorusFields.translate]
  have hpk : ((toCellGrid g).reflectionTo (natToInt c) (natToInt c + natToInt c')).axisPerm.symm k = k := rfl
  rw [hpk]
  rcases Nat.even_or_odd' (c' k) with ⟨t, ht | ht⟩
  · have hev : Even ((natToInt c + natToInt c') k - natToInt c k) := ⟨(t : ℤ), by simp [natToInt, ht]; ring⟩
    have hp : MirrorGrid.cellParity c' k = false := by simp [MirrorGrid.cellParity, ht]
    have hsg : ((toCellGrid g).reflectionTo (natToInt c) (natToInt c + natToInt c')).axisSign k = 1 := by
      simp only [CellWindows.CellGrid.reflectionTo, if_pos hev]
    rw [if_pos hsg, hp, ← hs]
    simp
  · have hod : ¬ Even ((natToInt c + natToInt c') k - natToInt c k) := by
      simp only [Pi.add_apply, natToInt, add_sub_cancel_left, ht]
      exact not_even_two_mul_add_one t
    have hp : MirrorGrid.cellParity c' k = true := by simp [MirrorGrid.cellParity, ht]
    have hsg : ((toCellGrid g).reflectionTo (natToInt c) (natToInt c + natToInt c')).axisSign k ≠ 1 := by
      simp only [CellWindows.CellGrid.reflectionTo, if_neg hod]
      decide
    rw [if_neg hsg, hp, ← hs]
    simp only [if_true]
    congr 2
    abel
private theorem prod_cellIndices_eq {R : Type} [CommMonoid R] (g : MirrorGrid) (f : (Fin 4 → ℕ) → R) :
    ∏ c ∈ g.cellIndices N, f c = ∏ κ ∈ (toCellGrid g).indices N, f (intToNat κ) := by
  refine Finset.prod_nbij' natToInt intToNat ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range] at hc
    simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, toCellGrid, natToInt]
    intro i
    have := hc i
    omega
  · intro κ hκ
    simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, toCellGrid] at hκ
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range, intToNat]
    intro i
    have := hκ i
    omega
  · intro c _
    funext i
    simp [intToNat, natToInt]
  · intro κ hκ
    simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico] at hκ
    funext i
    have := hκ i
    simp only [natToInt, intToNat]
    omega
  · intro c _
    congr 1
private theorem card_cellIndices_eq (g : MirrorGrid) :
    (g.cellIndices N).card = ((toCellGrid g).indices N).card := by
  simp only [MirrorGrid.cellIndices, CellWindows.CellGrid.indices, toCellGrid, Fintype.card_piFinset,
    Finset.card_range, Int.card_Ico, sub_zero, Int.toNat_natCast]
private theorem add_emod_sub_emod (a b n : ℤ) : ((a + b) % n - a) % n = b % n := by
  rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl n), ← Int.sub_emod, add_sub_cancel_left]
private theorem add_sub_emod_emod (a b n : ℤ) : (a + (b - a) % n) % n = b % n := by
  rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl n), ← Int.add_emod, add_sub_cancel]
private theorem prod_cellCopy_recentre (g : MirrorGrid) (hf : (toCellGrid g).Compatible N) (c : Fin 4 → ℕ)
    (F : TorusField N → ℝ) (W : TorusField N) :
    ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W =
      ∏ κ' ∈ (toCellGrid g).indices N, CellWindows.cellCopy (toCellGrid g) (natToInt c) κ' F W := by
  have hn : (0 : ℤ) < ((N / (toCellGrid g).side : ℕ) : ℤ) := by exact_mod_cast numCells_pos hf
  have hside : (g.recentre c).side = (toCellGrid g).side := rfl
  refine Finset.prod_nbij' (fun c' i => ((c i : ℤ) + c' i) % ((N / (toCellGrid g).side : ℕ) : ℤ))
    (fun κ' i => ((κ' i - c i) % ((N / (toCellGrid g).side : ℕ) : ℤ)).toNat) ?_ ?_ ?_ ?_ ?_
  · intro c' _
    simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico]
    intro i
    exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩
  · intro κ' _
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have h1 := Int.emod_nonneg (κ' i - c i) hn.ne'
    have h2 := Int.emod_lt_of_pos (κ' i - c i) hn
    rw [hside]
    omega
  · intro c' hc'
    simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range] at hc'
    funext i
    have h2 : ((c' i : ℕ) : ℤ) < ((N / (toCellGrid g).side : ℕ) : ℤ) := by exact_mod_cast hc' i
    have h1 := add_emod_sub_emod (c i : ℤ) (c' i : ℤ) ((N / (toCellGrid g).side : ℕ) : ℤ)
    rw [Int.emod_eq_of_lt (by positivity) h2] at h1
    simp only [h1, Int.toNat_natCast]
  · intro κ' hκ'
    simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico] at hκ'
    funext i
    have h0 := Int.emod_nonneg (κ' i - c i) hn.ne'
    have h1 := add_sub_emod_emod (c i : ℤ) (κ' i) ((N / (toCellGrid g).side : ℕ) : ℤ)
    rw [Int.emod_eq_of_lt (hκ' i).1 (hκ' i).2] at h1
    simp only [Int.toNat_of_nonneg h0, h1]
  · intro c' _
    rw [cellCopy_recentre_eq g c c' F]
    refine congrFun (cellCopy_congr_right hf _ _ _ (fun i => ?_) F) W
    refine ⟨((c i : ℤ) + c' i) / ((N / (toCellGrid g).side : ℕ) : ℤ), ?_⟩
    simp only [Pi.add_apply, natToInt]
    rw [Int.emod_def]
    ring
private theorem cellWindows_chessboardNorm_eq (g : MirrorGrid) (hf : (toCellGrid g).Compatible N) (β : ℝ)
    (c : Fin 4 → ℕ) (F : TorusField N → ℝ) :
    CellWindows.chessboardNorm (toCellGrid g) β (natToInt c) F = g.chessboardNormAt β N c F := by
  unfold CellWindows.chessboardNorm CellWindows.copyProductMean MirrorGrid.chessboardNormAt MirrorGrid.chessboardNorm
  have h1 : (∫ W, ∏ κ' ∈ (toCellGrid g).indices N,
        CellWindows.cellCopy (toCellGrid g) (natToInt c) κ' F W ∂(wilsonLaw β N)) =
      ∫ W, ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W ∂(wilsonLaw β N) :=
    integral_congr_ae (Filter.Eventually.of_forall fun W => (prod_cellCopy_recentre g hf c F W).symm)
  rw [h1, ← card_cellIndices_eq g]
  rfl
private theorem intToNat_mem_cellIndices (g : MirrorGrid) {κ : Fin 4 → ℤ} (hκ : κ ∈ (toCellGrid g).indices N) :
    intToNat κ ∈ g.cellIndices N := by
  simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, toCellGrid] at hκ
  simp only [MirrorGrid.cellIndices, Fintype.mem_piFinset, Finset.mem_range, intToNat]
  intro i
  have := hκ i
  omega
private theorem natToInt_intToNat (g : MirrorGrid) {κ : Fin 4 → ℤ} (hκ : κ ∈ (toCellGrid g).indices N) :
    natToInt (intToNat κ) = κ := by
  simp only [CellWindows.CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico] at hκ
  funext i
  have := hκ i
  simp only [natToInt, intToNat]
  omega
private theorem mem_cell_of_mem_cellSites (g : MirrorGrid) (hs : 0 < g.side) (c : Fin 4 → ℕ) {x : TorusSite N}
    (hx : x ∈ g.cellSites N c) : x ∈ (toCellGrid g).cell N (natToInt c) := by
  classical
  have h : g.cellIndex x = c := (Finset.mem_filter.mp hx).2
  unfold CellWindows.CellGrid.cell
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fun i => (((x i - ((g.offset i + 1 : ℤ) : ZMod N)).val % g.side : ℕ) : ℤ), fun i => ⟨by positivity, ?_⟩, ?_⟩
  · show (((x i - ((g.offset i + 1 : ℤ) : ZMod N)).val % g.side : ℕ) : ℤ) < (g.side : ℤ)
    exact_mod_cast Nat.mod_lt _ hs
  · funext i
    have hc : (x i - ((g.offset i + 1 : ℤ) : ZMod N)).val / g.side = c i := congrFun h i
    have hv := Nat.div_add_mod (x i - ((g.offset i + 1 : ℤ) : ZMod N)).val g.side
    rw [hc] at hv
    simp only [siteOfInt, toCellGrid, natToInt]
    generalize (x i - ((g.offset i + 1 : ℤ) : ZMod N)).val % g.side = r at hv ⊢
    have hz : ((g.side * c i + r : ℕ) : ZMod N) = x i - ((g.offset i + 1 : ℤ) : ZMod N) := by
      rw [hv, ZMod.natCast_zmod_val]
    push_cast at hz ⊢
    linear_combination -hz
private theorem isProbabilityMeasure_wilsonLaw (β : ℝ) : IsProbabilityMeasure (wilsonLaw β N) := by apply _root_.YangMills.SharedProofs.p2076 <;> assumption
private theorem chessboardNormAt_le_iSup (g : MirrorGrid) (hf : (toCellGrid g).Compatible N) (β : ℝ)
    (c : Fin 4 → ℕ) (F : TorusField N → ℝ) (hb : ∃ C : ℝ, ∀ W, |F W| ≤ C) (h0 : ∀ W, 0 ≤ F W) :
    g.chessboardNormAt β N c F ≤ ⨆ W, F W := by
  have := isProbabilityMeasure_wilsonLaw (N := N) β
  obtain ⟨C, hC⟩ := hb
  have hbd : BddAbove (Set.range F) := ⟨C, by rintro _ ⟨W, rfl⟩; exact (le_abs_self _).trans (hC W)⟩
  have hS : ∀ W, F W ≤ ⨆ W, F W := le_ciSup hbd
  have hS0 : 0 ≤ ⨆ W, F W := (h0 1).trans (hS 1)
  have hcard : ((g.recentre c).cellIndices N).card ≠ 0 := by
    have hpos := numCells_pos hf
    have hside : (g.recentre c).side = (toCellGrid g).side := rfl
    simp only [MirrorGrid.cellIndices, hside, Fintype.card_piFinset, Finset.card_range, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    positivity
  have hcopy0 : ∀ c' W, 0 ≤ (g.recentre c).cellCopy F c' W := fun c' W => h0 _
  have hcopy : ∀ c' W, (g.recentre c).cellCopy F c' W ≤ ⨆ W, F W := fun c' W => hS _
  have hprod : ∀ W, ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W ≤
      (⨆ W, F W) ^ ((g.recentre c).cellIndices N).card := fun W => by
    calc ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W
        ≤ ∏ _c' ∈ (g.recentre c).cellIndices N, ⨆ W, F W :=
          Finset.prod_le_prod (fun c' _ => hcopy0 c' W) (fun c' _ => hcopy c' W)
      _ = _ := by simp
  have hnn : ∀ W, 0 ≤ ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W := fun W =>
    Finset.prod_nonneg fun c' _ => hcopy0 c' W
  have hint : ∫ W, ∏ c' ∈ (g.recentre c).cellIndices N, (g.recentre c).cellCopy F c' W ∂(wilsonLaw β N) ≤
      (⨆ W, F W) ^ ((g.recentre c).cellIndices N).card := by
    have := integral_mono_of_nonneg (μ := wilsonLaw β N) (Filter.Eventually.of_forall hnn)
      (integrable_const ((⨆ W, F W) ^ ((g.recentre c).cellIndices N).card)) (Filter.Eventually.of_forall hprod)
    simpa using this
  unfold MirrorGrid.chessboardNormAt MirrorGrid.chessboardNorm
  calc _ ≤ ((⨆ W, F W) ^ ((g.recentre c).cellIndices N).card) ^
          (1 / (((g.recentre c).cellIndices N).card : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg hnn) hint (by positivity)
    _ = ⨆ W, F W := by rw [one_div, Real.pow_rpow_inv_natCast hS0 hcard]
private theorem chessboardNormAt_one (g : MirrorGrid) (β : ℝ) (c : Fin 4 → ℕ) :
    g.chessboardNormAt β N c (fun _ => 1) = 1 := by
  have := isProbabilityMeasure_wilsonLaw (N := N) β
  simp [MirrorGrid.chessboardNormAt, MirrorGrid.chessboardNorm, MirrorGrid.cellCopy]
theorem chessboardEstimate_of_cellWindows (hB : CellWindows.chessboardEstimateStatement) :
    chessboardEstimateStatement := by
  intro L M N _ β g hL _ _ hβ hN hg
  obtain ⟨p, _, hpM, hs⟩ := hg
  have hspos : 0 < g.side := by rw [hs]; positivity
  have hfit : (toCellGrid g).Compatible N :=
    ⟨hspos, by show 2 * g.side ∣ N; rw [hs, hN]; exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow L hpM)⟩
  have hodd : Odd (toCellGrid g).side := by show Odd g.side; rw [hs]; exact hL.pow
  refine ⟨fun F hF => ?_, fun c _ =>
    ⟨fun F hF => chessboardNormAt_le_iSup g hfit β c F hF.bounded hF.nonneg, chessboardNormAt_one g β c⟩⟩
  have key := (hB β N (toCellGrid g) hβ hfit hodd).2 ((toCellGrid g).indices N) (fun κ => F (intToNat κ)) subset_rfl
    (fun κ hκ => by
      have h := hF _ (intToNat_mem_cellIndices g hκ)
      refine ⟨h.measurable, h.bounded, h.nonneg, fun W W' hW => h.depends W W' fun b h1 h2 => hW b ?_ ?_⟩
      · rw [← natToInt_intToNat g hκ]
        exact mem_cell_of_mem_cellSites g hspos _ h1
      · rw [← natToInt_intToNat g hκ]
        exact mem_cell_of_mem_cellSites g hspos _ h2)
  calc ∫ W, ∏ c ∈ g.cellIndices N, F c W ∂(wilsonLaw β N)
      = ∫ W, ∏ κ ∈ (toCellGrid g).indices N, F (intToNat κ) W ∂(wilsonLaw β N) :=
        integral_congr_ae (Filter.Eventually.of_forall fun W => prod_cellIndices_eq g fun c => F c W)
    _ ≤ ∏ κ ∈ (toCellGrid g).indices N, CellWindows.chessboardNorm (toCellGrid g) β κ (F (intToNat κ)) := key
    _ = ∏ c ∈ g.cellIndices N, g.chessboardNormAt β N c (F c) := by
        rw [prod_cellIndices_eq g fun c => g.chessboardNormAt β N c (F c)]
        refine Finset.prod_congr rfl fun κ hκ => ?_
        rw [← cellWindows_chessboardNorm_eq g hfit β (intToNat κ) (F (intToNat κ)), natToInt_intToNat g hκ]
end YangMills.Construction.ChessboardGrids
end
