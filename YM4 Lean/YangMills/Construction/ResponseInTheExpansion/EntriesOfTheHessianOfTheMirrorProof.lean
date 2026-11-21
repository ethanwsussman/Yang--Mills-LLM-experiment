import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.FitsOfASetting
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorCoordinateReadsTheBox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsCold
import YangMills.Construction.ColdStepAtMirrorFrames.PairedVariablesOfTwoTori
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalf
import YangMills.Construction.ResponseInTheExpansion.EntriesAtAFlatTopAreOfOneColourProof
import YangMills.Construction.ResponseInTheExpansion.EntriesAtATopNearOneProof
import YangMills.Construction.ResponseInTheExpansion.EntriesOfTheHessianOfTheMirror
import YangMills.Construction.ResponseInTheExpansion.MirrorOfAColdBoxIsCold
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
open Classical
private theorem eventually_log_rpow_bounds (B K δ : ℝ) (hδ : 0 < δ) : ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    (64 : ℝ) ≤ x ^ ((1 : ℝ) / 20) ∧ 2 * B * Real.log x ^ 2 ≤ x ∧ 2 ≤ Real.log x ^ 3 - 1 ∧
    20 * x ^ ((1 : ℝ) / 90) + 4 * Real.log x ^ 3 + 2 * x ^ ((1 : ℝ) / 100) + 32 ≤ x ^ ((1 : ℝ) / 20) - 1 ∧
    K ≤ Real.exp (δ * (Real.log x ^ 3 - 1)) := by
  have t1 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 20)) Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have t2 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 20 - 1 / 90)) Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have t3 : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 20 - 1 / 100)) Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have tl : Filter.Tendsto Real.log Filter.atTop Filter.atTop := Real.tendsto_log_atTop
  have tl3 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 3) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num)).comp tl
  have o1 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0 : ℝ) < 1 / 20 by norm_num)).bound (show (0 : ℝ) < 1 / 32 by norm_num)
  have o2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 / (2 * (|B| + 1)) by positivity)
  have e1 := t1.eventually_ge_atTop 160
  have e2 := t2.eventually_ge_atTop 160
  have e3 := t3.eventually_ge_atTop 16
  have e4 := tl3.eventually_ge_atTop 3
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, K ≤ Real.exp (δ * (Real.log x ^ 3 - 1)) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.exp (δ * (Real.log x ^ 3 - 1))) Filter.atTop Filter.atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      refine Filter.Tendsto.const_mul_atTop hδ ?_
      exact Filter.tendsto_atTop_add_const_right _ (-1) tl3
    exact h1.eventually_ge_atTop K
  have e6 := Filter.eventually_ge_atTop (3 : ℝ)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (o1.and o2)))))))
  refine ⟨max x₀ 3, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have s1 : x ^ ((1 : ℝ) / 20) = x ^ ((1 : ℝ) / 90) * x ^ ((1 : ℝ) / 20 - 1 / 90) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have s2 : x ^ ((1 : ℝ) / 20) = x ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 20 - 1 / 100) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have p1 : 0 < x ^ ((1 : ℝ) / 90) := Real.rpow_pos_of_pos hx0 _
  have p2 : 0 < x ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hx0 _
  have p3 : 0 < x ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hx0 _
  have c1 : 160 * x ^ ((1 : ℝ) / 90) ≤ x ^ ((1 : ℝ) / 20) := by
    rw [s1]
    nlinarith
  have c2 : 16 * x ^ ((1 : ℝ) / 100) ≤ x ^ ((1 : ℝ) / 20) := by
    rw [s2]
    nlinarith
  have c3 : Real.log x ^ 3 ≤ 1 / 32 * x ^ ((1 : ℝ) / 20) := by
    have h9 := h7
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.norm_of_nonneg p3.le] at h9
    have : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [this] at h9
  have c4 : 2 * B * Real.log x ^ 2 ≤ x := by
    have h9 := h8
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.norm_of_nonneg (by positivity), Real.rpow_one] at h9
    have : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this] at h9
    have h10 : 2 * (|B| + 1) * Real.log x ^ 2 ≤ x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h9
      nlinarith
    have h11 : B ≤ |B| + 1 := by linarith [le_abs_self B]
    have h12 : 0 ≤ Real.log x ^ 2 := by positivity
    nlinarith
  refine ⟨by linarith, c4, by linarith, ?_, h5⟩
  nlinarith
private theorem siteOfCoords_add {F : BlockFrame} (j : ℕ) (g h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j g + siteOfCoords j h = siteOfCoords j (g + h) := by
  funext i
  simp [siteOfCoords]
private theorem fineBondAt_shift {F : BlockFrame} (Y : F.Cell) (g h o : Fin 4 → ℤ) (i : Fin 4) :
    fineBondAt (Y + siteOfCoords F.top g) h o i = fineBondAt Y (g + h) o i := by
  unfold fineBondAt
  rw [add_assoc, siteOfCoords_add]
private theorem int_eq_of_intCast_eq {N : ℕ} {a b : ℤ} (h : (a : ZMod N) = (b : ZMod N)) (hb : |a - b| < N) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have := Int.eq_zero_of_abs_lt_dvd h (by rwa [abs_sub_comm])
  omega
private theorem fineBondAt_injective {G : BlockFrame} (hodd : Odd G.blockSide) (hs : ∀ i, 2 ≤ G.extent i) (Y : G.Cell)
    (h h' o o' : Fin 4 → ℤ) (i i' : Fin 4)
    (ho : o ∈ centredCube G.blockSide) (ho' : o' ∈ centredCube G.blockSide) (hb : ∀ l, |h l - h' l| < G.extent l)
    (he : (fineBondAt Y h o i).1 = (fineBondAt Y h' o' i').1) : h = h' ∧ o = o' := by
  have c1 : Y + siteOfCoords G.top h = Y + siteOfCoords G.top h' := by
    have := congrArg enclosingCell he
    simpa only [fineBondAt, BlockOffsets.enclosingCell_offset hodd hs _ o ho,
      BlockOffsets.enclosingCell_offset hodd hs _ o' ho'] using this
  have c2 : siteOfCoords (F := G) G.top h = siteOfCoords G.top h' := add_left_cancel c1
  have hh : h = h' := by
    funext l
    have h1 : ((h l : ℤ) : ZMod (G.period G.top l)) = ((h' l : ℤ) : ZMod (G.period G.top l)) := congrFun c2 l
    exact int_eq_of_intCast_eq h1 (by rw [BlockOffsets.period_top]; exact hb l)
  subst hh
  refine ⟨rfl, ?_⟩
  have c3 : siteOfCoords (F := G) G.depth o = siteOfCoords G.depth o' := by
    have : (cellCentre G.depth (Y + siteOfCoords G.top h) + siteOfCoords G.depth o : G.Site G.depth) =
        cellCentre G.depth (Y + siteOfCoords G.top h) + siteOfCoords G.depth o' := he
    exact add_left_cancel this
  funext l
  have h1 : ((o l : ℤ) : ZMod (G.period G.depth l)) = ((o' l : ℤ) : ZMod (G.period G.depth l)) := congrFun c3 l
  refine int_eq_of_intCast_eq h1 ?_
  have b1 := CellSums.two_mul_abs_le_of_mem_centredCube hodd ho l
  have b2 := CellSums.two_mul_abs_le_of_mem_centredCube hodd ho' l
  rw [BlockOffsets.period_depth]
  have h3 : |o l - o' l| ≤ |o l| + |o' l| := abs_sub _ _
  have h4 : (1 : ℤ) ≤ G.blockSide := by exact_mod_cast hodd.pos
  have h5 : (2 : ℤ) ≤ G.extent l := by exact_mod_cast hs l
  push_cast
  nlinarith
private theorem directionCoordinate_eq_of_frames {G G' : BlockFrame} (hodd : Odd G.blockSide) (hs : ∀ i, 2 ≤ G.extent i)
    (hodd' : Odd G'.blockSide) (hs' : ∀ i, 2 ≤ G'.extent i)
    (hLL : G.blockSide = G'.blockSide) (Y : G.Cell) (Y' : G'.Cell) (hp op hq oq : Fin 4 → ℤ) (ip i : Fin 4)
    (X : imaginaryQuaternions)
    (hop : op ∈ centredCube G.blockSide) (hoq : oq ∈ centredCube G.blockSide) (hb : ∀ l, |hp l - hq l| < G.extent l)
    (hb' : ∀ l, |hp l - hq l| < G'.extent l) :
    directionCoordinate (Sum.inl ((fineBondAt Y hp op ip).1, ip, X) : ChartDirection G) (fineBondAt Y hq oq i).1 i =
      directionCoordinate (Sum.inl ((fineBondAt Y' hp op ip).1, ip, X) : ChartDirection G') (fineBondAt Y' hq oq i).1 i := by
  by_cases e : hp = hq ∧ op = oq ∧ ip = i
  · obtain ⟨rfl, rfl, rfl⟩ := e
    simp [directionCoordinate]
  · have n1 : ¬ ((fineBondAt Y hp op ip).1 = (fineBondAt Y hq oq i).1 ∧ ip = i) := fun ⟨c1, c2⟩ => by
      obtain ⟨d1, d2⟩ := fineBondAt_injective hodd hs Y _ _ _ _ _ _ hop hoq hb c1
      exact e ⟨d1, d2, c2⟩
    have n2 : ¬ ((fineBondAt Y' hp op ip).1 = (fineBondAt Y' hq oq i).1 ∧ ip = i) := fun ⟨c1, c2⟩ => by
      obtain ⟨d1, d2⟩ := fineBondAt_injective hodd' hs' Y' _ _ _ _ _ _ (hLL ▸ hop) (hLL ▸ hoq) hb' c1
      exact e ⟨d1, d2, c2⟩
    simp only [directionCoordinate]
    rw [if_neg n1, if_neg n2]
private theorem intCast_mul_eq {n L : ℕ} (a b : ℤ) (h : (a : ZMod n) = (b : ZMod n)) :
    (((L : ℤ) * a : ℤ) : ZMod (n * L)) = (((L : ℤ) * b : ℤ) : ZMod (n * L)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by push_cast; linear_combination (L : ℤ) * hk⟩
private theorem exists_reflected_offset (hcov : BlocksCoverLowerLevel) {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L)
    (t m : ℕ) (hm : 0 < m) (hn : 2 ≤ n) (o : TorusFields.TorusSite n) (b : TorusFields.TorusBond (n * L)) (Rb : ℕ)
    (hb : TorusFields.supDist (TorusLumps.parentBlock L b.1) o ≤ Rb)
    (hR : 2 * (L * Rb + L) ≤ n * L) :
    ∃ h ω : Fin 4 → ℤ, ω ∈ centredCube L ∧ WithinRadius Rb h ∧
      StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).depth b.1 =
        (fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o) h ω b.2).1 ∧
      reflectedBondPosition L t m o b = ((fineBondAt (0 : (reflectedTorusFrame L t m n).Cell) h ω b.2).1, b.2) ∧
      ∀ l, b.1 l - (TorusFields.siteOfInt (n := n * L) fun k => (L : ℤ) * ((o k).cast : ℤ)) l =
        (((L : ℤ) * h l + ω l : ℤ) : ZMod (n * L)) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set F := TorusFields.torusFrame L t n with hF
  have hn' : ∀ i, F.extent i = n := fun _ => rfl
  have hodd : Odd F.blockSide := hL
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => hn
  have hpt : ∀ i, F.period F.top i = n := TopLevelSites.period_top_of_extent hn'
  have hpb : ∀ i, F.period F.depth i = n * L := TopLevelSites.period_depth_of_extent hn'
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [hpt]; exact NeZero.ne n⟩
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by rw [hpb]; exact NeZero.ne _⟩
  set x := StepCosts.torusSiteInFrame F F.depth b.1 with hx
  obtain ⟨ω, hω, hxω⟩ := CellSums.exists_eq_cellCentre_add hcov hodd hs x
  haveI : NeZero (n * F.blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hcell : enclosingCell x = StepCosts.torusSiteInFrame F F.top (TorusLumps.parentBlock L b.1) :=
    TopLevelSites.enclosingCell_torusSiteInFrame hn' b.1
  set h : Fin 4 → ℤ := fun l => (TorusLumps.parentBlock L b.1 l - o l).valMinAbs with hh
  have hbh : TorusLumps.parentBlock L b.1 = o + TorusFields.siteOfInt h := by
    funext l
    simp [TorusFields.siteOfInt, hh]
  have hZ : enclosingCell x = StepCosts.torusSiteInFrame F F.top o + siteOfCoords F.top h := by
    rw [hcell, hbh, TorusChain.torusSiteInFrame_add hpt, TorusChain.torusSiteInFrame_siteOfInt hpt]
  have hbox : WithinRadius Rb h := by
    intro l
    have h1 : ((TorusLumps.parentBlock L b.1 l - o l).valMinAbs).natAbs ≤ TorusFields.supDist (TorusLumps.parentBlock L b.1) o :=
      Finset.le_sup (f := fun i => ((TorusLumps.parentBlock L b.1 i - o i).valMinAbs).natAbs) (Finset.mem_univ l)
    have h2 := h1.trans hb
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  suffices hfin : reflectedBondPosition L t m o b = ((fineBondAt (0 : (reflectedTorusFrame L t m n).Cell) h ω b.2).1, b.2) ∧
      ∀ l, b.1 l - (TorusFields.siteOfInt (n := n * L) fun k => (L : ℤ) * ((o k).cast : ℤ)) l =
        (((L : ℤ) * h l + ω l : ℤ) : ZMod (n * L)) by
    refine ⟨h, ω, hω, hbox, ?_, hfin.1, hfin.2⟩
    show x = cellCentre F.depth (StepCosts.torusSiteInFrame F F.top o + siteOfCoords F.top h) + siteOfCoords F.depth ω
    rw [← hZ]
    exact hxω
  · have hread : b.1 = TorusBlocks.blockCentreSite L (TorusLumps.parentBlock L b.1) + TorusFields.siteOfInt ω := by
      have e1 := congrArg (TorusLumps.toTorusSite (n * L)) hxω
      rw [hcell] at e1
      rw [hx, TopLevelSites.toTorusSite_torusSiteInFrame hpb, TopLevelSites.toTorusSite_add hpb] at e1
      have e2 := SettingFits.toTorusSite_cellCentre hn' (TorusLumps.parentBlock L b.1)
      rw [show F.blockSide = L from rfl] at e2
      rw [e2, TopLevelSites.toTorusSite_siteOfCoords hpb] at e1
      exact e1
    set c : Fin 4 → ℤ := fun l => (L : ℤ) * h l + ω l with hc
    have hval : ∀ l, (b.1 l - (TorusFields.siteOfInt (n := n * L) fun k => (L : ℤ) * ((o k).cast : ℤ)) l).valMinAbs = c l := by
      intro l
      rw [ZMod.valMinAbs_spec]
      constructor
      · have e1 := congrFun hread l
        have e2 : (((TorusLumps.parentBlock L b.1 l).cast : ℤ) : ZMod n) = ((((o l).cast : ℤ) + h l : ℤ) : ZMod n) := by
          have := congrFun hbh l
          simp only [ZMod.intCast_cast, ZMod.cast_id', id, Int.cast_add]
          simpa [TorusFields.siteOfInt] using this
        have e3 := intCast_mul_eq (L := L) _ _ e2
        simp only [TorusBlocks.blockCentreSite, TorusFields.siteOfInt, Pi.add_apply] at e1 ⊢
        rw [e1, e3]
        simp only [hc]
        push_cast
        ring
      · have b1 := CellSums.two_mul_abs_le_of_mem_centredCube hL hω l
        have b2 := hbox l
        have hLz : (1 : ℤ) ≤ L := by exact_mod_cast hL.pos
        have h3 : |(L : ℤ) * h l| ≤ L * Rb := by
          rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < L)]
          exact mul_le_mul_of_nonneg_left b2 (by omega)
        have h4 := abs_le.1 h3
        have h5 := abs_le.1 (show |ω l| ≤ |ω l| from le_rfl)
        simp only [hc, Set.mem_Ioc]
        push_cast
        constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
    set M := reflectedTorusFrame L t m n with hM
    haveI : ∀ j i, NeZero (M.period j i) := fun j i => ⟨by
      simp only [BlockFrame.period, hM, reflectedTorusFrame, reflectedFrame, TorusFields.torusFrame]
      exact mul_ne_zero (by omega) (pow_ne_zero _ (NeZero.ne L))⟩
    have e5 : (fun i => (b.1 i - (TorusFields.siteOfInt (n := n * L) fun l => (L : ℤ) * ((o l).cast : ℤ)) i).valMinAbs) = c :=
      funext hval
    refine ⟨?_, fun l => ?_⟩
    · unfold reflectedBondPosition
      rw [e5]
      unfold fineBondAt
      simp only [zero_add]
      rw [TorusContours.cellCentre_siteOfCoords, siteOfCoords_add]
      rfl
    · have h2 := ZMod.coe_valMinAbs (b.1 l - (TorusFields.siteOfInt (n := n * L) fun k => (L : ℤ) * ((o k).cast : ℤ)) l)
      rw [hval l] at h2
      exact h2.symm
private theorem deriv_deriv_eq_iteratedFDeriv (f : (Fin 2 → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0) :
    deriv (fun s : ℝ => deriv (fun s' : ℝ => f ![s, s']) 0) 0 =
      iteratedFDeriv ℝ 2 f 0 (fun l => Pi.single l 1) := by
  have hline0 : ∀ (u s : ℝ), HasDerivAt (fun s : ℝ => (![s, u] : Fin 2 → ℝ)) (Pi.single 0 1) s := by
    intro u s
    have e0 : (fun s : ℝ => (![s, u] : Fin 2 → ℝ)) = fun s => ![0, u] + s • (Pi.single 0 1 : Fin 2 → ℝ) := by
      funext s
      ext l
      fin_cases l <;> simp
    rw [e0]
    simpa using ((hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin 2 → ℝ)).const_add (![0, u] : Fin 2 → ℝ)
  have hline1 : ∀ (s u : ℝ), HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ)) (Pi.single 1 1) u := by
    intro s u
    have e0 : (fun u : ℝ => (![s, u] : Fin 2 → ℝ)) = fun u => ![s, 0] + u • (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext u
      ext l
      fin_cases l <;> simp
    rw [e0]
    simpa using ((hasDerivAt_id u).smul_const (Pi.single 1 1 : Fin 2 → ℝ)).const_add (![s, 0] : Fin 2 → ℝ)
  have h00 : (![0, 0] : Fin 2 → ℝ) = 0 := by
    ext l
    fin_cases l <;> simp
  have hev : ∀ᶠ s : ℝ in nhds 0, AnalyticAt ℝ f ![s, 0] := by
    have h1 : Filter.Tendsto (fun s : ℝ => (![s, 0] : Fin 2 → ℝ)) (nhds 0) (nhds 0) := by
      have := (hline0 0 0).continuousAt.tendsto
      rwa [h00] at this
    exact h1.eventually hf.eventually_analyticAt
  have e1 : (fun s : ℝ => deriv (fun s' : ℝ => f ![s, s']) 0) =ᶠ[nhds 0] fun s => fderiv ℝ f ![s, 0] (Pi.single 1 1) := by
    filter_upwards [hev] with s hs
    exact (hs.differentiableAt.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline1 s 0)).deriv
  rw [Filter.EventuallyEq.deriv_eq e1, iteratedFDeriv_two_apply]
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) ![0, 0] := by
    rw [h00]
    exact hf.fderiv.differentiableAt
  have h2 := h1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline0 0 0)
  have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) (Pi.single 1 1 : Fin 2 → ℝ))
  simp only [add_zero, ContinuousLinearMap.map_zero] at h3
  rw [h00] at h3
  exact h3.deriv
private theorem toImaginary_linear (a c : ℝ) (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (a • u + c • v) = a • toImaginary u + c • toImaginary v := by
  apply Subtype.ext
  show (⟨0, (a • u + c • v) 0, (a • u + c • v) 1, (a • u + c • v) 2⟩ : ℍ[ℝ]) =
    a • (⟨0, u 0, u 1, u 2⟩ : ℍ[ℝ]) + c • (⟨0, v 0, v 1, v 2⟩ : ℍ[ℝ])
  ext <;> simp
private theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
private theorem directionCoordinate_of_eq {F : BlockFrame} (z : F.Site F.depth) (k : Fin 4) (X : imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (h : z = x ∧ k = i) :
    directionCoordinate (Sum.inl (z, k, X) : ChartDirection F) x i = X := by
  simp only [directionCoordinate]
  exact if_pos h
private theorem directionCoordinate_of_ne {F : BlockFrame} (z : F.Site F.depth) (k : Fin 4) (X : imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (h : ¬ (z = x ∧ k = i)) :
    directionCoordinate (Sum.inl (z, k, X) : ChartDirection F) x i = 0 := by
  simp only [directionCoordinate]
  exact if_neg h
private def slotOfCoordinate {F : BlockFrame} (p : ChartCoordinate F) : F.Site F.depth × Fin 4 × imaginaryQuaternions :=
  (p.1.1.1, p.1.1.2, FlatHessian.colourUnit p.2)
private theorem stepCoordinates_twoCoordinateVariation {F : BlockFrame} (p q : ChartCoordinate F) (s s' : ℝ)
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (twoCoordinateVariation p q s s') x i =
      s • directionCoordinate (Sum.inl (slotOfCoordinate p) : ChartDirection F) x i +
        s' • directionCoordinate (Sum.inl (slotOfCoordinate q) : ChartDirection F) x i := by
  have hv : ∀ b : ↥(chordBonds (finiteCells F)), twoCoordinateVariation p q s s' b =
      s • (if b = p.1 then EuclideanSpace.single p.2 (1 : ℝ) else 0) +
        s' • (if b = q.1 then EuclideanSpace.single q.2 (1 : ℝ) else 0) := by
    intro b
    ext j
    have key : ∀ r : ChartCoordinate F, (if b = r.1 then EuclideanSpace.single r.2 (1 : ℝ) else 0 : EuclideanSpace ℝ (Fin 3)) j =
        if (b, j) = r then 1 else 0 := by
      intro r
      by_cases h1 : b = r.1
      · rw [if_pos h1]
        by_cases h3 : j = r.2
        · have : (b, j) = r := Prod.ext h1 h3
          rw [if_pos this, h3]
          simp
        · have : ¬ (b, j) = r := fun e => h3 (congrArg Prod.snd e)
          rw [if_neg this]
          simp [EuclideanSpace.single_apply, h3]
      · have : ¬ (b, j) = r := fun e => h1 (congrArg Prod.fst e)
        rw [if_neg h1, if_neg this]
        simp
    simp only [twoCoordinateVariation, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, key]
    split_ifs <;> simp
  unfold stepCoordinates
  by_cases hm : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos hm, hv, toImaginary_linear]
    have key : ∀ r : ChartCoordinate F,
        toImaginary (if (⟨(x, i), hm⟩ : ↥(chordBonds (finiteCells F))) = r.1 then EuclideanSpace.single r.2 (1 : ℝ) else 0) =
          directionCoordinate (Sum.inl (slotOfCoordinate r) : ChartDirection F) x i := by
      intro r
      by_cases h : (⟨(x, i), hm⟩ : ↥(chordBonds (finiteCells F))) = r.1
      · have h' : r.1.1.1 = x ∧ r.1.1.2 = i := by
          have := congrArg Subtype.val h
          simp only at this
          rw [← this]
          exact ⟨rfl, rfl⟩
        rw [if_pos h, show slotOfCoordinate r = (r.1.1.1, r.1.1.2, FlatHessian.colourUnit r.2) from rfl,
          directionCoordinate_of_eq _ _ _ _ _ h']
        rfl
      · have h' : ¬ (r.1.1.1 = x ∧ r.1.1.2 = i) := fun e => h (Subtype.ext (Prod.ext e.1.symm e.2.symm))
        rw [if_neg h, show slotOfCoordinate r = (r.1.1.1, r.1.1.2, FlatHessian.colourUnit r.2) from rfl,
          directionCoordinate_of_ne _ _ _ _ _ h', toImaginary_zero]
    rw [key, key]
  · rw [dif_neg hm]
    have h1 : ¬ (p.1.1.1 = x ∧ p.1.1.2 = i) := fun e => hm (by
      have : (x, i) = p.1.1 := Prod.ext e.1.symm e.2.symm
      rw [this]
      exact p.1.2)
    have h2 : ¬ (q.1.1.1 = x ∧ q.1.1.2 = i) := fun e => hm (by
      have : (x, i) = q.1.1 := Prod.ext e.1.symm e.2.symm
      rw [this]
      exact q.1.2)
    rw [show slotOfCoordinate p = (p.1.1.1, p.1.1.2, FlatHessian.colourUnit p.2) from rfl,
      show slotOfCoordinate q = (q.1.1.1, q.1.1.2, FlatHessian.colourUnit q.2) from rfl,
      directionCoordinate_of_ne _ _ _ _ _ h1, directionCoordinate_of_ne _ _ _ _ _ h2]
    simp
private theorem leftTranslate_zero {F : BlockFrame} (V : F.GaugeField F.top) :
    ColdStepAtMirrorFrames.leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
private theorem chartRestriction_pair {F : BlockFrame} (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions)
    (s s' : ℝ) : ColdStepAtMirrorFrames.chartRestriction a w V ![Sum.inl p, Sum.inl q] ![s, s'] =
      chartedEnergy a (fun x i => w x i + (s • directionCoordinate (Sum.inl p : ChartDirection F) x i +
        s' • directionCoordinate (Sum.inl q : ChartDirection F) x i)) V := by
  unfold ColdStepAtMirrorFrames.chartRestriction
  have e : (fun y i => ∑ l, (![s, s'] : Fin 2 → ℝ) l •
      directionMove ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection F) l) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [Fin.sum_univ_two, directionMove]
  rw [e, leftTranslate_zero]
  congr 1
  funext x i
  simp [Fin.sum_univ_two]
private theorem frameHessian_eq_chartMixedDeriv {F : BlockFrame} (a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (p q : ChartCoordinate F)
    (han : AnalyticAt ℝ (ColdStepAtMirrorFrames.chartRestriction a (fun x i => ColdStepAtMirrorFrames.stepFrame false a ρA m (x, i) V) V
      ![Sum.inl (slotOfCoordinate p), Sum.inl (slotOfCoordinate q)]) 0) :
    frameHessian a ρA m V p q =
      chartMixedDeriv a (fun x i => ColdStepAtMirrorFrames.stepFrame false a ρA m (x, i) V) V
        ![Sum.inl (slotOfCoordinate p), Sum.inl (slotOfCoordinate q)] := by
  unfold chartMixedDeriv
  rw [← deriv_deriv_eq_iteratedFDeriv _ han]
  unfold frameHessian
  congr 1
  funext s
  congr 1
  funext s'
  rw [chartRestriction_pair]
  congr 1
  funext x i
  simp only [coordsAboveFrame, stepCoordinates_twoCoordinateVariation]
private theorem unitGenerator_eq : WeightedResponses.unitGenerator = FlatHessian.colourUnit 0 := by
  apply Subtype.ext
  show (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = (⟨0, (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0,
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 1, (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 2⟩ : ℍ[ℝ])
  ext <;> simp
private theorem trivialHessian_eq_chartMixedDeriv (a : ℝ) (L u n : ℕ)
    (b b' : ↥(chordBonds (finiteCells (TorusFields.torusFrame L u n))))
    (han : AnalyticAt ℝ (ColdStepAtMirrorFrames.chartRestriction a (fun _ _ => 0)
      (uniformField (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top)
      ![Sum.inl (b.1.1, b.1.2, FlatHessian.colourUnit 0), Sum.inl (b'.1.1, b'.1.2, FlatHessian.colourUnit 0)]) 0) :
    WeightedResponses.trivialHessian a L u n b b' =
      chartMixedDeriv a (fun _ _ => 0) (uniformField (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top)
        ![Sum.inl (b.1.1, b.1.2, FlatHessian.colourUnit 0), Sum.inl (b'.1.1, b'.1.2, FlatHessian.colourUnit 0)] := by
  unfold chartMixedDeriv
  rw [← deriv_deriv_eq_iteratedFDeriv _ han]
  unfold WeightedResponses.trivialHessian
  congr 1
  funext s
  congr 1
  funext s'
  rw [chartRestriction_pair]
  congr 1
  funext x i
  simp only [WeightedResponses.pairCoordinates, zero_add, unitGenerator_eq]
  by_cases h1 : (x, i) = b.1 <;> by_cases h2 : (x, i) = b'.1
  · have e1 : b.1.1 = x ∧ b.1.2 = i := by rw [← h1]; exact ⟨rfl, rfl⟩
    have e2 : b'.1.1 = x ∧ b'.1.2 = i := by rw [← h2]; exact ⟨rfl, rfl⟩
    rw [if_pos h1, if_pos h2, directionCoordinate_of_eq _ _ _ _ _ e1, directionCoordinate_of_eq _ _ _ _ _ e2]
  · have e1 : b.1.1 = x ∧ b.1.2 = i := by rw [← h1]; exact ⟨rfl, rfl⟩
    have e2 : ¬ (b'.1.1 = x ∧ b'.1.2 = i) := fun e => h2 (Prod.ext e.1.symm e.2.symm)
    rw [if_pos h1, if_neg h2, directionCoordinate_of_eq _ _ _ _ _ e1, directionCoordinate_of_ne _ _ _ _ _ e2]
    simp
  · have e1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun e => h1 (Prod.ext e.1.symm e.2.symm)
    have e2 : b'.1.1 = x ∧ b'.1.2 = i := by rw [← h2]; exact ⟨rfl, rfl⟩
    rw [if_neg h1, if_pos h2, directionCoordinate_of_ne _ _ _ _ _ e1, directionCoordinate_of_eq _ _ _ _ _ e2]
    simp
  · have e1 : ¬ (b.1.1 = x ∧ b.1.2 = i) := fun e => h1 (Prod.ext e.1.symm e.2.symm)
    have e2 : ¬ (b'.1.1 = x ∧ b'.1.2 = i) := fun e => h2 (Prod.ext e.1.symm e.2.symm)
    rw [if_neg h1, if_neg h2, directionCoordinate_of_ne _ _ _ _ _ e1, directionCoordinate_of_ne _ _ _ _ _ e2]
    simp
abbrev _root_.YangMills.SharedProofs.p9762 := @trivialHessian_eq_chartMixedDeriv
private theorem single_dotProduct_mulVec_single {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (p q : ι) :
    (Pi.single p (1 : ℝ) : ι → ℝ) ⬝ᵥ Matrix.mulVec A (Pi.single q 1) = A p q := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
private theorem reflectedFunctional_bondIndicator {L t m n : ℕ} [NeZero L] [NeZero n] (o : TorusFields.TorusSite n)
    (b : TorusFields.TorusBond (n * L)) (e : Fin 3)
    (P : ChartCoordinate (reflectedTorusFrame L t m n)) (h1 : P.1.1 = reflectedBondPosition L t m o b) (h2 : P.2 = e) :
    reflectedFunctional L t m o (bondIndicator b) e = Pi.single P 1 := by
  funext q
  unfold reflectedFunctional
  have hsum : (∑ c : TorusFields.TorusBond (n * L), if reflectedBondPosition L t m o c = q.1.1 then bondIndicator b c else 0) =
      if reflectedBondPosition L t m o b = q.1.1 then 1 else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [bondIndicator]
    · intro c _ hc
      simp [bondIndicator, hc]
    · simp
  by_cases hq : q.2 = e
  · rw [if_pos hq, hsum]
    by_cases hp : reflectedBondPosition L t m o b = q.1.1
    · have : q = P := Prod.ext (Subtype.ext (by rw [h1, hp])) (by rw [h2, hq])
      rw [if_pos hp, this]
      simp
    · have : q ≠ P := fun e' => hp (by rw [e', h1])
      rw [if_neg hp, Pi.single_eq_of_ne this]
  · have : q ≠ P := fun e' => hq (by rw [e', h2])
    rw [if_neg hq, Pi.single_eq_of_ne this]
private theorem chartRestriction_bondIndicator {L u n : ℕ} [NeZero L] [NeZero n] (b : TorusFields.TorusBond (n * L))
    (B : ↥(chordBonds (finiteCells (TorusFields.torusFrame L u n))))
    (h1 : B.1 = (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1, b.2)) :
    ResponseInTheExpansion.chartRestriction L u n (bondIndicator b) = Pi.single B 1 := by
  funext q
  unfold ResponseInTheExpansion.chartRestriction
  rw [Finset.sum_eq_single b]
  · by_cases hp : (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1, b.2) = q.1
    · have : q = B := Subtype.ext (by rw [h1, hp])
      rw [if_pos hp, this]
      simp [bondIndicator]
    · have : q ≠ B := fun e' => hp (by rw [e', h1])
      rw [if_neg hp, Pi.single_eq_of_ne this]
  · intro c _ hc
    simp [bondIndicator, hc]
  · simp
private theorem torusSiteInFrame_mem_chordBonds (hcov : BlocksCoverLowerLevel) {L n : ℕ} [NeZero L] [NeZero n] (hL : Odd L)
    (u : ℕ) (hn : 2 ≤ n)
    (b : TorusFields.TorusBond (n * L)) (hb : b ∈ StepCosts.chartBonds L n) :
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1, b.2) ∈
      chordBonds (finiteCells (TorusFields.torusFrame L u n)) := by
  haveI : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  set F := TorusFields.torusFrame L u n with hF
  have hodd : Odd F.blockSide := hL
  have hs : ∀ i, 2 ≤ F.extent i := fun _ => hn
  have hall := hcov F hodd fun i => by have := hs i; omega
  have h1 : ¬ IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 b.1, b.2) := by
    simpa [StepCosts.chartBonds] using hb
  haveI i1 : NeZero (n * (TorusLumps.stepBlockFrame L n).blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  haveI i2 : NeZero (n * F.blockSide) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have h3 : ¬ IsAxialTreeBond (StepCosts.torusSiteInFrame F F.depth b.1, b.2) := fun h =>
    h1 ((TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame L n) (n := n) (fun _ => rfl) hL hn b.1 b.2).2
      ((TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := F) (n := n) (fun _ => rfl) hL hn b.1 b.2).1 h))
  have : (StepCosts.torusSiteInFrame F F.depth b.1 + unitStep F.depth b.2) ∈ sitesOfCells (finiteCells F) F.depth := hall _
  simp [chordBonds, innerBonds, hall, h3]
private theorem norm_bondFrameCoord_le (hMF : ReflectedFieldSmallCurvature) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hL : Odd L) (hc : c.Admissible a L)
    (hρ : c.ρA ≤ 1) {G : BlockFrame} (hG : G.blockSide = L) (m : ℕ) (hm : 16 ≤ m) (hside : ∀ i, 4 * m + 5 < G.extent i)
    (V : G.GaugeField G.top) (s : ℝ)
    (hs : 0 < s) (hsA : s ≤ c.σA) (hV : IsSmallCurvature s V) (b : G.Site G.depth × Fin 4) :
    ‖bondFrameCoord a c.ρA m b V‖ ≤ c.N 0 * s := by
  unfold bondFrameCoord
  rw [if_pos hside]
  unfold reflectedBondCoord minimizingBondCoordinate
  set G₂ := reflectedFrame G m with hG₂
  set U := reflectedField m (enclosingCell b.1) V with hU
  have hch : IsBlockTorus L G₂ := ⟨hG, 4 * m, by omega, fun _ => rfl⟩
  have hU' : IsSmallCurvature s U := hMF G m _ V s (by omega) hV
  have hcl := hc.estimates G₂ s U hch hs hsA hU'
  have hodd : Odd G₂.blockSide := hG ▸ hL
  have hs2 : ∀ i, 2 ≤ G₂.extent i := fun i => by
    show 2 ≤ 4 * m
    omega
  obtain ⟨w, hw, -, he⟩ := TopLevelSites.minimizingCoordinates_eq hodd hs2
    (show c.ρA < Real.pi by linarith [Real.pi_gt_three]) le_rfl hcl.minimizer
  rw [he]
  have hN : 0 ≤ c.N 0 * s := mul_nonneg (hc.positivity.2.2.2.2.2.1 0).le hs.le
  by_cases hb : reflectedBond m b ∈ chordBonds (finiteCells G₂)
  · exact (hw.2.1 _ hb).trans (min_le_right _ _)
  · rw [hw.1 _ hb]
    simpa using hN
abbrev _root_.YangMills.SharedProofs.p62111 := @norm_bondFrameCoord_le
private theorem curvature_gaugeTransform_eq {n : ℕ} (G : TorusFields.TorusSite n → UnitQuaternion) (W : TorusFields.TorusField n)
    (x : TorusFields.TorusSite n) (μ ν : Fin 4) :
    TorusFields.curvature (TorusFields.gaugeTransform G W) x μ ν = TorusFields.curvature W x μ ν := by apply _root_.YangMills.Construction.TorusFields.curvature_gaugeTransform <;> assumption
private theorem isAdmissibleChartPoint_of_le {F : BlockFrame} (hcov : BlocksCoverLowerLevel) {L : ℕ} {σA s₁ e : ℝ}
    (hF : IsBlockTorus L F) (hL : Odd L)
    (he0 : 0 ≤ e) (he : e ≤ 1 / (64 * (L : ℝ))) (hs₁ : 0 ≤ s₁) (hlt : s₁ + 8 * e < σA)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e) (hV : IsSmallCurvature s₁ V) :
    IsAdmissibleChartPoint L σA w V := by apply _root_.YangMills.SharedProofs.p28958 (s₁ := s₁) (e := e) <;> assumption
private theorem abs_sub_le_cellSupDist {G : BlockFrame} (hs : ∀ i, 2 ≤ G.extent i) (Y : G.Cell) (h h' : Fin 4 → ℤ)
    (hb : ∀ l, 2 * |h l - h' l| < G.extent l) (l : Fin 4) :
    |h l - h' l| ≤ (cellSupDist (Y + siteOfCoords G.top h) (Y + siteOfCoords G.top h') : ℤ) := by
  have hne : NeZero (G.period G.top l) := ⟨by
    rw [BlockOffsets.period_top]
    have := hs l
    omega⟩
  have e1 : ((Y + siteOfCoords G.top h : G.Cell) l - (Y + siteOfCoords G.top h' : G.Cell) l) =
      ((h l - h' l : ℤ) : ZMod (G.period G.top l)) := by
    simp [siteOfCoords]
  have e2 : ((Y + siteOfCoords G.top h : G.Cell) l - (Y + siteOfCoords G.top h' : G.Cell) l).valMinAbs = h l - h' l := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨e1, ?_⟩
    have h1 := abs_le.1 (le_refl |h l - h' l|)
    have h2 := hb l
    rw [BlockOffsets.period_top]
    constructor <;> linarith [h1.1, h1.2]
  have h3 : ((Y + siteOfCoords G.top h : G.Cell) l - (Y + siteOfCoords G.top h' : G.Cell) l).valMinAbs.natAbs ≤
      cellSupDist (Y + siteOfCoords G.top h) (Y + siteOfCoords G.top h') :=
    Finset.le_sup (f := fun i => (((Y + siteOfCoords G.top h : G.Cell) i - (Y + siteOfCoords G.top h' : G.Cell) i).valMinAbs).natAbs)
      (Finset.mem_univ l)
  rw [e2] at h3
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h3
private theorem bondFrameCoord_eq_of_agree (hMC : ReflectedCoordinateReadsBox) {F F' : BlockFrame}
    (hLL : F.blockSide = F'.blockSide) (htt : F.depth = F'.depth) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i) (a ρ : ℝ) (m₀ : ℕ) (hm : 0 < m₀)
    (hside : ∀ i, 4 * m₀ + 5 < F.extent i) (hside' : ∀ i, 4 * m₀ + 5 < F'.extent i)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (h ω : Fin 4 → ℤ) (i : Fin 4)
    (hω : ω ∈ centredCube F.blockSide)
    (hag : ∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m₀ u →
      V (Y + siteOfCoords F.top h + siteOfCoords F.top u.1) u.2 = V' (Y' + siteOfCoords F'.top h + siteOfCoords F'.top u.1) u.2) :
    bondFrameCoord a ρ m₀ (fineBondAt Y h ω i) V = bondFrameCoord a ρ m₀ (fineBondAt Y' h ω i) V' := by
  have hodd' : Odd F'.blockSide := hLL ▸ hodd
  have hω' : ω ∈ centredCube F'.blockSide := hLL ▸ hω
  unfold bondFrameCoord
  rw [if_pos hside, if_pos hside']
  unfold reflectedBondCoord reflectedBond
  have c1 : enclosingCell (fineBondAt Y h ω i).1 = Y + siteOfCoords F.top h := BlockOffsets.enclosingCell_offset hodd hs _ ω hω
  have c2 : enclosingCell (fineBondAt Y' h ω i).1 = Y' + siteOfCoords F'.top h := BlockOffsets.enclosingCell_offset hodd' hs' _ ω hω'
  have o1 : cellOffset (fineBondAt Y h ω i).1 = ω := BlockOffsets.cellOffset_offset hodd hs _ ω hω
  have o2 : cellOffset (fineBondAt Y' h ω i).1 = ω := BlockOffsets.cellOffset_offset hodd' hs' _ ω hω'
  rw [c1, c2, o1, o2]
  exact hMC F F' m₀ a ρ _ _ V V' ω (fineBondAt Y h ω i).2 hLL htt hm hag
private theorem norm_colourUnit (e : Fin 3) : ‖FlatHessian.colourUnit e‖ = 1 := by apply _root_.YangMills.SharedProofs.p39739 <;> assumption
private theorem fineBondAt_mem_chordBonds_iff (hPV : PairedCoordinatesAgree) {F F' : BlockFrame} (Y : F.Cell) (Y' : F'.Cell)
    (q : ℕ) (h o : Fin 4 → ℤ)
    (i : Fin 4) (hLL : F.blockSide = F'.blockSide) (hodd : Odd F.blockSide) (hs : ∀ i, 2 * q + 2 < F.extent i)
    (hs' : ∀ i, 2 * q + 2 < F'.extent i)
    (hI : WithinRadius q h) (ho : o ∈ centredCube F.blockSide) :
    fineBondAt Y h o i ∈ chordBonds (finiteCells F) ↔ fineBondAt Y' h o i ∈ chordBonds (finiteCells F') :=
  (hPV F F' Y Y' q Empty (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) h o i hLL hodd hs hs'
    (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) hI ho).1
private theorem exists_cell_offset {G : BlockFrame} (hs : ∀ i, 2 ≤ G.extent i) (y : G.Cell) (h₁ : Fin 4 → ℤ) (Rx : ℕ)
    (hd : cellSupDist y (0 + siteOfCoords G.top h₁) ≤ Rx) :
    ∃ h₃ : Fin 4 → ℤ, y = 0 + siteOfCoords G.top h₃ ∧ ∀ l, |h₃ l| ≤ |h₁ l| + Rx := by
  have hne : ∀ l, NeZero (G.period G.top l) := fun l => ⟨by
    rw [BlockOffsets.period_top]
    have := hs l
    omega⟩
  refine ⟨fun l => (y l).valMinAbs, ?_, fun l => ?_⟩
  · funext l
    haveI := hne l
    simp [siteOfCoords]
  · haveI := hne l
    set z : G.Cell := 0 + siteOfCoords G.top h₁ with hz
    have h1 := CellSums.residueNorm_add_le (y l - z l) (z l)
    rw [sub_add_cancel] at h1
    have h2 : CellSums.residueNorm (y l - z l) ≤ Rx := by
      have h3 : ((y l - z l).valMinAbs).natAbs ≤ cellSupDist y z :=
        Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ l)
      exact h3.trans hd
    have h4 : CellSums.residueNorm (z l) ≤ (h₁ l).natAbs :=
      CellSums.residueNorm_le_natAbs_of_cast (z l) (h₁ l) (by simp [hz, siteOfCoords])
    have h5 : ((y l).valMinAbs).natAbs ≤ (h₁ l).natAbs + Rx := by
      unfold CellSums.residueNorm at h1 h2 h4
      omega
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast h5
private theorem supDist_add_siteOfInt_le {n : ℕ} [NeZero n] (o : TorusFields.TorusSite n) (h : Fin 4 → ℤ) (K : ℕ)
    (hK : ∀ l, |h l| ≤ K) : TorusFields.supDist (o + TorusFields.siteOfInt h) o ≤ K := by
  unfold TorusFields.supDist
  refine Finset.sup_le fun l _ => ?_
  have h1 := CellSums.residueNorm_le_natAbs_of_cast ((o + TorusFields.siteOfInt h : TorusFields.TorusSite n) l - o l) (h l)
    (by simp [TorusFields.siteOfInt])
  unfold CellSums.residueNorm at h1
  refine h1.trans ?_
  have h2 := hK l
  rw [Int.abs_eq_natAbs] at h2
  exact_mod_cast h2
private theorem cellSupDist_le_directionDiameter {G : BlockFrame} (p q : G.Site G.depth × Fin 4 × imaginaryQuaternions) :
    cellSupDist (enclosingCell p.1) (enclosingCell q.1) ≤
      directionDiameter (![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) := by
  have h6 := Finset.le_sup (f := fun l' : Fin 2 => cellSupDist (directionCell ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) 0))
    (directionCell ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) l'))) (Finset.mem_univ (1 : Fin 2))
  have h7 := Finset.le_sup (f := fun l : Fin 2 => Finset.univ.sup fun l' : Fin 2 =>
    cellSupDist (directionCell ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) l))
      (directionCell ((![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) l'))) (Finset.mem_univ (0 : Fin 2))
  exact h6.trans h7
private theorem near_identity_arith {C₁ Ca Na s X Ee Aa Z W Θ Λ Q : ℝ} (hC : 0 < C₁) (hCa : 0 ≤ Ca) (hNa : 0 ≤ Na)
    (hs : 0 ≤ s) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hXE : X ≤ Aa * Ee) (hZ : Z ≤ Θ ^ 2) (hW : W ≤ Θ ^ 2) (hW0 : 0 ≤ W) (hΘ : 0 < Θ)
    (hK : (2 * (C₁ + C₁ * Ca) + 1) * Θ ≤ 1) (hΛ : Θ ≤ Λ)
    (hQ : 0 ≤ Q) (hA : 0 ≤ Aa * Ee) :
    C₁ * (s + (Na * s + Ca * W)) * X + C₁ * Z ≤ (C₁ * (1 + Na) + Q) * Aa * s * Ee + Λ := by
  have h1 : C₁ * (1 + Na) * s * X ≤ C₁ * (1 + Na) * s * (Aa * Ee) := mul_le_mul_of_nonneg_left hXE (by positivity)
  have h2 : C₁ * Ca * W * X ≤ C₁ * Ca * W := by
    have : 0 ≤ C₁ * Ca * W := by positivity
    nlinarith
  have h3 : C₁ * Ca * W ≤ C₁ * Ca * Θ ^ 2 := mul_le_mul_of_nonneg_left hW (by positivity)
  have h4 : C₁ * Z ≤ C₁ * Θ ^ 2 := mul_le_mul_of_nonneg_left hZ hC.le
  have h6 : (C₁ + C₁ * Ca) * Θ ^ 2 ≤ Θ := by nlinarith
  have h7 : 0 ≤ Q * (Aa * Ee) * s := by positivity
  nlinarith
private theorem abs_single_le_one (i l : Fin 4) : |(Pi.single i 1 : Fin 4 → ℤ) l| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
private theorem norm_minimalLog_le {L u mN n : ℕ} [NeZero n] (hs2 : ∀ i, 2 ≤ (reflectedTorusFrame L u mN n).extent i)
    (o : TorusFields.TorusSite n) (V : TorusFields.TorusField n) (g : TorusFields.TorusSite n → UnitQuaternion)
    (R s : ℝ) (ρn Rb1 : ℕ) (h₁ : Fin 4 → ℤ) (Vm : (reflectedTorusFrame L u mN n).GaugeField (reflectedTorusFrame L u mN n).top)
    (hvalue : ∀ (u' : Fin 4 → ℤ) (i : Fin 4), BondWithinRadius mN (u', i) →
      Vm (siteOfCoords (reflectedTorusFrame L u mN n).top u') i =
        TorusFields.gaugeTransform (restrictGauge g (supBall o R)) V (o + TorusFields.siteOfInt u') i)
    (hnearV : IsNearIdentity g V o R s) (hb1 : ∀ l, |h₁ l| ≤ (Rb1 : ℤ)) (hm : Rb1 + ρn + 4 ≤ mN)
    (hR : ((Rb1 + ρn + 3 : ℕ) : ℝ) ≤ R)
    (y' : (reflectedTorusFrame L u mN n).Cell) (i : Fin 4)
    (hy' : cellSupDist y' ((0 : (reflectedTorusFrame L u mN n).Cell) + siteOfCoords (reflectedTorusFrame L u mN n).top h₁) ≤ ρn + 2) :
    ‖LumpContours.minimalLog (Vm y' i)‖ ≤ s := by
  obtain ⟨h₃, hZ₃, hB₃⟩ := exists_cell_offset hs2 y' h₁ (ρn + 2) hy'
  have hB₄ : ∀ l, |h₃ l| ≤ (Rb1 : ℤ) + ρn + 2 := fun l => by
    have h1 := hB₃ l
    have h2 := hb1 l
    push_cast at h1
    linarith
  have hbi : BondWithinRadius mN (h₃, i) := by
    refine ⟨fun l => by have := hB₄ l; linarith, fun l => ?_⟩
    have h1 : |(h₃ + Pi.single i 1 : Fin 4 → ℤ) l| ≤ |h₃ l| + |(Pi.single i 1 : Fin 4 → ℤ) l| := abs_add_le _ _
    have h2 := abs_single_le_one i l
    have h3 := hB₄ l
    linarith
  have hv := hvalue h₃ i hbi
  have hy'' : Vm y' i = TorusFields.gaugeTransform (restrictGauge g (supBall o R)) V (o + TorusFields.siteOfInt h₃) i := by
    rw [hZ₃, zero_add]
    exact hv
  rw [hy'']
  set x' := o + TorusFields.siteOfInt h₃ with hx'
  have hKn : ∀ l, |h₃ l| ≤ ((Rb1 + ρn + 2 : ℕ) : ℤ) := fun l => by
    push_cast
    exact hB₄ l
  have ht1 : TorusFields.supDist x' o ≤ Rb1 + ρn + 2 := supDist_add_siteOfInt_le o h₃ _ hKn
  have hm1 : x' ∈ supBall o R := by
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have : (TorusFields.supDist x' o : ℝ) ≤ ((Rb1 + ρn + 3 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : TorusFields.supDist x' o ≤ Rb1 + ρn + 3)
    linarith
  have hm2 : x' + TorusFields.unitStep n i ∈ supBall o R := by
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have e1 : x' + TorusFields.unitStep n i = o + TorusFields.siteOfInt (h₃ + Pi.single i 1) := by
      rw [hx', add_assoc]
      congr 1
      funext l
      by_cases hl : l = i
      · subst hl
        simp [TorusFields.siteOfInt, TorusFields.unitStep]
      · simp [TorusFields.siteOfInt, TorusFields.unitStep, Pi.single_eq_of_ne hl]
    have hK3 : ∀ l, |(h₃ + Pi.single i 1 : Fin 4 → ℤ) l| ≤ ((Rb1 + ρn + 3 : ℕ) : ℤ) := fun l => by
      have h1 : |(h₃ + Pi.single i 1 : Fin 4 → ℤ) l| ≤ |h₃ l| + |(Pi.single i 1 : Fin 4 → ℤ) l| := abs_add_le _ _
      have h2 := abs_single_le_one i l
      have h3 := hB₄ l
      push_cast
      linarith
    have ht2 := supDist_add_siteOfInt_le o _ _ hK3
    rw [← e1] at ht2
    have : (TorusFields.supDist (x' + TorusFields.unitStep n i) o : ℝ) ≤ ((Rb1 + ρn + 3 : ℕ) : ℝ) := by exact_mod_cast ht2
    linarith
  have hval : TorusFields.gaugeTransform (restrictGauge g (supBall o R)) V x' i = gaugeTransform g V (x', i) := by
    simp only [TorusFields.gaugeTransform, restrictGauge, gaugeTransform, if_pos hm1, if_pos hm2]
  rw [hval]
  exact hnearV.log_le (x', i) hm1
set_option maxHeartbeats 2000000 in
private theorem norm_bondFrameCoord_le_of_near (hcov : BlocksCoverLowerLevel) (hMC : ReflectedCoordinateReadsBox)
    (hPV : PairedCoordinatesAgree) {a ρ : ℝ} {L u mN n m₀ ρn Rb1 : ℕ} [NeZero L] [NeZero n] (hL : Odd L) (hn2 : 2 ≤ n)
    (hm2 : 2 ≤ mN) (o : TorusFields.TorusSite n)
    (VT : (TorusFields.torusFrame L u n).GaugeField (TorusFields.torusFrame L u n).top)
    (Vm : (reflectedTorusFrame L u mN n).GaugeField (reflectedTorusFrame L u mN n).top) (R sW : ℝ) (h₁ : Fin 4 → ℤ)
    (hag : AgreeOnBall (finiteCells (TorusFields.torusFrame L u n)) VT (finiteCells (reflectedTorusFrame L u mN n)) Vm
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o) 0 mN)
    (hsideM : ∀ i, 4 * m₀ + 5 < (reflectedTorusFrame L u mN n).extent i)
    (hsideT : ∀ i, 4 * m₀ + 5 < (TorusFields.torusFrame L u n).extent i) (hm₀ : 0 < m₀)
    (hb1 : ∀ l, |h₁ l| ≤ (Rb1 : ℤ)) (hnat : Rb1 + ρn + m₀ + 4 ≤ mN) (hn3 : 2 * (Rb1 + ρn) + 2 < n)
    (hR : (Rb1 : ℝ) + 2 * ρn ≤ R)
    (hchild : ∀ bT ∈ StepCosts.chartBonds L n, supBall (TorusLumps.parentBlock L bT.1) (ρn : ℝ) ⊆ supBall o R →
      ‖bondFrameCoord a ρ m₀ (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n)
        (TorusFields.torusFrame L u n).depth bT.1, bT.2) VT‖ ≤ sW)
    (d : (reflectedTorusFrame L u mN n).Site (reflectedTorusFrame L u mN n).depth × Fin 4)
    (hd : d ∈ chordBonds (finiteCells (reflectedTorusFrame L u mN n)))
    (hdist : cellSupDist (enclosingCell d.1)
      ((0 : (reflectedTorusFrame L u mN n).Cell) + siteOfCoords (reflectedTorusFrame L u mN n).top h₁) ≤ ρn) :
    ‖bondFrameCoord a ρ m₀ d Vm‖ ≤ sW := by
  haveI hNL : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hoddT : Odd (TorusFields.torusFrame L u n).blockSide := hL
  have hoddM : Odd (reflectedTorusFrame L u mN n).blockSide := hL
  have hs2T : ∀ i, 2 ≤ (TorusFields.torusFrame L u n).extent i := fun _ => hn2
  have hs2M : ∀ i, 2 ≤ (reflectedTorusFrame L u mN n).extent i := fun i => by
    show 2 ≤ 4 * mN
    omega
  have hpt : ∀ i, (TorusFields.torusFrame L u n).period (TorusFields.torusFrame L u n).top i = n :=
    TopLevelSites.period_top_of_extent (fun _ => rfl)
  have hpb : ∀ i, (TorusFields.torusFrame L u n).period (TorusFields.torusFrame L u n).depth i = n * L :=
    TopLevelSites.period_depth_of_extent (fun _ => rfl)
  obtain ⟨h₃, hZ₃, hB₃⟩ := exists_cell_offset hs2M (enclosingCell d.1) h₁ ρn hdist
  obtain ⟨ω₃, hω₃, hd₃⟩ := CellSums.exists_eq_cellCentre_add hcov hoddM hs2M d.1
  have hd₄ : d = fineBondAt (0 : (reflectedTorusFrame L u mN n).Cell) h₃ ω₃ d.2 := by
    refine Prod.ext ?_ rfl
    show d.1 = cellCentre (reflectedTorusFrame L u mN n).depth
      ((0 : (reflectedTorusFrame L u mN n).Cell) + siteOfCoords (reflectedTorusFrame L u mN n).top h₃) +
        siteOfCoords (reflectedTorusFrame L u mN n).depth ω₃
    rw [← hZ₃]
    exact hd₃
  have hB₄ : ∀ l, |h₃ l| ≤ ((Rb1 + ρn : ℕ) : ℤ) := fun l => by
    have h1 := hB₃ l
    have h2 := hb1 l
    push_cast
    linarith
  have hmT₃ : fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o) h₃ ω₃ d.2 ∈
      chordBonds (finiteCells (TorusFields.torusFrame L u n)) :=
    (fineBondAt_mem_chordBonds_iff hPV (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o)
      (0 : (reflectedTorusFrame L u mN n).Cell) (Rb1 + ρn) h₃ ω₃ d.2 rfl hoddT
      (fun i => by
        show 2 * (Rb1 + ρn) + 2 < n
        omega)
      (fun i => by
        show 2 * (Rb1 + ρn) + 2 < 4 * mN
        omega) hB₄ hω₃).2 (hd₄ ▸ hd)
  have hfs : bondFrameCoord a ρ m₀ (fineBondAt (0 : (reflectedTorusFrame L u mN n).Cell) h₃ ω₃ d.2) Vm =
      bondFrameCoord a ρ m₀ (fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n)
        (TorusFields.torusFrame L u n).top o) h₃ ω₃ d.2) VT :=
    bondFrameCoord_eq_of_agree (F := (reflectedTorusFrame L u mN n)) (F' := (TorusFields.torusFrame L u n)) hMC rfl rfl hoddM hs2M hs2T
      a ρ m₀ hm₀ hsideM hsideT Vm VT _ _ h₃ ω₃ d.2 hω₃ (fun w' hw' => by
      have hbig : BondWithinRadius mN (h₃ + w'.1, w'.2) := by
        have hbd : ∀ l, |h₃ l| + (m₀ : ℤ) + 1 ≤ mN := fun l => by
          have h1 := hB₄ l
          have h2 : ((Rb1 + ρn : ℕ) : ℤ) + m₀ + 4 ≤ mN := by exact_mod_cast hnat
          linarith
        refine ⟨fun l => ?_, fun l => ?_⟩
        · have h1 : |(h₃ + w'.1) l| ≤ |h₃ l| + |w'.1 l| := abs_add_le _ _
          have h2 := hw'.1 l
          have h3 := hbd l
          linarith
        · have h1 : |(h₃ + w'.1 + Pi.single w'.2 1 : Fin 4 → ℤ) l| ≤ |h₃ l| + |(w'.1 + Pi.single w'.2 1 : Fin 4 → ℤ) l| := by
            rw [add_assoc]
            exact abs_add_le _ _
          have h2 := hw'.2 l
          have h3 := hbd l
          linarith
      have h1 := hag.2.2.2 (h₃ + w'.1, w'.2) hbig
      rw [add_assoc, add_assoc, siteOfCoords_add, siteOfCoords_add]
      exact h1.symm)
  rw [hd₄, hfs]
  set xT := (fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o)
    h₃ ω₃ d.2).1 with hxT
  set bT : TorusFields.TorusBond (n * L) := (TorusLumps.toTorusSite (n * L) xT, d.2) with hbT
  have hof : StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth bT.1 = xT :=
    TopLevelSites.torusSiteInFrame_toTorusSite hpb xT
  have hmem : bT ∈ StepCosts.chartBonds L n := by
    simp only [StepCosts.chartBonds, Finset.mem_filter, Finset.mem_univ, true_and]
    intro htree
    haveI i1 : NeZero (n * (TorusLumps.stepBlockFrame L n).blockSide) := hNL
    haveI i2 : NeZero (n * (TorusFields.torusFrame L u n).blockSide) := hNL
    have h1 := (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame L n) (n := n)
      (fun _ => rfl) hL hn2 bT.1 bT.2).1 htree
    have h2 : IsAxialTreeBond (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth bT.1, bT.2) :=
      (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := (TorusFields.torusFrame L u n)) (n := n)
        (fun _ => rfl) hL hn2 bT.1 bT.2).2 h1
    rw [hof] at h2
    exact (Finset.mem_filter.1 hmT₃).2 h2
  have hblk : TorusLumps.parentBlock L bT.1 = o + TorusFields.siteOfInt h₃ := by
    haveI i2 : NeZero (n * (TorusFields.torusFrame L u n).blockSide) := hNL
    have hcell : enclosingCell xT =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top (TorusLumps.parentBlock L bT.1) := by
      have h9 : enclosingCell (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth bT.1) =
          StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top (TorusLumps.parentBlock L bT.1) :=
        TopLevelSites.enclosingCell_torusSiteInFrame (F := (TorusFields.torusFrame L u n)) (n := n) (fun _ => rfl) bT.1
      rw [← h9, hof]
    have e0 : enclosingCell xT = StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o +
        siteOfCoords (TorusFields.torusFrame L u n).top h₃ := BlockOffsets.enclosingCell_offset hoddT hs2T _ ω₃ hω₃
    have e1 : StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top (o + TorusFields.siteOfInt h₃) =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top o +
          siteOfCoords (TorusFields.torusFrame L u n).top h₃ := by
      rw [TorusChain.torusSiteInFrame_add hpt, TorusChain.torusSiteInFrame_siteOfInt hpt]
    have e2 : StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top (TorusLumps.parentBlock L bT.1) =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top (o + TorusFields.siteOfInt h₃) := by
      rw [e1, ← e0]
      exact hcell.symm
    have e3 := congrArg (TorusLumps.toTorusSite n) e2
    rwa [TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt] at e3
  have htd : TorusFields.supDist (TorusLumps.parentBlock L bT.1) o ≤ Rb1 + ρn := by
    rw [hblk]
    exact supDist_add_siteOfInt_le o h₃ _ hB₄
  have hincl : supBall (TorusLumps.parentBlock L bT.1) (ρn : ℝ) ⊆ supBall o R := by
    intro z hz
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have htri : TorusFields.supDist z o ≤ TorusFields.supDist z (TorusLumps.parentBlock L bT.1) +
        TorusFields.supDist (TorusLumps.parentBlock L bT.1) o := by
      rw [← TorusChain.cellSupDist_torusSiteInFrame hpt, ← TorusChain.cellSupDist_torusSiteInFrame hpt,
        ← TorusChain.cellSupDist_torusSiteInFrame hpt]
      exact CellSums.cellSupDist_triangle (fun i => by have := hs2T i; omega) _ _ _
    have h1 : (TorusFields.supDist z o : ℝ) ≤ TorusFields.supDist z (TorusLumps.parentBlock L bT.1) + ((Rb1 + ρn : ℕ) : ℝ) := by
      have : TorusFields.supDist z o ≤ TorusFields.supDist z (TorusLumps.parentBlock L bT.1) + (Rb1 + ρn) := by omega
      exact_mod_cast this
    push_cast at h1
    linarith
  have := hchild bT hmem hincl
  rw [hof] at this
  exact this
private theorem abs_chartMixedDeriv_le {G : BlockFrame} {a δ Ck A E : ℝ} {w : G.Site G.depth → Fin 4 → imaginaryQuaternions}
    {V : G.GaugeField G.top} {p q : G.Site G.depth × Fin 4 × imaginaryQuaternions}
    (hδ : 0 < δ) (hCk : 0 ≤ Ck)
    (hker : |chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]| ≤
      Ck * Real.exp (-(δ * (directionDiameter (![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) : ℝ))))
    (hE : ∀ Dn : ℕ, cellSupDist (enclosingCell p.1) (enclosingCell q.1) ≤ Dn → Real.exp (-(δ / 2 * Dn)) ≤ A * E) :
    |chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]| ≤ Ck * (A * E) := by
  refine hker.trans (mul_le_mul_of_nonneg_left ?_ hCk)
  refine le_trans ?_ (hE _ (cellSupDist_le_directionDiameter p q))
  apply Real.exp_le_exp.2
  have : 0 ≤ δ * (directionDiameter (![Sum.inl p, Sum.inl q] : Fin 2 → ChartDirection G) : ℝ) := by positivity
  linarith
private theorem cellSupDist_self {G : BlockFrame} (z : G.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem stage_depth {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ) (h : T.base.depth = 0) :
    ∀ t, (T.stage t).depth = t
  | 0 => h
  | t + 1 => by
    show (T.stage t).depth + 1 = t + 1
    rw [stage_depth T h t]
private theorem couplingFlow_step {ℓ : TorusLumps.StepParameters} (hR : StepReturn.ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) (β : ℝ) (t : ℕ)
    (h : ∀ j ≤ t, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β j).1) :
    TorusLumps.HasExpansion ℓ t (TorusLumps.couplingFlow ℓ β t).1 (TorusLumps.couplingFlow ℓ β t).2 ∧
      |(TorusLumps.couplingFlow ℓ β (t + 1)).1 - (TorusLumps.couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p51822 <;> assumption
private theorem couplingFlow_le {ℓ : TorusLumps.StepParameters} (hR : StepReturn.ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → TorusLumps.HasExpansion ℓ 0 β (TorusLumps.wilsonWeight β)) (β : ℝ) (k e : ℕ)
    (h : ∀ j ≤ k + e, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β j).1) :
    (TorusLumps.couplingFlow ℓ β (k + e)).1 ≤ (TorusLumps.couplingFlow ℓ β k).1 + 2 * ℓ.B * e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 := ih fun j hj => h j (by omega)
    have h2 := (couplingFlow_step hR hW β (k + e) fun j hj => h j (by omega)).2
    have h3 := (abs_le.1 h2).2
    rw [← add_assoc]
    push_cast
    linarith
set_option maxHeartbeats 10000000 in
private theorem reflectedHessianEntriesAt_of (hcov : BlocksCoverLowerLevel) (hMF : ReflectedFieldSmallCurvature)
    (hMB : mirrorOfColdBallSmallCurvatureStatement) (hMA : ReflectedFieldAgreesOnBox) (hMC : ReflectedCoordinateReadsBox)
    (hPV : PairedCoordinatesAgree) (hK : ChartEnergyKernelBound) (hN : HessianEntriesNearTrivialTop)
    (hCol : FlatHessian.HessianAtFlatIsColourDiagonal)
    (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (hDr : Tb.Admissible) (c : ColdChainParameters) (hT : Tb.Compatible c)
    (hy : (2 : ℝ) ^ 1600 ≤ y)
    (hRow : StepReturn.ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (Tb.stepParameters y) 0 β (TorusLumps.wilsonWeight β))
    (hcurv : curvatureHalvesAt Tb y) : reflectedHessianEntriesAt Tb y := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, hc⟩ := hT
  have ha : 1 ≤ Tb.coupling := hDr.a_ge
  have hL : Odd Tb.side := hDr.L_odd
  have hL40 : 2 ^ 40 ≤ Tb.side := hDr.L_ge
  have hσ : 0 < Tb.threshold := hDr.σ_pos
  have hLp : (1 : ℝ) ≤ Tb.side := by exact_mod_cast hL.pos
  have hN0 : 0 < Tb.N 0 := by
    rw [← t6]
    exact hc.positivity.2.2.2.2.2.1 0
  obtain ⟨Cc, Nc, cc, xc, hcc, Hc⟩ := hcurv
  set ϱ : ℝ := Tb.threshold / 128 with hϱ
  set e₀ : ℝ := Tb.N 0 * Tb.threshold with he₀
  have he₀0 : 0 ≤ e₀ := by positivity
  have hϱ0 : 0 < ϱ := by positivity
  have hroom : e₀ + 2 * ϱ ≤ 1 / (64 * (Tb.side : ℝ)) := by
    have h1 := hDr.σ_L
    rw [le_div_iff₀ (by positivity)]
    have e : (e₀ + 2 * ϱ) * (64 * (Tb.side : ℝ)) = (Tb.N 0 * Tb.threshold + Tb.threshold / 64) * (64 * (Tb.side : ℝ)) := by
      rw [hϱ]
      ring
    rw [e]
    have h2 : 0 < Tb.threshold * Tb.side := by positivity
    nlinarith
  have hcold1 : Tb.threshold + 8 * (e₀ + 2 * ϱ) < c.σA := by
    have h1 := hDr.cold_le
    rw [t4]
    have h2 : Tb.ballRadius = Tb.threshold / 64 := rfl
    rw [h2] at h1
    rw [hϱ, he₀]
    linarith
  obtain ⟨C₁, hC₁, hnear⟩ := hN Tb.coupling Tb.side c ha hL hL40 hc Tb.threshold e₀ ϱ hσ he₀0 hϱ0 hroom hcold1
  obtain ⟨Ck, hCk, hker⟩ := hK Tb.coupling Tb.side c ha hL hL40 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  set δ' : ℝ := min (c.δ₁ / 32) (cc / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by positivity)
  set κ : ℝ := min (c.δ₁ / (2 * Tb.side)) δ' with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) hδ'0
  set K : ℝ := 2 * (C₁ + C₁ * |Cc|) + 1 with hKd
  obtain ⟨x₁, hx₁3, hx₁⟩ := eventually_log_rpow_bounds (Tb.stepParameters y).B K δ' hδ'0
  refine ⟨(C₁ * (1 + |Nc|) + 16 * Ck 2 / Tb.threshold) * Real.exp (c.δ₁ / 2), κ, max xc x₁, hκ0, ?_⟩
  intro T β k n _ nn j o V g s b b' e e' hloc hj hs hcoldV hnearV hb hb' hbox hbox'
  have hLℓ : Odd (Tb.stepParameters y).side := hL
  set x := (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 with hx
  have hxfloor : max xc x₁ ≤ x := hloc.floor_le
  obtain ⟨n1, n2, n3, n4, n5⟩ := hx₁ x ((le_max_right _ _).trans hxfloor)
  have hx3 : 3 ≤ x := hx₁3.trans ((le_max_right _ _).trans hxfloor)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set ρn : ℕ := ⌊Real.log x ^ 3⌋₊ with hρn
  set mN : ℕ := localBlockSide (Tb.stepParameters y) β k with hmN
  have hscale : localLogScale (Tb.stepParameters y) β k = (ρn : ℝ) := rfl
  rw [hscale] at hnearV hbox hbox' ⊢
  have hρ1 : Real.log x ^ 3 - 1 < ρn := by
    have := Nat.lt_floor_add_one (Real.log x ^ 3)
    linarith
  have hρ2 : (ρn : ℝ) ≤ Real.log x ^ 3 := Nat.floor_le (by positivity)
  have hρ3 : 2 ≤ ρn := by
    have : (2 : ℝ) < ρn := by linarith
    have h2 : 2 < ρn := by exact_mod_cast this
    omega
  have hm64 : 64 ≤ mN := Nat.le_floor (by exact_mod_cast n1)
  have hmlow : x ^ ((1 : ℝ) / 20) - 1 < mN := by
    have := Nat.lt_floor_add_one (x ^ ((1 : ℝ) / 20))
    have e : (mN : ℝ) = (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) := rfl
    rw [e]
    linarith
  have hst := hloc.onFamily
  have hjM : j < WeightedResponses.chainDepth x := hj
  have hu : k + j ≤ k + 2 * WeightedResponses.chainDepth x := by omega
  have htab := hst.onFamily (k + j) hu
  have hlev := stage_depth T hst.startsAtWilson.depth_eq (k + j)
  have hxu : (T.stage (k + j)).coupling = (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 :=
    hst.coupling_eq _ (hu.trans (Nat.le_succ _))
  have hρA : (T.stage (k + j)).anchorRadius = c.ρA := by
    rw [t3]
    exact htab.anchorRadius_eq
  have hrun : ∀ i ≤ k + 2 * WeightedResponses.chainDepth x, y ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β i).1 :=
    hloc.coupling_ge
  have hW' : ∀ β' : ℝ, (Tb.stepParameters y).y₁ ≤ β' →
      TorusLumps.HasExpansion (Tb.stepParameters y) 0 β' (TorusLumps.wilsonWeight β') := hW
  have hxu1 : (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ≤ x + 2 * (Tb.stepParameters y).B * j :=
    couplingFlow_le hRow hW' β k j fun i hi => hrun i (by omega)
  have hB1 : 1 ≤ (Tb.stepParameters y).B := hDr.B_ge
  have hj2 : (j : ℝ) ≤ Real.log x ^ 2 := by
    have h1 : (j : ℝ) ≤ (WeightedResponses.chainDepth x : ℝ) := by exact_mod_cast hjM.le
    exact h1.trans (Nat.floor_le (by positivity))
  have hxu2 : (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ≤ 2 * x := by
    have : 2 * (Tb.stepParameters y).B * j ≤ 2 * (Tb.stepParameters y).B * Real.log x ^ 2 := by gcongr
    linarith
  have hxu0 : y ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 := hrun _ hu
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx3
  set m₀ : ℕ := (T.stage (k + j)).toStepSetup.frameReach with hm₀
  have hm₀def : m₀ = TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 / 2 ^ 11 := by
    show TorusLumps.clusterRange (T.stage (k + j)).coupling / 2 ^ 11 = _
    rw [hxu]
  have hrange : (2 : ℝ) ^ 16 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ^ ((1 : ℝ) / 100) := by
    have h1 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity) (hy.trans hxu0) (by norm_num)
    have h2 : ((2 : ℝ) ^ 1600) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      norm_num
    rwa [h2] at h1
  have hm₀16 : 16 ≤ m₀ := by
    have h1 : 2 ^ 16 ≤ TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 := by
      have h2 : ((2 ^ 16 : ℕ) : ℝ) ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ^ ((1 : ℝ) / 100) := by
        have e : ((2 ^ 16 : ℕ) : ℝ) = (2 : ℝ) ^ 16 := by norm_num
        rw [e]
        exact hrange
      exact Nat.cast_le.1 (h2.trans (Nat.le_ceil _))
    rw [hm₀def]
    omega
  have hm₀le : (m₀ : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) + 1 := by
    have h1 : m₀ ≤ TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 := by
      rw [hm₀def]
      exact Nat.div_le_self _ _
    have h2 : (TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 : ℝ) ≤
        (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ^ ((1 : ℝ) / 100) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 ^ ((1 : ℝ) / 100) ≤ (2 * x) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (hy0.le.trans hxu0) hxu2 (by norm_num)
    have h4 : (2 * x) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ ((1 : ℝ) / 100) * x ^ ((1 : ℝ) / 100) :=
      Real.mul_rpow (by norm_num) hx0.le
    have h5 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) (show (1 : ℝ) / 100 ≤ 1 by norm_num)
      simpa using this
    have h6 : 0 ≤ x ^ ((1 : ℝ) / 100) := by positivity
    have h7 : (m₀ : ℝ) ≤ TorusLumps.clusterRange (TorusLumps.couplingFlow (Tb.stepParameters y) β (k + j)).1 := by exact_mod_cast h1
    nlinarith
  set R : ℝ := ballRadius (Tb.stepParameters y).side nn (ρn : ℝ) (j + 1) with hR
  have hLℓ1 : (1 : ℝ) ≤ (Tb.stepParameters y).side := hLp
  have hnn : 1 ≤ nn := hloc.one_le
  have hnnx : nn ≤ x ^ ((1 : ℝ) / 90) := hloc.le_rpow
  have hR1 : R ≤ 20 * x ^ ((1 : ℝ) / 90) + 4 * ρn := by
    have h1 : 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) ≤ 20 * nn := div_le_self (by positivity) (one_le_pow₀ hLℓ1)
    have : R = 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) + 4 * ρn := rfl
    linarith
  have hR0 : 4 * (ρn : ℝ) ≤ R := by
    have h1 : 0 ≤ 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) := by positivity
    have : R = 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) + 4 * ρn := rfl
    linarith
  have hρr : (0 : ℝ) ≤ ρn := by positivity
  set Rb : ℕ := ⌊R⌋₊ with hRb
  set Rb1 : ℕ := ⌊R - 5 / 2 * ρn⌋₊ with hRb1
  set Rb2 : ℕ := ⌊R - 2 * ρn⌋₊ with hRb2
  have hRbR : (Rb : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hRb1R : (Rb1 : ℝ) ≤ R - 5 / 2 * ρn := Nat.floor_le (by linarith)
  have hRb2R : (Rb2 : ℝ) ≤ R - 2 * ρn := Nat.floor_le (by linarith)
  have hnat : m₀ + Rb + 16 ≤ mN := by
    have : (m₀ : ℝ) + Rb + 16 ≤ mN := by linarith
    exact_mod_cast this
  have hRbr1 : Rb1 + ρn ≤ Rb := by
    have h1 : (Rb1 : ℝ) + ρn ≤ R := by linarith
    exact Nat.le_floor (by exact_mod_cast h1)
  have hRbr2 : Rb2 + ρn ≤ Rb := by
    have h1 : (Rb2 : ℝ) + ρn ≤ R := by linarith
    exact Nat.le_floor (by exact_mod_cast h1)
  have hn : 2 ^ 10 * mN ≤ n := by
    have h1 : (2 : ℝ) ^ 10 * localBoxRadius x ≤ n := hloc.side_ge
    have h2 : localBoxRadius x = (mN : ℝ) := rfl
    rw [h2] at h1
    exact_mod_cast h1
  have hbl : TorusFields.supDist (TorusLumps.parentBlock (Tb.stepParameters y).side b.1) o ≤ Rb1 := by
    have h1 := (Finset.mem_filter.1 hbox).2
    exact Nat.le_floor h1
  have hbl' : TorusFields.supDist (TorusLumps.parentBlock (Tb.stepParameters y).side b'.1) o ≤ Rb2 := by
    have h1 := (Finset.mem_filter.1 hbox').2
    exact Nat.le_floor h1
  have hfac : ∀ r : ℕ, r ≤ Rb → 2 * ((Tb.stepParameters y).side * r + (Tb.stepParameters y).side) ≤ n * (Tb.stepParameters y).side := by
    intro r hr
    have h1 : 2 * r + 2 ≤ n := by omega
    calc 2 * ((Tb.stepParameters y).side * r + (Tb.stepParameters y).side) = (2 * r + 2) * (Tb.stepParameters y).side := by ring
      _ ≤ n * (Tb.stepParameters y).side := Nat.mul_le_mul_right _ h1
  obtain ⟨h₁, ω₁, hω₁, hI₁, hT₁, hM₁, hZ₁⟩ :=
    exists_reflected_offset hcov hLℓ (k + j) mN (by omega) (by omega) o b Rb1 hbl (hfac _ (by omega))
  obtain ⟨h₂, ω₂, hω₂, hI₂, hT₂, hM₂, hZ₂⟩ :=
    exists_reflected_offset hcov hLℓ (k + j) mN (by omega) (by omega) o b' Rb2 hbl' (hfac _ (by omega))
  have hR3 : ((Rb1 + ρn + 3 : ℕ) : ℝ) ≤ R := by
    push_cast
    have : (3 : ℝ) ≤ 3 / 2 * ρn := by
      have : (2 : ℝ) ≤ ρn := by exact_mod_cast hρ3
      linarith
    linarith
  have hR5 : (Rb1 : ℝ) + 2 * ρn ≤ R := by
    have : (Rb1 : ℝ) + 5 / 2 * ρn ≤ R := by linarith
    linarith
  have hKρ : K ≤ Real.exp (δ' * (ρn : ℝ)) :=
    n5.trans (Real.exp_le_exp.2 (by nlinarith [(lt_min (by positivity) (by positivity) : 0 < δ')]))
  have hσA : Tb.threshold ≤ c.σA := by
    have := hDr.σ_le
    rw [t4]
    linarith
  have hρ1c : c.ρA ≤ 1 := by
    rw [t3]
    exact hDr.chain.2.2.2.2.1
  rw [hlev, hρA]
  clear n1 n2 n3 n4 n5 hrange hm₀le hxu1 hxu2 hxu0 hj2 hxu hmlow hx3 hlog0 hρ1 hρ2 hy hy0 hRbR hRb1R hRb2R hR1 hR0 hnnx hnn hρr
    hfac hbl hbl' hbox hbox' hrun hW' hB1 hLℓ1 hxfloor hx₁ hx₁3 hRow hW
  set Vg : TorusFields.TorusField n := TorusFields.gaugeTransform (restrictGauge g (supBall o R)) V with hVg
  set Vm := reflectedTopField (Tb.stepParameters y).side (k + j) mN o Vg with hVm
  have hn2 : 2 ≤ n := by omega
  have hpt : ∀ i, (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).period
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top i = n :=
    TopLevelSites.period_top_of_extent (fun _ => rfl)
  have hpb : ∀ i, (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).period
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).depth i = n * (Tb.stepParameters y).side :=
    TopLevelSites.period_depth_of_extent (fun _ => rfl)
  have hagree := hMA (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) mN
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o)
    (TorusFields.readAtLevel (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top Vg) (by omega)
    (fun i => by
      show 2 * mN + 2 < n
      omega)
  have hvalue : ∀ (u' : Fin 4 → ℤ) (i : Fin 4), BondWithinRadius mN (u', i) →
      Vm (siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top u') i =
        Vg (o + TorusFields.siteOfInt u') i := by
    intro u' i hbi
    have h1 := hagree.2.2.2 (u', i) hbi
    simp only [zero_add] at h1
    have e1 : StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o +
          siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top u' =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
          (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top (o + TorusFields.siteOfInt u') := by
      rw [TorusChain.torusSiteInFrame_add hpt, TorusChain.torusSiteInFrame_siteOfInt hpt]
    rw [e1, TopLevelSites.readAtLevel_torusSiteInFrame hpt] at h1
    exact h1.symm
  have hVmcold : IsSmallCurvature Tb.threshold Vm :=
    hMB (Tb.stepParameters y).side (k + j) mN n o V _ Tb.threshold hσ (by omega) (by omega) hL hcoldV
  have hsideM : ∀ i, 4 * m₀ + 5 < (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).extent i := fun i => by
    show 4 * m₀ + 5 < 4 * mN
    omega
  have hsideT : ∀ i, 4 * m₀ + 5 < (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).extent i := fun i => by
    show 4 * m₀ + 5 < n
    omega
  have hFM : IsBlockTorus Tb.side (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n) :=
    ⟨rfl, 4 * mN, by omega, fun _ => rfl⟩
  have hFT : IsBlockTorus Tb.side (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) :=
    ⟨rfl, n, by omega, fun _ => rfl⟩
  have hs2M : ∀ i, 2 ≤ (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).extent i := fun i => by
    show 2 ≤ 4 * mN
    omega
  have hs2T : ∀ i, 2 ≤ (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).extent i := fun _ => hn2
  have hoddM : Odd (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).blockSide := hL
  have hoddT : Odd (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).blockSide := hL
  set w₀ : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Site
      (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).depth → Fin 4 → imaginaryQuaternions :=
    fun x' i => ColdStepAtMirrorFrames.stepFrame false Tb.coupling c.ρA m₀ (x', i) Vm with hw₀
  have hsize : ∀ d ∈ chordBonds (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)),
      ‖w₀ d.1 d.2‖ ≤ e₀ := by
    intro d _
    have := norm_bondFrameCoord_le hMF hL hc hρ1c (G := (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)) rfl m₀
      hm₀16 hsideM Vm Tb.threshold hσ hσA hVmcold d
    rw [t6] at this
    exact this
  have hsmall : IsAdmissibleChartPoint Tb.side c.σA w₀ Vm :=
    isAdmissibleChartPoint_of_le hcov hFM hL he₀0 (by linarith) hσ.le (by linarith) w₀ Vm hsize hVmcold
  have hmT₁ : fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₁ ω₁ b.2 ∈
        chordBonds (finiteCells (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)) := by
    have := torusSiteInFrame_mem_chordBonds hcov hLℓ (k + j) hn2 b hb
    rw [hT₁] at this
    exact this
  have hmT₂ : fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₂ ω₂ b'.2 ∈
        chordBonds (finiteCells (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)) := by
    have := torusSiteInFrame_mem_chordBonds hcov hLℓ (k + j) hn2 b' hb'
    rw [hT₂] at this
    exact this
  have hsq : ∀ q : ℕ, q ≤ Rb → (∀ i, 2 * q + 2 < (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).extent i) ∧
      (∀ i, 2 * q + 2 < (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).extent i) := by
    intro q hq
    refine ⟨fun i => ?_, fun i => ?_⟩
    · show 2 * q + 2 < n
      omega
    · show 2 * q + 2 < 4 * mN
      omega
  have hmM₁ : fineBondAt (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₁ ω₁ b.2 ∈
      chordBonds (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)) :=
    (fineBondAt_mem_chordBonds_iff hPV (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o)
      (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) Rb1 h₁ ω₁ b.2 rfl hoddT
      (hsq Rb1 (by omega)).1 (hsq Rb1 (by omega)).2 hI₁ hω₁).1 hmT₁
  have hmM₂ : fineBondAt (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₂ ω₂ b'.2 ∈
      chordBonds (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)) :=
    (fineBondAt_mem_chordBonds_iff hPV (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o)
      (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) Rb2 h₂ ω₂ b'.2 rfl hoddT
      (hsq Rb2 (by omega)).1 (hsq Rb2 (by omega)).2 hI₂ hω₂).1 hmT₂
  set P : ChartCoordinate (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n) :=
    (⟨fineBondAt (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₁ ω₁ b.2, hmM₁⟩, e) with hP
  set Q : ChartCoordinate (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n) :=
    (⟨fineBondAt (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₂ ω₂ b'.2, hmM₂⟩, e') with hQ
  set Bb : ↥(chordBonds (finiteCells (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n))) :=
    ⟨fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₁ ω₁ b.2, hmT₁⟩ with hBb
  set Bc : ↥(chordBonds (finiteCells (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n))) :=
    ⟨fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₂ ω₂ b'.2, hmT₂⟩ with hBc
  have f1 : reflectedFunctional (Tb.stepParameters y).side (k + j) mN o (bondIndicator b) e = Pi.single P 1 :=
    reflectedFunctional_bondIndicator o b e P hM₁.symm rfl
  have f2 : reflectedFunctional (Tb.stepParameters y).side (k + j) mN o (bondIndicator b') e' = Pi.single Q 1 :=
    reflectedFunctional_bondIndicator o b' e' Q hM₂.symm rfl
  have f3 : ResponseInTheExpansion.chartRestriction (Tb.stepParameters y).side (k + j) n (bondIndicator b) = Pi.single Bb 1 :=
    chartRestriction_bondIndicator b Bb (by
      show fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₁ ω₁ b.2 = _
      rw [hT₁]
      rfl)
  have f4 : ResponseInTheExpansion.chartRestriction (Tb.stepParameters y).side (k + j) n (bondIndicator b') = Pi.single Bc 1 :=
    chartRestriction_bondIndicator b' Bc (by
      show fineBondAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₂ ω₂ b'.2 = _
      rw [hT₂]
      rfl)
  unfold trivialHessianPairing
  rw [f1, f2, single_dotProduct_mulVec_single, f3, f4, single_dotProduct_mulVec_single]
  have hhess : frameHessian Tb.coupling c.ρA m₀ Vm P Q =
      chartMixedDeriv Tb.coupling w₀ Vm ![Sum.inl (slotOfCoordinate P), Sum.inl (slotOfCoordinate Q)] :=
    frameHessian_eq_chartMixedDeriv _ _ _ _ _ _ (hker _ _ _ hFM hsmall 2 _).1
  have hflatcold : IsSmallCurvature Tb.threshold (ColdStepAtMirrorFrames.uniformField
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top) := by
    intro p₁ _
    have : plaquetteDefect (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top) p₁ = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, ColdStepAtMirrorFrames.uniformField]
    rw [this]
    exact hσ
  have hzero : IsAdmissibleChartPoint Tb.side c.σA (fun _ _ => (0 : imaginaryQuaternions))
      (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top) :=
    isAdmissibleChartPoint_of_le hcov hFT hL le_rfl (by positivity) hσ.le (by linarith) _ _ (fun _ _ => by simp) hflatcold
  have hflatK : (if e = e' then WeightedResponses.trivialHessian (Tb.stepParameters y).coupling (Tb.stepParameters y).side (k + j) n Bb Bc
      else 0) =
      chartMixedDeriv Tb.coupling (fun _ _ => 0) (ColdStepAtMirrorFrames.uniformField
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top)
        ![Sum.inl (Bb.1.1, Bb.1.2, FlatHessian.colourUnit e), Sum.inl (Bc.1.1, Bc.1.2, FlatHessian.colourUnit e')] := by
    rw [show ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top = flatTopField from rfl]
    rw [hCol Tb.coupling Tb.side c ha hL hL40 hc (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) Bb.1 Bc.1 e e' hFT Bb.2 Bc.2]
    by_cases hee : e = e'
    · rw [if_pos hee, if_pos hee]
      exact trivialHessian_eq_chartMixedDeriv _ _ _ _ _ _ (hker _ _ _ hFT hzero 2 _).1
    · rw [if_neg hee, if_neg hee]
  show |frameHessian Tb.coupling c.ρA m₀ Vm P Q - (if e = e' then WeightedResponses.trivialHessian (Tb.stepParameters y).coupling
    (Tb.stepParameters y).side (k + j) n Bb Bc else 0)| ≤ _
  rw [hhess, hflatK]
  haveI hNL : NeZero (n * (Tb.stepParameters y).side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have hb1 : ∀ l, |h₁ l| ≤ (Rb1 : ℤ) := hI₁
  have hb2 : ∀ l, |h₂ l| ≤ (Rb2 : ℤ) := hI₂
  have hdl : ∀ l, |h₁ l - h₂ l| ≤ (Rb1 : ℤ) + Rb2 := fun l => (abs_sub _ _).trans (add_le_add (hb1 l) (hb2 l))
  have hmn : 4 * Rb + 4 ≤ n ∧ 4 * Rb + 4 ≤ 4 * mN := by
    constructor <;> omega
  have hdM : ∀ l, 2 * |h₁ l - h₂ l| < (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).extent l := fun l => by
    have h1 := hdl l
    show 2 * |h₁ l - h₂ l| < ((4 * mN : ℕ) : ℤ)
    have h2 : (Rb1 : ℤ) + Rb ≥ 0 := by positivity
    push_cast
    have h3 : ((Rb1 : ℤ)) ≤ Rb := by exact_mod_cast (show Rb1 ≤ Rb by omega)
    have h4 : ((Rb2 : ℤ)) ≤ Rb := by exact_mod_cast (show Rb2 ≤ Rb by omega)
    have h5 : (4 * (Rb : ℤ) + 4) ≤ 4 * mN := by exact_mod_cast hmn.2
    linarith
  have hdT : ∀ l, 2 * |h₁ l - h₂ l| < (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).extent l := fun l => by
    have h1 := hdl l
    show 2 * |h₁ l - h₂ l| < (n : ℤ)
    have h3 : ((Rb1 : ℤ)) ≤ Rb := by exact_mod_cast (show Rb1 ≤ Rb by omega)
    have h4 : ((Rb2 : ℤ)) ≤ Rb := by exact_mod_cast (show Rb2 ≤ Rb by omega)
    have h5 : (4 * (Rb : ℤ) + 4) ≤ n := by exact_mod_cast hmn.1
    linarith
  have htd : ∀ Dn : ℕ, (∀ l, |h₁ l - h₂ l| ≤ (Dn : ℤ)) →
      TorusFields.supDist b.1 b'.1 ≤ (Tb.stepParameters y).side * Dn + (Tb.stepParameters y).side := by
    intro Dn hD
    unfold TorusFields.supDist
    refine Finset.sup_le fun l _ => ?_
    have hz : ((((Tb.stepParameters y).side : ℤ) * (h₁ l - h₂ l) + (ω₁ l - ω₂ l) : ℤ) : ZMod (n * (Tb.stepParameters y).side)) =
        b.1 l - b'.1 l := by
      have a1 := hZ₁ l
      have a2 := hZ₂ l
      have e1 : b.1 l - b'.1 l =
          (b.1 l - (TorusFields.siteOfInt (n := n * (Tb.stepParameters y).side) fun k' => ((Tb.stepParameters y).side : ℤ) * ((o k').cast : ℤ)) l) -
          (b'.1 l - (TorusFields.siteOfInt (n := n * (Tb.stepParameters y).side) fun k' => ((Tb.stepParameters y).side : ℤ) * ((o k').cast : ℤ)) l) := by
        ring
      rw [e1, a1, a2]
      push_cast
      ring
    have h1 := CellSums.residueNorm_le_natAbs_of_cast (b.1 l - b'.1 l) _ hz
    unfold CellSums.residueNorm at h1
    refine h1.trans ?_
    have c1 := CellSums.two_mul_abs_le_of_mem_centredCube hLℓ hω₁ l
    have c2 := CellSums.two_mul_abs_le_of_mem_centredCube hLℓ hω₂ l
    have hLz : (0 : ℤ) < (Tb.stepParameters y).side := by exact_mod_cast hL.pos
    have h2 : |((Tb.stepParameters y).side : ℤ) * (h₁ l - h₂ l) + (ω₁ l - ω₂ l)| ≤
        ((Tb.stepParameters y).side : ℤ) * Dn + (Tb.stepParameters y).side := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hLz]
      have h3 : ((Tb.stepParameters y).side : ℤ) * |h₁ l - h₂ l| ≤ (Tb.stepParameters y).side * Dn :=
        mul_le_mul_of_nonneg_left (hD l) hLz.le
      have h4 : |ω₁ l - ω₂ l| ≤ |ω₁ l| + |ω₂ l| := abs_sub _ _
      have h5 := abs_nonneg (ω₁ l)
      have h6 := abs_nonneg (ω₂ l)
      linarith
    rw [Int.abs_eq_natAbs] at h2
    exact_mod_cast h2
  have hexp : ∀ Dn : ℕ, TorusFields.supDist b.1 b'.1 ≤ (Tb.stepParameters y).side * Dn + (Tb.stepParameters y).side →
      Real.exp (-(c.δ₁ / 2 * Dn)) ≤ Real.exp (c.δ₁ / 2) * Real.exp (-(κ * (TorusFields.supDist b.1 b'.1 : ℝ))) := by
    intro Dn hd
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : (TorusFields.supDist b.1 b'.1 : ℝ) ≤ (Tb.side : ℝ) * Dn + Tb.side := by exact_mod_cast hd
    have h2 : κ ≤ c.δ₁ / (2 * Tb.side) := min_le_left _ _
    have h3 : κ * (TorusFields.supDist b.1 b'.1 : ℝ) ≤ (c.δ₁ / (2 * Tb.side)) * ((Tb.side : ℝ) * Dn + Tb.side) :=
      mul_le_mul h2 h1 (by positivity) (by positivity)
    have h4 : (c.δ₁ / (2 * Tb.side)) * ((Tb.side : ℝ) * Dn + Tb.side) = c.δ₁ / 2 * Dn + c.δ₁ / 2 := by
      field_simp
    linarith
  set Ee := Real.exp (-(κ * (TorusFields.supDist b.1 b'.1 : ℝ))) with hEe
  have hEe0 : 0 < Ee := Real.exp_pos _
  set Aa := Real.exp (c.δ₁ / 2) with hAa
  have hAa0 : 0 < Aa := Real.exp_pos _
  have hCk2 := hCk 2
  by_cases hsσ : 4 * s < Tb.threshold
  · have hcoldVg : IsColdOnBall (Tb.stepParameters y).threshold Vg o mN := fun p₁ hp₁ => by
      rw [hVg, curvature_gaugeTransform_eq]
      exact hcoldV p₁ hp₁
    have hcu : maxCurvatureOnBall Vg o R ≤ s ∧ 0 ≤ maxCurvatureOnBall Vg o R := by
      unfold maxCurvatureOnBall finsetSupNonneg
      refine ⟨(Finset.fold_max_le _).2 ⟨hs, fun p₁ hp₁ => ?_⟩, (Finset.le_fold_max _).2 (Or.inl le_rfl)⟩
      rw [hVg, curvature_gaugeTransform_eq]
      exact hnearV.curvature_le p₁ hp₁
    set Wc := Real.exp (-(cc * (ρn : ℝ))) with hWc
    have hWc0 : 0 < Wc := Real.exp_pos _
    set sW := |Nc| * s + |Cc| * Wc with hsW
    have hsW0 : 0 ≤ sW := by positivity
    have hb1r : ∀ l, |h₁ l| + (ρn : ℤ) + 2 ≤ (mN : ℤ) - 2 := by
      intro l
      have h1 := hb1 l
      have h2 : (Rb1 : ℤ) + ρn ≤ Rb := by exact_mod_cast hRbr1
      have h3 : (m₀ : ℤ) + Rb + 16 ≤ mN := by exact_mod_cast hnat
      have h4 : (0 : ℤ) ≤ m₀ := by positivity
      linarith
    have hlogs : ∀ (y' : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) (i : Fin 4),
        cellSupDist y' ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
          siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁) ≤ ρn + 2 →
        Vm y' i = expUnit (LumpContours.minimalLog (Vm y' i)) ∧ ‖LumpContours.minimalLog (Vm y' i)‖ ≤ s := fun y' i hy' =>
      ⟨(GaugeFixing.expUnit_minimalLog _).symm,
        norm_minimalLog_le hs2M o V g R s ρn Rb1 h₁ Vm hvalue hnearV hb1 (by omega) hR3 y' i hy'⟩
    have hwnear : ∀ d ∈ chordBonds (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)),
        cellSupDist (enclosingCell d.1) ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
          siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁) ≤ ρn → ‖w₀ d.1 d.2‖ ≤ sW := by
      intro d hd hdist
      have hloc' : IsLocalChainAbove Tb y T β k n nn xc := { hloc with floor_le := (le_max_left _ _).trans hloc.floor_le }
      have hchild : ∀ bT ∈ StepCosts.chartBonds (Tb.stepParameters y).side n,
          supBall (TorusLumps.parentBlock (Tb.stepParameters y).side bT.1) (ρn : ℝ) ⊆ supBall o R →
          ‖bondFrameCoord Tb.coupling c.ρA m₀ (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
            (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).depth bT.1, bT.2)
            (TorusFields.readAtLevel (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
              (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top Vg)‖ ≤ sW := by
        intro bT hbT hincl
        have h1 := (Hc T β k n nn j o Vg hloc' (by omega) hcoldVg).1 bT hbT hincl
        rw [hρA] at h1
        have h2 : Nc * maxCurvatureOnBall Vg o R ≤ |Nc| * s :=
          (mul_le_mul_of_nonneg_right (le_abs_self Nc) hcu.2).trans (mul_le_mul_of_nonneg_left hcu.1 (abs_nonneg _))
        have h3 : Cc * Wc ≤ |Cc| * Wc := mul_le_mul_of_nonneg_right (le_abs_self Cc) hWc0.le
        exact h1.trans (by
          show Nc * maxCurvatureOnBall Vg o R + Cc * Wc ≤ sW
          rw [hsW]
          linarith)
      have := norm_bondFrameCoord_le_of_near hcov hMC hPV (a := Tb.coupling) (ρ := c.ρA) (L := (Tb.stepParameters y).side)
        (u := k + j) (mN := mN) (n := n) (m₀ := m₀) (ρn := ρn) (Rb1 := Rb1)
        hLℓ hn2 (by omega) o (TorusFields.readAtLevel (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
          (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top Vg) Vm R sW h₁ hagree hsideM hsideT (by omega) hb1
        (by omega) (by omega) hR5 hchild d hd hdist
      exact this
    have hcell : enclosingCell (slotOfCoordinate P).1 = (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
        siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁ :=
      BlockOffsets.enclosingCell_offset hoddM hs2M _ ω₁ hω₁
    have hcellQ : enclosingCell (slotOfCoordinate Q).1 = (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
        siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₂ :=
      BlockOffsets.enclosingCell_offset hoddM hs2M _ ω₂ hω₂
    have hcell' : enclosingCell Bb.1.1 = (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
          siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁ :=
      BlockOffsets.enclosingCell_offset hoddT hs2T _ ω₁ hω₁
    have hmatch : ∀ (g' o₃ : Fin 4 → ℤ) (i : Fin 4), WithinRadius ρn g' → o₃ ∈ centredCube Tb.side →
        fineBondAt ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
          siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁) g' o₃ i ∈
            chordBonds (finiteCells (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)) →
        directionCoordinate (Sum.inl (slotOfCoordinate P)) (fineBondAt ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
          siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁) g' o₃ i).1 i =
          directionCoordinate (Sum.inl (Bb.1.1, Bb.1.2, FlatHessian.colourUnit e))
            (fineBondAt ((StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
              (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
                siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁) g' o₃ i).1 i ∧
        directionCoordinate (Sum.inl (slotOfCoordinate Q)) (fineBondAt ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
          siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁) g' o₃ i).1 i =
          directionCoordinate (Sum.inl (Bc.1.1, Bc.1.2, FlatHessian.colourUnit e'))
            (fineBondAt ((StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
              (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
                siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁) g' o₃ i).1 i := by
      intro g' o₃ i hg' ho₃ _
      rw [fineBondAt_shift, fineBondAt_shift]
      have hbd : ∀ (hx : Fin 4 → ℤ), (∀ l, |hx l| ≤ (Rb : ℤ)) →
          (∀ l, |hx l - (h₁ + g') l| < (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).extent l) ∧
          (∀ l, |hx l - (h₁ + g') l| < (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).extent l) := by
        intro hx hxb
        have key : ∀ l, |hx l - (h₁ + g') l| ≤ 2 * (Rb : ℤ) := fun l => by
          have h1 : |hx l - (h₁ + g') l| ≤ |hx l| + |(h₁ + g') l| := abs_sub _ _
          have h2 : |(h₁ + g') l| ≤ |h₁ l| + |g' l| := abs_add_le _ _
          have h3 := hxb l
          have h4 := hb1 l
          have h5 := hg' l
          have h6 : (Rb1 : ℤ) + ρn ≤ Rb := by exact_mod_cast hRbr1
          linarith
        refine ⟨fun l => ?_, fun l => ?_⟩
        · show _ < ((4 * mN : ℕ) : ℤ)
          have h5 : (4 * (Rb : ℤ) + 4) ≤ 4 * mN := by exact_mod_cast hmn.2
          have h6 := key l
          have h7 : (0 : ℤ) ≤ Rb := by positivity
          push_cast
          linarith
        · show _ < (n : ℤ)
          have h5 : (4 * (Rb : ℤ) + 4) ≤ n := by exact_mod_cast hmn.1
          have h6 := key l
          have h7 : (0 : ℤ) ≤ Rb := by positivity
          linarith
      have hB1 : ∀ l, |h₁ l| ≤ (Rb : ℤ) := fun l => (hb1 l).trans (by exact_mod_cast (show Rb1 ≤ Rb by omega))
      have hB2 : ∀ l, |h₂ l| ≤ (Rb : ℤ) := fun l => (hb2 l).trans (by exact_mod_cast (show Rb2 ≤ Rb by omega))
      exact ⟨directionCoordinate_eq_of_frames hoddM hs2M hoddT hs2T rfl
          (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
            (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o)
          h₁ ω₁ (h₁ + g') o₃ b.2 i (FlatHessian.colourUnit e) hω₁ ho₃ (hbd h₁ hB1).1 (hbd h₁ hB1).2,
        directionCoordinate_eq_of_frames hoddM hs2M hoddT hs2T rfl
          (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
            (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o)
          h₂ ω₂ (h₁ + g') o₃ b'.2 i (FlatHessian.colourUnit e') hω₂ ho₃ (hbd h₂ hB2).1 (hbd h₂ hB2).2⟩
    have hcore := hnear (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n)
      (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) w₀ Vm (fun y' i => LumpContours.minimalLog (Vm y' i))
      ((0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
        siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁)
      ((StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
          siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁) ρn s sW
      (slotOfCoordinate P) (slotOfCoordinate Q) (Bb.1.1, Bb.1.2, FlatHessian.colourUnit e) (Bc.1.1, Bc.1.2, FlatHessian.colourUnit e')
      (by omega) hFM hFT rfl
      (fun i => by
        show 2 * (ρn + 2) + 2 < 4 * mN
        omega)
      (fun i => by
        show 2 * (ρn + 2) + 2 < n
        omega)
      (norm_colourUnit _) (norm_colourUnit _) (norm_colourUnit _) (norm_colourUnit _) hs hsσ hsW0 hVmcold hsize hlogs hwnear hmatch
      (by rw [hcell, cellSupDist_self]; omega)
      (by
        have h9 : cellSupDist (enclosingCell (Bb.1.1, Bb.1.2, FlatHessian.colourUnit e).1)
            ((StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
              (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
                siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁) = 0 := by
          show cellSupDist (enclosingCell Bb.1.1) _ = 0
          rw [hcell', cellSupDist_self]
        rw [h9]
        omega)
    refine hcore.trans ?_
    set Dd := cellSupDist (enclosingCell (slotOfCoordinate P).1) (enclosingCell (slotOfCoordinate Q).1) with hDd
    have hD : ∀ l, |h₁ l - h₂ l| ≤ (Dd : ℤ) := fun l => by
      have h1 := abs_sub_le_cellSupDist hs2M (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₁ h₂ hdM l
      rw [hDd, hcell, hcellQ]
      exact h1
    have hX := hexp Dd (htd Dd hD)
    set Θ := Real.exp (-(δ' * (ρn : ℝ))) with hΘ
    have hΘ0 : 0 < Θ := Real.exp_pos _
    have hΘ2 : Θ ^ 2 = Real.exp (-(2 * δ' * (ρn : ℝ))) := by
      rw [hΘ, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hδc : δ' ≤ c.δ₁ / 32 := min_le_left _ _
    have hδd : δ' ≤ cc / 2 := min_le_right _ _
    have hρ0 : (0 : ℝ) ≤ ρn := by positivity
    have hKΘ : (2 * (C₁ + C₁ * |Cc|) + 1) * Θ ≤ 1 := by
      have h1 : K ≤ Real.exp (δ' * (ρn : ℝ)) := hKρ
      have h2 : Real.exp (δ' * (ρn : ℝ)) * Θ = 1 := by
        rw [hΘ, ← Real.exp_add]
        simp
      calc _ = K * Θ := rfl
        _ ≤ Real.exp (δ' * (ρn : ℝ)) * Θ := mul_le_mul_of_nonneg_right h1 hΘ0.le
        _ = 1 := h2
    have hfin := near_identity_arith (C₁ := C₁) (Ca := |Cc|) (Na := |Nc|) (s := s) (X := Real.exp (-(c.δ₁ / 2 * Dd))) (Ee := Ee)
      (Aa := Aa) (Z := Real.exp (-(c.δ₁ / 16 * ρn))) (W := Wc) (Θ := Θ) (Λ := Real.exp (-(κ * (ρn : ℝ))))
      (Q := 16 * Ck 2 / Tb.threshold)
      hC₁ (abs_nonneg _) (abs_nonneg _) hs (Real.exp_pos _).le
      (Real.exp_le_one_iff.2 (by
        have : 0 ≤ c.δ₁ / 2 * (Dd : ℝ) := by positivity
        linarith))
      hX
      (by
        rw [hΘ2]
        apply Real.exp_le_exp.2
        nlinarith)
      (by
        rw [hΘ2]
        apply Real.exp_le_exp.2
        nlinarith)
      hWc0.le hΘ0 hKΘ
      (by
        apply Real.exp_le_exp.2
        have : κ ≤ δ' := min_le_right _ _
        nlinarith)
      (by positivity) (by positivity)
    exact hfin
  · have hs4 : Tb.threshold ≤ 4 * s := not_lt.1 hsσ
    have hcP : enclosingCell (slotOfCoordinate P).1 = (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
        siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₁ :=
      BlockOffsets.enclosingCell_offset hoddM hs2M _ ω₁ hω₁
    have hcQ : enclosingCell (slotOfCoordinate Q).1 = (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) +
        siteOfCoords (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).top h₂ :=
      BlockOffsets.enclosingCell_offset hoddM hs2M _ ω₂ hω₂
    have hcP' : enclosingCell Bb.1.1 = (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
          siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₁ :=
      BlockOffsets.enclosingCell_offset hoddT hs2T _ ω₁ hω₁
    have hcQ' : enclosingCell Bc.1.1 = (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) +
          siteOfCoords (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top h₂ :=
      BlockOffsets.enclosingCell_offset hoddT hs2T _ ω₂ hω₂
    have mainM : |chartMixedDeriv Tb.coupling w₀ Vm ![Sum.inl (slotOfCoordinate P), Sum.inl (slotOfCoordinate Q)]| ≤ Ck 2 * (Aa * Ee) := by
      refine abs_chartMixedDeriv_le hδ hCk2.le ((hker _ _ _ hFM hsmall 2 _).2 le_rfl ?_) fun Dn hDn => hexp Dn (htd Dn fun l => ?_)
      · intro l
        fin_cases l
        · simpa [directionVector, slotOfCoordinate] using norm_colourUnit P.2
        · simpa [directionVector, slotOfCoordinate] using norm_colourUnit Q.2
      · rw [hcP, hcQ] at hDn
        exact (abs_sub_le_cellSupDist hs2M (0 : (reflectedTorusFrame (Tb.stepParameters y).side (k + j) mN n).Cell) h₁ h₂ hdM l).trans
          (by exact_mod_cast hDn)
    have mixedDerivBound : |chartMixedDeriv Tb.coupling (fun _ _ => 0) (ColdStepAtMirrorFrames.uniformField
        (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n) (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top)
        ![Sum.inl (Bb.1.1, Bb.1.2, FlatHessian.colourUnit e), Sum.inl (Bc.1.1, Bc.1.2, FlatHessian.colourUnit e')]| ≤
          Ck 2 * (Aa * Ee) := by
      refine abs_chartMixedDeriv_le hδ hCk2.le ((hker _ _ _ hFT hzero 2 _).2 le_rfl ?_) fun Dn hDn => hexp Dn (htd Dn fun l => ?_)
      · intro l
        fin_cases l
        · simpa [directionVector] using norm_colourUnit e
        · simpa [directionVector] using norm_colourUnit e'
      · have hDn' : cellSupDist (enclosingCell Bb.1.1) (enclosingCell Bc.1.1) ≤ Dn := hDn
        rw [hcP', hcQ'] at hDn'
        exact (abs_sub_le_cellSupDist hs2T (StepCosts.torusSiteInFrame (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n)
          (TorusFields.torusFrame (Tb.stepParameters y).side (k + j) n).top o) h₁ h₂ hdT l).trans (by exact_mod_cast hDn')
    refine (abs_sub _ _).trans ((add_le_add mainM mixedDerivBound).trans ?_)
    have hAE : 0 < Aa * Ee := by positivity
    have hq1 : 2 * Ck 2 ≤ 16 * Ck 2 / Tb.threshold * s := by
      have h1 : 16 * Ck 2 / Tb.threshold * s = 16 * Ck 2 * (s / Tb.threshold) := by ring
      have h2 : 1 / 4 ≤ s / Tb.threshold := by
        rw [le_div_iff₀ hσ]
        linarith
      rw [h1]
      nlinarith
    have hq2 : 0 ≤ C₁ * (1 + |Nc|) * s := by positivity
    have hq3 : 0 < Real.exp (-(κ * (ρn : ℝ))) := Real.exp_pos _
    calc Ck 2 * (Aa * Ee) + Ck 2 * (Aa * Ee) = (2 * Ck 2) * (Aa * Ee) := by ring
      _ ≤ (16 * Ck 2 / Tb.threshold * s) * (Aa * Ee) := mul_le_mul_of_nonneg_right hq1 hAE.le
      _ ≤ (C₁ * (1 + |Nc|) + 16 * Ck 2 / Tb.threshold) * Aa * s * Ee + Real.exp (-(κ * (ρn : ℝ))) := by
        have : 0 ≤ C₁ * (1 + |Nc|) * s * (Aa * Ee) := by positivity
        nlinarith
theorem reflectedHessianEntries (hcurv : curvatureHalvesStatement) (hN : HessianEntriesNearTrivialTop)
    (hCol : FlatHessian.HessianAtFlatIsColourDiagonal) (hMB : mirrorOfColdBallSmallCurvatureStatement)
    (hcov : BlocksCoverLowerLevel) (hMF : ReflectedFieldSmallCurvature) (hMA : ReflectedFieldAgreesOnBox)
    (hMC : ReflectedCoordinateReadsBox) (hPV : PairedCoordinatesAgree) (hK : ChartEnergyKernelBound) :
    reflectedHessianEntriesStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := hcurv a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hLL T hTa hTL hDr hCS hCH hr hCd => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hL hLL T hTa hTL hDr hCS hCH hr hCd
  obtain ⟨c, nss, hties, -⟩ := hCS
  refine ⟨max y₀ ((2 : ℝ) ^ 1600), fun y hy hR hW => ?_⟩
  exact reflectedHessianEntriesAt_of hcov hMF hMB hMA hMC hPV hK hN hCol T y hDr c hties ((le_max_right _ _).trans hy) hR
    (fun β hβ => hW β hβ) (Hy y ((le_max_left _ _).trans hy) hR hW)
end YangMills.Construction.ResponseInTheExpansion
end
