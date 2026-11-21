import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClear
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheChainForgets
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAScoredTowerOnColdMirrors
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps TorusMirror WeightedResponses
namespace ResponseInTheExpansion.ColdMirrorRestriction
section Geometry
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
private theorem add_siteOfInt_offset (o z : TorusSite n) : o + siteOfInt (MirrorDensities.offset o z) = z := by
  funext i
  simp [MirrorDensities.offset, siteOfInt]
private theorem abs_offset_le_supDist (o z : TorusSite n) (i : Fin 4) :
    |MirrorDensities.offset o z i| ≤ (_root_.YangMills.Construction.TorusFields.supDist z o : ℤ) := by apply _root_.YangMills.Construction.MirrorDensities.abs_offset_le <;> assumption
private theorem supDist_add_le (o z : TorusSite n) (e : Fin 4 → ℤ) (m : ℕ) (he : OffsetInBox m e) :
    _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt e) o ≤ m + _root_.YangMills.Construction.TorusFields.supDist z o := by
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle (z + siteOfInt e) z o
  have h2 : _root_.YangMills.Construction.TorusFields.supDist z (z + siteOfInt e) ≤ m := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le z e m fun i => by
    have := he i
    rw [Int.abs_eq_natAbs] at this
    omega
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm (z + siteOfInt e) z] at h1
  omega
private theorem add_mem_supBall {R : ℝ} {m : ℕ} (o z : TorusSite n) (e : Fin 4 → ℤ) (he : OffsetInBox m e)
    (hz : (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) + m ≤ R) : z + siteOfInt e ∈ supBall o R := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h1 : (_root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt e) o : ℝ) ≤ (m : ℝ) + _root_.YangMills.Construction.TorusFields.supDist z o := by
    exact_mod_cast supDist_add_le o z e m he
  linarith
private theorem fieldsAgreeNear_mirrorField (m : ℕ) (hm : 2 ≤ m) (z : TorusSite n) (W : TorusField n) :
    FieldsAgreeNear W (mirrorField m z W) z (0 : TorusSite (4 * m)) m := by
  intro b hb
  have h := mirrorField_siteOfInt (m := m) hm z W b hb
  show W (z + siteOfInt b.1) b.2 = mirrorField m z W (0 + siteOfInt b.1) b.2
  rw [zero_add]
  exact h.symm
variable {ℓ : StepParameters}
private theorem torusHotSites_subset_state (T : StageTower ℓ) (k n : ℕ) [NeZero n] (u : MarkedSample ℓ k n) :
    torusHotSites ℓ (stageState T k n u).1 ⊆ (stageState T k n u).2.1 := by
  intro z hz
  cases k with
  | zero =>
    exact (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
  | succ k =>
    refine (mem_thickening _ _ _).mpr ⟨z, ?_, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; exact Nat.zero_le _⟩
    refine Finset.mem_union_left _ ?_
    exact (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
private theorem stageState_fst (T : StageTower ℓ) (k n : ℕ) [NeZero n] (u : MarkedSample ℓ k n) :
    (stageState T k n u).1 = topField ℓ k n u := by apply _root_.YangMills.SharedProofs.p2480 <;> assumption
private theorem isCold_mirrorField_of_disjoint (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {m : ℕ} (hm : 1 ≤ m)
    (o z : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)) {R : ℝ} (hhot : torusHotSites ℓ W ⊆ Y) (hdisj : Disjoint Y (supBall o R))
    (hz : (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) + m ≤ R) : IsCold ℓ.threshold (mirrorField m z W) := by
  refine isCold_mirrorField (m := m) (by omega) z W hfit.σ_pos fun a μ ν hlt hb => ?_
  by_contra hcon
  have hh := mem_torusHotSites_of_mem_plaquetteVertices hfit hLn hlt (not_lt.mp hcon)
    (base_mem_plaquetteVertices (z + siteOfInt a) μ ν)
  have ha : OffsetInBox m a := by
    simpa using hb 0 (by simp [plaquetteOffsets])
  exact Finset.disjoint_left.mp hdisj (hhot hh) (add_mem_supBall o z a ha hz)
private theorem statesAgreeNear_mirrorField {Ω : Type} {m : ℕ} (hm : 2 ≤ m) [NeZero (4 * m)]
    (o z : TorusSite n) (W : TorusField n)
    (Y : Finset (TorusSite n)) (ω : Y → Ω) (ω' : (∅ : Finset (TorusSite (4 * m))) → Ω) {R : ℝ}
    (hdisj : Disjoint Y (supBall o R)) (hside : 2 * m + 2 < n) (hz : (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) + m ≤ R) :
    StatesAgreeNear ℓ W (mirrorField m z W) Y ∅ ω ω' z 0 m := by
  have hoff : ∀ e, OffsetInBox m e → z + siteOfInt e ∉ Y := fun e he hmem =>
    Finset.disjoint_left.mp hdisj hmem (add_mem_supBall o z e he hz)
  refine ⟨hside, by omega, fieldsAgreeNear_mirrorField m hm z W, fun e he => ?_, ?_, ?_⟩
  · constructor
    · intro hmem
      exact absurd hmem (hoff e he)
    · intro hmem
      simp at hmem
  · intro e _ _ hz' _
    simp at hz'
  · rintro ⟨e, he, hmem⟩
    exact absurd hmem (hoff e he)
private theorem card_le_of_supDist_le (o : TorusSite n) (S : Finset (TorusSite n)) (R : ℕ)
    (hS : ∀ z ∈ S, _root_.YangMills.Construction.TorusFields.supDist z o ≤ R) :
    (S.card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 4 := by
  have h1 : S.card ≤ (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R).card := by
    refine Finset.card_le_card_of_injOn (MirrorDensities.offset o) (fun z hz => ?_) (fun z _ z' _ hzz => ?_)
    · have hm : MirrorDensities.offset o z ∈ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) R := by
        rw [Fintype.mem_piFinset]
        intro i
        have := abs_le.mp (abs_offset_le_supDist o z i)
        have h2 := hS z hz
        simp only [Finset.mem_Icc]
        omega
      exact hm
    · rw [← add_siteOfInt_offset o z, ← add_siteOfInt_offset o z', hzz]
  rw [Fintype.card_piFinset] at h1
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
  rw [h2] at h1
  exact_mod_cast h1
end Geometry
section Walk
variable {ℓ : StepParameters}
private def DescendsClear (T : StageTower ℓ) (β : ℝ) (k H : ℕ) (m side : ℝ) : Prop :=
  ∀ h, k ≤ h → h < H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite n,
    ∀ᵐ u ∂(markedSampleLaw T β (h + 1) n),
      Disjoint (stageState T (h + 1) n u).2.1 (supBall o m) → StepAvoids T h m o u →
      ∀ o' : TorusSite (n * ℓ.side), parentBlock ℓ.side o' = o →
        Disjoint (stageState T h (n * ℓ.side) u.1).2.1 (supBall o' m)
private theorem measurable_fst_sample (ℓ : StepParameters) (h n : ℕ) :
    Measurable fun u : MarkedSample ℓ (h + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem le_cast_mul_side {side : ℝ} {n : ℕ} (_h0 : 0 ≤ side) (h : side ≤ n) :
    side ≤ ((n * ℓ.side : ℕ) : ℝ) := by
  have hL : (1 : ℝ) ≤ ℓ.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  push_cast
  nlinarith
abbrev _root_.YangMills.SharedProofs.p36346 := @le_cast_mul_side
private theorem ae_disjoint_sampleBelow {T : StageTower ℓ} {β : ℝ} {k H s : ℕ} {m side : ℝ}
    (hS : DescendsClear T β k H m side)
    (hfst : ∀ (h n : ℕ) [NeZero n], MeasurePreserving (fun u : MarkedSample ℓ (h + 1) n => u.1)
      (markedSampleLaw T β (h + 1) n) (markedSampleLaw T β h (n * ℓ.side)))
    (h0 : 0 ≤ side) (hs : k ≤ s) :
    ∀ D, s + D ≤ H → ∀ (n : ℕ) [NeZero n], side ≤ n → ℓ.side ∣ n → ∀ o : TorusSite (fineSide ℓ.side D n),
      ∀ᵐ u ∂(markedSampleLaw T β (s + D) n),
        Disjoint (stageState T (s + D) n u).2.1 (supBall (siteAbove ℓ.side D n o) m) →
        StepsAvoidOrigin T s m D n u o →
        Disjoint (stageState T s _ (sampleBelow ℓ s D n u)).2.1 (supBall o m) := by
  intro D
  induction D with
  | zero =>
    intro _ n _ _ _ o
    exact Filter.Eventually.of_forall fun u h _ => h
  | succ D ih =>
    intro hD n _ hn hLn o
    have hih := ih (by omega) (n * ℓ.side) (le_cast_mul_side h0 hn) (Dvd.intro_left n rfl) o
    have hlift : ∀ᵐ u ∂(markedSampleLaw T β (s + (D + 1)) n),
        Disjoint (stageState T (s + D) (n * ℓ.side) u.1).2.1
          (supBall (siteAbove ℓ.side D (n * ℓ.side) o) m) →
        StepsAvoidOrigin T s m D (n * ℓ.side) u.1 o →
        Disjoint (stageState T s _ (sampleBelow ℓ s D (n * ℓ.side) u.1)).2.1 (supBall o m) :=
      (hfst (s + D) n).quasiMeasurePreserving.ae hih
    have hdn := hS (s + D) (by omega) (by omega) n hn hLn (siteAbove ℓ.side (D + 1) n o)
    filter_upwards [hlift, hdn] with u h1 h2 hdis hmiss
    obtain ⟨hsm, hfc⟩ := hmiss
    exact h1 (h2 hdis hfc (siteAbove ℓ.side D (n * ℓ.side) o) rfl) hsm
end Walk
section Numbers
private theorem le_rpow_hundredth {b x : ℝ} (hb : 0 ≤ b) (hx : b ^ 100 ≤ x) : b ≤ x ^ ((1 : ℝ) / 100) := by
  have h := Real.rpow_le_rpow (by positivity) hx (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have h2 : (b ^ 100) ^ ((1 : ℝ) / 100) = b := by
    rw [← Real.rpow_natCast b 100, ← Real.rpow_mul hb]
    norm_num
  rwa [h2] at h
abbrev _root_.YangMills.SharedProofs.p61349 := @le_rpow_hundredth
end Numbers
section Main
private theorem mirror_responses_near {ℓ : StepParameters} (hfit : ℓ.Admissible) (T : StageTower ℓ) (β : ℝ)
    (al : ℕ → ℝ) (k : ℕ) {n : ℕ} [NeZero n]
    (hLn : ℓ.side ∣ n) {m : ℕ} (hm : 2 ≤ m) [NeZero (4 * m)] (hn₀ : ℓ.n₀ ≤ 4 * m) (hside : 2 * m + 2 < n)
    (o : TorusSite n) (h : PlaquetteWeight (fineSide ℓ.side k n)) (u : MarkedSample ℓ k n) (c nn R : ℝ)
    (Fz : TorusSite n → ℝ)
    (hr : (clusterRange (flowCouplings ℓ β k) : ℝ) / 64 ≤ (m : ℕ)) (hmid : 12 * nn + m ≤ R) (hnn : 1 ≤ nn)
    (h' : TorusSite n → PlaquetteWeight (fineSide ℓ.side k (4 * m)))
    (hsupp : ∀ z p, z ∉ supBall o (12 * nn) → IsPlaquetteAt ℓ.side k z p → h p = 0)
    (hzero : ∀ z, z ∉ weightSupportSites ℓ.side k n h → Fz z = 0)
    (hclose : ∀ (z : TorusSite n) (n' : ℕ) [NeZero n'] (W' : TorusField n') (z' : TorusSite n') (m : ℕ)
      (ω' : (∅ : Finset (TorusSite n')) → (T.stage k).labels.Ω) (h' : PlaquetteWeight (fineSide ℓ.side k n')),
      ℓ.n₀ ≤ n' → IsCold ℓ.threshold W' → (clusterRange (flowCouplings ℓ β k) : ℝ) / 64 ≤ m →
      StatesAgreeNear ℓ (stageState T k n u).1 W' (stageState T k n u).2.1 ∅ (stageState T k n u).2.2 ω' z z' m →
      WeightsAgreeAt ℓ.side k z z' h h' →
      |Fz z - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) n' z' W' h'| ≤
        Real.exp (-(c * m)) * weightNorm ℓ.side k h)
    (hagree : ∀ z ∈ weightSupportSites ℓ.side k n h, WeightsAgreeAt ℓ.side k z (0 : TorusSite (4 * m)) h (h' z))
    (hdisj : Disjoint (stageState T k n u).2.1 (supBall o R)) :
    (∀ z ∈ weightSupportSites ℓ.side k n h, IsCold ℓ.threshold (mirrorField m z (topField ℓ k n u))) ∧
    |∑ z, Fz z - ∑ z ∈ weightSupportSites ℓ.side k n h,
        centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * m) 0
        (mirrorField m z (topField ℓ k n u)) (h' z)| ≤
      25 ^ 4 * nn ^ 4 * Real.exp (-(c * m)) * weightNorm ℓ.side k h := by
  classical
  have hnear : ∀ z ∈ weightSupportSites ℓ.side k n h, (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) ≤ 12 * nn := by
    intro z hz
    by_contra hcon
    have hz' : z ∉ supBall o (12 * nn) := fun hm => hcon (Finset.mem_filter.mp hm).2
    obtain ⟨p, hp, hne⟩ := (Finset.mem_filter.mp hz).2
    exact hne (hsupp z p hz' hp)
  have hnearR : ∀ z ∈ weightSupportSites ℓ.side k n h, (_root_.YangMills.Construction.TorusFields.supDist z o : ℝ) + m ≤ R := fun z hz => by
    linarith [hnear z hz]
  have hcold : ∀ z ∈ weightSupportSites ℓ.side k n h, IsCold ℓ.threshold (mirrorField m z (topField ℓ k n u)) := by
    intro z hz
    rw [← stageState_fst T]
    exact isCold_mirrorField_of_disjoint hfit hLn (by omega) o z _ _ (torusHotSites_subset_state T k n u) hdisj
      (hnearR z hz)
  refine ⟨hcold, ?_⟩
  have hnn0 : (0 : ℝ) ≤ 12 * nn := by linarith
  have hcard := card_le_of_supDist_le o (weightSupportSites ℓ.side k n h) ⌊12 * nn⌋₊ fun z hz =>
    Nat.le_floor (hnear z hz)
  have hcard' : ((weightSupportSites ℓ.side k n h).card : ℝ) ≤ 25 ^ 4 * nn ^ 4 := by
    have h5 : 2 * (⌊12 * nn⌋₊ : ℝ) + 1 ≤ 25 * nn := by
      have := Nat.floor_le hnn0
      linarith
    calc ((weightSupportSites ℓ.side k n h).card : ℝ) ≤ (2 * (⌊12 * nn⌋₊ : ℝ) + 1) ^ 4 := hcard
      _ ≤ (25 * nn) ^ 4 := pow_le_pow_left₀ (by positivity) h5 4
      _ = 25 ^ 4 * nn ^ 4 := by ring
  have hsum : ∑ z, Fz z = ∑ z ∈ weightSupportSites ℓ.side k n h, Fz z :=
    (Finset.sum_subset (Finset.subset_univ _) fun z _ hz => hzero z hz).symm
  have hsize : 0 ≤ weightNorm ℓ.side k h :=
    le_trans (Real.iSup_nonneg fun _ => abs_nonneg _) (le_max_left _ _)
  have hexp : 0 ≤ Real.exp (-(c * m)) * weightNorm ℓ.side k h := mul_nonneg (Real.exp_pos _).le hsize
  rw [hsum, ← Finset.sum_sub_distrib]
  calc |∑ z ∈ weightSupportSites ℓ.side k n h,
          (Fz z - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * m) 0
          (mirrorField m z (topField ℓ k n u)) (h' z))|
      ≤ ∑ z ∈ weightSupportSites ℓ.side k n h,
          |Fz z - centeredResponse (coldResponseChain ℓ β (flowCouplings ℓ β) al k) (4 * m) 0
          (mirrorField m z (topField ℓ k n u)) (h' z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ weightSupportSites ℓ.side k n h, Real.exp (-(c * m)) * weightNorm ℓ.side k h := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hb := hclose z (4 * m) (mirrorField m z (topField ℓ k n u)) 0 m
          (fun x => (Finset.notMem_empty _ x.2).elim) (h' z) hn₀ (hcold z hz) hr
          (by
            rw [← stageState_fst T]
            exact statesAgreeNear_mirrorField hm o z _ _ _ _ hdisj hside (hnearR z hz))
          (hagree z hz)
        exact hb
    _ = ((weightSupportSites ℓ.side k n h).card : ℝ) * (Real.exp (-(c * m)) * weightNorm ℓ.side k h) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 25 ^ 4 * nn ^ 4 * (Real.exp (-(c * m)) * weightNorm ℓ.side k h) :=
        mul_le_mul_of_nonneg_right hcard' hexp
    _ = 25 ^ 4 * nn ^ 4 * Real.exp (-(c * m)) * weightNorm ℓ.side k h := by ring
theorem scoredTowerColdMirrorResponse (hF : chainResponseLocalityStatement)
    (hO : descentKeepsBallClearStatement)
    (hLaw : sampleBelowLawStatement) : scoredTowerColdMirrorResponseStatement := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, hr₁, H₁⟩ := hF a ha
  obtain ⟨L₂, r₂, c₂, hr₂, H₂⟩ := hO a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max c₁ c₂, fun c => lt_min (hr₁ c) (hr₂ c),
    fun L hL hL₀ Tb hTa hTL hD hCS hCH hr hC => ?_⟩
  obtain ⟨y₁, p₁⟩ := H₁ L hL ((le_max_left _ _).trans hL₀) Tb hTa hTL hD hCS hCH (hr.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨y₂, p₂⟩ := H₂ L hL ((le_max_right _ _).trans hL₀) Tb hTa hTL hD hCS hCH (hr.trans (min_le_right _ _))
    ((le_max_right _ _).trans hC)
  refine ⟨max Tb.floorMin (max y₁ y₂), fun y hy hRet hW => ?_⟩
  have e₀ : Tb.floorMin ≤ y := (le_max_left _ _).trans hy
  have e₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have e₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y e₀
  have hLgt : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side := hD.L_gt
  intro Kr hKr
  obtain ⟨c, xf, hc, Hc⟩ := p₁ y e₁ hRet hW Kr hKr
  obtain ⟨xd, Hd⟩ := p₂ y e₂ hRet hW
  have hb0 : (0 : ℝ) ≤ 64 * (((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ + 2) := by positivity
  refine ⟨25 ^ 4, c, max xf (max xd ((64 * (((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ + 2)) ^ 100)),
    hc, ?_⟩
  intro T S β k tp N _ nn o m' _ hch hLN hk hSK hSrun hrg hmid h hsupp
  have hxf : xf ≤ flowCouplings (Tb.stepParameters y) β k := (le_max_left _ _).trans hch.floor_le
  have hxd : xd ≤ flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hch.floor_le
  have hxb : (64 * (((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ + 2)) ^ 100 ≤
      flowCouplings (Tb.stepParameters y) β k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hch.floor_le
  have hroot := le_rpow_hundredth hb0 hxb
  have hrange : flowCouplings (Tb.stepParameters y) β k ^ ((1 : ℝ) / 100) ≤
      clusterRange (flowCouplings (Tb.stepParameters y) β k) :=
    Nat.le_ceil _
  have hm'r : ((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ + 2 ≤ m' := by
    linarith only [hroot, hrange, hrg]
  have hLn₀ : (0 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ := by positivity
  have hm2 : 2 ≤ m' := by
    have : (2 : ℝ) ≤ m' := by linarith only [hm'r, hLn₀]
    exact_mod_cast this
  have hLpos : (1 : ℝ) ≤ (Tb.stepParameters y).side := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Tb.stepParameters y).side)
  have hn₀' : ((Tb.stepParameters y).n₀ : ℝ) ≤ m' := by
    have h1 : ((Tb.stepParameters y).n₀ : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) hLpos
    linarith only [h1, hm'r]
  have hn₀ : (Tb.stepParameters y).n₀ ≤ 4 * m' := by
    have : (Tb.stepParameters y).n₀ ≤ m' := by exact_mod_cast hn₀'
    omega
  have hnn1 : 1 ≤ nn := hch.one_le
  have hmR : (m' : ℝ) + 12 ≤ localBoxRadius (flowCouplings (Tb.stepParameters y) β k) := by
    linarith only [hmid, hnn1]
  have hside0 : (0 : ℝ) ≤ 2 ^ 10 * localBoxRadius (flowCouplings (Tb.stepParameters y) β k) := by
    have : (0 : ℝ) ≤ localBoxRadius (flowCouplings (Tb.stepParameters y) β k) := Nat.cast_nonneg _
    positivity
  have hNs : 2 ^ 10 * localBoxRadius (flowCouplings (Tb.stepParameters y) β k) ≤ (N : ℝ) := hch.side_ge
  have hup : ∀ (d n : ℕ), (n : ℝ) ≤ (fineSide (Tb.stepParameters y).side d n : ℝ) := by
    intro d n
    rw [fineSide_eq]
    have h1 : 1 ≤ (Tb.stepParameters y).side ^ d := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne _))
    exact_mod_cast Nat.le_mul_of_pos_right n h1
  have hdvd : ∀ (d n : ℕ), (Tb.stepParameters y).side ∣ n →
      (Tb.stepParameters y).side ∣ fineSide (Tb.stepParameters y).side d n := by
    intro d n hn
    rw [fineSide_eq]
    exact Dvd.dvd.mul_right hn _
  have hN1 := hup (localChainDepth (Tb.stepParameters y) β k) N
  have hN2 := hup (localChainDepth (Tb.stepParameters y) β k)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)
  have hside' : (2 * m' + 2 : ℝ) < (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) : ℝ) := by
    linarith only [hN1, hN2, hNs, hmR, hm'r, hLn₀]
  have hside : 2 * m' + 2 < fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) := by
    exact_mod_cast hside'
  have hL2 := hdvd (localChainDepth (Tb.stepParameters y) β k) _ hLN
  have hL3 := hdvd (localChainDepth (Tb.stepParameters y) β k) _ hL2
  have hblock : IsBlockTorusSide (Tb.stepParameters y)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) := by
    refine ⟨hL3, ?_⟩
    have : ((Tb.stepParameters y).side : ℝ) * (Tb.stepParameters y).n₀ ≤
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) : ℝ) := by
      linarith only [hN1, hN2, hNs, hmR, hm'r]
    exact_mod_cast this
  have hrun : ∀ j ≤ k, (Tb.stepParameters y).y₁ ≤ flowCouplings (Tb.stepParameters y) β j :=
    fun j hj => hch.coupling_ge j (by omega)
  have hlaw := (hLaw (Tb.stepParameters y) hfit hLgt T hch.cutoff hch.measurable β S.coeffs).1
  have hfst : ∀ (h n : ℕ) [NeZero n], MeasurePreserving (fun u : MarkedSample (Tb.stepParameters y) (h + 1) n => u.1)
      (markedSampleLaw T β (h + 1) n) (markedSampleLaw T β h (n * (Tb.stepParameters y).side)) := fun h n _ =>
    ⟨measurable_fst_sample _ h n, (hlaw h 1 n).2⟩
  have hSD : DescendsClear T β k (k + 2 * localChainDepth (Tb.stepParameters y) β k)
      (localBoxRadius (flowCouplings (Tb.stepParameters y) β k))
      (2 ^ 10 * localBoxRadius (flowCouplings (Tb.stepParameters y) β k)) := by
    intro hh hkh hH n _ hn hLn oo
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkh
    have hch' : IsLocalChainAbove Tb y T β k n nn xd :=
      ⟨hxd, hch.coupling_ge, hch.onFamily, hch.cutoff, hch.measurable, hn, hch.one_le, hch.le_rpow⟩
    filter_upwards [Hd T β k n nn j oo hch' hLn (by omega)] with u hu hdis hmiss o' ho'
    exact ((hu hdis).2 hmiss).1 o' ho'
  have hA := ae_disjoint_sampleBelow hSD hfst hside0 (s := k + localChainDepth (Tb.stepParameters y) β k) (by omega)
    (localChainDepth (Tb.stepParameters y) β k) (by omega) N hNs hLN
    (siteAbove (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
      (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) o)
  have hB := ae_disjoint_sampleBelow hSD hfst hside0 (s := k) le_rfl (localChainDepth (Tb.stepParameters y) β k)
    (by omega)
    (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N) (hNs.trans hN1) hL2 o
  have hmp₁ : MeasurePreserving (sampleBelow (Tb.stepParameters y) (k + localChainDepth (Tb.stepParameters y) β k)
        (localChainDepth (Tb.stepParameters y) β k) N)
      (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k +
        localChainDepth (Tb.stepParameters y) β k) N)
      (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N)) :=
    ⟨(hlaw _ _ N).1, (hlaw _ _ N).2⟩
  have hmp₂ : MeasurePreserving (sampleBelow (Tb.stepParameters y) k (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))
      (markedSampleLaw T β (k + localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))
      (markedSampleLaw T β k (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k)
        (fineSide (Tb.stepParameters y).side (localChainDepth (Tb.stepParameters y) β k) N))) :=
    ⟨(hlaw _ _ _).1, (hlaw _ _ _).2⟩
  have hFg := Hc T S β k tp hk hSK hSrun hrun hxf _ hblock h
  refine ⟨∑ z, coldResponseChain (Tb.stepParameters y) β (flowCouplings (Tb.stepParameters y) β) S.coeffs k _ z
    (trivialField _) h, fun h' hh' => ?_⟩
  filter_upwards [hA, hmp₁.quasiMeasurePreserving.ae hB,
    hmp₁.quasiMeasurePreserving.ae (hmp₂.quasiMeasurePreserving.ae hFg)] with u a1 a2 a3 hloc
  obtain ⟨Fz, hsum, hzero, hclose⟩ := a3
  have hdisj := a2 (a1 hloc.1 hloc.2.1) hloc.2.2
  obtain ⟨hcold, hnear⟩ := mirror_responses_near hfit T β S.coeffs k hL3 hm2 hn₀ hside o h _ c nn _ Fz hrg hmid
    hnn1 h' hsupp hzero hclose hh' hdisj
  refine ⟨hcold, ?_⟩
  rw [hsum]
  refine le_trans (le_of_eq ?_) hnear
  congr 1
  unfold sampledLevelField
  ring
end Main
end ResponseInTheExpansion.ColdMirrorRestriction
end YangMills.Construction
end
