import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesAtParametersProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlocksHaveAGrid
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheFrameIsACurvatureFamily
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtTheLeastFieldOfTheChain
import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainOfNoFlux
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAtTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormFromAnExpansion
import YangMills.Construction.ColdStepAtMirrorFrames.LevelOfTheCurvedChainOnATorus
import YangMills.Construction.ColdStepAtMirrorFrames.LowerFamiliesReadOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields Filter
namespace YangMills.Construction.ColdStepAtMirrorFrames
private abbrev IntPoint : Type := Fin 4 → ℤ
private theorem dvd_sub_siteCoords {H : BlockFrame} {k : ℕ} (z : IntPoint) (i : Fin 4) :
    (H.period k i : ℤ) ∣ z i - siteCoords (siteOfCoords k z : H.Site k) i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.period_dvd_sub_siteCoords <;> assumption
private theorem period_top (H : BlockFrame) (i : Fin 4) : H.period H.top i = H.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
private theorem period_depth (H : BlockFrame) (i : Fin 4) :
    H.period H.depth i = H.extent i * H.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
private def blockPoint (L : ℕ) (q r : IntPoint) : IntPoint := fun i => (L : ℤ) * q i + r i
private theorem cellCentre_siteOfCoords (H : BlockFrame) (q : IntPoint) :
    (cellCentre H.depth (siteOfCoords H.top q : H.Cell) : H.Site H.depth) =
      siteOfCoords H.depth fun i => (H.blockSide : ℤ) * q i := by apply _root_.YangMills.Construction.HoleBounds.FromThresholds.cellCentre_siteOfCoords <;> assumption
private theorem enclosingCell_blockPoint (H : BlockFrame) (m : ℕ) (hm : H.blockSide = 2 * m + 1) {n : ℕ}
    (hn : ∀ i, H.extent i = n) (h0 : 0 < n) (q r : IntPoint) (hr : ∀ i, |r i| ≤ (m : ℤ)) :
    enclosingCell (siteOfCoords H.depth (blockPoint H.blockSide q r) : H.Site H.depth) =
      siteOfCoords H.top q := by
  unfold enclosingCell
  have h1 : H.top - H.depth = 1 := by simp [BlockFrame.top]
  rw [h1, pow_one]
  apply siteOfCoords_eq_of_dvd
  intro i
  have hLz : (H.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hLpos : (0 : ℤ) < (H.blockSide : ℤ) := by rw [hLz]; positivity
  have hmz : ((H.blockSide : ℤ) - 1) / 2 = m := by rw [hLz]; omega
  rw [hmz, period_top, hn]
  have hd := dvd_sub_siteCoords (H := H) (k := H.depth) (blockPoint H.blockSide q r) i
  rw [period_depth, hn] at hd
  obtain ⟨s, hs⟩ := hd
  have hbi := abs_le.1 (hr i)
  have hc : siteCoords (siteOfCoords H.depth (blockPoint H.blockSide q r) : H.Site H.depth) i + m =
      (r i + m) + (H.blockSide : ℤ) * (q i - (n : ℤ) * s) := by
    have : blockPoint H.blockSide q r i = (H.blockSide : ℤ) * q i + r i := rfl
    push_cast at hs
    rw [this] at hs
    linarith
  rw [hc, Int.add_mul_ediv_left _ _ hLpos.ne',
    Int.ediv_eq_zero_of_lt (by linarith [hbi.1]) (by rw [hLz]; linarith [hbi.2]), zero_add]
  exact ⟨s, by ring⟩
abbrev _root_.YangMills.DeltaSharedProofs.p502341 := @enclosingCell_blockPoint
private theorem exists_blockPoint (H : BlockFrame) (m : ℕ) (hm : H.blockSide = 2 * m + 1) (x : H.Site H.depth) :
    ∃ q r : IntPoint, (∀ i, |r i| ≤ (m : ℤ)) ∧ x = siteOfCoords H.depth (blockPoint H.blockSide q r) := by
  have hLz : (H.blockSide : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hLpos : (0 : ℤ) < (H.blockSide : ℤ) := by rw [hLz]; positivity
  refine ⟨fun i => (siteCoords x i + m) / (H.blockSide : ℤ),
    fun i => siteCoords x i - (H.blockSide : ℤ) * ((siteCoords x i + m) / (H.blockSide : ℤ)), ?_, ?_⟩
  · intro i
    have e1 := Int.emod_add_mul_ediv (siteCoords x i + m) (H.blockSide : ℤ)
    have e2 := Int.emod_nonneg (siteCoords x i + m) hLpos.ne'
    have e3 := Int.emod_lt_of_pos (siteCoords x i + m) hLpos
    rw [abs_le]
    constructor <;> nlinarith
  · conv_lhs => rw [← siteOfCoords_siteCoords x]
    congr 1
    funext i
    simp [blockPoint]
abbrev _root_.YangMills.DeltaSharedProofs.p502172 := @exists_blockPoint
private theorem card_centredCube (L : ℕ) (hL : Odd L) : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.card_centredCube_real <;> assumption
private theorem card_sites_in_cell_le (F : BlockFrame) (hodd : Odd F.blockSide) (n : ℕ) (hn : ∀ i, F.extent i = n)
    (h0 : 0 < n) (Y : F.Cell) :
    (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      (F.blockSide : ℝ) ^ 4 := by
  classical
  obtain ⟨m, hm⟩ := hodd
  have hm' : F.blockSide = 2 * m + 1 := hm
  have hsub : (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y) ⊆
      (centredCube F.blockSide).image fun r => cellCentre F.depth Y + siteOfCoords F.depth r := by
    intro y hy
    obtain ⟨_, hc⟩ := Finset.mem_filter.1 hy
    obtain ⟨q, r, hr, rfl⟩ := exists_blockPoint F m hm' y
    rw [enclosingCell_blockPoint F m hm' hn h0 q r hr] at hc
    refine Finset.mem_image.2 ⟨r, ?_, ?_⟩
    · unfold centredCube
      rw [Fintype.mem_piFinset]
      intro i
      have hz : (((F.blockSide : ℤ) - 1) / 2) = m := by
        rw [hm']; push_cast; omega
      rw [Finset.mem_Icc, hz]
      exact abs_le.1 (hr i)
    · rw [← hc, cellCentre_siteOfCoords, ← siteOfCoords_add]
      rfl
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := centredCube F.blockSide)
    (f := fun r => cellCentre F.depth Y + siteOfCoords F.depth r)
  have h3 : (((sitesOfCells (finiteCells F) F.depth).filter fun y => enclosingCell y = Y).card : ℝ) ≤
      ((centredCube F.blockSide).card : ℝ) := by
    exact_mod_cast h1.trans h2
  rw [card_centredCube F.blockSide ⟨m, hm⟩] at h3
  exact h3
private theorem cast_cast_eq {a b : ℕ} (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
private theorem readAtLevel_restrictToTorus {F : BlockFrame} {j m : ℕ} (hp : ∀ i, F.period j i = m)
    (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by apply _root_.YangMills.DeltaSharedProofs.p502190 <;> assumption
private theorem constantPlaneCurvature_eq (X : imaginaryQuaternions) (μ ν : Fin 4) :
    constantPlaneCurvature X μ ν = curvatureAlong X (planeUnitForm μ ν) := by
  funext α β
  show (if α = μ ∧ β = ν then X else if α = ν ∧ β = μ then -X else 0) =
    (if α = μ ∧ β = ν then (1 : ℝ) else if α = ν ∧ β = μ then -1 else 0) • X
  by_cases h1 : α = μ ∧ β = ν
  · rw [if_pos h1, if_pos h1, one_smul]
  · by_cases h2 : α = ν ∧ β = μ
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      exact (neg_one_smul ℝ X).symm
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, zero_smul]
abbrev _root_.YangMills.SharedProofs.p53264 := @constantPlaneCurvature_eq
private theorem planeUnitForm_antisymm (μ ν : Fin 4) (hμν : μ < ν) (i j : Fin 4) :
    planeUnitForm μ ν i j = - planeUnitForm μ ν j i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.planeUnitForm_antisymm <;> assumption
private theorem eventually_large (γ₀ : ℝ) (hγ₀ : 0 < γ₀) (n₁ : ℕ) :
    ∀ᶠ n : ℕ in atTop, n₁ ≤ n ∧ 2 ≤ n ∧ 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 < γ₀ ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤ 1 ∧
      4 * Real.log (1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2)) ^ 2 + 4 < (n : ℝ) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ 2‖ ≤ (1 / 64) * ‖x‖ := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (c := 1 / 64) (by norm_num)
    simpa using h
  have hlog' := hcast.eventually hlog
  have hbig : ∀ᶠ n : ℕ in atTop, (8 : ℝ) + 2 * Real.pi / γ₀ + 2 * Real.pi < (n : ℝ) :=
    hcast.eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop n₁, eventually_ge_atTop 2, hlog', hbig] with n h1 h2 h3 h4
  have hπ := Real.pi_gt_three
  have hdiv : 0 < 2 * Real.pi / γ₀ := by positivity
  have hn0 : (0 : ℝ) < n := by linarith
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hγ : 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 = 2 * Real.pi / (n : ℝ) ^ 2 := by simp
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rw [hγ, div_lt_iff₀ (by positivity)]
    have : 2 * Real.pi / γ₀ < (n : ℝ) ^ 2 := by linarith
    rw [div_lt_iff₀ hγ₀] at this
    linarith
  · rw [hγ, div_le_one (by positivity)]
    linarith
  · rw [hγ]
    have hinv : 1 / (2 * Real.pi / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 / (2 * Real.pi) := by field_simp
    rw [hinv]
    have hlo : 0 ≤ Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hup : Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) ≤ 2 * Real.log n := by
      have e1 : (n : ℝ) ^ 2 / (2 * Real.pi) ≤ (n : ℝ) ^ 2 := by
        apply div_le_self (by positivity)
        linarith
      have e2 := Real.log_le_log (by positivity) e1
      rwa [Real.log_pow] at e2
    have hsq2 : Real.log ((n : ℝ) ^ 2 / (2 * Real.pi)) ^ 2 ≤ 4 * Real.log n ^ 2 := by nlinarith
    have h3' : Real.log n ^ 2 ≤ (1 / 64) * n := by
      have := h3
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos hn0] at this
      exact this
    nlinarith
abbrev _root_.YangMills.SharedProofs.p36503 := @eventually_large
theorem flatLimitAtMinimizer (hgrid : LumpGridExists) (hsec : SecondOrderOnMultiplesOfSide)
    (hform : FlatLimitFromExpansion) (hfam : expansionAtFrameIsCurvatureFamily)
    (hlow : LocalFamilyOnTori) (hchain : ExpansionAtMinimizingChainField)
    (hlevel : ConstantCurvatureLevelOnTorus) (hno : ConstantCurvatureChainFlatOfZeroFlux) :
    flatLimitAtMinimizerStatement := by
  classical
  intro T hd hL hn₀ htrans hden t x f hx hrow
  obtain ⟨g⟩ := hgrid T.L hL
  have hLpos : 0 < T.L := by omega
  haveI : NeZero T.L := ⟨hLpos.ne'⟩
  obtain ⟨hadm, hfam'⟩ := hfam T g hd hL hn₀
  have hcf := hfam' htrans true t x f hx hrow (hden t x f true hx hrow)
  refine hform (torusStepParameters T g) t T.energyRatio 0 _ hadm le_rfl hcf ?_
  intro X μ ν hX hμν ε hε
  have hE : 0 < T.E := by linarith [hd.one_le_E]
  have hEE : T.E ≤ T.energyRatio := by
    show T.E ≤ T.E / T.η₃
    rw [le_div_iff₀ hd.η₃_pos]
    nlinarith [hd.η₃_le_one]
  obtain ⟨hcl, hsecond, hcentl⟩ :=
    hlow (torusStepParameters T g) t T.decayRate T.E T.energyRatio f hadm rfl rfl hE hEE hrow
  obtain ⟨hlim, _, _, _, _, _, hwide, _⟩ :=
    hsec (torusStepParameters T g) hadm T.L hLpos T.energyRatio (readOnMultiples T.L t f) hcl
  obtain ⟨q, hq1, hq2⟩ := hrow.flat_limit
  set Fm := constantPlaneCurvature X μ ν with hFmdef
  have hFm : IsAntisymmetricCurvature Fm := by
    intro a b
    rw [hFmdef, constantPlaneCurvature_eq]
    show planeUnitForm μ ν a b • X = - (planeUnitForm μ ν b a • X)
    rw [planeUnitForm_antisymm μ ν hμν a b]
    apply Subtype.ext
    show (-(planeUnitForm μ ν b a)) • (X : Quaternion ℝ) = -(planeUnitForm μ ν b a • (X : Quaternion ℝ))
    exact neg_smul _ _
  let A : Fin 4 → Fin 4 → imaginaryQuaternions := fun i j => (1 / 2 : ℝ) • Fm j i
  let B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions := fun c => ∑ ν', ((c.1 ν' : ℤ) : ℝ) • A c.2 ν'
  have hB : IsLinearPotential Fm B := by
    refine ⟨A, 0, fun x μ' => by simp [B], fun a b => ?_⟩
    show (1 / 2 : ℝ) • Fm a b - (1 / 2 : ℝ) • Fm b a = Fm a b
    rw [hFm b a]
    module
  have hB' : IsLinearPotential (curvatureAlong X (planeUnitForm μ ν)) B := by
    rw [← constantPlaneCurvature_eq]; exact hB
  have hlimit : ∀ c c' (Y Y' : imaginaryQuaternions),
      secondDerivLimitOnMultiples T.L (readOnMultiples T.L t f) c c' Y Y' = q c c' Y Y' := by
    intro c c' Y Y'
    refine tendsto_nhds_unique (hlim c c' Y Y') ((hq1 c c' Y Y').congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact (hsecond m c c' Y Y' hm).symm
  have hzero : ∑' cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      secondDerivLimitOnMultiples T.L (readOnMultiples T.L t f) cc.1 cc.2 (B cc.1) (B cc.2) = 0 := by
    simp only [hlimit]
    exact (hq2 Fm Fm B B hFm hFm hB hB).tsum_eq
  obtain ⟨γ₂, hγ₂, hw⟩ := hwide (planeUnitForm μ ν) (planeUnitForm_antisymm μ ν hμν) ε hε
  obtain ⟨γ₁, hγ₁, hrc⟩ := hchain T.a T.L T.chainParams T.σ T.decayRate T.E T.energyRatio t T.n₀
    (frameRadius x) f hd.one_le_a hd.odd_L hd.chain_admissible hd.σ_pos hrow
  have hev : ∀ᶠ n : ℕ in atTop, (64 ≤ n ∧ 2 ≤ n ∧ T.n₀ ≤ n) ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 < γ₁ ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤ 1 ∧
      2 * Real.pi * ((1 : ℕ) : ℝ) / (((n * T.L : ℕ) : ℝ)) ^ 2 < γ₂ ∧
      4 * Real.log (1 / (2 * Real.pi * ((1 : ℕ) : ℝ) / (((n * T.L : ℕ) : ℝ)) ^ 2)) ^ 2 + 4 <
        ((n * T.L : ℕ) : ℝ) := by
    have ht : Tendsto (fun n : ℕ => n * T.L) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hLpos) tendsto_id
    filter_upwards [eventually_large γ₁ hγ₁ (max 64 T.n₀), ht.eventually (eventually_large γ₂ hγ₂ 0)]
      with n h1 h2
    obtain ⟨a1, a2, a3, a4, _⟩ := h1
    obtain ⟨_, _, b3, _, b5⟩ := h2
    exact ⟨⟨le_trans (le_max_left _ _) a1, a2, le_trans (le_max_right _ _) a1⟩, a3, a4, b3, b5⟩
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hev
  refine ⟨n₁, fun n _ hn => ?_⟩
  obtain ⟨⟨h64, _, hnn⟩, hl1', hl2, hgam, hroom⟩ := hn₁ n hn
  have hl1 := hl1'.le
  have hnpos : 0 < n := by omega
  have hnL : T.n₀ ≤ n * T.L := le_trans hnn (Nat.le_mul_of_pos_right n hLpos)
  set F := torusFrame T.L t n with hF
  have hoddF : Odd F.blockSide := hd.odd_L
  have hMpos : 0 < n * T.L := Nat.mul_pos hnpos hLpos
  haveI : NeZero (n * T.L) := ⟨hMpos.ne'⟩
  have hM : ∀ i, F.period F.depth i = n * T.L := by
    intro i
    have : F.top - F.depth = 1 := by simp [BlockFrame.top]
    simp only [BlockFrame.period, this, pow_one]
    rfl
  have hMn : ∀ i, F.period F.top i = n := by
    intro i
    simp [BlockFrame.period]
    rfl
  set U := constantCurvatureChain F X μ ν 1 F.depth with hU
  set V := constantCurvatureChain F X μ ν 1 F.top with hV
  have hab := hlevel F X μ ν n 1 F.depth (n * T.L) hoddF (fun _ => rfl) hnpos hX hμν hl2
    (by simp [BlockFrame.top]) hM hMpos
  set γ' : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (((n * T.L : ℕ) : ℝ)) ^ 2 with hγ'
  have hγ'pos : 0 < γ' := by
    rw [hγ']
    have : (0 : ℝ) < ((n * T.L : ℕ) : ℝ) := by exact_mod_cast hMpos
    have hπ := Real.pi_pos
    simp only [Nat.cast_one, mul_one]
    positivity
  have hbound : ∀ y : F.Site F.depth, |subtractTrivial f F y U| ≤ ε * γ' ^ 2 := by
    intro y
    have h1 := hw γ' hγ'pos hgam (n * T.L) (Dvd.intro_left n rfl) hroom X (restrictToTorus (n * T.L) U) B hX
      hab hB' (toTorusSite (n * T.L) y)
    rw [hzero, mul_zero, sub_zero] at h1
    have h2 : centered (readOnMultiples T.L t f) (n * T.L) (toTorusSite (n * T.L) y)
        (restrictToTorus (n * T.L) U) = subtractTrivial f F y U :=
      hcentl n y U hnpos
    rw [h2] at h1
    exact h1
  have hflat : uniformField F F.top = constantCurvatureChain F X μ ν 0 F.top := by
    funext x i
    exact (hno F X μ ν F.top hoddF x i).symm
  have hflat' : constantCurvatureChain F X μ ν 0 F.depth = uniformField F F.depth := by
    funext x i
    exact hno F X μ ν F.depth hoddF x i
  have hzero₀ : (0 : ℝ) ≤ γ₁ := hγ₁.le
  have hrow0 : ∀ y : F.Site F.depth,
      centredExpansion true T.a T.chainParams.ρA (frameRadius x) f y 0 (uniformField F F.top) = 0 := by
    intro y
    rw [hflat]
    have := hrc X μ ν n 0 h64 hnL hX hμν (by simpa using hγ₁.le) y
    rw [this, hflat']
    unfold subtractTrivial
    ring
  set Y₀ : F.Cell := siteOfCoords _ fun k => (((0 : TorusSite n) k).cast : ℤ) with hY₀
  have hval : centered (densityOfTopFamily (torusStepParameters T g).side t (expansionAtFrameFamily T true x f)) n 0
      (constantCurvatureTop (torusStepParameters T g).side t n X μ ν) =
      ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y₀),
        subtractTrivial f F y U := by
    show cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) f Y₀ 0 (readAtLevel F F.top (restrictToTorus n V)) -
      cellCentredExpansion true T.a T.chainParams.ρA (frameRadius x) f Y₀ 0 (uniformField F F.top) = _
    rw [readAtLevel_restrictToTorus hMn]
    unfold cellCentredExpansion
    rw [Finset.sum_eq_zero (s := (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y₀))
      (f := fun y => centredExpansion true T.a T.chainParams.ρA (frameRadius x) f y 0 (uniformField F F.top))
      (fun y _ => hrow0 y), sub_zero]
    exact Finset.sum_congr rfl fun y _ => hrc X μ ν n 1 h64 hnL hX hμν hl1 y
  rw [hval]
  have hsum : |∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y₀),
      subtractTrivial f F y U| ≤ (T.L : ℝ) ^ 4 * (ε * γ' ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_card_nsmul _ _ _ fun y _ => hbound y).trans ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_sites_in_cell_le F hoddF n (fun _ => rfl) hnpos Y₀) (by positivity)
  refine hsum.trans (le_of_eq ?_)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hL' : (T.L : ℝ) ≠ 0 := by positivity
  rw [hγ']
  push_cast
  field_simp
  ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
