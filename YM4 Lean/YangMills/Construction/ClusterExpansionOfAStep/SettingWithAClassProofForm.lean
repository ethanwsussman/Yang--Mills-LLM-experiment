import YangMills.Construction.ClusterExpansionOfAStep.ClassBesideAFamily
import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.FineDistanceByBlocks
import YangMills.Construction.ClusterExpansionOfAStep.IntegralNearAClassIsBounded
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.MassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.NearBlocksAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCost
import YangMills.Construction.ClusterExpansionOfAStep.NearSitesOfAClass
import YangMills.Construction.ClusterExpansionOfAStep.SettingWithAClass
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensitiesNearAClass
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction.GasStep
open TorusFields TorusLumps StepSettings StepGas RenormalizationStepParameters StepCosts StepMarks BlockOffsets BlockPlaces TorusBalls
  ColdStepAtMirrorFrames BlockAverages ClusterExpansionOfAStep
theorem energy_ratio_arith {x a a₁ cE ch h ν b c k n Sa Z' Z S' S LNI K φB b₅ b₆ b₇ b₈ b₉ : ℝ}
    (hx : 0 ≤ x) (ha : 256 * ch ≤ a) (ha₁ : 256 * ch ≤ a₁) (hcE : 256 * ch ≤ cE) (hch : 0 ≤ ch)
    (hh : 0 ≤ h) (hν : 0 ≤ ν) (hb : 0 ≤ b) (hkb : k ≤ b) (hc : c ≤ h + ν) (hn : n = k + c)
    (h5 : Z' ≤ LNI + b₅)
    (hLNI : LNI ≤ K + (-(x * Sa) - x * (a / 4 * h) - x * (cE * b) + x * (a * h) + b₆ + φB + b₇))
    (h72 : -(x * Sa) - b₈ ≤ Z) (hfar : S' - S ≤ b₉)
    (hclasscost : b₅ + K + b₆ + b₇ + b₈ + b₉ ≤ 48 * ch * x * n) :
    Z' + S' ≤ φB + x * a * h + a₁ * x * ν - 16 * ch * x * n + (Z + S) := by
  have h1 : 64 * ch * n ≤ a / 4 * h + cE * b + a₁ * ν := by
    have e1 : 64 * ch * n ≤ 64 * ch * (b + h + ν) := by
      have : n ≤ b + h + ν := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e2 : 64 * ch * h ≤ a / 4 * h := mul_le_mul_of_nonneg_right (by linarith) hh
    have e3 : 64 * ch * b ≤ cE * b := mul_le_mul_of_nonneg_right (by linarith) hb
    have e4 : 64 * ch * ν ≤ a₁ * ν := mul_le_mul_of_nonneg_right (by linarith) hν
    nlinarith
  have h2 : x * (64 * ch * n) ≤ x * (a / 4 * h + cE * b + a₁ * ν) := mul_le_mul_of_nonneg_left h1 hx
  nlinarith
theorem sum_le_card_mul_of_exp_supDist {n : ℕ} [NeZero n] (c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A)
    (hball : ∀ (y : TorusSite n) (D : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ supDist Y y),
      Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤ A * Real.exp (-(c * D / 2)))
    (P Q : Finset (TorusSite n)) (hP : P.Nonempty) (D : ℕ) (f : TorusSite n → ℝ)
    (hf : ∀ Y ∈ Q, ∃ y ∈ P, D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y ∧ f Y ≤ Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y))) (hf0 : ∀ Y, 0 ≤ f Y) :
    ∑ Y ∈ Q, f Y ≤ (P.card : ℝ) * (A * Real.exp (-(c * D / 2))) := by
  classical
  calc ∑ Y ∈ Q, f Y
      ≤ ∑ Y ∈ Q, ∑ y ∈ P, (if D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y then Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) else 0) := by
        refine Finset.sum_le_sum fun Y hY => ?_
        obtain ⟨y, hy, hD, hle⟩ := hf Y hY
        have hnn : ∀ y' ∈ P, 0 ≤ (if D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y' then Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y')) else 0) := by
          intro y' _
          split_ifs
          · exact (Real.exp_pos _).le
          · exact le_rfl
        refine le_trans ?_ (Finset.single_le_sum hnn hy)
        rw [if_pos hD]
        exact hle
    _ ≤ ∑ Y : TorusSite n, ∑ y ∈ P, (if D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y then Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun Y _ _ => ?_
        refine Finset.sum_nonneg fun y _ => ?_
        split_ifs
        · exact (Real.exp_pos _).le
        · exact le_rfl
    _ = ∑ y ∈ P, ∑ Y : TorusSite n, (if D ≤ _root_.YangMills.Construction.TorusFields.supDist Y y then Real.exp (-(c * _root_.YangMills.Construction.TorusFields.supDist Y y)) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _y ∈ P, A * Real.exp (-(c * D / 2)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.sum_filter]
        exact hball y D
    _ = (P.card : ℝ) * (A * Real.exp (-(c * D / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
section Assembly
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem two_mul_supDist_le_extent (x y : TorusSite n) : 2 * _root_.YangMills.Construction.TorusFields.supDist x y ≤ n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
theorem ground_region_eq_restSet (G : GasGround R n) (hG : G.IsAdmissibleGround) (s : ChartSetting R n)
    (hV : s.coarse = G.coarse) (c : SettingCore R n) (hc : c.core = G.cut) : G.region = s.restSet c := by
  classical
  unfold ChartSetting.restSet
  rw [hV, hc]
  rcases hG with h | h
  · rw [h.region_eq, h.cut_eq]
    ext z
    simp [mem_thickening]
  · rw [h.region_eq, h.cut_eq]
    congr 2
    ext z
    simp only [Finset.mem_inter]
    exact ⟨fun hz => ⟨(mem_thickening (2 * R.nextRange) _ z).mpr ⟨z, hz, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩, hz⟩,
      fun hz => hz.2⟩
theorem ground_deviation_ge_of_mark_ne (G : GasGround R n) (hρ : 0 < R.ballRadius)
    (hp : IsCutoff R.ballRadius R.barrierFn) {W W' : TorusField (n * R.params.side)}
    {b : TorusBond (n * R.params.side)} (hne : 1 - bondMark R G.coarse W b ≠ 0)
    (hch : chartCoord R.params G.coarse W' b = chartCoord R.params G.coarse W b) :
    5 * R.ballRadius / 8 ≤
      ‖(frameDeviation R.params R.anchorRadius R.depth R.frameReach G.coarse W' b : ℍ[ℝ])‖ := by
  by_contra hlt
  push Not at hlt
  apply hne
  have h1 : ‖((chartCoord R.params G.coarse W b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b : imaginaryQuaternions) : ℍ[ℝ])‖ <
      5 * R.ballRadius / 8 := by
    have : ((frameDeviation R.params R.anchorRadius R.depth R.frameReach G.coarse W' b :
          imaginaryQuaternions) : ℍ[ℝ]) =
        ((chartCoord R.params G.coarse W b : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach G.coarse b : imaginaryQuaternions) : ℍ[ℝ]) := by
      unfold frameDeviation
      rw [hch]
      rfl
    rwa [this] at hlt
  unfold bondMark cutoffFactor
  rw [if_pos (by linarith), hp.vanish_small _ (norm_nonneg _) h1.le]
  simp
end Assembly
theorem card_sitesInBlocks_singleton {L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (hodd : Odd L) (Y : TorusSite n) :
    (sitesInBlocks L ({Y} : Finset (TorusSite n))).card = L ^ 4 := by
  have h := sum_sitesInBlocks (M := ℕ) (n := n) (L := L) hodd Y (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h, card_centredCube hodd]
theorem card_freeNear_le {R : StepSetup} {n : ℕ} [NeZero n] (hodd : Odd R.params.side) (s : ChartSetting R n)
    (N : Finset (TorusSite n)) :
    (s.freeNear N).card ≤ 4 * R.params.side ^ 4 * N.card := by
  classical
  have h1 : (s.freeNear N).card ≤ ((N.biUnion fun Y => sitesInBlocks R.params.side ({Y} : Finset (TorusSite n))) ×ˢ
      (Finset.univ : Finset (Fin 4))).card := by
    refine Finset.card_le_card_of_injOn (fun b => b.1) (fun b hb => ?_) ?_
    · have hN : bondBlock (R := R) b.1 ∈ N := (Finset.mem_filter.mp hb).2
      refine Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨_, hN, ?_⟩, Finset.mem_univ _⟩
      simp [sitesInBlocks, bondBlock]
    · intro a _ b _ hab
      exact Subtype.ext hab
  have h2 : (N.biUnion fun Y => sitesInBlocks R.params.side ({Y} : Finset (TorusSite n))).card ≤
      N.card * R.params.side ^ 4 := by
    refine Finset.card_biUnion_le_card_mul _ _ _ fun Y _ => ?_
    exact (card_sitesInBlocks_singleton hodd Y).le
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  nlinarith
theorem coordNorm_zero_eq : coordNorm 0 = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.coordNorm_zero <;> assumption
theorem div_side_le_supDist_of_not_mem_blocksNear {R : StepSetup} {n : ℕ} [NeZero n]
    (hFD : FineDistanceLeBlockDistance) {θ : GasSupport R n} {y Y : TorusSite n} (hy : y ∈ θ.core)
    (hY : Y ∉ blocksNear R.params.side R.range θ.sites) : R.range / R.params.side ≤ _root_.YangMills.Construction.TorusFields.supDist y Y := by
  classical
  obtain ⟨p, hp, z, hz, hpz⟩ := GasSupport.mem_core.mp hy
  have hq : parentBlock R.params.side
      (blockSite Y (fun _ => 0 : BlockOffset R.params.side) : TorusSite (n * R.params.side)) = Y :=
    parentBlock_blockSite Y _
  set q : TorusSite (n * R.params.side) := blockSite Y (fun _ => 0 : BlockOffset R.params.side) with hqdef
  have hfar : 5 * R.range < _root_.YangMills.Construction.TorusFields.supDist q z := by
    by_contra hle
    push Not at hle
    apply hY
    unfold blocksNear
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, q,
      Finset.mem_inter.mpr ⟨?_, (mem_thickening _ _ _).mpr ⟨z, hz, hle⟩⟩⟩
    simp [sitesInBlocks, hq]
  have h1 : R.range < _root_.YangMills.Construction.TorusFields.supDist p q := by
    have := _root_.YangMills.Construction.TorusFields.supDist_triangle q p z
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm q p] at this
    omega
  have h2 := hFD n R.params.side p q
  rw [hp, hq] at h2
  have h3 : R.range < R.params.side * (_root_.YangMills.Construction.TorusFields.supDist y Y + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h4 : R.range / R.params.side < _root_.YangMills.Construction.TorusFields.supDist y Y + 1 := Nat.div_lt_of_lt_mul h3
  omega
theorem mem_coreBonds_of_mem {R : StepSetup} {n : ℕ} [NeZero n] {θ : GasSupport R n}
    {b : TorusBond (n * R.params.side)} (hb : b ∈ θ.1) (hr : 1 ≤ R.range) : b ∈ θ.coreBonds := by
  classical
  have hs : b.1 ∈ θ.sites := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, GasSupport.parentBlock_mem_core hs,
    GasSupport.mem_core.mpr ⟨_, rfl, b.1, hs, ?_⟩⟩
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  have := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le b.1 b.2
  omega
theorem error_total_le {C5 CN C7 K₀ rr lx Nc nn X6 X9 Cb x10 chx kfl : ℝ} (hC5 : 0 ≤ C5) (hCN : 0 ≤ CN)
    (hC7 : 0 ≤ C7) (hK₀ : 0 ≤ K₀) (hr : 1 ≤ rr) (hl : 1 ≤ lx) (hNc : 0 ≤ Nc) (hnn : 0 ≤ nn) (hX6 : X6 ≤ 1)
    (hX9 : X9 ≤ 1) (hkf : kfl ≤ K₀ * Nc) (hNcn : Nc ≤ (29 * rr) ^ 4 * nn)
    (hCb : (C5 + CN + C7 + K₀ + 2) * 29 ^ 4 ≤ Cb) (h8 : Cb * rr ^ 8 * lx ≤ x10) (h10 : x10 ≤ chx) :
    C5 * rr ^ 4 * lx * Nc + kfl + X6 * Nc + CN * rr ^ 4 * lx * Nc + C7 * lx * Nc + X9 * Nc ≤ 48 * chx * nn := by
  have hP : 1 ≤ rr ^ 4 * lx := by
    have : 1 ≤ rr ^ 4 := one_le_pow₀ hr
    nlinarith
  have hr4 : 1 ≤ rr ^ 4 := one_le_pow₀ hr
  have h1 : C5 * rr ^ 4 * lx * Nc + kfl + X6 * Nc + CN * rr ^ 4 * lx * Nc + C7 * lx * Nc + X9 * Nc ≤
      (C5 + CN + C7 + K₀ + 2) * (rr ^ 4 * lx) * Nc := by
    have e1 : K₀ * Nc ≤ K₀ * (rr ^ 4 * lx) * Nc :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK₀ hP) hNc
    have e2 : X6 * Nc ≤ 1 * (rr ^ 4 * lx) * Nc :=
      mul_le_mul_of_nonneg_right (by linarith) hNc
    have e3 : X9 * Nc ≤ 1 * (rr ^ 4 * lx) * Nc :=
      mul_le_mul_of_nonneg_right (by linarith) hNc
    have e4 : C7 * lx * Nc ≤ C7 * (rr ^ 4 * lx) * Nc := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC7) hNc
      nlinarith
    nlinarith
  have hq0 : 0 ≤ (C5 + CN + C7 + K₀ + 2) * (rr ^ 4 * lx) := by positivity
  have h2 : (C5 + CN + C7 + K₀ + 2) * (rr ^ 4 * lx) * Nc ≤
      (C5 + CN + C7 + K₀ + 2) * (rr ^ 4 * lx) * ((29 * rr) ^ 4 * nn) := mul_le_mul_of_nonneg_left hNcn hq0
  have h4 : ((C5 + CN + C7 + K₀ + 2) * 29 ^ 4) * rr ^ 8 * lx * nn ≤ Cb * rr ^ 8 * lx * nn := by
    have : 0 ≤ rr ^ 8 * lx * nn := by positivity
    nlinarith
  have hchx : 0 ≤ chx := by
    have : 0 ≤ Cb * rr ^ 8 * lx := by
      have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
      positivity
    linarith
  have h5 : Cb * rr ^ 8 * lx * nn ≤ chx * nn := mul_le_mul_of_nonneg_right (h8.trans h10) hnn
  have h6 : chx * nn ≤ 48 * chx * nn := by
    have : 0 ≤ chx * nn := by positivity
    nlinarith
  linarith
theorem sum_activity_le_of_near_far {ι : Type} [Fintype ι] [DecidableEq ι] {N : Finset ι} {ζ' ζ₀ aY : ι → ℝ}
    {x a a₁ cE ch h ν b k c n LNI K φB b₅ b₆ b₇ e₈ b₉ : ℝ}
    (hx : 0 ≤ x) (ha : 256 * ch ≤ a) (ha₁ : 256 * ch ≤ a₁) (hcE : 256 * ch ≤ cE) (hch : 0 ≤ ch)
    (hh : 0 ≤ h) (hν : 0 ≤ ν) (hb : 0 ≤ b) (hkb : k ≤ b) (hc : c ≤ h + ν) (hn : n = k + c)
    (h5 : ∑ Y ∈ N, ζ' Y ≤ LNI + b₅)
    (hLNI : LNI ≤ K + (-(x * ∑ Y ∈ N, aY Y) - x * (a / 4 * h) - x * (cE * b) + x * (a * h) + b₆ + φB + b₇))
    (h72 : ∀ Y ∈ N, |ζ₀ Y + x * aY Y| ≤ e₈) (hfar : ∑ Y ∈ Finset.univ \ N, |ζ' Y - ζ₀ Y| ≤ b₉)
    (hclasscost : b₅ + K + b₆ + b₇ + e₈ * N.card + b₉ ≤ 48 * ch * x * n) :
    ∑ Y, ζ' Y ≤ φB + x * a * h + a₁ * x * ν - 16 * ch * x * n + ∑ Y, ζ₀ Y := by
  have e1 : ∑ Y, ζ' Y = ∑ Y ∈ N, ζ' Y + ∑ Y ∈ Finset.univ \ N, ζ' Y := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ N)]
  have e2 : ∑ Y, ζ₀ Y = ∑ Y ∈ N, ζ₀ Y + ∑ Y ∈ Finset.univ \ N, ζ₀ Y := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ N)]
  have h72' : -(x * ∑ Y ∈ N, aY Y) - e₈ * N.card ≤ ∑ Y ∈ N, ζ₀ Y := by
    have : ∑ Y ∈ N, (-(x * aY Y) - e₈) ≤ ∑ Y ∈ N, ζ₀ Y := Finset.sum_le_sum fun Y hY => by
      have := abs_le.mp (h72 Y hY)
      linarith [this.1]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at this
    linarith
  have hfar' : ∑ Y ∈ Finset.univ \ N, ζ' Y - ∑ Y ∈ Finset.univ \ N, ζ₀ Y ≤ b₉ := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_le_sum fun Y _ => le_abs_self _).trans hfar
  rw [e1, e2]
  exact energy_ratio_arith hx ha ha₁ hcE hch hh hν hb hkb hc hn h5 hLNI h72' hfar' hclasscost
section Generic
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem log_localIntegral_le (hIB : LocalIntegralLeBallVolume) (hρ : 0 < R.ballRadius)
    (hp : IsCutoff R.ballRadius R.barrierFn) (s : ChartSetting R n) (N : Finset (TorusSite n))
    (hNIpos : 0 < s.localIntegral N) (M : ℝ)
    (hM : ∀ η : FreeCoords s.free, s.InBalls η → -(s.localPotential N fun b => η b.1) ≤ M) :
    Real.log (s.localIntegral N) ≤ ((s.freeNear N).card : ℝ) * Real.log (liePointBallVolume R.ballRadius) + M := by
  classical
  have hU : ∀ ζ : s.freeNear N → EuclideanSpace ℝ (Fin 3), (∀ b, coordNorm (ζ b) < R.ballRadius) →
      -(s.localPotential N ζ) ≤ M := by
    intro ζ hζ
    have hη : s.InBalls (s.extendByZero N ζ) := by
      intro b
      unfold ChartSetting.extendByZero
      by_cases hb : b ∈ s.freeNear N
      · simp only [dif_pos hb]
        exact (hζ _).le
      · simp only [dif_neg hb]
        show coordNorm 0 ≤ R.ballRadius
        rw [coordNorm_zero_eq]
        exact hρ.le
    have h1 := hM _ hη
    have hfn : (fun b : s.freeNear N => s.extendByZero N ζ b.1) = ζ := by
      funext b
      unfold ChartSetting.extendByZero
      simp only [dif_pos b.2]
    rwa [hfn] at h1
  have hIBs := hIB R n s N M hρ hp hU
  have hpos2 := lt_of_lt_of_le hNIpos hIBs
  have hVk : liePointBallVolume R.ballRadius ^ (s.freeNear N).card ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hpos2
    exact lt_irrefl _ hpos2
  have hLNI := Real.log_le_log hNIpos hIBs
  rwa [Real.log_mul hVk (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at hLNI
theorem neg_potential_le_arith {x cost U Sa t A B o φ b₇ Ah : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t)
    (h1 : -U ≤ -(x * cost) + φ + b₇) (h2 : x * (Sa + t + A + B) - o ≤ x * (cost + Ah)) :
    -U ≤ -(x * Sa) - x * A - x * B + x * Ah + o + φ + b₇ := by
  have h3 := mul_nonneg hx ht
  have e1 : x * (Sa + t + A + B) = x * Sa + x * t + x * A + x * B := by ring
  have e2 : x * (cost + Ah) = x * cost + x * Ah := by ring
  rw [e1, e2] at h2
  linarith
theorem sum_abs_off_blocksNear_le (hFD : FineDistanceLeBlockDistance) (rt A4 : ℝ) (hrt : 0 < rt) (hA4 : 0 ≤ A4)
    (hball : ∀ (y : TorusSite n) (D : ℕ), ∑ Y ∈ Finset.univ.filter (fun Y : TorusSite n => D ≤ supDist Y y),
      Real.exp (-(rt / 2 ^ 5 * _root_.YangMills.Construction.TorusFields.supDist Y y)) ≤ A4 * Real.exp (-(rt / 2 ^ 5 * D / 2)))
    (θ : GasSupport R n) (hcore : θ.core.Nonempty) (f : TorusSite n → ℝ) (hL8 : 2 ^ 8 * R.params.side ≤ R.range)
    (hf : ∀ (Y : TorusSite n) (m : ℕ), Y ∉ blocksNear R.params.side R.range θ.sites →
      (∀ y ∈ θ.core, m + 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y Y) →
      2 * m + 2 < n → (R.range : ℝ) / (4 * R.params.side) ≤ m → |f Y| ≤ Real.exp (-(rt * m / 2 ^ 5))) :
    ∑ Y ∈ Finset.univ \ blocksNear R.params.side R.range θ.sites, |f Y| ≤
      A4 * Real.exp (-(rt / 2 ^ 5 * ((R.range / R.params.side : ℕ) : ℝ) / 2)) * Real.exp (2 * (rt / 2 ^ 5)) *
        ((blocksNear R.params.side R.range θ.sites).card : ℝ) := by
  classical
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hc₄ : 0 < rt / 2 ^ 5 := by positivity
  have hD256 : 2 ^ 8 ≤ R.range / R.params.side := (Nat.le_div_iff_mul_le hLpos).mpr hL8
  have hLR : (0 : ℝ) < (R.params.side : ℝ) := by exact_mod_cast hLpos
  have hDlt : (R.range : ℝ) < (R.params.side : ℝ) * (((R.range / R.params.side : ℕ) : ℝ) + 1) := by
    have h := Nat.lt_mul_div_succ R.range hLpos
    have h' : (R.range : ℝ) < ((R.params.side * (R.range / R.params.side + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hcN : θ.core.card ≤ (blocksNear R.params.side R.range θ.sites).card := by
    refine Finset.card_le_card fun y' hy' => ?_
    obtain ⟨p, hp', z, hz, hpz⟩ := GasSupport.mem_core.mp hy'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, p,
      Finset.mem_inter.mpr ⟨?_, (mem_thickening _ _ _).mpr ⟨z, hz, by omega⟩⟩⟩
    simp [sitesInBlocks, hp']
  have hg : ∀ Y ∈ Finset.univ \ blocksNear R.params.side R.range θ.sites, ∃ y' ∈ θ.core,
      R.range / R.params.side ≤ _root_.YangMills.Construction.TorusFields.supDist Y y' ∧
      |f Y| * Real.exp (-(2 * (rt / 2 ^ 5))) ≤ Real.exp (-(rt / 2 ^ 5 * _root_.YangMills.Construction.TorusFields.supDist Y y')) := by
    intro Y hY
    have hYN : Y ∉ blocksNear R.params.side R.range θ.sites := (Finset.mem_sdiff.mp hY).2
    obtain ⟨y₁, hy₁, hmin⟩ := Finset.exists_min_image θ.core (fun y' => _root_.YangMills.Construction.TorusFields.supDist y' Y) hcore
    have hfar1 := div_side_le_supDist_of_not_mem_blocksNear hFD hy₁ hYN
    have hhalf := two_mul_supDist_le_extent y₁ Y
    obtain ⟨m, hm⟩ : ∃ m, _root_.YangMills.Construction.TorusFields.supDist y₁ Y = m + 2 := ⟨_root_.YangMills.Construction.TorusFields.supDist y₁ Y - 2, by omega⟩
    have hreal : (R.range : ℝ) / (4 * R.params.side) ≤ m := by
      rw [div_le_iff₀ (by positivity)]
      have hmD : (((R.range / R.params.side : ℕ) : ℝ)) ≤ (m : ℝ) + 2 := by
        exact_mod_cast (by omega : R.range / R.params.side ≤ m + 2)
      have hD8 : (2 ^ 8 : ℝ) ≤ ((R.range / R.params.side : ℕ) : ℝ) := by exact_mod_cast hD256
      nlinarith
    have hL := hf Y m hYN (fun y' hy' => by
      have : _root_.YangMills.Construction.TorusFields.supDist y₁ Y ≤ _root_.YangMills.Construction.TorusFields.supDist y' Y := hmin y' hy'
      omega) (by omega) hreal
    refine ⟨y₁, hy₁, by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact hfar1, ?_⟩
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm Y y₁, hm]
    calc |f Y| * Real.exp (-(2 * (rt / 2 ^ 5)))
        ≤ Real.exp (-(rt * m / 2 ^ 5)) * Real.exp (-(2 * (rt / 2 ^ 5))) :=
          mul_le_mul_of_nonneg_right hL (Real.exp_pos _).le
      _ = Real.exp (-(rt / 2 ^ 5 * ((m + 2 : ℕ) : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
  have hs := sum_le_card_mul_of_exp_supDist (rt / 2 ^ 5) hc₄ A4 hA4 hball θ.core
    (Finset.univ \ blocksNear R.params.side R.range θ.sites) hcore (R.range / R.params.side)
    (fun Y => |f Y| * Real.exp (-(2 * (rt / 2 ^ 5)))) hg (fun Y => by positivity)
  rw [← Finset.sum_mul] at hs
  have hE2 : Real.exp (-(2 * (rt / 2 ^ 5))) * Real.exp (2 * (rt / 2 ^ 5)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hs2 := mul_le_mul_of_nonneg_right hs (Real.exp_pos (2 * (rt / 2 ^ 5))).le
  rw [mul_assoc, hE2, mul_one] at hs2
  have hcN' : (θ.core.card : ℝ) ≤ ((blocksNear R.params.side R.range θ.sites).card : ℝ) := by exact_mod_cast hcN
  have hpos3 : 0 ≤ A4 * Real.exp (-(rt / 2 ^ 5 * ((R.range / R.params.side : ℕ) : ℝ) / 2)) *
      Real.exp (2 * (rt / 2 ^ 5)) := by
    positivity
  nlinarith
theorem small_terms_le_one {T : ParameterAssignment} {Cb cs c6 C6 A4 A₁ : ℝ} (x : ℝ) (hx1 : 1 ≤ x) (r D : ℕ) (L : ℕ)
    (hLpos : 0 < L) (hfl : T.FloorConditions Cb cs x) (hrr : r = clusterRange x) (hCb3 : C6 ≤ Cb) (hCb4 : 1 ≤ Cb)
    (hCb5 : A₁ + 1 ≤ Cb) (hcs1 : cs ≤ c6) (hcs2 : cs ≤ T.rt / 2 ^ 5 / (2 * L)) (hrt : 0 < T.rt) (hA4 : 0 ≤ A4)
    (hA₁ : A₁ = A4 * Real.exp (2 * (T.rt / 2 ^ 5)) * Real.exp (T.rt / 2 ^ 5 / 2))
    (hDlt : (r : ℝ) < (L : ℝ) * ((D : ℝ) + 1)) :
    x ^ C6 * Real.exp (-(c6 * r)) ≤ 1 ∧
      A4 * Real.exp (-(T.rt / 2 ^ 5 * (D : ℝ) / 2)) * Real.exp (2 * (T.rt / 2 ^ 5)) ≤ 1 := by
  subst hrr
  have hCb0 : 0 ≤ Cb := by linarith
  have hLT : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hE : Cb * x ^ Cb * Real.exp (-(cs * clusterRange x)) ≤ 1 := by
    have h1 := hfl.stretched_tail.1
    have h2 : Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) (1 / 200 : ℝ)
      linarith
    exact h1.trans h2
  have hxCb : 1 ≤ x ^ Cb := Real.one_le_rpow hx1 hCb0
  have hEs : x ^ Cb * Real.exp (-(cs * clusterRange x)) ≤ 1 := by
    have h0 : 0 ≤ x ^ Cb * Real.exp (-(cs * clusterRange x)) := by positivity
    nlinarith
  have hr0 : (0 : ℝ) ≤ (clusterRange x : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hEs
    refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx1 hCb3) ?_ (Real.exp_pos _).le (by positivity)
    rw [Real.exp_le_exp]
    nlinarith
  · have hc4 : 0 < T.rt / 2 ^ 5 := by positivity
    have h1 : Real.exp (-(T.rt / 2 ^ 5 * (D : ℝ) / 2)) ≤
        Real.exp (T.rt / 2 ^ 5 / 2) * Real.exp (-(cs * clusterRange x)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h2 : cs * clusterRange x ≤ T.rt / 2 ^ 5 / (2 * L) * clusterRange x :=
        mul_le_mul_of_nonneg_right hcs2 hr0
      have h3 : T.rt / 2 ^ 5 / (2 * L) * clusterRange x ≤ T.rt / 2 ^ 5 / 2 * ((D : ℝ) + 1) := by
        have e : T.rt / 2 ^ 5 / (2 * L) * clusterRange x = T.rt / 2 ^ 5 / 2 * ((clusterRange x : ℝ) / L) := by
          field_simp
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_iff₀ hLT]
        linarith
      nlinarith
    have hA₁0 : 0 ≤ A₁ := by
      rw [hA₁]
      positivity
    have h4 : A4 * Real.exp (-(T.rt / 2 ^ 5 * (D : ℝ) / 2)) * Real.exp (2 * (T.rt / 2 ^ 5)) ≤
        A₁ * Real.exp (-(cs * clusterRange x)) := by
      rw [hA₁]
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA4 (Real.exp_pos (2 * (T.rt / 2 ^ 5))).le)
      nlinarith
    have h5 : A₁ * Real.exp (-(cs * clusterRange x)) ≤ Cb * x ^ Cb * Real.exp (-(cs * clusterRange x)) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      nlinarith
    linarith
theorem sum_activity_insertClass_le {R : StepSetup} {n : ℕ} [NeZero n] (s' s₀ : ChartSetting R n)
    (N : Finset (TorusSite n)) (aY : TorusSite n → ℝ) (lam : ℝ)
    {a a₁ cE ch h ν b k c nn φB b₅ b₆ b₇ e₈ b₉ K t A Ah : ℝ}
    (hx : 0 ≤ R.coupling) (ha : 256 * ch ≤ a) (ha₁ : 256 * ch ≤ a₁) (hcE : 256 * ch ≤ cE) (hch : 0 ≤ ch)
    (hh : 0 ≤ h) (hν : 0 ≤ ν) (hb : 0 ≤ b) (hkb : k ≤ b) (hc : c ≤ h + ν) (hn : nn = k + c) (ht : 0 ≤ t)
    (eA : A = a / 4 * h) (eAh : Ah = a * h)
    (hNIlog : ∀ M, (∀ η : FreeCoords s'.free, s'.InBalls η → -(s'.localPotential N fun b => η b.1) ≤ M) →
      Real.log (s'.localIntegral N) ≤ K + M)
    (h5 : ∑ Y ∈ N, s'.blockActivity lam Y ≤ Real.log (s'.localIntegral N) + b₅)
    (hNPs : ∀ η : FreeCoords s'.free, s'.InBalls η →
      -(s'.localPotential N fun b => η b.1) ≤ -(R.coupling * s'.energyNear N η) + φB + b₇)
    (hL6 : ∀ η : FreeCoords s'.free, s'.InBalls η →
      R.coupling * (∑ Y ∈ N, aY Y + t + A + cE * b) - b₆ ≤ R.coupling * (s'.energyNear N η + Ah))
    (h72 : ∀ Y ∈ N, |s₀.blockActivity lam Y + R.coupling * aY Y| ≤ e₈)
    (hfar : ∑ Y ∈ Finset.univ \ N, |s'.blockActivity lam Y - s₀.blockActivity lam Y| ≤ b₉)
    (hclasscost : b₅ + K + b₆ + b₇ + e₈ * N.card + b₉ ≤ 48 * ch * R.coupling * nn) :
    ∑ Y, s'.blockActivity lam Y ≤
      φB + R.coupling * a * h + a₁ * R.coupling * ν - 16 * ch * R.coupling * nn + ∑ Y, s₀.blockActivity lam Y := by
  subst eA eAh
  have hLNI := hNIlog _ fun η hη => neg_potential_le_arith hx ht (hNPs η hη) (hL6 η hη)
  exact sum_activity_le_of_near_far (ζ' := fun Y => s'.blockActivity lam Y) (ζ₀ := fun Y => s₀.blockActivity lam Y)
    (aY := aY) hx ha ha₁ hcE hch hh hν hb hkb hc hn h5 hLNI h72 hfar hclasscost
theorem settingMass_le_of_sum_activity {R : StepSetup} {n : ℕ} [NeZero n] (s' s₀ : ChartSetting R n) (lam E : ℝ)
    (hlog' : Real.log (∫ η, s'.cutoffProduct η * Real.exp (-s'.potential η)) = ∑ Y, s'.blockActivity lam Y)
    (hlog₀ : Real.log (∫ η, s₀.cutoffProduct η * Real.exp (-s₀.potential η)) = ∑ Y, s₀.blockActivity lam Y)
    (hI' : 0 < ∫ η, s'.cutoffProduct η * Real.exp (-s'.potential η))
    (hI₀ : 0 < ∫ η, s₀.cutoffProduct η * Real.exp (-s₀.potential η))
    (hm' : settingMass s' = ENNReal.ofReal (∫ η, s'.cutoffProduct η * Real.exp (-s'.potential η)))
    (hm₀ : settingMass s₀ = ENNReal.ofReal (∫ η, s₀.cutoffProduct η * Real.exp (-s₀.potential η)))
    (hle : ∑ Y, s'.blockActivity lam Y ≤ E + ∑ Y, s₀.blockActivity lam Y) :
    settingMass s' ≤ ENNReal.ofReal (Real.exp E) * settingMass s₀ := by
  rw [hm', hm₀, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_log hI', hlog', ← Real.exp_log hI₀, hlog₀, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hle
end Generic
set_option maxHeartbeats 4000000 in
theorem insertClassMassBound_proof (hD : LogIntegralEqSumActivity) (hL4 : StepLocality.DensityLocality)
    (hL5 : DensitySumNearComponentsBound) (h72 : ActivityNearLevelShare)
    (hL6 : StepEnergy.EnergyNearPieceBound) (hNP : NearPotentialLeEnergy)
    (hIB : LocalIntegralLeBallVolume) (hMass : SettingMassEqIntegral)
    (hCl : ComponentBesideFamily) (hNB : NearBlocksCardBound)
    (hCov : NearSitesLeLumpsAndLength) (hFD : FineDistanceLeBlockDistance)
    (hFl : StepFloors.EventuallyFloorConditions) : InsertClassMassBound := by
  classical
  obtain ⟨r1, p1, hD⟩ := hD
  obtain ⟨r2, p2, hL4⟩ := hL4
  obtain ⟨r3, p3, hL5⟩ := hL5
  obtain ⟨r4, p4, h72⟩ := h72
  obtain ⟨r5, p5, hMass⟩ := hMass
  refine ⟨fun c => min (r1 c) (min (r2 c) (min (r3 c) (min (r4 c) (r5 c)))),
    fun c => lt_min (p1 c) (lt_min (p2 c) (lt_min (p3 c) (lt_min (p4 c) (p5 c)))), fun T hT hrt => ?_⟩
  have t1 : T.rt ≤ r1 T.toChainParameters := hrt.trans (min_le_left _ _)
  have hrt' := hrt.trans (min_le_right _ _)
  have t2 : T.rt ≤ r2 T.toChainParameters := hrt'.trans (min_le_left _ _)
  have hrt'' := hrt'.trans (min_le_right _ _)
  have t3 : T.rt ≤ r3 T.toChainParameters := hrt''.trans (min_le_left _ _)
  have hrt''' := hrt''.trans (min_le_right _ _)
  have t4 : T.rt ≤ r4 T.toChainParameters := hrt'''.trans (min_le_left _ _)
  have t5 : T.rt ≤ r5 T.toChainParameters := hrt'''.trans (min_le_right _ _)
  obtain ⟨yD, hD⟩ := hD T hT t1
  obtain ⟨y4, hL4⟩ := hL4 T hT t2
  obtain ⟨C5, y5, hC5, hL5⟩ := hL5 T hT t3
  obtain ⟨C7, y7, hC7, h72⟩ := h72 T hT t4
  obtain ⟨yM, hMass⟩ := hMass T hT t5
  obtain ⟨C6, c6, hc6, y6, hL6⟩ := hL6 T hT
  obtain ⟨CN, yN, hCN, hNP⟩ := hNP T hT
  have hrtpos : 0 < T.rt := hT.rt_pos
  have hLT : (0 : ℝ) < T.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T.side)
  have hc₄pos : 0 < T.rt / 2 ^ 5 := by positivity
  obtain ⟨A4, hA4, hball⟩ := exists_sum_exp_supDist_le (T.rt / 2 ^ 5) hc₄pos
  obtain ⟨cs, hcspos, hcs1, hcs2⟩ : ∃ cs : ℝ, 0 < cs ∧ cs ≤ c6 ∧ cs ≤ T.rt / 2 ^ 5 / (2 * T.side) :=
    ⟨min c6 (T.rt / 2 ^ 5 / (2 * T.side)), lt_min hc6 (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 4 * (T.side : ℝ) ^ 4 * |Real.log (liePointBallVolume T.ballRadius)| :=
    ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = A4 * Real.exp (2 * (T.rt / 2 ^ 5)) * Real.exp (T.rt / 2 ^ 5 / 2) := ⟨_, rfl⟩
  obtain ⟨Cb, hCb1, hCb2, hCb3, hCb4, hCb5⟩ : ∃ Cb : ℝ, (C5 + CN + C7 + K₀ + 2) * 29 ^ 4 ≤ Cb ∧
      2 ^ 8 * (T.side : ℝ) + 1 ≤ Cb ∧ C6 ≤ Cb ∧ 1 ≤ Cb ∧ A₁ + 1 ≤ Cb :=
    ⟨max (max ((C5 + CN + C7 + K₀ + 2) * 29 ^ 4) (2 ^ 8 * (T.side : ℝ) + 1)) (max (max C6 1) (A₁ + 1)),
      le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _),
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨yF, hyF⟩ := hFl T hT Cb cs (by linarith) hcspos
  refine ⟨max (max (max (max yD y4) (max y5 y7)) (max (max yM y6) yN)) (max yF T.floorMin),
    fun y hy R hR n _ G σ i s hG hadm hset hσi hap hset' hbad => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨⟨⟨hyD, hy4⟩, hy5, hy7⟩, ⟨hyM, hy6⟩, hyN⟩, hyFl, hyT⟩ := hy
  have hfl := hyF R.coupling (hyFl.trans hR.le_coupling)
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hyT
  have hLeq : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hneq : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hκ : R.params.κ = T.κ := by rw [hR.params_eq]; rfl
  have hκ₁ : R.params.κ₁ = T.κ₁ := by rw [hR.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hρeq : R.ballRadius = T.ballRadius := by
    unfold StepSetup.ballRadius ParameterAssignment.ballRadius
    rw [hσ]
  have hp : IsCutoff R.ballRadius R.barrierFn := by
    rw [hρeq, hR.barrierFn_eq]
    exact hT.cut
  have hρ : 0 < R.ballRadius := by
    unfold StepSetup.ballRadius
    have := hfit.σ_pos
    positivity
  have hr6 : Cb ≤ (R.range : ℝ) := hfl.range_ge
  have hr8 : 2 ^ 8 * R.params.side ≤ R.range := by
    have h1 : ((2 ^ 8 * T.side + 1 : ℕ) : ℝ) ≤ (R.range : ℝ) := by
      push_cast
      linarith
    have h2 : 2 ^ 8 * T.side + 1 ≤ R.range := by exact_mod_cast h1
    rw [hLeq]
    omega
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne R.params.side)
  have hodd : Odd R.params.side := hfit.L_odd
  have h2L : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have hn : T.n₀ ≤ n := by
    rw [← hneq]
    rcases hG with h | h
    · exact h.n₀_le
    · have h2 := h.isBlockSide.2
      nlinarith
  have hn' : R.params.n₀ ≤ n := hneq ▸ hn
  have hx3 : (3 : ℝ) ≤ R.coupling := by
    have h1 : (2 : ℝ) ^ 1600 ≤ T.floorMin := le_max_right _ _
    have h2 : (3 : ℝ) ≤ 2 ^ 1600 :=
      le_trans (by norm_num : (3 : ℝ) ≤ 2 ^ 2) (pow_le_pow_right₀ (by norm_num) (by norm_num))
    exact le_trans h2 (le_trans h1 (le_trans hyT hR.le_coupling))
  have hfam : G.IsGasFamily (G.familyOf σ) := by
    refine ⟨fun θ h => ?_, fun θ θ' h h' hne => ?_⟩
    · obtain ⟨j, rfl, -⟩ := G.exists_spin_of_occupies h
      exact j.2
    · obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
      obtain ⟨j', rfl, hj'⟩ := G.exists_spin_of_occupies h'
      rcases hadm j j' (fun e => hne (congrArg Subtype.val e)) with e | e | e
      · exact absurd e hj
      · exact absurd e hj'
      · exact e
  have hapθ : ∀ θ', (G.familyOf σ).Occupies θ' → i.1.FarApart θ' := by
    intro θ' h
    obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
    rcases hap j with e | e
    · exact absurd e hj
    · exact e
  obtain ⟨hst₀, hmk₀, -, hnew⟩ := hCl R n G (G.familyOf σ) hr8 hρ hodd h2L hG hfam
  obtain ⟨hoff, hfam', hagree, hchart⟩ := hnew i.1 s i.2 hapθ hset
  obtain ⟨hst', hmk', hcls', -⟩ := hCl R n G ((G.familyOf σ).insertClass i.1 s) hr8 hρ hodd h2L hG hfam'
  have hself : ((G.familyOf σ).insertClass i.1 s).Occupies i.1 := GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  obtain ⟨⟨𝒦, h𝒦, hK⟩, hpiece, hbeside, hbadin, hbadimg, hlump⟩ := hcls' i.1 hself
  have hr1 : 1 ≤ R.range := by omega
  have hlog' := hD y hyD R hR n hn _ hset'
  have hlog₀ := hD y hyD R hR n hn _ hset
  obtain ⟨-, hI'pos, hm'⟩ := hMass y hyM R hR n hn _ hset'
  obtain ⟨-, hIpos, hm₀⟩ := hMass y hyM R hR n hn _ hset
  obtain ⟨hNIpos, hNIabs⟩ := hL5 y hy5 R hR n hn _ _ hset' hst' (hmk' hset') 𝒦 h𝒦
  have hNPs := hNP y hyN R hR n hn _ _ hset' hst' 𝒦 h𝒦 i.1.2
    (fun z hz => by
      show z ∈ G.recordedSites ∪ ((G.familyOf σ).insertClass i.1 s).sites
      rw [GasFamily.sites_insertClass]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hz))
    (fun z hz => by
      rw [hK]
      exact Finset.mem_union_right _ hz)
    (by rw [hK]; exact hbeside)
  rw [hK] at hNIpos hNIabs hNPs
  have hzero : (G.settingOf ((G.familyOf σ).insertClass i.1 s)).InBalls 0 := fun b => by
    show coordNorm 0 ≤ R.ballRadius
    rw [coordNorm_zero_eq]
    exact hρ.le
  have hcovA := (hCov R.params (n * R.params.side) R.range i.1.2
    ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).field 0) hr1).1
  have hlumps : hotLumpsWithin R.params ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).field 0) i.1.2 =
      (G.settingOf ((G.familyOf σ).insertClass i.1 s)).lumpsInPiece i.1.sites := by
    unfold hotLumpsWithin ChartSetting.lumpsInPiece
    rw [← hset'.hotLumps_eq 0 hzero]
    ext l
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans Finset.subset_union_right⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hlump hset' l h1 h2⟩
  have hbk : badBlockCount R.params.side i.1 ≤
      (badBlocksOff R.params.side (G.familyCore ((G.familyOf σ).insertClass i.1 s)).badBonds
        (G.familyCore ((G.familyOf σ).insertClass i.1 s)).core i.1.sites).card := by
    unfold badBlockCount
    exact Finset.card_le_card hbadimg
  have htop : (G.settingOf (G.familyOf σ)).region =
      (G.settingOf ((G.familyOf σ).insertClass i.1 s)).restSet (G.familyCore ((G.familyOf σ).insertClass i.1 s)) :=
    ground_region_eq_restSet G hG _ rfl _ rfl
  have hcore : i.1.core.Nonempty := by
    obtain ⟨z, hz⟩ := i.2.isCluster.1
    exact ⟨_, GasSupport.parentBlock_mem_core hz⟩
  have hxpos : 0 ≤ R.coupling := by linarith
  have hx1 : (1 : ℝ) ≤ R.coupling := by linarith
  have hlx1 : 1 ≤ Real.log R.coupling := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hrpos : (1 : ℝ) ≤ (R.range : ℝ) := by exact_mod_cast hr1
  have hDlt : (R.range : ℝ) < (T.side : ℝ) * (((R.range / R.params.side : ℕ) : ℝ) + 1) := by
    have h := Nat.lt_mul_div_succ R.range hLpos
    have h' : (R.range : ℝ) < ((R.params.side * (R.range / R.params.side + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hLTr : ((R.params.side : ℕ) : ℝ) = (T.side : ℝ) := by rw [hLeq]
    rwa [hLTr] at h'
  obtain ⟨hX6, hX9⟩ := small_terms_le_one (T := T) R.coupling hx1 R.range (R.range / R.params.side) T.side
    (Nat.pos_of_ne_zero (NeZero.ne T.side)) hfl rfl hCb3 hCb4 hCb5 hcs1 hcs2 hrtpos hA4 hA₁ hDlt
  have hfarsum := sum_abs_off_blocksNear_le hFD T.rt A4 hrtpos hA4 (hball n) i.1 hcore
    (fun Y => (G.settingOf ((G.familyOf σ).insertClass i.1 s)).blockActivity T.lam Y -
      (G.settingOf (G.familyOf σ)).blockActivity T.lam Y) hr8
    (fun Y m _ h1 h2 h3 => (hL4 y hy4 R hR n n hn hn _ _ Y Y m hset' hset).1 h3 (hagree Y m h1 h2))
  have hNcn : (((blocksNear R.params.side R.range i.1.sites).card : ℕ) : ℝ) ≤
      (29 * (R.range : ℝ)) ^ 4 * (supportUnitCount R.params.side R.range i.1 : ℝ) := by
    have h1 := hNB R.params.side R.range n i.1
    have h2 : 20 * R.range / R.params.side + 9 ≤ 29 * R.range := by
      have := Nat.div_le_self (20 * R.range) R.params.side
      omega
    have h3 : (blocksNear R.params.side R.range i.1.sites).card ≤
        (29 * R.range) ^ 4 * supportUnitCount R.params.side R.range i.1 :=
      h1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 4))
    exact_mod_cast h3
  have hkf : (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).freeNear
      (blocksNear R.params.side R.range i.1.sites)).card : ℝ) * Real.log (liePointBallVolume R.ballRadius) ≤
      K₀ * ((blocksNear R.params.side R.range i.1.sites).card : ℝ) := by
    have h1 := card_freeNear_le hodd (G.settingOf ((G.familyOf σ).insertClass i.1 s))
      (blocksNear R.params.side R.range i.1.sites)
    have h2 : (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).freeNear
        (blocksNear R.params.side R.range i.1.sites)).card : ℝ) ≤
        4 * (T.side : ℝ) ^ 4 * ((blocksNear R.params.side R.range i.1.sites).card : ℝ) := by
      have hLTr : ((R.params.side : ℕ) : ℝ) = (T.side : ℝ) := by rw [hLeq]
      have h1' : (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).freeNear
          (blocksNear R.params.side R.range i.1.sites)).card : ℝ) ≤
          4 * ((R.params.side : ℕ) : ℝ) ^ 4 * ((blocksNear R.params.side R.range i.1.sites).card : ℝ) := by
        exact_mod_cast h1
      rwa [hLTr] at h1'
    rw [hK₀, hρeq]
    have h3 := le_abs_self (Real.log (liePointBallVolume T.ballRadius))
    have h4 := abs_nonneg (Real.log (liePointBallVolume T.ballRadius))
    calc (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).freeNear
          (blocksNear R.params.side R.range i.1.sites)).card : ℝ) * Real.log (liePointBallVolume T.ballRadius)
        ≤ (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).freeNear
          (blocksNear R.params.side R.range i.1.sites)).card : ℝ) * |Real.log (liePointBallVolume T.ballRadius)| :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ ≤ (4 * (T.side : ℝ) ^ 4 * ((blocksNear R.params.side R.range i.1.sites).card : ℝ)) *
            |Real.log (liePointBallVolume T.ballRadius)| :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = _ := by ring
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    positivity
  have h10 : R.coupling ^ (1 / 10 : ℝ) ≤ T.gasRate * R.coupling :=
    (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)).trans hfl.log_powers.2.2
  have hclasscost := error_total_le hC5.le hCN.le hC7.le hK₀0 hrpos hlx1 (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hX6 hX9 hkf hNcn hCb1 hfl.log_powers.1 h10
  have hsub256 : 256 * T.gasRate = min T.cE (min (T.κ * T.threshold ^ 2) (T.κ₁ * T.threshold ^ 2)) := by
    unfold ParameterAssignment.gasRate
    ring
  have ha : 256 * T.gasRate ≤ R.params.κ * R.params.threshold ^ 2 := by
    rw [hsub256, hκ, hσ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ha₁ : 256 * T.gasRate ≤ R.params.κ₁ * R.params.threshold ^ 2 := by
    rw [hsub256, hκ₁, hσ]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hcE : 256 * T.gasRate ≤ T.cE := by
    rw [hsub256]
    exact min_le_left _ _
  have hch : 0 ≤ T.gasRate := by
    have h1 : 0 ≤ T.cE := hT.cE_pos.le
    have h2 : 0 ≤ T.κ * T.threshold ^ 2 := mul_nonneg hT.κ_pos.le (by positivity)
    have h3 : 0 ≤ T.κ₁ * T.threshold ^ 2 := by
      have hh := hfit.κ₁_pos
      rw [hκ₁] at hh
      exact mul_nonneg hh.le (by positivity)
    have : 0 ≤ 256 * T.gasRate := by
      rw [hsub256]
      exact le_min h1 (le_min h2 h3)
    linarith
  have hsum := sum_activity_insertClass_le (G.settingOf ((G.familyOf σ).insertClass i.1 s)) (G.settingOf (G.familyOf σ))
    (blocksNear R.params.side R.range i.1.sites)
    (fun Y => levelShare R.params.coupling R.params.side (R.depth + 1) (G.settingOf (G.familyOf σ)).region Y G.coarse)
    T.lam
    (a := R.params.κ * R.params.threshold ^ 2) (a₁ := R.params.κ₁ * R.params.threshold ^ 2) (cE := T.cE)
    (ch := T.gasRate)
    (h := ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).lumpsInPiece i.1.sites).card)
    (ν := excessLength R.params R.range i.1.2 ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).field 0))
    (b := (badBlocksOff R.params.side (G.familyCore ((G.familyOf σ).insertClass i.1 s)).badBonds
      (G.familyCore ((G.familyOf σ).insertClass i.1 s)).core i.1.sites).card)
    (k := badBlockCount R.params.side i.1)
    (c := ballCoverNumber (4 * R.range) i.1.2) (nn := supportUnitCount R.params.side R.range i.1)
    (t := 6 * R.params.κ * R.params.threshold ^ 2 *
      (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).coarseLumpsInPiece
        (G.familyCore ((G.familyOf σ).insertClass i.1 s)) i.1.sites).card : ℝ))
    (A := R.params.κ / 4 * R.params.threshold ^ 2 *
      (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).lumpsInPiece i.1.sites).card : ℝ))
    (Ah := R.params.κ * R.params.threshold ^ 2 *
      (((G.settingOf ((G.familyOf σ).insertClass i.1 s)).lumpsInPiece i.1.sites).card : ℝ))
    hxpos ha ha₁ hcE hch (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hbk)
    (by
      have h1 : ballCoverNumber (4 * R.range) i.1.2 ≤
          ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).lumpsInPiece i.1.sites).card +
          excessLength R.params R.range i.1.2 ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).field 0) := by
        rw [← hlumps]
        exact hcovA
      exact_mod_cast h1)
    (by
      unfold supportUnitCount
      push_cast
      ring)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hfit.κ_pos.le) (by positivity)) (Nat.cast_nonneg _))
    (by ring) rfl
    (fun M hM => log_localIntegral_le hIB hρ hp _ _ hNIpos M hM)
    (sub_le_iff_le_add'.mp (abs_le.mp hNIabs).2)
    hNPs
    (fun η hη => by
      have h2 := hL6 y hy6 R hR n _ (G.familyCore ((G.familyOf σ).insertClass i.1 s)) i.1.sites η hn' hset' hst'
        (hmk' hset') hpiece hη
        (fun b hb hb1 => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp (i.2.bad_subset_free (hbadin b hb hb1))).1).1,
          ground_deviation_ge_of_mark_ne G hρ hp (hbad b (hbadin b hb hb1))
            (hchart b (mem_coreBonds_of_mem (hbadin b hb hb1) hr1))⟩)
      rw [← htop] at h2
      exact h2)
    (fun Y hY => ((h72 y hy7 R hR n hn _ hset).1 (G.familyCore (G.familyOf σ)) Y hst₀ (hmk₀ hset) (hoff Y hY)).1)
    hfarsum
    (by
      have e : 48 * T.gasRate * R.coupling * (supportUnitCount R.params.side R.range i.1 : ℝ) =
          48 * (T.gasRate * R.coupling) * (supportUnitCount R.params.side R.range i.1 : ℝ) := by
        ring
      rw [e]
      exact hclasscost)
  refine settingMass_le_of_sum_activity _ _ T.lam _ hlog' hlog₀ hI'pos hIpos hm' hm₀ ?_
  unfold ChartSetting.classExponent
  rw [hlumps]
  have e : (G.settingOf ((G.familyOf σ).insertClass i.1 s)).densityNear i.1.2 =
      ∑ z ∈ nearSites R.range i.1.2, R.siteDensity (n * R.params.side) z
        ((G.settingOf ((G.familyOf σ).insertClass i.1 s)).field 0)
        (G.settingOf ((G.familyOf σ).insertClass i.1 s)).support
        (G.settingOf ((G.familyOf σ).insertClass i.1 s)).labelling := rfl
  rw [e]
  linarith
end YangMills.Construction.GasStep
end
