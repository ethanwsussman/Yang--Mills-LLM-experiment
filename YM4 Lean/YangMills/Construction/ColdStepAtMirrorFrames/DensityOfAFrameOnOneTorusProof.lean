import YangMills.Construction.ColdStepAtMirrorFrames.ChangeAlongASegment
import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DensityOfAFrameOnOneTorusForm
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeThroughCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation YangMills.Construction.Calculus
namespace YangMills.Construction.ColdStepAtMirrorFrames
open FrameCurves
variable {F : BlockFrame}
namespace FrameDensity
theorem weightedNorm_frameGapCurve_deriv_le (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z)
    (β β₀ ω Sg : ℝ) (hβ₀ : 0 ≤ β₀) (hω : 0 ≤ ω) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (Y : F.Cell)
    (hSg : ∑ b ∈ fineBonds F, Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) ≤ Sg)
    (h1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a ρ m b) V)
    (h2 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame false a ρ m b) V)
    {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (e : Fin p → Fin k) (hp : 0 < p)
    (hd : ∀ b ∈ chordBonds (finiteCells F), ‖bondDeriv (frameGap a ρ m b) V (c ∘ e) (X ∘ e)‖ ≤
      ω * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) (c ∘ e)))) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist Y (directionCell (chartDirections F n)))))
      (iteratedFDeriv ℝ p (frameGapCurve a ρ m V c X) 0 (fun l => Pi.single (e l) 1)) ≤
      3 * (ω * Sg) * Real.exp (-(β₀ * bondListDistance Y (c ∘ e))) := by
  have hf : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ
      (fun τ : Fin k → ℝ => frameGap a ρ m b (leftTranslate (bondSpread c X τ) V)) 0 :=
    fun b hb => (h2 b hb k c X).sub (h1 b hb k c X)
  have e1 := iteratedFDeriv_chartCoordinates (fun x i τ => frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V))
    (fun _ _ _ => (0 : imaginaryQuaternions)) hf (fun _ _ => analyticAt_const) (fun l : Fin p => (Pi.single (e l) 1 : Fin k → ℝ))
  unfold frameGapCurve
  rw [e1]
  refine (_root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist Y z))) (fun z => (Real.exp_pos _).le) _ _).trans ?_
  have hdw : ∀ b ∈ chordBonds (finiteCells F), ‖iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
      frameGap a ρ m (b.1, b.2) (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single (e l) 1)‖ ≤ ω * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) (c ∘ e))) := by
    intro b hb
    have hc : ContDiffAt ℝ p (fun τ : Fin k → ℝ => frameGap a ρ m b (leftTranslate (bondSpread c X τ) V)) 0 :=
      (hf b hb).contDiffAt
    have e2 := iteratedFDeriv_single_eq_bondDeriv (frameGap a ρ m b) V c X e hc
    refine le_trans (le_of_eq ?_) (hd b hb)
    exact congrArg norm e2
  have h3 := sum_chordBonds_weighted_le hsym htri β β₀ ω Sg Y (c ∘ e) (fun x i => iteratedFDeriv ℝ p (fun τ : Fin k → ℝ =>
      frameGap a ρ m (x, i) (leftTranslate (bondSpread c X τ) V)) 0
        (fun l => Pi.single (e l) 1)) hβ₀ hω hSg hdw
  have hz : ∑ b : ↥(innerBonds (finiteCells F) F.top), ‖iteratedFDeriv ℝ p (fun _ : Fin k → ℝ => (0 : imaginaryQuaternions)) 0
      (fun l => Pi.single (e l) 1)‖ * Real.exp (-(β * cellSupDist Y b.1.1)) = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [iteratedFDeriv_const_of_ne (by omega)]
    simp
  rw [hz, add_zero]
  exact mul_le_mul_of_nonneg_left h3 (by norm_num) |>.trans (le_of_eq (by ring))
theorem weightedNorm_chartCoordinates_frameGap_le (hsym : ∀ x y : F.Cell, cellSupDist x y = cellSupDist y x)
    (htri : ∀ x y z : F.Cell, cellSupDist x z ≤ cellSupDist x y + cellSupDist y z)
    (β β₀ ω Sg : ℝ) (hβ₀ : 0 ≤ β₀) (hω : 0 ≤ ω) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) (Y : F.Cell)
    (hSg : ∑ b ∈ fineBonds F, Real.exp (-((β - β₀) * cellSupDist (enclosingCell b.1) Y)) ≤ Sg)
    (hgap : ∀ b ∈ chordBonds (finiteCells F), ‖frameGap a ρ m b V‖ ≤ ω) :
    _root_.YangMills.Construction.Calculus.weightedNorm (fun n => Real.exp (-(β * cellSupDist Y (directionCell (chartDirections F n)))))
      (chartCoordinates (fun x i => frameGap a ρ m (x, i) V) (fun _ _ => 0)) ≤ 3 * (ω * Sg) := by
  refine (_root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.weightedNorm_chartCoordinates_le (fun z => Real.exp (-(β * cellSupDist Y z))) (fun z => (Real.exp_pos _).le) _ _).trans ?_
  have hdw : ∀ b ∈ chordBonds (finiteCells F), ‖frameGap a ρ m (b.1, b.2) V‖ ≤
      ω * Real.exp (-(β₀ * bondListDistance (enclosingCell b.1) (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) := by
    intro b hb
    simpa [bondListDistance] using hgap b hb
  have h3 := sum_chordBonds_weighted_le hsym htri β β₀ ω Sg Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
    (fun x i => frameGap a ρ m (x, i) V) hβ₀ hω hSg hdw
  have hz : ∑ b : ↥(innerBonds (finiteCells F) F.top), ‖(0 : imaginaryQuaternions)‖ * Real.exp (-(β * cellSupDist Y b.1.1)) = 0 := by
    simp
  rw [hz, add_zero]
  have h4 : bondListDistance Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by simp [bondListDistance]
  rw [h4] at h3
  simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h3
  exact mul_le_mul_of_nonneg_left h3 (by norm_num)
def partMaxDist (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (I : Finset (Fin k)) : ℕ :=
  I.sup fun l => cellSupDist Y (c l).1
theorem partMaxDist_image (Y : F.Cell) {k p : ℕ} (c : Fin k → F.Site F.top × Fin 4) (e : Fin p → Fin k) :
    partMaxDist Y c (Finset.univ.image e) = bondListDistance Y (c ∘ e) := by
  classical
  unfold partMaxDist bondListDistance
  rw [Finset.sup_image]
  rfl
theorem prod_exp_partMaxDist_le (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (P : OrderedFinpartition k) :
    ∏ i, Real.exp (-(β₀ * partMaxDist Y c (Finset.univ.image (P.emb i)))) ≤ Real.exp (-(β₀ * bondListDistance Y c)) := by
  classical
  have hle : ∀ i, Real.exp (-(β₀ * partMaxDist Y c (Finset.univ.image (P.emb i)))) ≤ 1 := fun i => by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ partMaxDist Y c (Finset.univ.image (P.emb i)) := by positivity
    nlinarith
  by_cases hD : bondListDistance Y c = 0
  · rw [hD]
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero]
    exact Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ => hle i
  · have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply hD
      unfold bondListDistance
      rw [hcon]
      simp
    obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun l => cellSupDist Y (c l).1)
    have hD' : bondListDistance Y c = cellSupDist Y (c l₀).1 := hl₀
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, l₀ ∈ Finset.univ.image (P.emb i₀) :=
      ⟨P.index l₀, Finset.mem_image.mpr ⟨P.invEmbedding l₀, Finset.mem_univ _, P.emb_invEmbedding l₀⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    have h1 : Real.exp (-(β₀ * partMaxDist Y c (Finset.univ.image (P.emb i₀)))) ≤ Real.exp (-(β₀ * bondListDistance Y c)) := by
      apply Real.exp_le_exp.mpr
      have h2 : cellSupDist Y (c l₀).1 ≤ partMaxDist Y c (Finset.univ.image (P.emb i₀)) :=
        Finset.le_sup (f := fun l => cellSupDist Y (c l).1) hi₀
      have h3 : (bondListDistance Y c : ℝ) ≤ partMaxDist Y c (Finset.univ.image (P.emb i₀)) := by
        rw [hD']
        exact_mod_cast h2
      nlinarith
    have h4 : ∏ i ∈ Finset.univ.erase i₀, Real.exp (-(β₀ * partMaxDist Y c (Finset.univ.image (P.emb i)))) ≤ 1 :=
      Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ => hle i
    have h5 := Real.exp_pos (-(β₀ * bondListDistance Y c))
    calc _ ≤ Real.exp (-(β₀ * bondListDistance Y c)) * 1 :=
          mul_le_mul h1 h4 (Finset.prod_nonneg fun i _ => (Real.exp_pos _).le) h5.le
      _ = _ := mul_one _
theorem iteratedFDeriv_neg_mul_sub {k : ℕ} (x : ℝ) (u v : (Fin k → ℝ) → ℝ) (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0)
    (vs : Fin k → Fin k → ℝ) :
    iteratedFDeriv ℝ k (fun τ => -x * (u τ - v τ)) 0 vs =
      -x * (iteratedFDeriv ℝ k u 0 vs - iteratedFDeriv ℝ k v 0 vs) := by
  have e : (fun τ => -x * (u τ - v τ)) = (-x) • u + x • v := by
    funext τ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hu' : ContDiffAt ℝ k u 0 := hu.contDiffAt
  have hv' : ContDiffAt ℝ k v 0 := hv.contDiffAt
  have h1 : ContDiffAt ℝ k ((-x) • u) 0 := hu'.const_smul (-x)
  have h2 : ContDiffAt ℝ k (x • v) 0 := hv'.const_smul x
  rw [e, iteratedFDeriv_add_apply h1 h2, iteratedFDeriv_const_smul_apply hu', iteratedFDeriv_const_smul_apply hv']
  change (-x) * iteratedFDeriv ℝ k u 0 vs + x * iteratedFDeriv ℝ k v 0 vs = _
  ring
end FrameDensity
open FrameDensity in
theorem frameDensityOnTorus_holds (hKer : CellEnergyKernelBound)
    (hCE : CellEnergyInCoordinates) (hLC : CellEnergyShareAtMinimizingChart)
    (hCh : IteratedDerivCompSegmentDiffBound) (hTh : IteratedDerivCompBound)
    (hCG : CubicTorusCellGeometry) : FrameDensityOnTorus := by
  classical
  intro a L c ha hL hL40 hc C hC
  obtain ⟨Ck, hCk, hker⟩ := hKer a L c ha hL hL40 hc
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hs₀ : 0 < c.s₀ := hc.classical.1.2.2.1
  have hlet : 2 ^ 6 * c.δ₂ ≤ c.δ₁ := hc.inequalities.2.1
  have hσA : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  have hκ₂ : 0 ≤ c.κ₂ := by
    have := hc.classical.1.2.2.2.2.1
    nlinarith
  have hKk : ∀ k, 0 < c.Kk k := hc.classical.1.2.2.2.2.2.2.2
  have hβ₀ : 0 ≤ c.δ₂ / 4 := by positivity
  have hββ : c.δ₂ / 4 ≤ c.δ₁ / 4 := by nlinarith
  have hrate : 0 < c.δ₁ / 4 - c.δ₂ / 4 := by nlinarith
  obtain ⟨Cg, hCg0, hCg⟩ := hCG.2 _ hrate
  have hgeo : ∀ k : ℕ, ∃ Sk : ℝ, 0 < Sk ∧ ∀ F : BlockFrame, Odd F.blockSide → IsLargeCubicTorus F → ∀ z : F.Cell,
      ∑ b ∈ fineBonds F, Real.exp (-((c.δ₁ / (k + 1)) * cellSupDist (enclosingCell b.1) z)) ≤ Sk * (F.blockSide : ℝ) ^ 4 := fun k =>
    hCG.2 _ (by positivity)
  choose Sk hSk0 hSk using hgeo
  obtain ⟨Sg, hSg⟩ : ∃ Sg, Sg = Cg * (L : ℝ) ^ 4 := ⟨_, rfl⟩
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    positivity
  obtain ⟨Kq, hKq⟩ : ∃ Kq : ℕ → ℝ, Kq = fun k => ∑ l ∈ Finset.range (k + 2), Ck l := ⟨_, rfl⟩
  have hKq0 : ∀ k, 0 ≤ Kq k := fun k => by
    rw [hKq]
    exact Finset.sum_nonneg fun l _ => (hCk l).le
  have hKql : ∀ k l, l ≤ k + 1 → Ck l ≤ Kq k := fun k l hl => by
    rw [hKq]
    exact Finset.single_le_sum (f := Ck) (fun i _ => (hCk i).le) (Finset.mem_range.mpr (by omega))
  obtain ⟨Mk, hMk⟩ : ∃ Mk : ℕ → ℝ, Mk = fun k => ∑ p ∈ Finset.range (k + 1), 16 ^ p * c.Kk p := ⟨_, rfl⟩
  have hMk0 : ∀ k, 0 ≤ Mk k := fun k => by
    rw [hMk]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hKk l).le
  have hMkl : ∀ k p, p ≤ k → 16 ^ p * c.Kk p ≤ Mk k := fun k p hp => by
    rw [hMk]
    exact Finset.single_le_sum (f := fun p => (16 : ℝ) ^ p * c.Kk p) (fun i _ => mul_nonneg (by positivity) (hKk i).le)
      (Finset.mem_range.mpr (by omega))
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁, C₁ = 3 * (C * Sg + 1) + 3 * Sg + 1 := ⟨_, rfl⟩
  have hC₁ : 1 ≤ C₁ := by
    rw [hC₁d]
    have : 0 ≤ C * Sg := by positivity
    nlinarith
  obtain ⟨Ch, hChd⟩ : ∃ Ch : ℕ → ℝ, Ch = fun k => 3 * (Mk k * (Sk k * (L : ℝ) ^ 4) + 1) + 1 := ⟨_, rfl⟩
  have hCh1 : ∀ k, 1 ≤ Ch k := fun k => by
    rw [hChd]
    have := hMk0 k
    have := hSk0 k
    have : 0 ≤ Mk k * (Sk k * (L : ℝ) ^ 4) := by positivity
    nlinarith
  obtain ⟨B0, hB0⟩ : ∃ B0, B0 = ∑ k ∈ Finset.range 4, segmentConstant k (Kq 3) C₁ + 1 := ⟨_, rfl⟩
  have hseg0 : ∀ k, 0 ≤ segmentConstant k (Kq 3) C₁ := fun k => by
    unfold segmentConstant
    have := hKq0 3
    positivity
  have hB00 : 0 < B0 := by
    rw [hB0]
    have : 0 ≤ ∑ k ∈ Finset.range 4, segmentConstant k (Kq 3) C₁ := Finset.sum_nonneg fun k _ => hseg0 k
    linarith
  have hsegB : ∀ k, k ≤ 3 → segmentConstant k (Kq 3) C₁ ≤ B0 := fun k hk => by
    rw [hB0]
    have := Finset.single_le_sum (f := fun k => segmentConstant k (Kq 3) C₁) (fun i _ => hseg0 i)
      (Finset.mem_range.mpr (show k < 4 by omega))
    linarith
  have hthr0 : ∀ k, 0 ≤ compositionConstant k (Kq k) (Ch k) := fun k => by
    unfold compositionConstant
    have := hKq0 k
    have := hCh1 k
    positivity
  refine ⟨fun k => B0 + compositionConstant k (Kq k) (Ch k) + c.N k, fun k => ?_, ?_⟩
  · have := hc.positivity.2.2.2.2.2.1 k
    have := hthr0 k
    simp only
    linarith
  intro x σ ω s m F V hx hs hss hω0 hω1 hch hV hfr Y
  have hFL : F.blockSide = L := hch.1
  have hodd : Odd F.blockSide := by rw [hFL]; exact hL
  obtain ⟨n₁, hn₁, hside⟩ := hch.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside i]
    omega
  obtain ⟨hsym', htri', hcsym, hctri, -⟩ := hCG.1 F hodd hch.2
  have hana1 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a c.ρA m b) V :=
    (hfr.small true).analytic
  have hana0 : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame false a c.ρA m b) V :=
    (hfr.small false).analytic
  have hleastAt : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' →
      minimalCellShare a (finiteCells F) Y V' = cellEnergyShare a Y (fun z i => stepFrame true a c.ρA m (z, i) V') V' := by
    intro V' hV'
    have h1 := (hc.classical.2 F s V' hch hs hss hV').1
    have h2 := (hc.estimates F s V' hch hs (hss.trans hσA) hV').cellShares.2.2.1
    have h3 := hLC F a c.ρA _ V' (by linarith) hodd hs2 h1 h2 Y
    rw [← h3]
    rfl
  have hSgY : ∑ b ∈ fineBonds F, Real.exp (-((c.δ₁ / 4 - c.δ₂ / 4) * cellSupDist (enclosingCell b.1) Y)) ≤ Sg := by
    have := hCg F hodd hch.2 Y
    rw [hFL] at this
    rw [hSg]
    exact this
  have hga : ∀ θ ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ (cellEnergyAtFrame true a c.ρA m Y V)
      (θ • chartCoordinates (fun x i => frameGap a c.ρA m (x, i) V) (fun _ _ => 0)) := fun θ hθ =>
    analyticAt_cellEnergyAtFrame hCE hodd hs2 a c.ρA m Y V θ (hker F _ V hch (hfr.between θ hθ) Y _ (chartDirections F)).1
  have hform : ∀ {k : ℕ} (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (fun τ => frameDensity false a c.ρA x m Y (leftTranslate (bondSpread e X τ) V)) =ᶠ[𝓝 0] fun τ => -x *
        (cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ + (1 : ℝ) • frameGapCurve a c.ρA m V e X τ) -
          cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ)) := by
    intro k e X
    filter_upwards [eventually_isSmallCurvature hs2 e X hV] with τ hτ
    unfold frameDensity
    rw [cellEnergyAtFrame_frameCurve_add_gap hCE hodd hs2, cellEnergyAtFrame_frameCurve hCE hodd hs2, hleastAt _ hτ]
  have hu : ∀ {k : ℕ} (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AnalyticAt ℝ (fun τ =>
      cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ + (1 : ℝ) • frameGapCurve a c.ρA m V e X τ)) 0 := by
    intro k e X
    have hsm : AnalyticAt ℝ (fun τ => (1 : ℝ) • frameGapCurve a c.ρA m V e X τ) 0 := by
      simp only [one_smul]
      exact analyticAt_frameGapCurve hana1 hana0 e X
    refine AnalyticAt.comp_of_eq (hga 1 ⟨zero_le_one, le_rfl⟩) ((analyticAt_frameCurve hana1 e X).add hsm) ?_
    change frameCurve true a c.ρA m V e X 0 + (1 : ℝ) • frameGapCurve a c.ρA m V e X 0 = _
    rw [frameCurve_zero, frameGapCurve_zero, zero_add]
  have hv : ∀ {k : ℕ} (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), AnalyticAt ℝ (fun τ =>
      cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ)) 0 := by
    intro k e X
    refine AnalyticAt.comp_of_eq (hga 0 ⟨le_rfl, zero_le_one⟩) (analyticAt_frameCurve hana1 e X) ?_
    rw [frameCurve_zero, zero_smul]
  refine ⟨fun k e X => ?_, fun k e X hk hX => ?_, fun k e X hk hX => ?_⟩
  · exact (analyticAt_const.mul ((hu e X).sub (hv e X))).congr (hform e X).symm
  · have hbound := hCh (chartDimension F) k (cellEnergyAtFrame true a c.ρA m Y V) (frameCurve true a c.ρA m V e X)
      (frameGapCurve a c.ρA m V e X) (fun n => Real.exp (-(c.δ₁ / 4 * cellSupDist Y (directionCell (chartDirections F n)))))
      (Kq 3) C₁ ω 1 (Real.exp (-(c.δ₂ / 4 * bondListDistance Y e)))
      (fun I => Real.exp (-(c.δ₂ / 4 * partMaxDist Y e I))) (fun n => (Real.exp_pos _).le) (frameCurve_zero _ _ _ _ _ _ _)
      (analyticAt_frameCurve hana1 e X) (analyticAt_frameGapCurve hana1 hana0 e X)
      (fun θ hθ => by
        rw [frameGapCurve_zero]
        exact hga θ hθ)
      (fun θ hθ l h1 h2 r => by
        rw [frameGapCurve_zero]
        refine abs_iteratedFDeriv_le_prod a Y _ V (funext fun z => cellEnergyAtFrame_smul_add hCE hodd hs2 a c.ρA m Y V θ z) c.δ₁ (c.δ₁ / 4) (Kq 3)
          (by positivity) ?_ (hKq0 3) (hker F _ V hch (hfr.between θ hθ) Y _ (chartDirections F)).1 (fun q hq => ?_) r
        · have hl : (l : ℝ) ≤ 4 := by exact_mod_cast (show l ≤ 4 by omega)
          nlinarith
        · exact ((hker F _ V hch (hfr.between θ hθ) Y l q).2 h1 hq).trans
            (mul_le_mul_of_nonneg_right (hKql 3 l (by omega)) (Real.exp_pos _).le))
      (fun p e' hp hinj => by
        have hpk : p ≤ k := by simpa using Fintype.card_le_of_injective e' hinj
        have h := _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.weightedNorm_iteratedFDeriv_frameCurve_le hcsym hctri hs2 (c.δ₁ / 4) (c.δ₂ / 4) C Sg hβ₀ hββ (by linarith) true a c.ρA m V Y hSgY
          hana1 e X hX e' hp (fun b hb => (hfr.small true).deriv_decay b hb p (e ∘ e') (X ∘ e') hp (by omega) (fun l => hX _))
        rw [partMaxDist_image]
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        rw [hC₁d]
        linarith)
      (fun p e' hp hinj => by
        have hpk : p ≤ k := by simpa using Fintype.card_le_of_injective e' hinj
        have h := _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameDensity.weightedNorm_frameGapCurve_deriv_le hcsym hctri (c.δ₁ / 4) (c.δ₂ / 4) ω Sg hβ₀ hω0 a c.ρA m V Y hSgY hana1 hana0 e X e' hp
          (fun b hb => hfr.gap_decay b hb p (e ∘ e') (X ∘ e') hp (by omega) (fun l => hX _))
        rw [partMaxDist_image]
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        have : 3 * Sg ≤ C₁ := by
          rw [hC₁d]
          have : 0 ≤ C * Sg := by positivity
          linarith
        nlinarith)
      (by
        rw [frameGapCurve_zero]
        refine (_root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameDensity.weightedNorm_chartCoordinates_frameGap_le hcsym hctri (c.δ₁ / 4) (c.δ₂ / 4) ω Sg hβ₀ hω0 a c.ρA m V Y hSgY hfr.gap).trans ?_
        have : 3 * Sg ≤ C₁ := by
          rw [hC₁d]
          have : 0 ≤ C * Sg := by positivity
          linarith
        nlinarith)
      (fun I => ⟨(Real.exp_pos _).le, by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ partMaxDist Y e I := by positivity
        nlinarith⟩)
      (fun P => prod_exp_partMaxDist_le Y e _ hβ₀ P) (hKq0 3) hC₁ hω0 hω1 ⟨zero_le_one, le_rfl⟩
    have hiter := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) (hform e X) k).eq_of_nhds
    unfold bondDeriv
    rw [hiter, iteratedFDeriv_neg_mul_sub x _ _ (hu e X) (hv e X), abs_mul, abs_neg, abs_of_nonneg hx]
    have h1 : x * |iteratedFDeriv ℝ k (fun τ => cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ +
          (1 : ℝ) • frameGapCurve a c.ρA m V e X τ)) 0 (fun l => Pi.single l 1) -
        iteratedFDeriv ℝ k (fun τ => cellEnergyAtFrame true a c.ρA m Y V (frameCurve true a c.ρA m V e X τ)) 0
          (fun l => Pi.single l 1)| ≤ x * (segmentConstant k (Kq 3) C₁ * ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e))) :=
      mul_le_mul_of_nonneg_left hbound hx
    refine h1.trans ?_
    have h2 : segmentConstant k (Kq 3) C₁ ≤ B0 + compositionConstant 0 (Kq 0) (Ch 0) + c.N 0 := by
      have := hsegB k hk
      have := hthr0 0
      have := hc.positivity.2.2.2.2.2.1 0
      linarith
    have h3 : 0 ≤ ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e)) := by positivity
    calc x * (segmentConstant k (Kq 3) C₁ * ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e)))
        = x * (segmentConstant k (Kq 3) C₁ * (ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e)))) := by ring
      _ ≤ x * ((B0 + compositionConstant 0 (Kq 0) (Ch 0) + c.N 0) * (ω * Real.exp (-(c.δ₂ / 4 * bondListDistance Y e)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h3) hx
      _ = _ := by ring
  · have hform3 : (fun τ => frameDensity false a c.ρA x m Y (leftTranslate (bondSpread e X τ) V)) = fun τ => -x *
        (cellEnergyAtFrame false a c.ρA m Y V (frameCurve false a c.ρA m V e X τ) -
          minimalCellShare a (finiteCells F) Y (leftTranslate (bondSpread e X τ) V)) := by
      funext τ
      unfold frameDensity
      rw [cellEnergyAtFrame_frameCurve hCE hodd hs2]
    have hQa := analyticAt_frameCurve hana0 e X
    have hQ0 := frameCurve_zero false a c.ρA m V e X
    have hchv := hc.estimates F s V hch hs (hss.trans hσA) hV
    have hsmall : IsAdmissibleChartPoint L c.σA (fun z i => stepFrame false a c.ρA m (z, i) V) V := by
      have h1 := hfr.between 1 ⟨zero_le_one, le_rfl⟩
      have e1 : (fun z i => interpolatedFrame 1 a c.ρA m (z, i) V) = fun z i => stepFrame false a c.ρA m (z, i) V := by
        funext z i
        simp [interpolatedFrame]
      rw [e1] at h1
      exact h1
    have hgA : AnalyticAt ℝ (cellEnergyAtFrame false a c.ρA m Y V) 0 := (hker F _ V hch hsmall Y _ (chartDirections F)).1
    have hua : AnalyticAt ℝ (fun τ => cellEnergyAtFrame false a c.ρA m Y V (frameCurve false a c.ρA m V e X τ)) 0 :=
      AnalyticAt.comp_of_eq hgA hQa hQ0
    have hva : AnalyticAt ℝ (fun τ => minimalCellShare a (finiteCells F) Y (leftTranslate (bondSpread e X τ) V)) 0 :=
      hchv.cellShares.2.1 Y k e X
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hbu := hTh (chartDimension F) k (cellEnergyAtFrame false a c.ρA m Y V) (frameCurve false a c.ρA m V e X)
      (fun n => Real.exp (-(c.δ₁ / ((k : ℝ) + 1) * cellSupDist Y (directionCell (chartDirections F n)))))
      (Kq k) (Ch k) (fun n => (Real.exp_pos _).le) hQa (by rw [hQ0]; exact hgA)
      (fun l h1 h2 r => by
        rw [hQ0]
        refine abs_iteratedFDeriv_le_prod a Y _ V (funext fun z => by rw [zero_add]; rfl) c.δ₁ (c.δ₁ / ((k : ℝ) + 1)) (Kq k)
          (by positivity) ?_ (hKq0 k) (hker F _ V hch hsmall Y _ (chartDirections F)).1 (fun q hq => ?_) r
        · have hl : (l : ℝ) ≤ (k : ℝ) + 1 := by
            have : (l : ℝ) ≤ k := by exact_mod_cast h2
            linarith
          rw [mul_div_assoc', div_le_iff₀ hk1]
          nlinarith
        · exact ((hker F _ V hch hsmall Y l q).2 h1 hq).trans
            (mul_le_mul_of_nonneg_right (hKql k l (by omega)) (Real.exp_pos _).le))
      (fun p e' hp hinj => by
        have hpk : p ≤ k := by simpa using Fintype.card_le_of_injective e' hinj
        have hS : ∑ b ∈ fineBonds F, Real.exp (-((c.δ₁ / ((k : ℝ) + 1) - 0) * cellSupDist (enclosingCell b.1) Y)) ≤
            Sk k * (L : ℝ) ^ 4 := by
          have := hSk k F hodd hch.2 Y
          rw [hFL] at this
          simpa using this
        have h := _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.weightedNorm_iteratedFDeriv_frameCurve_le hcsym hctri hs2 (c.δ₁ / ((k : ℝ) + 1)) 0 (Mk k) (Sk k * (L : ℝ) ^ 4) le_rfl (by positivity)
          (hMk0 k) false a c.ρA m V Y hS hana0 e X hX e' hp (fun b hb => by
            have h1 := (hfr.small false).deriv_bound b hb p (e ∘ e') (X ∘ e') hp (fun l => hX _)
            refine h1.trans ?_
            simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
            have h2 : Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) (e ∘ e'))) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have : (0 : ℝ) ≤ bondListDistance (enclosingCell b.1) (e ∘ e') := by positivity
              nlinarith
            have h3 : 0 ≤ (16 : ℝ) ^ p * c.Kk p := mul_nonneg (by positivity) (hKk p).le
            exact (mul_le_of_le_one_right h3 h2).trans (hMkl k p hpk))
        refine h.trans ?_
        simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
        rw [hChd]
        simp only
        linarith)
      hk (hKq0 k) (hCh1 k)
    have hbv : |iteratedFDeriv ℝ k (fun τ => minimalCellShare a (finiteCells F) Y (leftTranslate (bondSpread e X τ) V)) 0
        (fun l => Pi.single l 1)| ≤ c.N k := by
      have h1 := hchv.cellShares.2.2.2.2.2.2.1 Y k e X hk hX
      refine le_trans h1 ?_
      have h2 : Real.exp (-c.δ₁ * bondListDistance Y e) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ bondListDistance Y e := by positivity
        nlinarith
      exact mul_le_of_le_one_right (hc.positivity.2.2.2.2.2.1 k).le h2
    unfold bondDeriv
    rw [hform3, iteratedFDeriv_neg_mul_sub x _ _ hua hva, abs_mul, abs_neg, abs_of_nonneg hx]
    refine mul_le_mul_of_nonneg_left ?_ hx
    have h4 := abs_sub (iteratedFDeriv ℝ k (fun τ => cellEnergyAtFrame false a c.ρA m Y V (frameCurve false a c.ρA m V e X τ)) 0
        (fun l => Pi.single l 1)) (iteratedFDeriv ℝ k (fun τ => minimalCellShare a (finiteCells F) Y (leftTranslate (bondSpread e X τ) V)) 0
        (fun l => Pi.single l 1))
    have h5 : |iteratedFDeriv ℝ k (fun τ => cellEnergyAtFrame false a c.ρA m Y V (frameCurve false a c.ρA m V e X τ)) 0
        (fun l => Pi.single l 1)| ≤ compositionConstant k (Kq k) (Ch k) := hbu
    linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
