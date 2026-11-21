import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZeroProof
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreLocal
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmallProof
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfAFrameBetween
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace FrameBounds
theorem frameSmallness_mono {star : Bool} {a ρ δ₂ κ₂ C C' σ : ℝ} {Kk : ℕ → ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (h : C ≤ C') (hσ : 0 < σ)
    (hs : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V) : FrameSmallness star a ρ δ₂ κ₂ C' σ Kk m V :=
  { minimizer_exists := hs.minimizer_exists
    norm_le := fun b hb => (hs.norm_le b hb).trans (mul_le_mul_of_nonneg_right h hσ.le)
    norm_add_le := hs.norm_add_le
    holonomy_ratio := fun c x π hx => (hs.holonomy_ratio c x π hx).trans (mul_le_mul_of_nonneg_right h hσ.le)
    small_curvature := hs.small_curvature
    deriv_decay := fun b hb k c X h1 h2 hX => (hs.deriv_decay b hb k c X h1 h2 hX).trans
      (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
    deriv_bound := hs.deriv_bound
    deriv_eq_zero_off_box := hs.deriv_eq_zero_off_box
    analytic := hs.analytic
    gauge_covariant := hs.gauge_covariant
    translation_invariant := hs.translation_invariant }
theorem frameLocality_mono {F' : BlockFrame} {star : Bool} {a ρ δ₂ C C' σ : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (h : C ≤ C') (hσ : 0 < σ)
    (hs : FrameLocality star a ρ δ₂ C σ m V V' Y Y' r) :
    FrameLocality star a ρ δ₂ C' σ m V V' Y Y' r :=
  { value := fun x o i hb => (hs.value x o i hb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h hσ.le) (Real.exp_pos _).le)
    deriv := fun x o i k e X hb h1 h2 h3 hX => (hs.deriv x o i k e X hb h1 h2 h3 hX).trans
      (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
    eq_of_far := hs.eq_of_far }
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) : leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
theorem stepFrame_eq_interpolated (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (V : F.GaugeField F.top) :
    stepFrame star a ρ m b V = interpolatedFrame (if star then 0 else 1) a ρ m b V := by
  cases star <;> simp [interpolatedFrame]
theorem frameCoordField_eq_interpolated (star : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top) :
    frameCoordField star a ρ m V = fun z i => interpolatedFrame (if star then 0 else 1) a ρ m (z, i) V := by
  funext z i
  exact stepFrame_eq_interpolated star a ρ m (z, i) V
theorem frameFirstDeriv_eq_interpolated (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) :
    frameFirstDeriv star a ρ m b e = interpolatedSlope (if star then 0 else 1) a ρ m b e := by
  funext V
  unfold frameFirstDeriv interpolatedSlope
  rw [frameCoordField_eq_interpolated]
theorem frameAction_eq_interpolated (star : Bool) (a ρ : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4)
    (e : imaginaryQuaternions) (V : F.GaugeField F.top) :
    frameActionAlongBond star a ρ m b e V = energyAlongInterpolatedBond (if star then 0 else 1) a ρ m b e V := by
  funext u
  unfold frameActionAlongBond energyAlongInterpolatedBond
  rw [frameCoordField_eq_interpolated, stepFrame_eq_interpolated]
theorem bondDeriv_zero_interpolatedSlope {a ρ s : ℝ} {m : ℕ} {b : F.Site F.depth × Fin 4}
    {e : imaginaryQuaternions} (V : F.GaugeField F.top) :
    bondDeriv (interpolatedSlope s a ρ m b e) V (fun l : Fin 0 => l.elim0) (fun l : Fin 0 => l.elim0) =
      interpolatedSlope s a ρ m b e V := by
  unfold bondDeriv
  rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero]
theorem chartedSlope_eq_zero {a ρ : ℝ} {V : F.GaugeField F.top} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a (finiteCells F) V ρ w) (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedSlope a w V b e = 0 := by
  unfold chartedSlope
  apply IsLocalMin.deriv_eq_zero
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [zero_smul, add_zero, Function.update_eq_self]
  exact h.2.2 _
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem mem_chordBonds_iff (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.mem_chordBonds_iff <;> assumption
theorem isAxialTreeBond_iff (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) : IsAxialTreeBond (x, i) ↔
      cellOffset x i ≠ ((F.blockSide : ℤ) - 1) / 2 ∧ ∀ l, i < l → cellOffset x l = 0 := by
  unfold IsAxialTreeBond
  simp only
  rw [((hS F hL hs).2.2.1 x i)]
theorem mem_chordBonds_of_same_offset {F' : BlockFrame} (hcover : BlocksCoverLowerLevel) (hS : SiteDecomposition)
    (hL : Odd F.blockSide) (hL' : Odd F'.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    (hLL : F.blockSide = F'.blockSide) (Y : F.Cell) (Y' : F'.Cell) (h o : Fin 4 → ℤ) (i : Fin 4)
    (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) : fineBondAt Y' h o i ∈ chordBonds (finiteCells F') := by
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hs0' : ∀ i, 0 < F'.extent i := fun i => by have := hs' i; omega
  have ho' : o ∈ centredCube F'.blockSide := hLL ▸ ho
  have o1 := ((hS F hL hs).1 (Y + siteOfCoords F.top h) o ho).2
  have o2 := ((hS F' hL' hs').1 (Y' + siteOfCoords F'.top h) o ho').2
  rw [mem_chordBonds_iff hcover hL' hs0']
  rw [mem_chordBonds_iff hcover hL hs0] at hb
  have e1 : fineBondAt Y h o i = ((fineBondAt Y h o i).1, i) := rfl
  have e2 : fineBondAt Y' h o i = ((fineBondAt Y' h o i).1, i) := rfl
  rw [e1, isAxialTreeBond_iff hS hL hs] at hb
  rw [e2, isAxialTreeBond_iff hS hL' hs']
  have o1' : cellOffset (fineBondAt Y h o i).1 = o := o1
  have o2' : cellOffset (fineBondAt Y' h o i).1 = o := o2
  rw [o1'] at hb
  rw [o2', ← hLL]
  exact hb
theorem cellSupDist_add_le (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) (u : Fin 4 → ℤ) (r : ℕ) (hu : ∀ l, |u l| ≤ r)
    (hr : ∀ l, 2 * r < F.extent l) : cellSupDist y (y + siteOfCoords F.top u) ≤ r := by
  unfold cellSupDist
  refine Finset.sup_le fun l _ => ?_
  have hne : NeZero (F.period F.top l) := ⟨by
    rw [period_top]
    have := hs l
    omega⟩
  have e : y l - ((y + siteOfCoords F.top u : F.Cell)) l = -((u l : ℤ) : ZMod (F.period F.top l)) := by
    simp [siteOfCoords]
  rw [e, ZMod.natAbs_valMinAbs_neg]
  have hv : ((u l : ℤ) : ZMod (F.period F.top l)).valMinAbs = u l := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    rw [period_top]
    have a := abs_le.mp (hu l)
    have hrl : (2 * (r : ℤ)) < F.extent l := by exact_mod_cast hr l
    simp only [Set.mem_Ioc]
    constructor <;> omega
  rw [hv]
  have := hu l
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem far_decay_bound {δ₂ κ x Ct E₀ R M Lr : ℝ} (hδ : 0 < δ₂) (hκ : κ ≤ δ₂ / 2 ^ 14) (hκ0 : 0 < κ)
    (hx : 0 < x) (hxm : x ≤ Real.exp (δ₂ * M)) (hCt : 0 < Ct) (hM : 16 ≤ M) (hRM : 4 * M < R)
    (hL : 2 ^ 40 ≤ Lr) (hE : Lr * ((R - M - 2) / 2) - 2 * Lr - 1 ≤ E₀) :
    x * (Ct * Real.exp (-(δ₂ * E₀))) ≤ Ct * Real.exp (-(2 ^ 8 * κ * R)) := by
  have hkey : 2 ^ 8 * κ * R ≤ δ₂ * (E₀ - M) := by
    have h1 : 2 ^ 8 * κ * R ≤ δ₂ / 64 * R := by
      have : 2 ^ 8 * κ ≤ δ₂ / 64 := by
        have := mul_le_mul_of_nonneg_left hκ (by norm_num : (0 : ℝ) ≤ 2 ^ 8)
        linarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h2 : R / 64 ≤ E₀ - M := by
      have h3 : Lr * (R / 4 + 5) ≤ Lr * ((R - M - 2) / 2 - 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
      have h4 : R / 4 ≤ Lr * (R / 4) := by nlinarith
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h2 hδ.le
    linarith
  have hexp : Real.exp (δ₂ * M) * Real.exp (-(δ₂ * E₀)) ≤ Real.exp (-(2 ^ 8 * κ * R)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc x * (Ct * Real.exp (-(δ₂ * E₀))) = Ct * (x * Real.exp (-(δ₂ * E₀))) := by ring
    _ ≤ Ct * (Real.exp (δ₂ * M) * Real.exp (-(δ₂ * E₀))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxm (Real.exp_pos _).le) hCt.le
    _ ≤ Ct * Real.exp (-(2 ^ 8 * κ * R)) := mul_le_mul_of_nonneg_left hexp hCt.le
end FrameBounds
set_option maxHeartbeats 2000000 in
open FrameBounds in
theorem frameBoundsStatement_holds (hcover : BlocksCoverLowerLevel) (hS : SiteDecomposition)
    (hMF : ReflectedFrameChainBounds) (hSm : framesSmallStatement) (hLoc : framesLocalStatement)
    (hSl : interpolatedSlopeBounds) (hTwo : ChartedSlopeComparison) :
    frameBoundsStatement := by
  classical
  intro a L c ha hL hL40 hc
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  obtain ⟨Csm, σs, hCsm, hσs0, hsmall⟩ := hSm a L c ha hL hc
  obtain ⟨Cl, hCl, hlocal⟩ := hLoc a L c ha hL hc
  obtain ⟨Csl, σl, hCsl, hσl0, hslope⟩ := hSl a L c ha hL hL40 hc
  obtain ⟨Ct, hCt, htwo⟩ := hTwo a L c ha hL hL40 hc
  obtain ⟨C, hCdef⟩ : ∃ C, C = Csm + Cl + 2 * Csl + Ct + 3 := ⟨_, rfl⟩
  have hC3 : 3 ≤ C := by rw [hCdef]; linarith
  have hCf0 : 0 < frameBoundConstant c := by
    unfold frameBoundConstant
    have h1 := hKk 3
    have h2 : 0 < (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by
      have a1 := hKk 1
      have a2 := hKk 2
      positivity
    linarith
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hL40
    exact_mod_cast this
  refine ⟨frameBoundConstant c, C, min (min σs σl) (min (4 / 5 * c.s₀) (1 / (64 * L * (Csm + 1)))), hCf0,
    by linarith, ?_, ?_⟩
  · refine lt_min (lt_min hσs0 hσl0) (lt_min (by positivity) ?_)
    have : 0 < Csm + 1 := by linarith
    positivity
  intro κ σ x m t n₀ hκ0 hκ' hσ hσ₀ hx hm hn₀ hgap hy1 hy2 F V hT hV
  have hσsm : σ ≤ σs := hσ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσsl : σ ≤ σl := hσ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσs : 5 / 4 * σ ≤ c.s₀ := by
    have : σ ≤ 4 / 5 * c.s₀ := hσ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hσL : (Csm + 1) * σ ≤ 1 / (64 * L) := by
    have h1 : σ ≤ 1 / (64 * L * (Csm + 1)) := hσ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : 0 < Csm + 1 := by linarith
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hspos : 0 < 5 / 4 * σ := by positivity
  have hchain : ∀ F' : BlockFrame, IsCubicTopTorus L t n₀ F' → IsBlockTorus L F' := by
    rintro F' ⟨h1, _, n, h3, h4⟩
    exact ⟨h1, n, by omega, h3⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = frameDecayBound (frameBoundConstant c) c.δ₂ m := ⟨_, rfl⟩
  rw [← hωdef] at hgap hy1
  have hω0 : 0 ≤ ω := by
    rw [hωdef]
    unfold frameDecayBound
    positivity
  have hxpos : 0 < x := by linarith
  have hxω : ∀ C' : ℝ, 0 ≤ C' → C' ≤ C → x * (C' * ω) ≤ Real.exp (-(2 ^ 10 * κ * m)) := by
    intro C' h0 h1
    refine le_trans ?_ hy1
    have h2 : x ≤ x ^ 2 := by nlinarith
    have h3 : 0 ≤ C' * ω := by positivity
    calc x * (C' * ω) ≤ x ^ 2 * (C' * ω) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ x ^ 2 * (C * ω) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hω0) (by positivity)
      _ = C * x ^ 2 * ω := by ring
  have hE1 : Real.exp (-(2 ^ 10 * κ * m)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ 2 ^ 10 * κ * m := by positivity
    linarith
  have hval : ∀ (F₁ : BlockFrame) (V₁ : F₁.GaugeField F₁.top), IsBlockTorus L F₁ → IsSmallCurvature (5 / 4 * σ) V₁ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ chordBonds (finiteCells F₁), ∀ e : imaginaryQuaternions, ‖e‖ = 1 →
        |interpolatedSlope s a c.ρA m b e V₁| ≤ Csl * ω := by
    intro F₁ V₁ hF₁ hV₁ s hs b hb e he
    have h3 := (hslope σ m F₁ V₁ hσ hσsl hm (hωdef ▸ hgap) hF₁ hV₁ s hs b hb e).2.2 he 0 (fun l => l.elim0)
      (fun l => l.elim0) (by omega) (fun l => l.elim0)
    rw [bondDeriv_zero_interpolatedSlope] at h3
    have e0 : bondListDistance (enclosingCell b.1)
        (fun l : Fin 0 => l.elim0 : Fin 0 → F₁.Site F₁.top × Fin 4) = 0 := by
      simp [bondListDistance]
    rw [e0, ← hωdef] at h3
    simpa using h3
  have hst : ∀ star, FrameNearlyCritical star a c.ρA c.δ₂ C ω x m V := by
    intro star
    have hs : (if star then (0 : ℝ) else 1) ∈ Set.Icc (0 : ℝ) 1 := by
      cases star <;> simp
    have hsl := hslope σ m F V hσ hσsl hm (hωdef ▸ hgap) (hchain F hT) hV _ hs
    refine ⟨fun b hb e => ?_, fun b hb e => ?_, fun b hb e he => ?_, fun b hb e he k c' X hk hX => ?_⟩
    · rw [frameAction_eq_interpolated]
      exact (hsl b hb e).1
    · rw [frameFirstDeriv_eq_interpolated]
      exact (hsl b hb e).2.1
    · have h3 := hval F V (hchain F hT) hV _ hs b hb e he
      rw [congrFun (frameFirstDeriv_eq_interpolated star a c.ρA m b e) V]
      have h4 := hxω Csl (by linarith) (by rw [hCdef]; linarith)
      calc x * |interpolatedSlope (if star then 0 else 1) a c.ρA m b e V| ≤ x * (Csl * ω) :=
            mul_le_mul_of_nonneg_left h3 hxpos.le
        _ ≤ 1 := h4.trans hE1
    · rw [frameFirstDeriv_eq_interpolated]
      have h3 := (hsl b hb e).2.2 he k c' X hk hX
      rw [← hωdef] at h3
      refine h3.trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hω0) (Real.exp_pos _).le
      rw [hCdef]
      linarith
  refine ⟨fun hbig => (hMF a L c ha hL hc F m σ V (hchain F hT) hm hσ hσs hbig hV).near_minimizer, fun star =>
    frameSmallness_mono (by rw [hCdef]; linarith) hσ
      ((hsmall σ m F V hσ hσsm hm (hωdef ▸ hgap) (hchain F hT) hV).1 star),
    by rw [← hωdef]; exact hst, fun F' V' Y Y' r hT' hV' hag => ?_⟩
  have hFc := hchain F hT
  have hFc' := hchain F' hT'
  have ht : F'.depth = F.depth := hT'.2.1.trans hT.2.1.symm
  have hloc := fun star => hlocal σ m F F' V V' Y Y' r hσ hσs hm hFc hFc' ht hV hV' hag star
  refine ⟨fun star => frameLocality_mono (by rw [hCdef]; linarith) hσ (hloc star), fun star => ?_⟩
  obtain ⟨hFL, n, hn, hside⟩ := id hFc
  obtain ⟨hFL', n', hn', hside'⟩ := id hFc'
  have hOdd : Odd F.blockSide := hFL ▸ hL
  have hOdd' : Odd F'.blockSide := hFL' ▸ hL
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hs0' : ∀ i, 0 < F'.extent i := fun i => by have := hs2' i; omega
  have hr : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.1 i).resolve_left (by have := hs0 i; omega)
  have hr' : ∀ i, 2 * r + 2 < F'.extent i := fun i => (hag.2.1 i).resolve_left (by have := hs0' i; omega)
  intro h o i e hbox he
  have hb := hbox.2.1
  have ho := hbox.1
  have hb' := mem_chordBonds_of_same_offset hcover hS hOdd hOdd' hs2 hs2' (hFL.trans hFL'.symm) Y Y' h o i ho hb
  have hC0 : 0 < C := by linarith
  cases star with
  | true =>
    have hz : ∀ (F₁ : BlockFrame) (V₁ : F₁.GaugeField F₁.top) (b₁ : F₁.Site F₁.depth × Fin 4), IsBlockTorus L F₁ →
        IsSmallCurvature (5 / 4 * σ) V₁ → frameFirstDeriv true a c.ρA m b₁ e V₁ = 0 := by
      intro F₁ V₁ b₁ hF₁ hV₁
      have hl := (hcl F₁ (5 / 4 * σ) V₁ hF₁ hspos hσs hV₁).1
      unfold frameFirstDeriv
      have e1 : frameCoordField true a c.ρA m V₁ = minimizingCoordinates a (finiteCells F₁) V₁ c.ρA := by
        funext z j
        simp [frameCoordField, stepFrame, minimizingBondCoordinate]
      rw [e1]
      exact chartedSlope_eq_zero hl b₁ e
    rw [hz F V _ hFc hV, hz F' V' _ hFc' hV']
    simp only [sub_zero, abs_zero, mul_zero]
    positivity
  | false =>
    have e1 : ∀ (F₁ : BlockFrame) (V₁ : F₁.GaugeField F₁.top) (b₁ : F₁.Site F₁.depth × Fin 4),
        frameFirstDeriv false a c.ρA m b₁ e V₁ = interpolatedSlope 1 a c.ρA m b₁ e V₁ := fun F₁ V₁ b₁ => by
      simpa using congrFun (frameFirstDeriv_eq_interpolated false a c.ρA m b₁ e) V₁
    by_cases hr4 : r ≤ 4 * m
    · rw [e1, e1]
      have a1 := hval F V hFc hV 1 (Set.right_mem_Icc.mpr zero_le_one) _ hb e he
      have a2 := hval F' V' hFc' hV' 1 (Set.right_mem_Icc.mpr zero_le_one) _ hb' e he
      have h3 := hxω (2 * Csl) (by linarith) (by rw [hCdef]; linarith)
      have h4 : |interpolatedSlope 1 a c.ρA m (fineBondAt Y h o i) e V -
          interpolatedSlope 1 a c.ρA m (fineBondAt Y' h o i) e V'| ≤ 2 * Csl * ω := by
        refine (abs_sub _ _).trans ?_
        linarith
      have h5 : Real.exp (-(2 ^ 10 * κ * m)) ≤ Real.exp (-(2 ^ 8 * κ * r)) := by
        apply Real.exp_le_exp.mpr
        have h6 : (r : ℝ) ≤ 4 * m := by exact_mod_cast hr4
        nlinarith
      calc x * |interpolatedSlope 1 a c.ρA m (fineBondAt Y h o i) e V -
            interpolatedSlope 1 a c.ρA m (fineBondAt Y' h o i) e V'|
          ≤ x * (2 * Csl * ω) := mul_le_mul_of_nonneg_left h4 hxpos.le
        _ ≤ Real.exp (-(2 ^ 8 * κ * r)) := h3.trans h5
        _ ≤ C * Real.exp (-(2 ^ 8 * κ * r)) := le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
    · have hm4 : 4 * m < r := by omega
      have hbig : ∀ i, 4 * m + 5 < F.extent i := fun i => by have := hr i; omega
      have hbig' : ∀ i, 4 * m + 5 < F'.extent i := fun i => by have := hr' i; omega
      obtain ⟨r', hr'def⟩ : ∃ r', r' = r - m - 2 := ⟨_, rfl⟩
      have hr'r : r' + m + 2 = r := by omega
      have hin_mono : ∀ {p q : ℕ}, p ≤ q → ∀ u : Fin 4 → ℤ, WithinRadius p u → WithinRadius q u :=
        fun hpq u hu l => (hu l).trans (by exact_mod_cast hpq)
      have hS1 := (hsmall σ m F V hσ hσsm hm (hωdef ▸ hgap) hFc hV).1 false
      have hS2 := (hsmall σ m F' V' hσ hσsm hm (hωdef ▸ hgap) hFc' hV').1 false
      have hpt : ∀ (F₁ : BlockFrame) (V₁ : F₁.GaugeField F₁.top),
          FrameSmallness false a c.ρA c.δ₂ c.κ₂ Csm σ c.Kk m V₁ →
          IsAdmissibleChartPoint L c.s₀ (frameCoordField false a c.ρA m V₁) V₁ := by
        intro F₁ V₁ h1
        refine ⟨fun b₁ hb₁ => ?_, fun p hp => ?_⟩
        · have h2 := h1.norm_le b₁ hb₁
          have h3 : Csm * σ ≤ (Csm + 1) * σ := by nlinarith
          exact h2.trans (h3.trans hσL)
        · have h2 := h1.small_curvature p hp
          simp only [Bool.false_eq_true, if_false] at h2
          refine h2.trans_le ?_
          linarith
      have hag' : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r' := by
        refine ⟨fun i => Or.inr (by have := hr i; omega), fun i => Or.inr (by have := hr' i; omega),
          fun u hu => hag.2.2.1 u (hin_mono (by omega) u hu), fun b₁ hb₁ => hag.2.2.2 b₁ ?_⟩
        exact ⟨hin_mono (by omega) _ hb₁.1, hin_mono (by omega) _ hb₁.2⟩
      have hchartEq : ∀ (h₁ o₁ : Fin 4 → ℤ) (i₁ : Fin 4), WithinRadius r' h₁ → o₁ ∈ centredCube L →
          fineBondAt Y h₁ o₁ i₁ ∈ chordBonds (finiteCells F) →
          frameCoordField false a c.ρA m V (fineBondAt Y h₁ o₁ i₁).1 i₁ =
            frameCoordField false a c.ρA m V' (fineBondAt Y' h₁ o₁ i₁).1 i₁ := by
        intro h₁ o₁ i₁ hin₁ ho₁ hch₁
        have ho₂ : o₁ ∈ centredCube F.blockSide := hFL ▸ ho₁
        have c1 := ((hS F hOdd hs2).1 (Y + siteOfCoords F.top h₁) o₁ ho₂).1
        have hc1 : enclosingCell (fineBondAt Y h₁ o₁ i₁).1 = Y + siteOfCoords F.top h₁ := c1
        have hd : cellSupDist Y (Y + siteOfCoords F.top h₁) ≤ r' :=
          cellSupDist_add_le hs2 Y h₁ r' hin₁ (fun l => by have := hr l; omega)
        have hfar : cellSupDist Y (enclosingCell ((fineBondAt Y h₁ o₁ i₁).1 + unitStep F.depth i₁)) ≤ r := by
          rcases (hS F hOdd hs2).2.2.2 (fineBondAt Y h₁ o₁ i₁).1 i₁ with h3 | h3
          · rw [h3, hc1]
            omega
          · rw [h3, hc1]
            have e2 : (Y + siteOfCoords F.top h₁ + unitStep F.top i₁ : F.Cell) =
                Y + siteOfCoords F.top (h₁ + Pi.single i₁ 1) := by
              have e3 : (siteOfCoords F.top (h₁ + Pi.single i₁ 1) : F.Cell) =
                  siteOfCoords F.top h₁ + unitStep F.top i₁ := by
                funext l
                simp [siteOfCoords, unitStep]
              rw [e3, add_assoc]
            rw [e2]
            refine (cellSupDist_add_le hs2 Y _ (r' + 1) (fun l => ?_)
              (fun l => by have := hr l; omega)).trans (by omega)
            have a1 := hin₁ l
            by_cases hl : l = i₁
            · subst hl
              simp only [Pi.add_apply, Pi.single_eq_same]
              have := abs_add_le (h₁ l) 1
              simp only [abs_one] at this
              push_cast
              omega
            · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
              push_cast
              omega
        have hbox₁ : IsFineBondWithinRadius Y r h₁ o₁ i₁ :=
          ⟨ho₂, hch₁, hin_mono (by omega) _ hin₁, by rw [hc1]; omega, hfar⟩
        have hmb : (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h₁ o₁ i₁).1) := by
          rw [hc1]
          have h4 : m + cellSupDist Y (Y + siteOfCoords F.top h₁) < r := by omega
          have h5 : ((m + cellSupDist Y (Y + siteOfCoords F.top h₁) : ℕ) : ℝ) < r := by exact_mod_cast h4
          push_cast at h5
          linarith
        exact ((hloc false).eq_of_far rfl hbig hbig' h₁ o₁ i₁ hbox₁ hmb).1
      have hbox₂ : IsFineBondWithinRadius Y (r' / 2) h o i := by
        have hq : r / 4 ≤ r' / 2 := by omega
        exact ⟨hbox.1, hbox.2.1, hin_mono hq _ hbox.2.2.1, hbox.2.2.2.1.trans hq, hbox.2.2.2.2.trans hq⟩
      have hfin := htwo F F' (frameCoordField false a c.ρA m V) (frameCoordField false a c.ρA m V') V V' Y Y' r'
        (by omega) hFc hFc' ht (hpt F V hS1) (hpt F' V' hS2) hag' hchartEq h o i e hbox₂ he
      have hxm : x ≤ Real.exp (c.δ₂ * m) := by
        have h3 : x ^ 2 * Real.exp (-(2 * c.δ₂ * m)) ≤ 1 := by
          have h4 : 0 ≤ x ^ 2 * Real.exp (-(2 * c.δ₂ * m)) := by positivity
          have h5 : C * (x ^ 2 * Real.exp (-(2 * c.δ₂ * m))) ≤ 1 := by
            rw [← mul_assoc]
            exact hy2
          nlinarith
        have h6 : x ^ 2 ≤ (Real.exp (c.δ₂ * m)) ^ 2 := by
          rw [← Real.exp_nat_mul]
          have h7 : Real.exp (-(2 * c.δ₂ * m)) * Real.exp (((2 : ℕ) : ℝ) * (c.δ₂ * m)) = 1 := by
            rw [← Real.exp_add]
            simp only [Nat.cast_ofNat]
            have : -(2 * c.δ₂ * (m : ℝ)) + 2 * (c.δ₂ * m) = 0 := by ring
            rw [this, Real.exp_zero]
          have h8 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (((2 : ℕ) : ℝ) * (c.δ₂ * m))).le
          rw [mul_assoc, h7, mul_one, one_mul] at h8
          exact h8
        exact (pow_le_pow_iff_left₀ hxpos.le (Real.exp_pos _).le (by norm_num)).mp h6
      have hnum := far_decay_bound (δ₂ := c.δ₂) (κ := κ) (x := x) (Ct := Ct)
        (E₀ := (L : ℝ) * ((r' : ℝ) / 2) - 2 * L - 1) (R := r) (M := m) (Lr := L) hδ hκ' hκ0 hxpos hxm hCt
        (by exact_mod_cast hm) (by exact_mod_cast hm4) (by exact_mod_cast hL40) (by
          have h3 : (r : ℝ) = r' + m + 2 := by exact_mod_cast hr'r.symm
          rw [h3]
          apply le_of_eq
          ring)
      change x * |chartedSlope a (frameCoordField false a c.ρA m V) V (fineBondAt Y h o i) e -
        chartedSlope a (frameCoordField false a c.ρA m V') V' (fineBondAt Y' h o i) e| ≤ _
      calc _ ≤ x * (Ct * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r' : ℝ) / 2) - 2 * L - 1)))) :=
            mul_le_mul_of_nonneg_left hfin hxpos.le
        _ ≤ Ct * Real.exp (-(2 ^ 8 * κ * r)) := hnum
        _ ≤ C * Real.exp (-(2 ^ 8 * κ * r)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            rw [hCdef]
            linarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
