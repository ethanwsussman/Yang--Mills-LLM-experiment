import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorCoordinateReadsTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
namespace LocalFrames
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem bondDeriv_coe_sub {j k : ℕ} (G H : F.GaugeField j → imaginaryQuaternions) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0)
    (hH : ContDiffAt ℝ k (fun τ : Fin k → ℝ => H (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun V => (G V : ℍ[ℝ]) - (H V : ℍ[ℝ])) W c X =
      ((bondDeriv G W c X : imaginaryQuaternions) : ℍ[ℝ]) - ((bondDeriv H W c X : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondDeriv
  obtain ⟨g, hg⟩ : ∃ g : (Fin k → ℝ) → imaginaryQuaternions,
      g = fun τ => G (leftTranslate (bondSpread c X τ) W) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : (Fin k → ℝ) → imaginaryQuaternions,
      h = fun τ => H (leftTranslate (bondSpread c X τ) W) := ⟨_, rfl⟩
  rw [← hg] at hG ⊢
  rw [← hh] at hH ⊢
  have e : (fun τ : Fin k → ℝ => ((G (leftTranslate (bondSpread c X τ) W) : imaginaryQuaternions) : ℍ[ℝ]) -
      ((H (leftTranslate (bondSpread c X τ) W) : imaginaryQuaternions) : ℍ[ℝ])) =
        imaginaryQuaternions.subtypeL ∘ (g - h) := by
    funext τ
    simp [hg, hh]
  have hgh : ContDiffAt ℝ k (g - h) 0 := hG.sub hH
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left imaginaryQuaternions.subtypeL hgh le_rfl,
    iteratedFDeriv_sub_apply hG hH]
  simp
theorem bondFrameCoord_near_whole {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L) (hc : c.Admissible a L)
    (hMF : ReflectedFrameChainBounds) {m : ℕ} (hm : 16 ≤ m) {σ : ℝ} (hσ : 0 < σ) (hσs : 5 / 4 * σ ≤ c.s₀)
    (hF : IsBlockTorus L F) {V : F.GaugeField F.top} (hV : IsSmallCurvature (5 / 4 * σ) V)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F)) :
    ‖bondFrameCoord a c.ρA m b V - torusCoordinate a c.ρA b V‖ ≤ 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) ∧
    ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      ‖bondDeriv (bondFrameCoord a c.ρA m b) V e X - bondDeriv (torusCoordinate a c.ρA b) V e X‖ ≤
        frameBoundConstant c * Real.exp (-(c.δ₂ / 2 * m)) := by
  classical
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  have hspos : 0 < 5 / 4 * σ := by positivity
  have hσA : 5 / 4 * σ ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  have hCf0 : 0 < frameBoundConstant c := by
    unfold frameBoundConstant
    have h1 := hKk 3
    have h2 : 0 < (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by
      have a1 := hKk 1
      have a2 := hKk 2
      positivity
    linarith
  by_cases hbig : ∀ i, 4 * m + 5 < F.extent i
  · have hfacts := hMF a L c ha hL hc F m σ V hF hm hσ hσs hbig hV
    refine ⟨?_, fun k e X hk hk3 hX => ?_⟩
    · have h1 := hfacts.deviation_le b hb
      rw [Submodule.coe_norm, Submodule.coe_sub]
      exact h1
    · have hclause := hc.estimates F (5 / 4 * σ) V hF hspos hσA hV
      have hGa : ContDiffAt ℝ k
          (fun τ : Fin k → ℝ => bondFrameCoord a c.ρA m b (leftTranslate (bondSpread e X τ) V)) 0 :=
        (hfacts.analytic b hb k e X).contDiffAt
      have hWa : ContDiffAt ℝ k
          (fun τ : Fin k → ℝ => torusCoordinate a c.ρA b (leftTranslate (bondSpread e X τ) V)) 0 :=
        ((hclause.coordinates b hb).1 k e X).contDiffAt
      have hdif : bondDeriv (frameDeviation a c.ρA m b) V e X =
          ((bondDeriv (bondFrameCoord a c.ρA m b) V e X : imaginaryQuaternions) : ℍ[ℝ]) -
            ((bondDeriv (torusCoordinate a c.ρA b) V e X : imaginaryQuaternions) : ℍ[ℝ]) :=
        bondDeriv_coe_sub _ _ V e X hGa hWa
      have h1 := (hfacts.near_minimizer b hb).2 k e X hk hk3 hX
      rw [hdif] at h1
      rw [Submodule.coe_norm, Submodule.coe_sub]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCf0.le)
      apply Real.exp_le_exp.mpr
      have hmx : (m : ℝ) ≤ ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ) := by
        exact_mod_cast le_max_left _ _
      have : c.δ₂ / 4 * ((m : ℝ) + m) ≤
          c.δ₂ / 4 * ((m : ℝ) + ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e2 : c.δ₂ / 4 * ((m : ℝ) + m) = c.δ₂ / 2 * m := by ring
      linarith
  · have hfun : bondFrameCoord a c.ρA m b = torusCoordinate a c.ρA b := by
      funext V'
      simp only [bondFrameCoord, if_neg hbig]
      rfl
    rw [hfun]
    simp only [sub_self, norm_zero]
    refine ⟨by positivity, fun _ _ _ _ _ _ => by positivity⟩
theorem norm_sub_le_of_four {E : Type} [SeminormedAddCommGroup E] (A B B' A' : E) :
    ‖A - A'‖ ≤ ‖A - B‖ + ‖B - B'‖ + ‖A' - B'‖ := by
  have e : A - A' = (A - B) + (B - B') - (A' - B') := by abel
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
theorem mem_chordBonds_iff (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.mem_chordBonds_iff <;> assumption
theorem isAxialTreeBond_iff (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) : IsAxialTreeBond (x, i) ↔
      cellOffset x i ≠ ((F.blockSide : ℤ) - 1) / 2 ∧ ∀ l, i < l → cellOffset x l = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameBounds.isAxialTreeBond_iff <;> assumption
theorem siteOfCoords_inj {r : ℕ} (hs : ∀ i, 2 * r + 2 < F.extent i) {u w : Fin 4 → ℤ}
    (hu : WithinRadius r u) (hw : WithinRadius r w) (h : (siteOfCoords F.top u : F.Cell) = siteOfCoords F.top w) :
    u = w := by
  funext l
  have h1 := congrFun h l
  simp only [siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  rw [period_top] at h1
  obtain ⟨q, hq⟩ := h1
  have a1 := abs_le.mp (hu l)
  have a2 := abs_le.mp (hw l)
  have hsl : (2 * (r : ℤ) + 2) < F.extent l := by exact_mod_cast hs l
  have hq0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  rw [hq0] at hq
  omega
theorem cellSupDist_add_siteOfCoords (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) (u : Fin 4 → ℤ) (r : ℕ)
    (hu : ∀ l, |u l| ≤ r) (hr : ∀ l, 2 * r < F.extent l) :
    cellSupDist y (y + siteOfCoords F.top u) = Finset.univ.sup fun l => (u l).natAbs := by
  unfold cellSupDist
  refine Finset.sup_congr rfl fun l _ => ?_
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
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem leftTranslate_agree {F' : BlockFrame} {r k : ℕ} (hs : ∀ i, 2 * r + 2 < F.extent i)
    (hs' : ∀ i, 2 * r + 2 < F'.extent i) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell)
    (hag : ∀ b, BondWithinRadius r b →
      V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2)
    (e : Fin k → (Fin 4 → ℤ) × Fin 4) (he : ∀ l, BondWithinRadius r (e l)) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) (b : (Fin 4 → ℤ) × Fin 4) (hb : BondWithinRadius r b) :
    leftTranslate (bondSpread (bondsAt Y e) X τ) V (Y + siteOfCoords F.top b.1) b.2 =
      leftTranslate (bondSpread (bondsAt Y' e) X τ) V' (Y' + siteOfCoords F'.top b.1) b.2 := by
  simp only [leftTranslate, hag b hb]
  congr 2
  simp only [bondSpread]
  refine Finset.sum_congr rfl fun l _ => ?_
  have key : bondsAt Y e l = (Y + siteOfCoords F.top b.1, b.2) ↔
      bondsAt Y' e l = (Y' + siteOfCoords F'.top b.1, b.2) := by
    simp only [bondsAt, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      have := siteOfCoords_inj hs (he l).1 hb.1 (add_left_cancel h1)
      exact ⟨by rw [this], h2⟩
    · rintro ⟨h1, h2⟩
      have := siteOfCoords_inj hs' (he l).1 hb.1 (add_left_cancel h1)
      exact ⟨by rw [this], h2⟩
  by_cases hc : bondsAt Y e l = (Y + siteOfCoords F.top b.1, b.2)
  · rw [if_pos hc, if_pos (key.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (key.mpr h))]
end LocalFrames
open LocalFrames in
theorem framesLocalStatement_holds (hcover : BlocksCoverLowerLevel) (hS : SiteDecomposition)
    (hMF : ReflectedFrameChainBounds) (hMC : ReflectedCoordinateReadsBox) :
    framesLocalStatement := by
  classical
  intro a L c ha hL hc
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  have hCf0 : 0 < frameBoundConstant c := by
    unfold frameBoundConstant
    have h1 := hKk 3
    have h2 : 0 < (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by
      have a1 := hKk 1
      have a2 := hKk 2
      positivity
    linarith
  have hδ1 : c.δ₂ ≤ 1 := by
    have h1 := hc.inequalities.1
    have h2 := hc.inequalities.2.1
    linarith
  have he3 : Real.exp (c.δ₂ / 4) ≤ 3 := by
    have h1 : Real.exp (c.δ₂ / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.exp_one_lt_d9
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 14 * c.K + 6 * frameBoundConstant c + c.Kk 3 + 1 := ⟨_, rfl⟩
  have hk3 := hKk 3
  refine ⟨C, by rw [hCdef]; linarith, ?_⟩
  intro σ m F F' V V' Y Y' r hσ hσs hm hF hF' ht hV hV' hag star
  have hspos : 0 < 5 / 4 * σ := by positivity
  have cmp := (hcl F (5 / 4 * σ) V hF hspos hσs hV).2.2.2 F' V' Y Y' r hF' ht hV' hag
  obtain ⟨hFL, n, hn, hside⟩ := id hF
  obtain ⟨hFL', n', hn', hside'⟩ := id hF'
  have hOdd : Odd F.blockSide := hFL ▸ hL
  have hOdd' : Odd F'.blockSide := hFL' ▸ hL
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hside']; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hs0' : ∀ i, 0 < F'.extent i := fun i => by have := hs2' i; omega
  have hr : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.1 i).resolve_left (by have := hs0 i; omega)
  have hr' : ∀ i, 2 * r + 2 < F'.extent i := fun i => (hag.2.1 i).resolve_left (by have := hs0' i; omega)
  have hbond := hag.2.2.2
  have hfacts : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
      fineBondAt Y' h o i ∈ chordBonds (finiteCells F') ∧
      enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h ∧ cellOffset (fineBondAt Y h o i).1 = o ∧
      enclosingCell (fineBondAt Y' h o i).1 = Y' + siteOfCoords F'.top h ∧
      cellOffset (fineBondAt Y' h o i).1 = o := by
    rintro h o i ⟨ho, hch, hin, hd1, hd2⟩
    have ho' : o ∈ centredCube F'.blockSide := by
      rw [hFL']
      rw [hFL] at ho
      exact ho
    obtain ⟨c1, o1⟩ := (hS F hOdd hs2).1 (Y + siteOfCoords F.top h) o ho
    obtain ⟨c2, o2⟩ := (hS F' hOdd' hs2').1 (Y' + siteOfCoords F'.top h) o ho'
    refine ⟨?_, c1, o1, c2, o2⟩
    rw [mem_chordBonds_iff hcover hOdd' hs0']
    rw [mem_chordBonds_iff hcover hOdd hs0] at hch
    have e1 : fineBondAt Y h o i = ((fineBondAt Y h o i).1, i) := rfl
    have e2 : fineBondAt Y' h o i = ((fineBondAt Y' h o i).1, i) := rfl
    rw [e1, isAxialTreeBond_iff hS hOdd hs2] at hch
    rw [e2, isAxialTreeBond_iff hS hOdd' hs2']
    have o1' : cellOffset (fineBondAt Y h o i).1 = o := o1
    have o2' : cellOffset (fineBondAt Y' h o i).1 = o := o2
    rw [o1', hFL] at hch
    rw [o2', hFL']
    exact hch
  have hsame : (∀ i, 4 * m + 5 < F.extent i) → (∀ i, 4 * m + 5 < F'.extent i) → ∀ (h o : Fin 4 → ℤ) (i : Fin 4),
      IsFineBondWithinRadius Y r h o i → (m : ℝ) < (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) →
      stepFrame false a c.ρA m (fineBondAt Y h o i) V = stepFrame false a c.ρA m (fineBondAt Y' h o i) V' ∧
      ∀ (k : ℕ) (e : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
        (∀ l, BondWithinRadius r (e l)) →
        bondDeriv (stepFrame false a c.ρA m (fineBondAt Y h o i)) V (bondsAt Y e) X =
          bondDeriv (stepFrame false a c.ρA m (fineBondAt Y' h o i)) V' (bondsAt Y' e) X := by
    intro hbig hbig' h o i hbox hmb
    obtain ⟨hch', c1, o1, c2, o2⟩ := hfacts h o i hbox
    have hin := hbox.2.2.1
    have hD := cellSupDist_add_siteOfCoords hs2 Y h r hin (fun l => by have := hr l; omega)
    rw [c1] at hmb
    have hmb' : m + cellSupDist Y (Y + siteOfCoords F.top h) < r := by
      have : ((m + cellSupDist Y (Y + siteOfCoords F.top h) : ℕ) : ℝ) < r := by
        push_cast
        linarith
      exact_mod_cast this
    have hbound : ∀ l, |h l| + m ≤ r := by
      intro l
      have h1 : (h l).natAbs ≤ cellSupDist Y (Y + siteOfCoords F.top h) := by
        rw [hD]
        exact Finset.le_sup (f := fun l => (h l).natAbs) (Finset.mem_univ l)
      rw [Int.abs_eq_natAbs]
      omega
    have hagree : ∀ (V₁ : F.GaugeField F.top) (V₂ : F'.GaugeField F'.top),
        (∀ b, BondWithinRadius r b →
          V₁ (Y + siteOfCoords F.top b.1) b.2 = V₂ (Y' + siteOfCoords F'.top b.1) b.2) →
        bondFrameCoord a c.ρA m (fineBondAt Y h o i) V₁ = bondFrameCoord a c.ρA m (fineBondAt Y' h o i) V₂ := by
      intro V₁ V₂ h12
      simp only [bondFrameCoord, if_pos hbig, if_pos hbig', reflectedBondCoord]
      have e1 : reflectedBond m (fineBondAt Y h o i) = (siteOfCoords (reflectedFrame F m).depth o, i) := by
        unfold reflectedBond
        rw [o1]
        rfl
      have e2 : reflectedBond m (fineBondAt Y' h o i) = (siteOfCoords (reflectedFrame F' m).depth o, i) := by
        unfold reflectedBond
        rw [o2]
        rfl
      rw [e1, e2, c1, c2]
      refine hMC F F' m a c.ρA _ _ V₁ V₂ o i (hFL.trans hFL'.symm) ht.symm (by omega) (fun u hu => ?_)
      have hb : BondWithinRadius r (h + u.1, u.2) := by
        refine ⟨fun l => ?_, fun l => ?_⟩
        · have a1 := hbound l
          have a2 := hu.1 l
          have := abs_add_le (h l) (u.1 l)
          change |h l + u.1 l| ≤ (r : ℤ)
          omega
        · have a1 := hbound l
          have a2 := hu.2 l
          have := abs_add_le (h l) ((u.1 + Pi.single u.2 1 : Fin 4 → ℤ) l)
          have e3 : ((h + u.1, u.2).1 + Pi.single (h + u.1, u.2).2 1 : Fin 4 → ℤ) l =
              h l + (u.1 + Pi.single u.2 1 : Fin 4 → ℤ) l := by
            simp only [Pi.add_apply]
            ring
          rw [e3]
          omega
      have := h12 _ hb
      simp only [_root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalFrames.siteOfCoords_add, ← add_assoc] at this
      exact this
    have hfr : ∀ (b : F.Site F.depth × Fin 4) (V₁ : F.GaugeField F.top),
        stepFrame false a c.ρA m b V₁ = bondFrameCoord a c.ρA m b V₁ :=
      fun b V₁ => by simp [stepFrame]
    have hfr' : ∀ (b : F'.Site F'.depth × Fin 4) (V₁ : F'.GaugeField F'.top),
        stepFrame false a c.ρA m b V₁ = bondFrameCoord a c.ρA m b V₁ := fun b V₁ => by simp [stepFrame]
    refine ⟨by rw [hfr, hfr']; exact hagree V V' hbond, fun k e X he => ?_⟩
    unfold bondDeriv
    have hfun : (fun τ : Fin k → ℝ =>
        stepFrame false a c.ρA m (fineBondAt Y h o i) (leftTranslate (bondSpread (bondsAt Y e) X τ) V)) =
        fun τ : Fin k → ℝ =>
          stepFrame false a c.ρA m (fineBondAt Y' h o i) (leftTranslate (bondSpread (bondsAt Y' e) X τ) V') := by
      funext τ
      rw [hfr, hfr']
      exact hagree _ _ (leftTranslate_agree hr hr' V V' Y Y' hbond e he X τ)
    rw [hfun]
  have hnn : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), IsFineBondWithinRadius Y r h o i →
      0 ≤ (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := by
    intro h o i hbox
    have h1 : ((cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) : ℕ) : ℝ) ≤ r := by
      exact_mod_cast hbox.2.2.2.1
    linarith
  have hexp1 : ∀ x : ℝ, 0 ≤ x → Real.exp (-(c.δ₂ * x)) ≤ Real.exp (-(c.δ₂ / 4 * x)) := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have := mul_nonneg hδ.le hx
    linarith
  have hexp2 : ∀ x : ℝ, 0 ≤ x → Real.exp (-(c.δ₂ / 2 * x)) ≤ Real.exp (-(c.δ₂ / 4 * x)) := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have := mul_nonneg hδ.le hx
    linarith
  have hexp3 : ∀ x : ℝ, x ≤ 2 * m + 1 → Real.exp (-(c.δ₂ / 2 * m)) ≤ 3 * Real.exp (-(c.δ₂ / 4 * x)) := by
    intro x hx
    have h1 : -(c.δ₂ / 2 * m) ≤ c.δ₂ / 4 + -(c.δ₂ / 4 * x) := by
      have := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ c.δ₂ / 4)
      nlinarith
    calc Real.exp (-(c.δ₂ / 2 * m)) ≤ Real.exp (c.δ₂ / 4 + -(c.δ₂ / 4 * x)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (c.δ₂ / 4) * Real.exp (-(c.δ₂ / 4 * x)) := Real.exp_add _ _
      _ ≤ 3 * Real.exp (-(c.δ₂ / 4 * x)) := mul_le_mul_of_nonneg_right he3 (Real.exp_pos _).le
  have hexp4 : ∀ x : ℝ, x ≤ 2 * m + 1 → Real.exp (-(c.δ₂ * m)) ≤ 3 * Real.exp (-(c.δ₂ / 4 * x)) := by
    intro x hx
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp3 x hx)
    have : 0 ≤ c.δ₂ * m := by positivity
    linarith
  have hbigs : ∀ x : ℝ, x ≤ r → ¬ x ≤ 2 * m + 1 →
      (∀ i, 4 * m + 5 < F.extent i) ∧ ∀ i, 4 * m + 5 < F'.extent i := by
    intro x hx hn
    have h1 : (2 * m + 1 : ℝ) < r := by
      push Not at hn
      linarith
    have h2 : 2 * m + 1 < r := by exact_mod_cast h1
    exact ⟨fun i => by have := hr i; omega, fun i => by have := hr' i; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h o i hbox
    obtain ⟨hch', c1, o1, c2, o2⟩ := hfacts h o i hbox
    have hch := hbox.2.1
    have hx0 := hnn h o i hbox
    obtain ⟨x, hx⟩ : ∃ x, x = (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := ⟨_, rfl⟩
    have hxr : x ≤ r := by
      rw [hx]
      have : (0 : ℝ) ≤ cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := by positivity
      linarith
    have hW := cmp.coordinates h o i hbox
    rw [← hx] at hW hx0 ⊢
    have hE := Real.exp_pos (-(c.δ₂ / 4 * x))
    have hW2 : c.K * (5 / 4 * σ) * Real.exp (-(c.δ₂ * x)) ≤ 2 * c.K * σ * Real.exp (-(c.δ₂ / 4 * x)) := by
      have h1 := hexp1 x hx0
      have h2 : 0 ≤ c.K * σ := by positivity
      calc c.K * (5 / 4 * σ) * Real.exp (-(c.δ₂ * x)) = 5 / 4 * (c.K * σ) * Real.exp (-(c.δ₂ * x)) := by ring
        _ ≤ 5 / 4 * (c.K * σ) * Real.exp (-(c.δ₂ / 4 * x)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 2 * (c.K * σ) * Real.exp (-(c.δ₂ / 4 * x)) :=
            mul_le_mul_of_nonneg_right (by linarith) hE.le
        _ = _ := by ring
    have hCσ : ∀ B : ℝ, B ≤ 14 * c.K →
        B * σ * Real.exp (-(c.δ₂ / 4 * x)) ≤ C * σ * Real.exp (-(c.δ₂ / 4 * x)) := by
      intro B hB
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hσ.le) hE.le
      rw [hCdef]
      linarith
    cases star with
    | true =>
      have e1 : ∀ (b : F.Site F.depth × Fin 4) (V₁ : F.GaugeField F.top),
          stepFrame true a c.ρA m b V₁ = torusCoordinate a c.ρA b V₁ :=
        fun b V₁ => by simp [stepFrame, torusCoordinate]
      have e2 : ∀ (b : F'.Site F'.depth × Fin 4) (V₁ : F'.GaugeField F'.top),
          stepFrame true a c.ρA m b V₁ = torusCoordinate a c.ρA b V₁ :=
        fun b V₁ => by simp [stepFrame, torusCoordinate]
      rw [e1, e2]
      refine hW.trans (hW2.trans ?_)
      exact hCσ _ (by linarith)
    | false =>
      by_cases hxm : x ≤ 2 * m + 1
      · have e1 : ∀ (b : F.Site F.depth × Fin 4) (V₁ : F.GaugeField F.top),
            stepFrame false a c.ρA m b V₁ = bondFrameCoord a c.ρA m b V₁ :=
          fun b V₁ => by simp [stepFrame]
        have e2 : ∀ (b : F'.Site F'.depth × Fin 4) (V₁ : F'.GaugeField F'.top),
            stepFrame false a c.ρA m b V₁ = bondFrameCoord a c.ρA m b V₁ := fun b V₁ => by simp [stepFrame]
        rw [e1, e2]
        have k1 := (bondFrameCoord_near_whole ha hL hc hMF hm hσ hσs hF hV _ hch).1
        have k2 := (bondFrameCoord_near_whole ha hL hc hMF hm hσ hσs hF' hV' _ hch').1
        have k3 := hexp4 x hxm
        have hW' : ‖torusCoordinate a c.ρA (fineBondAt Y h o i) V - torusCoordinate a c.ρA (fineBondAt Y' h o i) V'‖ ≤
            c.K * (5 / 4 * σ) * Real.exp (-(c.δ₂ * x)) := by
          rw [Submodule.coe_norm, Submodule.coe_sub]
          exact hW
        have k4 : 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) ≤ 6 * c.K * σ * Real.exp (-(c.δ₂ / 4 * x)) := by
          have h2 : 0 ≤ 2 * c.K * σ := by positivity
          calc 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) ≤ 2 * c.K * σ * (3 * Real.exp (-(c.δ₂ / 4 * x))) :=
                mul_le_mul_of_nonneg_left k3 h2
            _ = _ := by ring
        rw [← Submodule.coe_sub, ← Submodule.coe_norm]
        refine (norm_sub_le_of_four _ (torusCoordinate a c.ρA (fineBondAt Y h o i) V)
          (torusCoordinate a c.ρA (fineBondAt Y' h o i) V') _).trans ?_
        have k5 := hCσ (14 * c.K) le_rfl
        nlinarith
      · obtain ⟨b1, b2⟩ := hbigs x hxr hxm
        have hmx : (m : ℝ) < x := by
          push Not at hxm
          have : (0 : ℝ) ≤ m := by positivity
          linarith
        rw [hx] at hmx
        rw [(hsame b1 b2 h o i hbox hmx).1, sub_self, norm_zero]
        have hC0 : 0 < C := by
          rw [hCdef]
          linarith
        positivity
  · intro h o i k e X hbox hk1 hk3' he hX
    obtain ⟨hch', c1, o1, c2, o2⟩ := hfacts h o i hbox
    have hch := hbox.2.1
    have hx0 := hnn h o i hbox
    obtain ⟨x, hx⟩ : ∃ x, x = (r : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := ⟨_, rfl⟩
    have hxr : x ≤ r := by
      rw [hx]
      have : (0 : ℝ) ≤ cellSupDist Y (enclosingCell (fineBondAt Y h o i).1) := by positivity
      linarith
    have hW := cmp.coordinateDerivatives h o i k e X hbox hk1 hk3' he hX
    rw [← hx] at hW hx0 ⊢
    have hE := Real.exp_pos (-(c.δ₂ / 4 * x))
    have hC0 : 0 < C := by
      rw [hCdef]
      linarith
    have hW2 : c.Kk 3 * Real.exp (-(c.δ₂ / 2 * x)) ≤ c.Kk 3 * Real.exp (-(c.δ₂ / 4 * x)) :=
      mul_le_mul_of_nonneg_left (hexp2 x hx0) hk3.le
    cases star with
    | true =>
      have e1 : stepFrame true a c.ρA m (fineBondAt Y h o i) = torusCoordinate a c.ρA (fineBondAt Y h o i) := by
        funext V₁
        simp [stepFrame, torusCoordinate]
      have e2 : stepFrame true a c.ρA m (fineBondAt Y' h o i) = torusCoordinate a c.ρA (fineBondAt Y' h o i) := by
        funext V₁
        simp [stepFrame, torusCoordinate]
      rw [e1, e2]
      refine hW.trans (hW2.trans (mul_le_mul_of_nonneg_right ?_ hE.le))
      rw [hCdef]
      linarith
    | false =>
      by_cases hxm : x ≤ 2 * m + 1
      · have e1 : stepFrame false a c.ρA m (fineBondAt Y h o i) = bondFrameCoord a c.ρA m (fineBondAt Y h o i) := by
          funext V₁
          simp [stepFrame]
        have e2 : stepFrame false a c.ρA m (fineBondAt Y' h o i) =
            bondFrameCoord a c.ρA m (fineBondAt Y' h o i) := by
          funext V₁
          simp [stepFrame]
        rw [e1, e2]
        have k1 := (bondFrameCoord_near_whole ha hL hc hMF hm hσ hσs hF hV _ hch).2 k (bondsAt Y e) X hk1 hk3' hX
        have k2 := (bondFrameCoord_near_whole ha hL hc hMF hm hσ hσs hF' hV' _ hch').2 k (bondsAt Y' e) X hk1 hk3' hX
        have k3 := hexp3 x hxm
        have k4 : frameBoundConstant c * Real.exp (-(c.δ₂ / 2 * m)) ≤
            3 * frameBoundConstant c * Real.exp (-(c.δ₂ / 4 * x)) := by
          calc frameBoundConstant c * Real.exp (-(c.δ₂ / 2 * m)) ≤
                frameBoundConstant c * (3 * Real.exp (-(c.δ₂ / 4 * x))) :=
                mul_le_mul_of_nonneg_left k3 hCf0.le
            _ = _ := by ring
        refine (norm_sub_le_of_four _ (bondDeriv (torusCoordinate a c.ρA (fineBondAt Y h o i)) V (bondsAt Y e) X)
          (bondDeriv (torusCoordinate a c.ρA (fineBondAt Y' h o i)) V' (bondsAt Y' e) X) _).trans ?_
        have k5 : (6 * frameBoundConstant c + c.Kk 3) * Real.exp (-(c.δ₂ / 4 * x)) ≤
            C * Real.exp (-(c.δ₂ / 4 * x)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE.le
          rw [hCdef]
          linarith
        nlinarith
      · obtain ⟨b1, b2⟩ := hbigs x hxr hxm
        have hmx : (m : ℝ) < x := by
          push Not at hxm
          have : (0 : ℝ) ≤ m := by positivity
          linarith
        rw [hx] at hmx
        rw [(hsame b1 b2 h o i hbox hmx).2 k e X he, sub_self, norm_zero]
        positivity
  · intro hst hbig hbig' h o i hbox hmb
    subst hst
    exact hsame hbig hbig' h o i hbox hmb
end YangMills.Construction.ColdStepAtMirrorFrames
end
