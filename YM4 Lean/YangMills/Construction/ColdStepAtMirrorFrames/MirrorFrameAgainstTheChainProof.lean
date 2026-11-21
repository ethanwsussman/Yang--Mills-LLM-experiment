import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeThroughTheMirror
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreLocalProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBox
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ReflectedFrame
theorem siteOfCoords_zero {j : ℕ} : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem cellCentre_zero {j : ℕ} : (cellCentre j (0 : F.Cell) : F.Site j) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.cellCentre_zero <;> assumption
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_add_le (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) (u : Fin 4 → ℤ) (r : ℕ) (hu : ∀ l, |u l| ≤ r)
    (hr : ∀ l, 2 * r < F.extent l) : cellSupDist y (y + siteOfCoords F.top u) ≤ r := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameBounds.cellSupDist_add_le <;> assumption
theorem cellSupDist_add_eq (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) (u : Fin 4 → ℤ) (r : ℕ) (hu : ∀ l, |u l| ≤ r)
    (hr : ∀ l, 2 * r < F.extent l) :
    cellSupDist y (y + siteOfCoords F.top u) = Finset.univ.sup fun l => (u l).natAbs := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalFrames.cellSupDist_add_siteOfCoords <;> assumption
theorem exp_neg_le_exp_neg {x y : ℝ} (h : x ≤ y) : Real.exp (-y) ≤ Real.exp (-x) :=
  Real.exp_le_exp.mpr (by linarith)
theorem mem_chordBonds_iff (hcover : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (b : F.Site F.depth × Fin 4) : b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.mem_chordBonds_iff <;> assumption
theorem isAxialTreeBond_iff (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) : IsAxialTreeBond (x, i) ↔
      cellOffset x i ≠ ((F.blockSide : ℤ) - 1) / 2 ∧ ∀ l, i < l → cellOffset x l = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameBounds.isAxialTreeBond_iff <;> assumption
theorem fineBondAt_self (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (x : F.Site F.depth) (i : Fin 4) : fineBondAt (enclosingCell x) 0 (cellOffset x) i = (x, i) := by
  unfold fineBondAt
  rw [siteOfCoords_zero, add_zero, ((hS F hL hs).2.1 x).1]
theorem fineBondAt_reflected (m : ℕ) (x : F.Site F.depth) (i : Fin 4) :
    fineBondAt (0 : (reflectedFrame F m).Cell) 0 (cellOffset x) i = reflectedBond m (x, i) := by
  unfold fineBondAt reflectedBond
  rw [siteOfCoords_zero, add_zero, cellCentre_zero, zero_add]
theorem bondDeriv_coe_sub {j k : ℕ} (G H : F.GaugeField j → imaginaryQuaternions) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hG : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0)
    (hH : ContDiffAt ℝ k (fun τ : Fin k → ℝ => H (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun V => (G V : ℍ[ℝ]) - (H V : ℍ[ℝ])) W c X =
      ((bondDeriv G W c X : imaginaryQuaternions) : ℍ[ℝ]) - ((bondDeriv H W c X : imaginaryQuaternions) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalFrames.bondDeriv_coe_sub <;> assumption
theorem norm_sum_le_card_mul {ι E : Type} [NormedAddCommGroup E] (A : Finset ι) (f : ι → E) (B : ℝ)
    (h : ∀ r ∈ A, ‖f r‖ ≤ B) : ‖∑ r ∈ A, f r‖ ≤ A.card * B := by
  calc ‖∑ r ∈ A, f r‖ ≤ ∑ r ∈ A, ‖f r‖ := norm_sum_le _ _
    _ ≤ ∑ _r ∈ A, B := Finset.sum_le_sum h
    _ = A.card * B := by simp
theorem card_piFinset_le {α : Type} {k : ℕ} (J : Fin k → Finset α) (h : ∀ l, (J l).card ≤ 16) :
    ((Fintype.piFinset J).card : ℝ) ≤ 16 ^ k := by
  classical
  rw [Fintype.card_piFinset]
  have : ∏ l, (J l).card ≤ ∏ _l : Fin k, 16 := Finset.prod_le_prod' fun l _ => h l
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this
end ReflectedFrame
open ReflectedFrame in
theorem reflectedFrameChainBounds_holds (hcover : BlocksCoverLowerLevel)
    (hS : SiteDecomposition) (hJ : reflectedImagesOfBond)
    (hag : ReflectedFieldAgreesOnBox) (hdm : DerivThroughReflection)
    (hcoldM : ReflectedFieldSmallCurvature) : ReflectedFrameChainBounds := by
  classical
  have : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ _
  intro a L c ha hL hc F m σ V hF hm hσ hσs hbig hV
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, hκ, hK, hC, hKk⟩, hcl⟩ := hc.classical
  have hκ0 : 0 < c.κ₂ := lt_of_lt_of_le (by positivity) hκ
  have hδκ : c.δ₂ / 2 ≤ c.κ₂ := by linarith
  have hFc := hF
  obtain ⟨hFL, n, hn, hside⟩ := hF
  have hOddF : Odd F.blockSide := hFL ▸ hL
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside]; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs2 i; omega
  have hbig2 : ∀ i, 2 * m + 2 < F.extent i := fun i => by have := hbig i; omega
  have hspos : 0 < 5 / 4 * σ := by positivity
  have hM : IsBlockTorus L (reflectedFrame F m) := ⟨hFL, 4 * m, by omega, fun _ => rfl⟩
  have hMs2 : ∀ i, 2 ≤ (reflectedFrame F m).extent i := fun i => by
    change 2 ≤ 4 * m
    omega
  have hMs0 : ∀ i, 0 < (reflectedFrame F m).extent i := fun i => by
    have := hMs2 i
    omega
  have hOddM : Odd (reflectedFrame F m).blockSide := hOddF
  have hσA : 5 / 4 * σ ≤ c.σA := by
    have h1 := hc.inequalities.2.2.1
    linarith
  have hcold : ∀ y : F.Cell, IsSmallCurvature (5 / 4 * σ) (reflectedField m y V) := fun y =>
    hcoldM F m y V _ (by omega) hV
  have hmir := fun y : F.Cell =>
    hcl (reflectedFrame F m) (5 / 4 * σ) (reflectedField m y V) hM hspos hσs (hcold y)
  have hcmp := fun y : F.Cell => (hcl F (5 / 4 * σ) V hFc hspos hσs hV).2.2.2 (reflectedFrame F m)
    (reflectedField m y V) y 0 m hM rfl (hcold y) (hag F m y V (by omega) hbig2)
  have hchain := fun y : F.Cell =>
    hc.estimates (reflectedFrame F m) (5 / 4 * σ) (reflectedField m y V) hM hspos hσA (hcold y)
  have hwhole := hc.estimates F (5 / 4 * σ) V hFc hspos hσA hV
  have hchart : ∀ b ∈ chordBonds (finiteCells F),
      reflectedBond m b ∈ chordBonds (finiteCells (reflectedFrame F m)) := by
    intro b hb
    rw [mem_chordBonds_iff hcover hOddF hs0] at hb
    rw [mem_chordBonds_iff hcover hOddM hMs0]
    have ho := ((hS F hOddF hs2).2.1 b.1).2
    have hoff : cellOffset (reflectedBond m b).1 = cellOffset b.1 := by
      have h1 := ((hS (reflectedFrame F m) hOddM hMs2).1 0 (cellOffset b.1) ho).2
      rw [cellCentre_zero, zero_add] at h1
      exact h1
    have hb' : ¬ IsAxialTreeBond (b.1, b.2) := hb
    have e : reflectedBond m b = ((reflectedBond m b).1, b.2) := rfl
    rw [e, isAxialTreeBond_iff hS hOddM hMs2, hoff]
    rw [isAxialTreeBond_iff hS hOddF hs2] at hb'
    exact hb'
  have hfc : ∀ b : F.Site F.depth × Fin 4, bondFrameCoord a c.ρA m b = fun V' =>
      minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b)
        (reflectedField m (enclosingCell b.1) V') := by
    intro b
    funext V'
    simp only [bondFrameCoord, if_pos hbig, reflectedBondCoord]
  have hanM : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt
      (minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b))
      (reflectedField m (enclosingCell b.1) V) :=
    fun b hb => ((hchain (enclosingCell b.1)).coordinates _ (hchart b hb)).1
  have hanF : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (bondFrameCoord a c.ρA m b) V := by
    intro b hb
    rw [hfc b]
    exact (hdm F m _ V imaginaryQuaternions _ (by omega) hbig2 (hanM b hb)).1
  have hzero_cell : ∀ b : F.Site F.depth × Fin 4,
      enclosingCell (reflectedBond m b).1 = (0 : (reflectedFrame F m).Cell) := by
    intro b
    have ho := ((hS F hOddF hs2).2.1 b.1).2
    have h1 := ((hS (reflectedFrame F m) hOddM hMs2).1 0 (cellOffset b.1) ho).1
    rw [cellCentre_zero, zero_add] at h1
    exact h1
  have hhigh : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), 1 ≤ k → AreUnitVectors X → ‖bondDeriv (bondFrameCoord a c.ρA m b) V e X‖ ≤
        16 ^ k * c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)) := by
    intro b hb k e X hk hX
    choose J hcard hzero hnorm hown hno using fun l => hJ F m (enclosingCell b.1) (e l) (by omega) hbig2
    rw [hfc b, (hdm F m _ V imaginaryQuaternions _ (by omega) hbig2 (hanM b hb)).2 k e X J
      (fun l z i hz => hzero l V (X l) z i hz)]
    have hpos : 0 ≤ c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)) := by
      have := hKk k
      positivity
    refine (norm_sum_le_card_mul _ _ (c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)))
      fun r hr => ?_).trans ?_
    · have hJr := Fintype.mem_piFinset.mp hr
      have hu : AreUnitVectors fun l =>
          reflectedDirection m (enclosingCell b.1) V (e l) (X l) (r l).1 (r l).2 := by
        intro l
        rw [hnorm l V (X l) (r l) (hJr l)]
        exact hX l
      refine ((hmir (enclosingCell b.1)).2.2.1 (reflectedBond m b) (hchart b hb) k r _ hk hu).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKk k).le
      apply exp_neg_le_exp_neg
      have hcell0 : enclosingCell (reflectedBond m b).1 = (0 : (reflectedFrame F m).Cell) := hzero_cell b
      rw [hcell0]
      refine mul_le_mul_of_nonneg_left ?_ hκ0.le
      have hle : bondListDistance (enclosingCell b.1) e ≤ bondListDistance (0 : (reflectedFrame F m).Cell) r := by
        refine Finset.sup_le fun l _ => ?_
        have hs1 : cellSupDist (0 : (reflectedFrame F m).Cell) (r l).1 ≤
            bondListDistance (0 : (reflectedFrame F m).Cell) r :=
          Finset.le_sup (f := fun l => cellSupDist (0 : (reflectedFrame F m).Cell) (r l).1) (Finset.mem_univ l)
        refine le_trans ?_ hs1
        by_cases hin : IsCoarseBondInBox (enclosingCell b.1) m (e l)
        · obtain ⟨u, hu1, hu2⟩ := hin
          obtain ⟨_, _, hother⟩ := hown l u hu1 hu2
          by_cases hro : r l = (siteOfCoords (reflectedFrame F m).top u.1, u.2)
          · rw [hro, hu2]
            have e1 := cellSupDist_add_eq (F := F) hs2 (enclosingCell b.1) u.1 m hu1.1
              (fun l => by have := hbig l; omega)
            have e2 := cellSupDist_add_eq (F := reflectedFrame F m) hMs2 0 u.1 m hu1.1
              (fun l => by change 2 * m < 4 * m; omega)
            rw [zero_add] at e2
            exact le_of_eq (e1.trans e2.symm)
          · refine le_trans ?_ (hother (r l) (hJr l) hro)
            rw [hu2]
            exact cellSupDist_add_le hs2 _ _ m hu1.1 (fun l => by have := hbig l; omega)
        · have hnb := hno l fun u hu h => hin ⟨u, hu, h⟩
          have := hJr l
          rw [hnb.1] at this
          simp at this
      exact_mod_cast hle
    · calc ((Fintype.piFinset J).card : ℝ) *
            (c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)))
          ≤ 16 ^ k * (c.Kk k * Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e))) :=
            mul_le_mul_of_nonneg_right (card_piFinset_le J hcard) hpos
        _ = _ := by ring
  have hoff : ∀ b ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (e : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∃ l, ¬ IsCoarseBondInBox (enclosingCell b.1) m (e l)) →
        bondDeriv (bondFrameCoord a c.ρA m b) V e X = 0 := by
    intro b hb k e X ⟨l, hl⟩
    choose J hcard hzero hnorm _ hno using fun l => hJ F m (enclosingCell b.1) (e l) (by omega) hbig2
    rw [hfc b, (hdm F m _ V imaginaryQuaternions _ (by omega) hbig2 (hanM b hb)).2 k e X J
      (fun l z i hz => hzero l V (X l) z i hz)]
    have hJl : J l = ∅ := (hno l fun u hu h => hl ⟨u, hu, h⟩).1
    have : Fintype.piFinset J = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
      have := Fintype.mem_piFinset.mp hr l
      rw [hJl] at this
      simp at this
    rw [this, Finset.sum_empty]
  have hsetup : ∀ b ∈ chordBonds (finiteCells F), ∃ o, o = cellOffset b.1 ∧
      fineBondAt (enclosingCell b.1) 0 o b.2 = b ∧
      fineBondAt (0 : (reflectedFrame F m).Cell) 0 o b.2 = reflectedBond m b ∧
      IsFineBondWithinRadius (enclosingCell b.1) m 0 o b.2 ∧
      cellSupDist (enclosingCell b.1) (enclosingCell (fineBondAt (enclosingCell b.1) 0 o b.2).1) = 0 := by
    intro b hb
    obtain ⟨y, hy⟩ : ∃ y, y = enclosingCell b.1 := ⟨_, rfl⟩
    have ho := ((hS F hOddF hs2).2.1 b.1).2
    obtain ⟨o, hodef⟩ : ∃ o, o = cellOffset b.1 := ⟨_, rfl⟩
    rw [← hodef] at ho
    have hlow : fineBondAt y 0 o b.2 = b := by
      rw [hy, hodef]
      exact fineBondAt_self hS hOddF hs2 b.1 b.2
    have hlowM : fineBondAt (0 : (reflectedFrame F m).Cell) 0 o b.2 = reflectedBond m b := by
      rw [hodef]
      exact fineBondAt_reflected m b.1 b.2
    have hbox : IsFineBondWithinRadius y m 0 o b.2 := by
      refine ⟨hFL ▸ ho, ?_, ?_, ?_, ?_⟩
      · rw [hlow]
        exact hb
      · intro i
        simp
      · rw [hlow, ← hy, cellSupDist_self]
        omega
      · rw [hlow]
        rcases (hS F hOddF hs2).2.2.2 b.1 b.2 with h | h
        · rw [h, ← hy, cellSupDist_self]
          omega
        · rw [h, ← hy]
          have e1 : (unitStep F.top b.2 : F.Cell) = siteOfCoords F.top (Pi.single b.2 1) := rfl
          rw [e1]
          refine (cellSupDist_add_le hs2 _ _ 1 (fun l => ?_) (fun l => ?_)).trans (by omega)
          · by_cases hl : l = b.2
            · subst hl
              simp
            · simp [Pi.single_eq_of_ne hl]
          · have := hbig l
            omega
    have hcd : cellSupDist y (enclosingCell (fineBondAt y 0 o b.2).1) = 0 := by
      rw [hlow, ← hy, cellSupDist_self]
    subst hy
    exact ⟨o, hodef, hlow, hlowM, hbox, hcd⟩
  have hsharp : ∀ b ∈ chordBonds (finiteCells F),
      ‖frameDeviation a c.ρA m b V‖ ≤ 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) := by
    intro b hb
    obtain ⟨o, hodef, hlow, hlowM, hbox, hcd⟩ := hsetup b hb
    have h1 := (hcmp (enclosingCell b.1)).coordinates 0 o b.2 hbox
    rw [hcd, hlow, hlowM] at h1
    have e1 : ‖frameDeviation a c.ρA m b V‖ = ‖((torusCoordinate a c.ρA b V : imaginaryQuaternions) : ℍ[ℝ]) -
        ((torusCoordinate a c.ρA (reflectedBond m b) (reflectedField m (enclosingCell b.1) V) :
          imaginaryQuaternions) : ℍ[ℝ])‖ := by
      unfold frameDeviation
      rw [congrFun (hfc b) V, norm_sub_rev]
      rfl
    rw [e1]
    refine h1.trans ?_
    have e2 : ((m : ℝ) - ((0 : ℕ) : ℝ)) = m := by simp
    rw [e2]
    have h4 : 0 ≤ c.K * σ * Real.exp (-(c.δ₂ * m)) := by positivity
    calc c.K * (5 / 4 * σ) * Real.exp (-(c.δ₂ * m)) = 5 / 4 * (c.K * σ * Real.exp (-(c.δ₂ * m))) := by ring
      _ ≤ 2 * (c.K * σ * Real.exp (-(c.δ₂ * m))) := mul_le_mul_of_nonneg_right (by norm_num) h4
      _ = 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) := by ring
  refine ⟨?_, hsharp, fun y => (hmir y).1, hanF, hhigh, hoff⟩
  intro b hb
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hKs : ∀ k, 1 ≤ k → k ≤ 3 → c.Kk k ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := by
    intro k h1 h3
    have a1 := hKk 1
    have a2 := hKk 2
    have a3 := hKk 3
    interval_cases k <;> linarith
  have hKs0 : 0 < c.Kk 1 + c.Kk 2 + c.Kk 3 := by
    have a1 := hKk 1
    have a2 := hKk 2
    have a3 := hKk 3
    linarith
  obtain ⟨o, hodef, hlow, hlowM, hbox, hcd⟩ := hsetup b hb
  have hCf1 : 2 * c.K + c.Kk 3 + (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) = frameBoundConstant c := rfl
  have hk3 := hKk 3
  refine ⟨?_, ?_⟩
  · refine (hsharp b hb).trans ?_
    have e2 : Real.exp (-(c.δ₂ * m)) ≤ Real.exp (-(c.δ₂ / 4 * m)) := by
      apply exp_neg_le_exp_neg
      have h0 : c.δ₂ / 4 ≤ c.δ₂ := by linarith
      exact mul_le_mul_of_nonneg_right h0 hmR
    have h5 : 2 * c.K ≤ frameBoundConstant c := by
      rw [← hCf1]
      have h6 : 0 ≤ (16 ^ 3 + 1) * (c.Kk 1 + c.Kk 2 + c.Kk 3) := by positivity
      linarith
    unfold frameDecayBound
    calc 2 * c.K * σ * Real.exp (-(c.δ₂ * m)) = 2 * c.K * (σ * Real.exp (-(c.δ₂ * m))) := by ring
      _ ≤ frameBoundConstant c * (σ * Real.exp (-(c.δ₂ / 4 * m))) :=
          mul_le_mul h5 (mul_le_mul_of_nonneg_left e2 hσ.le) (by positivity) (hK.le.trans (by linarith))
      _ = frameBoundConstant c * Real.exp (-(c.δ₂ / 4 * m)) * σ := by ring
  · intro k e X hk1 hk3' hX
    have hGa : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
        bondFrameCoord a c.ρA m b (leftTranslate (bondSpread e X τ) V)) 0 :=
      (hanF b hb k e X).contDiffAt
    have hWa : ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
        torusCoordinate a c.ρA b (leftTranslate (bondSpread e X τ) V)) 0 :=
      ((hwhole.coordinates b hb).1 k e X).contDiffAt
    have hdif : bondDeriv (frameDeviation a c.ρA m b) V e X =
        ((bondDeriv (bondFrameCoord a c.ρA m b) V e X : imaginaryQuaternions) : ℍ[ℝ]) -
          ((bondDeriv (torusCoordinate a c.ρA b) V e X : imaginaryQuaternions) : ℍ[ℝ]) :=
      bondDeriv_coe_sub _ _ V e X hGa hWa
    rw [hdif]
    have hdec := (hcl F (5 / 4 * σ) V hFc hspos hσs hV).2.2.1 b hb k e X hk1 hX
    choose J hcard hzero hnorm hown hno using fun l => hJ F m (enclosingCell b.1) (e l) (by omega) hbig2
    have hsum := (hdm F m (enclosingCell b.1) V imaginaryQuaternions _ (by omega) hbig2 (hanM b hb)).2 k e X J
      (fun l z i hz => hzero l V (X l) z i hz)
    rw [← hfc b] at hsum
    have hCfK : c.Kk 1 + c.Kk 2 + c.Kk 3 ≤ frameBoundConstant c := by
      rw [← hCf1]
      have h6 : 0 ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := hKs0.le
      linarith
    by_cases hall : ∀ l, IsCoarseBondInBox (enclosingCell b.1) m (e l)
    · choose u hu he using hall
      have hown' := fun l => hown l (u l) (hu l) (he l)
      let own : Fin k → (reflectedFrame F m).Cell × Fin 4 :=
        fun l => (siteOfCoords (reflectedFrame F m).top (u l).1, (u l).2)
      have hownmem : own ∈ Fintype.piFinset J := Fintype.mem_piFinset.mpr fun l => (hown' l).1
      rw [hsum, ← Finset.add_sum_erase _ _ hownmem]
      have hT : (fun l => reflectedDirection m (enclosingCell b.1) V (e l) (X l) (own l).1 (own l).2) = X :=
        funext fun l => (hown' l).2.1 V (X l)
      rw [hT]
      have hbonds : bondsAt (enclosingCell b.1) u = e := funext fun l => (he l).symm
      have hbondsM : bondsAt (0 : (reflectedFrame F m).Cell) u = own := by
        funext l
        simp [bondsAt, own]
      have h2 := (hcmp (enclosingCell b.1)).coordinateDerivatives 0 o b.2 k u X hbox hk1 hk3' (fun l => hu l) hX
      rw [hcd, hlow, hlowM, hbonds, hbondsM] at h2
      have hcell0 : enclosingCell (reflectedBond m b).1 = (0 : (reflectedFrame F m).Cell) := hzero_cell b
      have hS1 : ∀ r ∈ (Fintype.piFinset J).erase own, ‖bondDeriv
          (minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b))
          (reflectedField m (enclosingCell b.1) V) r
          (fun l => reflectedDirection m (enclosingCell b.1) V (e l) (X l) (r l).1 (r l).2)‖ ≤
          c.Kk k * Real.exp (-(c.κ₂ * m)) := by
        intro r hr
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hr
        obtain ⟨l, hl⟩ := Function.ne_iff.mp hne
        have hJr := Fintype.mem_piFinset.mp hmem
        have hdist := (hown' l).2.2 (r l) (hJr l) hl
        have hunits : AreUnitVectors fun l =>
            reflectedDirection m (enclosingCell b.1) V (e l) (X l) (r l).1 (r l).2 := by
          intro l'
          rw [hnorm l' V (X l') (r l') (hJr l')]
          exact hX l'
        refine ((hmir (enclosingCell b.1)).2.2.1 (reflectedBond m b) (hchart b hb) k r _ hk1 hunits).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKk k).le
        apply exp_neg_le_exp_neg
        rw [hcell0]
        have h3 : m ≤ bondListDistance (0 : (reflectedFrame F m).Cell) r :=
          hdist.trans (Finset.le_sup (f := fun l => cellSupDist (0 : (reflectedFrame F m).Cell) (r l).1)
            (Finset.mem_univ l))
        have h4 : (m : ℝ) ≤ bondListDistance (0 : (reflectedFrame F m).Cell) r := by exact_mod_cast h3
        exact mul_le_mul_of_nonneg_left h4 hκ0.le
      have hS2 := norm_sum_le_card_mul _ _ _ hS1
      have hcardE : (((Fintype.piFinset J).erase own).card : ℝ) ≤ 16 ^ 3 := by
        have h1 : (((Fintype.piFinset J).erase own).card : ℝ) ≤ ((Fintype.piFinset J).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
        refine h1.trans ((card_piFinset_le J hcard).trans ?_)
        exact pow_le_pow_right₀ (by norm_num) hk3'
      have hD : bondListDistance (enclosingCell b.1) e ≤ m := by
        refine Finset.sup_le fun l _ => ?_
        rw [he l]
        exact cellSupDist_add_le hs2 _ _ m (hu l).1 (fun l => by have := hbig l; omega)
      have hDR : ((bondListDistance (enclosingCell b.1) e : ℕ) : ℝ) ≤ m := by exact_mod_cast hD
      have hmaxe : ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ) = m := by rw [max_eq_left hD]
      rw [hmaxe]
      have hE0 := Real.exp_pos (-(c.δ₂ / 4 * ((m : ℝ) + m)))
      have hE2 : Real.exp (-(c.δ₂ / 2 * ((m : ℝ) - ((0 : ℕ) : ℝ)))) ≤
          Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) := by
        apply exp_neg_le_exp_neg
        apply le_of_eq
        push_cast
        ring
      have hE3 : Real.exp (-(c.κ₂ * m)) ≤ Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) := by
        apply exp_neg_le_exp_neg
        calc c.δ₂ / 4 * ((m : ℝ) + m) = c.δ₂ / 2 * m := by ring
          _ ≤ c.κ₂ * m := mul_le_mul_of_nonneg_right hδκ hmR
      have hdiff : ‖(((bondDeriv (minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m))
            (reflectedBond m b)) (reflectedField m (enclosingCell b.1) V) own X +
            ∑ r ∈ (Fintype.piFinset J).erase own, bondDeriv
            (minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b))
            (reflectedField m (enclosingCell b.1) V) r
            (fun l => reflectedDirection m (enclosingCell b.1) V (e l) (X l) (r l).1 (r l).2)) :
              imaginaryQuaternions) : ℍ[ℝ]) -
          ((bondDeriv (torusCoordinate a c.ρA b) V e X : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          ‖bondDeriv (torusCoordinate a c.ρA b) V e X - bondDeriv (torusCoordinate a c.ρA (reflectedBond m b))
            (reflectedField m (enclosingCell b.1) V) own X‖ + ‖∑ r ∈ (Fintype.piFinset J).erase own, bondDeriv
            (minimizingBondCoordinate a c.ρA (finiteCells (reflectedFrame F m)) (reflectedBond m b))
            (reflectedField m (enclosingCell b.1) V) r
            (fun l => reflectedDirection m (enclosingCell b.1) V (e l) (X l) (r l).1 (r l).2)‖ := by
        rw [← Submodule.coe_sub, Submodule.coe_norm]
        have e1 : ∀ p q w : imaginaryQuaternions, ‖p + q - w‖ ≤ ‖w - p‖ + ‖q‖ := by
          intro p q w
          have : p + q - w = -(w - p) + q := by abel
          rw [this]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
        exact e1 _ _ _
      refine hdiff.trans ?_
      have h6 : (((Fintype.piFinset J).erase own).card : ℝ) * (c.Kk k * Real.exp (-(c.κ₂ * m))) ≤
          16 ^ 3 * ((c.Kk 1 + c.Kk 2 + c.Kk 3) * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m)))) := by
        have h7 : c.Kk k * Real.exp (-(c.κ₂ * m)) ≤
            (c.Kk 1 + c.Kk 2 + c.Kk 3) * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) :=
          mul_le_mul (hKs k hk1 hk3') hE3 (Real.exp_pos _).le hKs0.le
        exact mul_le_mul hcardE h7 (by have := hKk k; positivity) (by norm_num)
      have h8 : c.Kk 3 * Real.exp (-(c.δ₂ / 2 * ((m : ℝ) - ((0 : ℕ) : ℝ)))) ≤
          c.Kk 3 * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) :=
        mul_le_mul_of_nonneg_left hE2 hk3.le
      have h9 : c.Kk 3 + 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3) ≤ frameBoundConstant c := by
        rw [← hCf1]
        have h6 : 0 ≤ c.Kk 1 + c.Kk 2 + c.Kk 3 := hKs0.le
        linarith
      calc _ ≤ c.Kk 3 * Real.exp (-(c.δ₂ / 2 * ((m : ℝ) - ((0 : ℕ) : ℝ)))) +
              (((Fintype.piFinset J).erase own).card : ℝ) * (c.Kk k * Real.exp (-(c.κ₂ * m))) :=
            add_le_add h2 hS2
        _ ≤ c.Kk 3 * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) +
              16 ^ 3 * ((c.Kk 1 + c.Kk 2 + c.Kk 3) * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m)))) :=
            add_le_add h8 h6
        _ = (c.Kk 3 + 16 ^ 3 * (c.Kk 1 + c.Kk 2 + c.Kk 3)) * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) := by ring
        _ ≤ frameBoundConstant c * Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + m))) :=
            mul_le_mul_of_nonneg_right h9 hE0.le
    · push Not at hall
      obtain ⟨l₀, hl₀⟩ := hall
      have hnb := hno l₀ fun u hu h => hl₀ ⟨u, hu, h⟩
      have hpi : Fintype.piFinset J = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun r hr => ?_
        have := Fintype.mem_piFinset.mp hr l₀
        rw [hnb.1] at this
        simp at this
      rw [hsum, hpi, Finset.sum_empty, ZeroMemClass.coe_zero, zero_sub, norm_neg, ← Submodule.coe_norm]
      have hD : m ≤ bondListDistance (enclosingCell b.1) e := hnb.2.trans
        (Finset.le_sup (f := fun l => cellSupDist (enclosingCell b.1) (e l).1) (Finset.mem_univ l₀))
      have hDR : (m : ℝ) ≤ ((bondListDistance (enclosingCell b.1) e : ℕ) : ℝ) := by exact_mod_cast hD
      have hmaxe : ((max m (bondListDistance (enclosingCell b.1) e) : ℕ) : ℝ) =
          bondListDistance (enclosingCell b.1) e := by
        rw [max_eq_right hD]
      rw [hmaxe]
      refine hdec.trans ?_
      have hexp : Real.exp (-(c.κ₂ * bondListDistance (enclosingCell b.1) e)) ≤
          Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + bondListDistance (enclosingCell b.1) e))) := by
        apply exp_neg_le_exp_neg
        have h0 : (0 : ℝ) ≤ bondListDistance (enclosingCell b.1) e := by positivity
        calc c.δ₂ / 4 * ((m : ℝ) + bondListDistance (enclosingCell b.1) e)
            ≤ c.δ₂ / 4 * (((bondListDistance (enclosingCell b.1) e : ℕ) : ℝ) +
                bondListDistance (enclosingCell b.1) e) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = c.δ₂ / 2 * bondListDistance (enclosingCell b.1) e := by ring
          _ ≤ c.κ₂ * bondListDistance (enclosingCell b.1) e := mul_le_mul_of_nonneg_right hδκ h0
      exact mul_le_mul ((hKs k hk1 hk3').trans hCfK) hexp (Real.exp_pos _).le (hKs0.le.trans hCfK)
end YangMills.Construction.ColdStepAtMirrorFrames
end
