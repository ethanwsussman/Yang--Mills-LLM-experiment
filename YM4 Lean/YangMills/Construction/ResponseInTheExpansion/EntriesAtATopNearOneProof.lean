import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOnATorus
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.EntriesMoveByTheirKernels
import YangMills.Construction.ResponseInTheExpansion.EntriesOnTwoToriProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
def HessianEntriesNearTrivialTop : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∀ s₁ e₀ ϱ : ℝ, 0 < s₁ → 0 ≤ e₀ → 0 < ϱ → e₀ + 2 * ϱ ≤ 1 / (64 * (L : ℝ)) →
      s₁ + 8 * (e₀ + 2 * ϱ) < c.σA →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (A : F.Site F.top → Fin 4 → imaginaryQuaternions) (Y : F.Cell)
        (Y' : F'.Cell) (R : ℕ) (sT sW : ℝ) (p q : F.Site F.depth × Fin 4 × imaginaryQuaternions)
        (p' q' : F'.Site F'.depth × Fin 4 × imaginaryQuaternions),
        1 ≤ R → IsBlockTorus L F → IsBlockTorus L F' → F'.depth = F.depth →
        (∀ i, 2 * (R + 2) + 2 < F.extent i) → (∀ i, 2 * (R + 2) + 2 < F'.extent i) →
        ‖p.2.2‖ = 1 → ‖q.2.2‖ = 1 → ‖p'.2.2‖ = 1 → ‖q'.2.2‖ = 1 →
        0 ≤ sT → 4 * sT < s₁ → 0 ≤ sW → IsSmallCurvature s₁ V →
        (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e₀) →
        (∀ y i, cellSupDist y Y ≤ R + 2 → V y i = expUnit (A y i) ∧ ‖A y i‖ ≤ sT) →
        (∀ b ∈ chordBonds (finiteCells F), cellSupDist (enclosingCell b.1) Y ≤ R → ‖w b.1 b.2‖ ≤ sW) →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius R h → o ∈ centredCube L →
          fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
          directionCoordinate (Sum.inl p) (fineBondAt Y h o i).1 i =
              directionCoordinate (Sum.inl p') (fineBondAt Y' h o i).1 i ∧
            directionCoordinate (Sum.inl q) (fineBondAt Y h o i).1 i =
              directionCoordinate (Sum.inl q') (fineBondAt Y' h o i).1 i) →
        8 * cellSupDist (enclosingCell p.1) Y ≤ R → 8 * cellSupDist (enclosingCell p'.1) Y' ≤ R →
        |chartMixedDeriv a w V ![Sum.inl p, Sum.inl q] -
            chartMixedDeriv a (fun _ _ => 0) (flatTopField (F := F')) ![Sum.inl p', Sum.inl q']| ≤
          C * (sT + sW) * Real.exp (-(c.δ₁ / 2 * cellSupDist (enclosingCell p.1) (enclosingCell q.1))) +
            C * Real.exp (-(c.δ₁ / 16 * R))
end YangMills.Construction.ResponseInTheExpansion
end

noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.ChartResponse YangMills.Construction.DirectionalDerivatives
namespace YangMills.Construction.ResponseInTheExpansion
variable {F : BlockFrame}
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private local instance normedAlgebraRatQuaternion : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
private theorem expUnit_smul_mul_smul (a b : ℝ) (X : imaginaryQuaternions) :
    expUnit (a • X) * expUnit (b • X) = expUnit ((a + b) • X) := by
  apply Subtype.ext
  have hcomm : Commute ((a • X : imaginaryQuaternions) : ℍ[ℝ]) ((b • X : imaginaryQuaternions) : ℍ[ℝ]) := by
    have ha : ((a • X : imaginaryQuaternions) : ℍ[ℝ]) = a • (X : ℍ[ℝ]) := rfl
    have hb : ((b • X : imaginaryQuaternions) : ℍ[ℝ]) = b • (X : ℍ[ℝ]) := rfl
    rw [ha, hb]
    exact ((Commute.refl _).smul_left a).smul_right b
  have hsum : (((a + b) • X : imaginaryQuaternions) : ℍ[ℝ]) =
      ((a • X : imaginaryQuaternions) : ℍ[ℝ]) + ((b • X : imaginaryQuaternions) : ℍ[ℝ]) := by
    rw [add_smul]
    rfl
  simp only [expUnit]
  show NormedSpace.exp _ * NormedSpace.exp _ = NormedSpace.exp _
  rw [hsum, NormedSpace.exp_add_of_commute hcomm]
private theorem norm_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_expUnit_sub_one_le' (x : imaginaryQuaternions) :
    ‖((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖x‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
private theorem plaquetteHolonomy_eq_product {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
private theorem chartedField_congr_off_tree (V : F.GaugeField F.top)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : ∀ z i, ¬ IsAxialTreeBond ((z, i) : F.Site F.depth × Fin 4) → w z i = w' z i) :
    chartedField w V = chartedField w' V := by
  funext x i
  unfold chartedField
  by_cases hc : IsCrossingBond ((x, i) : F.Site F.depth × Fin 4)
  · have : ¬ IsAxialTreeBond ((x, i) : F.Site F.depth × Fin 4) := fun ht => ht.1 hc
    simp only [if_pos hc, h x i this]
  · by_cases ht : IsAxialTreeBond ((x, i) : F.Site F.depth × Fin 4)
    · simp only [if_neg hc, if_pos ht]
    · simp only [if_neg hc, if_neg ht, h x i ht]
abbrev _root_.YangMills.SharedProofs.p9062 := @chartedField_congr_off_tree
private theorem isAdmissibleChartPoint_of_small (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) {L : ℕ}
    {σA s₁ e : ℝ} (hF : IsBlockTorus L F) (hL : Odd L)
    (he0 : 0 ≤ e) (he : e ≤ 1 / (64 * (L : ℝ))) (hs₁ : 0 ≤ s₁) (hlt : s₁ + 8 * e < σA)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e) (hV : IsSmallCurvature s₁ V) :
    IsAdmissibleChartPoint L σA w V := by
  classical
  obtain ⟨hFL, n, hn, hext⟩ := hF
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hext i]; omega
  have hall := hcov F hodd fun i => by have := hs i; omega
  have hchord : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F) := fun d hd => by
    have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
    simp [chordBonds, innerBonds, hall, hd]
  have hLp : (1 : ℝ) ≤ L := by exact_mod_cast hL.pos
  have he4 : e ≤ 1 / 4 := by
    refine he.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨fun b hb => (hw b hb).trans he, fun p hp => ?_⟩
  set w' : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun z i => if IsAxialTreeBond ((z, i) : F.Site F.depth × Fin 4) then 0 else w z i with hw'
  have hcf : chartedField w V = chartedField w' V := chartedField_congr_off_tree V fun z i ht => by simp [hw', ht]
  rw [hcf]
  have hcold : IsCold (finiteCells F) F.top s₁ V := fun p hp => by
    simp only [innerPlaquettes, Finset.mem_filter] at hp
    exact hV p hp.2.1
  have hmem : p ∈ innerPlaquettes (finiteCells F) F.depth := by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hall _, hp, fun y _ => hall y⟩
  have hcur := GaugeFixing.plaquetteDefect_chartedField_le hs hodd (finiteCells F) V s₁ e hs₁ hcold w' he4 (fun d _ => by
    by_cases ht : IsAxialTreeBond (d.1, d.2)
    · have : w' d.1 d.2 = 0 := by simp [hw', ht]
      rw [this]
      simpa using he0
    · have : w' d.1 d.2 = w d.1 d.2 := by simp [hw', ht]
      rw [this]
      exact hw (d.1, d.2) (hchord _ ht)) p hmem
  linarith
abbrev _root_.YangMills.SharedProofs.p28958 := @isAdmissibleChartPoint_of_small
private theorem cellSupDist_add_le (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell) (g : Fin 4 → ℤ) (R : ℕ)
    (hg : ∀ i, |g i| ≤ (R : ℤ)) : cellSupDist (Y + siteOfCoords F.top g) Y ≤ R := by apply _root_.YangMills.SharedProofs.p92070 <;> assumption
private theorem cellSupDist_add_unitStep_le (hs : ∀ i, 2 ≤ F.extent i) (y : F.Cell) (μ : Fin 4) :
    cellSupDist (y + unitStep F.top μ) y ≤ 1 := by
  refine cellSupDist_add_le hs y _ 1 fun i => ?_
  by_cases h : i = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
private theorem isSmallCurvature_leftTranslate {Y : F.Cell} {R : ℕ} {sT s₁ : ℝ} (hs : ∀ i, 2 ≤ F.extent i)
    (V : F.GaugeField F.top) (A v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (hV : IsSmallCurvature s₁ V) (hsT : 4 * sT < s₁)
    (hA : ∀ y i, cellSupDist y Y ≤ R + 2 → V y i = expUnit (A y i) ∧ ‖A y i‖ ≤ sT)
    (hv : ∀ y i, v y i = 0 ∨ (cellSupDist y Y ≤ R ∧ v y i = -A y i))
    (ϑ : F.Site F.top → Fin 4 → ℝ) (hϑ : ∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) :
    IsSmallCurvature s₁ (leftTranslate (fun y i => ϑ y i • v y i) V) := by
  classical
  have hp0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have tri := fun x y z => CellSums.cellSupDist_triangle (F := F) hp0 x y z
  rintro ⟨x, μ, ν⟩ hp
  set U := leftTranslate (fun y i => ϑ y i • v y i) V with hU
  by_cases hall : v x μ = 0 ∧ v (x + unitStep F.top μ) ν = 0 ∧ v (x + unitStep F.top ν) μ = 0 ∧ v x ν = 0
  · obtain ⟨h1, h2, h3, h4⟩ := hall
    have := hV (x, μ, ν) hp
    unfold plaquetteDefect at this ⊢
    rw [plaquetteHolonomy_eq_product] at this ⊢
    simpa [hU, leftTranslate, h1, h2, h3, h4, expUnit_zero_eq_one] using this
  · have hnear : cellSupDist x Y ≤ R + 1 := by
      by_contra hcon
      apply hall
      have key : ∀ y i, R < cellSupDist y Y → v y i = 0 := fun y i hy => (hv y i).resolve_right fun h => by omega
      have d1 := cellSupDist_add_unitStep_le hs x μ
      have d2 := cellSupDist_add_unitStep_le hs x ν
      have c1 := CellSums.cellSupDist_comm (x + unitStep F.top μ) x
      have c2 := CellSums.cellSupDist_comm (x + unitStep F.top ν) x
      have t1 := tri x (x + unitStep F.top μ) Y
      have t2 := tri x (x + unitStep F.top ν) Y
      exact ⟨key _ _ (by omega), key _ _ (by omega), key _ _ (by omega), key _ _ (by omega)⟩
    have hnear' : ∀ y, cellSupDist y x ≤ 1 → cellSupDist y Y ≤ R + 2 := fun y hy => by
      have := tri y x Y
      omega
    have bond : ∀ y i, cellSupDist y Y ≤ R + 2 → ‖((U y i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ sT := by
      intro y i hy
      obtain ⟨e1, e2⟩ := hA y i hy
      have hval : U y i = expUnit ((1 - (if v y i = 0 then 1 else ϑ y i)) • (A y i) +
          (if v y i = 0 then 1 else 0) • (A y i)) := by
        rcases hv y i with h0 | ⟨-, h1⟩
        · simp [hU, leftTranslate, h0, expUnit_zero_eq_one, e1]
        · by_cases h0 : v y i = 0
          · simp [hU, leftTranslate, h0, expUnit_zero_eq_one, e1]
          · have e3 : ϑ y i • v y i = (-ϑ y i) • A y i := by
              rw [h1, smul_neg]
              exact (neg_smul _ _).symm
            have e4 := expUnit_smul_mul_smul (-ϑ y i) 1 (A y i)
            rw [one_smul] at e4
            simp only [hU, leftTranslate, e3, if_neg h0, add_zero, zero_smul]
            rw [e1, e4]
            congr 2
            ring
      rw [hval]
      refine (norm_expUnit_sub_one_le' _).trans ?_
      by_cases h0 : v y i = 0
      · simpa [h0] using e2
      · simp only [if_neg h0, zero_smul, add_zero, norm_smul, Real.norm_eq_abs]
        have h1 := hϑ y i
        rw [abs_of_nonneg (by linarith)]
        have h2 := norm_nonneg (A y i)
        nlinarith
    have b1 := bond x μ (hnear' x (by simp [cellSupDist]))
    have b2 := bond (x + unitStep F.top μ) ν (hnear' _ (cellSupDist_add_unitStep_le hs x μ))
    have b3 := bond (x + unitStep F.top ν) μ (hnear' _ (cellSupDist_add_unitStep_le hs x ν))
    have b4 := bond x ν (hnear' x (by simp [cellSupDist]))
    unfold plaquetteDefect
    rw [plaquetteHolonomy_eq_product]
    have m1 := norm_mul_sub_one_le (U x μ * U (x + unitStep F.top μ) ν * (U (x + unitStep F.top ν) μ)⁻¹) (U x ν)⁻¹
    have m2 := norm_mul_sub_one_le (U x μ * U (x + unitStep F.top μ) ν) (U (x + unitStep F.top ν) μ)⁻¹
    have m3 := norm_mul_sub_one_le (U x μ) (U (x + unitStep F.top μ) ν)
    rw [norm_inv_sub_one] at m1 m2
    linarith
private theorem exp_neg_max_le (δ : ℝ) (hδ : 0 ≤ δ) (D d : ℕ) :
    Real.exp (-(δ * (max D d : ℕ))) ≤ Real.exp (-(δ / 2 * D)) * Real.exp (-(δ / 2 * d)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : (D : ℝ) ≤ (max D d : ℕ) := by exact_mod_cast le_max_left _ _
  have h2 : (d : ℝ) ≤ (max D d : ℕ) := by exact_mod_cast le_max_right _ _
  nlinarith
abbrev _root_.YangMills.SharedProofs.p848 := @exp_neg_max_le
set_option maxHeartbeats 2000000 in
theorem hessianEntriesNearTrivialTop_holds (hE : ChartResponse.HessianEntryLipschitz)
    (hT : ChartResponse.HessianEntryAgreeOnTwoTori)
    (hD : ColdStepAtMirrorFrames.decaySumOnTorusStatement) (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) :
    HessianEntriesNearTrivialTop := by
  intro a L c ha hL hL0 hc s₁ e₀ ϱ hs₁ he₀ hϱ hroom hcold
  obtain ⟨C₁, hC₁, hmove⟩ := hE a L c ha hL hL0 hc
  obtain ⟨C₂, hC₂, htwo⟩ := hT a L c ha hL hL0 hc ϱ hϱ
  have hδ : 0 < c.δ₁ := hc.positivity.1
  obtain ⟨S, hS⟩ := hD L (c.δ₁ / 2) hL (by positivity)
  have hS0 : 0 ≤ S ∨ True := Or.inr trivial
  refine ⟨C₁ * (|S| + 4 * |S|) + C₂ + 1, by positivity, ?_⟩
  intro F F' w V A Y Y' R sT sW p q p' q' hR hF hF' ht hext hext' hp hq hp' hq' hsT hsT4 hsW hV hw hA hwY hmatch hd hd'
  classical
  obtain ⟨hFL, n, hn, hsd⟩ := id hF
  obtain ⟨hFL', n', hn', hsd'⟩ := id hF'
  have hodd : Odd F.blockSide := hFL ▸ hL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsd i]; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hsd' i]; omega
  set Bt : Finset (F.Site F.depth × Fin 4) :=
    (chordBonds (finiteCells F)).filter fun b => cellSupDist (enclosingCell b.1) Y ≤ R with hBt
  set Bn : Finset (F.Site F.top × Fin 4) :=
    (finiteCells F ×ˢ (Finset.univ : Finset (Fin 4))).filter fun b => cellSupDist b.1 Y ≤ R with hBn
  set u : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i => if (z, i) ∈ Bt then -w z i else 0 with hu
  set v : F.Site F.top → Fin 4 → imaginaryQuaternions := fun y i => if (y, i) ∈ Bn then -A y i else 0 with hv
  have hv' : ∀ y i, v y i = 0 ∨ (cellSupDist y Y ≤ R ∧ v y i = -A y i) := by
    intro y i
    by_cases h : (y, i) ∈ Bn
    · right
      exact ⟨(Finset.mem_filter.1 h).2, by simp [hv, h]⟩
    · left
      simp [hv, h]
  have hcoldϑ := fun ϑ hϑ => isSmallCurvature_leftTranslate (Y := Y) (R := R) hs V A v hV hsT4 hA hv' ϑ hϑ
  have hbig : e₀ ≤ e₀ + 2 * ϱ := by linarith
  have hpts : ∀ (θ : F.Site F.depth → Fin 4 → ℝ) (ϑ : F.Site F.top → Fin 4 → ℝ), (∀ z i, 0 ≤ θ z i ∧ θ z i ≤ 1) →
      (∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) →
      IsAdmissibleChartPoint L c.σA (fun z i => w z i + θ z i • u z i) (leftTranslate (fun y i => ϑ y i • v y i) V) := by
    intro θ ϑ hθ hϑ
    refine isAdmissibleChartPoint_of_small hcov hF hL (by linarith) hroom hs₁.le hcold _ _ (fun b hb => ?_) (hcoldϑ ϑ hϑ)
    by_cases h : (b.1, b.2) ∈ Bt
    · have e : w b.1 b.2 + θ b.1 b.2 • u b.1 b.2 = (1 - θ b.1 b.2) • w b.1 b.2 := by
        simp only [hu, if_pos h]
        module
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hθ b.1 b.2).2])]
      have h1 := hw b hb
      have h2 := hθ b.1 b.2
      have h3 := norm_nonneg (w b.1 b.2)
      nlinarith
    · simp only [hu, if_neg h, smul_zero, add_zero]
      exact (hw b hb).trans hbig
  have hub : ∀ b, b ∉ Bt → u b.1 b.2 = 0 := fun b hb => by simp [hu, hb]
  have hvb : ∀ b, b ∉ Bn → v b.1 b.2 = 0 := fun b hb => by simp [hv, hb]
  have hstep := hmove F w u V v Bt Bn p q hF hp hq hub hvb hpts
  set w₁ : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun z i => w z i + u z i with hw₁
  set V₁ : F.GaugeField F.top := leftTranslate v V with hV₁
  have hV₁cold : IsSmallCurvature s₁ V₁ := by
    have := hcoldϑ (fun _ _ => 1) (fun _ _ => ⟨zero_le_one, le_rfl⟩)
    simpa [hV₁] using this
  have hw₁size : ∀ b ∈ chordBonds (finiteCells F), ‖w₁ b.1 b.2‖ ≤ e₀ := by
    intro b hb
    by_cases h : (b.1, b.2) ∈ Bt
    · simp only [hw₁, hu, if_pos h, add_neg_cancel, norm_zero]
      exact he₀
    · simp only [hw₁, hu, if_neg h, add_zero]
      exact hw b hb
  have hmoved : ∀ {G : BlockFrame} (p₁ q₁ : G.Site G.depth × Fin 4 × imaginaryQuaternions)
      (w₂ : G.Site G.depth → Fin 4 → imaginaryQuaternions) (s u' : ℝ), ‖p₁.2.2‖ = 1 → ‖q₁.2.2‖ = 1 →
      0 ≤ s → s ≤ ϱ → 0 ≤ u' → u' ≤ ϱ → ∀ z i, ‖w₂ z i‖ ≤ ‖shiftTwice p₁ q₁ 0 0 w₂ z i‖ + 0 →
      ∀ (ε : ℝ), ‖w₂ z i‖ ≤ ε → ‖shiftTwice p₁ q₁ s u' w₂ z i‖ ≤ ε + 2 * ϱ := by
    intro G p₁ q₁ w₂ s u' hp₁ hq₁ h0 h1 h2 h3 z i _ ε hε
    simp only [shiftTwice, DirectionalDerivatives.shiftCoordinates]
    have b1 : ‖directionCoordinate (Sum.inl p₁ : ChartDirection G) z i‖ ≤ 1 := by
      simp only [directionCoordinate]
      split_ifs
      · exact hp₁.le
      · simp
    have b2 : ‖directionCoordinate (Sum.inl q₁ : ChartDirection G) z i‖ ≤ 1 := by
      simp only [directionCoordinate]
      split_ifs
      · exact hq₁.le
      · simp
    have c1 : ‖s • directionCoordinate (Sum.inl p₁ : ChartDirection G) z i‖ ≤ ϱ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith [norm_nonneg (directionCoordinate (Sum.inl p₁ : ChartDirection G) z i)]
    have c2 : ‖u' • directionCoordinate (Sum.inl q₁ : ChartDirection G) z i‖ ≤ ϱ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h2]
      nlinarith [norm_nonneg (directionCoordinate (Sum.inl q₁ : ChartDirection G) z i)]
    calc _ ≤ ‖w₂ z i + s • directionCoordinate (Sum.inl p₁ : ChartDirection G) z i‖ +
            ‖u' • directionCoordinate (Sum.inl q₁ : ChartDirection G) z i‖ :=
          norm_add_le _ _
      _ ≤ ‖w₂ z i‖ + ‖s • directionCoordinate (Sum.inl p₁ : ChartDirection G) z i‖ +
            ‖u' • directionCoordinate (Sum.inl q₁ : ChartDirection G) z i‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ε + 2 * ϱ := by linarith
  have hroom' : ∀ s u', 0 ≤ s → s ≤ ϱ → 0 ≤ u' → u' ≤ ϱ →
      IsAdmissibleChartPoint L c.σA (shiftTwice p q s u' w₁) V₁ ∧
        IsAdmissibleChartPoint L c.σA (shiftTwice p' q' s u' (fun _ _ => 0)) (uniformField F' F'.top) := by
    intro s u' h0 h1 h2 h3
    constructor
    · refine isAdmissibleChartPoint_of_small hcov hF hL (by linarith) hroom hs₁.le hcold _ _ (fun b hb => ?_) hV₁cold
      exact hmoved p q w₁ s u' hp hq h0 h1 h2 h3 b.1 b.2 (by simp [shiftTwice, DirectionalDerivatives.shiftCoordinates]) e₀ (hw₁size b hb)
    · have hflat : IsSmallCurvature s₁ (uniformField F' F'.top) := by
        intro p₁ _
        have : plaquetteDefect (uniformField F' F'.top) p₁ = 0 := by
          simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, ColdStepAtMirrorFrames.uniformField]
        rw [this]
        exact hs₁
      refine isAdmissibleChartPoint_of_small hcov hF' hL (by linarith) hroom hs₁.le hcold _ _ (fun b _ => ?_) hflat
      refine (hmoved p' q' (fun _ _ => 0) s u' hp' hq' h0 h1 h2 h3 b.1 b.2
        (by simp [shiftTwice, DirectionalDerivatives.shiftCoordinates]) 0 (by simp)).trans ?_
      linarith
  have hag : AgreeOnBall (finiteCells F) V₁ (finiteCells F') (uniformField F' F'.top) Y Y' R := by
    refine ⟨fun i => Or.inr ?_, fun i => Or.inr ?_, fun h _ => ?_, fun b hb => ?_⟩
    · have := hext i
      omega
    · have := hext' i
      omega
    · exact ⟨fun _ => BlockOffsets.mem_finiteCells hs' _, fun _ => BlockOffsets.mem_finiteCells hs _⟩
    · have hbd : cellSupDist (Y + siteOfCoords F.top b.1) Y ≤ R := cellSupDist_add_le hs Y b.1 R hb.1
      have hmem : (Y + siteOfCoords F.top b.1, b.2) ∈ Bn := by
        simp only [hBn, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        exact ⟨BlockOffsets.mem_finiteCells hs _, hbd⟩
      obtain ⟨e1, -⟩ := hA (Y + siteOfCoords F.top b.1) b.2 (by omega)
      have e2 := expUnit_smul_mul_smul (-1) 1 (A (Y + siteOfCoords F.top b.1) b.2)
      rw [one_smul] at e2
      have e3 : (-1 : ℝ) • A (Y + siteOfCoords F.top b.1) b.2 = -A (Y + siteOfCoords F.top b.1) b.2 := by
        module
      rw [e3] at e2
      simp only [hV₁, leftTranslate, hv, if_pos hmem, ColdStepAtMirrorFrames.uniformField]
      rw [e1, e2]
      simp [expUnit_zero_eq_one]
  have hw₁box : ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius R h → o ∈ centredCube L →
      fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
      w₁ (fineBondAt Y h o i).1 i = (fun _ _ => (0 : imaginaryQuaternions)) (fineBondAt Y' h o i).1 i ∧
      directionCoordinate (Sum.inl p) (fineBondAt Y h o i).1 i = directionCoordinate (Sum.inl p') (fineBondAt Y' h o i).1 i ∧
      directionCoordinate (Sum.inl q) (fineBondAt Y h o i).1 i = directionCoordinate (Sum.inl q') (fineBondAt Y' h o i).1 i := by
    intro h o i hh ho hmem
    refine ⟨?_, hmatch h o i hh ho hmem⟩
    have hcell : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h :=
      BlockOffsets.enclosingCell_offset hodd hs _ o (by rw [hFL]; exact ho)
    have hin : ((fineBondAt Y h o i).1, i) ∈ Bt := by
      simp only [hBt, Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      rw [hcell]
      exact cellSupDist_add_le hs Y h R hh
    simp [hw₁, hu, hin]
  have hlast := htwo F F' w₁ (fun _ _ => 0) V₁ (uniformField F' F'.top) Y Y' R p q p' q' hR hF hF' ht hp hq hp' hq'
    hroom' hag hw₁box hd hd'
  set D := cellSupDist (enclosingCell p.1) (enclosingCell q.1) with hDd
  set E := Real.exp (-(c.δ₁ / 2 * D)) with hEd
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨-, -, hS1, hS2⟩ : ∃ _ : True, ∃ _ : True,
      (∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1.1) (enclosingCell p.1) : ℝ))) ≤ S) ∧
      (∑ z' ∈ finiteCells F, Real.exp (-(c.δ₁ / 2 * (cellSupDist z' (enclosingCell p.1) : ℝ))) ≤ S) :=
    ⟨trivial, trivial, (hS F n hFL (by omega) hsd (enclosingCell p.1)).1, (hS F n hFL (by omega) hsd (enclosingCell p.1)).2⟩
  have hsumT : ∑ b ∈ Bt, C₁ * Real.exp (-(c.δ₁ * (max D (cellSupDist (enclosingCell p.1) (enclosingCell b.1)) : ℕ))) *
      ‖u b.1 b.2‖ ≤ C₁ * sW * E * |S| := by
    have h1 : ∀ b ∈ Bt, C₁ * Real.exp (-(c.δ₁ * (max D (cellSupDist (enclosingCell p.1) (enclosingCell b.1)) : ℕ))) *
        ‖u b.1 b.2‖ ≤ C₁ * sW * E * Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) (enclosingCell p.1) : ℝ))) := by
      intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hub' : ‖u b.1 b.2‖ ≤ sW := by
        have e : u b.1 b.2 = -w b.1 b.2 := by
          simp only [hu]
          rw [if_pos hb]
        rw [e, norm_neg]
        exact hwY b hb'.1 hb'.2
      have h2 := exp_neg_max_le c.δ₁ hδ.le D (cellSupDist (enclosingCell p.1) (enclosingCell b.1))
      rw [CellSums.cellSupDist_comm (enclosingCell p.1) (enclosingCell b.1)] at h2
      rw [CellSums.cellSupDist_comm (enclosingCell p.1) (enclosingCell b.1)]
      calc _ ≤ C₁ * (E * Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) (enclosingCell p.1) : ℝ)))) * sW := by
            gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    have h3 : ∑ b ∈ Bt, Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) (enclosingCell p.1) : ℝ))) ≤ S := by
      refine le_trans ?_ hS1
      rw [Finset.sum_coe_sort (chordBonds (finiteCells F))
        (fun b => Real.exp (-(c.δ₁ / 2 * (cellSupDist (enclosingCell b.1) (enclosingCell p.1) : ℝ))))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
    have h4 : S ≤ |S| := le_abs_self S
    have : 0 ≤ C₁ * sW * E := by positivity
    exact mul_le_mul_of_nonneg_left (h3.trans h4) this
  have hsumN : ∑ b ∈ Bn, C₁ * Real.exp (-(c.δ₁ * (max D (cellSupDist (enclosingCell p.1) b.1) : ℕ))) * ‖v b.1 b.2‖ ≤
      C₁ * sT * E * (4 * |S|) := by
    have h1 : ∀ b ∈ Bn, C₁ * Real.exp (-(c.δ₁ * (max D (cellSupDist (enclosingCell p.1) b.1) : ℕ))) * ‖v b.1 b.2‖ ≤
        C₁ * sT * E * Real.exp (-(c.δ₁ / 2 * (cellSupDist b.1 (enclosingCell p.1) : ℝ))) := by
      intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hvb' : ‖v b.1 b.2‖ ≤ sT := by
        have e : v b.1 b.2 = -A b.1 b.2 := by
          simp only [hv]
          rw [if_pos hb]
        rw [e, norm_neg]
        exact (hA b.1 b.2 (by omega)).2
      have h2 := exp_neg_max_le c.δ₁ hδ.le D (cellSupDist (enclosingCell p.1) b.1)
      rw [CellSums.cellSupDist_comm (enclosingCell p.1) b.1] at h2
      rw [CellSums.cellSupDist_comm (enclosingCell p.1) b.1]
      calc _ ≤ C₁ * (E * Real.exp (-(c.δ₁ / 2 * (cellSupDist b.1 (enclosingCell p.1) : ℝ)))) * sT := by gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    have h3 : ∑ b ∈ Bn, Real.exp (-(c.δ₁ / 2 * (cellSupDist b.1 (enclosingCell p.1) : ℝ))) ≤ 4 * S := by
      have h5 : ∑ b ∈ Bn, Real.exp (-(c.δ₁ / 2 * (cellSupDist b.1 (enclosingCell p.1) : ℝ))) ≤
          ∑ b ∈ finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)),
            Real.exp (-(c.δ₁ / 2 * (cellSupDist b.1 (enclosingCell p.1) : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
      refine h5.trans ?_
      rw [Finset.sum_product]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      push_cast
      linarith
    have h4 : S ≤ |S| := le_abs_self S
    have : 0 ≤ C₁ * sT * E := by positivity
    exact mul_le_mul_of_nonneg_left (h3.trans (by linarith)) this
  have hfirst : |chartMixedDeriv a w₁ V₁ ![Sum.inl p, Sum.inl q] - chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]| ≤
      C₁ * sW * E * |S| + C₁ * sT * E * (4 * |S|) := hstep.trans (add_le_add hsumT hsumN)
  have hfin := abs_sub_le (chartMixedDeriv a w V ![Sum.inl p, Sum.inl q]) (chartMixedDeriv a w₁ V₁ ![Sum.inl p, Sum.inl q])
    (chartMixedDeriv a (fun _ _ => 0) (uniformField F' F'.top) ![Sum.inl p', Sum.inl q'])
  rw [abs_sub_comm (chartMixedDeriv a w V ![Sum.inl p, Sum.inl q])
    (chartMixedDeriv a w₁ V₁ ![Sum.inl p, Sum.inl q])] at hfin
  refine hfin.trans ?_
  have hR0 := Real.exp_pos (-(c.δ₁ / 16 * (R : ℝ)))
  have hSa := abs_nonneg S
  have e1 : C₁ * sW * E * |S| + C₁ * sT * E * (4 * |S|) ≤ (C₁ * (|S| + 4 * |S|) + C₂ + 1) * (sT + sW) * E := by
    have : 0 ≤ (sT + sW) * E := by positivity
    have h6 : 0 ≤ C₁ * |S| * sT * E := by positivity
    have h7 : 0 ≤ 4 * C₁ * |S| * sW * E := by positivity
    have h8 : 0 ≤ (C₂ + 1) * ((sT + sW) * E) := by positivity
    nlinarith
  have e2 : C₂ * Real.exp (-(c.δ₁ / 16 * R)) ≤ (C₁ * (|S| + 4 * |S|) + C₂ + 1) * Real.exp (-(c.δ₁ / 16 * R)) := by
    have : C₂ ≤ C₁ * (|S| + 4 * |S|) + C₂ + 1 := by
      have : 0 ≤ C₁ * (|S| + 4 * |S|) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this hR0.le
  exact add_le_add (hfirst.trans e1) (hlast.trans e2)
end YangMills.Construction.ResponseInTheExpansion
end
