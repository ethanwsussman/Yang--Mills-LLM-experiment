import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalarProof
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOverTheCells
import YangMills.Construction.ResponseInTheExpansion.CoordinateOfASmallForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
open ColdStepAtMirrorFrames.BlockOffsets ColdStepAtMirrorFrames.SmallUnits
namespace SmallFormCoordinate
variable {F : BlockFrame}
private def bondSet (F : BlockFrame) : Finset (F.Site F.top × Fin 4) := finiteCells F ×ˢ Finset.univ
private theorem mem_bondSet (hs : ∀ i, 0 < F.extent i) (b : F.Site F.top × Fin 4) : b ∈ bondSet F :=
  Finset.mem_product.2 ⟨TopLevelSites.mem_finiteCells hs _, Finset.mem_univ _⟩
private theorem isSmallCurvature_leftTranslate {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) {s ε : ℝ}
    (hε : ∀ x i, ‖v x i‖ ≤ ε) (hs : 4 * ε < s) : IsSmallCurvature s (leftTranslate v (uniformField F j)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponse.isSmallCurvature_leftTranslate_uniform <;> assumption
private theorem norm_sub_sub_deriv_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ → E) (K : ℝ)
    (hp : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 p u)
    (hK : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖deriv (deriv p) u‖ ≤ K) : ‖p 1 - p 0 - deriv p 0‖ ≤ K := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 h0)
  have hdp : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt p (deriv p u) u := fun u hu =>
    ((hp u hu).differentiableAt (by norm_num)).hasDerivAt
  have hq : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (deriv p) (deriv (deriv p) u) u := by
    intro u hu
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ p) u := (hp u hu).fderiv_right (m := 2) (by norm_num)
    have e : deriv p = fun x => fderiv ℝ p x 1 := by
      funext x
      rfl
    have hd : DifferentiableAt ℝ (fun x => fderiv ℝ p x 1) u :=
      (h2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
    rw [← e] at hd
    exact hd.hasDerivAt
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hA : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖deriv p u - deriv p 0‖ ≤ K := by
    intro u hu
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv p) (f' := deriv (deriv p)) (C := K)
      (fun x hx => (hq x hx).hasDerivWithinAt) hK h0 hu
    have h3 : ‖u - 0‖ ≤ 1 := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hu.1]
      exact hu.2
    calc ‖deriv p u - deriv p 0‖ ≤ K * ‖u - 0‖ := this
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one K
  have hr : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun x => p x - x • deriv p 0) (deriv p u - deriv p 0)
      (Set.Icc (0 : ℝ) 1) u := by
    intro u hu
    have e1 : HasDerivAt (fun x : ℝ => x • deriv p 0) ((1 : ℝ) • deriv p 0) u := (hasDerivAt_id u).smul_const _
    rw [one_smul] at e1
    exact ((hdp u hu).sub e1).hasDerivWithinAt
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun x => p x - x • deriv p 0)
    (f' := fun u => deriv p u - deriv p 0) (C := K) hr hA h0 h1
  have e : p 1 - p 0 - deriv p 0 = p 1 - deriv p 0 - p 0 := by abel
  rw [e]
  simpa using this
abbrev _root_.YangMills.SharedProofs.p29740 := @norm_sub_sub_deriv_le
private theorem line_restriction_derivs {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (J : P → E) (v : P) (hJ : ContDiffAt ℝ 3 J 0) :
    ContDiffAt ℝ 3 (fun τ : ℝ => J (τ • v)) 0 ∧ deriv (fun τ : ℝ => J (τ • v)) 0 = fderiv ℝ J 0 v ∧
      deriv (deriv fun τ : ℝ => J (τ • v)) 0 = iteratedFDeriv ℝ 2 J 0 ![v, v] := by
  have hl : ContDiff ℝ 3 (fun τ : ℝ => τ • v) := contDiff_id.smul contDiff_const
  have hJ' : ContDiffAt ℝ 3 J ((0 : ℝ) • v) := by simpa using hJ
  have hline : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => τ • v) v τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const v
  have hev : ∀ᶠ y in 𝓝 (0 : P), DifferentiableAt ℝ J y :=
    (hJ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hcont : Filter.Tendsto (fun τ : ℝ => τ • v) (𝓝 0) (𝓝 0) := by
    have := (hl.continuous.tendsto (0 : ℝ))
    simpa using this
  have hev2 : ∀ᶠ τ in 𝓝 (0 : ℝ), DifferentiableAt ℝ J (τ • v) := hcont.eventually hev
  have hder : ∀ᶠ τ in 𝓝 (0 : ℝ), HasDerivAt (fun τ : ℝ => J (τ • v)) (fderiv ℝ J (τ • v) v) τ :=
    hev2.mono fun τ hτ => by
      have := hτ.hasFDerivAt.comp_hasDerivAt τ (hline τ)
      exact this
  have hd0 : HasDerivAt (fun τ : ℝ => J (τ • v)) (fderiv ℝ J 0 v) 0 := by
    have := hder.self_of_nhds
    simpa using this
  refine ⟨hJ'.comp (0 : ℝ) hl.contDiffAt, hd0.deriv, ?_⟩
  have e1 : deriv (fun τ : ℝ => J (τ • v)) =ᶠ[𝓝 0] fun τ => fderiv ℝ J (τ • v) v :=
    hder.mono fun τ hτ => hτ.deriv
  rw [e1.deriv_eq]
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ J) 0 := hJ.fderiv_right (m := 2) (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ J) ((0 : ℝ) • v) := by
    simpa using h2.differentiableAt (by norm_num)
  have h3 := hd2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
  have h4 : HasDerivAt (fun τ : ℝ => fderiv ℝ J (τ • v) v) ((fderiv ℝ (fderiv ℝ J) 0 v) v) 0 := by
    have := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using this
  rw [h4.deriv, iteratedFDeriv_two_apply]
  simp
abbrev _root_.YangMills.SharedProofs.p62688 := @line_restriction_derivs
private theorem eq_smul_of_unit_eigen {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →ₗ[ℝ] E)
    (r : E → ℝ) (hT : ∀ X : E, ‖X‖ = 1 → T X = r X • X) (X₀ : E) (hX₀ : ‖X₀‖ = 1) (v : E) :
    T v = r X₀ • v := by
  have hne : ∀ X : E, ‖X‖ = 1 → X ≠ 0 := fun X hX h => by
    rw [h, norm_zero] at hX
    exact zero_ne_one hX
  have key : ∀ X : E, ‖X‖ = 1 → r X = r X₀ := by
    intro X hX
    by_cases h1 : X = X₀
    · rw [h1]
    by_cases h2 : X = -X₀
    · have e1 : T X = r X₀ • X := by
        rw [h2, map_neg, hT X₀ hX₀, smul_neg]
      have e3 : (r X₀ - r X) • X = 0 := by
        rw [sub_smul, ← e1, ← hT X hX, sub_self]
      rcases smul_eq_zero.1 e3 with h | h
      · linarith
      · exact absurd h (hne X hX)
    · have hw : X + X₀ ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
      have hw0 : ‖X + X₀‖ ≠ 0 := norm_ne_zero_iff.2 hw
      set Z : E := ‖X + X₀‖⁻¹ • (X + X₀) with hZ
      have hZ1 : ‖Z‖ = 1 := by
        rw [hZ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
      have e1 := hT Z hZ1
      have e2 : T Z = ‖X + X₀‖⁻¹ • (r X • X + r X₀ • X₀) := by
        rw [hZ, map_smul, map_add, hT X hX, hT X₀ hX₀]
      have e3 : r X • X + r X₀ • X₀ = r Z • (X + X₀) := by
        have e4 : ‖X + X₀‖⁻¹ • (r X • X + r X₀ • X₀) = ‖X + X₀‖⁻¹ • (r Z • (X + X₀)) := by
          rw [← e2, smul_comm, ← hZ]
          exact e1
        exact smul_right_injective _ (inv_ne_zero hw0) e4
      have e5 : (r X - r Z) • X = (r Z - r X₀) • X₀ := by
        rw [smul_add] at e3
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, e3]
        abel
      have hn : |r X - r Z| = |r Z - r X₀| := by
        have := congrArg norm e5
        rw [norm_smul, norm_smul, hX, hX₀, mul_one, mul_one] at this
        simpa using this
      have hzero : r X - r Z = 0 := by
        by_contra hne0
        rcases abs_eq_abs.1 hn with h | h
        · rw [← h] at e5
          exact h1 (smul_right_injective _ hne0 e5)
        · have hne1 : r Z - r X₀ ≠ 0 := by
            intro h0
            apply hne0
            rw [h, h0]
            simp
          have e6 : (r Z - r X₀) • X = (r Z - r X₀) • (-X₀) := by
            have e7 := e5
            rw [h, neg_smul] at e7
            rw [smul_neg, ← e7, neg_neg]
          exact h2 (smul_right_injective _ hne1 e6)
      have hzero2 : r Z - r X₀ = 0 := by
        rw [hzero, zero_smul] at e5
        rcases smul_eq_zero.1 e5.symm with h | h
        · exact h
        · exact absurd h (hne X₀ hX₀)
      linarith
  by_cases hv : v = 0
  · rw [hv, map_zero, smul_zero]
  · have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    set X : E := ‖v‖⁻¹ • v with hXd
    have hX1 : ‖X‖ = 1 := by
      rw [hXd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0]
    have ev : v = ‖v‖ • X := by
      rw [hXd, smul_smul, mul_inv_cancel₀ hv0, one_smul]
    have e1 := hT X hX1
    rw [key X hX1] at e1
    calc T v = ‖v‖ • T X := by
          nth_rewrite 1 [ev]
          rw [map_smul]
      _ = r X₀ • (‖v‖ • X) := by rw [e1, smul_comm]
      _ = r X₀ • v := by rw [← ev]
abbrev _root_.YangMills.SharedProofs.p34198 := @eq_smul_of_unit_eigen
section Parameters
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem estimatesAt_of (hc : c.Admissible a L) (hF : IsBlockTorus L F) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) : c.EstimatesAt a c.σA W :=
  hc.estimates F c.σA W hF hc.positivity.2.2.2.1 le_rfl hW
private theorem contDiffThree_coordinate (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) : ContDiffThreeAlongBonds (torusCoordinate a c.ρA b) W := fun k cc X =>
  (((estimatesAt_of hc hF hW).coordinates b hb).1 k cc X).contDiffAt
private theorem norm_bondDeriv_le (hc : c.Admissible a L) (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top} (hW : IsSmallCurvature c.σA W) {k : ℕ}
    (cc : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k) (hX : AreUnitVectors X) :
    ‖bondDeriv (torusCoordinate a c.ρA b) W cc X‖ ≤
      c.N k * Real.exp (-c.δ₁ * bondListDistance (enclosingCell b.1) cc) :=
  ((estimatesAt_of hc hF hW).coordinates b hb).2 k cc X hk hX
private def halfDecay (δ : ℝ) (Y : F.Cell) (e : ↥(bondSet F)) : ℝ :=
  Real.exp (-(δ / 2 * (cellSupDist Y e.1.1 : ℝ)))
private theorem halfDecay_nonneg (δ : ℝ) (Y : F.Cell) (e : ↥(bondSet F)) : 0 ≤ halfDecay δ Y e :=
  (Real.exp_pos _).le
private theorem sum_halfDecay_le {δ S : ℝ}
    (hS : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
      ∑ z ∈ A, Real.exp (-(δ / 2 * siteSupDist y z)) ≤ S) (Y : F.Cell) :
    ∑ e, halfDecay δ Y e ≤ 4 * S := by
  classical
  unfold halfDecay
  rw [Finset.sum_coe_sort (bondSet F) fun e => Real.exp (-(δ / 2 * (cellSupDist Y e.1 : ℝ)))]
  unfold bondSet
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := hS F F.top Y (finiteCells F)
  have e : ∑ z ∈ finiteCells F, Real.exp (-(δ / 2 * (cellSupDist Y z : ℝ))) =
      ∑ z ∈ finiteCells F, Real.exp (-(δ / 2 * siteSupDist Y z)) := rfl
  rw [e]
  norm_num
  linarith
private theorem norm_second_deriv_le (hJ : FormCompositionJet) (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {S : ℝ} (hS : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
      ∑ z ∈ A, Real.exp (-(c.δ₁ / 2 * siteSupDist y z)) ≤ S)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) (v : ↥(bondSet F) → imaginaryQuaternions) {s : ℝ} (hs : 0 ≤ s)
    (hv : ∀ e, ‖v e‖ ≤ s) :
    ‖iteratedFDeriv ℝ 2 (formComposition (bondSet F) (torusCoordinate a c.ρA b) W) 0 ![v, v]‖ ≤
      c.N 2 * (4 * S) ^ 2 * s ^ 2 := by
  classical
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hN : 0 < c.N 2 := hc.positivity.2.2.2.2.2.1 2
  set Y : F.Cell := enclosingCell b.1 with hY
  have hjet := (hJ imaginaryQuaternions F F.top (bondSet F) (torusCoordinate a c.ρA b) W
      (contDiffThree_coordinate hc hF hb hW)).2.2 2
    (fun cc => c.N 2 * (halfDecay c.δ₁ Y (cc 0) * halfDecay c.δ₁ Y (cc 1))) (by norm_num)
    (fun cc => mul_nonneg hN.le (mul_nonneg (halfDecay_nonneg _ _ _) (halfDecay_nonneg _ _ _)))
    (fun cc X hX => by
      refine (norm_bondDeriv_le hc hF hb hW _ X (by norm_num) hX).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hN.le
      unfold halfDecay
      rw [← Real.exp_add, Real.exp_le_exp]
      have h0 : cellSupDist Y (cc 0).1.1 ≤ bondListDistance Y (fun l => (cc l).1) :=
        Finset.le_sup (f := fun l => cellSupDist Y ((fun l => (cc l).1) l).1) (Finset.mem_univ (0 : Fin 2))
      have h1 : cellSupDist Y (cc 1).1.1 ≤ bondListDistance Y (fun l => (cc l).1) :=
        Finset.le_sup (f := fun l => cellSupDist Y ((fun l => (cc l).1) l).1) (Finset.mem_univ (1 : Fin 2))
      have h0' : (cellSupDist Y (cc 0).1.1 : ℝ) ≤ bondListDistance Y (fun l => (cc l).1) := by exact_mod_cast h0
      have h1' : (cellSupDist Y (cc 1).1.1 : ℝ) ≤ bondListDistance Y (fun l => (cc l).1) := by exact_mod_cast h1
      nlinarith) ![v, v]
  refine hjet.trans ?_
  have hsum : ∑ e, halfDecay c.δ₁ Y e * ‖v e‖ ≤ 4 * S * s := by
    calc ∑ e, halfDecay c.δ₁ Y e * ‖v e‖ ≤ ∑ e, halfDecay c.δ₁ Y e * s :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hv e) (halfDecay_nonneg _ _ _)
      _ = (∑ e, halfDecay c.δ₁ Y e) * s := by rw [Finset.sum_mul]
      _ ≤ 4 * S * s := mul_le_mul_of_nonneg_right (sum_halfDecay_le hS Y) hs
  have hsq : ∑ cc : Fin 2 → ↥(bondSet F), c.N 2 * (halfDecay c.δ₁ Y (cc 0) * halfDecay c.δ₁ Y (cc 1)) *
      ∏ l, ‖(![v, v] : Fin 2 → ↥(bondSet F) → imaginaryQuaternions) l (cc l)‖ =
      c.N 2 * (∑ e, halfDecay c.δ₁ Y e * ‖v e‖) ^ 2 := by
    set f : ↥(bondSet F) → ℝ := fun e => halfDecay c.δ₁ Y e * ‖v e‖ with hf
    have h2 : ∑ cc : Fin 2 → ↥(bondSet F), f (cc 0) * f (cc 1) = (∑ e, f e) ^ 2 := by
      have := Finset.prod_univ_sum (fun _ : Fin 2 => (Finset.univ : Finset ↥(bondSet F))) (fun _ e => f e)
      rw [Fintype.piFinset_univ, Fin.prod_univ_two] at this
      simp only [Fin.prod_univ_two] at this
      rw [sq]
      exact this.symm
    rw [← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun cc _ => ?_
    rw [Fin.prod_univ_two]
    simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hsq]
  have h0 : 0 ≤ ∑ e, halfDecay c.δ₁ Y e * ‖v e‖ :=
    Finset.sum_nonneg fun e _ => mul_nonneg (halfDecay_nonneg _ _ _) (norm_nonneg _)
  calc c.N 2 * (∑ e, halfDecay c.δ₁ Y e * ‖v e‖) ^ 2 ≤ c.N 2 * (4 * S * s) ^ 2 := by
        gcongr
    _ = c.N 2 * (4 * S) ^ 2 * s ^ 2 := by ring
private theorem bondDeriv_eq_fderiv (hJ : FormCompositionJet) (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature c.σA W) (e : ↥(bondSet F)) (v : imaginaryQuaternions) :
    bondDeriv (torusCoordinate a c.ρA b) W ![e.1] ![v] =
      fderiv ℝ (formComposition (bondSet F) (torusCoordinate a c.ρA b) W) 0 (singleBondForm e v) := by
  have h := (hJ imaginaryQuaternions F F.top (bondSet F) (torusCoordinate a c.ρA b) W
    (contDiffThree_coordinate hc hF hb hW)).2.1 1 ![e] ![v] (by norm_num)
  rw [iteratedFDeriv_one_apply] at h
  have e1 : (fun l : Fin 1 => ((![e] : Fin 1 → ↥(bondSet F)) l).1) = ![e.1] := by
    funext l
    fin_cases l
    rfl
  rw [e1] at h
  rw [← h]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p502378 := @bondDeriv_eq_fderiv
private theorem bondDeriv_uniform_eq_smul (hFl : FlatCoordinatesScalar) (hJ : FormCompositionJet)
    (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {b : F.Site F.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hW : IsSmallCurvature c.σA (uniformField F F.top))
    (e : ↥(bondSet F)) (X v : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e.1] ![v] =
      flatCoefficient a c.ρA X b e.1 • v := by
  classical
  let T : imaginaryQuaternions →ₗ[ℝ] imaginaryQuaternions :=
    (fderiv ℝ (formComposition (bondSet F) (torusCoordinate a c.ρA b) (uniformField F F.top)) 0).toLinearMap ∘ₗ
      LinearMap.single ℝ (fun _ : ↥(bondSet F) => imaginaryQuaternions) e
  have hTv : ∀ v : imaginaryQuaternions,
      T v = bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e.1] ![v] := fun v => by
    rw [bondDeriv_eq_fderiv hJ hc hF hb hW]
    have e2 : (LinearMap.single ℝ (fun _ : ↥(bondSet F) => imaginaryQuaternions) e) v = singleBondForm e v := by
      unfold singleBondForm
      rw [LinearMap.coe_single]
    change fderiv ℝ _ 0 ((LinearMap.single ℝ (fun _ : ↥(bondSet F) => imaginaryQuaternions) e) v) = _
    rw [e2]
  have h := eq_smul_of_unit_eigen T (fun Y => flatCoefficient a c.ρA Y b e.1) (fun Y hY => by
    simp only [hTv]
    exact (hFl a L c hL hc F b e.1 Y hF hY).2) X hX v
  rw [← hTv, h]
abbrev _root_.YangMills.DeltaSharedProofs.p500538 := @bondDeriv_uniform_eq_smul
end Parameters
end SmallFormCoordinate
open SmallFormCoordinate in
theorem smallFormCoordinate (hFl : FlatCoordinatesScalar) (hJ : FormCompositionJet) (hS : ExpDecaySumBounded) :
    smallFormCoordinateStatement := by
  intro a L c hL hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hN2 : 0 < c.N 2 := hc.positivity.2.2.2.2.2.1 2
  obtain ⟨S, hS0, hSum⟩ := hS (c.δ₁ / 2) (by positivity)
  refine ⟨c.N 2 * (4 * S) ^ 2, c.σA / 16, by positivity, by positivity, ?_⟩
  intro F b D X s hF hb hX hs0 hs1 hD
  classical
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  set G := torusCoordinate a c.ρA b with hG
  set v : ↥(bondSet F) → imaginaryQuaternions := fun e => D e.1.1 e.1.2 with hv
  have hvs : ∀ e, ‖v e‖ ≤ s := fun e => hD _ _
  set P : ℝ → F.GaugeField F.top := fun u => leftTranslate (fun y i => u • D y i) (uniformField F F.top) with hP
  set p : ℝ → imaginaryQuaternions := fun u => G (P u) with hp
  have hcold : ∀ u ∈ Set.Icc (0 : ℝ) 1, IsSmallCurvature c.σA (P u) := fun u hu =>
    isSmallCurvature_leftTranslate _ (ε := s) (fun y i => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
      calc u * ‖D y i‖ ≤ 1 * s := mul_le_mul hu.2 (hD y i) (norm_nonneg _) zero_le_one
        _ = s := one_mul s) (by linarith)
  have hext : ∀ τ : ℝ, extendByZero (τ • v) = fun y i => τ • D y i := fun τ => by
    funext y i
    unfold extendByZero
    rw [dif_pos (mem_bondSet hs _)]
    rfl
  have hshift : ∀ u τ : ℝ, P (u + τ) = leftTranslate (extendByZero (τ • v)) (P u) := fun u τ => by
    rw [hext]
    funext y i
    simp only [hP, leftTranslate, uniformField, mul_one]
    rw [add_comm u τ, expUnit_add_smul]
  have hline : ∀ u : ℝ, (fun τ : ℝ => formComposition (bondSet F) G (P u) (τ • v)) = fun τ => p (u + τ) :=
    fun u => by
      funext τ
      simp only [hp, hshift, formComposition]
  have hstep : ∀ u ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 p u ∧
      ‖deriv (deriv p) u‖ ≤ c.N 2 * (4 * S) ^ 2 * s ^ 2 := by
    intro u hu
    have hW := hcold u hu
    obtain ⟨hc3, -, -⟩ := hJ imaginaryQuaternions F F.top (bondSet F) G (P u) (contDiffThree_coordinate hc hF hb hW)
    obtain ⟨l1, -, l3⟩ := line_restriction_derivs _ v hc3
    rw [hline u] at l1 l3
    constructor
    · have h1 : ContDiffAt ℝ 3 (fun x : ℝ => x - u) u := contDiffAt_id.sub contDiffAt_const
      have l1' : ContDiffAt ℝ 3 (fun τ => p (u + τ)) (u - u) := by simpa using l1
      have h2 := ContDiffAt.comp (g := fun τ => p (u + τ)) (f := fun x : ℝ => x - u) u l1' h1
      have e : (fun τ => p (u + τ)) ∘ (fun x : ℝ => x - u) = p := by
        funext x
        simp
      rwa [e] at h2
    · have e1 : deriv (fun τ => p (u + τ)) = fun τ => deriv p (u + τ) :=
        funext fun τ => deriv_comp_const_add p u τ
      rw [e1, deriv_comp_const_add (deriv p) u 0, add_zero] at l3
      rw [l3]
      exact norm_second_deriv_le hJ hc hF hSum hb hW v hs0 hvs
  have hflat : P 0 = uniformField F F.top := by
    funext y i
    simp only [hP, leftTranslate, zero_smul, uniformField, mul_one]
    exact expUnit_zero
  have hW0 : IsSmallCurvature c.σA (uniformField F F.top) := by
    rw [← hflat]
    exact hcold 0 (by simp)
  have hp0 : p 0 = 0 := by
    simp only [hp, hflat, hG]
    exact (hFl a L c hL hc F b (0, 0) X hF hX).1
  have hp1 : p 1 = torusCoordinate a c.ρA b (leftTranslate D (uniformField F F.top)) := by
    simp only [hp, hP, one_smul, hG]
  have hd0 : deriv p 0 = flatLinearPart a c.ρA X b D := by
    obtain ⟨hc3, -, -⟩ := hJ imaginaryQuaternions F F.top (bondSet F) G (uniformField F F.top)
      (contDiffThree_coordinate hc hF hb hW0)
    obtain ⟨-, l2, -⟩ := line_restriction_derivs _ v hc3
    have e1 : (fun τ : ℝ => formComposition (bondSet F) G (uniformField F F.top) (τ • v)) = p := by
      funext τ
      simp only [formComposition, hext, hp, hP]
    rw [e1] at l2
    rw [l2]
    have e2 : v = ∑ e, singleBondForm e (v e) := by
      unfold singleBondForm
      exact (Finset.univ_sum_single v).symm
    nth_rewrite 1 [e2]
    rw [map_sum]
    have e3 : ∀ e : ↥(bondSet F),
        fderiv ℝ (formComposition (bondSet F) G (uniformField F F.top)) 0 (singleBondForm e (v e)) =
          flatCoefficient a c.ρA X b e.1 • D e.1.1 e.1.2 := fun e => by
      rw [← bondDeriv_eq_fderiv hJ hc hF hb hW0]
      exact bondDeriv_uniform_eq_smul hFl hJ hL hc hF hb hW0 e X _ hX
    simp only [e3]
    rw [Finset.sum_coe_sort (bondSet F) fun e => flatCoefficient a c.ρA X b e • D e.1 e.2]
    unfold bondSet flatLinearPart
    rw [Finset.sum_product]
  have hT := norm_sub_sub_deriv_le p _ (fun u hu => (hstep u hu).1) (fun u hu => (hstep u hu).2)
  rw [hp0, sub_zero, hp1, hd0] at hT
  exact hT
end WeightedResponses
end YangMills.Construction
end
