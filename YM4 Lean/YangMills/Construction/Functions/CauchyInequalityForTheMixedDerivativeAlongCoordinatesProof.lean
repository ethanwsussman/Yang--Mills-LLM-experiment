import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Functions.CauchyInequalityForTheMixedDerivativeAlongCoordinates
import Mathlib
open Filter Metric Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.CauchyEstimates
open ComplexVariables TorusBoundNotation Coordinates
variable {n : ℕ}
theorem foldr_coordDeriv_isHolomorphicScalar
    (rules : SeveralComplexVariables.HolomorphicCalculusRules) (hn : 1 ≤ n)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    (l : List (Fin n)) : IsHolomorphicScalar O (l.foldr coordDeriv F) := by
  induction l with
  | nil => exact hF
  | cons i l ih =>
    exact (rules n hn O ih.1 _ _ ih ih).2.2.2.2.2.1.1 i
theorem differentiableAt_along_axis {O : Set (ComplexCoordinates n)} {G : ComplexCoordinates n → ℂ}
    (hG : IsHolomorphicScalar O G) {z : ComplexCoordinates n} (i : Fin n) {w₀ : ℂ}
    (h : z + w₀ • ComplexCoordinates.stdBasisVector i ∈ O) :
    DifferentiableAt ℂ (fun w : ℂ => G (z + w • ComplexCoordinates.stdBasisVector i)) w₀ := by
  have h1 := (eventually_differentiableAt_line hG h i).self_of_nhds
  have h2 : DifferentiableAt ℂ (fun w : ℂ => w - w₀) w₀ := by fun_prop
  have h3 : DifferentiableAt ℂ (fun w : ℂ => G ((z + w₀ • ComplexCoordinates.stdBasisVector i) +
      (w - w₀) • ComplexCoordinates.stdBasisVector i)) w₀ :=
    DifferentiableAt.comp (g := fun w : ℂ => G ((z + w₀ • ComplexCoordinates.stdBasisVector i) +
      w • ComplexCoordinates.stdBasisVector i)) w₀ (by simpa using h1) h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  have : z + w₀ • ComplexCoordinates.stdBasisVector i + (w - w₀) • ComplexCoordinates.stdBasisVector i =
      z + w • ComplexCoordinates.stdBasisVector i := by
    rw [add_assoc, ← add_smul]
    simp
  simp only [this]
theorem norm_coordDeriv_le_of_sphere {O : Set (ComplexCoordinates n)} {G : ComplexCoordinates n → ℂ}
    (hG : IsHolomorphicScalar O G) {z : ComplexCoordinates n} {i : Fin n} {R C : ℝ} (hR : 0 < R)
    (hline : ∀ w : ℂ, ‖w‖ ≤ R → z + w • ComplexCoordinates.stdBasisVector i ∈ O)
    (hC : ∀ w : ℂ, ‖w‖ = R → ‖G (z + w • ComplexCoordinates.stdBasisVector i)‖ ≤ C) :
    ‖coordDeriv i G z‖ ≤ C / R := by
  have hd : DifferentiableOn ℂ (fun w : ℂ => G (z + w • ComplexCoordinates.stdBasisVector i))
      (closedBall 0 R) := fun w hw =>
    (differentiableAt_along_axis hG i (hline w (by simpa using hw))).differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (hd.diffContOnCl_ball subset_rfl)
    (fun w hw => hC w (by simpa using hw))
theorem add_smul_stdBasisVector_mem_closedPolydisk {r : Fin n → ℝ} {z : ComplexCoordinates n}
    (hz : z ∈ closedPolydisk r) {i : Fin n} (hzi : z i = 0) {w : ℂ} (hw : ‖w‖ ≤ r i) :
    z + w • ComplexCoordinates.stdBasisVector i ∈ closedPolydisk r := by
  intro j
  by_cases h : j = i
  · subst h
    simpa [ComplexCoordinates.stdBasisVector, hzi] using hw
  · simpa [ComplexCoordinates.stdBasisVector, h] using hz j
theorem norm_foldr_coordDeriv_le (rules : SeveralComplexVariables.HolomorphicCalculusRules)
    (hn : 1 ≤ n) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {B : ℝ} {O : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hPO : closedPolydisk r ⊆ O) (hF : IsHolomorphicScalar O F)
    (hB : ∀ z ∈ closedPolydisk r, ‖F z‖ ≤ B) (l : List (Fin n)) (hl : l.Nodup) :
    ∀ z ∈ closedPolydisk r, (∀ i ∈ l, z i = 0) →
      ‖l.foldr coordDeriv F z‖ ≤ B * (l.map fun i => (r i)⁻¹).prod := by
  induction l with
  | nil =>
    intro z hz _
    simpa using hB z hz
  | cons i l ih =>
    intro z hz hz0
    have hnot : i ∉ l := (List.nodup_cons.1 hl).1
    have ih' := ih (List.nodup_cons.1 hl).2
    have hzi : z i = 0 := hz0 i (by simp)
    have hline : ∀ w : ℂ, ‖w‖ ≤ r i →
        z + w • ComplexCoordinates.stdBasisVector i ∈ closedPolydisk r :=
      fun w hw => add_smul_stdBasisVector_mem_closedPolydisk hz hzi hw
    have hbound : ‖coordDeriv i (l.foldr coordDeriv F) z‖ ≤
        (B * (l.map fun i => (r i)⁻¹).prod) / r i := by
      refine norm_coordDeriv_le_of_sphere (foldr_coordDeriv_isHolomorphicScalar rules hn hF l) (hr i)
        (fun w hw => hPO (hline w hw)) fun w hw => ?_
      refine ih' _ (hline w hw.le) fun j hj => ?_
      have hji : j ≠ i := fun e => hnot (e ▸ hj)
      simpa [ComplexCoordinates.stdBasisVector, hji] using hz0 j (List.mem_cons_of_mem _ hj)
    calc ‖(i :: l).foldr coordDeriv F z‖
        = ‖coordDeriv i (l.foldr coordDeriv F) z‖ := rfl
      _ ≤ (B * (l.map fun i => (r i)⁻¹).prod) / r i := hbound
      _ = B * ((i :: l).map fun i => (r i)⁻¹).prod := by
        rw [List.map_cons, List.prod_cons, div_eq_mul_inv]
        ring
theorem norm_mixedDeriv_le_of_closedPolydisk
    (rules : SeveralComplexVariables.HolomorphicCalculusRules) (hn : 1 ≤ n) {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} {B : ℝ}
    (hF : IsHolomorphicScalar O F) (hPO : closedPolydisk r ⊆ O)
    (hB : ∀ z ∈ closedPolydisk r, ‖F z‖ ≤ B) :
    ‖mixedDeriv F 0‖ ≤ B * ∏ i, (r i)⁻¹ := by
  have h0 : (0 : ComplexCoordinates n) ∈ closedPolydisk r := fun i => by
    simpa using (hr i).le
  have h := norm_foldr_coordDeriv_le rules hn hr hPO hF hB _ (List.nodup_finRange n) 0 h0
    (fun _ _ => rfl)
  rw [← Fin.prod_univ_def] at h
  exact h
theorem norm_mixedDeriv_le_of_scaled_radius
    (rules : SeveralComplexVariables.HolomorphicCalculusRules)
    (a : WeightedModulusSum.Weights n) {F : ComplexCoordinates n → ℂ} {B : ℝ}
    (hF : IsHolomorphicScalar a.unitSet F) (hB : ∀ z ∈ a.unitSet, ‖F z‖ ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖mixedDeriv F 0‖ ≤ B * (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n := by
  have hn := a.one_le
  have hc := a.c_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : ∀ i, 0 < t / (n * a.c i) := fun i => div_pos ht.1 (mul_pos hn0 (hc i))
  have hsub : closedPolydisk (fun i => t / (n * a.c i)) ⊆ a.unitSet := by
    intro z hz
    have hle : a.weightedNorm z ≤ ∑ _i : Fin n, t / n := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hci := hc i
      calc a.c i * ‖z i‖ ≤ a.c i * (t / (n * a.c i)) :=
            mul_le_mul_of_nonneg_left (hz i) hci.le
        _ = t / n := by field_simp
    have hsum : ∑ _i : Fin n, t / (n : ℝ) = t := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    exact lt_of_le_of_lt (hsum ▸ hle) ht.2
  have h := norm_mixedDeriv_le_of_closedPolydisk rules hn hr hF hsub
    (fun z hz => hB z (hsub hz))
  have hprod : ∏ i, (t / (n * a.c i))⁻¹ = (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n := by
    have hterm : ∀ i, (t / (n * a.c i))⁻¹ = (n : ℝ) * a.c i * t⁻¹ := fun i => by
      rw [inv_div, div_eq_mul_inv]
    simp only [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hprod] at h
  calc ‖mixedDeriv F 0‖ ≤ B * ((n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n) := h
    _ = B * (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n := by ring
theorem mixedDerivCauchyBound_of_calculusRules
    (rules : SeveralComplexVariables.HolomorphicCalculusRules) : MixedDerivCauchyBound := by
  refine ⟨fun n hn r hr O F B hF hPO _ hB =>
    norm_mixedDeriv_le_of_closedPolydisk rules hn hr hF hPO hB,
    fun n a F B hF _ hB => ?_⟩
  have hlim : Tendsto (fun t : ℝ => B * (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n) (𝓝[<] 1)
      (𝓝 (B * (n : ℝ) ^ n * (∏ i, a.c i) * ((1 : ℝ)⁻¹) ^ n)) := by
    have hcont : ContinuousAt (fun t : ℝ => B * (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n) 1 :=
      ContinuousAt.mul continuousAt_const ((continuousAt_inv₀ one_ne_zero).pow n)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[<] 1, ‖mixedDeriv F 0‖ ≤
      B * (n : ℝ) ^ n * (∏ i, a.c i) * (t⁻¹) ^ n := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    exact norm_mixedDeriv_le_of_scaled_radius rules a hF hB ht
  simpa using ge_of_tendsto hlim hev
end YangMills.Construction.CauchyEstimates
end
