import YangMills.Construction.ColdChainAtEveryLevel.RotationOfABondAtEveryLevelProof
import YangMills.Construction.ColdChainAtEveryLevel.SizeOfABondAlongADirection
import YangMills.Construction.ColdChainAtEveryLevel.TotalUnderATurnedTopProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LatticePaths LatticeFractionalIntegration FlatPairing BlockLines
namespace BondAverageNorms
variable {F : BlockFrame} {j : ℕ}
theorem re_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by apply _root_.YangMills.Construction.BlockAverages.CoordinateStep.re_finset_sum <;> assumption
theorem re_real_smul (r : ℝ) (q : ℍ[ℝ]) : (r • q).re = r * q.re := by simp
theorem le_of_boundedOnAdjacentBlocks_twoBlockHull (hL : Odd F.blockSide) (hj : j + 1 ≤ F.top)
    {f : F.Site j → Fin 4 → ℝ} {c : F.Site (j + 1) × Fin 4} {t : ℝ}
    (hb : BoundedOnAdjacentBlocks f c t) {a : Lattice4} (ha : a ∈ twoBlockHull F.blockSide c.2) {k : Fin 4}
    (hk : a + basisVector k ∈ twoBlockHull F.blockSide c.2) : f (refineSite c.1 + siteOfCoords j a) k ≤ t := by apply _root_.YangMills.Construction.BondHull.le_of_mem_twoBlockHull <;> assumption
theorem norm_bondContour_holonomy_gap_le (hL : Odd F.blockSide) (X R : F.GaugeField j) {c : F.Site (j + 1) × Fin 4}
    {t : ℝ} (ht : 0 ≤ t)
    (hg : ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      ‖((X (refineSite c.1 + siteOfCoords j a) k * (R (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) :
        ℍ[ℝ]) - 1‖ ≤ t)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      5 * (F.blockSide : ℝ) * t := by apply _root_.YangMills.Construction.BlockAverages.BondAngle.norm_bondContour_holonomy_gap_le <;> assumption
theorem contourAverage_norm_near_one (hL : Odd F.blockSide) (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (u : UnitQuaternion) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ h' ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h' π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ) :
    0 ≤ 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c‖ ∧ 1 - ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c‖ ≤ δ ^ 2 / 2 := by apply _root_.YangMills.Construction.BlockAverages.BondAngle.contourAverage_norm_near_one <;> assumption
theorem norm_gaugedContourAverage (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (c : F.Site (j + 1) × Fin 4) : ‖gaugedContourAverage X k c‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.norm_gaugedContourAverage <;> assumption
def quaternionStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun r q => by ext <;> simp }
section Analytic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : E}
theorem analyticAt_pathHolonomy {X : E → F.GaugeField j}
    (hX : ∀ x i, AnalyticAt ℝ (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) z)
    (l : List PathStep) : ∀ x, AnalyticAt ℝ (fun σ => ((pathHolonomy (X σ) x l : UnitQuaternion) : ℍ[ℝ])) z := by
  induction l with
  | nil =>
    intro x
    simp only [pathHolonomy]
    exact analyticAt_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy, Submonoid.coe_mul]
    refine AnalyticAt.mul ?_ (ih _)
    rcases st with ⟨k, b⟩
    cases b with
    | true =>
      simpa [linkValue] using hX x k
    | false =>
      have h := hX (x - unitStep j k) k
      have h2 : AnalyticAt ℝ (fun σ => star ((X σ (x - unitStep j k) k : UnitQuaternion) : ℍ[ℝ])) z :=
        (quaternionStarCLM.analyticAt _).comp h
      simpa [linkValue, coe_unitQuaternion_inv] using h2
theorem analyticAt_contourAverage {X : E → F.GaugeField j}
    (hX : ∀ x i, AnalyticAt ℝ (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) z)
    (c : F.Site (j + 1) × Fin 4) : AnalyticAt ℝ (fun σ => _root_.YangMills.Construction.BlockAverages.contourAverage (X σ) c) z := by
  have hs : AnalyticAt ℝ (fun σ => ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (X σ) (refineSite c.1) (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ])) z :=
    Finset.analyticAt_fun_sum _ fun h _ => Finset.analyticAt_fun_sum _ fun π _ => analyticAt_pathHolonomy hX _ _
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  exact AnalyticAt.fun_smul (A := ℝ) analyticAt_const hs
theorem analyticAt_norm_of_ne_zero {G : E → ℍ[ℝ]} (hG : AnalyticAt ℝ G z) (h0 : G z ≠ 0) :
    AnalyticAt ℝ (fun σ => ‖G σ‖) z := by apply _root_.YangMills.SharedProofs.p78004 <;> assumption
end Analytic
theorem analyticAt_expTwistedField {k : ℕ} (R : F.GaugeField j) (f : F.Site j → Fin 4 → imaginaryQuaternions)
    (g : Fin k → F.Site j → Fin 4 → imaginaryQuaternions) (x : F.Site j) (i : Fin 4) :
    AnalyticAt ℝ (fun σ : Fin k → ℝ =>
      ((expTwistedField R (fun x i => f x i + ∑ l, σ l • g l x i) x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have h1 : AnalyticAt ℝ (fun σ : Fin k → ℝ => (f x i : ℍ[ℝ]) + ∑ l, σ l • (g l x i : ℍ[ℝ])) 0 := by
    refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun l _ => ?_)
    exact AnalyticAt.fun_smul (A := ℝ) ((ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).analyticAt _)
      analyticAt_const
  have h2 := (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp h1
  have h3 : AnalyticAt ℝ (fun σ : Fin k → ℝ => NormedSpace.exp ((f x i : ℍ[ℝ]) + ∑ l, σ l • (g l x i : ℍ[ℝ])) *
      ((R x i : UnitQuaternion) : ℍ[ℝ])) 0 := h2.mul analyticAt_const
  refine h3.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp [expTwistedField, expUnit]
theorem abs_re_le_norm_quaternion (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem norm_sq_eq_re_sq_add_pureComponent (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖pureComponent q‖ ^ 2 := by
  rw [sq ‖q‖, sq ‖pureComponent q‖, ← Quaternion.normSq_eq_norm_mul_self, ← Quaternion.normSq_eq_norm_mul_self]
  rw [Quaternion.normSq_def', Quaternion.normSq_def']
  simp only [pureComponent, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, smul_eq_mul]
  ring
theorem norm_exp_sub_exp_le_of_re_eq_zero {x y : ℍ[ℝ]} (hx : x.re = 0) (hy : y.re = 0) (hx1 : ‖x‖ ≤ 1)
    (hy1 : ‖y‖ ≤ 1) : ‖NormedSpace.exp x - NormedSpace.exp y‖ ≤ 4 * ‖x - y‖ := by
  have h1 := norm_pureComponent_exp_sub_sub_le hx hy hx1 hy1
  have h2 : ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y)‖ ≤ 3 * ‖x - y‖ := by
    have h3 : ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y)‖ ≤
        ‖pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y) - (x - y)‖ + ‖x - y‖ := by
      have := norm_add_le (pureComponent (NormedSpace.exp x) - pureComponent (NormedSpace.exp y) - (x - y)) (x - y)
      simpa using this
    have h4 : (‖x‖ + ‖y‖) * ‖x - y‖ ≤ 2 * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    linarith
  have h5 : |(NormedSpace.exp x - NormedSpace.exp y : ℍ[ℝ]).re| ≤ ‖x - y‖ := by
    have e : (NormedSpace.exp x - NormedSpace.exp y : ℍ[ℝ]).re = Real.cos ‖x‖ - Real.cos ‖y‖ := by
      rw [Quaternion.re_sub, re_exp_of_re_eq_zero hx, re_exp_of_re_eq_zero hy]
    rw [e]
    exact (Real.abs_cos_sub_cos_le _ _).trans (abs_norm_sub_norm_le x y)
  have h6 := norm_sq_eq_re_sq_add_pureComponent (NormedSpace.exp x - NormedSpace.exp y)
  rw [pureComponent_sub] at h6
  have h7 : ‖NormedSpace.exp x - NormedSpace.exp y‖ ^ 2 ≤ (4 * ‖x - y‖) ^ 2 := by
    rw [h6]
    have a1 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have a2 := sq_le_sq' (abs_le.1 h5).1 (abs_le.1 h5).2
    nlinarith [sq_nonneg ‖x - y‖]
  exact (abs_le_of_sq_le_sq' h7 (by positivity)).2
theorem abs_deriv_le_of_slope_bound {φ : ℝ → ℝ} {A B r : ℝ} (hd : DifferentiableAt ℝ φ 0) (hr : 0 < r)
    (h : ∀ τ : ℝ, |τ| < r → |φ τ - φ 0| ≤ (A + B * |τ|) * |τ|) : |deriv φ 0| ≤ A := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).abs
  have h2 : Filter.Tendsto (fun τ : ℝ => A + B * |τ|) (nhdsWithin 0 {0}ᶜ) (nhds A) := by
    have : Filter.Tendsto (fun τ : ℝ => A + B * |τ|) (nhds 0) (nhds (A + B * |(0 : ℝ)|)) :=
      (continuous_const.add (continuous_const.mul continuous_abs)).tendsto 0
    simp only [abs_zero, mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  have hev : ∀ᶠ τ in nhdsWithin (0 : ℝ) {0}ᶜ, |τ| < r := by
    have : ∀ᶠ τ in nhds (0 : ℝ), |τ| < r := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with τ hτ
      simpa [Real.dist_eq] using hτ
    exact this.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with τ hτ hne
  have hne' : τ ≠ 0 := hne
  have hp : 0 < |τ| := abs_pos.2 hne'
  rw [slope_def_field, sub_zero, abs_div, div_le_iff₀ hp]
  exact h τ hτ
theorem abs_re_sub_re_le_of_near_one (Z Z' : UnitQuaternion) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (h1 : ‖(Z : ℍ[ℝ]) - 1‖ ≤ δ) (h2 : ‖(Z' : ℍ[ℝ]) - (Z : ℍ[ℝ])‖ ≤ η) :
    |(Z' : ℍ[ℝ]).re - (Z : ℍ[ℝ]).re| ≤ η * (2 * δ + η) / 2 := by
  have a1 := norm_coe_sub_one_sq Z
  have a2 := norm_coe_sub_one_sq Z'
  have a4 : ‖(Z' : ℍ[ℝ]) - 1‖ ≤ δ + η := by
    have := norm_add_le ((Z : ℍ[ℝ]) - 1) ((Z' : ℍ[ℝ]) - (Z : ℍ[ℝ]))
    have e : (Z : ℍ[ℝ]) - 1 + ((Z' : ℍ[ℝ]) - (Z : ℍ[ℝ])) = (Z' : ℍ[ℝ]) - 1 := by abel
    rw [e] at this
    linarith
  have a6 : |‖(Z' : ℍ[ℝ]) - 1‖ - ‖(Z : ℍ[ℝ]) - 1‖| ≤ η := by
    refine le_trans ?_ h2
    have := abs_norm_sub_norm_le ((Z' : ℍ[ℝ]) - 1) ((Z : ℍ[ℝ]) - 1)
    simpa using this
  have e2 : (Z' : ℍ[ℝ]).re - (Z : ℍ[ℝ]).re =
      -((‖(Z' : ℍ[ℝ]) - 1‖ - ‖(Z : ℍ[ℝ]) - 1‖) * (‖(Z' : ℍ[ℝ]) - 1‖ + ‖(Z : ℍ[ℝ]) - 1‖)) / 2 := by
    have : (‖(Z' : ℍ[ℝ]) - 1‖ - ‖(Z : ℍ[ℝ]) - 1‖) * (‖(Z' : ℍ[ℝ]) - 1‖ + ‖(Z : ℍ[ℝ]) - 1‖) =
        ‖(Z' : ℍ[ℝ]) - 1‖ ^ 2 - ‖(Z : ℍ[ℝ]) - 1‖ ^ 2 := by ring
    rw [this, a1, a2]
    ring
  rw [e2, abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (add_nonneg (norm_nonneg ((Z' : ℍ[ℝ]) - 1)) (norm_nonneg ((Z : ℍ[ℝ]) - 1)))]
  have h5 : |‖(Z' : ℍ[ℝ]) - 1‖ - ‖(Z : ℍ[ℝ]) - 1‖| * (‖(Z' : ℍ[ℝ]) - 1‖ + ‖(Z : ℍ[ℝ]) - 1‖) ≤
      η * (2 * δ + η) :=
    mul_le_mul a6 (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hη
  linarith
theorem abs_norm_sub_norm_le_of_parts {W W' : ℍ[ℝ]} {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (nW1 : ‖W‖ ≤ 1)
    (nW'1 : ‖W'‖ ≤ 1) (hdiff : ‖W' - W‖ ≤ η) (hpW : ‖pureComponent W‖ ≤ δ) (hpW' : ‖pureComponent W'‖ ≤ δ + η)
    (hre : |W'.re - W.re| ≤ η * (2 * δ + η) / 2) (hW2 : 1 / 2 ≤ ‖W‖) :
    |‖W'‖ - ‖W‖| ≤ 4 * η * (2 * δ + η) := by
  have hsq : |‖W'‖ ^ 2 - ‖W‖ ^ 2| ≤ 2 * η * (2 * δ + η) := by
    rw [norm_sq_eq_re_sq_add_pureComponent W', norm_sq_eq_re_sq_add_pureComponent W]
    have ha : |W.re| ≤ 1 := (abs_re_le_norm_quaternion W).trans nW1
    have ha' : |W'.re| ≤ 1 := (abs_re_le_norm_quaternion W').trans nW'1
    have p1 : |W'.re ^ 2 - W.re ^ 2| ≤ η * (2 * δ + η) := by
      have e : W'.re ^ 2 - W.re ^ 2 = (W'.re - W.re) * (W'.re + W.re) := by ring
      rw [e, abs_mul]
      have h3 : |W'.re + W.re| ≤ 2 := (abs_add_le _ _).trans (by linarith)
      calc |W'.re - W.re| * |W'.re + W.re| ≤ (η * (2 * δ + η) / 2) * 2 :=
            mul_le_mul hre h3 (abs_nonneg _) (by positivity)
        _ = η * (2 * δ + η) := by ring
    have p2 : |‖pureComponent W'‖ ^ 2 - ‖pureComponent W‖ ^ 2| ≤ η * (2 * δ + η) := by
      have e : ‖pureComponent W'‖ ^ 2 - ‖pureComponent W‖ ^ 2 =
          (‖pureComponent W'‖ - ‖pureComponent W‖) * (‖pureComponent W'‖ + ‖pureComponent W‖) := by ring
      rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖pureComponent W'‖ + ‖pureComponent W‖)]
      have h3 : |‖pureComponent W'‖ - ‖pureComponent W‖| ≤ η := by
        refine (abs_norm_sub_norm_le _ _).trans ?_
        rw [← pureComponent_sub]
        exact (norm_pureComponent_le _).trans hdiff
      exact mul_le_mul h3 (by linarith) (by positivity) hη
    have e : W'.re ^ 2 + ‖pureComponent W'‖ ^ 2 - (W.re ^ 2 + ‖pureComponent W‖ ^ 2) =
        (W'.re ^ 2 - W.re ^ 2) + (‖pureComponent W'‖ ^ 2 - ‖pureComponent W‖ ^ 2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  have e : ‖W'‖ ^ 2 - ‖W‖ ^ 2 = (‖W'‖ - ‖W‖) * (‖W'‖ + ‖W‖) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖W'‖ + ‖W‖)] at hsq
  have hsum : 1 / 2 ≤ ‖W'‖ + ‖W‖ := by linarith [norm_nonneg W']
  have h3 : |‖W'‖ - ‖W‖| * (1 / 2) ≤ |‖W'‖ - ‖W‖| * (‖W'‖ + ‖W‖) :=
    mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  nlinarith
theorem norm_cubeAverage_le (hL : Odd F.blockSide) (Y : Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) {d : ℝ}
    (hY : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖Y h π‖ ≤ d) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), Y h π‖ ≤ d := by apply _root_.YangMills.Construction.BondHull.norm_smul_sum_perm_le <;> assumption
theorem abs_cubeAverage_le (hL : Odd F.blockSide) (Y : Lattice4 → Equiv.Perm (Fin 4) → ℝ) {d : ℝ}
    (hY : ∀ h ∈ centredCube F.blockSide, ∀ π, |Y h π| ≤ d) :
    |(1 / (24 * (F.blockSide : ℝ) ^ 4)) * ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), Y h π| ≤ d := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hcount : (∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ)) =
      24 * (F.blockSide : ℝ) ^ 4 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube hL,
      nsmul_eq_mul, mul_one]
    simp [Nat.factorial]
    ring
  rw [abs_mul, abs_of_nonneg (by positivity)]
  have hs : |∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), Y h π| ≤ d * (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [← hcount, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h hh => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
    rw [mul_one]
    exact hY h hh π
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * (d * (24 * (F.blockSide : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = d := by field_simp
theorem abs_norm_contourAverage_sub_le (hL : Odd F.blockSide) (X X' : F.GaugeField j) (c : F.Site (j + 1) × Fin 4)
    (u : UnitQuaternion) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hδ1 : δ ≤ 1)
    (h1 : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ)
    (h2 : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ η) :
    |‖_root_.YangMills.Construction.BlockAverages.contourAverage X' c‖ - ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c‖| ≤ 4 * η * (2 * δ + η) := by
  have hZZ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ η := by
    intro h hh π
    have e : pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ =
        (pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2))⁻¹) *
        (pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹) := by group
    rw [e]
    have e2 : ∀ a b : UnitQuaternion, ((a * b : UnitQuaternion) : ℍ[ℝ]) - (b : ℍ[ℝ]) =
        ((a : ℍ[ℝ]) - 1) * (b : ℍ[ℝ]) := by
      intro a b
      rw [Submonoid.coe_mul, sub_mul, one_mul]
    rw [e2, norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
    exact h2 h hh π
  have eW : ∀ Y : F.GaugeField j, _root_.YangMills.Construction.BlockAverages.contourAverage Y c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    intro Y
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    rw [smul_mul_assoc, Finset.sum_mul]
    simp only [Finset.sum_mul]
    rfl
  have nW : ∀ Y : F.GaugeField j, ‖_root_.YangMills.Construction.BlockAverages.contourAverage Y c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖_root_.YangMills.Construction.BlockAverages.contourAverage Y c‖ := by
    intro Y
    rw [norm_mul, _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion, mul_one]
  have hZ'1 : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        δ + η := by
    intro h hh π
    have := norm_add_le
      (((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1)
      (((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    rw [sub_add_sub_cancel'] at this
    linarith [h1 h hh π, hZZ h hh π]
  have hlow := (contourAverage_norm_near_one hL X c u hδ h1).2
  have hW2 : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ := by
    rw [nW]
    nlinarith
  have hsub : _root_.YangMills.Construction.BlockAverages.contourAverage X' c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      _root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        (((pathHolonomy X' (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    rw [eW, eW, ← smul_sub, ← Finset.sum_sub_distrib]
    simp only [Finset.sum_sub_distrib]
  have hdiff : ‖_root_.YangMills.Construction.BlockAverages.contourAverage X' c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      _root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ η := by
    rw [hsub]
    exact norm_cubeAverage_le hL _ hZZ
  have hre : |(_root_.YangMills.Construction.BlockAverages.contourAverage X' c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re -
      (_root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re| ≤ η * (2 * δ + η) / 2 := by
    have e : (_root_.YangMills.Construction.BlockAverages.contourAverage X' c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re -
        (_root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
        (_root_.YangMills.Construction.BlockAverages.contourAverage X' c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
          _root_.YangMills.Construction.BlockAverages.contourAverage X c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by simp
    rw [e, hsub, re_real_smul, re_finset_sum]
    simp only [re_finset_sum]
    exact abs_cubeAverage_le hL _ fun h hh π => by
      have := abs_re_sub_re_le_of_near_one _ _ hδ hη (h1 h hh π) (hZZ h hh π)
      simpa using this
  have hp : ∀ (Y : F.GaugeField j) (d : ℝ), (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide h π c.2) * u⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ d) →
      ‖pureComponent (_root_.YangMills.Construction.BlockAverages.contourAverage Y c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]))‖ ≤ d := by
    intro Y d hd
    rw [eW, pureComponent_smul, pureComponent_sum]
    simp only [pureComponent_sum]
    exact norm_cubeAverage_le hL _ fun h hh π => (norm_pureComponent_coe_le _).trans (hd h hh π)
  have hone : ∀ Y : F.GaugeField j, ‖_root_.YangMills.Construction.BlockAverages.contourAverage Y c * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ ≤ 1 := by
    intro Y
    rw [eW]
    exact norm_cubeAverage_le hL _ fun h _ π => (_root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion _).le
  have := abs_norm_sub_norm_le_of_parts hδ hη (hone X) (hone X') hdiff (hp X δ h1) (hp X' _ hZ'1) hre hW2
  rwa [nW, nW] at this
theorem expTwistedField_contour_near (hL : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {f : F.Site j → Fin 4 → imaginaryQuaternions} {c : F.Site (j + 1) × Fin 4} {t ε : ℝ} (ht : 0 ≤ t)
    (hf : BoundedOnAdjacentBlocks (fun x i => ‖(f x i : ℍ[ℝ])‖) c t)
    (hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) :
    ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (expTwistedField R f) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * (F.blockSide : ℝ) * t + ε := by
  intro h hh π
  have hg : ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      ‖((expTwistedField R f (refineSite c.1 + siteOfCoords j a) k *
        (R (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t := by
    intro a ha k hk
    have e : expTwistedField R f (refineSite c.1 + siteOfCoords j a) k * (R (refineSite c.1 + siteOfCoords j a) k)⁻¹ =
        expUnit (f (refineSite c.1 + siteOfCoords j a) k) := by
      simp [expTwistedField]
    rw [e]
    exact (BlockAverages.norm_exp_sub_one_le (f (refineSite c.1 + siteOfCoords j a) k).2).trans
      (le_of_boundedOnAdjacentBlocks_twoBlockHull hL hj hf ha hk)
  have e : pathHolonomy (expTwistedField R f) (refineSite c.1) (bondContour F.blockSide h π c.2) *
      (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R c))⁻¹ =
      (pathHolonomy (expTwistedField R f) (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2))⁻¹) *
        (pathHolonomy R (refineSite c.1) (bondContour F.blockSide h π c.2) *
          (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage R c))⁻¹) := by
    group
  rw [e]
  exact (norm_coe_mul_sub_one_le _ _).trans
    (add_le_add (norm_bondContour_holonomy_gap_le hL _ R ht hg hh π) (hsp h hh π))
theorem norm_coe_mul_inv_sub_one (A B : UnitQuaternion) :
    ‖((A * B⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(A : ℍ[ℝ]) - (B : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GaugeFixing.norm_mul_inv_sub_one <;> assumption
theorem expTwistedField_add_smul_link_gap (hL : Odd F.blockSide) (hj : j + 1 ≤ F.top) {R : F.GaugeField j}
    {f g : F.Site j → Fin 4 → imaginaryQuaternions} {c : F.Site (j + 1) × Fin 4} {t ρ τ : ℝ} (ht1 : t ≤ 1 / 2)
    (hτρ : |τ| * ρ ≤ 1 / 2)
    (hf : BoundedOnAdjacentBlocks (fun x i => ‖(f x i : ℍ[ℝ])‖) c t)
    (hg : BoundedOnAdjacentBlocks (fun x i => ‖(g x i : ℍ[ℝ])‖) c ρ) :
    ∀ a ∈ twoBlockHull F.blockSide c.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide c.2 →
      ‖((expTwistedField R (fun x i => f x i + τ • g x i) (refineSite c.1 + siteOfCoords j a) k *
        (expTwistedField R f (refineSite c.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * (|τ| * ρ) := by
  intro a ha k hk
  set y := refineSite c.1 + siteOfCoords j a with hy
  have e : expTwistedField R (fun x i => f x i + τ • g x i) y k * (expTwistedField R f y k)⁻¹ =
      expUnit (f y k + τ • g y k) * (expUnit (f y k))⁻¹ := by
    simp only [expTwistedField]
    group
  rw [e, norm_coe_mul_inv_sub_one]
  have h1 : ‖(f y k : ℍ[ℝ])‖ ≤ t := le_of_boundedOnAdjacentBlocks_twoBlockHull hL hj hf ha hk
  have h2 : ‖(g y k : ℍ[ℝ])‖ ≤ ρ := le_of_boundedOnAdjacentBlocks_twoBlockHull hL hj hg ha hk
  have h3 : ‖τ • (g y k : ℍ[ℝ])‖ ≤ |τ| * ρ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hc : ((f y k + τ • g y k : imaginaryQuaternions) : ℍ[ℝ]) = (f y k : ℍ[ℝ]) + τ • (g y k : ℍ[ℝ]) := rfl
  have hl := norm_exp_sub_exp_le_of_re_eq_zero (f y k + τ • g y k).2 (f y k).2
    (by
      rw [hc]
      refine (norm_add_le _ _).trans ?_
      linarith)
    (by linarith)
  have e3 : ((f y k + τ • g y k : imaginaryQuaternions) : ℍ[ℝ]) - (f y k : ℍ[ℝ]) = τ • (g y k : ℍ[ℝ]) := by
    rw [hc]
    abel
  rw [e3] at hl
  calc _ = ‖NormedSpace.exp ((f y k + τ • g y k : imaginaryQuaternions) : ℍ[ℝ]) -
        NormedSpace.exp (f y k : ℍ[ℝ])‖ := rfl
    _ ≤ 4 * ‖τ • (g y k : ℍ[ℝ])‖ := hl
    _ ≤ 4 * (|τ| * ρ) := by linarith
theorem bondAverageNormDerivStatement_of_referenceBounds (hB : referenceBoundsStatement) :
    bondAverageNormDerivStatement := by
  obtain ⟨C0, c0, L1, hC0, hc0, hB⟩ := hB
  refine ⟨max L1 1, fun L hodd hL0 => ?_⟩
  have hL1 : L1 ≤ L := le_trans (le_max_left _ _) hL0
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
  have hLp : (0 : ℝ) < L := by linarith
  obtain ⟨c, hcp, hcc0, hcs, hct⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ c0 ∧ (C0 + 1) * c ≤ 1 / 2 ∧
      (5 * (L : ℝ) + 1) * c ≤ 1 / 2 := by
    have p1 : 0 < 1 / (2 * (C0 + 1)) := by positivity
    have p2 : 0 < 1 / (2 * (5 * (L : ℝ) + 1)) := by positivity
    refine ⟨min c0 (min (1 / (2 * (C0 + 1))) (1 / (2 * (5 * (L : ℝ) + 1)))), lt_min hc0 (lt_min p1 p2),
      min_le_left _ _, ?_, ?_⟩
    · have h : min c0 (min (1 / (2 * (C0 + 1))) (1 / (2 * (5 * (L : ℝ) + 1)))) ≤ 1 / (2 * (C0 + 1)) :=
        (min_le_right _ _).trans (min_le_left _ _)
      calc _ ≤ (C0 + 1) * (1 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 1 / 2 := by field_simp
    · have h : min c0 (min (1 / (2 * (C0 + 1))) (1 / (2 * (5 * (L : ℝ) + 1)))) ≤ 1 / (2 * (5 * (L : ℝ) + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      calc _ ≤ (5 * (L : ℝ) + 1) * (1 / (2 * (5 * (L : ℝ) + 1))) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 1 / 2 := by field_simp
  refine ⟨160 * (L : ℝ) * (5 * (L : ℝ) + C0), c, by positivity, hcp, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hs hcold j b hj hb
  subst hFL
  have hj' : j + 1 ≤ F.top := hj
  obtain ⟨-, -, -, -, hcontour, -⟩ := hB F m S hodd hL1 hamb hm hreg s V hs0 (hs.trans hcc0) hcold
  set R := referenceFieldChain S V with hR
  set l : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hLp]; exact hLr)
  have hl2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
  set ε : ℝ := C0 * (s * l ^ 2) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 2 := by
    have h1 : s * l ^ 2 ≤ s := by nlinarith
    have h2 : C0 * (s * l ^ 2) ≤ C0 * s := mul_le_mul_of_nonneg_left h1 hC0.le
    have h3 : (C0 + 1) * s ≤ (C0 + 1) * c := mul_le_mul_of_nonneg_left hs (by positivity)
    nlinarith
  have hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide h π b.2) *
        (polarUnit (_root_.YangMills.Construction.BlockAverages.contourAverage (R j) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε := by
    intro h hh π
    have := hcontour j hj b hb h hh π
    have e : ε = C0 * s * levelScale F (j + 1) ^ 2 := by
      rw [hε, hl]
      unfold levelScale
      ring
    rw [e]
    exact this
  refine ⟨fun U => ?_, fun f t ht0 ht hf => ?_⟩
  · have e : expTwistedField (R j) (levelCoordinateImaginary R U j) = chartField R U j := by
      funext x i
      show expUnit ⟨unitQuaternionLog (chartGap R U j x i), re_unitQuaternionLog _⟩ * R j x i = _
      rw [expUnit_unitQuaternionLog]
      simp [chartGap]
    unfold bondAverageNorm
    rw [e]
    exact norm_gaugedContourAverage _ _ _
  · have ht5 : 5 * (F.blockSide : ℝ) * t ≤ 1 / 2 := by
      have : (5 * (F.blockSide : ℝ) + 1) * t ≤ (5 * (F.blockSide : ℝ) + 1) * c :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      nlinarith
    have ht1 : t ≤ 1 / 2 := by
      have : (5 * (F.blockSide : ℝ) + 1) * t ≤ (5 * (F.blockSide : ℝ) + 1) * c :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      nlinarith
    set δ : ℝ := 5 * (F.blockSide : ℝ) * t + ε with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hδ1 : δ ≤ 1 := by linarith
    have h1 := expTwistedField_contour_near hodd hj' ht0 hf hsp
    have hne : _root_.YangMills.Construction.BlockAverages.contourAverage (expTwistedField (R j) f) b ≠ 0 := by
      have := (contourAverage_norm_near_one hodd _ b _ hδ0 h1).2
      intro h0
      rw [h0, norm_zero] at this
      nlinarith
    have hA : ∀ (k : ℕ) (g : Fin k → F.Site j → Fin 4 → imaginaryQuaternions), AnalyticAt ℝ
        (fun σ : Fin k → ℝ => bondAverageNorm (R j) (fun x i => f x i + ∑ l, σ l • g l x i) b) 0 := by
      intro k g
      refine analyticAt_norm_of_ne_zero
        (analyticAt_contourAverage (fun x i => analyticAt_expTwistedField (R j) f g x i) b) ?_
      have e : (fun x i => f x i + ∑ l, (0 : Fin k → ℝ) l • g l x i) = f := by
        funext x i
        simp
      rw [e]
      exact hne
    refine ⟨hA, fun g ρ hρ hg => ?_⟩
    have hd : DifferentiableAt ℝ (fun τ : ℝ => bondAverageNorm (R j) (fun x i => f x i + τ • g x i) b) 0 := by
      have h2 := (hA 1 fun _ => g).differentiableAt
      have h3 : DifferentiableAt ℝ (fun τ : ℝ => (fun _ : Fin 1 => τ)) 0 :=
        differentiableAt_pi.2 fun _ => differentiableAt_id
      have h4 := DifferentiableAt.comp (0 : ℝ) (g := fun σ : Fin 1 → ℝ =>
        bondAverageNorm (R j) (fun x i => f x i + ∑ l, σ l • g x i) b) h2 h3
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
      simp [Function.comp]
    have hr : 0 < 1 / (2 * (ρ + 1)) := by positivity
    have hbound := abs_deriv_le_of_slope_bound (A := 160 * (F.blockSide : ℝ) * ρ * δ)
      (B := 1600 * (F.blockSide : ℝ) ^ 2 * ρ ^ 2) hd hr ?_
    · refine hbound.trans ?_
      have e1 : δ ≤ (5 * (F.blockSide : ℝ) + C0) * (t + s * l ^ 2) := by
        have hy : 0 ≤ s * l ^ 2 := by positivity
        rw [hδ, hε]
        nlinarith [mul_nonneg hC0.le ht0, mul_nonneg hLp.le hy]
      calc 160 * (F.blockSide : ℝ) * ρ * δ ≤
            160 * (F.blockSide : ℝ) * ρ * ((5 * (F.blockSide : ℝ) + C0) * (t + s * l ^ 2)) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = 160 * (F.blockSide : ℝ) * (5 * (F.blockSide : ℝ) + C0) * (t + s * l ^ 2) * ρ := by ring
    · intro τ hτ
      have hτρ : |τ| * ρ ≤ 1 / 2 := by
        have h2 : |τ| * ρ ≤ 1 / (2 * (ρ + 1)) * ρ := mul_le_mul_of_nonneg_right hτ.le hρ
        have h3 : 1 / (2 * (ρ + 1)) * ρ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          linarith
        linarith
      have hτ0 : 0 ≤ |τ| * ρ := by positivity
      have e0 : (fun x i => f x i + (0 : ℝ) • g x i) = f := by
        funext x i
        simp
      have hη : 0 ≤ 5 * (F.blockSide : ℝ) * (4 * (|τ| * ρ)) := by positivity
      have := abs_norm_contourAverage_sub_le hodd (expTwistedField (R j) f)
        (expTwistedField (R j) (fun x i => f x i + τ • g x i)) b _ hδ0 hη hδ1 h1
        (fun h hh π => norm_bondContour_holonomy_gap_le hodd _ _ (by positivity)
          (expTwistedField_add_smul_link_gap hodd hj' ht1 hτρ hf hg) hh π)
      show |bondAverageNorm (R j) (fun x i => f x i + τ • g x i) b -
        bondAverageNorm (R j) (fun x i => f x i + (0 : ℝ) • g x i) b| ≤ _
      rw [e0]
      refine this.trans (le_of_eq ?_)
      ring
end BondAverageNorms
end YangMills.Construction
end
