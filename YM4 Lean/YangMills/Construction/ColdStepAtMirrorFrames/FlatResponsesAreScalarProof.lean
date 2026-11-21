import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalar
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open BlockOffsets
variable {F : BlockFrame}
namespace FlatResponse
theorem isSmallCurvature_leftTranslate_uniform {j : ℕ} (v : F.Site j → Fin 4 → imaginaryQuaternions) {s ε : ℝ}
    (hε : ∀ x i, ‖v x i‖ ≤ ε) (hs : 4 * ε < s) : IsSmallCurvature s (leftTranslate v (uniformField F j)) := by
  intro p _
  have hb : ∀ x i, distFromOne (leftTranslate v (uniformField F j) x i) ≤ ε := by
    intro x i
    have e : leftTranslate v (uniformField F j) x i = expUnit (v x i) := by simp [leftTranslate, uniformField]
    rw [e]
    exact (distFromOne_expUnit_le _).trans (hε x i)
  have hst : ∀ x st, distFromOne (linkValue (leftTranslate v (uniformField F j)) x st) ≤ ε := by
    intro x st
    unfold linkValue
    split_ifs
    · exact hb _ _
    · rw [distFromOne_inv]
      exact hb _ _
  have h4 : ∀ a b c d : UnitQuaternion, distFromOne a ≤ ε → distFromOne b ≤ ε → distFromOne c ≤ ε →
      distFromOne d ≤ ε → distFromOne (a * (b * (c * d))) ≤ 4 * ε := by
    intro a b c d ha hb hc hd
    have h1 := distFromOne_mul a (b * (c * d))
    have h2 := distFromOne_mul b (c * d)
    have h3 := distFromOne_mul c d
    linarith
  have hp : distFromOne (plaquetteHolonomy (leftTranslate v (uniformField F j)) p) ≤ 4 * ε := by
    unfold plaquetteHolonomy
    simp only [pathHolonomy, mul_one]
    exact h4 _ _ _ _ (hst _ _) (hst _ _) (hst _ _) (hst _ _)
  exact lt_of_le_of_lt hp hs
theorem mul_expUnit_mul_inv (g : UnitQuaternion) (w w' : imaginaryQuaternions)
    (h : (g : ℍ[ℝ]) * (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = (w' : ℍ[ℝ])) :
    g * expUnit w * g⁻¹ = expUnit w' := by
  apply Subtype.ext
  have hgg : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  have hn : ‖(w' : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := by
    rw [← h, norm_mul, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, one_mul, mul_one]
  have hc : ∀ c : ℝ, ((c : ℝ) : ℍ[ℝ]) = c • (1 : ℍ[ℝ]) := fun c => by ext <;> simp
  change (g : ℍ[ℝ]) * NormedSpace.exp (w : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w' : ℍ[ℝ])
  rw [exp_imaginary_eq, exp_imaginary_eq, hn, hc, ← h]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, hgg]
theorem exists_conj_eq_neg (X : imaginaryQuaternions) :
    ∃ g : UnitQuaternion, (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - (X : ℍ[ℝ]) := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  set x := (X : ℍ[ℝ]).imI with hx
  set y := (X : ℍ[ℝ]).imJ with hy
  set z := (X : ℍ[ℝ]).imK with hz
  obtain ⟨a, b, c, hn, hd⟩ : ∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ a * x + b * y + c * z = 0 := by
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      exact ⟨1, 0, 0, by norm_num, by rw [hx0]; ring⟩
    · have hpos : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      set r := Real.sqrt (x ^ 2 + y ^ 2) with hr
      have hr0 : r ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
      refine ⟨- y / r, x / r, 0, ?_, ?_⟩
      · field_simp
        nlinarith
      · field_simp
        ring
  set q : ℍ[ℝ] := ⟨0, a, b, c⟩ with hq
  have hs : Quaternion.normSq q = 1 := by
    rw [Quaternion.normSq_def']
    simp only [hq]
    nlinarith
  have hu : q ∈ unitary ℍ[ℝ] := by
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hs]
      simp
    · rw [Quaternion.self_mul_star, hs]
      simp
  refine ⟨⟨q, hu⟩, ?_⟩
  have hi : (((⟨q, hu⟩ : UnitQuaternion)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star q := rfl
  rw [hi]
  change q * (X : ℍ[ℝ]) * star q = _
  have hqr : q.re = 0 := rfl
  have hqi : q.imI = a := rfl
  have hqj : q.imJ = b := rfl
  have hqk : q.imK = c := rfl
  ext
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_neg, hqr, hqi, hqj, hqk, hre,
      ← hx, ← hy, ← hz]
    ring
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imI_neg, hqr, hqi, hqj, hqk, hre,
      ← hx, ← hy, ← hz]
    linear_combination (2 * a) * hd - x * hn
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imJ_neg, hqr, hqi, hqj, hqk, hre,
      ← hx, ← hy, ← hz]
    linear_combination (2 * b) * hd - y * hn
  · simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
      Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.imK_neg, hqr, hqi, hqj, hqk, hre,
      ← hx, ← hy, ← hz]
    linear_combination (2 * c) * hd - z * hn
theorem eq_smul_of_conj_fixed (X D : imaginaryQuaternions) (hX : ‖X‖ = 1) (hu : (X : ℍ[ℝ]) ∈ unitary ℍ[ℝ])
    (hfix : (X : ℍ[ℝ]) * (D : ℍ[ℝ]) * star (X : ℍ[ℝ]) = (D : ℍ[ℝ])) :
    D = (-((D : ℍ[ℝ]) * (X : ℍ[ℝ])).re) • X := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  have hdre : (D : ℍ[ℝ]).re = 0 := D.2
  have hn : (X : ℍ[ℝ]).imI ^ 2 + (X : ℍ[ℝ]).imJ ^ 2 + (X : ℍ[ℝ]).imK ^ 2 = 1 := by
    have h1 : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      have : ‖(X : ℍ[ℝ])‖ = 1 := hX
      rw [this]
      norm_num
    rw [Quaternion.normSq_def', hre] at h1
    nlinarith
  have hi := congrArg (fun q : ℍ[ℝ] => q.imI) hfix
  have hj := congrArg (fun q : ℍ[ℝ] => q.imJ) hfix
  have hk := congrArg (fun q : ℍ[ℝ] => q.imK) hfix
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, hre, hdre] at hi hj hk
  apply Subtype.ext
  ext
  · simp [hre, hdre]
  · simp only [Submodule.coe_smul, Quaternion.imI_smul, Quaternion.re_mul, hre, hdre, smul_eq_mul]
    linear_combination (-1 / 2) * hi - ((D : ℍ[ℝ]).imI / 2) * hn
  · simp only [Submodule.coe_smul, Quaternion.imJ_smul, Quaternion.re_mul, hre, hdre, smul_eq_mul]
    linear_combination (-1 / 2) * hj - ((D : ℍ[ℝ]).imJ / 2) * hn
  · simp only [Submodule.coe_smul, Quaternion.imK_smul, Quaternion.re_mul, hre, hdre, smul_eq_mul]
    linear_combination (-1 / 2) * hk - ((D : ℍ[ℝ]).imK / 2) * hn
theorem adjointMap_minimizingCoordinates_of_gauge_fixed {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hT : MinimalActionGaugeCovariance) (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature c.σA V) (γ : F.Cell → UnitQuaternion)
    (hg : gaugeTransform γ V = V) (x : F.Site F.depth) (i : Fin 4) :
    adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V c.ρA x i) =
      minimizingCoordinates a (finiteCells F) V c.ρA x i := by
  classical
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hρ := hc.classical.1
  have hπ : c.ρA < Real.pi := by linarith [Real.pi_gt_three, hρ.2.1]
  have hOdd : Odd F.blockSide := by rw [hF.1]; exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; omega
  have hC := hc.estimates F c.σA V hF hσ le_rfl hV
  obtain ⟨w, hw, -, hu⟩ := hC.minimizer
  have hwρ : IsMinimizingChart a (finiteCells F) V c.ρA w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V c.ρA w := ⟨w, hwρ⟩
  have hl : minimizingCoordinates a (finiteCells F) V c.ρA = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact TopLevelSites.minimizingChart_unique hOdd hs hπ hex.choose_spec hwρ hu
  have ht := hT.2 F a c.ρA V w γ hOdd hs hwρ
  rw [hg] at ht
  have e := TopLevelSites.minimizingChart_unique hOdd hs hπ ht hwρ hu
  rw [hl]
  exact congrFun (congrFun e x) i
end FlatResponse
open FlatResponse in
theorem flatCoordinatesScalar_of_gaugeCovariance (hT : MinimalActionGaugeCovariance) : FlatCoordinatesScalar := by
  intro a L c hL hc F b e X hF hX
  classical
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  constructor
  · have hcold : IsSmallCurvature c.σA (uniformField F F.top) := by
      have h := isSmallCurvature_leftTranslate_uniform (F := F) (j := F.top) (fun _ _ => 0) (s := c.σA) (ε := 0)
        (fun _ _ => by simp) (by linarith)
      have e0 : leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) (uniformField F F.top) = uniformField F F.top := by
        funext x i
        have e1 : expUnit (0 : imaginaryQuaternions) = 1 := by
          apply Subtype.ext
          simp [expUnit]
        simp [leftTranslate, uniformField, e1]
      rwa [e0] at h
    obtain ⟨g, hg⟩ := exists_conj_eq_neg (torusCoordinate a c.ρA b (uniformField F F.top))
    have hgf : gaugeTransform (fun _ => g) (uniformField F F.top) = uniformField F F.top := by
      funext x i
      simp [gaugeTransform, uniformField]
    have h := adjointMap_minimizingCoordinates_of_gauge_fixed hT hL hc hF _ hcold (fun _ => g) hgf b.1 b.2
    have h2 := congrArg (fun v : imaginaryQuaternions => (v : ℍ[ℝ])) h
    change (g : ℍ[ℝ]) * (torusCoordinate a c.ρA b (uniformField F F.top) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (torusCoordinate a c.ρA b (uniformField F F.top) : ℍ[ℝ]) at h2
    rw [hg] at h2
    apply Subtype.ext
    have h3 : (2 : ℝ) • (torusCoordinate a c.ρA b (uniformField F F.top) : ℍ[ℝ]) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h2]
      simp
    simpa using h3
  · have hre : (X : ℍ[ℝ]).re = 0 := X.2
    have hun : Quaternion.normSq (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      have : ‖(X : ℍ[ℝ])‖ = 1 := hX
      rw [this]
      norm_num
    have hu : (X : ℍ[ℝ]) ∈ unitary ℍ[ℝ] := by
      rw [Unitary.mem_iff]
      constructor
      · rw [Quaternion.star_mul_self, hun]
        simp
      · rw [Quaternion.self_mul_star, hun]
        simp
    set g : UnitQuaternion := ⟨(X : ℍ[ℝ]), hu⟩ with hgdef
    have hginv : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (X : ℍ[ℝ]) := rfl
    have hXX : (X : ℍ[ℝ]) * star (X : ℍ[ℝ]) = 1 := by
      rw [Quaternion.self_mul_star, hun]
      simp
    set H : (Fin 1 → ℝ) → imaginaryQuaternions := fun τ =>
      torusCoordinate a c.ρA b (leftTranslate (bondSpread ![e] ![X] τ) (uniformField F F.top)) with hH
    let Lad : imaginaryQuaternions →L[ℝ] imaginaryQuaternions := LinearMap.toContinuousLinearMap (adjointMap g)
    have hsp : ∀ (τ : Fin 1 → ℝ) x i, bondSpread ![e] ![X] τ x i = if e = (x, i) then τ 0 • X else 0 := by
      intro τ x i
      simp [bondSpread]
    have hev : H =ᶠ[𝓝 0] fun τ => Lad (H τ) := by
      have hb : Metric.ball (0 : Fin 1 → ℝ) (c.σA / 8) ∈ 𝓝 (0 : Fin 1 → ℝ) := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hb] with τ hτ
      have hτ0 : |τ 0| ≤ c.σA / 8 := by
        have h1 : ‖τ‖ < c.σA / 8 := by simpa using hτ
        have h2 : ‖τ 0‖ ≤ ‖τ‖ := norm_le_pi_norm τ 0
        rw [Real.norm_eq_abs] at h2
        linarith
      have hcold : IsSmallCurvature c.σA (leftTranslate (bondSpread ![e] ![X] τ) (uniformField F F.top)) := by
        refine isSmallCurvature_leftTranslate_uniform _ (ε := c.σA / 8) (fun x i => ?_) (by linarith)
        rw [hsp]
        split_ifs
        · rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
          exact hτ0
        · simp
          positivity
      have hgf : gaugeTransform (fun _ => g) (leftTranslate (bondSpread ![e] ![X] τ) (uniformField F F.top)) =
          leftTranslate (bondSpread ![e] ![X] τ) (uniformField F F.top) := by
        funext x i
        simp only [gaugeTransform, leftTranslate, uniformField, mul_one, hsp]
        split_ifs
        · apply mul_expUnit_mul_inv
          simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, hginv]
          change τ 0 • ((X : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (X : ℍ[ℝ])) = _
          rw [mul_assoc, hXX, mul_one]
        · apply mul_expUnit_mul_inv
          simp
      exact (adjointMap_minimizingCoordinates_of_gauge_fixed hT hL hc hF _ hcold (fun _ => g) hgf b.1 b.2).symm
    have hD : bondDeriv (torusCoordinate a c.ρA b) (uniformField F F.top) ![e] ![X] =
        fderiv ℝ H 0 (Pi.single 0 1) := by
      unfold bondDeriv
      rw [iteratedFDeriv_one_apply]
    rw [hD]
    by_cases hdiff : DifferentiableAt ℝ H 0
    · have hd := hdiff.hasFDerivAt
      have h2 : fderiv ℝ H 0 = Lad.comp (fderiv ℝ H 0) := by
        have h3 : HasFDerivAt (fun τ => Lad (H τ)) (Lad.comp (fderiv ℝ H 0)) 0 := Lad.hasFDerivAt.comp 0 hd
        exact (hev.fderiv_eq (𝕜 := ℝ)).trans h3.fderiv
      have hfix : Lad (fderiv ℝ H 0 (Pi.single 0 1)) = fderiv ℝ H 0 (Pi.single 0 1) := by
        have := congrArg (fun M : (Fin 1 → ℝ) →L[ℝ] imaginaryQuaternions => M (Pi.single 0 1)) h2
        exact this.symm
      refine eq_smul_of_conj_fixed X _ hX hu ?_
      have := congrArg (fun v : imaginaryQuaternions => (v : ℍ[ℝ])) hfix
      exact this
    · rw [fderiv_zero_of_not_differentiableAt hdiff]
      simp
end ColdStepAtMirrorFrames
end YangMills.Construction
end
