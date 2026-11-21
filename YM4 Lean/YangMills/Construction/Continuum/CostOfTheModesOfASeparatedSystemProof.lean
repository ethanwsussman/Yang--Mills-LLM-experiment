import YangMills.Construction.Continuum.ComplexExtensionIsUniqueAndBounded
import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystem
import YangMills.Construction.Continuum.ModesAreCutoffsTimesCharacters
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff ENNReal Matrix
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions
open YangMills.Construction.Bumps YangMills.Construction.TorusMetric
namespace ModeCost
variable {n : ℕ}
theorem abs_apply_le_coordSupNorm (ξ : Config n) (i : Fin n) (c : Fin 4) :
    |ξ i c| ≤ coordSupNorm ξ := by
  have h1 : |ξ i c| ≤ ⨆ c, |ξ i c| :=
    le_ciSup (f := fun c => |ξ i c|) (Set.finite_range _).bddAbove c
  have h2 : (⨆ c, |ξ i c|) ≤ coordSupNorm ξ :=
    le_ciSup (f := fun i => ⨆ c, |ξ i c|) (Set.finite_range _).bddAbove i
  exact h1.trans h2
theorem coordSupNorm_nonneg (ξ : Config n) : 0 ≤ coordSupNorm ξ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem sqrt_sum_sq_le_two_mul {v : Fin 4 → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : ∀ c, |v c| ≤ b) :
    Real.sqrt (∑ c, v c ^ 2) ≤ 2 * b := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hc : ∀ c, v c ^ 2 ≤ b ^ 2 := fun c => by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h c) 2
  calc ∑ c, v c ^ 2 ≤ ∑ _c : Fin 4, b ^ 2 := Finset.sum_le_sum fun c _ => hc c
    _ = (2 * b) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
theorem sqrt_sum_sq_add_le_add (p q : Fin 4 → ℝ) :
    Real.sqrt (∑ c, (p c + q c) ^ 2) ≤
      Real.sqrt (∑ c, p c ^ 2) + Real.sqrt (∑ c, q c ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 4)) (WithLp.toLp 2 q)
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using h
theorem sqrt_sum_sq_mul_left {k : ℝ} (hk : 0 ≤ k) (p : Fin 4 → ℝ) :
    Real.sqrt (∑ c, (k * p c) ^ 2) = k * Real.sqrt (∑ c, p c ^ 2) := by
  have h : ∑ c, (k * p c) ^ 2 = k ^ 2 * ∑ c, p c ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => mul_pow _ _ _
  rw [h, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℂ} (hf : Differentiable ℝ f) (c : Fin 4)
    (y : Fin 4 → ℝ) : partialDerivR4 c f y = fderiv ℝ f y (Pi.single c 1) := by
  have hl : HasDerivAt (fun t : ℝ => y + t • (Pi.single c (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single c (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single c (1 : ℝ) : Fin 4 → ℝ)).const_add y
  have hy : HasFDerivAt f (fderiv ℝ f y)
      ((fun t : ℝ => y + t • (Pi.single c (1 : ℝ) : Fin 4 → ℝ)) 0) := by
    simpa using (hf y).hasFDerivAt
  unfold partialDerivR4
  exact (hy.comp_hasDerivAt (0 : ℝ) hl).deriv
theorem gradNorm_bddAbove {f : (Fin 4 → ℝ) → ℂ} (hf : f ∈ smoothCompactSet (Fin 4 → ℝ)) :
    BddAbove (range (gradNorm f)) := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by simp)
  obtain ⟨C, hC⟩ := (hf.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hf.2.fderiv (𝕜 := ℝ))
  refine ⟨Real.sqrt (∑ c : Fin 4, (C * ‖(Pi.single c (1 : ℝ) : Fin 4 → ℝ)‖) ^ 2), ?_⟩
  rintro _ ⟨y, rfl⟩
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [partialDerivR4_eq_fderiv hd]
  exact ((fderiv ℝ f y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))
noncomputable def complexBump : (Fin 4 → ℝ) → ℂ := fun y => (cubeBump y : ℂ)
theorem dotProduct_add_smul_single_sub (w y a δ : Fin 4 → ℝ) (c : Fin 4)
    (hδ : δ = Pi.single c 1) (t : ℝ) :
    w ⬝ᵥ (y + t • δ - a) = w ⬝ᵥ (y - a) + t * w c := by
  have h : y + t • δ - a = (y - a) + t • δ := by abel
  rw [h, dotProduct_add, dotProduct_smul, hδ, dotProduct_single]
  simp
theorem partialDerivR4_modeFun (Q : PointSystem n) (i : Fin n) (ξ : Config n)
    (hX : Differentiable ℝ complexBump) (c : Fin 4) (y : Fin 4 → ℝ) :
    partialDerivR4 c (Q.modeFun i ξ) y =
      (((Q.scale⁻¹ : ℝ) : ℂ) * partialDerivR4 c complexBump (Q.scale⁻¹ • (y - Q.base i)) +
          Complex.I * ((ξ i c : ℝ) : ℂ) * complexBump (Q.scale⁻¹ • (y - Q.base i))) *
        Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ) : ℂ)) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 4 → ℝ, δ = Pi.single c 1 := ⟨_, rfl⟩
  have hin : HasDerivAt (fun t : ℝ => Q.scale⁻¹ • (y + t • δ - Q.base i))
      (Q.scale⁻¹ • δ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + t • δ - Q.base i) δ 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add y).sub_const (Q.base i)
    exact h1.const_smul Q.scale⁻¹
  have hfd : HasFDerivAt complexBump (fderiv ℝ complexBump (Q.scale⁻¹ • (y - Q.base i)))
      ((fun t : ℝ => Q.scale⁻¹ • (y + t • δ - Q.base i)) 0) := by
    simpa using (hX (Q.scale⁻¹ • (y - Q.base i))).hasFDerivAt
  have hχ := hfd.comp_hasDerivAt (0 : ℝ) hin
  have hlin : HasDerivAt (fun t : ℝ => ξ i ⬝ᵥ (y + t • δ - Q.base i)) (ξ i c) 0 := by
    have h1 : (fun t : ℝ => ξ i ⬝ᵥ (y + t • δ - Q.base i)) =
        fun t : ℝ => ξ i ⬝ᵥ (y - Q.base i) + t * ξ i c :=
      funext (dotProduct_add_smul_single_sub _ _ _ _ c hδ)
    rw [h1]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ i c)).const_add (ξ i ⬝ᵥ (y - Q.base i))
  have hexp := ((hlin.ofReal_comp).const_mul Complex.I).cexp
  have hprod := hχ.mul hexp
  have hline : (fun t : ℝ => Q.modeFun i ξ (y + t • (Pi.single c (1 : ℝ) : Fin 4 → ℝ))) =
      ((complexBump ∘ fun t : ℝ => Q.scale⁻¹ • (y + t • δ - Q.base i)) *
        fun t : ℝ => Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y + t • δ - Q.base i) : ℝ) : ℂ))) := by
    subst hδ
    rfl
  unfold partialDerivR4 at *
  rw [hline, hprod.deriv]
  have hp : deriv (fun t : ℝ => complexBump (Q.scale⁻¹ • (y - Q.base i) +
      t • (Pi.single c (1 : ℝ) : Fin 4 → ℝ))) 0 =
      fderiv ℝ complexBump (Q.scale⁻¹ • (y - Q.base i)) δ := by
    have := partialDerivR4_eq_fderiv hX c (Q.scale⁻¹ • (y - Q.base i))
    unfold partialDerivR4 at this
    rw [this, hδ]
  rw [hp, map_smul, Complex.real_smul]
  simp only [Function.comp_apply, zero_smul, add_zero]
  ring
theorem norm_exp_I_mul_ofReal (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I r
theorem setDistR4_anti {A A' B B' : Set (Fin 4 → ℝ)} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDistR4 A' B' ≤ setDistR4 A B := by
  unfold setDistR4
  exact le_iInf₂ fun a ha => le_iInf₂ fun b hb =>
    iInf₂_le_of_le a (hA ha) (iInf₂_le_of_le b (hB hb) le_rfl)
theorem base_mem_outerBox (Q : PointSystem n) (i : Fin n) : Q.base i ∈ Q.outerBox i := by
  have hm := Q.scale_pos
  show EuclideanCoords.supCoord (Q.base i - Q.base i) ≤ 2 * Q.scale / 2
  have h0 : EuclideanCoords.supCoord (Q.base i - Q.base i) = 0 := by
    simp [EuclideanCoords.supCoord]
  rw [h0]
  linarith
theorem boxGap_ne_top (Q : PointSystem n) (hn : 2 ≤ n) : Q.boxGap ≠ ⊤ := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 : Q.boxGap ≤ setDistR4 (Q.outerBox ⟨0, by omega⟩) (Q.outerBox ⟨1, by omega⟩) :=
    iInf_le_of_le _ (iInf_le_of_le _ (iInf_le _ hne))
  have h2 : setDistR4 (Q.outerBox ⟨0, by omega⟩) (Q.outerBox ⟨1, by omega⟩) ≤
      ENNReal.ofReal (euclidNormVec (Q.base ⟨0, by omega⟩ - Q.base ⟨1, by omega⟩)) :=
    iInf₂_le_of_le _ (base_mem_outerBox Q _) (iInf₂_le _ (base_mem_outerBox Q _))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h1.trans h2)
theorem outerBox_subset_closedBallR4 (Q : PointSystem n) (i : Fin n) :
    Q.outerBox i ⊆ closedBallR4 (Q.base i) 1 := by
  intro y hy
  have hy' : EuclideanCoords.supCoord (y - Q.base i) ≤ 2 * Q.scale / 2 := hy
  have hm := Q.scale_pos
  have hc : ∀ c, |(y - Q.base i) c| ≤ Q.scale := fun c =>
    (le_ciSup (f := fun c => |(y - Q.base i) c|) (Set.finite_range _).bddAbove c).trans
      (hy'.trans (by linarith))
  have h := sqrt_sum_sq_le_two_mul hm.le hc
  have h2 := Q.scale_le_half
  show euclidNormVec (y - Q.base i) ≤ 1
  unfold euclidNormVec
  linarith
end ModeCost
open ModeCost in
theorem modeCostOfSeparated_holds
    (hModes : ModesAreLocalCharacters)
    (hExt : complexifyUniqueAndBounded)
    (hBump : GevreyBumpBounds) :
    ModeCostOfSeparated := by
  obtain ⟨-, -, -, -, ⟨hsmooth, hcomp, hbd, -, -, -⟩, -⟩ := hBump
  intro n hn Q hsep c a G T hT ξ hξ
  obtain ⟨-, hc, hG, hmul, -⟩ := id hT
  have hm : 0 < Q.scale := Q.scale_pos
  have hm2 : Q.scale ≤ 1 / 2 := Q.scale_le_half
  have hM : 0 ≤ coordSupNorm ξ := coordSupNorm_nonneg ξ
  have hXs : complexBump ∈ smoothCompactSet (Fin 4 → ℝ) :=
    ⟨Complex.ofRealCLM.contDiff.comp hsmooth,
      hcomp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero⟩
  have hXd : Differentiable ℝ complexBump := hXs.1.differentiable (by simp)
  have hXnorm : ∀ v, ‖complexBump v‖ ≤ 1 := fun v => by
    show ‖((cubeBump v : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbd v).1]
    exact (hbd v).2
  have hXbdd : BddAbove (range fun v => ‖complexBump v‖) :=
    ⟨1, by rintro _ ⟨v, rfl⟩; exact hXnorm v⟩
  obtain ⟨S, hSdef⟩ : ∃ S, S = uniformNorm complexBump := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀, G₀ = gradSupNorm complexBump := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = modeConst := ⟨_, rfl⟩
  have hXS : ∀ v, ‖complexBump v‖ ≤ S := fun v => by
    rw [hSdef]; exact le_ciSup hXbdd v
  have hXG : ∀ v, gradNorm complexBump v ≤ G₀ := fun v => by
    rw [hG₀def]; exact le_ciSup (gradNorm_bddAbove hXs) v
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hXS 0)
  have hC2S : 2 * S ≤ C := by
    rw [hCdef, hSdef]; exact le_max_left _ _
  have hCG : G₀ ≤ C := by
    rw [hCdef, hG₀def]; exact le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hsup : ∀ i, uniformNorm (Q.modeFun i ξ) ≤ S := fun i => by
    refine ciSup_le fun y => ?_
    have h : Q.modeFun i ξ y = complexBump (Q.scale⁻¹ • (y - Q.base i)) *
        Complex.exp (Complex.I * ((ξ i ⬝ᵥ (y - Q.base i) : ℝ) : ℂ)) := rfl
    rw [h, norm_mul, norm_exp_I_mul_ofReal, mul_one]
    exact hXS _
  have hgrad : ∀ i, gradSupNorm (Q.modeFun i ξ) ≤
      Q.scale⁻¹ * G₀ + 2 * (coordSupNorm ξ * S) := fun i => by
    refine ciSup_le fun y => ?_
    obtain ⟨u, hu⟩ : ∃ u, u = Q.scale⁻¹ • (y - Q.base i) := ⟨_, rfl⟩
    have hentry : ∀ k, ‖partialDerivR4 k (Q.modeFun i ξ) y‖ ≤
        Q.scale⁻¹ * ‖partialDerivR4 k complexBump u‖ + |ξ i k| * S := fun k => by
      rw [partialDerivR4_modeFun Q i ξ hXd k y, norm_mul, norm_exp_I_mul_ofReal, mul_one, ← hu]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hm)]
      · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hXS u) (abs_nonneg _)
    calc gradNorm (Q.modeFun i ξ) y
        ≤ Real.sqrt (∑ k, (Q.scale⁻¹ * ‖partialDerivR4 k complexBump u‖ + |ξ i k| * S) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hentry k) 2)
      _ ≤ Real.sqrt (∑ k, (Q.scale⁻¹ * ‖partialDerivR4 k complexBump u‖) ^ 2) +
            Real.sqrt (∑ k, (|ξ i k| * S) ^ 2) := sqrt_sum_sq_add_le_add _ _
      _ ≤ Q.scale⁻¹ * G₀ + 2 * (coordSupNorm ξ * S) := by
          refine add_le_add ?_ (sqrt_sum_sq_le_two_mul (mul_nonneg hM hS0) fun k => ?_)
          · rw [sqrt_sum_sq_mul_left (inv_pos.2 hm).le]
            exact mul_le_mul_of_nonneg_left (hXG u) (inv_pos.2 hm).le
          · rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hS0)]
            exact mul_le_mul_of_nonneg_right (abs_apply_le_coordSupNorm ξ i k) hS0
  obtain ⟨W, hW⟩ : ∃ W, W = max 1 c := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = 1 + Q.scale * coordSupNorm ξ := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := hW ▸ le_max_left _ _
  have hWc : c ≤ W := hW ▸ le_max_right _ _
  have hL1 : 1 ≤ L := by
    rw [hL]; nlinarith [mul_nonneg hm.le hM]
  have hminv : 1 ≤ Q.scale⁻¹ := (one_le_inv₀ hm).2 (by linarith)
  have hentry : ∀ i, max (uniformNorm (Q.modeFun i ξ)) (c * gradSupNorm (Q.modeFun i ξ)) ≤
      C * W * Q.scale⁻¹ * L := fun i => by
    have hone : 1 ≤ W * Q.scale⁻¹ * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hW1 hminv) hL1
    have hgrad' : gradSupNorm (Q.modeFun i ξ) ≤ C * Q.scale⁻¹ * L := by
      have heq : C * Q.scale⁻¹ * L = Q.scale⁻¹ * C + coordSupNorm ξ * C := by
        rw [hL]; field_simp
      rw [heq]
      refine (hgrad i).trans (add_le_add (mul_le_mul_of_nonneg_left hCG (inv_pos.2 hm).le) ?_)
      nlinarith [mul_le_mul_of_nonneg_left hC2S hM]
    refine max_le ?_ ?_
    · calc uniformNorm (Q.modeFun i ξ) ≤ S := hsup i
        _ ≤ C := by linarith
        _ ≤ C * (W * Q.scale⁻¹ * L) := le_mul_of_one_le_right hC0 hone
        _ = C * W * Q.scale⁻¹ * L := by ring
    · have hCmL : 0 ≤ C * Q.scale⁻¹ * L :=
        mul_nonneg (mul_nonneg hC0 (inv_pos.2 hm).le) (by linarith)
      calc c * gradSupNorm (Q.modeFun i ξ) ≤ c * (C * Q.scale⁻¹ * L) :=
            mul_le_mul_of_nonneg_left hgrad' hc.le
        _ ≤ W * (C * Q.scale⁻¹ * L) := mul_le_mul_of_nonneg_right hWc hCmL
        _ = C * W * Q.scale⁻¹ * L := by ring
  have hfin : Q.boxGap ≠ ⊤ := boxGap_ne_top Q hn
  have hd : 0 < Q.boxGap.toReal := ENNReal.toReal_pos hsep.ne' hfin
  have hsupp : ∀ i, tsupport (Q.modeFun i ξ) ⊆ Q.outerBox i := fun i =>
    (hModes n (by omega) Q i ξ hξ).2.1
  have hdist : ∀ i i', i ≠ i' → ENNReal.ofReal Q.boxGap.toReal ≤
      setDistR4 (tsupport (Q.modeFun i ξ)) (tsupport (Q.modeFun i' ξ)) := fun i i' hne => by
    rw [ENNReal.ofReal_toReal hfin]
    exact (iInf_le_of_le i (iInf_le_of_le i' (iInf_le _ hne))).trans
      (setDistR4_anti (hsupp i) (hsupp i'))
  have hmem : Q.modeFamily ξ ∈ smoothComplexTupleSet n := by
    refine ⟨fun i => (hModes n (by omega) Q i ξ hξ).1, fun i i' hne => ?_⟩
    refine Set.disjoint_left.2 fun y hy hy' => ?_
    have h0 : setDistR4 (tsupport (Q.modeFun i ξ)) (tsupport (Q.modeFun i' ξ)) ≤ 0 := by
      refine iInf₂_le_of_le y hy (iInf₂_le_of_le y hy' ?_)
      simp [euclidNormVec]
    have h1 := (hdist i i' hne).trans h0
    exact absurd (ENNReal.ofReal_pos.2 hd) (not_lt.2 h1)
  refine ⟨hmem, ?_, ?_⟩
  · intro i
    rw [← hCdef, ← hW, ← hL]
    exact hentry i
  · have hb := (hExt n hn T hmul).2 c a G hT Q.boxGap.toReal hd ⟨Q.modeFamily ξ, hmem⟩
      (fun i => ⟨closedBallR4 (Q.base i) 1, 1, ⟨Q.base i, rfl⟩, le_rfl,
        (hsupp i).trans (outerBox_subset_closedBallR4 Q i)⟩) hdist
    have hval : complexifyAtModes T Q ξ = complexify T ⟨Q.modeFamily ξ, hmem⟩ :=
      dif_pos hmem
    have hprod : ∏ i, max (uniformNorm (Q.modeFamily ξ i)) (c * gradSupNorm (Q.modeFamily ξ i)) ≤
        (C * W * Q.scale⁻¹ * L) ^ n := by
      calc ∏ i, max (uniformNorm (Q.modeFamily ξ i)) (c * gradSupNorm (Q.modeFamily ξ i))
          ≤ ∏ _i : Fin n, C * W * Q.scale⁻¹ * L :=
            Finset.prod_le_prod
              (fun i _ => le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _))
              (fun i _ => hentry i)
        _ = (C * W * Q.scale⁻¹ * L) ^ n := by simp
    have hw0 : 0 ≤ max 1 (Q.boxGap.toReal ^ (-(a : ℤ))) := le_max_of_le_left zero_le_one
    rw [hval, ← hCdef, ← hW, ← hL]
    unfold PointSystem.sepWeight
    refine hb.trans ((mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (mul_nonneg (by positivity) hG) hw0)).trans (le_of_eq ?_))
    have hz : Q.scale ^ (-(n : ℤ)) = Q.scale⁻¹ ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [hz, mul_pow, mul_pow, mul_pow, mul_pow]
    ring
end YangMills.Construction.ConfigSpace
