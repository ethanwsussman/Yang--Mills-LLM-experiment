import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfTheExponential
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogNearOne
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages GaugeFixing LumpContours TorusFields QuaternionExponential QuaternionLog
namespace BondMoves
namespace LocalReparametrization
variable {n : ℕ}
def imaginaryCoord (i : Fin 3) : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ![q.imI, q.imJ, q.imK] i
      map_add' := fun p q => by fin_cases i <;> simp
      map_smul' := fun c q => by fin_cases i <;> simp }
theorem imaginaryCoord_apply (i : Fin 3) (q : ℍ[ℝ]) : imaginaryCoord i q = ![q.imI, q.imJ, q.imK] i := rfl
theorem sum_imaginaryCoord_smul_basis (w : imaginaryQuaternions) :
    ∑ i, imaginaryCoord i (w : ℍ[ℝ]) • imaginaryBasis i = w := by
  apply Subtype.ext
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  simp only [Fin.sum_univ_three, imaginaryCoord_apply, imaginaryBasis]
  ext
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).re
    rw [hre]
    ring
  · show (w : ℍ[ℝ]).imI * 1 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imI
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 1 + (w : ℍ[ℝ]).imK * 0 = (w : ℍ[ℝ]).imJ
    ring
  · show (w : ℍ[ℝ]).imI * 0 + (w : ℍ[ℝ]).imJ * 0 + (w : ℍ[ℝ]).imK * 1 = (w : ℍ[ℝ]).imK
    ring
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_iteratedFDeriv_pi_le_of_forall {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m j : ℕ}
    {F : E → Fin m → ℝ} {x : E} (hF : ContDiffAt ℝ j F x) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ p, ‖iteratedFDeriv ℝ j (fun y => F y p) x‖ ≤ B) : ‖iteratedFDeriv ℝ j F x‖ ≤ B := by
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  have e := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) p).iteratedFDeriv_comp_left hF le_rfl
  have e2 : (iteratedFDeriv ℝ j F x v) p = iteratedFDeriv ℝ j (fun y => F y p) x v := by
    have : (fun y => F y p) = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) p) ∘ F := rfl
    rw [this, e]
    rfl
  rw [e2]
  exact ((iteratedFDeriv ℝ j (fun y => F y p) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h p) (by positivity))
theorem bondMoveLinear_repeatBondsThrice {k : ℕ} (c : Fin k → TorusBond n) (u : Fin k → Fin 3 → ℝ)
    (β : TorusBond n) :
    bondMoveLinear (repeatBondsThrice c) (basisAtEachBond k) β
        (fun p => u (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) =
      ∑ l, if c l = β then ∑ i, u l i • imaginaryBasis i else 0 := by
  rw [bondMoveLinear_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [repeatBondsThrice, basisAtEachBond, Equiv.symm_apply_apply]
  split_ifs <;> simp
end LocalReparametrization
open LocalReparametrization in
theorem perturbLocallyReparametrized_of (he : IteratedDerivBounded) (hl : MinimalLogAnalyticNearOne) :
    PerturbLocallyReparametrized := by
  classical
  obtain ⟨Lg, hLg, hL⟩ := hl
  choose C hC0 hC using he
  set t : Set ℍ[ℝ] := Metric.ball 1 1 with ht
  set CL : ℝ := ∑ i ∈ Finset.range 41, ‖iteratedFDerivWithin ℝ i Lg t 1‖ with hCL
  set Dn : ℝ := 1 + ∑ i ∈ Finset.range 41, C i * 3 ^ i with hDn
  have hDn1 : 1 ≤ Dn := by
    have : 0 ≤ ∑ i ∈ Finset.range 41, C i * 3 ^ i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hC0 i) (by positivity)
    linarith
  set S3 : ℝ := ∑ i : Fin 3, ‖imaginaryCoord i‖ with hS3
  have hS30 : 0 ≤ S3 := Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _
  have h1t : (1 : ℍ[ℝ]) ∈ t := Metric.mem_ball_self one_pos
  have hLg40 : ContDiffOn ℝ 40 Lg t := fun x hx => (hLg x hx).contDiffAt.contDiffWithinAt
  have htopen : IsOpen t := Metric.isOpen_ball
  have hexpIm : ContDiff ℝ ⊤ (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) := by
    have h : AnalyticOnNhd ℝ (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) Set.univ := fun x _ => NormedSpace.exp_analytic x
    exact h.contDiff.comp imaginaryQuaternions.subtypeL.contDiff
  have hexp0 : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit]
  have hLg1 : Lg 1 = 0 := by
    have h := hL 1 (by simp)
    have h2 : (minimalLog (1 : UnitQuaternion) : imaginaryQuaternions) = 0 := by
      have h3 := minimalLog_expUnit (0 : imaginaryQuaternions) (by simpa using Real.pi_pos)
      rwa [hexp0] at h3
    simpa [h2] using h.symm
  refine ⟨fun j => S3 * ((Nat.factorial j : ℝ) * CL * Dn ^ j), ?_⟩
  intro n V k c X τ₀
  let G : TorusBond n → (Fin k → ℝ) → UnitQuaternion := fun β τ =>
    expUnit (bondMoveLinear c X β τ) * (expUnit (bondMoveLinear c X β τ₀))⁻¹
  let cc : TorusBond n → ℍ[ℝ] := fun β => (((expUnit (bondMoveLinear c X β τ₀))⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have hGs : ∀ β, ContDiff ℝ ⊤ (fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ])) := fun β => by
    have : (fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ])) =
        fun τ => NormedSpace.exp ((bondMoveLinear c X β τ : imaginaryQuaternions) : ℍ[ℝ]) * cc β := rfl
    rw [this]
    exact (hexpIm.comp (bondMoveLinear c X β).contDiff).mul contDiff_const
  have hG1 : ∀ β, ((G β τ₀ : UnitQuaternion) : ℍ[ℝ]) = 1 := fun β => by simp [G]
  let m : TorusBond n → ℝ := fun β => ((Finset.univ.filter fun l => c l = β).card : ℝ)
  let A : (Fin k → ℝ) → (Fin (k * 3) → ℝ) := fun τ p =>
    (m (c (finProdFinEquiv.symm p).1))⁻¹ * imaginaryCoord (finProdFinEquiv.symm p).2
      (Lg ((G (c (finProdFinEquiv.symm p).1) τ : UnitQuaternion) : ℍ[ℝ]))
  have hLgG : ∀ β, ContDiffAt ℝ 40 (fun τ => Lg ((G β τ : UnitQuaternion) : ℍ[ℝ])) τ₀ := fun β => by
    have h1 : ContDiffAt ℝ 40 Lg ((G β τ₀ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [hG1]
      exact (hLg 1 h1t).contDiffAt
    exact h1.comp τ₀ ((hGs β).of_le le_top).contDiffAt
  have hAp : ∀ p, ContDiffAt ℝ 40 (fun τ => A τ p) τ₀ := fun p =>
    contDiffAt_const.mul ((imaginaryCoord _).contDiff.contDiffAt.comp τ₀ (hLgG _))
  have hA : ContDiffAt ℝ 40 A τ₀ := contDiffAt_pi.mpr hAp
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · funext p
    simp only [A, hG1, hLg1, map_zero, mul_zero, Pi.zero_apply]
  · have hnear : ∀ᶠ τ in 𝓝 τ₀, ∀ l, ‖((G (c l) τ : UnitQuaternion) : ℍ[ℝ]) - 1‖ < 1 := by
      refine eventually_all.mpr fun l => ?_
      have hc : ContinuousAt (fun τ => ‖((G (c l) τ : UnitQuaternion) : ℍ[ℝ]) - 1‖) τ₀ :=
        (((hGs (c l)).continuous.continuousAt).sub continuousAt_const).norm
      exact hc.eventually_lt continuousAt_const (by simp [hG1])
    refine hnear.mono fun τ hτ => ?_
    funext x i
    rw [perturb_eq_expUnit_mul, perturb_eq_expUnit_mul, perturb_eq_expUnit_mul]
    set β : TorusBond n := (x, i) with hβ
    have hmove : bondMoveLinear (repeatBondsThrice c) (basisAtEachBond k) β (A τ) =
        ∑ l, if c l = β then ∑ j, ((m (c l))⁻¹ * imaginaryCoord j (Lg ((G (c l) τ : UnitQuaternion) : ℍ[ℝ]))) •
          imaginaryBasis j else 0 :=
      bondMoveLinear_repeatBondsThrice c
        (fun l j => (m (c l))⁻¹ * imaginaryCoord j (Lg ((G (c l) τ : UnitQuaternion) : ℍ[ℝ]))) β
    by_cases hex : ∃ l₀, c l₀ = β
    · obtain ⟨l₀, hl₀⟩ := hex
      have hw : ((minimalLog (G β τ) : imaginaryQuaternions) : ℍ[ℝ]) = Lg ((G β τ : UnitQuaternion) : ℍ[ℝ]) :=
        hL _ (by rw [← hl₀]; exact hτ l₀)
      have hm0 : m β ≠ 0 := by
        simp only [m]
        have : 0 < (Finset.univ.filter fun l => c l = β).card :=
          Finset.card_pos.mpr ⟨l₀, by simp [hl₀]⟩
        exact_mod_cast this.ne'
      have hsum : bondMoveLinear (repeatBondsThrice c) (basisAtEachBond k) β (A τ) = minimalLog (G β τ) := by
        rw [hmove]
        have h1 : ∀ l, (if c l = β then ∑ j, ((m (c l))⁻¹ *
              imaginaryCoord j (Lg ((G (c l) τ : UnitQuaternion) : ℍ[ℝ]))) • imaginaryBasis j else 0) =
            if c l = β then (m β)⁻¹ • minimalLog (G β τ) else 0 := by
          intro l
          split_ifs with hcl
          · rw [hcl, ← hw]
            simp only [mul_smul]
            rw [← Finset.smul_sum, sum_imaginaryCoord_smul_basis]
          · rfl
        simp only [h1]
        rw [← Finset.sum_filter, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        have : ((Finset.univ.filter fun l => c l = β).card : ℝ) * (m β)⁻¹ = 1 := mul_inv_cancel₀ hm0
        rw [this, one_smul]
      rw [hsum, expUnit_minimalLog]
      simp only [G]
      rw [mul_assoc, inv_mul_cancel_left]
    · have hall : ∀ l, c l ≠ β := fun l hl => hex ⟨l, hl⟩
      have h0 : ∀ σ : Fin k → ℝ, bondMoveLinear c X β σ = 0 := fun σ => by
        rw [bondMoveLinear_apply]
        exact Finset.sum_eq_zero fun l _ => if_neg (hall l)
      have h1 : bondMoveLinear (repeatBondsThrice c) (basisAtEachBond k) β (A τ) = 0 := by
        rw [hmove]
        exact Finset.sum_eq_zero fun l _ => if_neg (hall l)
      rw [h0, h0, h1, hexp0, one_mul, one_mul]
  · intro hk hu j hj1 hj40
    have hj40' : ((j : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hj40
    have hB : 0 ≤ S3 * ((Nat.factorial j : ℝ) * CL * Dn ^ j) := by positivity
    refine norm_iteratedFDeriv_pi_le_of_forall (hA.of_le hj40') hB fun p => ?_
    set l := (finProdFinEquiv.symm p).1 with hl
    set i := (finProdFinEquiv.symm p).2 with hi
    set β := c l with hβ
    let Lc : ℍ[ℝ] →L[ℝ] ℝ := (m β)⁻¹ • imaginaryCoord i
    have e1 : (fun σ => A σ p) = Lc ∘ fun τ => Lg ((G β τ : UnitQuaternion) : ℍ[ℝ]) := rfl
    have hm1 : 1 ≤ m β := by
      simp only [m]
      have : 0 < (Finset.univ.filter fun l' => c l' = β).card :=
        Finset.card_pos.mpr ⟨l, by simp [hβ]⟩
      exact_mod_cast this
    have hLc : ‖Lc‖ ≤ S3 := by
      have h1 : ‖Lc‖ ≤ ‖imaginaryCoord i‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun q => ?_
        have e : Lc q = (m β)⁻¹ * imaginaryCoord i q := rfl
        rw [e, norm_mul, norm_inv, Real.norm_of_nonneg (by linarith)]
        calc (m β)⁻¹ * ‖imaginaryCoord i q‖ ≤ 1 * ‖imaginaryCoord i q‖ :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hm1) (norm_nonneg _)
          _ ≤ ‖imaginaryCoord i‖ * ‖q‖ := by rw [one_mul]; exact (imaginaryCoord i).le_opNorm q
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun i : Fin 3 => ‖imaginaryCoord i‖)
        (fun _ _ => ContinuousLinearMap.opNorm_nonneg _) (Finset.mem_univ i)
    have hJ : ‖iteratedFDeriv ℝ j (fun τ => Lg ((G β τ : UnitQuaternion) : ℍ[ℝ])) τ₀‖ ≤
        (Nat.factorial j : ℝ) * CL * Dn ^ j := by
      let s : Set (Fin k → ℝ) := (fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ])) ⁻¹' t
      have hso : IsOpen s := htopen.preimage (hGs β).continuous
      have hxs : τ₀ ∈ s := by
        show ((G β τ₀ : UnitQuaternion) : ℍ[ℝ]) ∈ t
        rw [hG1]
        exact h1t
      have hCi : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Lg t ((G β τ₀ : UnitQuaternion) : ℍ[ℝ])‖ ≤ CL := by
        intro i hi
        rw [hG1]
        exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i Lg t 1‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      have hDi : ∀ i, 1 ≤ i → i ≤ j →
          ‖iteratedFDerivWithin ℝ i (fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ])) s τ₀‖ ≤ Dn ^ i := by
        intro i hi1 hi2
        rw [iteratedFDerivWithin_of_isOpen i hso hxs]
        let Rc : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := (ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (cc β)
        have e2 : (fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ])) =
            Rc ∘ fun τ => NormedSpace.exp ((bondMoveLinear c X β τ : imaginaryQuaternions) : ℍ[ℝ]) := rfl
        have hRc : ‖Rc‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
          simp only [Rc, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
          rw [norm_mul, norm_unitQuaternion]
          simp
        have hcd : ContDiffAt ℝ i
            (fun τ => NormedSpace.exp ((bondMoveLinear c X β τ : imaginaryQuaternions) : ℍ[ℝ])) τ₀ :=
          ((hexpIm.comp (bondMoveLinear c X β).contDiff).of_le le_top).contDiffAt
        rw [e2]
        refine (Rc.norm_iteratedFDeriv_comp_left hcd le_rfl).trans ?_
        have hj1' := norm_iteratedFDeriv_exp_comp_le (bondMoveLinear c X β) (hC i) τ₀
        have hΞ : ‖bondMoveLinear c X β‖ ≤ 3 := by
          refine (norm_bondMoveLinear_le c X β).trans ?_
          simp only [hu _, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          exact_mod_cast hk
        have h3 : C i * ‖bondMoveLinear c X β‖ ^ i ≤ C i * 3 ^ i :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hΞ i) (hC0 i)
        have h4 : C i * 3 ^ i ≤ Dn := by
          have h5 := Finset.single_le_sum (f := fun i => C i * (3 : ℝ) ^ i)
            (fun i _ => mul_nonneg (hC0 i) (by positivity)) (Finset.mem_range.mpr (show i < 41 by omega))
          linarith
        calc ‖Rc‖ * ‖iteratedFDeriv ℝ i
              (fun τ => NormedSpace.exp ((bondMoveLinear c X β τ : imaginaryQuaternions) : ℍ[ℝ])) τ₀‖
            ≤ 1 * (C i * ‖bondMoveLinear c X β‖ ^ i) := mul_le_mul hRc hj1' (norm_nonneg _) zero_le_one
          _ ≤ Dn := by rw [one_mul]; exact h3.trans h4
          _ ≤ Dn ^ i := le_self_pow₀ hDn1 (by omega)
      have hmain := norm_iteratedFDerivWithin_comp_le (g := Lg) (f := fun τ => ((G β τ : UnitQuaternion) : ℍ[ℝ]))
        (n := j) (s := s) (t := t) (x := τ₀) (N := 40) hLg40 ((hGs β).contDiffOn.of_le le_top) hj40'
        htopen.uniqueDiffOn hso.uniqueDiffOn (fun _ h => h) hxs hCi hDi
      rw [iteratedFDerivWithin_of_isOpen j hso hxs] at hmain
      exact hmain
    rw [e1]
    refine (Lc.norm_iteratedFDeriv_comp_left ((hLgG β).of_le hj40') le_rfl).trans ?_
    exact mul_le_mul hLc hJ (norm_nonneg _) hS30
end BondMoves
end YangMills.Construction
end
