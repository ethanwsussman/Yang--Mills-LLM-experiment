import YangMills.Construction.ClusterExpansionOfAStep.KernelAlongAMoveProof
import YangMills.Construction.ResponseInTheExpansion.KernelsAtBasesAlongAMove
import YangMills.Construction.ResponseInTheExpansion.TheScoreOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TorusLumps TorusFields BondMoves StepCosts WeightedResponses TopLevelSites
namespace ResponseInTheExpansion
namespace KernelProductProof
private theorem inv_expUnit (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
private theorem partitionFn_pos (s : ℝ) : 0 < partitionFn s := by apply _root_.YangMills.Construction.TorusLumps.KernelMass.zero_lt_partitionFn <;> assumption
private def reLinear : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re
      map_add' := fun p q => by simp
      map_smul' := fun c q => by simp }
private def reMulLeft (q : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℝ := reLinear ∘L ContinuousLinearMap.mul ℝ ℍ[ℝ] q
private theorem reMulLeft_apply (q p : ℍ[ℝ]) : reMulLeft q p = (q * p).re := rfl
private theorem norm_reMulLeft_le (q : ℍ[ℝ]) : ‖reMulLeft q‖ ≤ ‖q‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p => ?_
  rw [reMulLeft_apply, Real.norm_eq_abs]
  exact (abs_re_le_norm _).trans_eq (norm_mul _ _)
section Sum
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
private def sumReExp (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) (τ : E) : ℝ :=
  ∑ i, reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))
private theorem contDiff_reExpTerm (q : ℍ[ℝ]) (Ξ : E →L[ℝ] imaginaryQuaternions) :
    ContDiff ℝ ⊤ fun τ => reMulLeft q (NormedSpace.exp ((Ξ τ : imaginaryQuaternions) : ℍ[ℝ])) :=
  (reMulLeft q).contDiff.comp (contDiff_exp_imaginary.comp Ξ.contDiff)
private theorem contDiff_sumReExp (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) :
    ContDiff ℝ ⊤ (sumReExp q Ξ) :=
  ContDiff.sum fun i _ => contDiff_reExpTerm (q i) (Ξ i)
private theorem norm_iteratedFDeriv_reExpTerm_le (q : ℍ[ℝ]) (Ξ : E →L[ℝ] imaginaryQuaternions) (hq : ‖q‖ ≤ 1)
    {S C : ℝ} (hS : ‖Ξ‖ ≤ S) (hC0 : 0 ≤ C) {j : ℕ}
    (hC : ∀ v : imaginaryQuaternions,
      ‖iteratedFDeriv ℝ j (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) v‖ ≤ C) (τ : E) :
    ‖iteratedFDeriv ℝ j (fun τ => reMulLeft q (NormedSpace.exp ((Ξ τ : imaginaryQuaternions) : ℍ[ℝ]))) τ‖ ≤
      C * S ^ j := by
  have hcd : ContDiffAt ℝ j (fun τ => NormedSpace.exp ((Ξ τ : imaginaryQuaternions) : ℍ[ℝ])) τ :=
    ((contDiff_exp_imaginary.comp Ξ.contDiff).of_le (by exact_mod_cast le_top)).contDiffAt
  have e := (reMulLeft q).norm_iteratedFDeriv_comp_left hcd le_rfl
  refine e.trans ?_
  have h1 := norm_iteratedFDeriv_exp_comp_le Ξ hC τ
  have h2 : ‖reMulLeft q‖ ≤ 1 := (norm_reMulLeft_le _).trans hq
  have h3 : C * ‖Ξ‖ ^ j ≤ C * S ^ j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) hS j) hC0
  calc ‖reMulLeft q‖ * ‖iteratedFDeriv ℝ j (fun τ => NormedSpace.exp ((Ξ τ : imaginaryQuaternions) : ℍ[ℝ])) τ‖
      ≤ 1 * (C * S ^ j) := mul_le_mul h2 (h1.trans h3) (norm_nonneg _) zero_le_one
    _ = C * S ^ j := one_mul _
private theorem norm_iteratedFDeriv_sumReExp_le (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions)
    (hq : ∀ i, ‖q i‖ ≤ 1) (Ms : Finset ι)
    (hoff : ∀ i, i ∉ Ms → Ξ i = 0) {S C : ℝ} (hS : ∀ i, ‖Ξ i‖ ≤ S) (hC0 : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j)
    (hC : ∀ v : imaginaryQuaternions,
      ‖iteratedFDeriv ℝ j (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) v‖ ≤ C) (τ : E) :
    ‖iteratedFDeriv ℝ j (sumReExp q Ξ) τ‖ ≤ Ms.card * (C * S ^ j) := by
  classical
  have hsum : sumReExp q Ξ = fun τ =>
      ∑ i ∈ Finset.univ, reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) := rfl
  rw [hsum, iteratedFDeriv_sum (fun i _ => (contDiff_reExpTerm (q i) (Ξ i)).of_le (by exact_mod_cast le_top))]
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖iteratedFDeriv ℝ j
      (fun τ => reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) τ‖ ≤
      if i ∈ Ms then C * S ^ j else 0 := by
    intro i
    split_ifs with hi
    · exact norm_iteratedFDeriv_reExpTerm_le (q i) (Ξ i) (hq i) (hS i) hC0 hC τ
    · have h0 : (fun τ => reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) =
          fun _ => reMulLeft (q i) (NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ])) := by
        funext σ
        rw [hoff i hi]
        simp
      rw [h0, iteratedFDeriv_const_of_ne (by omega)]
      simp
  calc ∑ i, ‖iteratedFDeriv ℝ j
        (fun τ => reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) τ‖
      ≤ ∑ i, if i ∈ Ms then C * S ^ j else 0 := Finset.sum_le_sum fun i _ => hterm i
    _ = Ms.card * (C * S ^ j) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
private theorem sumReExp_le_add (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) (hq : ∀ i, ‖q i‖ ≤ 1)
    (Ms : Finset ι) (hoff : ∀ i, i ∉ Ms → Ξ i = 0) (τ τ' : E) :
    sumReExp q Ξ τ ≤ sumReExp q Ξ τ' + 2 * Ms.card := by
  classical
  have hone : ∀ (i : ι) (w : imaginaryQuaternions),
      |reMulLeft (q i) (NormedSpace.exp ((w : imaginaryQuaternions) : ℍ[ℝ]))| ≤ 1 := by
    intro i w
    rw [reMulLeft_apply]
    refine (abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h1 : ‖NormedSpace.exp ((w : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 := WeightedResponses.norm_unitQuaternion (expUnit w)
    rw [h1, mul_one]
    exact hq i
  have hdiff : ∀ i, reMulLeft (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) ≤
      reMulLeft (q i) (NormedSpace.exp ((Ξ i τ' : imaginaryQuaternions) : ℍ[ℝ])) + if i ∈ Ms then 2 else 0 := by
    intro i
    split_ifs with hi
    · have h1 := abs_le.mp (hone i (Ξ i τ))
      have h2 := abs_le.mp (hone i (Ξ i τ'))
      linarith [h1.2, h2.1]
    · rw [hoff i hi]
      simp
  unfold sumReExp
  refine (Finset.sum_le_sum fun i _ => hdiff i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith
end Sum
private theorem iteratedDeriv_real_exp (i : ℕ) : iteratedDeriv i Real.exp = Real.exp := by apply _root_.YangMills.Construction.KernelVariation.iteratedDeriv_real_exp <;> assumption
private theorem re_mul_inv_expUnit_mul (q : ℍ[ℝ]) (g : UnitQuaternion) (w : imaginaryQuaternions) :
    (q * (((expUnit w * g)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      reMulLeft (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))
        (NormedSpace.exp (((-w : imaginaryQuaternions) : imaginaryQuaternions) : ℍ[ℝ])) := by
  rw [mul_inv_rev, inv_expUnit, reMulLeft_apply]
  simp only [Submonoid.coe_mul, mul_assoc]
  rfl
end KernelProductProof
open KernelProductProof in
theorem kernelProductAlongPerturbation_of_jets (he : QuaternionExponential.IteratedDerivBounded)
    (hs : BondScoreProperties) : KernelProductAlongPerturbation := by
  classical
  choose C hC0 hC using he
  set Ch : ℝ := 1 + ∑ i ∈ Finset.range 41, C i with hCh
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range 41, C i := Finset.sum_nonneg fun i _ => hC0 i
  have hCh1 : 1 ≤ Ch := by linarith
  have hCi : ∀ i, i ≤ 40 → C i ≤ Ch := fun i hi => by
    have := Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (show i < 41 by omega))
    linarith
  have hfac1 : (1 : ℝ) ≤ (Nat.factorial 40 : ℝ) := by exact_mod_cast Nat.factorial_pos 40
  refine ⟨(Nat.factorial 40 : ℝ) * Ch, one_le_mul_of_one_le_of_one_le hfac1 hCh1, ?_⟩
  intro ℓ x hfit ha hx n _ W V b k c X S hS1 hXS
  have hA1 : 1 ≤ ℓ.coupling * x := one_le_mul_of_one_le_of_one_le ha hx
  set A : ℝ := ℓ.coupling * x with hA
  have hA0 : 0 ≤ A := by linarith
  have hS0 : 0 ≤ S := by linarith
  let F : BlockFrame := stepBlockFrame ℓ.side n
  let W₀ : F.GaugeField 0 := readAtLevel F 0 W
  let β : F.Cell × Fin 4 → TorusBond n := fun y => (toTorusSite (F := F) (j := 1) n y.1, y.2)
  have hper : ∀ i, F.period 1 i = n := fun i => by
    simp [F, BlockFrame.period, stepBlockFrame, BlockFrame.top]
  have hβ : Function.Injective β := by
    intro y y' h
    have hh := Prod.ext_iff.mp h
    have h1 : toTorusSite (F := F) (j := 1) n y.1 = toTorusSite (F := F) (j := 1) n y'.1 := hh.1
    have h2 : y.2 = y'.2 := hh.2
    exact Prod.ext (toTorusSite_injective hper h1) h2
  let Ξ : F.Cell × Fin 4 → (Fin k → ℝ) →L[ℝ] imaginaryQuaternions := fun y => -bondMoveLinear c X (β y)
  let Ms : Finset (F.Cell × Fin 4) := Finset.univ.filter fun y => ∃ l, c l = β y
  have hoff : ∀ y, y ∉ Ms → Ξ y = 0 := by
    intro y hy
    have hno : ∀ l, c l ≠ β y := fun l hl => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hl⟩)
    ext1 τ
    simp only [Ξ, neg_apply, ContinuousLinearMap.zero_apply]
    rw [bondMoveLinear_apply, Finset.sum_eq_zero fun l _ => if_neg (hno l), neg_zero]
  have hMs : (Ms.card : ℝ) ≤ k := by
    have h1 : Ms.image β ⊆ Finset.univ.image c := by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hy).2
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ hβ] at h2
    have h3 : (Finset.univ.image c).card ≤ k := Finset.card_image_le.trans (by simp)
    exact_mod_cast h2.trans h3
  have hΞ : ∀ y, ‖Ξ y‖ ≤ S := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ hS0 fun v => ?_
    simp only [Ξ, neg_apply, norm_neg]
    exact ((bondMoveLinear c X (β y)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((norm_bondMoveLinear_le c X (β y)).trans hXS) (norm_nonneg _))
  let hots := hotLumps ℓ.grid ℓ.threshold (levelSites F 0) W₀
  let Wb : F.Cell × Fin 4 → ℍ[ℝ] := fun y => contourMean ℓ.baseDepth hots b W₀ y
  let qb : F.Cell × Fin 4 → ℍ[ℝ] := fun y =>
    Wb y * (((V (toTorusSite (F := F) (j := 1) n y.1) y.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have hqb : ∀ y, ‖qb y‖ ≤ 1 := by
    intro y
    simp only [qb]
    rw [norm_mul, WeightedResponses.norm_unitQuaternion, mul_one]
    exact norm_contourMean_le _ _ _ _ _
  let zz : ℝ := ∏ y : F.Cell × Fin 4, partitionFn (ℓ.coupling * x * ‖Wb y‖)
  have hzz : 0 < zz := Finset.prod_pos fun y _ => partitionFn_pos _
  have hwt : 0 < zz⁻¹ := inv_pos.mpr hzz
  let Eb : (Fin k → ℝ) → ℝ := fun τ => A * sumReExp qb Ξ τ
  have hterm : ∀ y τ, (Wb y * (((readAtLevel F 1 (perturb c X τ V) y.1 y.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      reMulLeft (qb y) (NormedSpace.exp ((Ξ y τ : imaginaryQuaternions) : ℍ[ℝ])) := by
    intro y τ
    have h1 : readAtLevel F 1 (perturb c X τ V) y.1 y.2 =
        expUnit (bondMoveLinear c X (β y) τ) * V (toTorusSite (F := F) (j := 1) n y.1) y.2 :=
      perturb_eq_expUnit_mul _ _ _ _ _ _
    rw [h1, re_mul_inv_expUnit_mul]
    rfl
  have hK : ∀ τ, kernelProduct ℓ x W (perturb c X τ V) b = zz⁻¹ * Real.exp (Eb τ) := by
    intro τ
    have h1 : kernelProduct ℓ x W (perturb c X τ V) b = Real.exp (Eb τ) / zz := by
      simp only [kernelProduct, bondKernel, zz]
      rw [Finset.prod_div_distrib, ← Real.exp_sum]
      congr 2
      simp only [Eb, sumReExp]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hterm y τ]
      rfl
    rw [h1, div_eq_inv_mul]
  have hEs : ContDiff ℝ 40 Eb := contDiff_const.mul ((contDiff_sumReExp qb Ξ).of_le le_top)
  have hKfun : (fun τ => kernelProduct ℓ x W (perturb c X τ V) b) = fun τ => zz⁻¹ * Real.exp (Eb τ) :=
    funext hK
  have hpos : ∀ τ, 0 < kernelProduct ℓ x W (perturb c X τ V) b := fun τ => by
    rw [hK]
    exact mul_pos hwt (Real.exp_pos _)
  have hexpE : ContDiff ℝ 40 fun τ => Real.exp (Eb τ) := Real.contDiff_exp.comp hEs
  refine ⟨?_, hpos, ?_, ?_, ?_⟩
  · rw [hKfun]
    exact contDiff_const.mul hexpE
  · intro τ i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_of_nonneg (hpos τ).le]
    · have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
      set κ : ℝ := (k : ℝ) + 1 with hκdef
      have hκ : 1 ≤ κ := by linarith
      set D : ℝ := A * κ ^ 2 * Ch * S with hDdef
      have hDi : ∀ i', 1 ≤ i' → i' ≤ i → ‖iteratedFDeriv ℝ i' Eb τ‖ ≤ D ^ i' := by
        intro i' h1 h2
        have hsr := norm_iteratedFDeriv_sumReExp_le qb Ξ hqb Ms hoff hΞ (hC0 i') h1 (hC i') τ
        have hcd : ContDiffAt ℝ i' (sumReExp qb Ξ) τ :=
          ((contDiff_sumReExp _ _).of_le (by exact_mod_cast le_top)).contDiffAt
        have e : ‖iteratedFDeriv ℝ i' Eb τ‖ = A * ‖iteratedFDeriv ℝ i' (sumReExp qb Ξ) τ‖ := by
          have h3 := iteratedFDeriv_const_smul_apply' (a := A) hcd
          simp only [smul_eq_mul] at h3
          show ‖iteratedFDeriv ℝ i' (fun τ => A * sumReExp qb Ξ τ) τ‖ = _
          rw [h3, norm_smul, Real.norm_of_nonneg hA0]
        rw [e]
        have hMκ : (Ms.card : ℝ) ≤ κ := by linarith
        have hSi : 0 ≤ S ^ i' := by positivity
        have hCle : C i' * S ^ i' ≤ Ch * S ^ i' :=
          mul_le_mul_of_nonneg_right (hCi i' (by omega)) hSi
        have hCnn : 0 ≤ C i' * S ^ i' := mul_nonneg (hC0 i') hSi
        have a1 : A ≤ A ^ i' := le_self_pow₀ hA1 (by omega)
        have c1 : Ch ≤ Ch ^ i' := le_self_pow₀ hCh1 (by omega)
        have k1 : κ ≤ (κ ^ 2) ^ i' := by
          have h4 : κ ≤ κ ^ 2 := le_self_pow₀ hκ (by omega)
          exact h4.trans (le_self_pow₀ (one_le_pow₀ hκ) (by omega))
        calc A * ‖iteratedFDeriv ℝ i' (sumReExp qb Ξ) τ‖
            ≤ A * ((Ms.card : ℝ) * (C i' * S ^ i')) := mul_le_mul_of_nonneg_left hsr hA0
          _ ≤ A * (κ * (Ch * S ^ i')) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hMκ hCle hCnn (by linarith)) hA0
          _ = A * Ch * κ * S ^ i' := by ring
          _ ≤ A ^ i' * Ch ^ i' * (κ ^ 2) ^ i' * S ^ i' :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul a1 c1 (by linarith) (by positivity)) k1 (by linarith) (by positivity)) hSi
          _ = D ^ i' := by
            rw [hDdef, mul_pow (A * κ ^ 2 * Ch) S i', mul_pow (A * κ ^ 2) Ch i', mul_pow A (κ ^ 2) i']
            ring
      have hexpb : ‖iteratedFDeriv ℝ i (fun τ => Real.exp (Eb τ)) τ‖ ≤
          (Nat.factorial i : ℝ) * Real.exp (Eb τ) * D ^ i :=
        norm_iteratedFDeriv_comp_le (g := Real.exp) (f := Eb) (n := i) (N := 40) (x := τ)
          (C := Real.exp (Eb τ)) (D := D) Real.contDiff_exp hEs hi'
          (fun i' _ => by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp,
              Real.norm_of_nonneg (Real.exp_pos _).le])
          hDi
      have hcd : ContDiffAt ℝ i (fun τ => Real.exp (Eb τ)) τ := (hexpE.of_le hi').contDiffAt
      have h3 := iteratedFDeriv_const_smul_apply' (a := zz⁻¹) hcd
      simp only [smul_eq_mul] at h3
      rw [hKfun, h3, norm_smul, Real.norm_of_nonneg hwt.le, hK τ]
      have hf1 : (Nat.factorial i : ℝ) ≤ (Nat.factorial 40 : ℝ) ^ i := by
        have h1 : (Nat.factorial i : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hi
        exact h1.trans (le_self_pow₀ hfac1 (by omega))
      have hfin : (Nat.factorial i : ℝ) * D ^ i ≤ ((Nat.factorial 40 : ℝ) * Ch * A * κ ^ 2 * S) ^ i := by
        calc (Nat.factorial i : ℝ) * D ^ i ≤ (Nat.factorial 40 : ℝ) ^ i * D ^ i :=
              mul_le_mul_of_nonneg_right hf1 (by positivity)
          _ = ((Nat.factorial 40 : ℝ) * Ch * A * κ ^ 2 * S) ^ i := by
              rw [← mul_pow, hDdef]
              congr 1
              ring
      calc zz⁻¹ * ‖iteratedFDeriv ℝ i (fun τ => Real.exp (Eb τ)) τ‖
          ≤ zz⁻¹ * ((Nat.factorial i : ℝ) * Real.exp (Eb τ) * D ^ i) :=
            mul_le_mul_of_nonneg_left hexpb hwt.le
        _ = ((Nat.factorial i : ℝ) * D ^ i) * (zz⁻¹ * Real.exp (Eb τ)) := by ring
        _ ≤ ((Nat.factorial 40 : ℝ) * Ch * A * κ ^ 2 * S) ^ i * (zz⁻¹ * Real.exp (Eb τ)) :=
            mul_le_mul_of_nonneg_right hfin (mul_pos hwt (Real.exp_pos _)).le
  · intro τ τ'
    rw [hK τ, hK τ']
    have h1 := sumReExp_le_add qb Ξ hqb Ms hoff τ τ'
    have h2 : Eb τ ≤ 2 * A * k + Eb τ' := by
      simp only [Eb]
      have h3 := mul_le_mul_of_nonneg_left h1 hA0
      have h4 : A * (2 * (Ms.card : ℝ)) ≤ A * (2 * k) :=
        mul_le_mul_of_nonneg_left (by linarith) hA0
      nlinarith
    calc zz⁻¹ * Real.exp (Eb τ) ≤ zz⁻¹ * Real.exp (2 * A * k + Eb τ') :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hwt.le
      _ = Real.exp (2 * A * k) * (zz⁻¹ * Real.exp (Eb τ')) := by rw [Real.exp_add]; ring
  · intro c₀
    obtain ⟨-, hsc, -⟩ := hs ℓ hfit x n b c₀
    let q₀ : ℍ[ℝ] := -(bondMean ℓ W₀ b c₀ * (((V c₀.1 c₀.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    have hq₀ : ‖q₀‖ ≤ 1 := by
      simp only [q₀]
      rw [norm_neg, norm_mul, WeightedResponses.norm_unitQuaternion, mul_one]
      exact norm_bondMean_le _ _ _ _
    let Ξ₀ : (Fin k → ℝ) →L[ℝ] imaginaryQuaternions := -bondMoveLinear c X c₀
    have hΞ₀ : ‖Ξ₀‖ ≤ S := by
      refine ContinuousLinearMap.opNorm_le_bound _ hS0 fun v => ?_
      simp only [Ξ₀, neg_apply, norm_neg]
      exact ((bondMoveLinear c X c₀).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((norm_bondMoveLinear_le c X c₀).trans hXS) (norm_nonneg _))
    let R₀ : ℝ := meanNorm ℓ W b c₀ *
      (deriv partitionFn (ℓ.coupling * x * meanNorm ℓ W b c₀) / partitionFn (ℓ.coupling * x * meanNorm ℓ W b c₀))
    have hform : (fun τ => bondScore ℓ x W (perturb c X τ V) b c₀) =
        (fun _ => R₀) + fun τ => reMulLeft q₀ (NormedSpace.exp ((Ξ₀ τ : imaginaryQuaternions) : ℍ[ℝ])) := by
      funext τ
      have h1 : perturb c X τ V c₀.1 c₀.2 = expUnit (bondMoveLinear c X c₀ τ) * V c₀.1 c₀.2 :=
        perturb_eq_expUnit_mul _ _ _ _ _ _
      rw [hsc W (perturb c X τ V), h1, re_mul_inv_expUnit_mul]
      simp only [Pi.add_apply, q₀, Ξ₀, reMulLeft_apply, neg_mul, Quaternion.re_neg, neg_apply]
      rw [sub_eq_add_neg]
    have hT : ContDiff ℝ ⊤ fun τ => reMulLeft q₀ (NormedSpace.exp ((Ξ₀ τ : imaginaryQuaternions) : ℍ[ℝ])) :=
      contDiff_reExpTerm q₀ Ξ₀
    refine ⟨?_, ?_⟩
    · rw [hform]
      exact contDiff_const.add (hT.of_le le_top)
    · intro τ i hi1 hi
      have hcdT : ContDiffAt ℝ i
          (fun τ => reMulLeft q₀ (NormedSpace.exp ((Ξ₀ τ : imaginaryQuaternions) : ℍ[ℝ]))) τ :=
        (hT.of_le (by exact_mod_cast le_top)).contDiffAt
      have hcdR : ContDiffAt ℝ i (fun _ : Fin k → ℝ => R₀) τ := contDiffAt_const
      rw [hform, iteratedFDeriv_add_apply hcdR hcdT, iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, zero_add]
      refine (norm_iteratedFDeriv_reExpTerm_le q₀ Ξ₀ hq₀ hΞ₀ (hC0 i) (hC i) τ).trans ?_
      have hSi : 0 ≤ S ^ i := by positivity
      have h1 : C i ≤ ((Nat.factorial 40 : ℝ) * Ch) ^ i := by
        have hb : 1 ≤ (Nat.factorial 40 : ℝ) * Ch := one_le_mul_of_one_le_of_one_le hfac1 hCh1
        have h2 : Ch ≤ (Nat.factorial 40 : ℝ) * Ch := le_mul_of_one_le_left (by linarith) hfac1
        exact ((hCi i hi).trans h2).trans (le_self_pow₀ hb (by omega))
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h1 hSi
end ResponseInTheExpansion
end YangMills.Construction
end
