import YangMills.Construction.ClusterExpansionOfAStep.AMoveReadAtZero
import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsInMassProofForm
import YangMills.Construction.ClusterExpansionOfAStep.JetsOfTheExponential
import YangMills.Construction.ClusterExpansionOfAStep.KernelAlongAMove
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ResponseInTheExpansion.SizeOfTheMeanOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields TorusLumps BondMoves QuaternionExponential WeightedResponses TopLevelSites
namespace KernelVariation
theorem norm_coe_unitQuaternion_eq_one (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem expUnit_inv (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
theorem partitionFn_pos (s : ℝ) : 0 < partitionFn s := by apply _root_.YangMills.Construction.TorusLumps.KernelMass.zero_lt_partitionFn <;> assumption
def reCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re
      map_add' := fun p q => by simp
      map_smul' := fun c q => by simp }
def reMulCLM (q : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℝ := reCLM ∘L ContinuousLinearMap.mul ℝ ℍ[ℝ] q
theorem reMulCLM_apply (q p : ℍ[ℝ]) : reMulCLM q p = (q * p).re := rfl
theorem abs_re_le_norm_of_quaternion (p : ℍ[ℝ]) : |p.re| ≤ ‖p‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem norm_reMulCLM_le (q : ℍ[ℝ]) : ‖reMulCLM q‖ ≤ ‖q‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p => ?_
  rw [reMulCLM_apply, Real.norm_eq_abs]
  exact (abs_re_le_norm_of_quaternion _).trans_eq (norm_mul _ _)
section SumOfRealParts
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
def sumReExp (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) (τ : E) : ℝ :=
  ∑ i, reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))
theorem contDiff_reMulCLM_exp (q : ℍ[ℝ]) (Ξ : E →L[ℝ] imaginaryQuaternions) :
    ContDiff ℝ ⊤ fun τ => reMulCLM q (NormedSpace.exp ((Ξ τ : imaginaryQuaternions) : ℍ[ℝ])) :=
  (reMulCLM q).contDiff.comp (contDiff_exp_imaginary.comp Ξ.contDiff)
theorem contDiff_sumReExp (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) :
    ContDiff ℝ ⊤ (sumReExp q Ξ) :=
  ContDiff.sum fun i _ => contDiff_reMulCLM_exp (q i) (Ξ i)
theorem norm_iteratedFDeriv_sumReExp_le (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions)
    (hq : ∀ i, ‖q i‖ ≤ 1) (Ms : Finset ι)
    (hoff : ∀ i, i ∉ Ms → Ξ i = 0) {S C : ℝ} (hS : ∀ i, ‖Ξ i‖ ≤ S) (hC0 : 0 ≤ C) {j : ℕ} (hj : 1 ≤ j)
    (hC : ∀ v : imaginaryQuaternions,
      ‖iteratedFDeriv ℝ j (fun w : imaginaryQuaternions => NormedSpace.exp (w : ℍ[ℝ])) v‖ ≤ C) (τ : E) :
    ‖iteratedFDeriv ℝ j (sumReExp q Ξ) τ‖ ≤ Ms.card * (C * S ^ j) := by
  classical
  have hsum : sumReExp q Ξ = fun τ =>
      ∑ i ∈ Finset.univ, reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) := rfl
  rw [hsum, iteratedFDeriv_sum (fun i _ => (contDiff_reMulCLM_exp (q i) (Ξ i)).of_le (by exact_mod_cast le_top))]
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖iteratedFDeriv ℝ j
      (fun τ => reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) τ‖ ≤
      if i ∈ Ms then C * S ^ j else 0 := by
    intro i
    split_ifs with hi
    · have hcd : ContDiffAt ℝ j (fun τ => NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) τ :=
        ((contDiff_exp_imaginary.comp (Ξ i).contDiff).of_le (by exact_mod_cast le_top)).contDiffAt
      have hcomp := (reMulCLM (q i)).norm_iteratedFDeriv_comp_left hcd le_rfl
      refine hcomp.trans ?_
      have hjet := norm_iteratedFDeriv_exp_comp_le (Ξ i) hC τ
      have hre : ‖reMulCLM (q i)‖ ≤ 1 := (norm_reMulCLM_le _).trans (hq i)
      have hpow : C * ‖Ξ i‖ ^ j ≤ C * S ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) (hS i) j) hC0
      calc ‖reMulCLM (q i)‖ *
            ‖iteratedFDeriv ℝ j (fun τ => NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) τ‖
          ≤ 1 * (C * S ^ j) := mul_le_mul hre (hjet.trans hpow) (norm_nonneg _) zero_le_one
        _ = C * S ^ j := one_mul _
    · have hconst : (fun τ => reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) =
          fun _ => reMulCLM (q i) (NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ])) := by
        funext σ
        rw [hoff i hi]
        simp
      rw [hconst, iteratedFDeriv_const_of_ne (by omega)]
      simp
  calc ∑ i, ‖iteratedFDeriv ℝ j
        (fun τ => reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ]))) τ‖
      ≤ ∑ i, if i ∈ Ms then C * S ^ j else 0 := Finset.sum_le_sum fun i _ => hterm i
    _ = Ms.card * (C * S ^ j) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
theorem sumReExp_le (q : ι → ℍ[ℝ]) (Ξ : ι → E →L[ℝ] imaginaryQuaternions) (hq : ∀ i, ‖q i‖ ≤ 1)
    (Ms : Finset ι) (hoff : ∀ i, i ∉ Ms → Ξ i = 0) (τ : E) :
    sumReExp q Ξ τ ≤ sumReExp q Ξ 0 + 2 * Ms.card := by
  classical
  have hone : ∀ (i : ι) (w : imaginaryQuaternions),
      |reMulCLM (q i) (NormedSpace.exp ((w : imaginaryQuaternions) : ℍ[ℝ]))| ≤ 1 := by
    intro i w
    rw [reMulCLM_apply]
    refine (abs_re_le_norm_of_quaternion _).trans ?_
    rw [norm_mul]
    have hunit : ‖NormedSpace.exp ((w : imaginaryQuaternions) : ℍ[ℝ])‖ = 1 :=
      norm_coe_unitQuaternion_eq_one (expUnit w)
    rw [hunit, mul_one]
    exact hq i
  have hdiff : ∀ i, reMulCLM (q i) (NormedSpace.exp ((Ξ i τ : imaginaryQuaternions) : ℍ[ℝ])) ≤
      reMulCLM (q i) (NormedSpace.exp ((Ξ i 0 : imaginaryQuaternions) : ℍ[ℝ])) + if i ∈ Ms then 2 else 0 := by
    intro i
    split_ifs with hi
    · have hτ := abs_le.mp (hone i (Ξ i τ))
      have h0 := abs_le.mp (hone i (Ξ i 0))
      linarith [hτ.2, h0.1]
    · rw [hoff i hi]
      simp
  unfold sumReExp
  refine (Finset.sum_le_sum fun i _ => hdiff i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith
end SumOfRealParts
theorem iteratedDeriv_real_exp (i : ℕ) : iteratedDeriv i Real.exp = Real.exp := by
  induction i with
  | zero => simp
  | succ i ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]
theorem kernelAlongPerturbationBounds_of_iteratedDerivBounded (he : IteratedDerivBounded) :
    KernelAlongPerturbationBounds := by
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
  intro ℓ x ha hx n _ W V k c X hu
  have hA1 : 1 ≤ ℓ.coupling * x := one_le_mul_of_one_le_of_one_le ha hx
  set A : ℝ := ℓ.coupling * x with hA
  have hA0 : 0 ≤ A := by linarith
  let F : BlockFrame := stepBlockFrame ℓ.side n
  let β : F.Cell × Fin 4 → TorusBond n := fun y => (toTorusSite (F := F) (j := 1) n y.1, y.2)
  have hper : ∀ i, F.period 1 i = n := fun i => by
    simp [F, BlockFrame.period, stepBlockFrame, BlockFrame.top]
  have hβ : Function.Injective β := by
    intro y y' h
    have hpair := Prod.ext_iff.mp h
    have hsite : toTorusSite (F := F) (j := 1) n y.1 = toTorusSite (F := F) (j := 1) n y'.1 := hpair.1
    have hdir : y.2 = y'.2 := hpair.2
    exact Prod.ext (toTorusSite_injective hper hsite) hdir
  let Ξ : F.Cell × Fin 4 → (Fin k → ℝ) →L[ℝ] imaginaryQuaternions := fun y => -bondMoveLinear c X (β y)
  let Ms : Finset (F.Cell × Fin 4) := Finset.univ.filter fun y => ∃ l, c l = β y
  have hoff : ∀ y, y ∉ Ms → Ξ y = 0 := by
    intro y hy
    have hno : ∀ l, c l ≠ β y := fun l hl => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, l, hl⟩)
    ext1 τ
    simp only [Ξ, neg_apply, zero_apply]
    rw [bondMoveLinear_apply, Finset.sum_eq_zero fun l _ => if_neg (hno l), neg_zero]
  have hMs : (Ms.card : ℝ) ≤ k := by
    have himage : Ms.image β ⊆ Finset.univ.image c := by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hy).2
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩
    have hcard := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ hβ] at hcard
    have hck : (Finset.univ.image c).card ≤ k := Finset.card_image_le.trans (by simp)
    exact_mod_cast hcard.trans hck
  have hΞ : ∀ y, ‖Ξ y‖ ≤ k := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _) fun v => ?_
    simp only [Ξ, neg_apply, norm_neg]
    refine ((bondMoveLinear c X (β y)).le_opNorm v).trans ?_
    refine mul_le_mul_of_nonneg_right ((norm_bondMoveLinear_le c X (β y)).trans ?_) (norm_nonneg _)
    simp only [hu _, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_rfl
  let hots := hotLumps ℓ.grid ℓ.threshold (levelSites F 0) W
  let Wb : (F.Cell → F.Site 0) → F.Cell × Fin 4 → ℍ[ℝ] := fun b y => contourMean ℓ.baseDepth hots b W y
  let qb : (F.Cell → F.Site 0) → F.Cell × Fin 4 → ℍ[ℝ] := fun b y =>
    Wb b y * (((V (toTorusSite (F := F) (j := 1) n y.1) y.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  have hqb : ∀ b y, ‖qb b y‖ ≤ 1 := by
    intro b y
    simp only [qb]
    rw [norm_mul, norm_coe_unitQuaternion_eq_one, mul_one]
    exact norm_contourMean_le _ _ _ _ _
  let zz : (F.Cell → F.Site 0) → ℝ := fun b =>
    ∏ y : F.Cell × Fin 4, partitionFn (ℓ.coupling * x * ‖Wb b y‖)
  have hzz : ∀ b, 0 < zz b := fun b => Finset.prod_pos fun y _ => partitionFn_pos _
  let B := baseChoices ℓ W
  let wt : (F.Cell → F.Site 0) → ℝ := fun b => (1 / (B.card : ℝ)) * (zz b)⁻¹
  have hwt : ∀ b, 0 ≤ wt b := fun b => mul_nonneg (by positivity) (inv_pos.mpr (hzz b)).le
  let Eb : (F.Cell → F.Site 0) → (Fin k → ℝ) → ℝ := fun b τ => A * sumReExp (qb b) Ξ τ
  have hterm : ∀ b y τ,
      (Wb b y * (((readAtLevel F 1 (perturb c X τ V) y.1 y.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      reMulCLM (qb b y) (NormedSpace.exp ((Ξ y τ : imaginaryQuaternions) : ℍ[ℝ])) := by
    intro b y τ
    have hread : readAtLevel F 1 (perturb c X τ V) y.1 y.2 =
        expUnit (bondMoveLinear c X (β y) τ) * V (toTorusSite (F := F) (j := 1) n y.1) y.2 :=
      perturb_eq_expUnit_mul _ _ _ _ _ _
    rw [hread, mul_inv_rev, expUnit_inv, reMulCLM_apply]
    simp only [qb, Submonoid.coe_mul, mul_assoc]
    rfl
  have hK : ∀ τ, kernelAlongPerturbation ℓ x W V c X τ = ∑ b ∈ B, wt b * Real.exp (Eb b τ) := by
    intro τ
    simp only [kernelAlongPerturbation, averagedKernel]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hprod : ∏ y : F.Cell × Fin 4, bondKernel ℓ x W (readAtLevel F 1 (perturb c X τ V)) b y =
        Real.exp (Eb b τ) / zz b := by
      simp only [bondKernel, zz]
      rw [Finset.prod_div_distrib, ← Real.exp_sum]
      congr 2
      simp only [Eb, sumReExp]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← hterm b y τ]
      rfl
    simp only [wt]
    rw [show (∏ c_1 : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X τ V)) b c_1) =
      Real.exp (Eb b τ) / zz b from hprod]
    ring
  have hEs : ∀ b, ContDiff ℝ 40 (Eb b) := fun b =>
    contDiff_const.mul ((contDiff_sumReExp (qb b) Ξ).of_le le_top)
  have hKfun : kernelAlongPerturbation ℓ x W V c X = fun τ => ∑ b ∈ B, wt b * Real.exp (Eb b τ) :=
    funext hK
  have hnn : ∀ τ, 0 ≤ kernelAlongPerturbation ℓ x W V c X τ := fun τ => by
    rw [hK]
    exact Finset.sum_nonneg fun b _ => mul_nonneg (hwt b) (Real.exp_pos _).le
  have hterms : ∀ b, ContDiff ℝ 40 fun τ => wt b * Real.exp (Eb b τ) := fun b =>
    contDiff_const.mul (Real.contDiff_exp.comp (hEs b))
  refine ⟨?_, hnn, ?_, ?_⟩
  · rw [hKfun]
    exact ContDiff.sum fun b _ => hterms b
  · intro τ i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Real.norm_of_nonneg (hnn τ)]
    · have hi' : ((i : ℕ) : WithTop ℕ∞) ≤ 40 := by exact_mod_cast hi
      set κ : ℝ := (k : ℝ) + 1 with hκdef
      have hκ : 1 ≤ κ := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      set D : ℝ := A * κ ^ 2 * Ch with hDdef
      have hDi : ∀ b, ∀ i', 1 ≤ i' → i' ≤ i → ‖iteratedFDeriv ℝ i' (Eb b) τ‖ ≤ D ^ i' := by
        intro b i' hlow hhigh
        have hsr := norm_iteratedFDeriv_sumReExp_le (qb b) Ξ (hqb b) Ms hoff hΞ (hC0 i') hlow (hC i') τ
        have hcd : ContDiffAt ℝ i' (sumReExp (qb b) Ξ) τ :=
          ((contDiff_sumReExp _ _).of_le (by exact_mod_cast le_top)).contDiffAt
        have hscale : ‖iteratedFDeriv ℝ i' (Eb b) τ‖ =
            A * ‖iteratedFDeriv ℝ i' (sumReExp (qb b) Ξ) τ‖ := by
          have hsmul := iteratedFDeriv_const_smul_apply' (a := A) hcd
          simp only [smul_eq_mul] at hsmul
          show ‖iteratedFDeriv ℝ i' (fun τ => A * sumReExp (qb b) Ξ τ) τ‖ = _
          rw [hsmul, norm_smul, Real.norm_of_nonneg hA0]
        rw [hscale]
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hkκ : (k : ℝ) ≤ κ := by linarith
        have hMκ : (Ms.card : ℝ) ≤ κ := hMs.trans hkκ
        have hCle : C i' * (k : ℝ) ^ i' ≤ Ch * κ ^ i' :=
          mul_le_mul (hCi i' (by omega)) (pow_le_pow_left₀ hk0 hkκ i') (by positivity) (by linarith)
        have hCnn : 0 ≤ C i' * (k : ℝ) ^ i' := mul_nonneg (hC0 i') (by positivity)
        have hApow : A ≤ A ^ i' := le_self_pow₀ hA1 (by omega)
        have hChpow : Ch ≤ Ch ^ i' := le_self_pow₀ hCh1 (by omega)
        have hκpow : κ * κ ^ i' ≤ (κ ^ 2) ^ i' := by
          rw [← pow_succ', ← pow_mul]
          exact pow_le_pow_right₀ hκ (by omega)
        calc A * ‖iteratedFDeriv ℝ i' (sumReExp (qb b) Ξ) τ‖
            ≤ A * ((Ms.card : ℝ) * (C i' * (k : ℝ) ^ i')) := mul_le_mul_of_nonneg_left hsr hA0
          _ ≤ A * (κ * (Ch * κ ^ i')) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hMκ hCle hCnn (by linarith)) hA0
          _ = A * Ch * (κ * κ ^ i') := by ring
          _ ≤ A ^ i' * Ch ^ i' * (κ ^ 2) ^ i' :=
            mul_le_mul (mul_le_mul hApow hChpow (by linarith) (by positivity)) hκpow
              (by positivity) (by positivity)
          _ = D ^ i' := by
            rw [hDdef, mul_pow (A * κ ^ 2) Ch i', mul_pow A (κ ^ 2) i']
            exact mul_right_comm (A ^ i') (Ch ^ i') ((κ ^ 2) ^ i')
      have hexpb : ∀ b, ‖iteratedFDeriv ℝ i (fun τ => Real.exp (Eb b τ)) τ‖ ≤
          (Nat.factorial i : ℝ) * Real.exp (Eb b τ) * D ^ i := fun b =>
        norm_iteratedFDeriv_comp_le (g := Real.exp) (f := Eb b) (n := i) (N := 40) (x := τ)
          (C := Real.exp (Eb b τ)) (D := D) Real.contDiff_exp (hEs b) hi'
          (fun i' _ => by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp,
              Real.norm_of_nonneg (Real.exp_pos _).le])
          (hDi b)
      have hone : ∀ b, ‖iteratedFDeriv ℝ i (fun τ => wt b * Real.exp (Eb b τ)) τ‖ ≤
          wt b * ((Nat.factorial i : ℝ) * Real.exp (Eb b τ) * D ^ i) := by
        intro b
        have hcd : ContDiffAt ℝ i (fun τ => Real.exp (Eb b τ)) τ :=
          ((Real.contDiff_exp.comp (hEs b)).of_le hi').contDiffAt
        have hsmul := iteratedFDeriv_const_smul_apply' (a := wt b) hcd
        simp only [smul_eq_mul] at hsmul
        rw [hsmul, norm_smul, Real.norm_of_nonneg (hwt b)]
        exact mul_le_mul_of_nonneg_left (hexpb b) (hwt b)
      rw [hKfun, iteratedFDeriv_sum (fun b _ => (hterms b).of_le hi'), Finset.sum_apply]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun b _ => hone b).trans ?_)
      have hsum : ∑ b ∈ B, wt b * ((Nat.factorial i : ℝ) * Real.exp (Eb b τ) * D ^ i) =
          ((Nat.factorial i : ℝ) * D ^ i) * ∑ b ∈ B, wt b * Real.exp (Eb b τ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hsum]
      refine mul_le_mul_of_nonneg_right ?_
        (Finset.sum_nonneg fun b _ => mul_nonneg (hwt b) (Real.exp_pos _).le)
      have hf1 : (Nat.factorial i : ℝ) ≤ (Nat.factorial 40 : ℝ) ^ i := by
        have hfac : (Nat.factorial i : ℝ) ≤ Nat.factorial 40 := by exact_mod_cast Nat.factorial_le hi
        exact hfac.trans (le_self_pow₀ hfac1 (by omega))
      calc (Nat.factorial i : ℝ) * D ^ i ≤ (Nat.factorial 40 : ℝ) ^ i * D ^ i :=
            mul_le_mul_of_nonneg_right hf1 (by positivity)
        _ = ((Nat.factorial 40 : ℝ) * Ch * A * κ ^ 2) ^ i := by
            rw [← mul_pow, hDdef]
            congr 1
            rw [mul_assoc (Nat.factorial 40 : ℝ) Ch A, mul_assoc (Nat.factorial 40 : ℝ),
              mul_comm (A * κ ^ 2) Ch, mul_assoc Ch A]
  · intro τ
    rw [hK τ, hK 0, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have hle := sumReExp_le (qb b) Ξ (hqb b) Ms hoff τ
    have hE : Eb b τ ≤ 2 * A * k + Eb b 0 := by
      simp only [Eb]
      have hscaled := mul_le_mul_of_nonneg_left hle hA0
      have hcount : A * (2 * (Ms.card : ℝ)) ≤ A * (2 * k) :=
        mul_le_mul_of_nonneg_left (by linarith) hA0
      nlinarith
    calc wt b * Real.exp (Eb b τ) ≤ wt b * Real.exp (2 * A * k + Eb b 0) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (hwt b)
      _ = Real.exp (2 * A * k) * (wt b * Real.exp (Eb b 0)) := by rw [Real.exp_add]; ring
end KernelVariation
end YangMills.Construction
end
