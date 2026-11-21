import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBounds
import YangMills.Construction.ConfigurationSpace.BlockProdDerivBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.BlockProdDeriv
open YangMills.Construction.BumpFunctions YangMills.Construction.WhitneyScales
open scoped ContDiff
variable {n : ℕ}
def coordProd (g : CoordIndex n → ℝ → ℂ) (x : Config n) : ℂ :=
  ∏ ι, g ι (coords x ι)
theorem coords_coordBasis (κ ι : CoordIndex n) :
    coords (coordBasis κ) ι = if ι = κ then 1 else 0 := by
  rcases eq_or_ne ι κ with rfl | h
  · simp [coords, coordBasis]
  · rw [if_neg h]
    unfold coords coordBasis
    by_cases h1 : (ofLex ι).1 = (ofLex κ).1
    · have h2 : (ofLex ι).2 ≠ (ofLex κ).2 := fun h2 => h (ofLex.injective (Prod.ext h1 h2))
      rw [h1]
      simp [h2]
    · simp [Pi.single_eq_of_ne h1]
theorem coords_add_smul_coordBasis (x : Config n) (t : ℝ) (κ ι : CoordIndex n) :
    coords (x + t • coordBasis κ) ι =
      coords x ι + t * (if ι = κ then 1 else 0) := by
  rw [← coords_coordBasis]
  simp [coords]
theorem dirDeriv_coordProd (g : CoordIndex n → ℝ → ℂ) (κ : CoordIndex n) :
    dirDeriv (coordBasis κ) (coordProd g) =
      coordProd (Function.update g κ (deriv (g κ))) := by
  funext x
  have hline : (fun t : ℝ => coordProd g (x + t • coordBasis κ)) =
      fun t => (∏ ι ∈ Finset.univ.erase κ, g ι (coords x ι)) *
        g κ (coords x κ + t) := by
    funext t
    unfold coordProd
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ κ)]
    congr 1
    · refine Finset.prod_congr rfl fun ι hι => ?_
      rw [coords_add_smul_coordBasis, if_neg (Finset.ne_of_mem_erase hι)]
      simp
    · rw [coords_add_smul_coordBasis, if_pos rfl]
      simp
  change lineDeriv ℝ (coordProd g) x (coordBasis κ) = _
  unfold lineDeriv
  rw [hline, deriv_const_mul_field, deriv_comp_const_add, add_zero]
  unfold coordProd
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ κ)]
  congr 1
  · refine Finset.prod_congr rfl fun ι hι => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hι)]
  · rw [Function.update_self]
theorem iterate_dirDeriv_coordProd (g : CoordIndex n → ℝ → ℂ)
    (κ : CoordIndex n) (m : ℕ) :
    (dirDeriv (coordBasis κ))^[m] (coordProd g) =
      coordProd (Function.update g κ (iteratedDeriv m (g κ))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, dirDeriv_coordProd, Function.update_idem,
      Function.update_self, iteratedDeriv_succ]
theorem foldr_iterate_dirDeriv_coordProd (g : CoordIndex n → ℝ → ℂ)
    (α : MultiIdx (CoordIndex n)) (l : List (CoordIndex n)) (hl : l.Nodup) :
    l.foldr (fun ι h => (dirDeriv (coordBasis ι))^[α ι] h) (coordProd g) =
      coordProd (fun ι => if ι ∈ l then iteratedDeriv (α ι) (g ι) else g ι) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih hl.of_cons, iterate_dirDeriv_coordProd]
    congr 1
    funext ι
    by_cases h : ι = a
    · subst h
      simp [(List.nodup_cons.1 hl).1]
    · simp [h]
theorem configMultiDeriv_coordProd (g : CoordIndex n → ℝ → ℂ)
    (α : MultiIdx (CoordIndex n)) :
    configMultiDeriv α (coordProd g) =
      coordProd (fun ι => iteratedDeriv (α ι) (g ι)) := by
  unfold configMultiDeriv iterDirDeriv
  rw [foldr_iterate_dirDeriv_coordProd _ _ _ (Finset.sort_nodup _ _)]
  simp
theorem iteratedDeriv_ofReal_comp_affine (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (a w : ℝ) (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => ((b (a * t - w) : ℝ) : ℂ)) =
      fun t => ((a ^ m * iteratedDeriv m b (a * t - w) : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℝ (iteratedDeriv m b) (a * t - w) :=
      (hb.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)) _
    have h1 : HasDerivAt (iteratedDeriv m b) (iteratedDeriv (m + 1) b (a * t - w)) (a * t - w) := by
      rw [iteratedDeriv_succ]
      exact hd.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => a * t - w) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).sub_const w
    have h3 := (h1.comp t h2).const_mul (a ^ m)
    have h4 := h3.ofReal_comp
    refine h4.deriv.trans ?_
    congr 1
    ring
theorem ofRealFun_blockProd (j : ℕ) (z : IntPoint n) :
    ofRealFun (blockProd j z) =
      coordProd (fun ι t =>
        ((mollifiedUnitIndicator (2 / whitneySide j * t - (z ι : ℝ)) : ℝ) : ℂ)) := by
  funext x
  simp only [ofRealFun, blockProd, coordProd]
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun ι _ => ?_
  congr 2
  ring
theorem contDiff_coords (ι : CoordIndex n) :
    ContDiff ℝ ∞ fun x : Config n => coords x ι :=
  contDiff_apply_apply ℝ ℝ _ _
theorem two_div_whitneySide (j : ℕ) : 2 / whitneySide j = 2 * whitneyRatio⁻¹ * 2 ^ j := by
  unfold whitneySide whitneyScale
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv, inv_inv]
  ring
theorem card_coordIndex (n : ℕ) : Fintype.card (CoordIndex n) = 4 * n := by
  have : Fintype.card (CoordIndex n) = Fintype.card (Fin n × Fin 4) := rfl
  rw [this, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
theorem prod_factorial_le_factorial_order (γ : MultiIdx (CoordIndex n)) :
    ∏ ι, ((γ ι).factorial : ℝ) ≤ ((MultiIdx.order γ).factorial : ℝ) := by
  have h : ∏ ι, (γ ι).factorial ≤ (MultiIdx.order γ).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum _ _)
  exact_mod_cast h
theorem blockProdDerivBound_of_smoothBumps (hbumps : BumpFunctions.SmoothBumpsGevreyBounds) :
    BlockProdDerivBound := by
  obtain ⟨-, -, -, ⟨hbsm, -, -, -, -⟩, -, hder⟩ := hbumps
  intro n _ j z
  refine ⟨?_, fun γ x => ?_⟩
  · have hblock : ContDiff ℝ ∞ (blockProd (n := n) j z) := by
      unfold blockProd
      refine contDiff_prod fun ι _ => hbsm.comp ?_
      exact (((contDiff_const.mul (contDiff_coords ι)).div_const _).sub contDiff_const)
    exact Complex.ofRealCLM.contDiff.comp hblock
  · have hc : 0 < whitneyRatio := isWhitneyRatio_whitneyRatio.1
    have ha : 0 < 2 / whitneySide j := by
      rw [two_div_whitneySide]
      positivity
    have hA : 0 ≤ integralConstBound := zero_le_one.trans (le_max_left _ _)
    have hC : 0 ≤ blockConst := by norm_num [blockConst, gevreyConst]
    rw [ofRealFun_blockProd, configMultiDeriv_coordProd]
    simp only [coordProd, iteratedDeriv_ofReal_comp_affine mollifiedUnitIndicator hbsm]
    generalize hadef : 2 / whitneySide j = a at ha
    calc ‖∏ ι, (((a ^ γ ι * iteratedDeriv (γ ι) mollifiedUnitIndicator
            (a * coords x ι - (z ι : ℝ)) : ℝ)) : ℂ)‖
        = ∏ ι, |a ^ γ ι * iteratedDeriv (γ ι) mollifiedUnitIndicator
            (a * coords x ι - (z ι : ℝ))| := by
          rw [norm_prod]
          exact Finset.prod_congr rfl fun ι _ => Complex.norm_real _
      _ ≤ ∏ ι, (a ^ γ ι * (integralConstBound * blockConst ^ γ ι *
            ((γ ι).factorial : ℝ) ^ 2)) := by
          refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun ι _ => ?_
          rw [abs_mul, abs_of_pos (pow_pos ha _)]
          exact mul_le_mul_of_nonneg_left (hder _ _).2.2 (pow_pos ha _).le
      _ = integralConstBound ^ (4 * n) * (a * blockConst) ^ MultiIdx.order γ *
            (∏ ι, ((γ ι).factorial : ℝ)) ^ 2 := by
          simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow,
            Finset.prod_const, Finset.card_univ, card_coordIndex, mul_pow, MultiIdx.order]
          ring
      _ ≤ integralConstBound ^ (4 * n) * (a * blockConst) ^ MultiIdx.order γ *
            ((MultiIdx.order γ).factorial : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (Finset.prod_nonneg fun _ _ => by positivity)
            (prod_factorial_le_factorial_order γ) 2
      _ = integralConstBound ^ (4 * n) *
            (2 * blockConst * whitneyRatio⁻¹ * 2 ^ j) ^ MultiIdx.order γ *
            ((MultiIdx.order γ).factorial : ℝ) ^ 2 := by
          rw [← hadef, two_div_whitneySide]
          congr 3
          ring
end YangMills.Construction.ConfigurationSpace.BlockProdDeriv
end
