import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMoments
import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.ReflectionPositivity.CentredMomentsAreSumsOfCumulantsProof
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantOfVariablesWithBoundedCentredMoments
import YangMills.Construction.WindowAtItsEnds.TheFactorialSumIsAtMostACount
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants.CentredMomentBound
open YangMills.Construction.Cumulants (mixedCumulant momentGeneratingFunction shiftTuple)
open YangMills.Construction.Probability (IsBoundedRealRV)
open YangMills.Construction.SetPartition (PartitionsFin blockCount blockFactorialSum)
private def clampAbs (C x : ℝ) : ℝ := max (-|C|) (min x |C|)
private theorem abs_clampAbs_le (C x : ℝ) : |clampAbs C x| ≤ |C| := by
  have hC := abs_nonneg C
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
private theorem clampAbs_of_abs_le {C x : ℝ} (h : |x| ≤ C) : clampAbs C x = x := by
  have hx := abs_le.mp (h.trans (le_abs_self C))
  rw [clampAbs, min_eq_left hx.2, max_eq_right hx.1]
private theorem prod_blocks_eq {n : ℕ} (π : PartitionsFin n) (f : Fin n → ℝ) :
    ∏ J ∈ π.parts, ∏ a ∈ J, f a = ∏ a, f a := by
  have h := Finset.prod_biUnion (s := π.parts) (t := id) (f := f) π.disjoint
  rw [π.biUnion_parts] at h
  exact h.symm
abbrev _root_.YangMills.DeltaSharedProofs.p21832 := @prod_blocks_eq
private theorem mixedCumulant_congr_ae {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) {n : ℕ}
    {X Y : Fin n → Ω → ℝ} (h : ∀ i, X i =ᵐ[ν] Y i) : mixedCumulant ν X = mixedCumulant ν Y := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.mixedCumulant_congr_ae <;> assumption
theorem cumulantBoundByCentredMoments_holds
    (hCumulants : YangMills.Construction.Cumulants.CumulantMomentRelations)
    (hMoments : YangMills.Construction.Cumulants.MixedCumulantMomentExpansion)
    (hCount : YangMills.Construction.CouplingFlow.FactorialSumBound) :
    CumulantBoundByCentredMoments := by
  intro Ω _ ν _ n Z G hn hZ hbd hG hJ
  choose C hC using hbd
  set W : Fin n → Ω → ℝ := fun i ω => clampAbs (C i) (Z i ω) with hWdef
  have hWZ : ∀ i, W i =ᵐ[ν] Z i := fun i => by
    filter_upwards [hC i] with ω hω
    exact clampAbs_of_abs_le hω
  have hW : ∀ i, IsBoundedRealRV (W i) := fun i =>
    ⟨measurable_const.max ((hZ i).min measurable_const), |C i|, fun ω => abs_clampAbs_le _ _⟩
  set c : Fin n → ℝ := fun i => -∫ ω, Z i ω ∂ν with hc
  set Y : Fin n → Ω → ℝ := shiftTuple W c with hYdef
  have hYval : ∀ i ω, Y i ω = W i ω - ∫ ω', Z i ω' ∂ν := fun i ω => by
    simp [hYdef, shiftTuple, hc, sub_eq_add_neg]
  have hY : ∀ i, IsBoundedRealRV (Y i) := fun i => by
    obtain ⟨B, hB⟩ := (hW i).bounded
    refine ⟨(hW i).measurable.add_const _, B + |c i|, fun ω => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add_left (hB ω) _)
  have hshift : mixedCumulant ν Y = mixedCumulant ν W :=
    (hCumulants Ω ν n W hW).2.2.2.1 n W c hn hW
  have hcum : mixedCumulant ν Z = mixedCumulant ν Y := by
    rw [hshift]
    exact mixedCumulant_congr_ae ν fun i => (hWZ i).symm
  have hblock : ∀ J : Finset (Fin n), J.Nonempty →
      ‖((∫ ω, ∏ l ∈ J, Y l ω ∂ν : ℝ) : ℂ)‖ ≤ ∏ l ∈ J, G l := fun J hJne => by
    have hint : ∫ ω, ∏ l ∈ J, Y l ω ∂ν = ∫ ω, ∏ i ∈ J, (Z i ω - ∫ ω', Z i ω' ∂ν) ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.2 hWZ] with ω hω
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [hYval, hω l]
    rw [Complex.norm_real, Real.norm_eq_abs, hint]
    exact hJ J hJne
  have hterm : ∀ π : PartitionsFin n,
      ‖(-1 : ℂ) ^ (blockCount π - 1) * ((blockCount π - 1).factorial : ℂ) *
          ∏ J ∈ π.parts, ((∫ ω, ∏ l ∈ J, Y l ω ∂ν : ℝ) : ℂ)‖ ≤
        ((blockCount π - 1).factorial : ℝ) * ∏ i, G i := fun π => by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast,
      norm_prod, ← prod_blocks_eq π G]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun J hJp =>
      hblock J (π.nonempty_of_mem_parts hJp)
  have hprod : 0 ≤ ∏ i, G i := Finset.prod_nonneg fun i _ => hG i
  have hcount : (blockFactorialSum n : ℝ) ≤ 2 ^ n * (n.factorial : ℝ) := by
    have h1 : (blockFactorialSum n : ℝ) ≤ (n.factorial : ℝ) * 2 ^ (n - 1) := by
      exact_mod_cast hCount n (by omega)
    have h2 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n :=
      pow_le_pow_right₀ one_le_two (Nat.sub_le _ _)
    have h3 : (0 : ℝ) ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  rw [hcum, hMoments Ω ν n Y (by omega) hY]
  calc ‖∑ π : PartitionsFin n, (-1 : ℂ) ^ (blockCount π - 1) *
          ((blockCount π - 1).factorial : ℂ) *
            ∏ J ∈ π.parts, ((∫ ω, ∏ l ∈ J, Y l ω ∂ν : ℝ) : ℂ)‖
      ≤ ∑ π : PartitionsFin n, ((blockCount π - 1).factorial : ℝ) * ∏ i, G i :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => hterm π)
    _ = (blockFactorialSum n : ℝ) * ∏ i, G i := by
        rw [← Finset.sum_mul, blockFactorialSum]
        push_cast
        rfl
    _ ≤ 2 ^ n * (n.factorial : ℝ) * ∏ i, G i := mul_le_mul_of_nonneg_right hcount hprod
end YangMills.Construction.AdmissibleConstants.CentredMomentBound
end
