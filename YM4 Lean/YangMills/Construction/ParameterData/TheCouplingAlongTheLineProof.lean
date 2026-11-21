import YangMills.Construction.ParameterData.FirstPassageOfTheFlowProof
import YangMills.Construction.ParameterData.TheCouplingAlongTheLine
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
open CouplingFlow TorusLumps StepReturn
private theorem inv_le_log_increment {A s : ℝ} (hA : 0 < A) (hs : 0 < s) (m : ℕ) :
    1 / (A + s * ((m : ℝ) + 1)) ≤
      (Real.log (1 + s * ((m : ℝ) + 1) / A) - Real.log (1 + s * (m : ℝ) / A)) / s := by
  have hu : 0 < 1 + s * (m : ℝ) / A := by positivity
  have hv : 0 < 1 + s * ((m : ℝ) + 1) / A := by positivity
  have hlog : Real.log (1 + s * ((m : ℝ) + 1) / A) - Real.log (1 + s * (m : ℝ) / A) =
      Real.log ((1 + s * ((m : ℝ) + 1) / A) / (1 + s * (m : ℝ) / A)) :=
    (Real.log_div hv.ne' hu.ne').symm
  have hkey := Real.one_sub_inv_le_log_of_pos (div_pos hv hu)
  rw [hlog, le_div_iff₀ hs]
  refine le_trans (le_of_eq ?_) hkey
  have hD : A + s * ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring
private theorem sum_inv_le_log {x : ℕ → ℝ} {A s : ℝ} {K : ℕ} (hA : 0 < A) (hs : 0 < s)
    (hlow : ∀ l < K, A + s * ((K : ℝ) - l) ≤ 2 * x l) (m : ℕ) (hm : m ≤ K) :
    ∑ l ∈ Finset.Ico (K - m) K, 1 / x l ≤ 2 / s * Real.log (1 + s * (m : ℝ) / A) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlt : K - (m + 1) < K := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    have hidx : K - (m + 1) + 1 = K - m := by omega
    rw [hidx]
    have hih := ih (by omega)
    have hcast : (K : ℝ) - ((K - (m + 1) : ℕ) : ℝ) = (m : ℝ) + 1 := by
      rw [Nat.cast_sub hm]
      push_cast
      ring
    have hl := hlow _ hlt
    rw [hcast] at hl
    have hpos : 0 < A + s * ((m : ℝ) + 1) := by positivity
    have hx : 0 < x (K - (m + 1)) := by linarith
    have h1 : 1 / x (K - (m + 1)) ≤ 2 * (1 / (A + s * ((m : ℝ) + 1))) := by
      rw [div_le_iff₀ hx]
      have : 2 * (1 / (A + s * ((m : ℝ) + 1))) * x (K - (m + 1)) =
          (2 * x (K - (m + 1))) / (A + s * ((m : ℝ) + 1)) := by ring
      rw [this, le_div_iff₀ hpos]
      linarith
    have h2 := inv_le_log_increment hA hs m
    have h3 : 2 / s * Real.log (1 + s * (((m + 1 : ℕ) : ℝ)) / A) =
        2 * ((Real.log (1 + s * ((m : ℝ) + 1) / A) - Real.log (1 + s * (m : ℝ) / A)) / s) +
          2 / s * Real.log (1 + s * (m : ℝ) / A) := by
      push_cast
      ring
    rw [h3]
    linarith
private theorem sub_eq_sum_increments (b d x : ℕ → ℝ) (k K : ℕ) (hk : k ≤ K) :
    x k - x K = ∑ l ∈ Finset.Ico k K, b l + ∑ l ∈ Finset.Ico k K, d l / x l -
      ∑ l ∈ Finset.Ico k K, CouplingFlow.stepRemainder b d x l := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h := ih (by omega)
    have hle : k ≤ k + m := by omega
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top hle, Finset.sum_Ico_succ_top hle,
      Finset.sum_Ico_succ_top hle]
    simp only [CouplingFlow.stepRemainder] at h ⊢
    linarith
private theorem abs_sub_linear_le {b d x : ℕ → ℝ} {c₀ c M Cr X : ℝ} {K k : ℕ} (hk : k ≤ K)
    (hc₀ : 0 < c₀) (hX : 0 < X) (hXK : X ≤ x K)
    (hslope : HasAverageSlope b c₀ c) (hd : ∀ t, |d t| ≤ M)
    (hlow : ∀ l < K, x K + 3 / 4 * c₀ * ((K : ℝ) - l) ≤ 2 * x l)
    (hrem : ∑ l ∈ Finset.range K, |CouplingFlow.stepRemainder b d x l| ≤ Cr) :
    |x k - x K - c₀ * ((K : ℝ) - k)| ≤
      2 * c + Cr + 8 * M / (3 * c₀) * Real.log (1 + 3 * c₀ * ((K - k : ℕ) : ℝ) / (4 * X)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hd 0)
  have hA : 0 < x K := lt_of_lt_of_le hX hXK
  have hs : 0 < 3 / 4 * c₀ := by positivity
  have hsum := sub_eq_sum_increments b d x k K hk
  have hb := hslope k K hk
  have hr : |∑ l ∈ Finset.Ico k K, CouplingFlow.stepRemainder b d x l| ≤ Cr := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hrem)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    intro l hl
    simp only [Finset.mem_Ico, Finset.mem_range] at hl ⊢
    exact hl.2
  have hxpos : ∀ l ∈ Finset.Ico k K, 0 < x l := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have h := hlow l hl'.2
    have hKl : (0 : ℝ) ≤ (K : ℝ) - l := by
      have : (l : ℝ) ≤ K := by exact_mod_cast hl'.2.le
      linarith
    have : 0 ≤ 3 / 4 * c₀ * ((K : ℝ) - l) := by positivity
    linarith
  have hint := sum_inv_le_log hA hs hlow (K - k) (Nat.sub_le K k)
  rw [Nat.sub_sub_self hk] at hint
  have hd1 : |∑ l ∈ Finset.Ico k K, d l / x l| ≤ M * ∑ l ∈ Finset.Ico k K, 1 / x l := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hxl := hxpos l hl
    rw [abs_div, abs_of_pos hxl, mul_one_div]
    exact div_le_div_of_nonneg_right (hd l) hxl.le
  have hmono : Real.log (1 + 3 / 4 * c₀ * ((K - k : ℕ) : ℝ) / x K) ≤
      Real.log (1 + 3 * c₀ * ((K - k : ℕ) : ℝ) / (4 * X)) := by
    have hn : (0 : ℝ) ≤ ((K - k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp : 0 < 1 + 3 / 4 * c₀ * ((K - k : ℕ) : ℝ) / x K := by positivity
    refine Real.log_le_log hp ?_
    have e : 3 * c₀ * ((K - k : ℕ) : ℝ) / (4 * X) = 3 / 4 * c₀ * ((K - k : ℕ) : ℝ) / X := by
      field_simp
    rw [e]
    have := div_le_div_of_nonneg_left (by positivity : 0 ≤ 3 / 4 * c₀ * ((K - k : ℕ) : ℝ)) hX hXK
    linarith
  have hd2 : |∑ l ∈ Finset.Ico k K, d l / x l| ≤
      8 * M / (3 * c₀) * Real.log (1 + 3 * c₀ * ((K - k : ℕ) : ℝ) / (4 * X)) := by
    have e : 8 * M / (3 * c₀) = M * (2 / (3 / 4 * c₀)) := by
      field_simp
      ring
    rw [e, mul_assoc]
    refine hd1.trans (mul_le_mul_of_nonneg_left (hint.trans ?_) hM)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have hexp : x k - x K - c₀ * ((K : ℝ) - k) =
      (∑ l ∈ Finset.Ico k K, b l - ((K : ℝ) - k) * c₀) + ∑ l ∈ Finset.Ico k K, d l / x l -
        ∑ l ∈ Finset.Ico k K, CouplingFlow.stepRemainder b d x l := by
    rw [hsum]
    ring
  rw [hexp]
  rw [abs_le] at hb hr hd2 ⊢
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2, hd2.1, hd2.2]
private theorem abs_couplingAt_succ_sub_le {ℓ : TorusLumps.StepParameters}
    (hret : StepReturn.ExpansionReturnsAt ℓ) {β : ℝ} {t : ℕ}
    (hy : ℓ.y₁ ≤ CouplingFlow.couplingAt ℓ β t)
    (hrow : TorusLumps.HasExpansion ℓ t (CouplingFlow.couplingAt ℓ β t)
      (TorusLumps.couplingFlow ℓ β t).2) :
    |CouplingFlow.couplingAt ℓ β (t + 1) - CouplingFlow.couplingAt ℓ β t| ≤ 2 * ℓ.B := by apply _root_.YangMills.DeltaSharedProofs.p502367 <;> assumption
theorem couplingAlongLine : couplingAlongLineStatement := by
  intro T y D hD g hg hy K β hβ k hk
  have hB := hD.errorMargin
  have hcH : 0 ≤ D.cH := by
    have h := hB.slope 0 0 le_rfl
    have := (abs_nonneg _).trans h
    linarith
  have hCr := hB.Cr_nonneg
  have hc₀ : 0 < D.c₀ := by
    have : (10 : ℝ) < D.c₀ := hB.slope_gt
    linarith
  have hX : 0 < D.X₀ := by
    have := hB.floor_ge
    linarith
  rcases hk.eq_or_lt with rfl | hlt
  · have hz : |D.coupling β k - D.coupling β k - D.c₀ * ((k : ℝ) - k)| = 0 := by simp
    rw [hz]
    have : D.lineGap (k - k) = 2 * D.cH + D.Cr := by simp [TrajectoryParameters.lineGap]
    rw [this]
    linarith
  · obtain ⟨-, -, hcut⟩ := hβ
    have hg2X : D.X₀ ≤ g ^ (-2 : ℤ) :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hy
    have hg216 : 16 * D.cH ≤ g ^ (-2 : ℤ) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hy
    have hBpos : 0 < T.B := hB.admissible.B_pos
    have hBs := hD.shift_ge
    have htop : ∀ l < K, g ^ (-2 : ℤ) + 2 * T.B < D.coupling β l := by
      intro l hl
      have h : g ^ (-2 : ℤ) + D.shift < D.coupling β l := hcut l hl
      linarith
    have habove : ∀ l < K, D.X₀ ≤ D.coupling β l := by
      intro l hl
      have := htop l hl
      linarith
    have hfl : y ≤ D.X₀ := hB.floor_le
    have hK0 : 0 < K := by omega
    have hβX : D.X₀ ≤ β := habove 0 hK0
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hrow := hB.expansion β K' hβX (fun l hl => habove l (by omega))
    have hstep : |D.coupling β (K' + 1) - D.coupling β K'| ≤ 2 * T.B :=
      abs_couplingAt_succ_sub_le hB.returns (hfl.trans (habove K' (by omega))) hrow
    have hlast : g ^ (-2 : ℤ) ≤ D.coupling β (K' + 1) := by
      have h1 := (abs_le.mp hstep).1
      have h2 := htop K' (by omega)
      linarith
    have hXK : D.X₀ ≤ D.coupling β (K' + 1) := hg2X.trans hlast
    have hstay : CouplingFlow.StaysAbove D.X₀ (CouplingFlow.couplingAt (T.stepParameters y) β)
        (K' + 1) := by
      intro l hl
      rcases hl.eq_or_lt with rfl | hl'
      · exact hXK
      · exact habove l hl'
    have bud := (hB.bounds β).boundsUpTo (K' + 1) hstay
    have hline : ∀ l < K' + 1, 3 / 4 * D.c₀ * (((K' + 1 : ℕ) : ℝ) - l) - 2 * D.cH ≤
        D.coupling β l - D.coupling β (K' + 1) :=
      fun l hl => (bud.drop_two_sided l (K' + 1) hl.le le_rfl).1
    have hlow : ∀ l < K' + 1,
        D.coupling β (K' + 1) + 3 / 4 * D.c₀ * (((K' + 1 : ℕ) : ℝ) - l) ≤
          2 * D.coupling β l := by
      intro l hl
      have h1 := hline l hl
      have h2 := htop l hl
      linarith
    have hone : (1 : ℝ) ≤ D.coupling β (K' + 1) := by
      have := hB.floor_ge
      have h8 : (8 : ℝ) ≤ D.X₀ := this
      linarith
    have hpow : D.coupling β (K' + 1) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hone (by norm_num)
    have hsr : ∑ l ∈ Finset.range (K' + 1),
        |CouplingFlow.stepRemainder (FamilyNorms.ParameterAssignment.oneLoop T)
          (FamilyNorms.ParameterAssignment.secondStep T) (D.coupling β) l| ≤
          D.Cr * D.coupling β (K' + 1) ^ (-(1 / 4) : ℝ) := bud.sum_abs_remainder_le
    have hrem : ∑ l ∈ Finset.range (K' + 1),
        |CouplingFlow.stepRemainder (FamilyNorms.ParameterAssignment.oneLoop T)
          (FamilyNorms.ParameterAssignment.secondStep T) (D.coupling β) l| ≤ D.Cr :=
      hsr.trans (mul_le_of_le_one_right hCr hpow)
    have hs : CouplingFlow.HasAverageSlope (FamilyNorms.ParameterAssignment.oneLoop T) D.c₀ D.cH :=
      hB.slope
    exact abs_sub_linear_le hk hc₀ hX hXK hs hB.secondStep_le hlow hrem
end YangMills.Construction.TrajectoryData
end
