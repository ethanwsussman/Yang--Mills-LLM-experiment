import YangMills.ContinuumLimit.OneStepDropsAlongARun
import YangMills.ContinuumLimit.TuningAtAdmissibleTables
import YangMills.Construction.TheStatementsProvedTogether.FromTheFourPointLawOnTheWindowProof
import YangMills.Construction.TheStatementsProvedTogether.FromConcentrationInOneBoxProof
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.BranchHot
open Construction ContinuumLimit
open Construction.TheStatementsProvedTogether
open Construction.ResponseInTheExpansion

def RefinedTable (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  ∃ C₁ M : ℝ, FamilyNorms.RefinedExpansionHolds T y C₁ M

theorem refined_tables : TotalDensities.HoldsAtAdmissibleParameters RefinedTable := by
  obtain ⟨Q,hQ,fL,cR,cS,fN,fC,C₀,h1,h2,hT⟩ := refined_expansion_recovers
  refine ⟨⟨Q,fL,fun _ => C₀,cR,cS,fN,fC,fun _ => 0⟩, ⟨hQ,h1,h2⟩,fun T hTa hM => ?_⟩
  obtain ⟨y₀,C₁,M,hy⟩ := hT T hTa hM.side_ge hM.rt_le hM.threshold_le hM.n₀_ge hM.Cs_ge
    hM.derivBound_ge hM.holds
  exact ⟨y₀, fun y hy' => ⟨C₁,M,hy y hy'⟩⟩

theorem slope_record_cutoffs (a : ℕ → ℝ) {s c : ℝ} (hs : 0 < s)
    (ha : CouplingFlow.HasAverageSlope a s c) :
    ∃ᶠ n : ℕ in atTop, ∀ i < n, s / 2 * ((n:ℝ)-i) ≤ ∑ t ∈ Finset.Ico i n, a t := by
  let A (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, a t) - s / 2 * n
  have unbounded (v : ℝ) : ∃ n, v < A n := by
    obtain ⟨n,hn⟩ := exists_nat_gt ((v + 2*c)/(s/2))
    have hb := (div_lt_iff₀ (by positivity : 0 < s/2)).mp hn
    have hl := (abs_le.mp (ha 0 n (Nat.zero_le n))).1
    simp only [Nat.Ico_zero_eq_range,Nat.cast_zero,sub_zero] at hl
    refine ⟨n, ?_⟩
    dsimp [A]; nlinarith only [hb,hl]
  apply frequently_atTop.2
  intro N
  let S := (Finset.range (N+1)).image A
  have hS : S.Nonempty := by exact ⟨A 0,Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))⟩
  let B := S.max' hS
  let k := Nat.find (unbounded B)
  have hrec : B < A k := Nat.find_spec (unbounded B)
  have hN : N ≤ k := by
    by_contra! h
    have : A k ≤ B := Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
    linarith
  refine ⟨k,hN,fun i hi => ?_⟩
  have ht : A i ≤ B := le_of_not_gt (Nat.find_min (unbounded B) hi)
  have he := ht.trans hrec.le
  dsimp [A] at he
  rw [Finset.sum_Ico_eq_sub _ hi.le]
  linarith

theorem uniform_record_gap {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
    {Kr : WeightedResponses.ResponseParameters} {lam cr s c : ℝ} (hs : 0 < s)
    (ha : CouplingFlow.HasAverageSlope (FamilyNorms.ParameterAssignment.oneLoop T) s c)
    (hr : RunTable T y Kr lam cr) (hF : RefinedTable T y) :
    ∃ H : ℝ, ∃ᶠ k : ℕ in atTop, ∀ (b P : ℝ), H ≤ P → IsTunedAt T y P k b →
      ∀ i < k, P + s/4 ≤ TotalDensityFlow.coupling (T.stepParameters y) b i := by
  obtain ⟨C₁,M,hF⟩ := hF
  let A := C₁ * (2*C₁+1)
  let X := max (1:ℝ) (max (8*M/s) ((8*A/s)^(4/5:ℝ)))
  refine ⟨X + |cr|, (slope_record_cutoffs _ hs ha).mono ?_⟩
  intro k hk b P hP ht
  let x := flowCouplings (T.stepParameters y) b
  let a := FamilyNorms.ParameterAssignment.oneLoop T
  have had := (above_iff_total expansion_gives_total_flow total_density_flow_unique hr).mp ht.1
  have he := (total_flow_of_above_total expansion_gives_total_flow total_density_flow_unique hr ht.1).2
  have hterm : x k = P := (he k le_rfl).symm.trans ht.2
  have hl (t : ℕ) (htk : t ≤ k) : X ≤ x t := by
    have h := hr.descent b had.1 k had.2 t htk
    change lam * ((k:ℝ)-t) - cr ≤ x t - x k at h
    have hd : 0 ≤ lam * ((k:ℝ)-t) := mul_nonneg hr.lam_pos.le (sub_nonneg.mpr (by exact_mod_cast htk))
    linarith [le_abs_self cr]
  have hs₁ (t : ℕ) (htk : t < k) : a t - s/4 ≤ x t - x (t+1) := by
    have hstay : CouplingFlow.StaysAbove y (CouplingFlow.couplingAt (T.stepParameters y) b) t :=
      fun j hj => had.2 j (lt_of_le_of_lt hj htk)
    have hrm := CouplingFlow.followsFlowAbove_couplingAt hF le_rfl b t hstay
    change |x (t+1) - (x t - a t - FamilyNorms.ParameterAssignment.secondStep T t / x t)| ≤
      A * x t ^ (-(5/4):ℝ) at hrm
    have hX := hl t htk.le
    have hA : 0 < A := by dsimp [A]; have := hF.C₁_pos; positivity
    have h₁ := Levels.OneStepDropsAlongARun.remainder_term_le hA hs ((le_max_right _ _).trans ((le_max_right _ _).trans hX))
    have h₂ := Levels.OneStepDropsAlongARun.second_term_le hs (hF.secondStep_le t)
      ((le_max_left _ _).trans hX) ((le_max_left _ _).trans ((le_max_right _ _).trans hX))
    linarith [(abs_le.mp hrm).2, (abs_le.mp h₂).1]
  intro i hi
  have hprefix : ∀ n, i ≤ n → n ≤ k →
      (∑ t ∈ Finset.Ico i n, a t) - s/4*((n:ℝ)-i) ≤ x i - x n := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => simp
    | succ n hin ih =>
        intro hn
        rw [Finset.sum_Ico_succ_top hin, Nat.cast_succ]
        have hp := ih (Nat.le_of_succ_le hn)
        have hstep := hs₁ n hn
        linarith
  have h₁ := hprefix k hi.le le_rfl
  have h₂ := hk i hi
  change s/2*((k:ℝ)-i) ≤ ∑ t ∈ Finset.Ico i k, a t at h₂
  have hinc : (1:ℝ) ≤ (k:ℝ)-i := by
    have hh : (i:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (show i+1 ≤ k from hi)
    linarith
  rw [he i hi.le]
  change P + s/4 ≤ x i
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hinc)]

end YangMills.BranchHot
end



