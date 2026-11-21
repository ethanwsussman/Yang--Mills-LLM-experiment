import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.ResponseInTheExpansion.ResponseAlongTheFlowProof
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import YangMills.Construction.WindowOfTheParameters.TheExpansionGivesTheTotalFlow
import YangMills.Construction.WindowOfTheParameters.TotalFlowIsOne
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.ResponseInTheExpansion

def Run (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ) (k : ℕ) : Prop :=
  ∀ j ≤ k, y ≤ flowCouplings (T.stepParameters y) β j

def Above (T : RenormalizationStepParameters.ParameterAssignment) (y β : ℝ) (K : ℕ) : Prop :=
  y ≤ β ∧ ∀ j < K, y ≤ flowCouplings (T.stepParameters y) β j

structure RunTable (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
    (Kr : WeightedResponses.ResponseParameters) (lam c₅ : ℝ) : Prop where
  adm : T.Admissible
  floor : T.floorMin ≤ y
  returns : StepReturn.ExpansionReturnsAt (T.stepParameters y)
  bare : ∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)
  response : Kr.Admissible (T.stepParameters y)
  lam_pos : 0 < lam
  descent : WeightedResponses.HasLinearDescent (T.stepParameters y) lam c₅
  coeff : ∀ (β : ℝ) (k : ℕ), Run T y β k → ∃ al : ℕ → ℝ, IsChainResponseCoeff (T.stepParameters y) Kr β k al
  near : ∀ (β : ℝ) (k : ℕ) (al : ℕ → ℝ), Run T y β k → IsChainResponseCoeff (T.stepParameters y) Kr β k al →
    |al k - 1| ≤ 1 / 4
  unique : ∀ (β : ℝ) (k : ℕ) (al al' : ℕ → ℝ), Run T y β k →
    IsChainResponseCoeff (T.stepParameters y) Kr β k al → IsChainResponseCoeff (T.stepParameters y) Kr β k al' →
      ∀ j ≤ k, al j = al' j

open Classical in
def runSlope (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
    (Kr : WeightedResponses.ResponseParameters) (β : ℝ) (k : ℕ) : ℝ :=
  if h : ∃ al : ℕ → ℝ, IsChainResponseCoeff (T.stepParameters y) Kr β k al then h.choose k else 1

def runDomain (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (k : ℕ) : Set ℝ :=
  {β | y + 2 * T.B < β ∧ ∀ j < k, y + 2 * T.B < flowCouplings (T.stepParameters y) β j}

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : WeightedResponses.ResponseParameters} {lam c₅ : ℝ}

namespace RunAboveTheFloor

theorem above_mono {β : ℝ} {K K' : ℕ} (h : Above T y β K') (hK : K ≤ K') : Above T y β K :=
  ⟨h.1, fun j hj => h.2 j (lt_of_lt_of_le hj hK)⟩

theorem run_mono {β : ℝ} {k k' : ℕ} (h : Run T y β k') (hk : k ≤ k') : Run T y β k :=
  fun j hj => h j (hj.trans hk)

theorem above_succ_of_run {β : ℝ} {k : ℕ} (h : Run T y β k) : Above T y β (k + 1) :=
  ⟨h 0 (Nat.zero_le k), fun j hj => h j (Nat.lt_succ_iff.mp hj)⟩

theorem run_of_above_succ {β : ℝ} {k : ℕ} (h : Above T y β (k + 1)) : Run T y β k :=
  fun j hj => h.2 j (Nat.lt_succ_of_le hj)

theorem above_succ_iff_run {β : ℝ} {k : ℕ} : Above T y β (k + 1) ↔ Run T y β k :=
  ⟨run_of_above_succ, above_succ_of_run⟩

private theorem coldResponseChain_congr (ℓ : TorusLumps.StepParameters) (β : ℝ) (x : ℕ → ℝ) {a a' : ℕ → ℝ}
    (t : ℕ) (h : ∀ i < t, a i = a' i) : coldResponseChain ℓ β x a t = coldResponseChain ℓ β x a' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [coldResponseChain]
    rw [ih fun i hi => h i (by omega), h t (by omega)]

private theorem isChainResponseCoeff_congr {ℓ : TorusLumps.StepParameters} {K : WeightedResponses.ResponseParameters}
    {β : ℝ} {k : ℕ} {a a' : ℕ → ℝ} (h : IsChainResponseCoeff ℓ K β k a) (hh : ∀ i ≤ k, a i = a' i) :
    IsChainResponseCoeff ℓ K β k a' := by
  refine ⟨by rw [← hh 0 (Nat.zero_le _)]; exact h.zero_eq, fun j hj => ?_⟩
  rw [← hh j hj, ← coldResponseChain_congr ℓ β (flowCouplings ℓ β) j fun i hi => hh i (by omega)]
  exact h.bounds j hj

private theorem isChainResponseCoeff_of_le {ℓ : TorusLumps.StepParameters} {K : WeightedResponses.ResponseParameters}
    {β : ℝ} {k j : ℕ} {a : ℕ → ℝ} (h : IsChainResponseCoeff ℓ K β k a) (hj : j ≤ k) :
    IsChainResponseCoeff ℓ K β j a :=
  ⟨h.zero_eq, fun i hi => h.bounds i (hi.trans hj)⟩

end RunAboveTheFloor

theorem chainFunctional_flow (ℓ : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) :
    WeightedResponses.chainFunctional ℓ β (flowCouplings ℓ β) t = (TorusLumps.couplingFlow ℓ β t).2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show TorusLumps.kernelImage ℓ (flowCouplings ℓ β t) (WeightedResponses.chainFunctional ℓ β (flowCouplings ℓ β) t) =
      TorusLumps.kernelImage ℓ (TorusLumps.couplingFlow ℓ β t).1 (TorusLumps.couplingFlow ℓ β t).2
    rw [ih]
    rfl

theorem hasExpansion_of_above (h : RunTable T y Kr lam c₅) {β : ℝ} {t : ℕ} (hβ : Above T y β t) :
    TorusLumps.HasExpansion (T.stepParameters y) t (flowCouplings (T.stepParameters y) β t)
      (TorusLumps.couplingFlow (T.stepParameters y) β t).2 := by
  induction t with
  | zero => exact h.bare β hβ.1
  | succ t ih =>
    have hx : y ≤ flowCouplings (T.stepParameters y) β t := hβ.2 t (Nat.lt_succ_self t)
    exact (ResponseAlongFlow.expansion_step h.returns hx
      (ih (RunAboveTheFloor.above_mono hβ (Nat.le_succ t)))).1

theorem abs_flow_step_le (h : RunTable T y Kr lam c₅) {β : ℝ} {t : ℕ} (hβ : Run T y β t) :
    |flowCouplings (T.stepParameters y) β (t + 1) - flowCouplings (T.stepParameters y) β t| ≤ 2 * T.B :=
  (ResponseAlongFlow.expansion_step h.returns (hβ t le_rfl)
    (hasExpansion_of_above h (RunAboveTheFloor.above_mono (RunAboveTheFloor.above_succ_of_run hβ)
      (Nat.le_succ t)))).2.1

theorem total_flow_of_above (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) {β : ℝ} {t : ℕ} (hβ : Above T y β t) :
    TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β t ∧
      ∀ j ≤ t, TotalDensityFlow.coupling (T.stepParameters y) β j = flowCouplings (T.stepParameters y) β j := by
  have hadm : Conventions.IsAdmissibleBlockingFactor (T.stepParameters y).side :=
    ⟨h.adm.L_odd, le_trans (by norm_num) h.adm.L_ge⟩
  have hside : 2 ≤ (T.stepParameters y).side := le_trans (by norm_num) h.adm.L_ge
  have hflow : TotalDensityFlow.IsFlowUpTo (T.stepParameters y) β t (flowCouplings (T.stepParameters y) β) := by
    refine hGives T y h.adm (h.adm.fits y h.floor) hadm β t _ rfl (fun j hj => hβ.2 j hj) ?_
    intro j hj
    rw [chainFunctional_flow]
    exact hasExpansion_of_above h (RunAboveTheFloor.above_mono hβ hj)
  obtain ⟨hD, he⟩ := hUniq (T.stepParameters y) β t _ hside hflow
  exact ⟨hD, fun j hj => (he j hj).symm⟩

theorem above_iff_total (hGives : TotalDensityFlow.ExpansionGivesFlow) (hUniq : TotalDensityFlow.FlowIsUnique)
    (h : RunTable T y Kr lam c₅) {β : ℝ} {K : ℕ} :
    (y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) ↔ Above T y β K := by
  constructor
  · intro hT
    induction K with
    | zero => exact ⟨hT.1, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ K ih =>
      have hK : Above T y β K := ih ⟨hT.1, fun j hj => hT.2 j (Nat.lt_succ_of_lt hj)⟩
      have he := (total_flow_of_above hGives hUniq h hK).2
      refine ⟨hT.1, fun j hj => ?_⟩
      rw [← he j (Nat.lt_succ_iff.mp hj)]
      exact hT.2 j hj
  · intro hA
    have he := (total_flow_of_above hGives hUniq h hA).2
    refine ⟨hA.1, fun j hj => ?_⟩
    rw [he j hj.le]
    exact hA.2 j hj

theorem total_flow_of_above_total (hGives : TotalDensityFlow.ExpansionGivesFlow)
    (hUniq : TotalDensityFlow.FlowIsUnique) (h : RunTable T y Kr lam c₅) {β : ℝ} {K : ℕ}
    (hβ : y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) :
    TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K ∧
      ∀ j ≤ K, TotalDensityFlow.coupling (T.stepParameters y) β j = flowCouplings (T.stepParameters y) β j :=
  total_flow_of_above hGives hUniq h ((above_iff_total hGives hUniq h).mp hβ)

theorem runSlope_isChain (h : RunTable T y Kr lam c₅) {β : ℝ} {k : ℕ} (hr : Run T y β k) :
    IsChainResponseCoeff (T.stepParameters y) Kr β k (runSlope T y Kr β) := by
  obtain ⟨al, hal⟩ := h.coeff β k hr
  have hagree : ∀ j ≤ k, al j = runSlope T y Kr β j := by
    intro j hj
    have hrj : Run T y β j := RunAboveTheFloor.run_mono hr hj
    have hex : ∃ al' : ℕ → ℝ, IsChainResponseCoeff (T.stepParameters y) Kr β j al' :=
      ⟨al, RunAboveTheFloor.isChainResponseCoeff_of_le hal hj⟩
    rw [runSlope, dif_pos hex]
    exact h.unique β j al hex.choose hrj (RunAboveTheFloor.isChainResponseCoeff_of_le hal hj) hex.choose_spec
      j le_rfl
  exact RunAboveTheFloor.isChainResponseCoeff_congr hal hagree

theorem runSlope_zero (h : RunTable T y Kr lam c₅) {β : ℝ} {k : ℕ} (hr : Run T y β k) :
    runSlope T y Kr β 0 = 1 :=
  (runSlope_isChain h hr).zero_eq

theorem abs_runSlope_sub_one_le (h : RunTable T y Kr lam c₅) {β : ℝ} {k : ℕ} (hr : Run T y β k) :
    |runSlope T y Kr β k - 1| ≤ 1 / 4 :=
  h.near β k _ hr (runSlope_isChain h hr)

theorem run_of_mem_domain (h : RunTable T y Kr lam c₅) {β : ℝ} {k : ℕ} (hβ : β ∈ runDomain T y k) :
    Run T y β k := by
  have hB : 0 ≤ T.B := le_trans zero_le_one h.adm.B_ge
  have hlow : ∀ j < k, y ≤ flowCouplings (T.stepParameters y) β j := fun j hj => by
    have := hβ.2 j hj
    linarith
  cases k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    show y ≤ β
    linarith [hβ.1]
  | succ m =>
    have hm : Run T y β m := fun i hi => hlow i (Nat.lt_succ_of_le hi)
    intro j hj
    rcases Nat.lt_or_ge j (m + 1) with hjk | hjk
    · exact hlow j hjk
    · have hjm : j = m + 1 := le_antisymm hj hjk
      subst hjm
      have hd := abs_flow_step_le h hm
      have hxm := hβ.2 m (Nat.lt_succ_self m)
      have := (abs_le.mp hd).1
      linarith

theorem above_of_mem_domain (h : RunTable T y Kr lam c₅) {β : ℝ} {k : ℕ} (hβ : β ∈ runDomain T y k) :
    Above T y β (k + 1) :=
  RunAboveTheFloor.above_succ_of_run (run_of_mem_domain h hβ)

end YangMills.ContinuumLimit

end
