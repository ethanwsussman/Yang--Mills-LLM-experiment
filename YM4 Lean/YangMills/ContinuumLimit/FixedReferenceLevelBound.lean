import YangMills.ContinuumLimit.StoppedCovarianceEstimate
import YangMills.ContinuumLimit.ReferencePairRescaling
import YangMills.ContinuumLimit.ScoredTowerSelection
import YangMills.ContinuumLimit.StoppingScalesAtReferenceLevel
import YangMills.ContinuumLimit.ReferenceRoots
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory ProbabilityTheory
namespace YangMills.BranchHot
open Construction RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
open TheStatementsProvedTogether FreeEnergies TorusLumps PeriodicLattice ContinuumLimit

def NoEscapingLevel (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) (L M : ℕ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ (k : ℕ → ℕ) (b : ℕ → ℝ), StrictMono k →
    (∀ j, 0 < b j) → (∀ j, b j ∈ runDomain T y (k j)) →
    (∀ j, IsTunedAt T y (TotalDensityFlow.coupling (T.stepParameters y) (b j) (k j)) (k j) (b j)) →
    (∀ j, referenceResponse L M (k j) (b j) = r) →
    Tendsto (fun j => TotalDensityFlow.coupling (T.stepParameters y) (b j) (k j)) atTop atTop → False

/-- Decay of the actual reference covariance at a stopped level excludes a positive
calibration level along any sequence whose terminal inverse coupling diverges. -/
theorem noEscapingLevel_of_stageDecay {Tb : ParameterAssignment} {Kr KrRun : ResponseParameters} {y lam cr : ℝ}
    (H : RunTable Tb y KrRun lam cr) (hTw : HasScoredTowers Tb Kr y)
    (hdecay : StageDecayAt Tb Kr y) (M : ℕ+) : NoEscapingLevel Tb y Tb.side M := by
  let p := Tb.stepParameters y
  have hfit := H.adm.fits y H.floor
  have hL13 : 13 ≤ Tb.side := by have := H.adm.L_ge; omega
  have hL : Conventions.IsAdmissibleBlockingFactor Tb.side := ⟨H.adm.L_odd,hL13⟩
  have hLs : (24:ℝ) ≤ Tb.side := by exact_mod_cast (show 24 ≤ Tb.side by have := H.adm.L_ge; omega)
  let : NeZero Tb.side := ⟨by omega⟩
  let ell := torusSide Tb.side M
  have hM : 1 ≤ (M:ℕ) := M.property
  have hell : 48 ≤ ell := by
    have he : (Tb.side:ℝ)^1 ≤ (Tb.side:ℝ)^(M:ℕ) :=
      pow_le_pow_right₀ (by linarith) hM
    dsimp [ell,torusSide]
    rw [pow_one] at he
    linarith
  obtain ⟨vt,hvt,hshape⟩ := StoppedReference.stoppedTests_shaped p hfit hL M hell
  intro r hr K b hmono hb hdom ht hlevel hhot
  let P (j : ℕ) := TotalDensityFlow.coupling p (b j) (K j)
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < K j :=
    (eventually_ge_atTop (1:ℕ)).mono fun j hj => (Nat.zero_le (K 0)).trans_lt (hmono hj)
  obtain ⟨k,A,hA,hk,hq,hwindow⟩ := ReferenceCalibration.stopping_scales_on_tuned_flow_nat H M
    K b P hr hpos (Eventually.of_forall fun j => (hlevel j).ge)
    (Eventually.of_forall ht) hhot
  let u (j : ℕ) := K j-k j
  let q (j : ℕ) := Tb.side^(u j)
  have hev := hq.eventually (hdecay ell A vt (by linarith) hA hvt.1 (r/2) (by linarith))
  obtain ⟨j,hest,hwin⟩ := (hev.and hwindow).exists
  obtain ⟨_,hfloor,hlo,hhi⟩ := hwin
  obtain ⟨T,S,hKr,hFlow⟩ := hTw (b j) (k j) hfloor
  let m := (M:ℕ) + u j
  let f := StoppedReference.stoppedTests Tb.side M (u j)
  have hside : ((2*Tb.side^m:ℕ):ℝ) = ell * (q j:ℝ) := by
    simp [m,q,ell,torusSide,pow_add,mul_assoc]
  have hdiv : 2*Tb.side ∣ 2*Tb.side^m := by
    have hm : 1 ≤ m := hM.trans (Nat.le_add_right _ _)
    exact Nat.mul_dvd_mul_left _ (dvd_pow_self _ (by omega : m ≠ 0))
  have hsep : IsSeparatedTestTuple p m ((6/5:ℝ)*(q j:ℝ)) vt f := by
    rw [show (q j:ℝ) = (p.side:ℝ)^(u j) by change ((Tb.side^(u j):ℕ):ℝ) = (Tb.side:ℝ)^(u j); exact Nat.cast_pow ..]
    exact hshape (u j)
  have hbound := hest T S (b j) (k j) m hKr hFlow hfloor hside hdiv hlo hhi f hsep
  have hcov := StoppedReference.reference_eq_covariance (L:=Tb.side) (M:=(M:ℕ)) (k:=k j) (r:=u j)
    (by omega) hM (b j)
  change |cov[curvatureObservable (fineWeight (StoppedReference.fineSource Tb.side (k j) m (f 0))
      (fineSide Tb.side (k j) (2*Tb.side^m))),
    curvatureObservable (fineWeight (StoppedReference.fineSource Tb.side (k j) m (f 1))
      (fineSide Tb.side (k j) (2*Tb.side^m))); wilsonLaw (b j) (fineSide Tb.side (k j) (2*Tb.side^m))]| ≤ r/2 at hbound
  rw [←hcov] at hbound
  have he : k j + u j = K j := by
    change k j + (K j-k j) = K j
    exact Nat.add_sub_of_le (hk j)
  rw [he,hlevel j,abs_of_pos hr] at hbound
  linarith

/-- The flow table and the scored towers may have independent response coefficients.
Only the gauge action, blocking factor, and running inverse coupling enter the reference law. -/
def NoEscapingAtTables (Tb : ParameterAssignment) (y : ℝ) : Prop :=
  ∀ (Kr : ResponseParameters) (lam cr : ℝ), RunTable Tb y Kr lam cr →
    ∀ M : ℕ+, NoEscapingLevel Tb y Tb.side M

theorem noEscapingTables_of_stageDecay (h : AtResponseParameters StageDecayAt) :
    TotalDensities.HoldsAtAdmissibleParameters NoEscapingAtTables := by
  refine (onScoredTowers h).mono ?_
  rintro Tb y _ ⟨Kr, _, T, hStage⟩ KrRun lam cr H M
  exact noEscapingLevel_of_stageDecay H T hStage M

end YangMills.BranchHot
end
