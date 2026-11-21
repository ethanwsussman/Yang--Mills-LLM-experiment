import YangMills.Construction.ClusterExpansionOfAStep.DeepDensitiesAgainstTheCutProof
import YangMills.Construction.ClusterExpansionOfAStep.FieldOfASettingIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.GradientsOfTwoSettingsProof
import YangMills.Construction.ClusterExpansionOfAStep.PotentialOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.TwoSettingsOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsInTwoSettings
import YangMills.Construction.LawInAState.CellsOfAPair
import YangMills.Construction.SummableBoundsOfTheFlow.LawOfACutIsAProbability
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open StepSettings TorusFields TorusLumps BlockOffsets SettingShifts
namespace NearFunctionsTwoSettings
set_option linter.unusedSectionVars false
variable {R : StepSetup} {n : ℕ} [NeZero n] {Y : TorusSite n}
private theorem measurable_coordsByIndex (s : ChartSetting R n) (Y : TorusSite n) : Measurable (s.coordsByIndex Y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.DeepCutoff.measurable_coordsByIndex <;> assumption
private theorem inBalls_of_forall_lt (s : ChartSetting R n) {η : FreeCoords s.free} (h : ∀ b, ‖η b‖ < R.ballRadius) : s.InBalls η := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.inBalls_of_norm_lt <;> assumption
private theorem partPotential_one (s : ChartSetting R n) : s.partPotential 1 = s.potential := by
  funext η
  simp [ChartSetting.partPotential, ChartSetting.potential]
private theorem weightedMean_eq_ballExpectation {s : ChartSetting R n} {u : FreeCoords s.free → ℝ}
    {Ψ : ColdStepAtMirrorFrames.BondField s.free → ℝ}
    (e : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] u) (G : FreeCoords s.free → ℝ) :
    weightedMean (s.lawDensity u) G = ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn) Ψ G := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LocalMeans.weightedMean_eq_ballExpectation <;> assumption
private theorem abs_ballExpectation_sub_le (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement) {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ}
    {p : ℝ → ℝ} {Ψ : ColdStepAtMirrorFrames.BondField ι → ℝ} (hρ : 0 < ρ) (hp : ColdStepAtMirrorFrames.IsCutoff ρ p) (hΨ : Continuous Ψ)
    {f g f' g' : ColdStepAtMirrorFrames.BondField ι → ℝ} {ε B : ℝ} (hf' : Measurable f') (hg' : Measurable g')
    (hff : ∀ η, (∀ b, ‖η b‖ < ρ) → f η = f' η) (hgg : ∀ η, (∀ b, ‖η b‖ < ρ) → g η = g' η)
    (hfB : ∀ η, (∀ b, ‖η b‖ < ρ) → |f η| ≤ B) (hgB : ∀ η, (∀ b, ‖η b‖ < ρ) → |g η| ≤ B)
    (hε : ∀ η, (∀ b, ‖η b‖ < ρ) → |f η - g η| ≤ ε) :
    |ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ f - ColdStepAtMirrorFrames.ballExpectation (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ g| ≤ ε := by
  obtain ⟨hpr, hme, -, hob, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ
  rw [← hme f, ← hme g]
  have afe : f =ᵐ[ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ] f' := hob.mono fun η h => hff η h
  have age : g =ᵐ[ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ] g' := hob.mono fun η h => hgg η h
  have intf : Integrable f (ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) :=
    Integrable.of_bound (hf'.aestronglyMeasurable.congr afe.symm) B (hob.mono fun η h => by
      simpa [Real.norm_eq_abs] using hfB η h)
  have intg : Integrable g (ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) :=
    Integrable.of_bound (hg'.aestronglyMeasurable.congr age.symm) B (hob.mono fun η h => by
      simpa [Real.norm_eq_abs] using hgB η h)
  rw [← integral_sub intf intg]
  have h := norm_integral_le_of_norm_le_const (μ := ConvexObservables.normalizedBallLaw (ColdStepAtMirrorFrames.cutoffFactor ρ p) Ψ) (C := ε) (f := fun η => f η - g η)
    (hob.mono fun η h => by simpa [Real.norm_eq_abs] using hε η h)
  simpa [Real.norm_eq_abs] using h
private theorem le_clusterRange {A x : ℝ} (hA : 0 ≤ A) (hx : A ^ 100 ≤ x) : A ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.SettingGradients.le_clusterRange_of_pow_le <;> assumption
section Coordinates
open Classical in
private def coordsOfIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) (z : NearBondIndex → EuclideanSpace ℝ (Fin 3)) :
    FreeCoords s.free :=
  fun b => if h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1 then z h.choose else 0
private theorem measurable_coordsOfIndex (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) : Measurable (coordsOfIndex s Y k) := by
  classical
  refine measurable_pi_iff.mpr fun b => ?_
  unfold coordsOfIndex
  by_cases h : ∃ q, IsNearIndex R.params.side k q ∧ nearBond R.params.side Y q = b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const
private theorem coordsOfIndex_inBalls (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) (hρ : 0 ≤ R.ballRadius)
    {z : NearBondIndex → EuclideanSpace ℝ (Fin 3)} (hz : ClusterExpansionOfAStep.CoordsInBalls R z) : s.InBalls (coordsOfIndex s Y k z) := by
  intro b
  unfold coordsOfIndex
  split_ifs with h
  · exact hz _
  · rw [coordNorm_eq_norm]
    simpa using hρ
private theorem coordsOfIndex_congr (s : ChartSetting R n) (Y : TorusSite n) (k : ℕ) {z z' : NearBondIndex → EuclideanSpace ℝ (Fin 3)}
    (hz : ∀ q, IsNearIndex R.params.side k q → z q = z' q) : coordsOfIndex s Y k z = coordsOfIndex s Y k z' := by
  funext b
  unfold coordsOfIndex
  split_ifs with h
  · exact hz _ h.choose_spec.1
  · rfl
private theorem coordsByIndex_inBalls (s : ChartSetting R n) (Y : TorusSite n) (hρ : 0 ≤ R.ballRadius) {η : FreeCoords s.free}
    (hη : s.InBalls η) : ClusterExpansionOfAStep.CoordsInBalls R (s.coordsByIndex Y η) := by
  intro q
  unfold ChartSetting.coordsByIndex
  split_ifs with h
  · exact hη _
  · rw [coordNorm_eq_norm]
    simpa using hρ
private theorem coordsAgreeNear_coordsOfIndex (hodd : Odd R.params.side) {s s' : ChartSetting R n} {k : ℕ} (hk : 2 * k + 2 < n)
    (hfree : ∀ q, IsNearIndex R.params.side k q → (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y q ∈ s'.free))
    (η' : FreeCoords s'.free) :
    CoordsAgreeNear s s' Y Y k (coordsOfIndex s Y k (s'.coordsByIndex Y η')) η' := by
  intro q hq
  simp only [ChartSetting.coordsByIndex]
  by_cases hf : nearBond R.params.side Y q ∈ s.free
  · have hf' := (hfree q hq).mp hf
    rw [dif_pos hf, dif_pos hf']
    have hex : ∃ q₂, IsNearIndex R.params.side k q₂ ∧ nearBond R.params.side Y q₂ = (⟨_, hf⟩ : s.free).1 := ⟨q, hq, rfl⟩
    unfold coordsOfIndex
    rw [dif_pos hex]
    have e : hex.choose = q := eq_of_nearBond_eq hodd hk hex.choose_spec.1 hq hex.choose_spec.2
    rw [e]
    simp only [ChartSetting.coordsByIndex, dif_pos hf']
  · have hf' : nearBond R.params.side Y q ∉ s'.free := fun e => hf ((hfree q hq).mpr e)
    rw [dif_neg hf, dif_neg hf']
end Coordinates
section States
private theorem statesAgreeNear_of_settingsAgreeNear {z : TorusSite (n * R.params.side)} (hodd : Odd R.params.side) (hn : 2 ≤ n) {s s' : ChartSetting R n} (hs : s.IsAdmissible)
    {η : FreeCoords s.free} {η' : FreeCoords s'.free} {Mx k m₂ : ℕ} (hag : SettingsAgreeNear s s' Y Y Mx)
    (hk1 : 1 ≤ k) (hk : k ≤ Mx) (hnear : CoordsAgreeNear s s' Y Y k η η') {o : Fin 4 → ℤ} (ho : o ∈ BlockAverages.centredCube R.params.side)
    (hz : z = fineSite R.params.side Y 0 o) (hm : m₂ = R.params.side * k - R.params.side) :
    StatesAgreeNear R.params (s.field η) (s'.field η') s.support s'.support s.labelling s'.labelling z z m₂ := by
  have side : 2 * m₂ + 2 < n * R.params.side := by
    have hN := hag.lt_extent
    rw [hm]
    have h1 : (2 * k + 3) * R.params.side ≤ n * R.params.side := Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 * k + 3) * R.params.side = 2 * (R.params.side * k) + 3 * R.params.side := by ring
    have h3 := Nat.sub_le (R.params.side * k) R.params.side
    have h4 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    omega
  rw [hz]
  refine ⟨side, side, ?_, ?_, ?_, fun _ => sameBlockPosition_fineSite R.params Y Y 0 o⟩
  · rw [hm]
    exact fieldsAgreeNear_of_settings hodd hn hn hs.subset_chart hag hk1 hk hnear ho
  · intro h hh
    rw [hm] at hh
    obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hk1 ho hh
    rw [hx n Y]
    refine hag.support_iff kk o' (fun l => ?_) ho'
    have := hkk l
    have h3 : (k : ℤ) ≤ Mx := by exact_mod_cast hk
    linarith
  · intro h hh hz₁ hz₂ _
    rw [hm] at hh
    obtain ⟨kk, o', ho', hkk, hx⟩ := exists_fineSite_add hodd hk1 ho hh
    have e1 := hx n Y
    have h1 : fineSite R.params.side Y kk o' ∈ s.support := e1 ▸ hz₁
    have h2 : fineSite R.params.side Y kk o' ∈ s'.support := e1 ▸ hz₂
    have hb : OffsetInBox Mx kk := fun l => by
      have := hkk l
      have h3 : (k : ℤ) ≤ Mx := by exact_mod_cast hk
      linarith
    have := hag.labelling_eq kk o' h1 h2 hb ho'
    have c1 : s.labelling ⟨_, hz₁⟩ = s.labelling ⟨_, h1⟩ := by congr 2
    have c2 : s'.labelling ⟨_, hz₂⟩ = s'.labelling ⟨_, h2⟩ := by congr 2
    rw [c1, c2, this]
private theorem abs_settingMean_sub_le (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement) {Q Q' : ResponseInTheExpansion.StateFunction R (n * R.params.side)}
    {z : TorusSite (n * R.params.side)} {K ρ : ℝ} (hQ : IsNearlyLocalStateFunction R Q z K ρ) (hQ' : IsNearlyLocalStateFunction R Q' z K ρ) (hρ : 0 < R.ballRadius)
    (hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    {s s' : ChartSetting R n} (hs : s.IsAdmissible) {k Mx m₂ : ℕ} (hag : SettingsAgreeNear s s' Y Y Mx)
    (hk1 : 1 ≤ k) (hk : k ≤ Mx) {o : Fin 4 → ℤ} (ho : o ∈ BlockAverages.centredCube R.params.side) (hz : z = fineSite R.params.side Y 0 o)
    (hm : m₂ = R.params.side * k - R.params.side) (hfl : ρ + (clusterRange R.coupling : ℝ) / 64 ≤ m₂)
    (hlive : ∀ (s₁ : ChartSetting R n), s₁.IsAdmissible → ∀ η, s₁.InBalls η → WeightedResponses.IsLiveState R.params R.coupling R.labelWeight (s₁.field η) s₁.support s₁.labelling)
    (hs' : s'.IsAdmissible)
    (hpair : ∀ (W W' : TorusField (n * R.params.side)) (A A' : Finset (TorusSite (n * R.params.side))) (ω : A → R.labels.Ω) (ω' : A' → R.labels.Ω),
      WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W A ω → WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W' A' ω' →
      StatesAgreeNear R.params W W' A A' ω ω' z z m₂ → |Q W A ω - Q' W' A' ω'| ≤ K * Real.exp (-R.params.decayRate * (m₂ - ρ)))
    {Ψ : ColdStepAtMirrorFrames.BondField s.free → ℝ} {Ψ' : ColdStepAtMirrorFrames.BondField s'.free → ℝ} (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ')
    (he : ∀ η, s.InBalls η → Ψ =ᶠ[nhds η] s.potential) (he' : ∀ η, s'.InBalls η → Ψ' =ᶠ[nhds η] s'.potential) {Wd : ℝ}
    (hWide : ∀ (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ), Measurable F → DependsWithin R.params.side k F →
      (∀ z z', ClusterExpansionOfAStep.CoordsInBalls R z → ClusterExpansionOfAStep.CoordsInBalls R z' → |F z - F z'| ≤ o) →
      |weightedMean (s.lawDensity s.potential) (fun η => F (s.coordsByIndex Y η)) -
        weightedMean (s'.lawDensity s'.potential) (fun η => F (s'.coordsByIndex Y η))| ≤ o * Wd) :
    |StateLaws.settingMean s Q - StateLaws.settingMean s' Q'| ≤ K * Real.exp (-R.params.decayRate * (m₂ - ρ)) * 2 + 2 * K * Wd := by
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-R.params.decayRate * (m₂ - ρ)) := ⟨_, rfl⟩
  rw [← hE]
  rw [← hE] at hpair
  have side : 2 * k + 2 < n := by have := hag.lt_extent; omega
  have size : ∀ η : FreeCoords s.free, |Q (s.field η) s.support s.labelling| ≤ K := fun η => hQ.abs_le _ _ _
  have size' : ∀ η : FreeCoords s'.free, |Q' (s'.field η) s'.support s'.labelling| ≤ K := fun η => hQ'.abs_le _ _ _
  obtain ⟨G, hGd⟩ : ∃ G : FreeCoords s.free → ℝ, G = fun η => Q (s.field η) s.support s.labelling := ⟨_, rfl⟩
  obtain ⟨G', hGd'⟩ : ∃ G' : FreeCoords s'.free → ℝ, G' = fun η => Q' (s'.field η) s'.support s'.labelling := ⟨_, rfl⟩
  have hG : Measurable G := by
    rw [hGd]
    exact (hQ.measurable s.support).comp ((ClusterExpansionOfAStep.ChartSetting.measurable_field s).prodMk (measurable_const (a := s.labelling)))
  have hG' : Measurable G' := by
    rw [hGd']
    exact (hQ'.measurable s'.support).comp ((ClusterExpansionOfAStep.ChartSetting.measurable_field s').prodMk (measurable_const (a := s'.labelling)))
  obtain ⟨F, hFd⟩ : ∃ F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ, F = fun z => G (coordsOfIndex s Y k z) := ⟨_, rfl⟩
  have hF : Measurable F := by rw [hFd]; exact hG.comp (measurable_coordsOfIndex s Y k)
  have hFr : DependsWithin R.params.side k F := fun z z' h => by
    rw [hFd]
    show G _ = G _
    rw [coordsOfIndex_congr s Y k h]
  have Fsize : ∀ z, |F z| ≤ K := fun z => by
    rw [hFd, hGd]
    exact size _
  have hFo : ∀ z z', ClusterExpansionOfAStep.CoordsInBalls R z → ClusterExpansionOfAStep.CoordsInBalls R z' → |F z - F z'| ≤ 2 * K := fun z z' _ _ => by
    have a := Fsize z
    have b := Fsize z'
    have := abs_sub (F z) (F z')
    linarith
  have wide := hWide F (2 * K) hF hFr hFo
  have near1 : ∀ {η : FreeCoords s.free}, s.InBalls η → |F (s.coordsByIndex Y η) - Q (s.field η) s.support s.labelling| ≤ K * E := fun {η} hb => by
    have hag₁ : SettingsAgreeNear s s Y Y Mx := settingsAgreeNear_refl s hs Y Mx hag.lt_extent
    have hnear := coordsAgreeNear_coordsOfIndex (Y := Y) hodd side (fun _ _ => Iff.rfl) η
    have := hQ.abs_sub_le _ _ _ _ _ _ m₂ (hlive s hs _ (coordsOfIndex_inBalls s Y k hρ.le (coordsByIndex_inBalls s Y hρ.le hb))) (hlive s hs η hb)
      hfl (statesAgreeNear_of_settingsAgreeNear hodd hn hs hag₁ hk1 hk hnear ho hz hm)
    rw [← hE] at this
    rw [hFd, hGd]
    exact this
  have near2 : ∀ {η : FreeCoords s'.free}, s'.InBalls η → |F (s'.coordsByIndex Y η) - Q' (s'.field η) s'.support s'.labelling| ≤ K * E := fun {η} hb => by
    have hnear := coordsAgreeNear_coordsOfIndex (Y := Y) hodd side
      (fun q hq => hag.free_iff q ⟨fun l => (hq.1 l).trans (by exact_mod_cast hk), hq.2⟩) η
    have := hpair _ _ _ _ _ _ (hlive s hs _ (coordsOfIndex_inBalls s Y k hρ.le (coordsByIndex_inBalls s' Y hρ.le hb))) (hlive s' hs' η hb)
      (statesAgreeNear_of_settingsAgreeNear hodd hn hs hag hk1 hk hnear ho hz hm)
    rw [hFd, hGd]
    exact this
  have m1 : |StateLaws.settingMean s Q - weightedMean (s.lawDensity s.potential) (fun η => F (s.coordsByIndex Y η))| ≤ K * E := by
    have e0 : StateLaws.settingMean s Q = weightedMean (s.lawDensity s.potential) (fun η => Q (s.field η) s.support s.labelling) := rfl
    rw [e0, weightedMean_eq_ballExpectation he, weightedMean_eq_ballExpectation he, abs_sub_comm]
    refine abs_ballExpectation_sub_le hLaw hρ hcut hΨ (B := K) (hF.comp (measurable_coordsByIndex s Y)) hG (fun _ _ => rfl)
      (fun η h => by rw [hGd]) (fun η h => Fsize _) (fun η h => size η) (fun η h => near1 (inBalls_of_forall_lt s h))
  have m2 : |weightedMean (s'.lawDensity s'.potential) (fun η => F (s'.coordsByIndex Y η)) - StateLaws.settingMean s' Q'| ≤ K * E := by
    have e0 : StateLaws.settingMean s' Q' = weightedMean (s'.lawDensity s'.potential) (fun η => Q' (s'.field η) s'.support s'.labelling) := rfl
    rw [e0, weightedMean_eq_ballExpectation he', weightedMean_eq_ballExpectation he']
    refine abs_ballExpectation_sub_le hLaw hρ hcut hΨ' (B := K) (hF.comp (measurable_coordsByIndex s' Y)) hG' (fun _ _ => rfl)
      (fun η h => by rw [hGd']) (fun η h => Fsize _) (fun η h => size' η) (fun η h => near2 (inBalls_of_forall_lt s' h))
  have t1 := abs_sub_le (StateLaws.settingMean s Q) (weightedMean (s.lawDensity s.potential) (fun η => F (s.coordsByIndex Y η)))
    (StateLaws.settingMean s' Q')
  have t2 := abs_sub_le (weightedMean (s.lawDensity s.potential) (fun η => F (s.coordsByIndex Y η)))
    (weightedMean (s'.lawDensity s'.potential) (fun η => F (s'.coordsByIndex Y η))) (StateLaws.settingMean s' Q')
  linarith
end States
set_option maxHeartbeats 2000000 in
theorem main_bound (hbox : ClusterExpansionOfAStep.LocalMeansClose) (hconv : ClusterExpansionOfAStep.SettingsUniformlyConvex)
    (htie : ClusterExpansionOfAStep.ChartPotentialConvex) (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement) (hPot : PotentialFactorization) :
    nearFunctionsTwoSettingsStatement := by
  obtain ⟨r₁, p₁, W⟩ := hbox
  obtain ⟨r₂, p₂, H1⟩ := hconv
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (p₁ c) (p₂ c), fun T hT hrt _ => ?_⟩
  obtain ⟨yw, W⟩ := W T hT (hrt.trans (min_le_left _ _))
  obtain ⟨Cv, y₁, hCv, H1⟩ := H1 T hT (hrt.trans (min_le_right _ _))
  have hrt0 := hT.rt_pos
  have hσ := hT.σ_pos
  have hlam : 0 < T.lam := hT.chain.2.2.1
  have hLbig : (2 : ℝ) ^ 40 ≤ T.side := by exact_mod_cast hT.L_ge
  have hLpos : (0 : ℝ) < T.side := by linarith [show (0 : ℝ) < 2 ^ 40 by norm_num]
  refine ⟨max T.floorMin (max yw (max y₁ (max 1 ((2 ^ 20 * (T.side : ℝ)) ^ 100)))), fun y hy' R A hK hAT => ?_⟩
  have hy0 : T.floorMin ≤ y := (le_max_left _ _).trans hy'
  have hy : max yw (max y₁ (max 1 ((2 ^ 20 * (T.side : ℝ)) ^ 100))) ≤ y := (le_max_right _ _).trans hy'
  intro n _ Q Q' z K ρ hn hρ0 hQ hQ' s s' m hs hs' hm hag hpr
  have hOT := hAT.onFamily
  obtain ⟨hR, hρA, hp, hyx, hstep⟩ := id hOT
  have hyw : yw ≤ y := (le_max_left _ _).trans hy
  have hy1 : y₁ ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hx1 : 1 ≤ R.coupling := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).trans hyx
  have hx0 : 0 < R.coupling := by linarith
  have hxr : (2 ^ 20 * (T.side : ℝ)) ^ 100 ≤ R.coupling :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))).trans hyx
  have hrbig : 2 ^ 20 * (T.side : ℝ) ≤ R.range := le_clusterRange (by positivity) hxr
  have hL : R.params.side = T.side := by rw [hR]; rfl
  have hLc : (R.params.side : ℝ) = T.side := by rw [hL]
  have hRrt : R.params.rt = T.rt := by rw [hR]; rfl
  have hRσ : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hRn₀ : R.params.n₀ = T.n₀ := by rw [hR]; rfl
  have hodd : Odd R.params.side := by rw [hL]; exact hT.L_odd
  have hL1 : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hρR : 0 < R.ballRadius := by
    show 0 < R.params.threshold / 64
    rw [hRσ]
    positivity
  have hcut : ColdStepAtMirrorFrames.IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = T.threshold / 64
      rw [hRσ]
    rw [e, hp]
    exact hT.cut
  have hσR : 0 < R.params.threshold := by rw [hRσ]; exact hσ
  have hrtR : 0 < R.params.rt := by rw [hRrt]; exact hrt0
  have hnT : T.n₀ ≤ n := by rw [← hRn₀]; exact hn
  have hn₀ : 4096 ≤ T.n₀ := hT.n₀_ge
  have hr0 : (0 : ℝ) ≤ R.range := Nat.cast_nonneg _
  have hmr : (R.range : ℝ) / (4 * T.side) ≤ m := by
    have h1 : 0 ≤ (R.range : ℝ) / (4 * R.params.side) := by positivity
    rw [← hLc]
    linarith
  have hρm : ρ ≤ 4 * m := by
    have h1 : 0 ≤ (R.range : ℝ) / (4 * R.params.side) := by positivity
    linarith
  have hmbig : (2 : ℝ) ^ 18 ≤ m := by
    have h1 : (R.range : ℝ) ≤ m * (4 * T.side) := (div_le_iff₀ (by positivity)).mp hmr
    have h2 : (2 : ℝ) ^ 18 * (4 * T.side) ≤ m * (4 * T.side) := by
      have : (2 : ℝ) ^ 18 * (4 * T.side) = 2 ^ 20 * T.side := by ring
      linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hmN : 2 ^ 18 ≤ m := by exact_mod_cast hmbig
  obtain ⟨t, htd⟩ : ∃ t, t = m / 4 := ⟨_, rfl⟩
  have hLt : R.params.side ≤ R.params.side * t := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, m₂ = R.params.side * t - R.params.side := ⟨_, rfl⟩
  have hm₃ : R.params.side * t ≤ m₂ + R.params.side := by omega
  have hm₃r : (T.side : ℝ) * t ≤ m₂ + T.side := by
    rw [← hLc]
    exact_mod_cast hm₃
  have ht4 : (m : ℝ) ≤ 4 * t + 3 := by
    have : m ≤ 4 * t + 3 := by omega
    exact_mod_cast this
  have hm₄ : (T.side : ℝ) * (m / 8) ≤ m₂ := by
    have : (m : ℝ) / 8 ≤ t - 1 := by linarith
    have := mul_le_mul_of_nonneg_left this hLpos.le
    linarith
  have hm₅ : (2 : ℝ) ^ 37 * m ≤ m₂ := by
    have : (2 : ℝ) ^ 40 * (m / 8) ≤ T.side * (m / 8) := by gcongr
    linarith
  have hfl : ρ + (clusterRange R.coupling : ℝ) / 64 ≤ m₂ := by
    have h1 : (R.range : ℝ) ≤ m * (4 * T.side) := (div_le_iff₀ (by positivity)).mp hmr
    have h2 : (clusterRange R.coupling : ℝ) = R.range := rfl
    have h3 : (2 : ℝ) ^ 6 * m ≤ T.side * (m / 16) := by
      have : (2 : ℝ) ^ 40 * (m / 16) ≤ T.side * (m / 16) := by gcongr
      linarith
    rw [h2]
    nlinarith
  have hE : Real.exp (-R.params.decayRate * (m₂ - ρ)) ≤ Real.exp (-(R.params.rt * m / 2 ^ 4)) := by
    apply Real.exp_le_exp.mpr
    have hf : R.params.decayRate = T.rt / 2 ^ 12 := by
      show R.params.rt / 2 ^ 12 = _
      rw [hRrt]
    rw [hf, hRrt]
    have h1 : (m : ℝ) ≤ (m₂ : ℝ) - ρ := by linarith
    have h2 : T.rt / 2 ^ 12 * (m : ℝ) ≤ T.rt / 2 ^ 12 * ((m₂ : ℝ) - ρ) := by gcongr
    have h3 : (2 : ℝ) ^ 36 * m ≤ (m₂ : ℝ) - ρ := by linarith
    have h4 : T.rt / 2 ^ 12 * ((2 : ℝ) ^ 36 * m) ≤ T.rt / 2 ^ 12 * ((m₂ : ℝ) - ρ) := by gcongr
    have h5 : 0 ≤ T.rt * m := by positivity
    nlinarith
  have hWd : Real.exp (-(T.rt * m / 2 ^ 3)) ≤ Real.exp (-(R.params.rt * m / 2 ^ 4)) := by
    apply Real.exp_le_exp.mpr
    rw [hRrt]
    have h5 : 0 ≤ T.rt * m := by positivity
    linarith
  have hk1 : 1 ≤ t := by omega
  have hk : t ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Ψ, K₁, e₁, c₁, -, -⟩ := htie R T.lam Cv hσR hrtR hx0 hlam n s _ (H1 y hy1 R hOT n hnT s hs).1
  obtain ⟨Ψ', K₂, e₂, c₂, -, -⟩ := htie R T.lam Cv hσR hrtR hx0 hlam n s' _ (H1 y hy1 R hOT n hnT s' hs').1
  have wide := fun (F : (NearBondIndex → EuclideanSpace ℝ (Fin 3)) → ℝ) (o : ℝ) (hF : Measurable F)
      (hFr : DependsWithin R.params.side t F)
      (hFo : ∀ z z', ClusterExpansionOfAStep.CoordsInBalls R z → ClusterExpansionOfAStep.CoordsInBalls R z' → |F z - F z'| ≤ o) => by
    have h := W y hyw R hOT n n hnT hnT s s' _ _ m hs hs' hag hmr _ _
      (ClusterExpansionOfAStep.AlikePotentials.part_potential 1 zero_le_one le_rfl) F o hF (by rw [← hL, ← htd]; exact hFr) hFo
    rw [partPotential_one, partPotential_one] at h
    exact h
  obtain ⟨o, ho, hz⟩ := exists_fineSite_of_parentBlock hodd (parentBlock R.params.side z) z rfl
  have hm₂Lm : m₂ ≤ R.params.side * m - R.params.side := by
    rw [hm₂]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hk) _
  have hlive : ∀ (s₁ : ChartSetting R n), s₁.IsAdmissible → ∀ η, s₁.InBalls η → WeightedResponses.IsLiveState R.params R.coupling R.labelWeight (s₁.field η) s₁.support s₁.labelling := by
    intro s₁ hs₁ η hη
    have hrow : R.HasExpansions := hOT.isStep.1
    have hfits : R.params.Admissible := by rw [hR]; exact hT.fits y hy0
    have hρA' : 0 < R.anchorRadius := by rw [hOT.anchorRadius_eq]; exact hT.chain.2.2.2.1
    have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
      have h1 : R.ballRadius = R.params.threshold / 64 := rfl
      have h2 : R.params.threshold ≤ 1 := by rw [hRσ]; exact hT.σ_one
      have h3 := Real.pi_gt_three
      have h4 : R.anchorRadius ≤ 1 := by rw [hOT.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
      linarith
    have hLpos' : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    have hblock : IsBlockTorusSide R.params (n * R.params.side) :=
      ⟨Dvd.intro_left n rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
    refine ⟨hs₁.isHull η hη, ?_⟩
    obtain ⟨hD, hk', hj, heq, -⟩ := hPot R hfits hrow hρA' hρπ n hn s₁ hs₁ η hη
    have hΦ : 0 < ∏ X ∈ chainComponents R.range s₁.support, R.clusterFactor (n * R.params.side) (s₁.field η) s₁.support s₁.labelling X :=
      Finset.prod_pos fun X hX => lt_of_le_of_ne (hrow.2.factor_nonneg _ hblock _ _ _ X) (hs₁.factor_ne_zero η hη X hX).symm
    have hpos := mul_pos (mul_pos hD hΦ) (Real.exp_pos (-s₁.potential η))
    rw [← heq] at hpos
    exact (mul_pos_iff_of_pos_right hk').mp ((mul_pos_iff_of_pos_right hj).mp hpos)
  have cr := abs_settingMean_sub_le hLaw hQ hQ' hρR hcut hodd hn2 hs hag hk1 hk ho hz hm₂ hfl hlive hs'
    (fun W W' A A' ω ω' hl hl' ha => hpr W W' A A' ω ω' m₂ hl hl' hfl hm₂Lm ha)
    c₁.smooth.continuous c₂.smooth.continuous e₁ e₂ wide
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hQ.abs_le (trivialField _) ∅ (StateLaws.emptyLabelling R.labels.Ω))
  refine cr.trans ?_
  have a1 := mul_le_mul_of_nonneg_left hE hK0
  have a2 := mul_le_mul_of_nonneg_left hWd hK0
  linarith
end NearFunctionsTwoSettings
theorem nearFunctionsTwoSettingsStatement_holds (hbox : ClusterExpansionOfAStep.LocalMeansClose) (hconv : ClusterExpansionOfAStep.SettingsUniformlyConvex)
    (htie : ClusterExpansionOfAStep.ChartPotentialConvex) (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement) (hPot : PotentialFactorization) :
    nearFunctionsTwoSettingsStatement := by apply _root_.YangMills.Construction.MomentLaw.NearFunctionsTwoSettings.main_bound <;> assumption
end YangMills.Construction.MomentLaw
end
