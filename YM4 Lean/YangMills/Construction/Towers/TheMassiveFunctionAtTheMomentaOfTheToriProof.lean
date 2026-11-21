import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.TheMassiveFunctionAtTheMomentaOfTheTori
import YangMills.Construction.Towers.TheMassiveSymbolsAreHolomorphicInTheNumberAndTheMomentumProof
import YangMills.Construction.Towers.TheSecondDifferentialsOfTheMassiveFunctionsAtTheBackgrounds
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.TorusMomenta
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.PeriodicOperators.Tempered (EventuallyForSides complexHessian hessianSymbol
  IsHessianSymbol)
open YangMills.Construction.Tower.MassiveOpFunctions.Scaling (shiftedMomentum)
open YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians (backgroundModeOnQuotient)
open YangMills.Construction.Tower.FullSpace.BackgroundJets (massWidth momentumPolydisc stripHalfWidth
  scaledResponseField addScalarJet vertexOperatorJet edgeOperatorJet massiveLogFn)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
section Numbers
variable {I : PeriodicData}
theorem toComplexVec_mem_realDualPoints (κ : AmbientSpace) : toComplexVec κ ∈ realDualPoints := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.toComplexVec_mem_realDualPoints <;> assumption
theorem add_mem_realDualPoints {a b : Fin 4 → ℂ} (ha : a ∈ realDualPoints)
    (hb : b ∈ realDualPoints) : a + b ∈ realDualPoints :=
  fun j => by simp [ha j, hb j]
theorem sub_mem_realDualPoints {a b : Fin 4 → ℂ} (ha : a ∈ realDualPoints)
    (hb : b ∈ realDualPoints) : a - b ∈ realDualPoints :=
  fun j => by simp [ha j, hb j]
theorem logNumber_congr {T S : JetQuad I I} {p : Fin 4 → ℂ} (hp : p ∈ realDualPoints)
    (h00 : ∀ κ ∈ realDualPoints, T.f00 κ = S.f00 κ) (h10 : ∀ κ ∈ realDualPoints, T.f10 κ = S.f10 κ)
    (h01 : ∀ κ ∈ realDualPoints, T.f01 κ = S.f01 κ) (h11 : ∀ κ ∈ realDualPoints, T.f11 κ = S.f11 κ) :
    JetQuad.logNumber p T = JetQuad.logNumber p S := by apply _root_.YangMills.Construction.Tower.MassiveLogDet.Holomorphy.logNumber_congr_of_real <;> assumption
theorem logNumber_eq_of_eqAsJet {δ : ℝ} (hδ : 0 ≤ δ) {T S : JetQuad I I} {p : Fin 4 → ℂ}
    (hp : p ∈ realDualPoints) (h : JetQuad.EqAsJet δ p T S) :
    JetQuad.logNumber p T = JetQuad.logNumber p S := by
  have hs : ∀ κ ∈ realDualPoints, κ ∈ imStrip (2 * δ) := by
    intro κ hκ μ
    have h0 : (κ μ).im = 0 := hκ μ
    rw [h0, abs_zero]
    positivity
  obtain ⟨h00, h10, h01, h11⟩ := h
  refine logNumber_congr hp (fun κ hκ => h00 (hs κ hκ)) (fun κ hκ => h10 ?_)
    (fun κ hκ => h01 ?_) (fun κ hκ => h11 hκ)
  · exact ⟨hs κ hκ, hs _ (add_mem_realDualPoints hκ hp)⟩
  · exact ⟨hs κ hκ, hs _ (sub_mem_realDualPoints hκ hp)⟩
end Numbers
section Large
variable {L : ℕ}
theorem exists_forall_ge_of_eventuallyForSides (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) :
    ∃ n₀, 1 ≤ n₀ ∧ ∀ n, n₀ ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem tendsto_const_mul_exp_neg_side (hL : 2 ≤ L) {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ))) atTop (𝓝 0) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.tendsto_mul_exp_neg <;> assumption
end Large
theorem tendsto_scaled_logNumber {F I : PeriodicData} {L : ℕ} (hL : 2 ≤ L)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {C c : ℝ} (hc : 0 < c) {n₀ : ℕ}
    {p : AmbientSpace}
    (εPlus εMinus : F.UnitQuot → ℂ)
    (D : ∀ n : ℕ, (F.QuotMod (2 * L ^ n) → ℂ) → (F.QuotMod (2 * L ^ n) → ℂ) → ℂ)
    (hp : ∀ n, n₀ ≤ n → p ∈ dualLattice (2 * L ^ n))
    (hD : ∀ n, n₀ ≤ n → IsCloseToLogNumber F I T (2 * L ^ n) (D n) C c) :
    Tendsto (fun n : ℕ => (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ *
        D n (descendField F (2 * L ^ n) (blochWave F (toComplexVec p) εPlus))
          (descendField F (2 * L ^ n) (blochWave F (-toComplexVec p) εMinus))) atTop
      (𝓝 (JetQuad.logNumber (toComplexVec p)
        (jetAlong F I I T (toComplexVec p) εPlus εMinus))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := ((tendsto_const_mul_exp_neg_side hL hc C).mul_const
    (wNorm (F.quotWeight 1) εPlus)).mul_const (wNorm (F.quotWeight 1) εMinus)
  simp only [zero_mul] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop n₀] with n hn
  exact hD n hn p (hp n hn) εPlus εMinus
theorem finestMesh_smul_shiftedMomentum_mem {L : ℕ} (hL : 0 < L) (k n : ℕ) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (m : Fin 4 → ℤ) :
    finestMesh L k • shiftedMomentum p m ∈ dualLattice (2 * L ^ (n + k)) := by
  obtain ⟨j, hj⟩ := hp
  have hη : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  refine ⟨fun μ => j μ + 2 * (L : ℤ) ^ n * m μ, fun μ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, shiftedMomentum, hj μ, hη]
  push_cast
  rw [pow_add]
  field_simp
theorem side_inv_pow_mul_finestMesh_sq {L : ℕ} (hL : 0 < L) (k n : ℕ) :
    (((2 * L ^ n : ℕ) : ℂ) ^ 4)⁻¹ * ((finestMesh L k : ℝ) : ℂ) ^ 2 =
      (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
        (((PeriodicLattice.torusSide L (n + k))⁻¹ ^ 4 : ℝ) : ℂ) := by
  have hη : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [PeriodicLattice.torusSide, hη]
  push_cast
  rw [pow_add]
  field_simp
theorem massiveLogFnAtTorusMomenta_holds
    (hsec : BackgroundHessians.HessianRelation)
    (hloc : Locality.OpFunsLocal)
    (hlog : LogDetSecondDerivs.Claim)
    (hidx : TowerIndexSets.Claim)
    (hT : YangMills.Construction.Tower.MassiveOpFunctions.Tempered.MassiveFamilyTempered)
    (hP : YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined.Claim)
    (hM : DualLatticeDensity.Claim)
    (hQ : Quotients.QuotientTransposeNorm) : MassiveLogFnAtTorusMomenta := by
  intro L hS k hk z hz n hn p hp hW μPlus μMinus
  have hL2 : 2 ≤ L := le_trans (by norm_num) hS.2
  have hL0 : 0 < L := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hη : 0 < finestMesh L k := by
    unfold finestMesh meshAt
    exact zpow_pos hLR _
  have hz' : 0 < finestMesh L k ^ 2 * z := by positivity
  have hδ0 : 0 ≤ massWidth z := (norm_nonneg _).trans (hW 0)
  have hstrip : toComplexVec p ∈ momentumPolydisc stripHalfWidth :=
    fun μ => (hW μ).trans (min_le_left _ _)
  obtain ⟨loc₁, loc₂, sym₁, sym₂, jets⟩ := (hloc L hS z hz).2 k hk
  obtain ⟨ps, pb, -⟩ := hidx L hS k 0 (Nat.zero_le k)
  obtain ⟨-, -, -, ⟨s₁, C₁, c₁, -, hc₁, cl₁⟩, -, -⟩ := hlog _ _ pb ps _ loc₁ sym₁
  obtain ⟨-, -, -, ⟨s₂, C₂, c₂, -, hc₂, cl₂⟩, -, -⟩ := hlog _ _ pb pb _ loc₂ sym₂
  obtain ⟨n₃, -, hrel⟩ := exists_forall_ge_of_eventuallyForSides hL2 (hsec L hS k hk z hz)
  have hfin : ∀ j : ℕ, Finite ((colourEdges L k 0).QuotMod (2 * L ^ j)) := fun j =>
    (hQ _ _ pb pb (2 * L ^ j) (Nat.mul_pos (by norm_num) (pow_pos hL0 _))).1.2.1
  let N : ℕ → ℕ := fun j => Nat.card ((colourEdges L k 0).QuotMod (2 * L ^ j))
  let e : ∀ j : ℕ, Fin (N j) ≃ (colourEdges L k 0).QuotMod (2 * L ^ j) := fun j =>
    haveI := hfin j
    (Finite.equivFin _).symm
  have hmom : ∀ j, n ≤ j → p ∈ dualLattice (2 * L ^ j) := fun j hj =>
    (hM L hS).1 n j hn hj hp
  have hsides : ∀ {s₀ j : ℕ}, s₀ ≤ j → s₀ ≤ 2 * L ^ j := by
    intro s₀ j hj
    have := Nat.lt_pow_self (n := j) (by omega : 1 < L)
    omega
  obtain ⟨K, hK⟩ : ∃ K, K = max (max s₁ s₂) (max n n₃) := ⟨_, rfl⟩
  have g₁ : s₁ ≤ K := by omega
  have g₂ : s₂ ≤ K := by omega
  have g₃ : n ≤ K := by omega
  have g₄ : n₃ ≤ K := by omega
  have t₁ := tendsto_scaled_logNumber (F := colourEdges L k 0) (I := colourVertices L k 0)
    (n₀ := K) hL2 (T := scaledVertexOpFun L k z) hc₁ (p := p)
    (scaledResponseField L k (toComplexVec p) μPlus)
    (scaledResponseField L k (-toComplexVec p) μMinus)
    (fun j => logDetSecondDeriv (colourEdges L k 0) (colourVertices L k 0)
      (scaledVertexOpFun L k z) (e j)) (fun j hj => hmom j (g₃.trans hj))
    (fun j hj => ((cl₁ _ (hsides (g₁.trans hj))).2 _ (e j)).2.2)
  have t₂ := tendsto_scaled_logNumber (F := colourEdges L k 0) (I := colourEdges L k 0)
    (n₀ := K) hL2 (T := scaledEdgeOpFun L k z) hc₂ (p := p)
    (scaledResponseField L k (toComplexVec p) μPlus)
    (scaledResponseField L k (-toComplexVec p) μMinus)
    (fun j => logDetSecondDeriv (colourEdges L k 0) (colourEdges L k 0)
      (scaledEdgeOpFun L k z) (e j)) (fun j hj => hmom j (g₃.trans hj))
    (fun j hj => ((cl₂ _ (hsides (g₂.trans hj))).2 _ (e j)).2.2)
  have l₁ := logNumber_eq_of_eqAsJet hδ0 (toComplexVec_mem_realDualPoints p)
    (jets p hW μPlus μMinus).1
  have l₂ := logNumber_eq_of_eqAsJet hδ0 (toComplexVec_mem_realDualPoints p)
    (jets p hW μPlus μMinus).2
  simp only [YangMills.Construction.Tower.FullSpace.BackgroundJets.jetAlongResponse] at l₁ l₂
  rw [l₁] at t₁
  rw [l₂] at t₂
  let G : ℕ → ℂ := fun j => (((2 * L ^ j : ℕ) : ℂ) ^ 4)⁻¹ *
    ((((finestMesh L k : ℝ) : ℂ)) ^ 2 *
      ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        backgroundCoeff L k (toComplexVec p) μPlus ρ m *
          backgroundCoeff L k (-toComplexVec p) μMinus σ (-m) *
          complexHessian (massiveFieldFamily L (finestMesh L k ^ 2 * z)) (j + k)
            (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
              (finestMesh L k • shiftedMomentum p m) ρ)
            (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
              (-(finestMesh L k • shiftedMomentum p m)) σ))
  have hGl : Tendsto G atTop (𝓝 (massiveLogFn L k (toComplexVec p) μPlus μMinus z)) := by
    have h := t₁.sub (t₂.const_mul (1 / 2 : ℂ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop K] with j hj
    have r := hrel j (g₄.trans hj) (N j) (e j) p (hmom j (g₃.trans hj)) hstrip μPlus μMinus
    simp only [G]
    rw [← r]
    simp only [backgroundModeOnQuotient]
    ring
  obtain ⟨hTemp, -⟩ := hT L hS _ hz'
  obtain ⟨-, δ, π, ε, hc⟩ := id hTemp
  obtain ⟨-, P, hPP, -⟩ := hP L hS _ hTemp
  have hpol : IsHessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))
      (hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z))) :=
    Classical.epsilon_spec (p := IsHessianSymbol L _) ⟨P, hPP⟩
  obtain ⟨n₄, -, hbound⟩ := exists_forall_ge_of_eventuallyForSides hL2 hc.approx
  have hεt : Tendsto (fun j => ε (j + k)) atTop (𝓝 0) :=
    hc.err_tendsto.comp (tendsto_add_atTop_nat k)
  have hterm : ∀ (m : Fin 4 → ℤ) (ρ σ : Fin 4), Tendsto (fun j : ℕ =>
      (((PeriodicLattice.torusSide L (j + k))⁻¹ ^ 4 : ℝ) : ℂ) *
        complexHessian (massiveFieldFamily L (finestMesh L k ^ 2 * z)) (j + k)
          (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
            (finestMesh L k • shiftedMomentum p m) ρ)
          (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
            (-(finestMesh L k • shiftedMomentum p m)) σ)) atTop
      (𝓝 (hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
        (fun μ => ((finestMesh L k : ℝ) : ℂ) *
          PlaneWaves.shiftedFreq (toComplexVec p) m μ))) := by
    intro m ρ σ
    have hκ : (fun μ => ((finestMesh L k : ℝ) : ℂ) *
        PlaneWaves.shiftedFreq (toComplexVec p) m μ) =
          toComplexVec (finestMesh L k • shiftedMomentum p m) := by
      funext μ
      simp [PlaneWaves.shiftedFreq, toComplexVec, shiftedMomentum]
    have hmem : toComplexVec (finestMesh L k • shiftedMomentum p m) ∈ imStrip δ := by
      intro μ
      have h0 : (toComplexVec (finestMesh L k • shiftedMomentum p m) μ).im = 0 :=
        toComplexVec_mem_realDualPoints _ μ
      rw [h0, abs_zero]
      exact hc.delta_pos.le
    rw [hκ, hpol δ π ε hc ρ σ hmem, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hεt
    filter_upwards [eventually_ge_atTop (max n n₄)] with j hj
    have hb := hbound (j + k) (by omega) _
      (finestMesh_smul_shiftedMomentum_mem hL0 k j (hmom j (by omega)) m) 2 2 ρ σ
    simpa using hb
  have hGr : Tendsto G atTop (𝓝 ((((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
      ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
        hessianSymbol L (massiveFieldFamily L (finestMesh L k ^ 2 * z)) ρ σ
            (fun μ => ((finestMesh L k : ℝ) : ℂ) *
              PlaneWaves.shiftedFreq (toComplexVec p) m μ) *
          backgroundCoeff L k (toComplexVec p) μPlus ρ m *
          backgroundCoeff L k (-toComplexVec p) μMinus σ (-m))) := by
    have h : Tendsto (fun j : ℕ => (((finestMesh L k : ℝ) : ℂ) ^ 2)⁻¹ *
        ∑ m ∈ PlaneWaves.freqBox L k, ∑ ρ : Fin 4, ∑ σ : Fin 4,
          ((((PeriodicLattice.torusSide L (j + k))⁻¹ ^ 4 : ℝ) : ℂ) *
            complexHessian (massiveFieldFamily L (finestMesh L k ^ 2 * z)) (j + k)
              (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
                (finestMesh L k • shiftedMomentum p m) ρ)
              (YangMills.Construction.PeriodicOperators.Tempered.fourierModeForm L (j + k) 2
                (-(finestMesh L k • shiftedMomentum p m)) σ)) *
            backgroundCoeff L k (toComplexVec p) μPlus ρ m *
            backgroundCoeff L k (-toComplexVec p) μMinus σ (-m)) atTop _ :=
      Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun ρ _ =>
        tendsto_finsetSum _ fun σ _ => ((hterm m ρ σ).mul_const _).mul_const _)
    refine h.congr fun j => ?_
    simp only [G]
    rw [← mul_assoc, side_inv_pow_mul_finestMesh_sq hL0 k j, mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun ρ _ =>
      Finset.sum_congr rfl fun σ _ => ?_
    ring
  exact tendsto_nhds_unique hGl hGr
end YangMills.Construction.Tower.MassiveOpFunctions.TorusMomenta
end
