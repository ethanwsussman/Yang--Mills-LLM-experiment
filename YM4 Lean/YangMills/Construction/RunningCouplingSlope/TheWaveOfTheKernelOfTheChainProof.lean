import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChainIsATotal
import YangMills.Construction.RunningCouplingSlope.TheWaveOfTheKernelOfTheChain
import YangMills.Construction.RunningCouplingSlope.TheWaveOfTheKernelOfTheDifferenceProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open TorusFields SlopeCoefficient BlockAverages
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem fderiv_fderiv_comp_clm_zero {Ψ : F → ℝ} (hΨ : ContDiffAt ℝ 2 Ψ 0) (T : E →L[ℝ] F) (u v : E) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ T)) 0 u v = fderiv ℝ (fderiv ℝ Ψ) 0 (T u) (T v) := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.secondDeriv_comp_clm <;> assumption
end Calculus
private theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
private theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
variable {n : ℕ} [NeZero n]
private def abelianField (X : imaginaryQuaternions) (θ : TorusBond n → ℝ) : TorusField n :=
  fun x i => expUnit (θ (x, i) • X)
private def abelianLift (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions)
    (θ : TorusBond n → ℝ) : ℝ :=
  H n (abelianField X θ)
private def bondSpread {k : ℕ} (c : Fin k → TorusBond n) :
    (Fin k → ℝ) →L[ℝ] (TorusBond n → ℝ) :=
  ContinuousLinearMap.pi fun b => ∑ l, if c l = b then
    (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ) else 0
private theorem bondSpread_apply {k : ℕ} (c : Fin k → TorusBond n) (σ : Fin k → ℝ)
    (b : TorusBond n) : bondSpread c σ b = ∑ l, if c l = b then σ l else 0 := by
  simp only [bondSpread, ContinuousLinearMap.coe_pi', ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
private theorem bondSpread_single {k : ℕ} (c : Fin k → TorusBond n) (l : Fin k) :
    bondSpread c (Pi.single l 1) = Pi.single (c l) 1 := by
  funext b
  rw [bondSpread_apply, Pi.single_apply, Finset.sum_eq_single l]
  · by_cases h : c l = b
    · simp [h]
    · simp [h, Ne.symm h]
  · intro l' _ hne
    split_ifs <;> simp [hne]
  · simp
private theorem perturb_const {k : ℕ} (c : Fin k → TorusBond n) (X : imaginaryQuaternions)
    (σ : Fin k → ℝ) :
    perturb c (fun _ => X) σ (trivialField n) = abelianField X (bondSpread c σ) := by
  funext x i
  have h : (∑ l, if c l = (x, i) then σ l • X else 0) = (bondSpread c σ (x, i)) • X := by
    rw [bondSpread_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  simp only [perturb, trivialField, abelianField, mul_one, h]
private theorem abelianLift_comp {H : GaugeTotal} {k : ℕ} (c : Fin k → TorusBond n)
    (X : imaginaryQuaternions) :
    (fun σ : Fin k → ℝ => H n (perturb c (fun _ => X) σ (trivialField n))) =
      abelianLift H n X ∘ bondSpread c := by
  funext σ
  simp only [Function.comp, abelianLift, perturb_const]
private theorem contDiffAt_abelianLift {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0) :
    ContDiffAt ℝ 2 (abelianLift H n X) 0 := by
  classical
  let e := Fintype.equivFin (TorusBond n)
  let c : Fin (Fintype.card (TorusBond n)) → TorusBond n := e.symm
  let π₀ : (TorusBond n → ℝ) →ₗ[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    { toFun := fun θ l => θ (c l)
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  let π : (TorusBond n → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    LinearMap.toContinuousLinearMap π₀
  have hid : ∀ θ : TorusBond n → ℝ, bondSpread c (π θ) = θ := by
    intro θ
    funext b
    rw [bondSpread_apply, Finset.sum_eq_single (e b)]
    · simp [c, π, π₀]
    · intro l _ hl
      have : c l ≠ b := fun h => hl (by simp [← h, c])
      simp [this]
    · simp
  have hφ := hs _ c fun _ => X
  have hcomp : abelianLift H n X =
      (fun σ => H n (perturb c (fun _ => X) σ (trivialField n))) ∘ π := by
    funext θ
    simp only [Function.comp, perturb_const, abelianLift, hid]
  rw [hcomp]
  refine ContDiffAt.comp (0 : TorusBond n → ℝ) ?_ π.contDiff.contDiffAt
  simpa using hφ
private def abelianHessian (H : GaugeTotal) (n : ℕ) [NeZero n] (X : imaginaryQuaternions) :
    (TorusBond n → ℝ) →L[ℝ] (TorusBond n → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (abelianLift H n X)) 0
private theorem hessianAtTrivial_eq_abelianHessian {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (c c' : TorusBond n) :
    hessianAtTrivial H n c c' X X = abelianHessian H n X (Pi.single c 1) (Pi.single c' 1) := by
  have hX : (![X, X] : Fin 2 → imaginaryQuaternions) = fun _ => X := by
    funext l
    fin_cases l <;> rfl
  unfold hessianAtTrivial mixedDeriv
  rw [hX, iteratedFDeriv_two_apply, abelianLift_comp (H := H) (![c, c'] : Fin 2 → TorusBond n) X,
    fderiv_fderiv_comp_clm_zero (contDiffAt_abelianLift X hs), bondSpread_single, bondSpread_single]
  rfl
private theorem secondDerivAlong_eq_abelianHessian {H : GaugeTotal} (X : imaginaryQuaternions)
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (a : TorusBond n → ℝ) :
    secondDerivAlong H n (fun c => a c • X) = abelianHessian H n X a a := by
  let Ln : ℝ →L[ℝ] (TorusBond n → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have hpath : (fun s : ℝ => H n (expAlong n (fun c => a c • X) s)) = abelianLift H n X ∘ Ln := by
    funext s
    have : expAlong n (fun c => a c • X) s = abelianField X (Ln s) := by
      funext x i
      simp [expAlong, abelianField, Ln, smul_smul]
    simp only [Function.comp, abelianLift, this]
  unfold secondDerivAlong
  rw [hpath, iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_two_apply,
    fderiv_fderiv_comp_clm_zero (contDiffAt_abelianLift X hs)]
  simp [Ln, abelianHessian]
private def unitAngle (y : TorusSite n) : TorusBond n → ℝ := Pi.single (y, secondAxis) 1
private def siteAngles (f : TorusSite n → ℝ) : TorusBond n → ℝ := fun c =>
  if c.2 = secondAxis then f c.1 else 0
private theorem siteAngles_eq_sum (f : TorusSite n → ℝ) :
    siteAngles f = ∑ y, f y • unitAngle y := by
  funext b
  rw [Finset.sum_apply]
  by_cases h : b.2 = secondAxis
  · rw [Finset.sum_eq_single b.1]
    · have e : b = (b.1, secondAxis) := by rw [← h]
      simp [siteAngles, h, unitAngle, ← e]
    · intro y _ hy
      have : b ≠ (y, secondAxis) := fun e => hy (by rw [e])
      simp [unitAngle, this]
    · simp
  · have h0 : siteAngles f b = 0 := by simp [siteAngles, h]
    rw [h0]
    refine (Finset.sum_eq_zero fun y _ => ?_).symm
    have : b ≠ (y, secondAxis) := fun e => h (by rw [e])
    simp [unitAngle, this]
private theorem planeWave_eq (f : TorusSite n → ℝ) :
    planeWaveOnTorus f = fun c => siteAngles f c • thirdGenerator := by
  funext c
  by_cases h : c.2 = secondAxis <;> simp [planeWaveOnTorus, siteAngles, h]
private theorem secondDerivAlong_planeWave {H : GaugeTotal}
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (f : TorusSite n → ℝ) :
    secondDerivAlong H n (planeWaveOnTorus f) = ∑ y, ∑ x, f y * f x *
      hessianAtTrivial H n (y, secondAxis) (x, secondAxis) thirdGenerator thirdGenerator := by
  rw [planeWave_eq, secondDerivAlong_eq_abelianHessian thirdGenerator hs, siteAngles_eq_sum]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hessianAtTrivial_eq_abelianHessian thirdGenerator hs]
  simp only [unitAngle]
  ring
private theorem tendsto_perturb {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    Tendsto (fun σ : Fin k → ℝ => perturb c X σ (trivialField n)) (𝓝 0) (𝓝 (trivialField n)) := by
  have hc : Continuous fun σ : Fin k → ℝ => perturb c X σ (trivialField n) := by
    refine continuous_pi fun x => continuous_pi fun i => ?_
    simp only [perturb, trivialField, mul_one]
    refine continuous_expUnit.comp (continuous_finset_sum _ fun l _ => ?_)
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  have h0 : perturb c X (0 : Fin k → ℝ) (trivialField n) = trivialField n := by
    funext x i
    simp [perturb, trivialField, expUnit_zero]
  have := hc.tendsto 0
  rwa [h0] at this
private theorem hessianAtTrivial_translate {H : GaugeTotal} (h : IsGaugeTotalAt H n) (y x : TorusSite n) :
    hessianAtTrivial H n (y, secondAxis) (x, secondAxis) thirdGenerator thirdGenerator =
      hessianAtTrivial H n (0, secondAxis) (x - y, secondAxis) thirdGenerator thirdGenerator := by
  classical
  let g : TorusIsometry := ⟨1, fun _ => 1, fun i => -(y i).valMinAbs, fun _ => Or.inl rfl⟩
  have hon : ∀ z : TorusSite n, g.mapSite z = z - y := by
    intro z
    funext i
    simp [TorusIsometry.mapSite, g, sub_eq_add_neg]
  have hcar : ∀ σ : Fin 2 → ℝ, g.Transports
      (perturb ![(y, secondAxis), (x, secondAxis)] ![thirdGenerator, thirdGenerator] σ
        (trivialField n))
      (perturb ![(0, secondAxis), (x - y, secondAxis)]
        ![thirdGenerator, thirdGenerator] σ (trivialField n)) := by
    intro σ z k
    have e1 : g.axisSign (g.axisPerm.symm k) = 1 := rfl
    rw [if_pos e1]
    have e2 : g.axisPerm.symm k = k := rfl
    rw [e2, hon]
    simp only [perturb, trivialField, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have a0 : ((0 : TorusSite n), secondAxis) = (z - y, k) ↔ (y, secondAxis) = (z, k) := by
      simp only [Prod.mk.injEq, and_congr_left_iff]
      intro _
      constructor
      · intro h
        exact (sub_eq_zero.mp h.symm).symm
      · intro h
        rw [h, sub_self]
    have a1 : (x - y, secondAxis) = (z - y, k) ↔ (x, secondAxis) = (z, k) := by
      simp only [Prod.mk.injEq, sub_left_inj]
    simp only [a0, a1]
    congr!
  have hev := (tendsto_perturb ![(y, secondAxis), (x, secondAxis)]
    ![thirdGenerator, thirdGenerator]).eventually (h.isometry_invariant g)
  have hE : (fun σ : Fin 2 → ℝ => H n (perturb
      ![(y, secondAxis), (x, secondAxis)] ![thirdGenerator, thirdGenerator] σ (trivialField n))) =ᶠ[𝓝 0]
      fun σ => H n (perturb ![(0, secondAxis), (x - y, secondAxis)]
        ![thirdGenerator, thirdGenerator] σ (trivialField n)) := by
    filter_upwards [hev] with σ hσ
    exact (hσ _ (hcar σ)).symm
  have h2 := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hE 2).self_of_nhds
  unfold hessianAtTrivial mixedDeriv
  exact DFunLike.congr_fun h2 _
private theorem cosinePhase_mul_add_sinePhase_mul {t : ℝ} {j : ℤ} (ht : t * n = 2 * Real.pi * j)
    (x y : TorusSite n) :
    cosinePhase t x * cosinePhase t y + sinePhase t x * sinePhase t y = cosinePhase t (x - y) := by apply _root_.YangMills.SharedProofs.p72641 <;> assumption
theorem chainKernelCosineSum_of_chainLogarithm (h : ChainLogarithmIsGaugeTotal) :
    ChainKernelCosineSum := by
  intro a ha L _ hLs k ρ hρ hρ1 n₀ m t ht
  have hL1 : 1 < L := by have := hLs.2; omega
  have hsT : Tendsto (fun n : ℕ => 2 * L ^ n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have := Nat.lt_pow_self (n := n) hL1
      change n ≤ 2 * L ^ n
      omega) tendsto_id
  filter_upwards [hsT.eventually (h a ha L hLs k ρ hρ hρ1), eventually_ge_atTop n₀] with n htot hn
  have hj : t * ((2 * L ^ n : ℕ) : ℝ) = 2 * Real.pi * ((m * (L : ℤ) ^ (n - n₀) : ℤ) : ℝ) := by
    have hp : (L : ℝ) ^ n = (L : ℝ) ^ n₀ * (L : ℝ) ^ (n - n₀) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    have hL0 : (L : ℝ) ≠ 0 := by
      have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      exact this.ne'
    rw [ht]
    push_cast
    rw [hp]
    field_simp
  rw [secondDerivAlong_planeWave htot.contDiffAt_perturb,
    secondDerivAlong_planeWave htot.contDiffAt_perturb]
  have hrow : ∀ y : TorusSite (2 * L ^ n),
      (∑ x, cosinePhase t y * cosinePhase t x * hessianAtTrivial (chainLogarithm a ρ L k) (2 * L ^ n)
          (y, secondAxis) (x, secondAxis) thirdGenerator thirdGenerator) +
        (∑ x, sinePhase t y * sinePhase t x * hessianAtTrivial (chainLogarithm a ρ L k) (2 * L ^ n)
          (y, secondAxis) (x, secondAxis) thirdGenerator thirdGenerator) =
      chainCosineSum a ρ L n k t := by
    intro y
    rw [← Finset.sum_add_distrib]
    unfold chainCosineSum
    refine (Finset.sum_congr rfl fun x _ => ?_).trans
      (Fintype.sum_equiv (Equiv.subRight y) _ _ fun _ => rfl)
    have ex : (Equiv.subRight y) x = x - y := rfl
    rw [hessianAtTrivial_translate htot, ← add_mul, ex, ← cosinePhase_mul_add_sinePhase_mul hj x y]
    ring
  rw [← Finset.sum_add_distrib]
  simp only [hrow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : ((Fintype.card (TorusSite (2 * L ^ n)) : ℕ) : ℝ) = (2 * (L : ℝ) ^ n) ^ 4 := by
    simp [ZMod.card]
  rw [hc]
end YangMills.Construction.RunningCouplingSlope
end
