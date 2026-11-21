import YangMills.Construction.RunningCouplingSlope.GaugeDirectionsOfTheWholeChainProof
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChainIsATotal
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheChainIsTheHessian
import YangMills.Construction.RunningCouplingSlope.TheGaugeShiftReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheWaveIsReadOnTheTop
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SecondDerivAlongWave
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem quadraticRemainder_isLittleO {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hf0 : fderiv ℝ f 0 = 0) :
    (fun w => f w - f 0 - (1 / 2) * fderiv ℝ (fderiv ℝ f) 0 w w) =o[𝓝 0] fun w => ‖w‖ ^ 2 := by apply _root_.YangMills.SharedProofs.p5928 <;> assumption
private theorem curve_quadratic_expansion {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hf0 : fderiv ℝ f 0 = 0) {c : ℝ → E} {v : E} (hc0 : c 0 = 0) (hc : HasDerivAt c v 0) :
    (fun r => f (c r) - f 0 - r ^ 2 / 2 * fderiv ℝ (fderiv ℝ f) 0 v v) =o[𝓝 0]
      fun r : ℝ => r ^ 2 := by apply _root_.YangMills.SharedProofs.p98659 <;> assumption
private theorem iteratedDeriv_two_eq_of_expansion {ψ : ℝ → ℝ} (hψ : ContDiffAt ℝ 2 ψ 0)
    (hψ0 : ψ 0 = 0) {q : ℝ} (h : (fun r => ψ r - r ^ 2 / 2 * q) =o[𝓝 0] fun r : ℝ => r ^ 2) :
    iteratedDeriv 2 ψ 0 = q := by
  have hr2 : (fun r : ℝ => r ^ 2) =o[𝓝 0] fun r : ℝ => r := by
    simpa using Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num)
  have hq2 : (fun r : ℝ => r ^ 2 / 2 * q) =O[𝓝 0] fun r : ℝ => r ^ 2 := by
    have : (fun r : ℝ => r ^ 2 / 2 * q) = fun r => (q / 2) * r ^ 2 := by
      funext r
      ring
    rw [this]
    exact isBigO_const_mul_self _ _ _
  have hψ2 : (fun r => ψ r) =O[𝓝 0] fun r : ℝ => r ^ 2 := by
    have := h.isBigO.add hq2
    refine this.congr_left fun r => ?_
    ring
  have hz : HasDerivAt ψ 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simpa [hψ0] using hψ2.trans_isLittleO hr2
  have hfz : fderiv ℝ ψ 0 = 0 := by
    have := hz.hasFDerivAt.fderiv
    simpa using this
  have h2 := quadraticRemainder_isLittleO hψ hfz
  set p := fderiv ℝ (fderiv ℝ ψ) 0 1 1 with hp
  have hlin : ∀ r : ℝ, fderiv ℝ (fderiv ℝ ψ) 0 r r = r ^ 2 * p := by
    intro r
    have e : r = r • (1 : ℝ) := by simp
    conv_lhs => rw [e]
    rw [map_smul, map_smul]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hp]
    ring
  have h3 : (fun r : ℝ => r ^ 2 / 2 * (q - p)) =o[𝓝 0] fun r : ℝ => r ^ 2 := by
    have h4 : (fun r => ψ r - ψ 0 - (1 / 2) * fderiv ℝ (fderiv ℝ ψ) 0 r r) =o[𝓝 0]
        fun r : ℝ => r ^ 2 := by
      refine h2.congr_right ?_ |>.trans_isBigO (isBigO_refl _ _)
      intro r
      simp
    have := h4.sub h
    refine this.congr_left fun r => ?_
    rw [hlin, hψ0]
    ring
  have h5 : q - p = 0 := by
    have h6 := h3.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    have h7 : Tendsto (fun t : ℝ => t ^ 2 / 2 * (q - p) / t ^ 2) (𝓝[≠] 0) (𝓝 ((q - p) / 2)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have : t ≠ 0 := ht
      field_simp
    have := tendsto_nhds_unique h6 h7
    linarith
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp only [← hp]
  linarith
end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem mixedDeriv_eq_secondFDeriv (g : E → ℝ) (hg : ContDiffAt ℝ 2 g 0) (x y : E) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => g (s • x + u • y)) 0) 0 =
      fderiv ℝ (fderiv ℝ g) 0 x y := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
private theorem deriv_line_eq_fderiv {g : E → ℝ} (hg : DifferentiableAt ℝ g 0) (x : E) :
    deriv (fun u : ℝ => g (u • x)) 0 = fderiv ℝ g 0 x := by
  have h1 : HasDerivAt (fun u : ℝ => u • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have h2 : HasFDerivAt g (fderiv ℝ g 0) ((0 : ℝ) • x) := by
    simpa using hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
end
open YangMills.Construction.TorusFields YangMills.Construction.BlockAverages YangMills.Construction.SlopeCoefficient
private theorem continuous_expUnit : Continuous expUnit := by apply _root_.YangMills.Construction.TorusFields.continuous_expUnit <;> assumption
private theorem expUnit_zero : expUnit 0 = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem tendsto_expAlong {n : ℕ} (B : TorusBond n → imaginaryQuaternions) :
    Tendsto (expAlong n B) (𝓝 0) (𝓝 (trivialField n)) := by
  have hc : Continuous (expAlong n B) := by
    refine continuous_pi fun x => continuous_pi fun i => ?_
    exact continuous_expUnit.comp (by fun_prop)
  have h0 : expAlong n B 0 = trivialField n := by
    funext x i
    simp [expAlong, trivialField, expUnit_zero]
  have := hc.tendsto 0
  rwa [h0] at this
private theorem contDiffAt_planeWave_line {n : ℕ} [NeZero n] {H : GaugeTotal}
    (hs : ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun σ : Fin k → ℝ => H n (perturb c X σ (trivialField n))) 0)
    (f : TorusSite n → ℝ) :
    ContDiffAt ℝ 2 (fun u : ℝ => H n (expAlong n (planeWaveOnTorus f) u)) 0 := by
  classical
  let e := Fintype.equivFin (TorusBond n)
  let c : Fin (Fintype.card (TorusBond n)) → TorusBond n := e.symm
  let θ : TorusBond n → ℝ := fun b => if b.2 = secondAxis then f b.1 else 0
  let line : ℝ →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) fun l => θ (c l)
  have hperturb : ∀ u : ℝ, perturb c (fun _ => thirdGenerator) (line u) (trivialField n) =
      expAlong n (planeWaveOnTorus f) u := by
    intro u
    funext x i
    have h : (∑ l, if c l = (x, i) then (line u) l • thirdGenerator else 0) =
        u • planeWaveOnTorus f (x, i) := by
      rw [Finset.sum_eq_single (e (x, i))]
      · have hce : c (e (x, i)) = (x, i) := by simp [c]
        rw [if_pos hce]
        have hl : (line u) (e (x, i)) = u * θ (x, i) := by
          simp only [line, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
          rw [Pi.smul_apply, hce]
          rfl
        rw [hl]
        by_cases hi : i = secondAxis
        · simp [θ, planeWaveOnTorus, hi, smul_smul]
        · simp [θ, planeWaveOnTorus, hi]
      · intro l _ hl
        have : c l ≠ (x, i) := fun h => hl (by simp [← h, c])
        simp [this]
      · simp
    simp only [perturb, trivialField, expAlong, mul_one, h]
  have hφ := hs _ c fun _ => thirdGenerator
  have hcomp : (fun u : ℝ => H n (expAlong n (planeWaveOnTorus f) u)) =
      (fun σ => H n (perturb c (fun _ => thirdGenerator) σ (trivialField n))) ∘ line := by
    funext u
    simp only [Function.comp, hperturb]
  rw [hcomp]
  refine ContDiffAt.comp (0 : ℝ) ?_ line.contDiff.contDiffAt
  simpa using hφ
section
open YangMills.Construction.Tower
variable {L n k : ℕ}
private theorem exists_orthonormal_coords (hc : PauliCoordsOrthonormal)
    (hp : Tower.FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    ∃ (ι : Type) (_ : Fintype ι) (Ψ : edgeFormSpace L n k j ≃ₗ[ℝ] (ι → ℝ)),
      ∀ f g : edgeFormSpace L n k j, (edgeFormPairing (f : Tower.Edge L n k j → Matrices.ComplexMatrix2)
        (g : Tower.Edge L n k j → Matrices.ComplexMatrix2)).re = ∑ i, Ψ f i * Ψ g i := by
  have hfin : Finite (PositiveEdge L n k j) :=
    Set.finite_univ_iff.mp ((((hp L hL k j hj).1 n hn).2.2.1 Set.univ).2.1)
  letI : Fintype (Fin 3 × PositiveEdge L n k j) := Fintype.ofFinite _
  obtain ⟨Ψ, -, hΨ⟩ := (hc L n k j hL hn hj).1
  exact ⟨_, inferInstance, Ψ, fun f g => by rw [hΨ f g, Complex.ofReal_re]⟩
abbrev _root_.YangMills.SharedProofs.p44870 := @exists_orthonormal_coords
private theorem form_eq_of_pairing_eq (hc : PauliCoordsOrthonormal)
    (hp : Tower.FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {y y' : edgeFormSpace L n k j}
    (h : ∀ x : edgeFormSpace L n k j,
      (edgeFormPairing (y : Tower.Edge L n k j → Matrices.ComplexMatrix2)
        (x : Tower.Edge L n k j → Matrices.ComplexMatrix2)).re =
      (edgeFormPairing (y' : Tower.Edge L n k j → Matrices.ComplexMatrix2)
        (x : Tower.Edge L n k j → Matrices.ComplexMatrix2)).re) : y = y' := by
  obtain ⟨ι, _, Ψ, hΨ⟩ := exists_orthonormal_coords hc hp hL hn hj
  have h1 := h (Ψ.symm (Ψ y - Ψ y'))
  rw [hΨ, hΨ, LinearEquiv.apply_symm_apply] at h1
  have h2 : ∑ i, (Ψ y i - Ψ y' i) ^ 2 = 0 := by
    have : ∑ i, (Ψ y i - Ψ y' i) ^ 2 = ∑ i, Ψ y i * (Ψ y - Ψ y') i -
        ∑ i, Ψ y' i * (Ψ y - Ψ y') i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [this, h1, sub_self]
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 h2
  apply Ψ.injective
  funext i
  have := h3 i (Finset.mem_univ i)
  have h4 : Ψ y i - Ψ y' i = 0 := by simpa using this
  linarith
private theorem pairing_zero_right (hc : PauliCoordsOrthonormal)
    (hp : Tower.FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (f : edgeFormSpace L n k j) :
    (edgeFormPairing (f : Tower.Edge L n k j → Matrices.ComplexMatrix2)
      ((0 : edgeFormSpace L n k j) : Tower.Edge L n k j → Matrices.ComplexMatrix2)).re = 0 := by
  obtain ⟨ι, _, Ψ, h⟩ := exists_orthonormal_coords hc hp hL hn hj
  rw [h, map_zero]
  simp
private theorem levelForms_eq_of_pairing_eq (hc : PauliCoordsOrthonormal)
    (hp : Tower.FaceSums.FacesAndPairings) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {J J' : LevelForms L n k}
    (h : ∀ ξ : LevelForms L n k, levelPairing (formValues J) (formValues ξ) =
      levelPairing (formValues J') (formValues ξ)) : J = J' := by
  classical
  have hz : ∀ (M : LevelForms L n k), ∑ i : Fin k, (edgeFormPairing
      (M.2 i : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)
      (((0 : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i :
          edgeFormSpace L n k ((i : ℕ) + 1)) :
        Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)).re = 0 := fun M =>
    Finset.sum_eq_zero fun i _ => pairing_zero_right hc hp hL hn i.2 _
  refine Prod.ext ?_ ?_
  · refine form_eq_of_pairing_eq hc hp hL hn (Nat.zero_le _) fun x => ?_
    have hs0 : ∀ M : LevelForms L n k,
        levelPairing (formValues M) (formValues ((x, 0) : LevelForms L n k)) =
        (edgeFormPairing (M.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
          (x : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)).re := by
      intro M
      have e1 := hz M
      change (edgeFormPairing (M.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
          (x : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)).re + ∑ i : Fin k, (edgeFormPairing
          (M.2 i : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)
          (((0 : (i : Fin k) → edgeFormSpace L n k ((i : ℕ) + 1)) i :
              edgeFormSpace L n k ((i : ℕ) + 1)) :
            Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)).re = _
      rw [e1, add_zero]
    have h1 := h (x, 0)
    rwa [hs0, hs0] at h1
  · funext i
    refine form_eq_of_pairing_eq hc hp hL hn i.2 fun x => ?_
    have h1 := h (0, Pi.single i x)
    have hs : ∀ M : LevelForms L n k, ∑ j : Fin k, (edgeFormPairing
        (M.2 j : Tower.Edge L n k ((j : ℕ) + 1) → Matrices.ComplexMatrix2)
        (((Pi.single i x : (j : Fin k) → edgeFormSpace L n k ((j : ℕ) + 1)) j :
            edgeFormSpace L n k ((j : ℕ) + 1)) :
          Tower.Edge L n k ((j : ℕ) + 1) → Matrices.ComplexMatrix2)).re =
        (edgeFormPairing (M.2 i : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)
          (x : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)).re := by
      intro M
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        exact pairing_zero_right hc hp hL hn j.2 _
      · simp
    have hs1 : ∀ M : LevelForms L n k,
        levelPairing (formValues M) (formValues ((0, Pi.single i x) : LevelForms L n k)) =
        (edgeFormPairing (M.2 i : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)
          (x : Tower.Edge L n k ((i : ℕ) + 1) → Matrices.ComplexMatrix2)).re := by
      intro M
      have e1 := hs M
      change (edgeFormPairing (M.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)
          ((0 : edgeFormSpace L n k 0) : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)).re +
          ∑ j : Fin k, (edgeFormPairing
          (M.2 j : Tower.Edge L n k ((j : ℕ) + 1) → Matrices.ComplexMatrix2)
          (((Pi.single i x : (j : Fin k) → edgeFormSpace L n k ((j : ℕ) + 1)) j :
              edgeFormSpace L n k ((j : ℕ) + 1)) :
            Tower.Edge L n k ((j : ℕ) + 1) → Matrices.ComplexMatrix2)).re = _
      rw [e1, pairing_zero_right hc hp hL hn (Nat.zero_le _), zero_add]
    rwa [hs1, hs1] at h1
private theorem hessian_eq_coords (a : ℝ) {N : ℕ} (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    (hg : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0) (τ τ' : LevelTriple L n k) :
    hessianOfFreeEnergy a τ τ' =
      fderiv ℝ (fderiv ℝ fun w => tripleFreeEnergy a (e w)) 0 (e.symm τ) (e.symm τ') := by
  rw [← mixedDeriv_eq_secondFDeriv _ hg]
  unfold hessianOfFreeEnergy
  simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
private theorem expMove_zero_unitPoint :
    expMove (0 : LevelForms L n k) (unitPoint L n k) = unitPoint L n k := by apply _root_.YangMills.SharedProofs.p5970 <;> assumption
end
open YangMills.Construction.Tower in
theorem secondDerivAlongWaveEqHessian_holds (hF : ChainFreeEnergyAnalytic.Claim)
    (hG : GaugeDirectionsAreFlat) (hM : ChainMapsAtMinimizers)
    (hT : ChainLogarithmIsGaugeTotal) (hR : PlaneWaveRepresentsTorusField)
    (hc : PauliCoordsOrthonormal) (hp : Tower.FaceSums.FacesAndPairings) :
    SecondDerivAlongWaveEqHessian := by
  intro a ha L _ hLs k hk ρ hρ hρ1
  have hL1 : 1 < L := by have := hLs.2; omega
  have hsT : Tendsto (fun n : ℕ => 2 * L ^ n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have := Nat.lt_pow_self (n := n) hL1
      change n ≤ 2 * L ^ n
      omega) tendsto_id
  filter_upwards [hsT.eventually (hT a ha L hLs k ρ hρ hρ1), eventually_gt_atTop 0] with n htot hn
    f B hB t ht
  obtain ⟨N, e, c, hc0, hcd, hev⟩ := ht
  have hFn := hF a ha L hLs k n hk hn
  have hgC : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0 := ((hFn.1 N e).1).contDiffAt
  have hD0 : fderiv ℝ (fun w => tripleFreeEnergy a (e w)) 0 = 0 := by
    ext x
    have hd : DifferentiableAt ℝ (fun w => tripleFreeEnergy a (e w)) 0 :=
      hgC.differentiableAt (by simp)
    have h1 := deriv_line_eq_fderiv hd x
    have h2 := (hG a ha L hLs k n hk hn).1 (e x)
    simp only [map_smul] at h1
    rw [h2] at h1
    simpa using h1.symm
  have hV := tendsto_expAlong (n := 2 * L ^ n) (planeWaveOnTorus f)
  have ev1 := hV.eventually (hFn.2 ρ hρ hρ1)
  have ev2 := hV.eventually (hM a ha L hLs k n hk hn)
  have key : ∀ᶠ u in 𝓝 (0 : ℝ), chainLogarithm a ρ L k (2 * L ^ n)
      (expAlong (2 * L ^ n) (planeWaveOnTorus f) u) =
      tripleFreeEnergy a (e (c u)) - tripleFreeEnergy a (e 0) := by
    filter_upwards [ev1, ev2, hev] with u h1 h2 h3
    obtain ⟨hl, hgr, hmu⟩ := h3
    have hr := hR L hLs k n hk hn f B hB u
    obtain ⟨J, μ, hJ, hμ, -, hΨ⟩ := h1 _ hr _ hl
    have hmaps := h2 _ hr _ hl
    have eJ : J = (e (c u)).2.1 :=
      levelForms_eq_of_pairing_eq hc hp hLs hn fun ξ => by rw [hJ ξ, hgr ξ]
    have eμ : μ = (e (c u)).2.2 := by
      refine form_eq_of_pairing_eq hc hp hLs hn (le_refl k) fun x => ?_
      obtain ⟨ξ, rfl⟩ := hmaps.topDeriv_surjective x
      rw [← hμ ξ, ← hmu ξ, eJ]
    have e0 : tripleFreeEnergy a (e 0) = chainFreeEnergy a (unitPoint L n k) 0 0 := by
      simp only [tripleFreeEnergy, map_zero, Prod.fst_zero, Prod.snd_zero, expMove_zero_unitPoint]
    rw [hΨ, eJ, eμ, e0]
    rfl
  have hψ := contDiffAt_planeWave_line htot.contDiffAt_perturb f
  have hexp := curve_quadratic_expansion hgC hD0 hc0 hcd
  have hψ0 : chainLogarithm a ρ L k (2 * L ^ n)
      (expAlong (2 * L ^ n) (planeWaveOnTorus f) 0) = 0 := by
    have := key.self_of_nhds
    rw [this, hc0, sub_self]
  rw [hessian_eq_coords a e hgC t t]
  refine iteratedDeriv_two_eq_of_expansion hψ hψ0 (hexp.congr' ?_ EventuallyEq.rfl)
  filter_upwards [key] with u hu
  simp only [hu]
end YangMills.Construction.RunningCouplingSlope.SecondDerivAlongWave
end
