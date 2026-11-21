import YangMills.Construction.OneLoopLaw.CovarianceOfASymbolProof
import YangMills.Construction.OneLoopLaw.PeriodicityAndGaugeRelationOfASymbol
import YangMills.Construction.OneLoopLaw.PolarisationVanishesOnGaugeDirections
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStripProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.SymbolPeriodicity
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.Tempered
theorem exists_exponent_of_eventuallyForSides {L : ℕ} (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) : ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k, k₀ ≤ k → P k := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem complexify_mem_imStrip {δ : ℝ} (hδ : 0 ≤ δ) (y : InfiniteLattice.AmbientSpace) :
    toComplexVec y ∈ imStrip δ := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_mem_imStrip <;> assumption
theorem complexify_add (x y : InfiniteLattice.AmbientSpace) :
    toComplexVec (x + y) = toComplexVec x + toComplexVec y := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem add_complexify_mem_imStrip {δ : ℝ} {w : Fin 4 → ℂ} (hw : w ∈ imStrip δ)
    (y : InfiniteLattice.AmbientSpace) : w + toComplexVec y ∈ imStrip δ :=
  fun μ => by simpa [toComplexVec] using hw μ
theorem two_pi_smul_castVec_mem_dualLattice {s : ℕ} (hs : 0 < s) (v : Fin 4 → ℤ) :
    (2 * Real.pi) • castVec v ∈ dualLattice s := by apply _root_.YangMills.SharedProofs.p28269 <;> assumption
theorem eq_zero_on_imStrip_of_approx (hJ : DualLatticeDensity.Claim) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L} {δ : ℝ}
    {σ : SymbolArray} {e : ℕ → ℝ}
    (c : IsTemperedWitness L F δ σ e) {G : (Fin 4 → ℂ) → ℂ}
    {O : Set (Coordinates.ComplexCoordinates 4)}
    (hO : imStrip δ ⊆ O)
    (hG : Coordinates.ComplexCoordinates.IsHolomorphicIn O
      fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => G z)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) (hnn : ∀ k, N ≤ k → 0 ≤ e k)
    (hb : ∀ k, N ≤ k → ∀ p ∈ dualLattice (2 * L ^ k), ‖G (toComplexVec p)‖ ≤ C * e k) :
    ∀ w ∈ imStrip δ, G w = 0 := by
  have hcG : ContinuousOn G O := (continuous_apply (0 : Fin 1)).comp_continuousOn hG.2.1
  have hcv : Continuous toComplexVec :=
    continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  have hg : Continuous fun y => G (toComplexVec y) :=
    hcG.comp_continuous hcv fun y => hO (complexify_mem_imStrip c.delta_pos.le y)
  have hlim : Tendsto (fun k => C * e k) atTop (𝓝 0) := by
    simpa using c.err_tendsto.const_mul C
  exact ((hJ L hL).2.2 (fun y => G (toComplexVec y)) N (fun k => C * e k) hg hN
    (fun k hk => mul_nonneg hC (hnn k hk)) hlim hb).2 δ G c.delta_pos ⟨O, hO, hG⟩ (fun _ => rfl)
theorem symbol_periodicOnStrip (hJ : DualLatticeDensity.Claim)
    (hP : PlaneWaveSymmetries.PlaneWaveLawsHold) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L} {δ : ℝ}
    {σ : SymbolArray} {e : ℕ → ℝ}
    (c : IsTemperedWitness L F δ σ e) (μ ν : Fin 4) : RiemannSums.PeriodicOnStrip δ (σ μ ν) := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨k₁, h₁, p₁⟩ := exists_exponent_of_eventuallyForSides hL2 c.err_nonneg
  obtain ⟨k₂, -, p₂⟩ := exists_exponent_of_eventuallyForSides hL2 c.approx
  obtain ⟨O, hO, hh⟩ := c.analytic
  have hol := (hh μ ν).1
  intro w hw q hq
  obtain ⟨v, hv⟩ := hq
  have hqv : q = (2 * Real.pi) • castVec v := by
    ext ρ
    simp only [Pi.smul_apply, castVec, smul_eq_mul, hv ρ]
    ring
  let G : (Fin 4 → ℂ) → ℂ := fun z => σ μ ν (z + toComplexVec q) - σ μ ν z
  have hc : ContinuousOn (σ μ ν) O := (continuous_apply (0 : Fin 1)).comp_continuousOn hol.2.1
  have hshift : Continuous fun z : Fin 4 → ℂ => z + toComplexVec q :=
    continuous_id.add continuous_const
  have hG : Coordinates.ComplexCoordinates.IsHolomorphicIn
      (O ∩ (fun z => z + toComplexVec q) ⁻¹' O)
      fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => G z := by
    refine ⟨hol.1.inter (hol.1.preimage hshift), continuousOn_pi.2 fun _ => ?_, ?_⟩
    · have hs : ContinuousOn (fun z => σ μ ν (z + toComplexVec q))
          (O ∩ (fun z => z + toComplexVec q) ⁻¹' O) :=
        hc.comp hshift.continuousOn fun z hz => hz.2
      exact hs.sub (hc.mono inter_subset_left)
    · intro a ha j
      filter_upwards [hol.2.2 a ha.1 j, hol.2.2 (a + toComplexVec q) ha.2 j] with ζ h h'
      have e1 : (fun ζ : ℂ => fun _ : Fin 1 =>
            σ μ ν (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j + toComplexVec q)) =
          fun ζ : ℂ => fun _ : Fin 1 =>
            σ μ ν (a + toComplexVec q + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) := by
        funext ζ _
        rw [add_right_comm]
      have h'' : DifferentiableAt ℂ (fun ζ : ℂ => fun _ : Fin 1 =>
          σ μ ν (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j + toComplexVec q)) ζ := by
        rw [e1]
        exact h'
      exact h''.sub h
  have hsub : imStrip δ ⊆ O ∩ (fun z => z + toComplexVec q) ⁻¹' O :=
    fun z hz => ⟨hO hz, hO (add_complexify_mem_imStrip hz q)⟩
  have hN₁ : k₁ ≤ max k₁ k₂ := le_max_left _ _
  have hN₂ : k₂ ≤ max k₁ k₂ := le_max_right _ _
  have key := eq_zero_on_imStrip_of_approx hJ hL c hsub hG (C := 2) (by norm_num) (h₁.trans hN₁)
    (fun k hk => p₁ k (hN₁.trans hk)) (by
      intro k hk p hp
      have hk0 : 0 < k := lt_of_lt_of_le h₁ (hN₁.trans hk)
      have facts := hP L k hL hk0
      have hs : 0 < 2 * L ^ k := by
        have : 0 < L := by omega
        positivity
      have hq' : q ∈ dualLattice (2 * L ^ k) := hqv ▸ two_pi_smul_castVec_mem_dualLattice hs v
      have a := p₂ k (hN₂.trans hk) p hp 0 0 μ ν
      have b := p₂ k (hN₂.trans hk) (p + q) (add_mem hp hq') 0 0 μ ν
      rw [if_pos rfl] at a b
      have w1 : fourierModeForm L k 0 (p + q) μ = fourierModeForm L k 0 p μ := by
        rw [hqv]
        exact facts.periodic 0 μ p hp v
      have w2 : fourierModeForm L k 0 (-(p + q)) ν = fourierModeForm L k 0 (-p) ν := by
        rw [← facts.periodic 0 ν (-p) (neg_mem hp) (-v)]
        congr 1
        rw [hqv]
        ext ρ
        simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, castVec, smul_eq_mul,
          Int.cast_neg]
        ring
      rw [w1, w2, complexify_add] at b
      have le : ‖G (toComplexVec p)‖ ≤ e k + e k := by
        refine le_trans (le_of_eq ?_) ((norm_sub_le _ _).trans (add_le_add a b))
        congr 1
        simp only [G]
        ring
      linarith)
  exact sub_eq_zero.1 (key w hw)
theorem complexHessian_finset_sum {L k : ℕ} {F : FieldFamily L}
    (hF : ComplexHessianOfMember.Properties F k)
    (c : Fin 4 → ℂ) (B : Fin 4 → UnitEdge L k → Matrices.ComplexMatrix2)
    (hB : ∀ μ, B μ ∈ Tower.complexEdgeForms L k 0 0)
    {B' : UnitEdge L k → Matrices.ComplexMatrix2} (hB' : B' ∈ Tower.complexEdgeForms L k 0 0)
    (s : Finset (Fin 4)) :
    complexHessian F k (∑ μ ∈ s, c μ • B μ) B' = ∑ μ ∈ s, c μ * complexHessian F k (B μ) B' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hF.linear_left 1 0 (zero_mem _) 0 (zero_mem _) B' hB'
    simp only [one_smul, add_zero, one_mul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hF.linear_left (c a) (B a) (hB a) _ (sum_mem fun μ _ => Submodule.smul_mem _ _ (hB μ)) B'
        hB', ih]
theorem symbol_satisfiesWardIdentity (hJ : DualLatticeDensity.Claim)
    (hP : PlaneWaveSymmetries.PlaneWaveLawsHold) (hM : ComplexHessianOfMember.Statement)
    (hV : GaugeDirectionHessian.HessianKillsGaugeDirections) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L} {δ : ℝ}
    {σ : SymbolArray} {e : ℕ → ℝ}
    (hF : IsLatticeFunctional L F) (c : IsTemperedWitness L F δ σ e) :
    TemperedStiffness.SatisfiesWardIdentity δ σ := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨k₁, h₁, p₁⟩ := exists_exponent_of_eventuallyForSides hL2 c.err_nonneg
  obtain ⟨k₂, -, p₂⟩ := exists_exponent_of_eventuallyForSides hL2 c.approx
  obtain ⟨k₃, -, p₃⟩ := exists_exponent_of_eventuallyForSides hL2 hF
  obtain ⟨O, hO, hh⟩ := c.analytic
  intro w hw ν
  let G : (Fin 4 → ℂ) → ℂ := fun z => ∑ μ, (Complex.exp (Complex.I * z μ) - 1) * σ μ ν z
  have hc : ∀ μ, ContinuousOn (σ μ ν) O := fun μ =>
    (continuous_apply (0 : Fin 1)).comp_continuousOn (hh μ ν).1.2.1
  have hG : Coordinates.ComplexCoordinates.IsHolomorphicIn O
      fun (z : Coordinates.ComplexCoordinates 4) (_ : Fin 1) => G z := by
    refine ⟨(hh 0 ν).1.1, continuousOn_pi.2 fun _ => ?_, ?_⟩
    · refine continuousOn_finsetSum _ fun μ _ => ContinuousOn.mul ?_ (hc μ)
      exact Continuous.continuousOn (by fun_prop)
    · intro a ha j
      have hall : ∀ᶠ ζ in 𝓝 (0 : ℂ), ∀ μ : Fin 4, DifferentiableAt ℂ
          (fun ζ : ℂ => fun _ : Fin 1 =>
            σ μ ν (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ :=
        eventually_all.2 fun μ => (hh μ ν).1.2.2 a ha j
      filter_upwards [hall] with ζ h
      refine differentiableAt_pi.2 fun _ => ?_
      refine DifferentiableAt.fun_sum fun μ _ => ?_
      refine DifferentiableAt.mul ?_ (differentiableAt_pi.1 (h μ) 0)
      have hco : DifferentiableAt ℂ
          (fun ζ : ℂ => (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) μ) ζ := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        fun_prop
      exact ((hco.const_mul Complex.I).cexp).sub_const 1
  let N := max k₁ (max k₂ k₃)
  have hN₁ : k₁ ≤ N := le_max_left _ _
  have hN₂ : k₂ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₃ : k₃ ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  refine eq_zero_on_imStrip_of_approx hJ hL c hO hG (C := 8) (by norm_num) (h₁.trans hN₁)
    (fun k hk => p₁ k (hN₁.trans hk)) ?_ w hw
  intro k hk p hp
  have hk0 : 0 < k := lt_of_lt_of_le h₁ (hN₁.trans hk)
  have facts := hP L k hL hk0
  have hmem := p₃ k (hN₃.trans hk)
  have lin := hM L k hL hk0 F hmem
  have hneg : -p ∈ dualLattice (2 * L ^ k) := neg_mem hp
  have hB' := facts.mem_complex 0 ν (-p) hneg
  have hzero : ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) *
      complexHessian F k (fourierModeForm L k 0 p μ) (fourierModeForm L k 0 (-p) ν) = 0 := by
    have hv := hV L k hL hk0 F hmem (PlaneWaveSymmetries.phaseSite L k 0 p)
      (facts.phaseSite_traceless 0 p hp) _ hB'
    rw [facts.covDiff_phaseSite 0 p hp,
      complexHessian_finset_sum lin _ _ (fun μ => facts.mem_complex 0 μ p hp) hB'] at hv
    exact hv
  let t : ℂ := (((PeriodicLattice.torusSide L k)⁻¹ ^ 4 : ℝ) : ℂ)
  let X : Fin 4 → ℂ := fun μ =>
    t * complexHessian F k (fourierModeForm L k 0 p μ) (fourierModeForm L k 0 (-p) ν)
  have hG' : G (toComplexVec p) = ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) *
      (σ μ ν (toComplexVec p) - X μ) := by
    have hX : ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) * X μ = 0 := by
      have : ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) * X μ =
          t * ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) *
            complexHessian F k (fourierModeForm L k 0 p μ) (fourierModeForm L k 0 (-p) ν) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [X]
        ring
      rw [this, hzero, mul_zero]
    simp only [mul_sub, Finset.sum_sub_distrib, hX, sub_zero]
    rfl
  rw [hG']
  have hterm : ∀ μ ∈ (Finset.univ : Finset (Fin 4)),
      ‖(Complex.exp (Complex.I * (p μ : ℂ)) - 1) * (σ μ ν (toComplexVec p) - X μ)‖ ≤
        2 * e k := by
    intro μ _
    have a := p₂ k (hN₂.trans hk) p hp 0 0 μ ν
    rw [if_pos rfl] at a
    have a' : ‖σ μ ν (toComplexVec p) - X μ‖ ≤ e k := by
      rw [norm_sub_rev]
      exact a
    have hexp : ‖Complex.exp (Complex.I * (p μ : ℂ)) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
      norm_num
    rw [norm_mul]
    exact mul_le_mul hexp a' (norm_nonneg _) (by norm_num)
  refine (norm_sum_le_of_le _ hterm).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
theorem periodicityAndWardClaim_holds (hP : PlaneWaveSymmetries.PlaneWaveLawsHold)
    (hM : ComplexHessianOfMember.Statement)
    (hV : GaugeDirectionHessian.HessianKillsGaugeDirections)
    (hJ : DualLatticeDensity.Claim) :
    PeriodicityAndWardClaim := by
  intro L hL F δ σ e hF c
  exact ⟨fun μ ν => symbol_periodicOnStrip hJ hP hL c μ ν,
    symbol_satisfiesWardIdentity hJ hP hM hV hL hF c⟩
end YangMills.Construction.OneLoopLaw.SymbolPeriodicity
end
