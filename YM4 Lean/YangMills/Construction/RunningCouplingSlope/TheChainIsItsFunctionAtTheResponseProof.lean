import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.RunningCouplingSlope.ColourCoordinatesOfATower
import YangMills.Construction.RunningCouplingSlope.FirstOrderOfTheChainIsNearTheResponse
import YangMills.Construction.RunningCouplingSlope.FunctionOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.GaugeDirectionsOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheChainIsTheHessian
import YangMills.Construction.RunningCouplingSlope.TheChainIsItsFunctionAtTheResponse
import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheWholeChainIsBounded
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Tower.CriticalBranchResponse
section MixedDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem deriv_deriv_eq_fderiv_fderiv (φ : E → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (x y : E) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => φ (s • x + u • y)) 0) 0 =
      fderiv ℝ (fderiv ℝ φ) 0 x y := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
end MixedDerivative
variable {L n k : ℕ}
private theorem hessianOfFreeEnergy_eq_fderiv_coords (a : ℝ) {N : ℕ}
    (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelTriple L n k)
    (hφ : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0) (σ σ' : LevelTriple L n k) :
    hessianOfFreeEnergy a σ σ' =
      fderiv ℝ (fderiv ℝ fun w => tripleFreeEnergy a (e w)) 0 (e.symm σ) (e.symm σ') := by
  rw [← deriv_deriv_eq_fderiv_fderiv _ hφ]
  unfold hessianOfFreeEnergy
  simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
private theorem topFormNormSq_nonneg_and_pairing_le (hc : PauliCoordsOrthonormal)
    (hf : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hn : 0 < n) (f g : edgeFormSpace L n k k) :
    0 ≤ topFormNormSq f ∧
      (edgeFormPairing (f : Edge L n k k → Matrices.ComplexMatrix2)
        (g : Edge L n k k → Matrices.ComplexMatrix2)).re ≤
      Real.sqrt (topFormNormSq f) * Real.sqrt (topFormNormSq g) := by
  have hfin : Finite (Edge L n k k) := Set.finite_univ_iff.1 ((hf L hL k k le_rfl).1 n hn).2.1
  haveI : Finite (PositiveEdge L n k k) := Subtype.finite
  letI : Fintype (Fin 3 × PositiveEdge L n k k) := Fintype.ofFinite _
  obtain ⟨Ψ, -, hΨ⟩ := (hc L n k k hL hn le_rfl).1
  have hSq : ∀ h : edgeFormSpace L n k k, topFormNormSq h = ∑ i, Ψ h i ^ 2 := by
    intro h
    simp only [topFormNormSq, hΨ h h, Complex.ofReal_re, sq]
  refine ⟨by rw [hSq]; positivity, ?_⟩
  rw [hΨ f g, Complex.ofReal_re, hSq f, hSq g, ← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
private theorem backgroundCurvatureNormSq_meshScaledResponse
    (hm : ResponseMaps.ResponseMapsHold) (hr : TorusResponseRelations.statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hn : 0 < n) (B : edgeFormSpace L n k k) :
    backgroundCurvatureNormSq (meshScaledResponse L n k B) =
      (edgeFormPairing (periodicDefect L n k B : Edge L n k k → Matrices.ComplexMatrix2)
        (B : Edge L n k k → Matrices.ComplexMatrix2)).re := by
  have hM := hm L hL k n hk hn
  have hR := hr L hL k hk n hn B
  have hAdj := hM.coboundary_transpose (formCoboundary L n k (meshScaledResponse L n k B))
    (meshScaledResponse L n k B)
  have hCross := hM.crossing_transpose (periodicDefect L n k B) (meshScaledResponse L n k B)
  rw [hR.coboundary_eq, hCross, hM.crossing_eq, hR.smoothing_eq] at hAdj
  simp only [backgroundCurvatureNormSq, ← hAdj]
abbrev _root_.YangMills.SharedProofs.p4981 := @backgroundCurvatureNormSq_meshScaledResponse
private theorem abs_two_mul_add_le {C₂ C₃ r v v' w E T x₁ x₂ : ℝ} (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hr0 : 0 ≤ r) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hE0 : 0 ≤ E) (hT0 : 0 ≤ T) (hv'0 : 0 ≤ v')
    (hvv : v' ≤ v) (hTr : T ≤ Real.sqrt C₃ * r)
    (hx₁ : |x₁| ≤ C₂ * (v' + E * w) * T) (hx₂ : |x₂| ≤ C₂ * T * T) :
    |2 * x₁ + x₂| ≤ (2 * C₂ * Real.sqrt C₃ + C₂ * C₃) * (r * v + E * w * r + r * r) := by
  set q := Real.sqrt C₃ with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q * q = C₃ := Real.mul_self_sqrt hC₃
  have hMixed : C₂ * (v' + E * w) * T ≤ C₂ * q * (r * v + E * w * r) := by
    have hStep : C₂ * (v' + E * w) * T ≤ C₂ * (v + E * w) * T := by gcongr
    have hScale := mul_le_mul_of_nonneg_left hTr
      (mul_nonneg hC₂ (add_nonneg hv0 (mul_nonneg hE0 hw0)))
    calc _ ≤ C₂ * (v + E * w) * T := hStep
      _ ≤ C₂ * (v + E * w) * (q * r) := hScale
      _ = _ := by ring
  have hSquare : C₂ * T * T ≤ C₂ * C₃ * (r * r) := by
    have hTT : T * T ≤ (q * r) * (q * r) := mul_le_mul hTr hTr hT0 (mul_nonneg hq0 hr0)
    have hqr : (q * r) * (q * r) = C₃ * (r * r) := by rw [← hq2]; ring
    calc C₂ * T * T = C₂ * (T * T) := by ring
      _ ≤ C₂ * (C₃ * (r * r)) := mul_le_mul_of_nonneg_left (hqr ▸ hTT) hC₂
      _ = _ := by ring
  have hP : 0 ≤ r * v + E * w * r := by positivity
  have hCC : 0 ≤ C₂ * C₃ := by positivity
  have hCq : 0 ≤ 2 * C₂ * q := by positivity
  calc |2 * x₁ + x₂| ≤ |2 * x₁| + |x₂| := abs_add_le _ _
    _ = 2 * |x₁| + |x₂| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (C₂ * q * (r * v + E * w * r)) + C₂ * C₃ * (r * r) := by linarith
    _ ≤ (2 * C₂ * q + C₂ * C₃) * (r * v + E * w * r + r * r) := by nlinarith
theorem secondDerivAlongWaveNearResponseHessian_holds (hFlat : GaugeDirectionsAreFlat)
    (hBdd : HessianOfFreeEnergyBounded)
    (hNear : FirstVariationNearResponse)
    (hEq : SecondDerivAlongWaveEqHessian)
    (hMin : MinimizerFirstVariation)
    (hAn : ChainFreeEnergyAnalytic.Claim)
    (hMaps : ResponseMaps.ResponseMapsHold)
    (hRel : TorusResponseRelations.statement)
    (hPauli : PauliCoordsOrthonormal)
    (hFields : BondSetFields.ProductStructureHolds) :
    SecondDerivAlongWaveNearResponseHessian := by
  intro a ha L _ hLs k hk ρ hρ hρ1
  obtain ⟨C₂, c, hC₂, hc, hB⟩ := hBdd a ha L hLs k hk
  obtain ⟨C₃, hC₃, hN⟩ := hNear a ha L hLs k hk
  have hD := hEq a ha L hLs k hk ρ hρ hρ1
  refine ⟨2 * C₂ * Real.sqrt C₃ + C₂ * C₃, c, by positivity, hc, ?_⟩
  filter_upwards [hB, hN, hD, eventually_gt_atTop 0] with n hBn hNn hDn hn f B hf
  obtain ⟨⟨t, ht⟩, -⟩ := hMin a ha L hLs k n hk hn B
  obtain ⟨l, A, σ, hA, hdec, hsq⟩ := hNn B t ht
  rw [hDn f B hf t ht]
  obtain ⟨N, e, -⟩ := ht
  have hφ : ContDiffAt ℝ 2 (fun w => tripleFreeEnergy a (e w)) 0 :=
    ((hAn a ha L hLs k n hk hn).1 N e).1.contDiffAt
  have hsym : ∀ x y, fderiv ℝ (fderiv ℝ fun w => tripleFreeEnergy a (e w)) 0 x y =
      fderiv ℝ (fderiv ℝ fun w => tripleFreeEnergy a (e w)) 0 y x :=
    (hφ.isSymmSndFDerivAt (by simp)).eq
  have hH := hessianOfFreeEnergy_eq_fderiv_coords a e hφ
  have hg0 := (hFlat a ha L hLs k n hk hn).2 l A hA
  set b := backgroundOnlyTriple (meshScaledResponse L n k B) with hb
  set g := backgroundOnlyTriple A with hgdef
  have hexp : hessianOfFreeEnergy a t t =
      hessianOfFreeEnergy a b b + 2 * hessianOfFreeEnergy a b σ + hessianOfFreeEnergy a σ σ := by
    have e1 := hg0 b
    have e2 := hg0 σ
    have e3 := hg0 g
    rw [hH] at e1 e2 e3
    rw [hdec]
    simp only [hH, map_add, ContinuousLinearMap.add_apply]
    rw [hsym (e.symm b) (e.symm g), hsym (e.symm σ) (e.symm b), hsym (e.symm σ) (e.symm g)]
    linarith
  obtain ⟨hν0, hpair⟩ := topFormNormSq_nonneg_and_pairing_le hPauli hFields hLs hk hn
    (periodicDefect L n k B) B
  have hcurv := backgroundCurvatureNormSq_meshScaledResponse hMaps hRel hLs hk hn B
  have hrr : Real.sqrt (topFormNormSq (periodicDefect L n k B)) *
      Real.sqrt (topFormNormSq (periodicDefect L n k B)) =
        topFormNormSq (periodicDefect L n k B) :=
    Real.mul_self_sqrt hν0
  have hvv : Real.sqrt (backgroundCurvatureNormSq (meshScaledResponse L n k B)) ≤
      Real.sqrt (Real.sqrt (topFormNormSq (periodicDefect L n k B)) *
        Real.sqrt (topFormNormSq B)) :=
    Real.sqrt_le_sqrt (hcurv ▸ hpair)
  have hTr : Real.sqrt (tripleNormSq σ) ≤
      Real.sqrt C₃ * Real.sqrt (topFormNormSq (periodicDefect L n k B)) := by
    rw [← Real.sqrt_mul hC₃]
    exact Real.sqrt_le_sqrt hsq
  have b1 := hBn.2 (meshScaledResponse L n k B) σ
  have b2 := hBn.1 σ σ
  have key := abs_two_mul_add_le hC₂ hC₃ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.exp_pos _).le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hvv hTr b1 b2
  have e0 : hessianOfFreeEnergy a t t - hessianOfFreeEnergy a b b =
      2 * hessianOfFreeEnergy a b σ + hessianOfFreeEnergy a σ σ := by
    rw [hexp]
    ring
  rw [e0]
  refine key.trans (le_of_eq ?_)
  rw [hrr]
end YangMills.Construction.RunningCouplingSlope
end
