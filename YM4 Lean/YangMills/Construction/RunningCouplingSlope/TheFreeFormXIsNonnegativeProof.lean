import YangMills.Construction.RunningCouplingSlope.TheFreeFormXIsNonnegative
import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FreeXNonnegLemmas
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
open YangMills.Construction.Tower.FreeCoercivity
open YangMills.Construction.Coercivity
open YangMills.Construction.Tower.RealFrequencyFamily
open YangMills.Construction.Tower.FreeSymbolCoefficients
open YangMills.Construction.Tower.FreeSandwiches
open YangMills.Construction.Tower.PlaneWaves hiding vertexWeight
section Families
variable {ι : Type}
private theorem norm_familyDivergence_sq_le (d b : ι → Fin 4 → ℂ) (m : ι) :
    ‖familyDivergence d b m‖ ^ 2 ≤ (∑ μ, ‖d m μ‖ ^ 2) * bondNormSq b m := by
  have h1 : ‖familyDivergence d b m‖ ≤ ∑ μ, ‖d m μ‖ * ‖b m μ‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [norm_mul, RCLike.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) (fun μ => ‖d m μ‖)
    (fun μ => ‖b m μ‖)
  calc ‖familyDivergence d b m‖ ^ 2 ≤ (∑ μ, ‖d m μ‖ * ‖b m μ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
private theorem norm_weightedSiteSum_sq_le {p r B T : ℝ} {s : Finset ι} {z : ι} {D : ι → ℝ}
    {d : ι → Fin 4 → ℂ} {v : ι → ℝ} {u : ι → Fin 4 → ℂ} {dc : Fin 4 → ℂ}
    (h : IsAdmissibleFamily p r B T s z D d v u dc)
    (b : ι → Fin 4 → ℂ) : ‖weightedSiteSum s v (familyDivergence d b)‖ ^ 2 ≤ bondDirichlet s D b := by
  have h1 : ‖weightedSiteSum s v (familyDivergence d b)‖ ≤ ∑ m ∈ s, |v m| * ‖familyDivergence d b m‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun m => |v m|) (fun m => ‖familyDivergence d b m‖)
  have h3 : ∑ m ∈ s, |v m| ^ 2 = 1 := by
    simp only [sq_abs]
    exact h.site_sum_sq
  rw [h3, one_mul] at h2
  calc ‖weightedSiteSum s v (familyDivergence d b)‖ ^ 2
        ≤ (∑ m ∈ s, |v m| * ‖familyDivergence d b m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ∑ m ∈ s, ‖familyDivergence d b m‖ ^ 2 := h2
    _ ≤ bondDirichlet s D b := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [h.eq_normSq m hm]
        exact norm_familyDivergence_sq_le d b m
end Families
section Products
variable {J : Type} [Finite J] (w : J → ℝ)
private theorem wInner_eq_sum [Fintype J] (f g : J → ℂ) :
    wInner w f g = ∑ i, (w i : ℂ) * (conj (f i) * g i) := by
  simp only [wInner, PeriodicOperators.wPairing, tsum_fintype]
private theorem wInner_sub_right (f g g' : J → ℂ) :
    wInner w f (g - g') = wInner w f g - wInner w f g' := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.wInner_sub_right <;> assumption
private theorem conj_wInner (f g : J → ℂ) :
    conj (wInner w f g) = wInner w g f := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => by ring
end Products
private theorem pauliCoeff_topEdge_eq {L k : ℕ} {κ : Fin 4 → ℂ}
    (hav : Tower.PlaneWaveCalculus.SmoothingSymbols L k) (b : (colourEdges L k 0).UnitQuot → ℂ)
    (a : Fin 3) (μ : Fin 4) :
    pauliCoeff a (Tower.PlaneWaveCalculus.topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ b) μ) =
      weightedBondSum (freqBox L k) (edgeWeights L k κ) (edgeColourCoeffs L k b a) μ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.pauliCoeff_smoothing_edge <;> assumption
end FreeXNonnegLemmas
theorem freeXSymbolNonneg_proof (hCoercive : Tower.FreeCoercivity.FreeOperatorsCoercive)
    (hForms : Tower.FreeSymbolCoefficients.FreeSymbolForms)
    (hSand : Tower.FreeSandwiches.SandwichFacts)
    (hNum : Tower.RealFrequencyFamily.FamilyBoundsHold)
    (hPlane : Tower.PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hIndex : PeriodicOperators.TowerIndexSets.Claim)
    (hSymbols : PeriodicOperators.StripSymbols.Claim) :
    FreeXSymbolNonneg := by
  open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
    YangMills.Construction.Tower.FreeResolvents YangMills.Construction.Tower.FreeCoercivity
    YangMills.Construction.Coercivity YangMills.Construction.Tower.RealFrequencyFamily
    YangMills.Construction.Tower.FreeSymbolCoefficients
    YangMills.Construction.Tower.FreeSandwiches YangMills.Construction.Tower.PlaneWaves in
  intro L hL k hk κ hκ
  obtain ⟨cXi, -, cY, -, cC, -, hc⟩ := hCoercive
  obtain ⟨hops, -, -, -⟩ := hc L hL k hk
  have hB0 := (hIndex L hL k 0 (Nat.zero_le k)).2.1
  have hBk := (hIndex L hL k k le_rfl).2.1
  have : Finite (colourEdges L k 0).UnitQuot := hB0.finite_quot
  have : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have facts : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ (T : I'.Carrier → I.Carrier → ℂ), IsPeriodicKernel I I' T →
        SymbolSummableAt I I' T κ → StripSymbols.PointwiseCalculus I I' T κ :=
    fun hI hI' T hT hf => (hSymbols.2.1 _ _ hI hI').2.1 T κ hT hf
  have fQ := hops.Q.2.2 κ (Set.mem_univ κ)
  have fQt := hops.Qt.2.2 κ (Set.mem_univ κ)
  have fXi := hops.Xi.2.2 κ (Set.mem_univ κ)
  have FQt := facts hBk hB0 _ hops.Qt.1 fQt
  have FXi := facts hB0 hB0 _ hops.Xi.1 fXi
  obtain ⟨-, hper, hform, hprod⟩ := FQt.comp (colourEdges L k 0) hB0 _ hops.Q.1 fQ
  obtain ⟨-, -, hmapX⟩ := FXi.linComb _ hper hform 1 (-1)
  have eX : StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).Xi
      (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) =
        (trivialRescaledOperators L k).X := by
    funext a b
    simp [StripSymbols.linCombKernel, Tower.RescaledOperators.X, sub_eq_add_neg]
  have hX : symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ -
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ).comp
          (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ) := by
    have hmapX' := (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ)
      eX).symm.trans hmapX
    rw [hmapX', hprod]
    have hneg : ∀ M : QuotHom (colourEdges L k 0) (colourEdges L k 0), (-1 : ℂ) • M = -M :=
      fun M => neg_one_smul ℂ M
    simp only [one_smul, sub_eq_add_neg]
    rw [hneg]
  refine ⟨hX, fun b => ?_⟩
  have F := hForms L hL k hk κ hκ
  have W := hSand L hL k hk κ hκ
  obtain ⟨z, hz⟩ := hNum L hL k hk κ hκ
  obtain ⟨-, -, -, -, -, -, hav, -⟩ := hPlane L hL k hk
  obtain ⟨Qb, hQb⟩ : ∃ Qb, Qb = symbolHom (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q κ b := ⟨_, rfl⟩
  have e1 : wInner ((colourEdges L k 0).quotWeight 1) b
      (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b) =
      wInner ((colourEdges L k 0).quotWeight 1) b
        (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi κ b) -
      wInner ((colourEdges L k 0).quotWeight 1) b
        (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ Qb) := by
    rw [hX, hQb]
    exact FreeXNonnegLemmas.wInner_sub_right _ _ _ _
  have h := W.edge_adjoint b Qb
  rw [← hQb] at h
  have e2 : wInner ((colourEdges L k 0).quotWeight 1) b
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ Qb) =
      starRingEnd ℂ (topEdgeInner L k Qb Qb) :=
    (FreeXNonnegLemmas.conj_wInner _ _ _).symm.trans (congrArg (starRingEnd ℂ) h.symm)
  have e3 : ∀ a μ, topEdgeCoeff L k Qb a μ =
      weightedBondSum (freqBox L k) (edgeWeights L k κ) (edgeColourCoeffs L k b a) μ := fun a μ => by
    rw [hQb]
    exact FreeXNonnegLemmas.pauliCoeff_topEdge_eq hav b a μ
  have e4 := F.edge_Xi b
  have e5 := W.edge_norm Qb
  rw [e1, e2, e5]
  change 0 ≤ (edgeInner L k b _ - _).re
  rw [e4]
  simp only [Complex.sub_re, Complex.conj_re, Complex.ofReal_re, e3]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun a _ => ?_
  have := FreeXNonnegLemmas.norm_weightedSiteSum_sq_le hz (edgeColourCoeffs L k b a)
  simp only [bondQuadraticForm]
  linarith
end YangMills.Construction.RunningCouplingSlope
end
