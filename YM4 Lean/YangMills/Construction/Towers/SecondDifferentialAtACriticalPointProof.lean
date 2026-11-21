import YangMills.Construction.Towers.DifferentialsOfRealAnalyticMapsProof
import YangMills.Construction.Towers.DifferentialOfTheCompositeOfTheCriticalBranchProof
import YangMills.Construction.Towers.RealAnalyticMapsAlongExponentialCurvesProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.CriticalSecondDeriv
open AnalyticDifferentials AnalyticNearField LeftChartFields
section MixedPartials
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem hasDerivAt_deriv_comp_of_fderiv_eq_zero {ψ : E → ℂ} {c : ℝ × ℝ → E}
    (hψ : ContDiffAt ℝ 2 ψ (c 0)) (hc : ContDiffAt ℝ 2 c 0) (hcrit : fderiv ℝ ψ (c 0) = 0) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => ψ (c (s, t))) 0)
      (fderiv ℝ (fderiv ℝ ψ) (c 0) (fderiv ℝ c 0 (1, 0)) (fderiv ℝ c 0 (0, 1))) 0 := by
  have hψn : ∀ᶠ y in 𝓝 (c 0), DifferentiableAt ℝ ψ y :=
    (hψ.eventually (by simp)).mono fun y h => h.differentiableAt (by norm_num)
  have hcn : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), DifferentiableAt ℝ c p :=
    (hc.eventually (by simp)).mono fun y h => h.differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have htend : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 0) :=
    hline.continuousAt.tendsto
  have hctend : Tendsto (fun s : ℝ => c (s, 0)) (𝓝 0) (𝓝 (c 0)) :=
    (hc.continuousAt.tendsto).comp htend
  have hs : ∀ᶠ s : ℝ in 𝓝 0, deriv (fun t : ℝ => ψ (c (s, t))) 0 =
      fderiv ℝ ψ (c (s, 0)) (fderiv ℝ c (s, 0) (0, 1)) := by
    filter_upwards [htend.eventually hcn, hctend.eventually hψn] with s h1 h2
    have hl : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) (0, 1) 0 :=
      (hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))
    have h3 : HasDerivAt (fun t : ℝ => c (s, t)) (fderiv ℝ c (s, 0) (0, 1)) 0 :=
      h1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    exact (h2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3).deriv
  have hψ2 : DifferentiableAt ℝ (fderiv ℝ ψ) (c 0) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc2 : DifferentiableAt ℝ (fderiv ℝ c) 0 :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc0 : HasFDerivAt c (fderiv ℝ c 0) (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hc1 : HasDerivAt (fun s : ℝ => c (s, 0)) (fderiv ℝ c 0 (1, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ) hc0 hline
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ ψ (c (s, 0)))
      (fderiv ℝ (fderiv ℝ ψ) (c 0) (fderiv ℝ c 0 (1, 0))) 0 :=
    hψ2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc1
  have hc20 : HasFDerivAt (fderiv ℝ c) (fderiv ℝ (fderiv ℝ c) 0) (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) :=
    hc2.hasFDerivAt
  have hB : HasDerivAt (fun s : ℝ => fderiv ℝ c (s, 0))
      (fderiv ℝ (fderiv ℝ c) 0 (1, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, 0) : ℝ × ℝ)) (0 : ℝ) hc20 hline
  have hv : HasDerivAt (fun s : ℝ => fderiv ℝ c (s, 0) (0, 1))
      (fderiv ℝ (fderiv ℝ c) 0 (1, 0) (0, 1)) 0 := by
    simpa using hB.clm_apply (hasDerivAt_const (0 : ℝ) ((0, 1) : ℝ × ℝ))
  have hfin := hA.clm_apply hv
  have hz : (fun s : ℝ => fderiv ℝ ψ (c (s, 0)) (fderiv ℝ c (s, 0) (0, 1))) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => ψ (c (s, t))) 0 := hs.mono fun s h => h.symm
  have hfin' := hfin.congr_of_eventuallyEq hz.symm
  simpa [Prod.mk_zero_zero, hcrit] using hfin'
theorem hasDerivAt_deriv_comp_swap_of_fderiv_eq_zero {ψ : E → ℂ} {c : ℝ × ℝ → E}
    (hψ : ContDiffAt ℝ 2 ψ (c 0)) (hc : ContDiffAt ℝ 2 c 0) (hcrit : fderiv ℝ ψ (c 0) = 0) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => ψ (c (s, t))) 0)
      (fderiv ℝ (fderiv ℝ ψ) (c 0) (fderiv ℝ c 0 (1, 0)) (fderiv ℝ c 0 (0, 1))) 0 := by
  have hsw : HasFDerivAt (fun p : ℝ × ℝ => (p.2, p.1))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)) (0 : ℝ × ℝ) :=
    hasFDerivAt_snd.prodMk hasFDerivAt_fst
  have hc' : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => c (p.2, p.1)) 0 :=
    ContDiffAt.comp (0 : ℝ × ℝ) (g := c) (f := fun p : ℝ × ℝ => (p.2, p.1)) hc
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hd : HasFDerivAt (fun p : ℝ × ℝ => c (p.2, p.1))
      ((fderiv ℝ c 0).comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ))) (0 : ℝ × ℝ) :=
    HasFDerivAt.comp (0 : ℝ × ℝ) (g := c) (f := fun p : ℝ × ℝ => (p.2, p.1))
      (hc.differentiableAt (by norm_num)).hasFDerivAt hsw
  have h := hasDerivAt_deriv_comp_of_fderiv_eq_zero (ψ := ψ) (c := fun p : ℝ × ℝ => c (p.2, p.1))
    hψ hc' hcrit
  rw [hd.fderiv] at h
  have hsym := hψ.isSymmSndFDerivAt (by simp)
  have hv := hsym (fderiv ℝ c 0 (0, 1)) (fderiv ℝ c 0 (1, 0))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst'] at h
  have h' : HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => ψ (c (s, t))) 0)
      (fderiv ℝ (fderiv ℝ ψ) (c 0) (fderiv ℝ c 0 (0, 1)) (fderiv ℝ c 0 (1, 0))) 0 := h
  rw [hv] at h'
  exact h'
theorem eventuallyEq_deriv_slice_snd {G G' : ℝ × ℝ → ℂ} (h : G =ᶠ[𝓝 0] G') :
    (fun s : ℝ => deriv (fun t : ℝ => G (s, t)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => G' (s, t)) 0 := by
  have hline : Tendsto (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 0) :=
    (((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))).continuousAt).tendsto
  filter_upwards [hline.eventually h.eventually_nhds] with s hs
  have hc : Tendsto (fun t : ℝ => ((s, t) : ℝ × ℝ)) (𝓝 0) (𝓝 (s, 0)) :=
    (((hasDerivAt_const (0 : ℝ) s).prodMk (hasDerivAt_id (0 : ℝ))).continuousAt).tendsto
  exact Filter.EventuallyEq.deriv_eq (hc.eventually hs)
theorem eventuallyEq_deriv_slice_fst {G G' : ℝ × ℝ → ℂ} (h : G =ᶠ[𝓝 0] G') :
    (fun t : ℝ => deriv (fun s : ℝ => G (s, t)) 0) =ᶠ[𝓝 0]
      fun t : ℝ => deriv (fun s : ℝ => G' (s, t)) 0 := by
  have hline : Tendsto (fun t : ℝ => ((0, t) : ℝ × ℝ)) (𝓝 0) (𝓝 0) :=
    (((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))).continuousAt).tendsto
  filter_upwards [hline.eventually h.eventually_nhds] with t ht
  have hc : Tendsto (fun s : ℝ => ((s, t) : ℝ × ℝ)) (𝓝 0) (𝓝 (0, t)) :=
    (((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t)).continuousAt).tendsto
  exact Filter.EventuallyEq.deriv_eq (hc.eventually ht)
end MixedPartials
section EntrywiseMatrices
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def entryCLM (r c : Fin 2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X r c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem eq_sum_entry_smul_single (X : ComplexMatrix2) :
    X = ∑ r, ∑ c, X r c • (Matrix.single r c (1 : ℂ) : ComplexMatrix2) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Fin.sum_univ_two, Matrix.sum_apply, Matrix.single_apply]
theorem contDiffOn_of_forall_entry {f : E → ComplexMatrix2} {S : Set E}
    (h : ∀ r c, ContDiffOn ℝ ∞ (fun p => f p r c) S) : ContDiffOn ℝ ∞ f S := by
  have hf : f = fun p => ∑ r, ∑ c, f p r c • (Matrix.single r c (1 : ℂ) : ComplexMatrix2) :=
    funext fun p => eq_sum_entry_smul_single (f p)
  rw [hf]
  exact ContDiffOn.sum fun r _ => ContDiffOn.sum fun c _ => (h r c).smul contDiffOn_const
theorem differentiableAt_of_forall_entry {f : ℝ → ComplexMatrix2} {t : ℝ}
    (h : ∀ r c, DifferentiableAt ℝ (fun u => f u r c) t) : DifferentiableAt ℝ f t := by apply _root_.YangMills.Construction.Tower.AnalyticRepresentation.differentiableAt_of_forall_entry <;> assumption
theorem contDiff_matExp : ContDiff ℝ ∞ (ComplexMatrix2.matExp) := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.contDiff_matExp <;> assumption
end EntrywiseMatrices
section PauliCoefficients
def halfTraceMulLinear (M : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ComplexMatrix2.halfTrace (X * M)
  map_add' X Y := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, add_mul, Matrix.trace_add]
    ring
  map_smul' c X := by
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring
def halfTraceMulCLM (M : ComplexMatrix2) : ComplexMatrix2 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap ((halfTraceMulLinear M).restrictScalars ℝ)
def pauliCoeff (a : Fin 3) : ComplexMatrix2 →ₗ[ℝ] ℝ :=
  Complex.reLm ∘ₗ (halfTraceMulLinear (ComplexMatrix2.pauliFamily a)).restrictScalars ℝ
theorem pauliCoeff_apply (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a X = (ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily a)).re := rfl
theorem halfTrace_mul_pauliFamily_zero (X : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 0) = (X 0 1 + X 1 0) / 2 := by
  have h : ComplexMatrix2.pauliFamily 0 = !![0, 1; 1, 0] := rfl
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, h]
  ring
theorem halfTrace_mul_pauliFamily_one (X : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 1) =
      Complex.I * (X 0 1 - X 1 0) / 2 := by
  have h : ComplexMatrix2.pauliFamily 1 = !![0, -Complex.I; Complex.I, 0] := rfl
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, h]
  ring
theorem halfTrace_mul_pauliFamily_two (X : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 2) = (X 0 0 - X 1 1) / 2 := by
  have h : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := rfl
  simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, h]
  ring
theorem entries_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (X 0 0).im = 0 ∧ X 1 1 = -X 0 0 ∧ (X 0 1).re = (X 1 0).re ∧ (X 0 1).im = -(X 1 0).im := by
  obtain ⟨h1, h2⟩ := hX
  have e00 : X 0 0 = star (X 0 0) := congrFun (congrFun h1 0) 0
  have e01 : X 0 1 = star (X 1 0) := congrFun (congrFun h1 0) 1
  have htr : X 0 0 + X 1 1 = 0 := by
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using h2
  refine ⟨?_, by linear_combination htr, ?_, ?_⟩
  · have := congrArg Complex.im e00
    simp at this
    linarith
  · rw [e01]; simp
  · rw [e01]; simp
theorem halfTrace_mul_pauliFamily_eq_ofReal {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) (a : Fin 3) :
    ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily a) = ((pauliCoeff a X : ℝ) : ℂ) := by
  obtain ⟨h0, h1, h2, h3⟩ := entries_of_mem_hermitianTraceless hX
  rw [pauliCoeff_apply]
  apply Complex.ext
  · simp
  · fin_cases a
    · show (ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 0)).im = _
      rw [halfTrace_mul_pauliFamily_zero]
      simp [h3]
    · show (ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 1)).im = _
      rw [halfTrace_mul_pauliFamily_one]
      simp [h2]
    · show (ComplexMatrix2.halfTrace (X * ComplexMatrix2.pauliFamily 2)).im = _
      rw [halfTrace_mul_pauliFamily_two]
      simp [h0, h1]
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by
  obtain ⟨h0, h1, h2, h3⟩ := entries_of_mem_hermitianTraceless hX
  have c0 : pauliCoeff 0 X = (X 1 0).re := by
    rw [pauliCoeff_apply, halfTrace_mul_pauliFamily_zero]
    simp [h2]
  have c1 : pauliCoeff 1 X = (X 1 0).im := by
    rw [pauliCoeff_apply, halfTrace_mul_pauliFamily_one]
    simp [h3]
  have c2 : pauliCoeff 2 X = (X 0 0).re := by
    rw [pauliCoeff_apply, halfTrace_mul_pauliFamily_two]
    simp [h1]
  have p0 : ComplexMatrix2.pauliFamily 0 = !![0, 1; 1, 0] := rfl
  have p1 : ComplexMatrix2.pauliFamily 1 = !![0, -Complex.I; Complex.I, 0] := rfl
  have p2 : ComplexMatrix2.pauliFamily 2 = !![1, 0; 0, -1] := rfl
  rw [Fin.sum_univ_three, c0, c1, c2, p0, p1, p2]
  ext i l
  fin_cases i <;> fin_cases l <;> apply Complex.ext <;> simp [h0, h1, h2, h3]
theorem pauliFamily_mem (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
end PauliCoefficients
section EdgeForms
variable {L n k j : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_isPositivelyOriented (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := rfl
structure LinkFacts (L n k j : ℕ) : Prop where
  not_opp : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented
  conditions : (finiteData L n k j).Conditions
  tangentEq : FiniteTangentSpaceEq L n k j
  curveLog : ∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra
theorem extendOddly_mem (hl : LinkFacts L n k j) {f : Edge L n k j → ComplexMatrix2}
    (hf : ∀ b, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact hf b hb
  · by_cases hb : b.IsPositivelyOriented
    · simp only [extendOddly, if_pos hb, if_neg (hl.not_opp b hb), opposite_opposite]
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [extendOddly, if_pos hr, if_neg hb, neg_neg]
theorem edgeFormOfPositiveValues_mem (hl : LinkFacts L n k j)
    {w : PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ b, w b ∈ ComplexMatrix2.hermitianTraceless) :
    edgeFormOfPositiveValues w ∈ edgeFormSpace L n k j := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [edgeFormOfPositiveValues, dif_pos hb]
    exact hw _
  · by_cases hb : b.IsPositivelyOriented
    · have hr := hl.not_opp b hb
      have hrr : b.opposite.opposite.IsPositivelyOriented := hb
      simp only [edgeFormOfPositiveValues, dif_pos hb, dif_neg hr, dif_pos hrr]
      rfl
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      simp only [edgeFormOfPositiveValues, dif_pos hr, dif_neg hb, neg_neg]
theorem pauliBasisForm_mem (hl : LinkFacts L n k j) (b : PositiveEdge L n k j) (a : Fin 3) :
    pauliBasisForm b a ∈ edgeFormSpace L n k j := by
  refine edgeFormOfPositiveValues_mem hl fun c => ?_
  split_ifs
  · exact pauliFamily_mem a
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
theorem edgeForm_ext {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) (h : ∀ b, b.IsPositivelyOriented → B b = B' b) :
    B = B' := by apply _root_.YangMills.SharedProofs.p88895 <;> assumption
theorem pauliBasisForm_apply (b c : PositiveEdge L n k j) (a : Fin 3) :
    pauliBasisForm b a c.1 =
      open Classical in if c = b then ComplexMatrix2.pauliFamily a else 0 := by
  simp only [pauliBasisForm, edgeFormOfPositiveValues, dif_pos c.2]
theorem ofReal_smul_eq_smul (s : ℝ) (B : Edge L n k j → ComplexMatrix2) : (s : ℂ) • B = s • B :=
  algebraMap_smul ℂ s B
variable [Fintype (PositiveEdge L n k j)] {N : ℕ} (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N)
theorem formOfCoords_eq_sum (y : Fin N → ℝ) :
    formOfCoords ν y = ∑ i : PositiveEdge L n k j × Fin 3,
      y (ν i) • pauliBasisForm i.1 i.2 := by apply _root_.YangMills.Construction.Tower.AnalyticAlongExpCurves.formOfCoords_eq_sum <;> assumption
theorem formOfCoords_apply (y : Fin N → ℝ) (b : PositiveEdge L n k j) :
    formOfCoords ν y b.1 = ∑ a, y (ν (b, a)) • ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.AnalyticAlongExpCurves.formOfCoords_apply <;> assumption
theorem formOfCoords_mem (hl : LinkFacts L n k j) (y : Fin N → ℝ) :
    formOfCoords ν y ∈ edgeFormSpace L n k j := by
  rw [formOfCoords_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (pauliBasisForm_mem hl i.1 i.2)
theorem formOfCoords_add_smul (s t : ℝ) (u u' : Fin N → ℝ) :
    formOfCoords ν (s • u + t • u') =
      s • formOfCoords ν u + t • formOfCoords ν u' := by
  simp only [formOfCoords_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]
theorem continuous_formOfCoords : Continuous (formOfCoords ν) := by
  have h : formOfCoords ν = fun y => ∑ i : PositiveEdge L n k j × Fin 3,
      y (ν i) • pauliBasisForm i.1 i.2 := funext (formOfCoords_eq_sum ν)
  rw [h]
  exact continuous_finsetSum _ fun i _ => (continuous_apply _).smul continuous_const
def pauliCoords : (PositiveEdge L n k j → ComplexMatrix2) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun i =>
    (pauliCoeff (ν.symm i).2) ∘ₗ (LinearMap.proj (ν.symm i).1))
theorem pauliCoords_apply (Y : PositiveEdge L n k j → ComplexMatrix2) (i : Fin N) :
    pauliCoords ν Y i = pauliCoeff (ν.symm i).2 (Y (ν.symm i).1) := rfl
theorem formOfCoords_pauliCoords {Y : PositiveEdge L n k j → ComplexMatrix2}
    (hY : ∀ b, Y b ∈ ComplexMatrix2.hermitianTraceless) (b : PositiveEdge L n k j) :
    formOfCoords ν (pauliCoords ν Y) b.1 = Y b := by
  rw [formOfCoords_apply]
  simp only [pauliCoords_apply, Equiv.symm_apply_apply]
  exact sum_pauliCoeff_smul (hY b)
def edgeFormCoords (B : Edge L n k j → ComplexMatrix2) : Fin N → ℝ :=
  pauliCoords ν (restrictToPositiveEdges B)
theorem formOfCoords_edgeFormCoords (hl : LinkFacts L n k j) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : formOfCoords ν (edgeFormCoords ν B) = B :=
  edgeForm_ext (formOfCoords_mem ν hl _) hB fun b hb =>
    formOfCoords_pauliCoords ν (Y := restrictToPositiveEdges B) (fun c => hB.1 c.1 c.2) ⟨b, hb⟩
theorem smul_add_smul_eq_formOfCoords (hl : LinkFacts L n k j)
    {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) (s t : ℝ) :
    (s : ℂ) • B + (t : ℂ) • B' =
      formOfCoords ν (s • edgeFormCoords ν B + t • edgeFormCoords ν B') := by
  rw [formOfCoords_add_smul, formOfCoords_edgeFormCoords ν hl hB,
    formOfCoords_edgeFormCoords ν hl hB', ofReal_smul_eq_smul, ofReal_smul_eq_smul]
end EdgeForms
section ExpTwist
variable {L n k j : ℕ}
theorem expTwist_of_isPositivelyOriented (A U : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := if_pos hb
theorem isUnit_det_of_mem_compactGaugeGroup {V : ComplexMatrix2}
    (hV : V ∈ PeriodicLattice.compactGaugeGroup) : IsUnit V.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem eq_expTwist {V A U : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldSpace L n k j)
    (h : ∀ b, b.IsPositivelyOriented → V b = ComplexMatrix2.matExp (Complex.I • A b) * U b) :
    V = PeriodicLattice.expTwist A U := by apply _root_.YangMills.Construction.Tower.ProlongDifferential.eq_expTwist <;> assumption
theorem expTwist_zero {U : Edge L n k j → ComplexMatrix2} (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist 0 U = U := by apply _root_.YangMills.Construction.Tower.AnalyticNearField.expTwist_zero <;> assumption
theorem expTwist_mem (hl : LinkFacts L n k j) {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    PeriodicLattice.expTwist A U ∈ fieldSpace L n k j := by
  have h := hl.conditions.1.1 U hU A hA
  obtain ⟨-, hbij, -⟩ := hl.tangentEq
  have hw : (fun b : PositiveEdge L n k j => ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1) ∈
      specialUnitaryPower (PositiveEdge L n k j) := fun b => by
    have h1 := (h b).1 1
    exact show ComplexMatrix2.matExp (Complex.I • A b.1) * U b.1 ∈
        ComplexMatrix2.specialUnitary from by
      simpa [leftExpMul, LatticeData.onPositive, finiteData] using h1
  obtain ⟨V, hV, hVw⟩ := hbij.surjOn hw
  have h2 := eq_expTwist (A := A) (U := U) hV fun b hb => congrFun hVw ⟨b, hb⟩
  rw [← h2]
  exact hV
theorem hasDerivAt_expTwist_smul (hl : LinkFacts L n k j) {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    HasDerivAt (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b)
      (Complex.I • A b * U b) 0 := by
  have h := ((hl.conditions.1.1 U hU A hA) ⟨b, hb⟩).2
  have he : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b) =
      fun t : ℝ => leftExpMul ((t : ℂ) • A b) (U b) := by
    funext t
    rw [expTwist_of_isPositivelyOriented _ _ hb]
    rfl
  rw [he]
  exact h
theorem curveTangent_expTwist_smul (hl : LinkFacts L n k j) {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    curveTangent (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U) = A := by
  have h0 : PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • A) U = U := by
    simpa using expTwist_zero hU
  have key : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b) 0 *
        (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • A) U b)⁻¹) = A b := by
    intro b hb
    rw [(hasDerivAt_expTwist_smul hl hA hU hb).deriv, h0, mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compactGaugeGroup (hU.1 b (mem_univ b))),
      mul_one, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  have hmem := extendOddly_mem hl (f := fun b => Complex.I⁻¹ •
    (deriv (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b) 0 *
      (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • A) U b)⁻¹))
    fun b hb => by
      rw [key b hb]
      exact hA.1 b hb
  exact edgeForm_ext hmem hA fun b hb => (if_pos hb).trans (key b hb)
theorem curveTangent_mem (hl : LinkFacts L n k j) {I : Set ℝ}
    {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hI : IsOpenIntervalAroundZero I) (hγ : MapsTo γ I (fieldSpace L n k j))
    (hd : ∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableAt ℝ (fun t => γ t b) 0) :
    curveTangent γ ∈ edgeFormSpace L n k j :=
  extendOddly_mem hl fun b hb =>
    ((hl.curveLog I hI (fun t => γ t b) (fun _ ht => (hγ ht).1 b (mem_univ b)) (hd b hb)).2.2.2)
theorem exists_interval_subset {S : Set ℝ} (hS : S ∈ 𝓝 (0 : ℝ)) :
    ∃ I ⊆ S, IsOpenIntervalAroundZero I := by apply _root_.YangMills.Construction.Tower.AnalyticAlongExpCurves.exists_openInterval_subset <;> assumption
theorem hasDerivAt_pair_fst : HasDerivAt (fun s : ℝ => ((s, 0) : ℝ × ℝ)) (1, 0) 0 :=
  (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
theorem hasDerivAt_pair_snd : HasDerivAt (fun t : ℝ => ((0, t) : ℝ × ℝ)) (0, 1) 0 :=
  (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
theorem curveTangent_congr {f g : ℝ → Edge L n k j → ComplexMatrix2} (h : f =ᶠ[𝓝 0] g) :
    curveTangent f = curveTangent g := by apply _root_.YangMills.SharedProofs.p19450 <;> assumption
theorem curveTangent_family_mem (hl : LinkFacts L n k j) {U₀ : Edge L n k j → ComplexMatrix2}
    {𝒪 : Set (ℝ × ℝ)} {W : ℝ × ℝ → Edge L n k j → ComplexMatrix2}
    (hW : IsSmoothTwoParamFamily U₀ 𝒪 W)
    {σ : ℝ → ℝ × ℝ} {e : ℝ × ℝ} (hσ : HasDerivAt σ e 0) (hσ0 : σ 0 = 0) :
    curveTangent (fun s => W (σ s)) ∈ edgeFormSpace L n k j := by
  obtain ⟨hO, h0O, hmaps, -, hent⟩ := hW
  have hnb : σ ⁻¹' 𝒪 ∈ 𝓝 (0 : ℝ) :=
    hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hO.mem_nhds h0O)
  obtain ⟨I, hIS, hI⟩ := exists_interval_subset hnb
  refine curveTangent_mem hl hI (fun s hs => hmaps (hIS hs)) fun b hb =>
    differentiableAt_of_forall_entry fun r c => ?_
  have hd : DifferentiableAt ℝ (fun p => W p b r c) (σ 0) := by
    rw [hσ0]
    exact ((hent b hb r c).contDiffAt (hO.mem_nhds h0O)).differentiableAt (by simp)
  exact hd.comp (0 : ℝ) hσ.differentiableAt
variable [Fintype (PositiveEdge L n k j)] [Nonempty (PositiveEdge L n k j)] {N : ℕ}
  (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N)
theorem exists_coords_of_family (hl : LinkFacts L n k j)
    (hE : PowerExpCharts.ExpChartsStatement) (hM : ComplexMatrix2.ExpLogEstimates)
    {U₀ : Edge L n k j → ComplexMatrix2}
    (hU₀ : U₀ ∈ fieldSpace L n k j) {D : Set (Fin N → ℝ)} (hD : IsOpen D) (h0D : 0 ∈ D)
    {𝒪 : Set (ℝ × ℝ)} {W : ℝ × ℝ → Edge L n k j → ComplexMatrix2}
    (hW : IsSmoothTwoParamFamily U₀ 𝒪 W) :
    ∃ (𝒪' : Set (ℝ × ℝ)) (c : ℝ × ℝ → Fin N → ℝ), IsOpen 𝒪' ∧ (0 : ℝ × ℝ) ∈ 𝒪' ∧
      ContDiffOn ℝ ∞ c 𝒪' ∧ c 0 = 0 ∧ MapsTo c 𝒪' D ∧
      (∀ p ∈ 𝒪', W p = PeriodicLattice.expTwist (formOfCoords ν (c p)) U₀) ∧
      fderiv ℝ c 0 (1, 0) = edgeFormCoords ν (curveTangent fun s : ℝ => W (s, 0)) ∧
      fderiv ℝ c 0 (0, 1) = edgeFormCoords ν (curveTangent fun t : ℝ => W (0, t)) := by
  obtain ⟨hO, h0O, hmaps, hW0, hent⟩ := hW
  have hp₀ : (restrictToPositiveEdges U₀) ∈ specialUnitaryPower (PositiveEdge L n k j) :=
    fun b => hU₀.1 b.1 (mem_univ _)
  obtain ⟨-, -, hch⟩ := (hE (PositiveEdge L n k j) (PositiveEdge L n k j)).1 _ hp₀
  have hε : 0 < Real.log (19 / 10) := Real.log_pos (by norm_num)
  obtain ⟨-, -, -, -, hdom, hlog, -⟩ := hch _ hε (by rw [Real.exp_log (by norm_num)])
  set X : ℝ × ℝ → PositiveEdge L n k j → ComplexMatrix2 :=
    fun p => restrictToPositiveEdges (W p) with hXdef
  have hX : ContDiffOn ℝ ∞ X 𝒪 :=
    contDiffOn_pi.2 fun b => contDiffOn_of_forall_entry fun r c => hent b.1 b.2 r c
  set dom := PowerExpCharts.logDomain (restrictToPositiveEdges U₀) with hdomdef
  have hO₁ : IsOpen (𝒪 ∩ X ⁻¹' dom) := hX.continuousOn.isOpen_inter_preimage hO hdom
  set Y : ℝ × ℝ → PositiveEdge L n k j → ComplexMatrix2 :=
    fun p => PowerExpCharts.logChart (restrictToPositiveEdges U₀) (X p) with hYdef
  have hY : ContDiffOn ℝ ∞ Y (𝒪 ∩ X ⁻¹' dom) :=
    hlog.comp (hX.mono inter_subset_left) fun p hp => hp.2
  have hc₁ : ContDiffOn ℝ ∞ (fun p => pauliCoords ν (Y p)) (𝒪 ∩ X ⁻¹' dom) :=
    (pauliCoords ν).contDiff.comp_contDiffOn hY
  have hUb : ∀ b : Edge L n k j, U₀ b * (U₀ b)⁻¹ = 1 := fun b =>
    Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compactGaugeGroup (hU₀.1 b (mem_univ b)))
  have hX0 : X 0 = restrictToPositiveEdges U₀ := by
    simp only [hXdef]
    exact congrArg _ hW0
  have h0₁ : (0 : ℝ × ℝ) ∈ 𝒪 ∩ X ⁻¹' dom := by
    refine ⟨h0O, fun b => ?_⟩
    rw [hX0]
    simp [restrictToPositiveEdges, hUb]
  have hlog1 : ComplexMatrix2.logSeries 1 = 0 := by simp [ComplexMatrix2.logSeries]
  have hY0 : Y 0 = 0 := by
    funext b
    simp only [hYdef, hX0, PowerExpCharts.logChart, restrictToPositiveEdges, hUb, hlog1]
    simp
  have hc0 : pauliCoords ν (Y 0) = 0 := by rw [hY0, map_zero]
  have hpt : ∀ p ∈ 𝒪 ∩ X ⁻¹' dom, ∀ b : PositiveEdge L n k j,
      Y p b ∈ ComplexMatrix2.hermitianTraceless ∧
      ComplexMatrix2.matExp (Complex.I • Y p b) = W p b.1 * (U₀ b.1)⁻¹ := by
    intro p hp b
    have hA : W p b.1 * (U₀ b.1)⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
      have h1 : U₀ b.1.opposite = (U₀ b.1)⁻¹ := hU₀.2 b.1 (mem_univ _)
      rw [← h1]
      exact ComplexMatrix2.specialUnitary.mul_mem ((hmaps hp.1).1 b.1 (mem_univ _))
        (hU₀.1 _ (mem_univ _))
    have hsp := Matrix.mem_specialUnitaryGroup_iff.1 hA
    obtain ⟨H, -, hlogH, -, hexp, -, hdet⟩ := hM.2.2.2.2.2.2.2.1 _ hsp.1 (hp.2 b)
    obtain ⟨-, hH, -⟩ := hdet hsp.2
    have hYH : Y p b = H := by
      simp only [hYdef, hXdef, PowerExpCharts.logChart, restrictToPositiveEdges, hlogH]
      rw [smul_smul, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    rw [hYH]
    exact ⟨hH, hexp⟩
  have hYdiff : HasFDerivAt Y (fderiv ℝ Y 0) (0 : ℝ × ℝ) :=
    ((hY.contDiffAt (hO₁.mem_nhds h0₁)).differentiableAt (by simp)).hasFDerivAt
  have hXdiff : HasFDerivAt X (fderiv ℝ X 0) (0 : ℝ × ℝ) :=
    ((hX.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by simp)).hasFDerivAt
  have hcd : HasFDerivAt (fun p => pauliCoords ν (Y p))
      ((pauliCoords ν).comp (fderiv ℝ Y 0)) (0 : ℝ × ℝ) :=
    (pauliCoords ν).hasFDerivAt.comp (0 : ℝ × ℝ) hYdiff
  have key : ∀ (σ : ℝ → ℝ × ℝ) (e : ℝ × ℝ), HasDerivAt σ e 0 → σ 0 = 0 →
      fderiv ℝ (fun p => pauliCoords ν (Y p)) 0 e =
        edgeFormCoords ν (curveTangent fun s : ℝ => W (σ s)) := by
    intro σ e hσ hσ0
    have hnb : σ ⁻¹' (𝒪 ∩ X ⁻¹' dom) ∈ 𝓝 (0 : ℝ) :=
      hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hO₁.mem_nhds h0₁)
    obtain ⟨I, hIS, hI⟩ := exists_interval_subset hnb
    have hXσ : HasDerivAt (fun s => X (σ s)) (fderiv ℝ X 0 e) 0 :=
      (show HasFDerivAt X (fderiv ℝ X 0) (σ 0) by rw [hσ0]; exact hXdiff).comp_hasDerivAt
        (0 : ℝ) hσ
    have hYσ : HasDerivAt (fun s => Y (σ s)) (fderiv ℝ Y 0 e) 0 :=
      (show HasFDerivAt Y (fderiv ℝ Y 0) (σ 0) by rw [hσ0]; exact hYdiff).comp_hasDerivAt
        (0 : ℝ) hσ
    have hval : ∀ b : PositiveEdge L n k j, fderiv ℝ Y 0 e b =
        restrictToPositiveEdges (curveTangent fun s : ℝ => W (σ s)) b := by
      intro b
      have hdb : DifferentiableAt ℝ (fun s => W (σ s) b.1) 0 :=
        ((hasDerivAt_pi.1 hXσ) b).differentiableAt
      obtain ⟨-, hdl, heq, -⟩ := hl.curveLog I hI (fun s => W (σ s) b.1)
        (fun s hs => (hmaps (hIS hs).1).1 b.1 (mem_univ _)) hdb
      have hW0b : W (σ 0) b.1 = U₀ b.1 := by rw [hσ0]; exact congrFun hW0 b.1
      simp only [hW0b] at hdl heq
      have h1 := (hasDerivAt_pi.1 hYσ) b
      have h2 := hdl.hasDerivAt.const_smul (1 / Complex.I)
      have h3 : (1 / Complex.I) •
          deriv (fun s => ComplexMatrix2.logSeries (W (σ s) b.1 * (U₀ b.1)⁻¹)) 0 =
          fderiv ℝ Y 0 e b := h2.unique h1
      simp only [restrictToPositiveEdges, curveTangent, extendOddly, if_pos b.2, hW0b]
      rw [← h3, one_div]
      exact heq
    have e1 : fderiv ℝ (fun p => pauliCoords ν (Y p)) 0 e = pauliCoords ν (fderiv ℝ Y 0 e) := by
      rw [hcd.fderiv]
      rfl
    rw [e1]
    exact congrArg (pauliCoords ν) (funext hval)
  refine ⟨(𝒪 ∩ X ⁻¹' dom) ∩ (fun p => pauliCoords ν (Y p)) ⁻¹' D, fun p => pauliCoords ν (Y p),
    hc₁.continuousOn.isOpen_inter_preimage hO₁ hD, ⟨h0₁, ?_⟩, hc₁.mono inter_subset_left, hc0,
    fun p hp => hp.2, ?_, key (fun s => (s, 0)) (1, 0) hasDerivAt_pair_fst rfl,
    key (fun t => (0, t)) (0, 1) hasDerivAt_pair_snd rfl⟩
  · show pauliCoords ν (Y 0) ∈ D
    rw [hc0]
    exact h0D
  · intro p hp
    refine eq_expTwist (hmaps hp.1.1) fun b hb => ?_
    have h1 : formOfCoords ν (pauliCoords ν (Y p)) b = Y p ⟨b, hb⟩ :=
      formOfCoords_pauliCoords ν (fun c => (hpt p hp.1 c).1) ⟨b, hb⟩
    rw [h1, (hpt p hp.1 ⟨b, hb⟩).2, mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compactGaugeGroup (hU₀.1 b (mem_univ b))),
      mul_one]
end ExpTwist
section ChartPullback
variable {L n k j : ℕ} [Fintype (PositiveEdge L n k j)] {N : ℕ}
  (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N)
def chartPullback (F : (Edge L n k j → ComplexMatrix2) → ℂ) (U₀ : Edge L n k j → ComplexMatrix2)
    (y : Fin N → ℝ) : ℂ :=
  F (PeriodicLattice.expTwist (formOfCoords ν y) U₀)
structure ChartPullbackData (𝒩 : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U₀ : Edge L n k j → ComplexMatrix2) (D : Set (Fin N → ℝ)) : Prop where
  isOpen : IsOpen D
  zero_mem : (0 : Fin N → ℝ) ∈ D
  mapsTo : ∀ y ∈ D, PeriodicLattice.expTwist (formOfCoords ν y) U₀ ∈ 𝒩
  contDiffOn : ContDiffOn ℝ ∞ (chartPullback ν F U₀) D
theorem contDiffAt_two_of_infty {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} (h : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ 2 f x := by
  exact_mod_cast contDiffAt_infty.1 h 2
theorem formOfCoords_zero : formOfCoords ν 0 = 0 := by
  simp [formOfCoords_eq_sum]
theorem formOfCoords_smul (t : ℝ) (y : Fin N → ℝ) :
    formOfCoords ν (t • y) = t • formOfCoords ν y := by apply _root_.YangMills.Construction.Tower.AnalyticAlongExpCurves.formOfCoords_smul <;> assumption
theorem isOpen_coordRegion_and_zero_mem (hl : LinkFacts L n k j)
    {𝒪 : Set (Edge L n k j → ComplexMatrix2)} (h : IsZeroNhd 𝒪) :
    IsOpen (coordRegion ν 𝒪) ∧ (0 : Fin N → ℝ) ∈ coordRegion ν 𝒪 := by
  obtain ⟨⟨O, hO, hEq⟩, h0⟩ := h
  refine ⟨?_, ?_⟩
  · have he : coordRegion ν 𝒪 = formOfCoords ν ⁻¹' O := by
      ext y
      simp only [coordRegion, mem_ofPred_eq, hEq, mem_inter_iff, mem_preimage]
      exact ⟨fun h => h.1, fun h => ⟨h, formOfCoords_mem ν hl y⟩⟩
    rw [he]
    exact hO.preimage (continuous_formOfCoords ν)
  · show formOfCoords ν 0 ∈ 𝒪
    rw [formOfCoords_zero]
    exact h0
omit [Fintype (PositiveEdge L n k j)] in
theorem contDiffAt_chartPullback {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (r : ChartPullbackData ν 𝒩 F U₀ D) : ContDiffAt ℝ ∞ (chartPullback ν F U₀) 0 :=
  r.contDiffOn.contDiffAt (r.isOpen.mem_nhds r.zero_mem)
theorem fderiv_chartPullback_eq_zero (hl : LinkFacts L n k j)
    {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (r : ChartPullbackData ν 𝒩 F U₀ D)
    (hg : ∀ B ∈ edgeFormSpace L n k j, leftDeriv F U₀ B = 0) :
    fderiv ℝ (chartPullback ν F U₀) 0 = 0 := by
  have hd : HasFDerivAt (chartPullback ν F U₀) (fderiv ℝ (chartPullback ν F U₀) 0)
      (0 : Fin N → ℝ) :=
    ((contDiffAt_chartPullback ν r).differentiableAt (by simp)).hasFDerivAt
  refine ContinuousLinearMap.ext fun y => ?_
  have hline : HasDerivAt (fun t : ℝ => t • y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const y
  have hd' : HasFDerivAt (chartPullback ν F U₀) (fderiv ℝ (chartPullback ν F U₀) 0)
      ((fun t : ℝ => t • y) 0) := by simpa using hd
  have h0 := hd'.comp_hasDerivAt (0 : ℝ) hline
  have h1 : HasDerivAt (fun t : ℝ => chartPullback ν F U₀ (t • y))
      (fderiv ℝ (chartPullback ν F U₀) 0 y) 0 := h0
  have h2 : (fun t : ℝ => chartPullback ν F U₀ (t • y)) = fun t : ℝ =>
      F (PeriodicLattice.expTwist (algebraMap ℝ ℂ t • formOfCoords ν y) U₀) := by
    funext t
    rw [chartPullback, formOfCoords_smul, algebraMap_smul]
  have h3 := hg _ (formOfCoords_mem ν hl y)
  simp only [leftDeriv, directionalDeriv] at h3
  rw [← h2, h1.deriv] at h3
  simpa using h3
theorem leftSecondDeriv_eq (hl : LinkFacts L n k j) {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (r : ChartPullbackData ν 𝒩 F U₀ D) (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0)
    {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) :
    leftSecondDeriv F U₀ B B' =
      fderiv ℝ (fderiv ℝ (chartPullback ν F U₀)) 0 (edgeFormCoords ν B) (edgeFormCoords ν B') := by
  set u := edgeFormCoords ν B with hu
  set u' := edgeFormCoords ν B' with hu'
  set cl : ℝ × ℝ →L[ℝ] Fin N → ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight u'
    with hcl
  have hψ : ContDiffAt ℝ 2 (chartPullback ν F U₀) (cl 0) := by
    rw [map_zero]
    exact contDiffAt_two_of_infty (contDiffAt_chartPullback ν r)
  have hcr : fderiv ℝ (chartPullback ν F U₀) (cl 0) = 0 := by
    rw [map_zero]
    exact crit
  have h := hasDerivAt_deriv_comp_of_fderiv_eq_zero hψ cl.contDiff.contDiffAt hcr
  have e1 : cl (1, 0) = u := by simp [hcl]
  have e2 : cl (0, 1) = u' := by simp [hcl]
  rw [cl.fderiv, map_zero, e1, e2] at h
  have hfun : (fun s : ℝ => deriv (fun t : ℝ =>
      F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') U₀)) 0) =
      fun s : ℝ => deriv (fun t : ℝ => chartPullback ν F U₀ (cl (s, t))) 0 := by
    funext s
    congr 1
    funext t
    rw [smul_add_smul_eq_formOfCoords ν hl hB hB', chartPullback]
    simp [hcl, hu, hu']
  show deriv (fun s : ℝ => deriv (fun t : ℝ =>
    F (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') U₀)) 0) 0 = _
  rw [hfun]
  exact h.deriv
theorem leftSecondDeriv_comm (hl : LinkFacts L n k j) {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (r : ChartPullbackData ν 𝒩 F U₀ D) (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0)
    {B B' : Edge L n k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k j)
    (hB' : B' ∈ edgeFormSpace L n k j) :
    leftSecondDeriv F U₀ B B' = leftSecondDeriv F U₀ B' B := by
  rw [leftSecondDeriv_eq ν hl r crit hB hB', leftSecondDeriv_eq ν hl r crit hB' hB]
  exact ((contDiffAt_two_of_infty (contDiffAt_chartPullback ν r)).isSymmSndFDerivAt
    (by simp)) _ _
variable [Nonempty (PositiveEdge L n k j)]
theorem mixed_partials_of_family (hl : LinkFacts L n k j)
    (hE : PowerExpCharts.ExpChartsStatement)
    (hM : ComplexMatrix2.ExpLogEstimates) {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (hU₀ : U₀ ∈ fieldSpace L n k j) (r : ChartPullbackData ν 𝒩 F U₀ D)
    (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0) {𝒪 : Set (ℝ × ℝ)}
    {W : ℝ × ℝ → Edge L n k j → ComplexMatrix2} (hW : IsSmoothTwoParamFamily U₀ 𝒪 W) :
    ∃ 𝒪' : Set (ℝ × ℝ), IsOpen 𝒪' ∧ ((0 : ℝ), (0 : ℝ)) ∈ 𝒪' ∧ MapsTo W 𝒪' 𝒩 ∧
      ContDiffOn ℝ ∞ (fun p => F (W p)) 𝒪' ∧
      HasDerivAt (fun s : ℝ => deriv (fun t : ℝ => F (W (s, t))) 0)
        (leftSecondDeriv F U₀ (curveTangent fun s : ℝ => W (s, 0))
          (curveTangent fun t : ℝ => W (0, t))) 0 ∧
      HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => F (W (s, t))) 0)
        (leftSecondDeriv F U₀ (curveTangent fun s : ℝ => W (s, 0))
          (curveTangent fun t : ℝ => W (0, t))) 0 := by
  obtain ⟨𝒪', c, hO', h0, hc, hc0, hcD, hWc, h1, h2⟩ :=
    exists_coords_of_family ν hl hE hM hU₀ r.isOpen r.zero_mem hW
  have hFW : ∀ p ∈ 𝒪', F (W p) = chartPullback ν F U₀ (c p) := fun p hp => by
    rw [hWc p hp]; rfl
  have hsm : ContDiffOn ℝ ∞ (fun p => chartPullback ν F U₀ (c p)) 𝒪' :=
    r.contDiffOn.comp hc hcD
  refine ⟨𝒪', hO', h0, fun p hp => ?_, hsm.congr hFW, ?_⟩
  · rw [hWc p hp]
    exact r.mapsTo _ (hcD hp)
  have hgerm : (fun p => F (W p)) =ᶠ[𝓝 0] fun p => chartPullback ν F U₀ (c p) :=
    Filter.eventuallyEq_of_mem (hO'.mem_nhds h0) hFW
  have hψ : ContDiffAt ℝ 2 (chartPullback ν F U₀) (c 0) := by
    rw [hc0]
    exact contDiffAt_two_of_infty (contDiffAt_chartPullback ν r)
  have hcd : ContDiffAt ℝ 2 c 0 := contDiffAt_two_of_infty (hc.contDiffAt (hO'.mem_nhds h0))
  have hcr : fderiv ℝ (chartPullback ν F U₀) (c 0) = 0 := by
    rw [hc0]
    exact crit
  have m1 := hasDerivAt_deriv_comp_of_fderiv_eq_zero hψ hcd hcr
  have m2 := hasDerivAt_deriv_comp_swap_of_fderiv_eq_zero hψ hcd hcr
  have hT1 := curveTangent_family_mem hl hW hasDerivAt_pair_fst rfl
  have hT2 := curveTangent_family_mem hl hW hasDerivAt_pair_snd rfl
  rw [h1, h2, hc0, ← leftSecondDeriv_eq ν hl r crit hT1 hT2] at m1 m2
  exact ⟨m1.congr_of_eventuallyEq (eventuallyEq_deriv_slice_snd hgerm),
    m2.congr_of_eventuallyEq (eventuallyEq_deriv_slice_fst hgerm)⟩
end ChartPullback
section MainRequirements
variable {L n k j : ℕ}
theorem entrywiseDifferentiableCurves : EntrywiseDifferentiableCurves L n k j :=
  fun _ _ h => ⟨h.1, h.2.1, fun b hb t ht =>
    (differentiableAt_of_forall_entry fun r c => h.2.2 b hb r c t ht).differentiableWithinAt⟩
theorem edgeFormPairing_zero (B : Edge L n k j → ComplexMatrix2) : edgeFormPairing 0 B = 0 := by
  simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, ComplexMatrix2.halfTrace,
    ComplexMatrix2.fullTrace]
theorem edgeFormPairing_pauliBasisForm (X : Edge L n k j → ComplexMatrix2)
    (b : PositiveEdge L n k j) (a : Fin 3) :
    edgeFormPairing X (pauliBasisForm b a) =
      ComplexMatrix2.halfTrace (X b.1 * ComplexMatrix2.pauliFamily a) := by apply _root_.YangMills.DeltaSharedProofs.p500976 <;> assumption
theorem isSmoothTwoParamFamily_expTwist_curve (hl : LinkFacts L n k j)
    {U₀ : Edge L n k j → ComplexMatrix2}
    (hU₀ : U₀ ∈ fieldSpace L n k j) {I : Set ℝ} {γ : ℝ → Edge L n k j → ComplexMatrix2}
    (hγ : IsSmoothCurveAt U₀ I γ) {B' : Edge L n k j → ComplexMatrix2}
    (hB' : B' ∈ edgeFormSpace L n k j) :
    IsSmoothTwoParamFamily U₀ (univ ×ˢ I)
      (fun p : ℝ × ℝ => PeriodicLattice.expTwist ((p.1 : ℂ) • B') (γ p.2)) := by
  obtain ⟨hI, hγm, hγ0, hent⟩ := hγ
  refine ⟨isOpen_univ.prod hI.1, ⟨mem_univ _, hI.2.2⟩, fun p hp => ?_, ?_, fun b hb r c => ?_⟩
  · refine expTwist_mem hl ?_ (hγm hp.2)
    rw [ofReal_smul_eq_smul]
    exact Submodule.smul_mem _ _ hB'
  · simp only [Complex.ofReal_zero, zero_smul, hγ0]
    exact expTwist_zero hU₀
  · have hexp : ContDiff ℝ ∞
        (fun p : ℝ × ℝ => ComplexMatrix2.matExp ((p.1 : ℂ) • (Complex.I • B' b))) :=
      contDiff_matExp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_const)
    have hcurve : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => γ p.2 b) (univ ×ˢ I) :=
      contDiffOn_of_forall_entry fun r c =>
        (hent b hb r c).comp contDiff_snd.contDiffOn fun p hp => hp.2
    have hmat := hexp.contDiffOn.mul hcurve
    refine ((entryCLM r c).contDiff.comp_contDiffOn hmat).congr fun p _ => ?_
    show (PeriodicLattice.expTwist ((p.1 : ℂ) • B') (γ p.2)) b r c = _
    rw [expTwist_of_isPositivelyOriented _ _ hb]
    simp only [Pi.smul_apply, smul_comm Complex.I (p.1 : ℂ) (B' b)]
    rfl
theorem isDifferentiableFieldCurve_expTwist (hl : LinkFacts L n k j)
    {A U : Edge L n k j → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n k j) (hU : U ∈ fieldSpace L n k j) :
    IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup univ
      (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U) := by
  refine ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩, fun t _ => ?_, fun b hb => ?_⟩
  · refine expTwist_mem hl ?_ hU
    rw [ofReal_smul_eq_smul]
    exact Submodule.smul_mem _ _ hA
  · have h : ContDiff ℝ ∞
        (fun t : ℝ => ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • A b)) * U b) :=
      (contDiff_matExp.comp (Complex.ofRealCLM.contDiff.smul contDiff_const)).mul contDiff_const
    have he : (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • A) U b) =
        fun t : ℝ => ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • A b)) * U b := by
      funext t
      rw [expTwist_of_isPositivelyOriented _ _ hb]
      simp only [Pi.smul_apply, smul_comm Complex.I (t : ℂ) (A b)]
    rw [he]
    exact (h.differentiable (by simp)).differentiableOn
variable [Fintype (PositiveEdge L n k j)] [Nonempty (PositiveEdge L n k j)] {N : ℕ}
  (ν : PositiveEdge L n k j × Fin 3 ≃ Fin N)
theorem mixedPartialsEqHessian (hl : LinkFacts L n k j)
    (hE : PowerExpCharts.ExpChartsStatement)
    (hM : ComplexMatrix2.ExpLogEstimates) {𝒩 : Set (Edge L n k j → ComplexMatrix2)}
    {F : (Edge L n k j → ComplexMatrix2) → ℂ} {U₀ : Edge L n k j → ComplexMatrix2}
    {D : Set (Fin N → ℝ)}
    (hU₀ : U₀ ∈ fieldSpace L n k j) (r : ChartPullbackData ν 𝒩 F U₀ D)
    (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0) : MixedPartialsEqHessian 𝒩 F U₀ := by
  intro 𝒪 W hW
  obtain ⟨𝒪', hO', h0, hm, hs, m1, m2⟩ := mixed_partials_of_family ν hl hE hM hU₀ r crit hW
  exact ⟨⟨𝒪', hO', h0, hm, hs⟩, m1.deriv, m2.deriv⟩
theorem gradientDerivAlongCurves (hl : LinkFacts L n k j)
    (hE : PowerExpCharts.ExpChartsStatement) (hM : ComplexMatrix2.ExpLogEstimates)
    {𝒩 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℂ}
    {U₀ : Edge L n k j → ComplexMatrix2} {D : Set (Fin N → ℝ)}
    (hU₀ : U₀ ∈ fieldSpace L n k j) (r : ChartPullbackData ν 𝒩 F U₀ D)
    (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0) (hreal : ∀ V ∈ 𝒩, (F V).im = 0)
    (hG : ∀ V ∈ 𝒩, HasLeftGradientAt 𝒩 F V) : GradientDerivAlongCurves 𝒩 F U₀ := by
  intro I γ hγ
  have hI := hγ.1
  have hγm := hγ.2.1
  have hγ0 := hγ.2.2.1
  have hInb : I ∈ 𝓝 (0 : ℝ) := hI.1.mem_nhds hI.2.2
  have hfin : ∀ B : Edge L n k j → ComplexMatrix2, HasFiniteSupp (restrictToPositiveEdges B) :=
    fun _ => Set.toFinite _
  have hT : curveTangent γ ∈ edgeFormSpace L n k j := by
    refine curveTangent_mem hl hI hγm fun b hb => differentiableAt_of_forall_entry fun r c => ?_
    exact ((hγ.2.2.2 b hb r c).contDiffAt hInb).differentiableAt (by simp)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ 𝒩 := by
    obtain ⟨𝒪', hO', h0, hm, -⟩ := mixed_partials_of_family ν hl hE hM hU₀ r crit
      (isSmoothTwoParamFamily_expTwist_curve hl hU₀ hγ (Submodule.zero_mem _))
    have ht : Tendsto (fun t : ℝ => ((0, t) : ℝ × ℝ)) (𝓝 0) (𝓝 (0, 0)) :=
      hasDerivAt_pair_snd.continuousAt.tendsto
    filter_upwards [ht.eventually (hO'.mem_nhds h0), hInb] with t h1 h2
    have h3 := hm h1
    simp only [Complex.ofReal_zero, zero_smul] at h3
    rwa [expTwist_zero (hγm h2)] at h3
  have key : ∀ B' ∈ edgeFormSpace L n k j,
      HasDerivAt (fun t => edgeFormPairing (leftGradient 𝒩 F (γ t)) B')
        (leftSecondDeriv F U₀ (curveTangent γ) B') 0 := by
    intro B' hB'
    obtain ⟨-, -, -, -, -, -, m2⟩ := mixed_partials_of_family ν hl hE hM hU₀ r crit
      (isSmoothTwoParamFamily_expTwist_curve hl hU₀ hγ hB')
    have t1 : (curveTangent fun s : ℝ =>
        PeriodicLattice.expTwist ((s : ℂ) • B') (γ 0)) = B' := by
      rw [hγ0]
      exact curveTangent_expTwist_smul hl hB' hU₀
    have t2 : (curveTangent fun t : ℝ =>
        PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B') (γ t)) = curveTangent γ := by
      refine curveTangent_congr ?_
      filter_upwards [hInb] with t ht
      simp only [Complex.ofReal_zero, zero_smul]
      exact expTwist_zero (hγm ht)
    have m2' : HasDerivAt
        (fun t : ℝ => deriv (fun s : ℝ =>
          F (PeriodicLattice.expTwist ((s : ℂ) • B') (γ t))) 0)
        (leftSecondDeriv F U₀
          (curveTangent fun s : ℝ => PeriodicLattice.expTwist ((s : ℂ) • B') (γ 0))
          (curveTangent fun t : ℝ =>
            PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B') (γ t))) 0 := m2
    rw [t1, t2] at m2'
    rw [leftSecondDeriv_comm ν hl r crit hT hB']
    refine m2'.congr_of_eventuallyEq ?_
    filter_upwards [hnear] with t ht
    exact (hG _ ht).2.1.2.2 B' hB' (hfin B')
  have hform : ∀ V ∈ 𝒩, leftGradient 𝒩 F V ∈ edgeFormSpace L n k j := fun V hV =>
    (hG V hV).2.1.2.1 hreal
  have hcoef : ∀ (b : PositiveEdge L n k j) (a : Fin 3),
      HasDerivAt (fun t => pauliCoeff a (leftGradient 𝒩 F (γ t) b.1))
        (leftSecondDeriv F U₀ (curveTangent γ) (pauliBasisForm b a)).re 0 := by
    intro b a
    have h := key _ (pauliBasisForm_mem hl b a)
    have hev : (fun t => edgeFormPairing (leftGradient 𝒩 F (γ t)) (pauliBasisForm b a)) =ᶠ[𝓝 0]
        fun t => ((pauliCoeff a (leftGradient 𝒩 F (γ t) b.1) : ℝ) : ℂ) := by
      filter_upwards [hnear] with t ht
      rw [edgeFormPairing_pauliBasisForm]
      exact halfTrace_mul_pauliFamily_eq_ofReal ((hform _ ht).1 b.1 b.2) a
    have h' := h.congr_of_eventuallyEq hev.symm
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h'
    simpa [Function.comp_def] using h2
  set yD : Fin N → ℝ := fun i =>
    (leftSecondDeriv F U₀ (curveTangent γ)
      (pauliBasisForm (ν.symm i).1 (ν.symm i).2)).re with hyD
  have hDf : formOfCoords ν yD ∈ edgeFormSpace L n k j := formOfCoords_mem ν hl yD
  have hDpos : ∀ b : PositiveEdge L n k j,
      HasDerivAt (fun t => leftGradient 𝒩 F (γ t) b.1) (formOfCoords ν yD b.1) 0 := by
    intro b
    have hs := HasDerivAt.fun_sum (u := Finset.univ) fun (a : Fin 3) (_ : a ∈ Finset.univ) =>
      (hcoef b a).smul_const (ComplexMatrix2.pauliFamily a)
    have hval : formOfCoords ν yD b.1 = ∑ a,
        (leftSecondDeriv F U₀ (curveTangent γ) (pauliBasisForm b a)).re •
          ComplexMatrix2.pauliFamily a := by
      simp only [formOfCoords_apply, hyD, Equiv.symm_apply_apply]
    rw [hval]
    refine hs.congr_of_eventuallyEq ?_
    filter_upwards [hnear] with t ht
    exact (sum_pauliCoeff_smul ((hform _ ht).1 b.1 b.2)).symm
  have hPair : PairsAsHessian F U₀ (curveTangent γ) (formOfCoords ν yD) := by
    intro B' hB'
    have e : ∀ X : Edge L n k j → ComplexMatrix2, edgeFormPairing X B' =
        ∑ b : PositiveEdge L n k j, halfTraceMulCLM (B' b.1) (X b.1) := fun X =>
      finsum_eq_sum_of_fintype _
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      fun (b : PositiveEdge L n k j) (_ : b ∈ Finset.univ) =>
        (halfTraceMulCLM (B' b.1)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hDpos b)
    have h1 : HasDerivAt (fun t => edgeFormPairing (leftGradient 𝒩 F (γ t)) B')
        (edgeFormPairing (formOfCoords ν yD) B') 0 := by
      simp only [e]
      exact hsum
    exact h1.unique (key B' hB')
  refine ⟨hnear.mono fun t ht => ⟨ht, hG _ ht⟩, key, formOfCoords ν yD, hDf, fun b => ?_,
    hPair, fun D' hD' hp => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · exact hDpos ⟨b, hb⟩
    · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
      have h1 := (hDpos ⟨b.opposite, hr⟩).neg
      have h2 : formOfCoords ν yD b = -formOfCoords ν yD b.opposite := by
        rw [hDf.2 b, neg_neg]
      rw [h2]
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with t ht
      have h3 : leftGradient 𝒩 F (γ t) b.opposite = -leftGradient 𝒩 F (γ t) b :=
        (hform _ ht).2 b
      show leftGradient 𝒩 F (γ t) b = -leftGradient 𝒩 F (γ t) b.opposite
      rw [h3, neg_neg]
  · refine edgeForm_ext hD' hDf fun b hb => ?_
    have hc : ∀ a, pauliCoeff a (D' b) = pauliCoeff a (formOfCoords ν yD b) := by
      intro a
      have h1 := hp _ (pauliBasisForm_mem hl ⟨b, hb⟩ a)
      have h2 := hPair _ (pauliBasisForm_mem hl ⟨b, hb⟩ a)
      rw [edgeFormPairing_pauliBasisForm] at h1 h2
      rw [pauliCoeff_apply, pauliCoeff_apply]
      exact congrArg Complex.re (h1.trans h2.symm)
    calc D' b = ∑ a, pauliCoeff a (D' b) • ComplexMatrix2.pauliFamily a :=
          (sum_pauliCoeff_smul (hD'.1 b hb)).symm
      _ = ∑ a, pauliCoeff a (formOfCoords ν yD b) • ComplexMatrix2.pauliFamily a := by
          simp only [hc]
      _ = formOfCoords ν yD b := sum_pauliCoeff_smul (hDf.1 b hb)
theorem hessianOfComp {j' : ℕ} (hT : AnalyticNearField.CompositionAndExpTwist)
    (hN : AnalyticDifferentials.AnalyticMapsDifferentiable) (hF : LeftChartFacts.HoldEverywhere)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k) (hj' : j' ≤ k)
    (hl : LinkFacts L n k j) (hl' : LinkFacts L n k j')
    (hE : PowerExpCharts.ExpChartsStatement) (hM : ComplexMatrix2.ExpLogEstimates)
    [Fintype (PositiveEdge L n k j')] {N' : ℕ}
    (ν' : PositiveEdge L n k j' × Fin 3 ≃ Fin N')
    {𝒩 : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → ℂ}
    {U₀ : Edge L n k j → ComplexMatrix2} {D : Set (Fin N → ℝ)}
    (hU₀ : U₀ ∈ fieldSpace L n k j) (r : ChartPullbackData ν 𝒩 F U₀ D)
    (crit : fderiv ℝ (chartPullback ν F U₀) 0 = 0) : HessianOfComp j' F U₀ := by
  intro 𝒲 𝔭 U hU h𝔭 hpU B hB B' hB'
  have hUc : U ∈ fieldSpace L n k j' := h𝔭.1.1 hU
  obtain ⟨𝒪₀, h𝒪₀, hexp, hsm⟩ := ((hT L n k j' j j hL hn hj' hj hj).2 U 𝒲 hUc hU).2 𝔭 h𝔭
  obtain ⟨hDo, h0D⟩ := isOpen_coordRegion_and_zero_mem ν' hl' h𝒪₀
  set cl : ℝ × ℝ →L[ℝ] Fin N' → ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (edgeFormCoords ν' B) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (edgeFormCoords ν' B') with hcldef
  have hcl : ∀ p : ℝ × ℝ, (p.1 : ℂ) • B + (p.2 : ℂ) • B' = formOfCoords ν' (cl p) := by
    intro p
    rw [smul_add_smul_eq_formOfCoords ν' hl' hB hB']
    simp [hcldef]
  have hW : IsSmoothTwoParamFamily U₀ (cl ⁻¹' coordRegion ν' 𝒪₀)
      (fun p : ℝ × ℝ => 𝔭 (PeriodicLattice.expTwist ((p.1 : ℂ) • B + (p.2 : ℂ) • B') U)) := by
    refine ⟨hDo.preimage cl.continuous, ?_, fun p hp => ?_, ?_, fun b hb r c => ?_⟩
    · show cl 0 ∈ coordRegion ν' 𝒪₀
      rw [map_zero]
      exact h0D
    · have h1 := hexp _ hp
      simp only
      rw [hcl]
      exact h𝔭.2.1 h1
    · simp only [Complex.ofReal_zero, zero_smul, add_zero]
      rw [expTwist_zero hUc]
      exact hpU
    · refine ((hsm N' ν' b r c).2.comp cl.contDiff.contDiffOn fun p hp => hp).congr fun p _ => ?_
      simp only [hcl, Function.comp_def]
  obtain ⟨-, -, -, -, -, m1, -⟩ := mixed_partials_of_family ν hl hE hM hU₀ r crit hW
  have hdiff : IsDifferentiableFieldMap 𝒲 𝔭 :=
    ((hN L n k j' j hL hn hj' hj 𝒲 h𝔭.1).2.1 𝔭 h𝔭).2.1
  have htan : ∀ C ∈ edgeFormSpace L n k j',
      (curveTangent fun s : ℝ => 𝔭 (PeriodicLattice.expTwist ((s : ℂ) • C) U)) =
        leftDifferential 𝔭 U C := by
    intro C hC
    have h := (((hF L k j' j j hL hj' hj hj).2.1 n hn).2.1.1 𝒲 𝔭 hdiff U hU) univ _
      (isDifferentiableFieldCurve_expTwist hl' hC hUc) (by
        simp only [Complex.ofReal_zero, zero_smul]
        exact expTwist_zero hUc)
    rw [curveTangent_expTwist_smul hl' hC hUc] at h
    exact h.2
  have t1 : (curveTangent fun s : ℝ =>
      𝔭 (PeriodicLattice.expTwist ((s : ℂ) • B + ((0 : ℝ) : ℂ) • B') U)) =
        leftDifferential 𝔭 U B := by
    simp only [Complex.ofReal_zero, zero_smul, add_zero]
    exact htan B hB
  have t2 : (curveTangent fun t : ℝ =>
      𝔭 (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B + (t : ℂ) • B') U)) =
        leftDifferential 𝔭 U B' := by
    simp only [Complex.ofReal_zero, zero_smul, zero_add]
    exact htan B' hB'
  have m1' : HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      F (𝔭 (PeriodicLattice.expTwist ((s : ℂ) • B + (t : ℂ) • B') U))) 0)
      (leftSecondDeriv F U₀
        (curveTangent fun s : ℝ =>
          𝔭 (PeriodicLattice.expTwist ((s : ℂ) • B + ((0 : ℝ) : ℂ) • B') U))
        (curveTangent fun t : ℝ =>
          𝔭 (PeriodicLattice.expTwist (((0 : ℝ) : ℂ) • B + (t : ℂ) • B') U))) 0 := m1
  rw [t1, t2] at m1'
  exact m1'.deriv
end MainRequirements
theorem positiveEdge_nonempty (L n k j : ℕ) : Nonempty (PositiveEdge L n k j) := by apply _root_.YangMills.Construction.Tower.IdentityChart.nonempty_positiveEdge <;> assumption
theorem hessianAtCriticalPoint (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hT : AnalyticNearField.CompositionAndExpTwist)
    (hN : AnalyticDifferentials.AnalyticMapsDifferentiable)
    (hC : LeftChartFields.Claim)
    (hF : LeftChartFacts.HoldEverywhere)
    (hE : PowerExpCharts.ExpChartsStatement)
    (hM : ComplexMatrix2.ExpLogEstimates) :
    HessianAtCriticalPoint := by
  intro L n k j j' hL hn hj hj'
  refine ⟨entrywiseDifferentiableCurves, entrywiseDifferentiableCurves, fun 𝒩 F U₀ hcp => ?_⟩
  have linkFacts : ∀ i, i ≤ k → LinkFacts L n k i := fun i hi =>
    ⟨fun b hb => not_opposite_isPositivelyOriented hA hL hn hi b hb,
      ((hC.2.2 L k i hL hi).1 n hn).1,
      ((hC.2.2 L k i hL hi).1 n hn).2.1, fun I hI => (hC.1 I hI).1⟩
  have hl := linkFacts j hj
  have hl' := linkFacts j' hj'
  have : Finite (PositiveEdge L n k j) := hl.tangentEq.1
  have : Finite (PositiveEdge L n k j') := hl'.tangentEq.1
  have : Fintype (PositiveEdge L n k j) := Fintype.ofFinite _
  have : Fintype (PositiveEdge L n k j') := Fintype.ofFinite _
  have : Nonempty (PositiveEdge L n k j) := positiveEdge_nonempty L n k j
  have ν := Fintype.equivFin (PositiveEdge L n k j × Fin 3)
  have ν' := Fintype.equivFin (PositiveEdge L n k j' × Fin 3)
  obtain ⟨hU₀, hmem, hra, hreal, hzero⟩ := hcp
  have hG : ∀ V ∈ 𝒩, HasLeftGradientAt 𝒩 F V := fun V hV =>
    (((hN L n k j j hL hn hj hj 𝒩 hra.1).1 F hra).2.2.2 V hV).1
  obtain ⟨𝒪, h𝒪, hexp, hsm⟩ := ((hT L n k j j j hL hn hj hj hj).2 U₀ 𝒩 hU₀ hmem).1 F hra
  obtain ⟨hDo, h0⟩ := isOpen_coordRegion_and_zero_mem ν hl h𝒪
  have r : ChartPullbackData ν 𝒩 F U₀ (coordRegion ν 𝒪) :=
    ⟨hDo, h0, fun y hy => hexp _ hy, (hsm _ ν).2⟩
  have crit := fderiv_chartPullback_eq_zero ν hl r fun B hB => by
    have h := (hG U₀ hmem).2.1.2.2 B hB (Set.toFinite _)
    rw [← h, hzero, edgeFormPairing_zero]
  exact ⟨mixedPartialsEqHessian ν hl hE hM hU₀ r crit,
    gradientDerivAlongCurves ν hl hE hM hU₀ r crit hreal hG,
    hessianOfComp ν hT hN hF hL hn hj hj' hl hl' hE hM ν' hU₀ r crit⟩
end Tower.CriticalSecondDeriv
end YangMills.Construction
end
