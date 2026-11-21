import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Matrices.UnimodularArgumentHolomorphy
import Mathlib
open Filter Set
open scoped Matrix.Norms.L2Operator NNReal Topology
noncomputable section
namespace YangMills.Construction.Matrices.UnimodularArguments
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy
private theorem exists_coordMonomial {N : ℕ} (m : Fin N → ℕ) (n : ℕ) (hm : ∑ j, m j = n) :
    ∃ L : ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexCoordinates N) ℂ,
      ‖L‖ ≤ 1 ∧ ∀ y : ComplexCoordinates N, L (fun _ => y) = ∏ j, y j ^ m j := by
  subst hm
  let idx : Fin (∑ j, m j) → Fin N := fun i => (finSigmaFinEquiv.symm i).1
  refine ⟨(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (∑ j, m j)) ℂ).compContinuousLinearMap
      fun i => ContinuousLinearMap.proj (idx i), ?_, fun y => ?_⟩
  · refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun y => ?_
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_le_pi_norm (y i) (idx i)
  · simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply]
    calc ∏ i, y (idx i) = ∏ s : (Σ j, Fin (m j)), y s.1 :=
          (Fintype.prod_equiv finSigmaFinEquiv _ _ fun s => by simp [idx]).symm
      _ = ∏ j, ∏ _ : Fin (m j), y j := Fintype.prod_sigma ..
      _ = ∏ j, y j ^ m j := by simp
private def coordMonomial {N : ℕ} (n : ℕ) (m : Fin N → ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ComplexCoordinates N) ℂ :=
  open Classical in
  if h : ∑ j, m j = n then Classical.choose (exists_coordMonomial m n h) else 0
private theorem coordMonomial_norm_le {N : ℕ} (n : ℕ) (m : Fin N → ℕ) :
    ‖coordMonomial n m‖ ≤ 1 := by
  unfold coordMonomial
  split_ifs with h
  · exact (Classical.choose_spec (exists_coordMonomial m n h)).1
  · simp
private theorem coordMonomial_apply_diag {N : ℕ} {n : ℕ} {m : Fin N → ℕ} (h : ∑ j, m j = n)
    (y : ComplexCoordinates N) : coordMonomial n m (fun _ => y) = ∏ j, y j ^ m j := by
  unfold coordMonomial
  rw [dif_pos h]
  exact (Classical.choose_spec (exists_coordMonomial m n h)).2 y
private def coeffSeries {N N' : ℕ} (c : (Fin N → ℕ) → ComplexCoordinates N') :
    FormalMultilinearSeries ℂ (ComplexCoordinates N) (ComplexCoordinates N') := fun n =>
  ∑ m ∈ Finset.piAntidiag Finset.univ n, (coordMonomial n m).smulRight (c m)
private theorem coeffSeries_apply_diag {N N' : ℕ} (c : (Fin N → ℕ) → ComplexCoordinates N')
    (n : ℕ) (y : ComplexCoordinates N) :
    coeffSeries c n (fun _ => y) =
      ∑ m ∈ Finset.piAntidiag Finset.univ n, (∏ j, y j ^ m j) • c m := by
  unfold coeffSeries
  rw [sum_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ContinuousMultilinearMap.smulRight_apply,
    coordMonomial_apply_diag (Finset.mem_piAntidiag.mp hm).1]
private theorem coeffSeries_norm_le {N N' : ℕ} (c : (Fin N → ℕ) → ComplexCoordinates N')
    (n : ℕ) : ‖coeffSeries c n‖ ≤ ∑ m ∈ Finset.piAntidiag Finset.univ n, ‖c m‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [ContinuousMultilinearMap.norm_smulRight]
  exact mul_le_of_le_one_left (norm_nonneg _) (coordMonomial_norm_le n m)
private theorem analyticAt_of_hasPowerSeriesSumOn {N N' : ℕ}
    {f : ComplexCoordinates N → ComplexCoordinates N'} {a : ComplexCoordinates N} {ρ : ℝ}
    (hρ : 0 < ρ) (h : HasPowerSeriesSumOn f a ρ) : AnalyticAt ℂ f a := by
  obtain ⟨c, hsum, hconv⟩ := h
  let r : ℝ≥0 := ⟨ρ / 2, by positivity⟩
  have hr0 : (0 : ℝ) < r := by change 0 < ρ / 2; positivity
  have hrρ : (r : ℝ) < ρ := by change ρ / 2 < ρ; linarith
  let z₀ : ComplexCoordinates N := a + fun _ => (r : ℂ)
  have hz₀ : z₀ ∈ closedPolydisk a r := by
    intro j
    simp [z₀]
  have hsummable := (hconv r hrρ).1 z₀ hz₀
  have hterm : ∀ m : Fin N → ℕ, ‖monomialTerm c a z₀ m‖ = (r : ℝ) ^ (∑ j, m j) * ‖c m‖ := by
    intro m
    simp [monomialTerm, z₀, norm_smul, Finset.prod_pow_eq_pow_sum]
  have hpow : HasFPowerSeriesOnBall f (coeffSeries c) a (r : ENNReal) := by
    refine ⟨?_, by exact_mod_cast hr0, ?_⟩
    · refine (coeffSeries c).le_radius_of_bound (∑' m, ‖monomialTerm c a z₀ m‖) fun n => ?_
      calc ‖coeffSeries c n‖ * (r : ℝ) ^ n
          ≤ (∑ m ∈ Finset.piAntidiag Finset.univ n, ‖c m‖) * (r : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (coeffSeries_norm_le c n) (by positivity)
        _ = ∑ m ∈ Finset.piAntidiag Finset.univ n, ‖monomialTerm c a z₀ m‖ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [hterm, (Finset.mem_piAntidiag.mp hm).1, mul_comm]
        _ ≤ _ := hsummable.sum_le_tsum _ fun _ _ => norm_nonneg _
    · intro y hy
      have hyn : ‖y‖ < r := by simpa using hy
      have hz : a + y ∈ openPolydisk a ρ := by
        intro j
        simpa using ((norm_le_pi_norm y j).trans_lt hyn).trans hrρ
      have hs : HasSum (fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m) (f (a + y)) := by
        have hterms : monomialTerm c a (a + y) =
            fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m := by
          funext m
          simp [monomialTerm]
        rw [← hterms]
        exact hsum (a + y) hz
      have hfib := (Equiv.sigmaFiberEquiv fun m : Fin N → ℕ => ∑ j, m j).hasSum_iff.mpr hs
      refine hfib.sigma fun n => ?_
      rw [coeffSeries_apply_diag]
      have hfin := Finset.hasSum (Finset.piAntidiag Finset.univ n)
        fun m : Fin N → ℕ => (∏ j, y j ^ m j) • c m
      exact (Equiv.subtypeEquivRight fun m : Fin N → ℕ => by simp).symm.hasSum_iff.mpr hfin
  exact hpow.analyticAt
private theorem differentiableOn_of_isHolomorphicIn
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (h : ComplexCoordinates.IsHolomorphicIn O f) : DifferentiableOn ℂ f O := by
  intro b hb
  obtain ⟨L, hL⟩ := ((hH.1 N O h.1).1 N' f h).2.2.1 b hb
  exact (hasFDerivAt_of_restrictScalars ℝ hL rfl).differentiableAt.differentiableWithinAt
abbrev _root_.YangMills.SharedProofs.p33060 := @differentiableOn_of_isHolomorphicIn
private theorem analyticAt_of_isHolomorphicIn
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (h : ComplexCoordinates.IsHolomorphicIn O f) {a : ComplexCoordinates N} (ha : a ∈ O) :
    AnalyticAt ℂ f a := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h.1 a ha
  have hsub : closedPolydisk a (ε / 2) ⊆ O := fun z hz => hball <| by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr hz) (by linarith)
  exact analyticAt_of_hasPowerSeriesSumOn (by positivity)
    (((hH.1 N O h.1).1 N' f h).1 a ha _ (by positivity) hsub)
private theorem isHolomorphicIn_of_differentiableOn {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hO : IsOpen O) (h : DifferentiableOn ℂ f O) :
    ComplexCoordinates.IsHolomorphicIn O f := by
  refine ⟨hO, h.continuousOn, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • stdBasisVector j := by fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • stdBasisVector j ∈ O :=
    hline.continuousAt.eventually_mem (hO.mem_nhds (by simpa using ha))
  filter_upwards [hnear] with ζ hζ
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => a + ζ • stdBasisVector j) ζ := by fun_prop
  exact (h.differentiableAt (hO.mem_nhds hζ)).comp ζ hd
abbrev _root_.YangMills.SharedProofs.p1029 := @isHolomorphicIn_of_differentiableOn
private def linearCoordEquiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {N : ℕ} (e : E ≃ ComplexCoordinates N)
    (hadd : ∀ x y, e (x + y) = e x + e y) (hsmul : ∀ (t : ℂ) x, e (t • x) = t • e x) :
    E ≃L[ℂ] ComplexCoordinates N :=
  LinearEquiv.toContinuousLinearEquiv { e with map_add' := hadd, map_smul' := hsmul }
private def matrixCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  linearCoordEquiv matrixEquiv (fun _ _ => rfl) fun _ _ => rfl
private def matrixPiCLE {P : Type} [Fintype P] {k : ℕ} (ν : P ≃ Fin k) :
    (P → ComplexMatrix2) ≃L[ℂ] ComplexCoordinates
      (productDim fun _ : Fin k => ComplexCoordinates.Component.matrix) :=
  linearCoordEquiv (GroupLieProduct.matrixPiEquiv ν)
    (fun _ _ => by funext _; rfl) fun _ _ => by funext _; rfl
private theorem differentiableOn_of_coords
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {N N' : ℕ} (e : E ≃L[ℂ] ComplexCoordinates N)
    (e' : E' ≃L[ℂ] ComplexCoordinates N') {O : Set E} {f : E → E'}
    (h : ComplexCoordinates.IsHolomorphicIn (e '' O) (e' ∘ f ∘ e.symm)) :
    DifferentiableOn ℂ f O := by
  intro x hx
  have hg := differentiableOn_of_isHolomorphicIn hH h
  have h₁ : DifferentiableAt ℂ (e' ∘ f ∘ e.symm) (e x) :=
    (hg (e x) ⟨x, hx, rfl⟩).differentiableAt (h.1.mem_nhds ⟨x, hx, rfl⟩)
  have h₂ : DifferentiableAt ℂ (e'.symm ∘ (e' ∘ f ∘ e.symm) ∘ e) x :=
    e'.symm.differentiableAt.comp x (h₁.comp x e.differentiableAt)
  have h₃ : e'.symm ∘ (e' ∘ f ∘ e.symm) ∘ e = f := by
    funext y
    simp
  rw [h₃] at h₂
  exact h₂.differentiableWithinAt
private theorem analyticAt_of_coords
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {N N' : ℕ} (e : E ≃L[ℂ] ComplexCoordinates N)
    (e' : E' ≃L[ℂ] ComplexCoordinates N') {O : Set E} {f : E → E'}
    (h : ComplexCoordinates.IsHolomorphicIn (e '' O) (e' ∘ f ∘ e.symm)) {x : E} (hx : x ∈ O) :
    AnalyticAt ℂ f x := by
  have h₁ : AnalyticAt ℂ (e' ∘ f ∘ e.symm) (e x) :=
    analyticAt_of_isHolomorphicIn hH h ⟨x, hx, rfl⟩
  have he : AnalyticAt ℂ e x := (e : E →L[ℂ] ComplexCoordinates N).analyticAt x
  have he' : AnalyticAt ℂ e'.symm (((e' ∘ f ∘ e.symm) ∘ e) x) :=
    (e'.symm : ComplexCoordinates N' →L[ℂ] E').analyticAt _
  have h₂ : AnalyticAt ℂ (e'.symm ∘ (e' ∘ f ∘ e.symm) ∘ e) x :=
    he'.comp (h₁.comp he)
  have h₃ : e'.symm ∘ (e' ∘ f ∘ e.symm) ∘ e = f := by
    funext y
    simp
  rwa [h₃] at h₂
private theorem differentiable_matExp
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    Differentiable ℂ ComplexMatrix2.matExp := by apply _root_.YangMills.SharedProofs.p11731 <;> assumption
private theorem differentiableOn_logSeries
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    DifferentiableOn ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall := by apply _root_.YangMills.SharedProofs.p36036 <;> assumption
private theorem isOpen_logBall : IsOpen ComplexMatrix2.logBall :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
private def expChartPoint {P : Type} (x₀ A : P → ComplexMatrix2) : P → ComplexMatrix2 :=
  fun p => ComplexMatrix2.matExp (A p) * x₀ p
private theorem exists_expChart_nhd
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {P : Type} [Fintype P] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {D : Set (P → ComplexMatrix2)} {F : (P → ComplexMatrix2) → ComplexMatrix2} (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F D) {x₀ : P → ComplexMatrix2} (hx₀ : x₀ ∈ D)
    (hdet : (F x₀).det = 1) {B : V → P → ComplexMatrix2}
    (hB : Differentiable ℂ B) (hB0 : B 0 = 0) :
    ∃ W : Set V, IsOpen W ∧ 0 ∈ W ∧
      (∀ w ∈ W, expChartPoint x₀ (B w) ∈ D ∧
        F (expChartPoint x₀ (B w)) * (F x₀)⁻¹ ∈ ComplexMatrix2.logBall) ∧
      DifferentiableOn ℂ
        (fun w => ComplexMatrix2.logSeries (F (expChartPoint x₀ (B w)) * (F x₀)⁻¹)) W := by
  have hexp := differentiable_matExp hH
  have hT : Differentiable ℂ fun w => expChartPoint x₀ (B w) := by
    refine differentiable_pi.mpr fun p => ?_
    exact (hexp.comp (differentiable_pi.mp hB p)).mul_const _
  have hT0 : expChartPoint x₀ (B 0) = x₀ := by
    funext p
    simp [expChartPoint, hB0]
  have hW₁ : IsOpen ((fun w => expChartPoint x₀ (B w)) ⁻¹' D) := hD.preimage hT.continuous
  have hQ : DifferentiableOn ℂ (fun w => F (expChartPoint x₀ (B w)) * (F x₀)⁻¹)
      ((fun w => expChartPoint x₀ (B w)) ⁻¹' D) :=
    (hF.comp hT.differentiableOn fun w hw => hw).mul_const _
  refine ⟨((fun w => expChartPoint x₀ (B w)) ⁻¹' D) ∩
      (fun w => F (expChartPoint x₀ (B w)) * (F x₀)⁻¹) ⁻¹' ComplexMatrix2.logBall,
    hQ.continuousOn.isOpen_inter_preimage hW₁ isOpen_logBall, ⟨?_, ?_⟩,
    fun w hw => ⟨hw.1, hw.2⟩,
    (differentiableOn_logSeries hH).comp (hQ.mono inter_subset_left) fun w hw => hw.2⟩
  · change expChartPoint x₀ (B 0) ∈ D
    rwa [hT0]
  · change F (expChartPoint x₀ (B 0)) * (F x₀)⁻¹ ∈ ComplexMatrix2.logBall
    have hu : IsUnit (F x₀).det := by simp [hdet]
    rw [hT0, Matrix.mul_nonsing_inv _ hu]
    simp [ComplexMatrix2.logBall]
private theorem expChartPoint_mem_unimodularPi (hE : ComplexMatrix2.ExpLogEstimates) {P : Type}
    {x₀ A : P → ComplexMatrix2} (hx : x₀ ∈ GroupLieProduct.unimodularPi P)
    (hA : ∀ p, A p ∈ ComplexMatrix2.traceless) :
    expChartPoint x₀ A ∈ GroupLieProduct.unimodularPi P := by
  intro p
  have h₁ := hE.2.2.2.2.2.1 (A p)
  have h₂ : ComplexMatrix2.fullTrace (A p) = 0 := hA p
  have h₃ : (x₀ p).det = 1 := hx p
  change (ComplexMatrix2.matExp (A p) * x₀ p).det = 1
  rw [Matrix.det_mul, h₁, h₂, h₃]
  simp
private theorem tracelessTuple_mem {n : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (w : ComplexCoordinates (n * 3)) (i : Fin n) :
    tracelessTuple b w i ∈ ComplexMatrix2.traceless :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (b c).2
private theorem differentiable_tracelessTuple {n : ℕ}
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (i : Fin n) :
    Differentiable ℂ fun w : ComplexCoordinates (n * 3) => tracelessTuple b w i := by
  unfold tracelessTuple
  fun_prop
theorem holomorphicAtUnimodular_holds (hE : ComplexMatrix2.ExpLogEstimates)
    (hH : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    UnimodularArguments.HolomorphicAtUnimodular := by
  intro P _ k ν D F hD hF hmaps
  have hFd : DifferentiableOn ℂ F D :=
    differentiableOn_of_coords hH (matrixPiCLE ν) matrixCLE hF
  have hFc := hFd.continuousOn
  have hdet : ∀ U ∈ unimodularPart D, (F U).det = 1 := hmaps
  refine ⟨⟨D, hD, rfl⟩, ⟨⟨D, hD, rfl⟩, fun U hU _ => hmaps U hU, fun x hx => ?_⟩, ?_, ?_⟩
  · have hA : AnalyticAt ℂ F x := analyticAt_of_coords hH (matrixPiCLE ν) matrixCLE hF hx.1
    exact ⟨fun U _ => F U, analyticAt_pi_iff.mpr fun _ => hA, Eventually.of_forall fun _ => rfl⟩
  · intro N μ b hN
    have hmem : ∀ X : Fin N → ComplexMatrix2,
        X ∈ (fun U : P → ComplexMatrix2 => U ∘ μ.symm) '' unimodularPart D ↔
          X ∘ μ ∈ unimodularPart D := by
      intro X
      constructor
      · rintro ⟨U, hU, rfl⟩
        have : (U ∘ μ.symm) ∘ μ = U := by
          funext p
          simp
        rwa [this]
      · intro h
        refine ⟨X ∘ μ, h, ?_⟩
        funext i
        simp
    have hcomp : Continuous fun X : Fin N → ComplexMatrix2 => X ∘ μ :=
      continuous_pi fun p => continuous_apply (μ p)
    refine ⟨hN, ⟨(fun X : Fin N → ComplexMatrix2 => X ∘ μ) ⁻¹' D, hD.preimage hcomp, ?_⟩,
      fun X hX => hdet _ ((hmem X).1 hX),
      hFc.comp hcomp.continuousOn fun X hX => ((hmem X).1 hX).1, fun X hX => ?_⟩
    · ext X
      rw [hmem]
      refine and_congr_right fun _ => ?_
      exact ⟨fun h i => by simpa using h (μ.symm i), fun h p => h (μ p)⟩
    · have hx₀ := (hmem X).1 hX
      have hB : Differentiable ℂ
          fun (w : ComplexCoordinates (N * 3)) (p : P) => tracelessTuple b w (μ p) :=
        differentiable_pi.mpr fun p => differentiable_tracelessTuple b (μ p)
      obtain ⟨W, hWo, hW0, hW, hWd⟩ := exists_expChart_nhd hH hD hFd hx₀.1 (hdet _ hx₀) hB (by
        funext p
        simp [tracelessTuple])
      refine ⟨W, hW0, fun w hw => ⟨(hmem _).2 ⟨(hW w hw).1,
        expChartPoint_mem_unimodularPi hE hx₀.2 fun p => tracelessTuple_mem b w (μ p)⟩,
        (hW w hw).2⟩, ?_⟩
      exact isHolomorphicIn_of_differentiableOn hWo
        (matrixCLE.differentiable.comp_differentiableOn hWd)
  · intro b
    have hinl : Continuous fun x : P ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl :=
      continuous_pi fun p => continuous_apply (Sum.inl p)
    refine ⟨⟨(fun x : P ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl) ⁻¹' D, hD.preimage hinl, ?_⟩,
      fun x hx => hdet _ hx, hFc.comp hinl.continuousOn fun x hx => hx.1, fun p hp => ?_⟩
    · ext x
      refine and_congr_right fun _ => ?_
      refine ⟨fun h i => ?_, fun h q => h (Sum.inl q)⟩
      rcases i with q | e
      · exact h q
      · exact e.elim
    · have hB : Differentiable ℂ
          fun (A : P ⊕ Empty → ComplexMatrix2) (q : P) => A (Sum.inl q) :=
        differentiable_pi.mpr fun q => differentiable_apply (Sum.inl q)
      obtain ⟨W, hWo, hW0, hW, hWd⟩ :=
        exists_expChart_nhd hH hD hFd hp.1 (hdet _ hp) hB rfl
      have hzero : (0 : P ⊕ Empty → ComplexMatrix2) ∈ GroupLieProduct.tracelessPi (P ⊕ Empty) :=
        fun _ => ComplexMatrix2.traceless.zero_mem
      refine ⟨W ∩ GroupLieProduct.tracelessPi (P ⊕ Empty), ⟨hW0, hzero⟩,
        fun A hA => ⟨⟨(hW A hA.1).1,
          expChartPoint_mem_unimodularPi hE hp.2 fun q => hA.2 (Sum.inl q)⟩,
          (hW A hA.1).2⟩, ⟨inter_subset_right, fun A hA => ?_⟩, fun ν' => ?_⟩
      · obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hWo A hA.1
        refine ⟨s, hs, fun C hC hlt => ⟨hball ?_, hC⟩⟩
        rw [Metric.mem_ball, dist_eq_norm]
        refine (pi_norm_lt_iff hs).mpr fun i => lt_of_le_of_lt ?_ hlt
        exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm ((C - A) i))
          (Set.finite_range _).bddAbove i
      · have hT : Differentiable ℂ (GroupLieProduct.tupleOfCoords b ν') :=
          differentiable_pi.mpr fun i => differentiable_tracelessTuple b (ν' i)
        have hpre : GroupLieProduct.tupleOfCoords b ν' ⁻¹'
            (W ∩ GroupLieProduct.tracelessPi (P ⊕ Empty)) =
            GroupLieProduct.tupleOfCoords b ν' ⁻¹' W := by
          ext w
          exact ⟨fun h => h.1, fun h => ⟨h, fun i => tracelessTuple_mem b w (ν' i)⟩⟩
        rw [hpre]
        exact isHolomorphicIn_of_differentiableOn (hWo.preimage hT.continuous)
          (matrixCLE.differentiable.comp_differentiableOn
            (hWd.comp hT.differentiableOn fun w hw => hw))
end YangMills.Construction.Matrices.UnimodularArguments
