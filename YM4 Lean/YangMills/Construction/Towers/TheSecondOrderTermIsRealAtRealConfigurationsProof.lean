import YangMills.Construction.Towers.TheMapsOfOneStepKeepRealFunctionsProof
import YangMills.Construction.Towers.TheSecondOrderTermIsRealAtRealConfigurations
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HermitianQuadratic
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicLattice (compactGaugeGroup complexGaugeGroup)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Tower.AsDifferentials
  (boundedSubmodule IsQuadraticExpansion quadraticTerm quadraticTermAt
    HasUniqueQuadraticTerm IsLinearOn)
open YangMills.Construction.Tower.LevelwiseMeans (valuesOrOne)
open YangMills.Construction.Tower.LevelwiseMeans.Unbounded (levelwiseMean meanOfDefined)
open YangMills.Construction.Tower.FullSpace.AsDifferentials
  (iterMean iterRatio topLogRatio topDeriv)
private theorem inv_mem_compact {A : ComplexMatrix2} (h : A ∈ compactGaugeGroup) :
    A⁻¹ ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem ofReal_smul_mem {r : ℝ} {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    (r : ℂ) • X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_smul_mem_hermitianTraceless <;> assumption
private theorem matExp_I_smul_mem {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • Y) ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
private theorem inv_I_smul_logSeries_mem (hE : ComplexMatrix2.ExpLogEstimates)
    {A : ComplexMatrix2} (hA : A ∈ compactGaugeGroup)
    (h₁ : ComplexMatrix2.operatorNorm (A - 1) < 1) :
    Complex.I⁻¹ • ComplexMatrix2.logSeries A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p12580 <;> assumption
private theorem isClosed_hermitianTraceless :
    IsClosed (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.LeftChartFields.isClosed_hermitianTraceless <;> assumption
private theorem complexLogMean_mem (hM : Averaging.ComplexLogMeanOfSmallFamilies) {ι : Type}
    [Fintype ι] [Nonempty ι] (V : ι → ComplexMatrix2) (hV : ∀ i, V i ∈ compactGaugeGroup)
    (hd : ComplexMatrix2.familyDiameter V < Averaging.centreOfMassDiameter) :
    PeriodicLattice.complexLogMean V ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.RealityOfOneStep.complexLogMean_mem_compact <;> assumption
private theorem matExp_finsum_mul_mem (hE : ComplexMatrix2.ExpLogEstimates) {X : Type}
    (s : Set X) (W : X → ComplexMatrix2) (T : ComplexMatrix2) (r : ℝ)
    (hW : ∀ x ∈ s, W x ∈ compactGaugeGroup)
    (hW₁ : ∀ x ∈ s, ComplexMatrix2.operatorNorm (W x - 1) < 1) (hTr : T ∈ compactGaugeGroup) :
    ComplexMatrix2.matExp ((r : ℂ) • ∑ᶠ x ∈ s, ComplexMatrix2.logSeries (W x)) * T ∈
      compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.RealityOfOneStep.matExp_finsum_mul_mem <;> assumption
private theorem list_map_prod_mem {β : Type} (U : β → ComplexMatrix2) (Γ : List β)
    (h : ∀ b, U b ∈ compactGaugeGroup) : (Γ.map U).prod ∈ compactGaugeGroup := by apply _root_.YangMills.Construction.Tower.FullSpace.RealityOfOneStep.list_map_prod_mem <;> assumption
section Unbounded
variable {L k j : ℕ}
private theorem nonempty_contourOrder {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') : Nonempty (ContourOrder L y x) :=
  ⟨(offsetSupport L y x).equivFin.symm⟩
private theorem vertex_mem_coarser (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hP : CubesOfOrderPartition L k j 1) (w : Vertex L k j) :
    (w : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by apply _root_.YangMills.SharedProofs.p3071 <;> assumption
private theorem coe_toFiner {a a' : ℝ} {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
private theorem complexSmoothing_mem_compact (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) (hjk : j ≤ k)
    (c : Edge L k j) (V : Edge L k (j - 1) → ComplexMatrix2) (hc : c.IsPositivelyOriented)
    (hR : ∀ b, V b ∈ compactGaugeGroup) (hV : V ∈ complexDomainNearOne L c) :
    complexSmoothing L V c ∈ compactGaugeGroup := by
  obtain ⟨hP, -, -, -⟩ := hY L hL k j 1 (hj.trans hjk) hj hjk le_rfl hj
  obtain ⟨⟨-, hdt, hdh⟩, hW₁⟩ := hV
  have hcontour : ∀ y : Vertex L k j, (y = c.initial ∨ y = c.terminal) →
      ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        complexContourMean L V y x ∈ compactGaugeGroup := by
    intro y hy x hx
    have := nonempty_contourOrder (L := L) y x
    refine complexLogMean_mem hM _ (fun σ => list_map_prod_mem V _ hR) ?_
    rcases hy with rfl | rfl
    · exact hdt x hx
    · exact hdh x hx
  have hdiff : (toFiner (meshAt L k (j - 1)) (c.terminal - c.initial) : AmbientSpace) =
      (c.terminal : AmbientSpace) - (c.initial : AmbientSpace) := by
    rw [coe_toFiner (vertex_mem_coarser hL hP (c.terminal - c.initial)), AddSubgroup.coe_sub]
  have hterm : ∀ x ∈ cubeVertices L (meshAt L k (j - 1)) c.initial,
      shifted c x ∈ cubeVertices L (meshAt L k (j - 1)) c.terminal := by
    intro x hx
    have ht := hP.cube_add c.initial (c.terminal - c.initial)
    rw [add_sub_cancel] at ht
    show ((shifted c x : Vertex L k (j - 1)) : AmbientSpace) ∈
      cubeOfOrder L (meshAt L k (j - 1)) 1 c.terminal
    rw [ht]
    refine ⟨(x : AmbientSpace), hx, ?_⟩
    unfold shifted
    rw [AddSubgroup.coe_add, hdiff, AddSubgroup.coe_sub]
  have htr : transportAlong V c ∈ compactGaugeGroup := list_map_prod_mem V _ hR
  have hval : complexSmoothing L V c = complexSmoothingPositive L V c := if_pos hc
  rw [hval]
  refine matExp_finsum_mul_mem hE _ _ _ _ (fun x hx => ?_) hW₁ htr
  exact mul_mem (mul_mem (mul_mem (hcontour _ (Or.inl rfl) x hx) (list_map_prod_mem V _ hR))
    (inv_mem_compact (hcontour _ (Or.inr rfl) _ (hterm x hx)))) (inv_mem_compact htr)
private theorem opposite_isPositivelyOriented {a : ℝ} {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
private theorem meanOfDefined_mem_compact (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hjk : j < k) (w : Edge L k j → Option ComplexMatrix2)
    (hw : ∀ b, valuesOrOne w b ∈ compactGaugeGroup)
    (c : Edge L k (j + 1)) (hc : c.IsPositivelyOriented) {g : ComplexMatrix2}
    (hg : meanOfDefined w c = some g) : g ∈ compactGaugeGroup := by
  classical
  have hρ : IsAdmissiblePolydiscRadius L (polydiscRadius L) := (hA.1 L hL).2.2
  unfold meanOfDefined at hg
  split_ifs at hg with h
  obtain rfl := Option.some.inj hg
  exact complexSmoothing_mem_compact (j := j + 1) hM hY hE hL (by omega) (by omega) c _ hc hw
    ((hρ.fullSpace k j hjk c hc).subset_complexDomain h.2)
private theorem levelwiseMean_mem_compact (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (W : Edge L k 0 → ComplexMatrix2) (hW : ∀ b, W b ∈ compactGaugeGroup) (i : ℕ) (hi : i ≤ k) :
    ∀ b, valuesOrOne (levelwiseMean W i) b ∈ compactGaugeGroup := by
  classical
  induction i with
  | zero => exact hW
  | succ i ih =>
    intro c
    have hI := ih (by omega)
    by_cases hc : c.IsPositivelyOriented
    · have e : levelwiseMean W (i + 1) c = meanOfDefined (levelwiseMean W i) c := if_pos hc
      unfold valuesOrOne
      rw [e]
      cases h : meanOfDefined (levelwiseMean W i) c with
      | none => exact one_mem _
      | some g => exact meanOfDefined_mem_compact hA hM hY hE hL (by omega) _ hI c hc h
    · have e : levelwiseMean W (i + 1) c =
          (meanOfDefined (levelwiseMean W i) c.opposite).map (·⁻¹) := if_neg hc
      unfold valuesOrOne
      rw [e]
      cases h : meanOfDefined (levelwiseMean W i) c.opposite with
      | none => exact one_mem _
      | some g =>
        exact inv_mem_compact (meanOfDefined_mem_compact hA hM hY hE hL (by omega) _ hI _
          (opposite_isPositivelyOriented hc) h)
end Unbounded
section Directions
variable {a : ℝ}
private theorem expTwist_mem_compact {U B : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : ∀ b, U b ∈ compactGaugeGroup) (hB : B ∈ edgeFormSpace a) (t : ℝ)
    (b : InfiniteLattice.Link a) :
    expTwist ((t : ℂ) • B) U b ∈ compactGaugeGroup := by
  classical
  have hval : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B) b) * U b ∈ compactGaugeGroup :=
    fun b hb => mul_mem (matExp_I_smul_mem (ofReal_smul_mem (hB.1 b hb))) (hU b)
  by_cases hb : b.IsPositivelyOriented
  · simp only [expTwist, if_pos hb]
    exact hval b hb
  · simp only [expTwist, if_neg hb]
    exact inv_mem_compact (hval _ (opposite_isPositivelyOriented hb))
private theorem mem_complexEdgeForms_of_mem {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace a) : B ∈ complexEdgeForms a :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
end Directions
private theorem mem_of_tendsto_rate {g : ℝ → ComplexMatrix2} {c : ComplexMatrix2} {C δ : ℝ}
    (hδ : 0 < δ) (hb : ∀ t : ℝ, t ≠ 0 → |t| < δ → ‖g t - c‖ ≤ C * |t|)
    (hr : ∀ᶠ t : ℝ in 𝓝[≠] 0, g t ∈ ComplexMatrix2.hermitianTraceless) :
    c ∈ ComplexMatrix2.hermitianTraceless := by
  have hz : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => C * |t| := by fun_prop
    have h := this.tendsto 0
    simp only [abs_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| < δ := by
    have : Continuous fun t : ℝ => |t| := by fun_prop
    have h := this.tendsto 0
    simp only [abs_zero] at h
    exact (h.eventually_lt_const hδ).filter_mono nhdsWithin_le_nhds
  have ht : Tendsto g (𝓝[≠] 0) (𝓝 c) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' ?_ ?_ hz)
    · exact Eventually.of_forall fun t => norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin, hnear] with t h₀ h₁
      exact hb t h₀ h₁
  exact isClosed_hermitianTraceless.mem_of_tendsto ht hr
private theorem taylor_coeffs_mem {f : ℝ → ComplexMatrix2} {a b : ComplexMatrix2} {K δ : ℝ}
    (hδ : 0 < δ)
    (hb : ∀ t : ℝ, |t| < δ →
      ‖f t - (t : ℂ) • a - (1 / 2 : ℂ) • ((t : ℂ) * (t : ℂ)) • b‖ ≤ K * |t| ^ 3)
    (hr : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ ComplexMatrix2.hermitianTraceless) :
    a ∈ ComplexMatrix2.hermitianTraceless ∧ b ∈ ComplexMatrix2.hermitianTraceless := by
  have hr' := hr.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
  have ha : a ∈ ComplexMatrix2.hermitianTraceless := by
    refine mem_of_tendsto_rate (g := fun t => ((t⁻¹ : ℝ) : ℂ) • f t)
      (C := ‖b‖ / 2 + |K| * δ) hδ ?_ ?_
    · intro t h₀ h₁
      have hc : (t : ℂ) ≠ 0 := by exact_mod_cast h₀
      set R := f t - (t : ℂ) • a - (1 / 2 : ℂ) • ((t : ℂ) * (t : ℂ)) • b with hR
      have e : ((t⁻¹ : ℝ) : ℂ) • f t - a = ((t : ℂ) / 2) • b + ((t⁻¹ : ℝ) : ℂ) • R := by
        rw [hR]
        push_cast
        match_scalars <;> field_simp <;> ring
      have hR' : ‖R‖ ≤ K * |t| ^ 3 := hb t h₁
      have ht : 0 < |t| := abs_pos.2 h₀
      have n₁ : ‖((t : ℂ) / 2) • b‖ = |t| / 2 * ‖b‖ := by
        rw [norm_smul, norm_div, Complex.norm_real]
        simp
      have n₂ : ‖((t⁻¹ : ℝ) : ℂ) • R‖ = |t|⁻¹ * ‖R‖ := by
        rw [norm_smul, Complex.norm_real]
        simp
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [n₁, n₂]
      have h₃ : |t|⁻¹ * ‖R‖ ≤ |K| * δ * |t| := by
        have : |t|⁻¹ * ‖R‖ ≤ |t|⁻¹ * (K * |t| ^ 3) :=
          mul_le_mul_of_nonneg_left hR' (inv_nonneg.2 ht.le)
        have e₃ : |t|⁻¹ * (K * |t| ^ 3) = K * |t| * |t| := by
          field_simp
        have : K * |t| * |t| ≤ |K| * δ * |t| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (le_abs_self K) h₁.le ht.le (abs_nonneg K)) ht.le
        linarith
      nlinarith
    · filter_upwards [hr'] with t ht
      exact ofReal_smul_mem ht
  refine ⟨ha, ?_⟩
  refine mem_of_tendsto_rate
    (g := fun t => (((2 : ℝ) * (t⁻¹ * t⁻¹) : ℝ) : ℂ) • (f t - (t : ℂ) • a))
    (C := 2 * |K|) hδ ?_ ?_
  · intro t h₀ h₁
    have hc : (t : ℂ) ≠ 0 := by exact_mod_cast h₀
    set R := f t - (t : ℂ) • a - (1 / 2 : ℂ) • ((t : ℂ) * (t : ℂ)) • b with hR
    have e : (((2 : ℝ) * (t⁻¹ * t⁻¹) : ℝ) : ℂ) • (f t - (t : ℂ) • a) - b =
        (((2 : ℝ) * (t⁻¹ * t⁻¹) : ℝ) : ℂ) • R := by
      rw [hR]
      push_cast
      match_scalars <;> field_simp
    have hR' : ‖R‖ ≤ K * |t| ^ 3 := hb t h₁
    have ht : 0 < |t| := abs_pos.2 h₀
    have n₂ : ‖(((2 : ℝ) * (t⁻¹ * t⁻¹) : ℝ) : ℂ) • R‖ = 2 * (|t|⁻¹ * |t|⁻¹) * ‖R‖ := by
      rw [norm_smul, Complex.norm_real]
      simp
    rw [e, n₂]
    have h₃ : 2 * (|t|⁻¹ * |t|⁻¹) * ‖R‖ ≤ 2 * (|t|⁻¹ * |t|⁻¹) * (K * |t| ^ 3) :=
      mul_le_mul_of_nonneg_left hR' (by positivity)
    have e₃ : 2 * (|t|⁻¹ * |t|⁻¹) * (K * |t| ^ 3) = 2 * K * |t| := by
      field_simp
    have : 2 * K * |t| ≤ 2 * |K| * |t| :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) ht.le
    linarith
  · filter_upwards [hr'] with t ht
    exact ofReal_smul_mem
      (ComplexMatrix2.hermitianTraceless.sub_mem ht (ofReal_smul_mem ha))
section Expression
variable {L k : ℕ}
private theorem topLogRatio_real_eventually (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hC : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (hUG : U ∈ fieldSpace L k 0) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k 0)) (c : PositiveEdge (meshAt L k k)) :
    ∀ᶠ t : ℝ in 𝓝 0, topLogRatio L k U c ((t : ℂ) • B) ∈ ComplexMatrix2.hermitianTraceless := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hold := (hC L hL (j + 1) hk).2.1 j (by omega) _ (hU.2 j (by omega)) U hU
  have hcp : c.1.IsPositivelyOriented := c.2
  obtain ⟨F, O, h, hne, hpos, h0, hhol, -, hv⟩ := hold.local_iter c.1 hcp
  obtain ⟨⟨-, hop⟩, -⟩ := hhol OneLoop.pauliBasis
  obtain ⟨s, hs, hball⟩ := hop 0 h0
  have hBc := mem_complexEdgeForms_of_mem hB
  have hne' : Nonempty F := hne.to_subtype
  set M : ℝ := ∑ b : F, ComplexMatrix2.operatorNorm (B b) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| * M < s := by
    have hcont : Continuous fun t : ℝ => |t| * M := by fun_prop
    have hlim := hcont.tendsto 0
    simp only [abs_zero, zero_mul] at hlim
    exact hlim.eventually_lt_const hs
  filter_upwards [hnear] with t ht
  have hmem : (fun b : F => ((t : ℂ) • B) b) ∈ O := by
    refine hball _ ?_ ?_
    · exact fun b => ((complexEdgeForms _).smul_mem (t : ℂ) hBc).1 b.1 (hpos b.1 b.2)
    · have hle : GroupLieProduct.supNorm
          ((fun b : F => ((t : ℂ) • B) b) - (0 : F → ComplexMatrix2)) ≤ |t| * M := by
        refine ciSup_le fun b => ?_
        have e : ComplexMatrix2.operatorNorm
            (((fun b : F => ((t : ℂ) • B) b) - (0 : F → ComplexMatrix2)) b) =
            |t| * ComplexMatrix2.operatorNorm (B b) := by
          show ‖((t : ℂ) • B) b - 0‖ = |t| * ‖B b‖
          rw [sub_zero, Pi.smul_apply, norm_smul, Complex.norm_real]
          rfl
        rw [e]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun b : F => ComplexMatrix2.operatorNorm (B b))
            (fun _ _ => norm_nonneg _) (Finset.mem_univ b)) (abs_nonneg t)
      exact hle.trans_lt ht
  obtain ⟨-, hn, -⟩ := hv _ ((complexEdgeForms _).smul_mem (t : ℂ) hBc) hmem
  have hWr := expTwist_mem_compact hUG.1 hB t
  have h₁ := levelwiseMean_mem_compact hA hM hY hE hL _ hWr (j + 1) le_rfl c.1
  have h₂ := levelwiseMean_mem_compact hA hM hY hE hL U hUG.1 (j + 1) le_rfl c.1
  exact inv_I_smul_logSeries_mem hE (mul_mem h₁ (inv_mem_compact h₂)) hn
private theorem complexIterDeriv_isLinearOn
    (hC : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) :
    IsLinearOn (complexEdgeForms (meshAt L k 0)) (complexIterDeriv L k k U) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ((hC L hL (j + 1) hk).2.1 j (by omega) _ (hU.2 j (by omega)) U hU).linear_iter
private theorem quadraticTerm_diag_mem (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hC : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies) (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
    (hUG : U ∈ fieldSpace L k 0)
    (x : boundedSubmodule (complexEdgeForms (meshAt L k 0)))
    (hB : (x : Edge L k 0 → ComplexMatrix2) ∈ edgeFormSpace (meshAt L k 0))
    (c : PositiveEdge (meshAt L k k)) :
    quadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
      (topDeriv L k U) x x c ∈ ComplexMatrix2.hermitianTraceless := by
  classical
  have hT := (hC L hL k hk).2.2 U hU
  obtain ⟨-, hex, -⟩ := hT
  obtain ⟨K, δ, hδ, hK⟩ := hex.2 c
  set q := quadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
    (topDeriv L k U) with hq
  set B : Edge L k 0 → ComplexMatrix2 := x.1 with hBdef
  set M : ℝ := GroupLieProduct.supNorm B with hMdef
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => norm_nonneg _
  have hpos : 0 < δ / (M + 1) := by positivity
  have hlin := complexIterDeriv_isLinearOn hC hL hk hU
  have hnorm : ∀ t : ℝ, GroupLieProduct.supNorm (((t : ℂ) • x : boundedSubmodule _) :
      Edge L k 0 → ComplexMatrix2) = |t| * M := by
    intro t
    show (⨆ b, ComplexMatrix2.operatorNorm (((t : ℂ) • B) b)) =
      |t| * ⨆ b, ComplexMatrix2.operatorNorm (B b)
    rw [Real.mul_iSup_of_nonneg (abs_nonneg t)]
    refine iSup_congr fun b => ?_
    show ‖((t : ℂ) • B) b‖ = |t| * ‖B b‖
    rw [Pi.smul_apply, norm_smul, Complex.norm_real]
    rfl
  have main := taylor_coeffs_mem (f := fun t : ℝ => topLogRatio L k U c ((t : ℂ) • B))
    (a := topDeriv L k U B c) (b := q x x c) (K := K * M ^ 3) hpos ?_
    (topLogRatio_real_eventually hA hC hM hY hE hL hk hU hUG hB c)
  · exact main.2
  intro t ht
  have hsmall : |t| * M < δ := by
    have : |t| * (M + 1) < δ := (lt_div_iff₀ (by positivity)).1 ht
    nlinarith [abs_nonneg t]
  have hmain := hK ((t : ℂ) • x) (by rw [hnorm]; exact hsmall)
  rw [hnorm] at hmain
  have e₁ : topDeriv L k U (((t : ℂ) • x : boundedSubmodule _) : Edge L k 0 → ComplexMatrix2) c =
      (t : ℂ) • topDeriv L k U B c := by
    have := (hlin B x.2.1 B x.2.1 (t : ℂ)).2
    show complexIterDeriv L k k U ((t : ℂ) • B) c.1 = _
    rw [this]
    rfl
  have e₂ : q ((t : ℂ) • x) ((t : ℂ) • x) c = ((t : ℂ) * (t : ℂ)) • q x x c := by
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_smul]
  rw [e₁, e₂] at hmain
  have e₃ : K * (|t| * M) ^ 3 = K * M ^ 3 * |t| ^ 3 := by ring
  rw [e₃] at hmain
  exact hmain
end Expression
theorem quadraticTermHermitianAtRealFields_holds (hA : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hC : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hM : Averaging.ComplexLogMeanOfSmallFamilies)
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hE : ComplexMatrix2.ExpLogEstimates) : QuadraticTermHermitianAtRealFields := by
  classical
  intro L hL k hk U hU hUG B hB B' hB' c
  unfold FullSpace.AsDifferentials.complexQuadraticTerm quadraticTermAt
  split_ifs with h
  · obtain ⟨hb, hb'⟩ := h
    set x : boundedSubmodule (complexEdgeForms (meshAt L k 0)) := ⟨B, hb⟩ with hx
    set y : boundedSubmodule (complexEdgeForms (meshAt L k 0)) := ⟨B', hb'⟩ with hy
    obtain ⟨-, hex, -⟩ := (hC L hL k hk).2.2 U hU
    have hsym := hex.1
    have d₁ := quadraticTerm_diag_mem hA hC hM hY hE hL hk hU hUG x hB c
    have d₂ := quadraticTerm_diag_mem hA hC hM hY hE hL hk hU hUG y hB' c
    have d₃ := quadraticTerm_diag_mem hA hC hM hY hE hL hk hU hUG (x + y)
      ((edgeFormSpace _).add_mem hB hB') c
    set q := quadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
      (topDeriv L k U) with hq
    have e : q x y c = ((1 / 2 : ℝ) : ℂ) • (q (x + y) (x + y) c - q x x c - q y y c) := by
      have hs : q y x c = q x y c := by rw [hsym y x]
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, hs]
      push_cast
      match_scalars <;> ring
    show q x y c ∈ ComplexMatrix2.hermitianTraceless
    rw [e]
    exact ofReal_smul_mem (ComplexMatrix2.hermitianTraceless.sub_mem
      (ComplexMatrix2.hermitianTraceless.sub_mem d₃ d₁) d₂)
  · exact ComplexMatrix2.hermitianTraceless.zero_mem
end YangMills.Construction.Tower.FullSpace.HermitianQuadratic
end
