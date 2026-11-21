import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayersProof
import YangMills.Construction.TransferOperators.InsertionObservableIsRealLocalAndGaugeInvariantProof
import YangMills.Construction.TransferOperators.PolynomialsOfTheNextSymmetricStackDecompose
import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import YangMills.Construction.TransferOperators.ReversalInvarianceAtContinuousFunctionsInTheNextStack
import YangMills.Construction.TransferOperators.ReversalInvariancePassesToTheNextSymmetricStack
import YangMills.Construction.TransferOperators.ReversalOfTheFunctionOfTheStepBetweenSymmetricStacks
import YangMills.Construction.TransferOperators.TwoEliminationsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice SpinHarmonics Matrices.ComplexMatrix2
namespace TransferOperators.CenteredStackReversal
variable {μ : Fin 4}
theorem continuous_transportedLinkVariable (S : Stack) (j : ℤ) (b : SliceLink μ) :
    Continuous fun U : GaugeField 1 => S.transportedLinkVariable μ U j b := by apply _root_.YangMills.Construction.TransferOperators.SliceMean.continuous_transportedLinkVariable <;> assumption
theorem continuous_blockValues (S : Stack) (B : Block μ) (j : ℤ) :
    Continuous fun U : GaugeField 1 => S.blockValues B U j :=
  continuous_pi fun b => continuous_transportedLinkVariable S j b.1
theorem continuous_enclosingValues (D : CenteredStackStep μ) : Continuous D.enclosingValues :=
  continuous_pi fun p => continuous_transportedLinkVariable D.enclosingStack p.1.1 p.1.2
theorem integrable_continuousMap_comp {K : Type} [Finite K] {ρ : Measure (GaugeField 1)}
    [IsProbabilityMeasure ρ] (g : C(K → specialUnitary, ℂ)) {W : GaugeField 1 → K → specialUnitary}
    (hW : Continuous W) : Integrable (fun U => g (W U)) ρ :=
  Integrable.of_bound (g.continuous.comp hW).measurable.aestronglyMeasurable ‖g‖
    (ae_of_all _ fun _ => g.norm_coe_le_norm _)
theorem integrable_triple_product {K L M : Type} [Finite K] [Finite L] [Finite M]
    {ρ : Measure (GaugeField 1)} [IsProbabilityMeasure ρ] (f : C(K → specialUnitary, ℂ))
    (h : C(L → specialUnitary, ℂ)) (Φ : C(M → specialUnitary, ℂ))
    {W₁ : GaugeField 1 → K → specialUnitary}
    {W₂ : GaugeField 1 → L → specialUnitary} {W₃ : GaugeField 1 → M → specialUnitary}
    (h₁ : Continuous W₁) (h₂ : Continuous W₂) (h₃ : Continuous W₃) :
    Integrable (fun U => f (W₁ U) * h (W₂ U) * Φ (W₃ U)) ρ := by
  have hc : Continuous fun U => f (W₁ U) * h (W₂ U) * Φ (W₃ U) :=
    ((f.continuous.comp h₁).mul (h.continuous.comp h₂)).mul (Φ.continuous.comp h₃)
  refine Integrable.of_bound hc.measurable.aestronglyMeasurable (‖f‖ * ‖h‖ * ‖Φ‖)
    (ae_of_all _ fun U => ?_)
  rw [norm_mul, norm_mul]
  gcongr
  · exact f.norm_coe_le_norm _
  · exact h.norm_coe_le_norm _
  · exact Φ.norm_coe_le_norm _
theorem continuous_of_mem_smoothSet {J : Type} [Finite J] {F : (J → specialUnitary) → ℂ}
    (hF : F ∈ smoothSet) : Continuous F :=
  (mem_iInter.1 hF) 0
theorem isRealEntryPolynomial_permuteArgs {J : Type} [Finite J] (s : Equiv.Perm J)
    {F : (J → specialUnitary) → ℂ} (hF : IsRealEntryPolynomial F) :
    IsRealEntryPolynomial (permuteArgs s F) := by
  obtain ⟨⟨p, hp⟩, hr⟩ := hF
  refine ⟨⟨MvPolynomial.rename (Sum.map (Prod.map s id) (Prod.map s id)) p, fun u => ?_⟩,
    fun u => hr _⟩
  have e : entryEval (fun b => u (s b)) = entryEval u ∘
      Sum.map (Prod.map s id) (Prod.map s id) := by
    funext x
    rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩ <;> rfl
  rw [MvPolynomial.eval_rename, permuteArgs, hp, e]
theorem sum_integral_eq_sum_integral_permuteArgs {K : Type} [Finite K]
    {ρ : Measure (GaugeField 1)} [IsProbabilityMeasure ρ] (s : Equiv.Perm K)
    {W : GaugeField 1 → K → specialUnitary} (hW : Continuous W)
    {m : ℕ} (N : Fin m → C(K → specialUnitary, ℂ)) (hreal : ∀ α u, (N α u).im = 0)
    (hinv : ∀ T : C(K → specialUnitary, ℂ), (∀ u, (T u).im = 0) →
      ∫ U, T (W U) ∂ρ = ∫ U, permuteArgs s T (W U) ∂ρ) :
    ∑ α, ∫ U, N α (W U) ∂ρ = ∑ α, ∫ U, permuteArgs s (N α) (W U) ∂ρ := by
  have hsumApp : ∀ u, (∑ α, N α) u = ∑ α, N α u := fun u => by
    simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  have key := hinv (∑ α, N α) fun u => by
    rw [hsumApp, Complex.im_sum]
    exact Finset.sum_eq_zero fun α _ => hreal α u
  have hP : ∀ α, Integrable (fun U => permuteArgs s (N α) (W U)) ρ := fun α =>
    integrable_continuousMap_comp (precompAlong s (N α)) hW
  rw [← integral_finsetSum _ fun α _ => integrable_continuousMap_comp (N α) hW,
    ← integral_finsetSum _ fun α _ => hP α]
  calc ∫ U, ∑ α, N α (W U) ∂ρ = ∫ U, (∑ α, N α) (W U) ∂ρ :=
        integral_congr_ae (ae_of_all _ fun U => (hsumApp _).symm)
    _ = ∫ U, permuteArgs s (∑ α, N α : C(K → specialUnitary, ℂ)) (W U) ∂ρ := key
    _ = ∫ U, ∑ α, permuteArgs s (N α) (W U) ∂ρ :=
        integral_congr_ae (ae_of_all _ fun U => hsumApp _)
theorem sum_integral_terms_eq_reversed (hBoth : CenteredStack.OuterEliminationStatement)
    (hRev : CenteredStack.ReversalStatement)
    (hCont : ReversalInvariantContinuousNextStack.Statement)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)} (hν : IsPeriodicGibbs β ν)
    [IsProbabilityMeasure ν] (hG : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β)
    (D : CenteredStackStep μ)
    (hinv : IsReversalInvariantOnCenteredStack μ ν D.center D.halfWidth D.one_le_halfWidth)
    (hne : (linksWithin D.vertexSet).Nonempty) {m : ℕ}
    (f h : Fin m → (D.block.links → specialUnitary) → ℂ)
    (Φ : Fin m → C(D.InnerPairs → specialUnitary, ℂ))
    (hf : ∀ α, IsRealEntryPolynomial (f α)) (hh : ∀ α, IsRealEntryPolynomial (h α))
    (hΦ : ∀ α, IsRealEntryPolynomial (Φ α : (D.InnerPairs → specialUnitary) → ℂ)) :
    ∑ α, ∫ U, f α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        h α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        Φ α (D.enclosingValues U) ∂ν =
      ∑ α, ∫ U, h α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        f α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) (Φ α)
          (D.enclosingValues U) ∂ν := by
  have hex : ∀ α, IsRealEntryPolynomial
      (levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) (Φ α) :
        (D.InnerPairs → specialUnitary) → ℂ) :=
    fun α => isRealEntryPolynomial_permuteArgs _ (hΦ α)
  have hL := fun α => hBoth μ β hβ ν hG D (f α) (h α) (hf α) (hh α) (Φ α) (hΦ α)
  have hR := fun α => hBoth μ β hβ ν hG D (h α) (f α) (hh α) (hf α) _ (hex α)
  obtain ⟨N, hN⟩ : ∃ N : Fin m → C(D.InnerPairs → specialUnitary, ℂ), ∀ α,
      (N α : (D.InnerPairs → specialUnitary) → ℂ) = D.transferStepFunction β (hf α) (hh α) (Φ α) :=
    ⟨fun α => ⟨_, continuous_of_mem_smoothSet (hL α).1⟩, fun _ => rfl⟩
  have hreal : ∀ α u, (N α u).im = 0 := fun α u => by
    rw [hN α]
    exact (hL α).2.1 u
  have habs := sum_integral_eq_sum_integral_permuteArgs
    (reflectPairPerm D.center D.halfWidth D.vertexSet)
    (continuous_enclosingValues D) N hreal fun T hT =>
      hCont μ β hβ ν hν D.center D.halfWidth D.one_le_halfWidth hinv D.vertexSet T hne hT
  have hperm : ∀ α, permuteArgs (reflectPairPerm D.center D.halfWidth D.vertexSet) (N α) =
      D.transferStepFunction β (hh α) (hf α)
        (levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) (Φ α)) := fun α => by
    rw [hN α, ← levelReversal_eq_permuteArgs]
    exact hRev μ β hβ D (f α) (h α) (hf α) (hh α) (Φ α) (hΦ α)
  refine (Finset.sum_congr rfl fun α _ => ?_).trans (habs.trans
    (Finset.sum_congr rfl fun α _ => ?_))
  · rw [(hL α).2.2, hN α]
  · rw [(hR α).2.2, hperm α]
theorem vertices_finite (B : Block μ) : B.vertices.Finite := by apply _root_.YangMills.Construction.TransferOperators.LogKernelRatio.finite_vertices <;> assumption
theorem integral_eq_integral_levelReversal_of_step
    (hBoth : CenteredStack.OuterEliminationStatement)
    (hRev : CenteredStack.ReversalStatement)
    (hCont : ReversalInvariantContinuousNextStack.Statement)
    (hDec : CenteredStack.PolynomialSplitStatement)
    {β : ℝ} (hβ : 0 < β) {ν : Measure (GaugeField 1)} (hν : IsPeriodicGibbs β ν)
    [IsProbabilityMeasure ν] (hG : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β)
    (D : CenteredStackStep μ)
    (hinv : IsReversalInvariantOnCenteredStack μ ν D.center D.halfWidth D.one_le_halfWidth)
    (hne : (linksWithin D.vertexSet).Nonempty)
    (v₀ : Set (SliceSite μ)) [Finite v₀] (hv : v₀ ⊆ D.vertexSet)
    (hB : (D.block.links : Set (SliceLink μ)) = linksWithin v₀)
    (Ψ : (centeredLinkPairs D.center (D.halfWidth + 1) v₀ → specialUnitary) → ℂ)
    (hΨ : IsRealEntryPolynomial Ψ) :
    ∫ U, Ψ (fun p => D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
      ∫ U, levelReversal D.center (D.halfWidth + 1) v₀ Ψ
        (fun p => D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2) ∂ν := by
  obtain ⟨m, f, h, Φ, hf, hh, hΦ, hdec⟩ := hDec μ D v₀ hv hB Ψ hΨ
  have hsum := sum_integral_terms_eq_reversed hBoth hRev hCont hβ hν hG D hinv hne f h Φ hf hh hΦ
  have hb₁ := continuous_blockValues D.enclosingStack D.block (D.center - D.halfWidth)
  have hb₂ := continuous_blockValues D.enclosingStack D.block (D.center + D.halfWidth + 1)
  have ho := continuous_enclosingValues D
  have hleft : ∫ U, Ψ (fun p => D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
      ∑ α, ∫ U, f α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        h α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        Φ α (D.enclosingValues U) ∂ν := by
    have hI : ∀ α, Integrable (fun U =>
        f α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        h α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        Φ α (D.enclosingValues U)) ν := fun α =>
      integrable_triple_product ⟨f α, (hf α).1.continuous⟩ ⟨h α, (hh α).1.continuous⟩ (Φ α)
        hb₁ hb₂ ho
    rw [← integral_finsetSum _ fun α _ => hI α]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    exact hdec fun p => D.enclosingStack.transportedLinkVariable μ U p.1 p.2
  have hright : ∫ U, levelReversal D.center (D.halfWidth + 1) v₀ Ψ
        (fun p => D.enclosingStack.transportedLinkVariable μ U p.1.1 p.1.2) ∂ν =
      ∑ α, ∫ U, h α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        f α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) (Φ α)
          (D.enclosingValues U) ∂ν := by
    have hI : ∀ α, Integrable (fun U =>
        h α (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
        f α (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
        levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) (Φ α)
          (D.enclosingValues U)) ν := fun α =>
      integrable_triple_product ⟨h α, (hh α).1.continuous⟩ ⟨f α, (hf α).1.continuous⟩
        (levelExchanged _ (Φ α)) hb₁ hb₂ ho
    rw [← integral_finsetSum _ fun α _ => hI α]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have e := hdec fun p =>
      D.enclosingStack.transportedLinkVariable μ U (reflectedLevel D.center p.1) p.2
    have e₁ : reflectedLevel D.center (D.center - D.halfWidth) = D.center + D.halfWidth + 1 := by
      simp only [reflectedLevel]
      ring
    have e₂ : reflectedLevel D.center (D.center + D.halfWidth + 1) = D.center - D.halfWidth := by
      simp only [reflectedLevel]
      ring
    simp only [e₁, e₂] at e
    refine e.trans (Finset.sum_congr rfl fun α _ => ?_)
    rw [mul_comm (f α _) (h α _)]
    rfl
  rw [hleft, hright]
  exact hsum
theorem reversalInvariantSucc
    (hStates : GibbsHaarKernels.Statement)
    (hBoth : CenteredStack.OuterEliminationStatement)
    (hRev : CenteredStack.ReversalStatement)
    (hCont : ReversalInvariantContinuousNextStack.Statement)
    (hDec : CenteredStack.PolynomialSplitStatement) : ReversalInvariantSuccStatement := by
  intro μ β hβ ν hν i k hk hinv v₀ _ Ψ hne hΨ _
  have hprob : IsProbabilityMeasure ν := hν.1.1
  have hG : ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β :=
    ((hStates.1 β hβ ν hprob).1).mp hν.1
  have hfin : ((linksWithin v₀).Finite) := linksWithin_finite v₀
  have hmono : ∀ {w w' : Set (SliceSite μ)}, w ⊆ w' → linksWithin w ⊆ linksWithin w' :=
    fun hs _ hb => ⟨hs hb.1, hs hb.2⟩
  obtain ⟨B, hB⟩ : ∃ B : Block μ, (B.links : Set (SliceLink μ)) = linksWithin v₀ :=
    ⟨⟨hfin.toFinset, by
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hfin.mem_toFinset.2 hb⟩⟩, hfin.coe_toFinset⟩
  have hsf : Finite ↥(v₀ ∪ B.thickenedBlock.vertices) :=
    ((Set.toFinite v₀).union (vertices_finite _)).to_subtype
  exact integral_eq_integral_levelReversal_of_step hBoth hRev hCont hDec hβ hν hG
    ⟨i, k, hk, v₀ ∪ B.thickenedBlock.vertices, hsf, B,
      fun b hb => hmono subset_union_right (B.thickened_subset_linksWithin hb)⟩
    hinv (hne.mono (hmono subset_union_left)) v₀ subset_union_left hB Ψ hΨ
end TransferOperators.CenteredStackReversal
end YangMills.Construction
end
