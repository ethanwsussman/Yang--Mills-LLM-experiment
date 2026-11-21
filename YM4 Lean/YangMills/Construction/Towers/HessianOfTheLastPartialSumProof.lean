import YangMills.Construction.Towers.CurvesAndHessianOfTheFibreOfTheIterateProof
import YangMills.Construction.Towers.IteratesOfTheAveragingAlongTwiceDifferentiableCurves
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.SecondOrderOfACompositeAtOneProof
import YangMills.Construction.Towers.TheChainOfABlockField
import YangMills.Construction.Towers.TheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower
namespace LastPartialHessian
variable {L n k j : ℕ}
theorem isOpenFieldSet_iff (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (U : Set (Edge L n k j → ComplexMatrix2)) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ↔
      U ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) U := by apply _root_.YangMills.Construction.Tower.CompositeSecondOrder.isOpenFieldSet_iff <;> assumption
theorem exists_openNhd_sub_of_eventually
    (hop : ∀ U : Set (Edge L n k j → ComplexMatrix2), IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ↔
      U ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) U)
    {U₀ : Set (Edge L n k j → ComplexMatrix2)} (h₀ : IsOpenNhdOfOne U₀)
    {P : (Edge L n k j → ComplexMatrix2) → Prop} (hP : EventuallyNearIdentity (fieldSpace L n k j) P) :
    ∃ U : Set (Edge L n k j → ComplexMatrix2), IsOpenNhdOfOne U ∧ U ⊆ U₀ ∧ ∀ V ∈ U, P V := by
  obtain ⟨hc, O₀, hO₀, e₀⟩ := (hop U₀).1 h₀.1
  obtain ⟨u, hu, h1u, husub⟩ := mem_nhdsWithin.1 hP
  refine ⟨u ∩ U₀, ⟨(hop _).2 ⟨fun V hV => hc hV.2, u ∩ O₀, hu.inter hO₀, ?_⟩, ⟨h1u, h₀.2⟩⟩,
    inter_subset_right, fun V hV => husub ⟨hV.1, hc hV.2⟩⟩
  rw [e₀, inter_assoc]
theorem eventuallyNearIdentity_mem
    (hop : ∀ U : Set (Edge L n k j → ComplexMatrix2), IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ↔
      U ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) U)
    {U : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenNhdOfOne U) :
    EventuallyNearIdentity (fieldSpace L n k j) fun V => V ∈ U := by
  obtain ⟨-, O, hO, e⟩ := (hop U).1 h.1
  have h1 : trivialField L n k j ∈ O := by
    have h2 := h.2
    rw [e] at h2
    exact h2.1
  refine mem_nhdsWithin.2 ⟨O, hO, h1, fun V hV => ?_⟩
  show V ∈ U
  rw [e]
  exact hV
theorem fibre_isRelativelyOpen {j' : ℕ}
    (hop : ∀ U : Set (Edge L n k j → ComplexMatrix2), IsOpenFieldSet PeriodicLattice.compactGaugeGroup U ↔
      U ⊆ fieldSpace L n k j ∧ ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j) U)
    (g : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) (W : Edge L n k j' → ComplexMatrix2)
    {S T : Set (Edge L n k j → ComplexMatrix2)} (hS : IsOpenFieldSet PeriodicLattice.compactGaugeGroup S)
    (hsub : S ⊆ T) (hT : T ⊆ fieldSpace L n k j) :
    ComplexMatrix2.IsRelativelyOpen {U | U ∈ T ∧ g U = W} {U | U ∈ S ∧ g U = W} := by
  obtain ⟨-, O, hO, e⟩ := (hop S).1 hS
  refine ⟨O, hO, ?_⟩
  ext U
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := h1
    rw [e] at h3
    exact ⟨h3.1, hsub h1, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h3⟩
    rw [e]
    exact ⟨h1, hT h2⟩
theorem prolongIter_eq_prolong (b : CriticalBranchData L n k) {j t : ℕ}
    (h : j + 1 ≤ t) (W : Edge L n k t → ComplexMatrix2) :
    b.prolongIter (Nat.le_of_succ_le h) W = b.prolong j (b.prolongIter h W) := by
  induction t, h using Nat.le_induction with
  | base => simp [CriticalBranchData.prolongIter, Nat.leRec_self, Nat.leRec_succ]
  | succ t h ih =>
    have e₁ : ∀ (h' : j ≤ t + 1) (V : Edge L n k (t + 1) → ComplexMatrix2),
        b.prolongIter h' V = b.prolongIter (Nat.le_of_succ_le h) (b.prolong t V) := by
      intro h' V
      simp [CriticalBranchData.prolongIter, Nat.leRec_succ, Nat.le_of_succ_le h]
    have e₂ : ∀ (h' : j + 1 ≤ t + 1) (V : Edge L n k (t + 1) → ComplexMatrix2),
        b.prolongIter h' V = b.prolongIter h (b.prolong t V) := by
      intro h' V
      simp [CriticalBranchData.prolongIter, Nat.leRec_succ, h]
    rw [e₁, e₂, ih]
theorem descendingChain_eq_prolongIter (W : Edge L n k k → ComplexMatrix2) {j : ℕ}
    (hj : j ≤ k) : descendingChain W hj = chosenProlongIter L n k hj W := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.descendingChain_eq_chosenProlongIter <;> assumption
theorem isHessianFormAt_hessianForm {X T S : Type} [AddCommGroup T] [Module ℝ T] [AddCommGroup S]
    [Module ℝ S] (R : Geometry.CurveData X T) {N : Set X} {F : X → ℝ} {x : X}
    (e : S →ₗ[ℝ] R.tangentSpan N x) (ι : S → T) (he : ∀ v, (e v : T) = ι v)
    (h : R.HasUniqueHessianAt N F x) : R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) := by apply _root_.YangMills.Construction.Tower.FibreCurves.isHessianFormAt_chosen <;> assumption
theorem deriv_deriv_add {f g : ℝ → ℝ} (hf : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t)
    (hf' : DifferentiableAt ℝ (deriv f) 0) (hg : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ g t)
    (hg' : DifferentiableAt ℝ (deriv g) 0) :
    deriv (deriv fun t => f t + g t) 0 = deriv (deriv f) 0 + deriv (deriv g) 0 := by
  have e : deriv (fun t => f t + g t) =ᶠ[𝓝 0] fun t => deriv f t + deriv g t := by
    filter_upwards [hf, hg] with t h1 h2
    exact deriv_fun_add h1 h2
  rw [e.deriv_eq]
  exact deriv_fun_add hf' hg'
theorem halfTrace_mul_self_re_nonneg {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (A * A)).re := by apply _root_.YangMills.SharedProofs.p2980 <;> assumption
theorem traceFinsumPairing_self_re_nonneg {ι : Type*} {f : ι → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (traceFinsumPairing f f).re := by
  unfold traceFinsumPairing
  by_cases h : (Function.support fun i => ComplexMatrix2.halfTrace (f i * f i)).Finite
  · rw [finsum_eq_sum_of_support_subset (s := h.toFinset) _ (by simp), Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => halfTrace_mul_self_re_nonneg (hf i)
  · rw [finsum_of_infinite_support h]
    simp
theorem fineOnlyFamilyNorm_sq (l : FineOnlyFamily L n k)
    (hl : ∀ i x, l i x ∈ ComplexMatrix2.hermitianTraceless) :
    fineOnlyFamilyNorm l ^ 2 = ∑ i, traceFinsumNorm (l i) ^ 2 := by
  have hnn : ∀ i, 0 ≤ (traceFinsumPairing (l i) (l i)).re :=
    fun i => traceFinsumPairing_self_re_nonneg (hl i)
  have h1 : (fineOnlyFamilyPairing l l).re = ∑ i, (traceFinsumPairing (l i) (l i)).re := by
    simp [fineOnlyFamilyPairing, fineOnlyPairing, Complex.re_sum]
  rw [fineOnlyFamilyNorm, h1, Real.sq_sqrt (Finset.sum_nonneg fun i _ => hnn i)]
  exact Finset.sum_congr rfl fun i _ => by rw [traceFinsumNorm, Real.sq_sqrt (hnn i)]
theorem exists_smoothingFibreNhd (hSums : PartialGaugedActionsHold)
    (hCB : CriticalBranchExists) (hF : SmoothingFibres)
    (hNb : FibreNeighbourhoodsOfSteps)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (hk : 1 ≤ k) : ∃ U, IsSmoothingFibreNhd L n k U := by
  have hop := isOpenFieldSet_iff (j := 0) (k := k) hE hL hn (Nat.zero_le k)
  have hb : (chosenCriticalBranch L n k).IsCritical := Classical.epsilon_spec (hCB L n k hL hn)
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨-, -, -, -, -, -, U₁, h₁, -, hfib⟩ := hF L n (i + 1) i hL hn (Nat.lt_succ_self i)
  obtain ⟨U₂, h₂, hcrit₂⟩ := hb.prolongComp_critical (i + 1) le_rfl
  obtain ⟨U₃, h₃, hsub₃, hmem₃⟩ := exists_openNhd_sub_of_eventually hop h₁ (eventuallyNearIdentity_mem hop h₂)
  have hS := hSums L n (i + 1) (i + 1) hL hn (by omega) le_rfl U₃ h₃
  have hloc := hNb.2.2.1 L n (i + 1) 0
  refine ⟨U₁, h₁, hfib, ?_⟩
  refine (hS.and hcrit₂).mono ?_
  rintro W ⟨hW, hc₂⟩
  have hU := chainBottom_eq W
  have hx := hW.isCritical.1
  have o₂ := fibre_isRelativelyOpen hop (smoothingIter L n (i + 1) (i + 1)) W h₃.1
    (fun V hV => hmem₃ V hV) h₂.1.1
  have o₁ := fibre_isRelativelyOpen hop (smoothingIter L n (i + 1) (i + 1)) W h₃.1 hsub₃ h₁.1.1
  have c₃ := (hNb.1 _ _ (fieldCurveData L n (i + 1) 0) hloc _ _ (plaquetteAction L n (i + 1)) o₂
    (chosenProlongComp L n (i + 1) (i + 1) W)).1.2 ⟨hx, hc₂⟩
  have c₁ := ((hNb.1 _ _ (fieldCurveData L n (i + 1) 0) hloc _ _ (plaquetteAction L n (i + 1)) o₁
    (chosenProlongComp L n (i + 1) (i + 1) W)).1.1 c₃).2
  rw [hU]
  exact c₁
end LastPartialHessian
theorem lastPartialHessianFormula_proof (hSums : PartialGaugedActionsHold)
    (hCB : CriticalBranchExists) (hF : SmoothingFibres)
    (hG : AxialFunctionFacts.statement)
    (hCh : BlockFieldChainProperties) (hCo : ProlongCompositesAndVertexLayers.Statement)
    (hY : RestrictionHessian.Statement) (hNb : FibreNeighbourhoodsOfSteps)
    (hTw : AnalyticAlongC2CurveStatement)
    (hSub : SubmersionFibresAreSubmanifolds)
    (hE : BondSetFields.ProductStructureHolds)
    (hIt : SmoothingIterAlongTwiceDiffCurves)
    (hC2 : AnalyticIsC2OnSubsetsStatement)
    (hNear : SmallNhdsForPartialGaugedActions) :
    LastPartialHessianFormula := by
  intro L n k hL hn hk
  have hN : IsSmoothingFibreNhd L n k (smoothingFibreNhd L n k) :=
    Classical.epsilon_spec (LastPartialHessian.exists_smoothingFibreNhd hSums hCB hF hNb hE hL hn hk)
  refine ⟨hN, ?_⟩
  have hop := LastPartialHessian.isOpenFieldSet_iff (j := 0) (k := k) hE hL hn (Nat.zero_le k)
  obtain ⟨hFrom, hObj, -⟩ := hCo.1 L n k hL hn hk
  have hP : ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)),
      (∀ j ∈ Set.Iic k, ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k j → ComplexMatrix2) =
          leftDifferential (smoothingIter L n k j) U (B : Edge L n k 0 → ComplexMatrix2)) ∧
      ∀ j ∈ Set.Iic k, ∀ (I : Set ℝ) (γ : ℝ → Edge L n k 0 → ComplexMatrix2),
        (fieldCurveData L n k 0).IsTwiceDiffCurve I γ → γ 0 = U →
        (fieldCurveData L n k 0).tangent γ ∈ edgeFormSpace L n k 0 →
        ∃ J : Set ℝ, IsOpenIntervalAroundZero J ∧ J ⊆ I ∧
          (fieldCurveData L n k j).IsTwiceDiffCurve J
            (fun t => smoothingIter L n k j (γ t)) ∧
          (fieldCurveData L n k j).tangent (fun t => smoothingIter L n k j (γ t)) =
            leftDifferential (smoothingIter L n k j) U ((fieldCurveData L n k 0).tangent γ) :=
    Filter.Eventually.and
      ((Filter.eventually_all_finite (Set.finite_Iic k)).2
        fun j hj => hObj.iterDifferential_linear j hj)
      ((Filter.eventually_all_finite (Set.finite_Iic k)).2 fun j hj => hIt L n k j hL hn hj)
  obtain ⟨W₀, hW₀, hsub₀, hPW⟩ :=
    LastPartialHessian.exists_openNhd_sub_of_eventually hop hN.isOpenNhd hP
  obtain ⟨N, hNo, hsub, hAn, hMan, hOnto⟩ := hNear L n k hL hn hk W₀ hW₀
  have hlevel : ∀ i : Fin k, ∀ᶠ W in 𝓝[fieldSpace L n k k] (fun _ => (1 : ComplexMatrix2)),
      (∃ Ug : Set (Edge L n k (i : ℕ) → ComplexMatrix2),
        IsAnalyticFieldFunction Ug (axialFunction L n k (i : ℕ)) ∧
          descendingChain W i.is_lt.le ∈ Ug) ∧
      (IsAxialGaugeAt L n k (i : ℕ) (descendingChain W i.is_lt.le) →
        ∀ B ∈ edgeFormSpace L n k (i : ℕ), ∀ (I : Set ℝ) (γ : ℝ → Edge L n k (i : ℕ) → ComplexMatrix2),
          (fieldCurveData L n k (i : ℕ)).IsTwiceDiffCurve I γ →
          γ 0 = descendingChain W i.is_lt.le → (fieldCurveData L n k (i : ℕ)).tangent γ = B →
            deriv (deriv fun t => axialFunction L n k (i : ℕ) (γ t)) 0 =
              traceFinsumNorm (contourLogDeriv L n k (i : ℕ)
                (descendingChain W i.is_lt.le) B) ^ 2) ∧
      ∃ T : edgeFormSpace L n k (i : ℕ) →ₗ[ℝ] fineOnlyFunctions L n k (i : ℕ),
        ∀ B : edgeFormSpace L n k (i : ℕ), (T B : FineOnlyVertex L n k (i : ℕ) → ComplexMatrix2) =
          contourLogDeriv L n k (i : ℕ) (descendingChain W i.is_lt.le)
            (B : Edge L n k (i : ℕ) → ComplexMatrix2) := by
    intro i
    have hGi := hG L n k (i : ℕ) hL hn i.is_lt
    obtain ⟨Ug, hg1, -, hg3⟩ := hGi.analytic_near_identity
    have hopi := LastPartialHessian.isOpenFieldSet_iff (j := (i : ℕ)) (k := k) hE hL hn i.is_lt.le
    have hQ := ((LastPartialHessian.eventuallyNearIdentity_mem hopi hg1).and
      (hGi.deriv_deriv_along_curve.and (hObj.contourLogDeriv_linear (i : ℕ) i.is_lt)))
    refine ((hFrom.tendsto (i : ℕ) i.is_lt.le).eventually hQ).mono ?_
    rintro W ⟨h1, h2, h3⟩
    rw [← LastPartialHessian.descendingChain_eq_prolongIter W i.is_lt.le] at h1 h2 h3
    exact ⟨⟨Ug, hg3, h1⟩, h2, h3⟩
  have hChain := (hCh L n k hL hn hk (by have := hL.2; omega)).1
  have hSum := hSums L n k k hL hn hk le_rfl N hNo
  refine ((((Filter.eventually_all.2 hlevel).and hChain).and hSum).and hN.critical_bottom).mono ?_
  rintro W ⟨⟨⟨hlev, hChainW⟩, hPS⟩, hcrit⟩ B
  have hcF : (fieldCurveData L n k 0).IsCriticalOn
      (fibreWithin N (smoothingIter L n k k) W) (partialGaugedAction L n k k) (chainBottom W) := by
    rw [chainBottom_eq W]
    exact hPS.isCritical
  have hUN : chainBottom W ∈ N := hcF.1.1
  have hopen : ComplexMatrix2.IsRelativelyOpen (smoothingIterFibre (smoothingFibreNhd L n k) W)
      (fibreWithin N (smoothingIter L n k k) W) :=
    LastPartialHessian.fibre_isRelativelyOpen hop (smoothingIter L n k k) W hNo.1
      (fun V hV => hsub₀ (hsub hV)) hN.isOpenNhd.1.1
  have hloc := hNb.2.2.1 L n k 0
  have key := fun F : (Edge L n k 0 → ComplexMatrix2) → ℝ =>
    hNb.1 _ _ (fieldCurveData L n k 0) hloc _ _ F hopen (chainBottom W)
  have hcA : (fieldCurveData L n k 0).IsCriticalOn
      (fibreWithin N (smoothingIter L n k k) W) (plaquetteAction L n k) (chainBottom W) :=
    (key _).1.2 ⟨hcF.1, hcrit⟩
  obtain ⟨hlin, hcurv⟩ := hPW _ (hsub hUN)
  have hsubm := hSub L n k 0 k hL hn (Nat.zero_le k) le_rfl N (smoothingIter L n k k) hMan
    (fun V hV => hOnto V hV) W
  have hsm : IsFieldSubmanifold (fibreWithin N (smoothingIter L n k k) W) := hsubm.1.1
  obtain ⟨-, fin, -⟩ := id hsm
  let := fin
  have hYA := hY.2 L n k 0 _ _ (plaquetteAction L n k) hsm hsm subset_rfl
    (hC2 L n k 0 hL hn (Nat.zero_le k) N _ _ (hAn 0 (Nat.zero_le k)) fun V hV => hV.1)
  have hYF := hY.2 L n k 0 _ _ (partialGaugedAction L n k k) hsm hsm subset_rfl
    (hC2 L n k 0 hL hn (Nat.zero_le k) N _ _ (hAn k le_rfl) fun V hV => hV.1)
  obtain ⟨hparA, hlocA, hhessA, -⟩ := hYA
  obtain ⟨-, -, hhessF, -⟩ := hYF
  have hspec := fun j (hj : j ≤ k) => Classical.epsilon_spec (hlin j hj)
  have hmem : ∀ v : LinearMap.ker (topConstraintMap L n k W),
      (edgeFormSpace L n k 0).subtype ((LinearMap.ker (topConstraintMap L n k W)).subtype v) ∈
        (fieldCurveData L n k 0).tangentSpan
          (fibreWithin N (smoothingIter L n k k) W) (chainBottom W) := by
    intro v
    refine (hsubm.2 _ hUN hcF.1.2 _).2 ⟨v.1.2, ?_⟩
    have h1 : (topConstraintMap L n k W v.1 : Edge L n k k → ComplexMatrix2) = 0 := by
      rw [LinearMap.mem_ker.1 v.2]
      rfl
    exact (hspec k le_rfl v.1).symm.trans h1
  let e : LinearMap.ker (topConstraintMap L n k W) →ₗ[ℝ] (fieldCurveData L n k 0).tangentSpan
      (fibreWithin N (smoothingIter L n k k) W) (chainBottom W) :=
    LinearMap.codRestrict _ ((edgeFormSpace L n k 0).subtype ∘ₗ
      (LinearMap.ker (topConstraintMap L n k W)).subtype) hmem
  have hIA := LastPartialHessian.isHessianFormAt_hessianForm (fieldCurveData L n k 0) e
    (fun v : LinearMap.ker (topConstraintMap L n k W) => (v.1.1 : Edge L n k 0 → ComplexMatrix2))
    (fun _ => rfl) (hhessA _ hcA)
  have hIF := LastPartialHessian.isHessianFormAt_hessianForm (fieldCurveData L n k 0) e
    (fun v : LinearMap.ker (topConstraintMap L n k W) => (v.1.1 : Edge L n k 0 → ComplexMatrix2))
    (fun _ => rfl) (hhessF _ hcF)
  obtain ⟨d, O, φ, z, hφ, hz, hφz⟩ := hlocA _ hcF.1
  obtain ⟨D, -, hread⟩ := hparA (Fin d → ℝ) O φ z hφ hz
  obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hread.exists_curve (by rw [hφz]; exact hcA) B.1.1
    (by rw [hφz]; exact hmem B)
  rw [hφz] at hγ0
  have valA := hIA I γ B hγ hγN hγ0 hγt
  have valF := hIF I γ B hγ hγN hγ0 hγt
  have htf : (fieldCurveData L n k 0).tangent γ ∈ edgeFormSpace L n k 0 := by
    rw [hγt]
    exact B.1.2
  have hterm : ∀ i (hi : i < k),
      (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ
        (fun s => axialFunction L n k i (smoothingIter L n k i (γ s))) t) ∧
      DifferentiableAt ℝ (deriv fun s => axialFunction L n k i (smoothingIter L n k i (γ s))) 0 ∧
      deriv (deriv fun s => axialFunction L n k i (smoothingIter L n k i (γ s))) 0 =
        traceFinsumNorm (contourLogDeriv L n k i (descendingChain W hi.le)
          (smoothingIterDifferential L n k i (chainBottom W) B.1 : edgeFormSpace L n k i).1) ^ 2 := by
    intro i hi
    obtain ⟨⟨Ug, hg, hVg⟩, halong, -⟩ := hlev ⟨i, hi⟩
    obtain ⟨J, -, -, hγ', hγ't⟩ := hcurv i hi.le I γ hγ hγ0 htf
    have h0 : (fun t => smoothingIter L n k i (γ t)) 0 = descendingChain W hi.le := by
      show smoothingIter L n k i (γ 0) = _
      rw [hγ0]
      exact ((hChainW.1 i hi.le).2).symm
    have htB : (fieldCurveData L n k i).tangent (fun t => smoothingIter L n k i (γ t)) =
        (smoothingIterDifferential L n k i (chainBottom W) B.1 : edgeFormSpace L n k i).1 := by
      rw [hγ't, hγt]
      exact (hspec i hi.le B.1).symm
    obtain ⟨e1, e2⟩ := hTw L n k i hL hn hi.le Ug _ hg _ hVg J _ hγ' h0
    exact ⟨e1, e2, halong (hChainW.2.1 i hi) _ (smoothingIterDifferential L n k i (chainBottom W) B.1).2
      J _ hγ' h0 htB⟩
  have hsum : ∀ i, i ≤ k → deriv (deriv fun t => partialGaugedAction L n k i (γ t)) 0 =
      deriv (deriv fun t => plaquetteAction L n k (γ t)) 0 + ∑ j ∈ Finset.range i,
        deriv (deriv fun s => axialFunction L n k j (smoothingIter L n k j (γ s))) 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < k := hi
      obtain ⟨a1, a2, -⟩ := hterm i hi'
      obtain ⟨b1, b2⟩ := hTw L n k 0 hL hn (Nat.zero_le k) N _ (hAn i hi'.le) _ hUN I γ hγ hγ0
      have he : (fun t => partialGaugedAction L n k (i + 1) (γ t)) =
          fun t => partialGaugedAction L n k i (γ t) +
            axialFunction L n k i (smoothingIter L n k i (γ t)) := rfl
      rw [he, LastPartialHessian.deriv_deriv_add b1 b2 a1 a2, ih hi'.le, Finset.sum_range_succ,
        add_assoc]
  have hnorm : fineOnlyFamilyNorm (contourFamily W B.1) ^ 2 =
      ∑ i : Fin k, traceFinsumNorm (contourFamily W B.1 i) ^ 2 := by
    refine LastPartialHessian.fineOnlyFamilyNorm_sq _ fun i x => ?_
    obtain ⟨-, -, T, hT⟩ := hlev i
    have h1 := (T (smoothingIterDifferential L n k (i : ℕ) (chainBottom W) B.1)).2
    have h2 := hT (smoothingIterDifferential L n k (i : ℕ) (chainBottom W) B.1)
    rw [show contourFamily W B.1 i = _ from h2.symm]
    exact h1 x (mem_univ _)
  have hFk : deriv (deriv fun t => partialGaugedAction L n k k (γ t)) 0 =
      deriv (deriv fun t => plaquetteAction L n k (γ t)) 0 +
        ∑ i : Fin k, traceFinsumNorm (contourFamily W B.1 i) ^ 2 := by
    rw [hsum k le_rfl, ← Fin.sum_univ_eq_sum_range
      (fun j => deriv (deriv fun s => axialFunction L n k j (smoothingIter L n k j (γ s))) 0) k]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (hterm i i.is_lt).2.2
  have eF := ((key (partialGaugedAction L n k k)).2 hcF).2
    (LinearMap.ker (topConstraintMap L n k W))
    (fun v : LinearMap.ker (topConstraintMap L n k W) => (v.1.1 : Edge L n k 0 → ComplexMatrix2))
  have eA := ((key (plaquetteAction L n k)).2 hcA).2
    (LinearMap.ker (topConstraintMap L n k W))
    (fun v : LinearMap.ker (topConstraintMap L n k W) => (v.1.1 : Edge L n k 0 → ComplexMatrix2))
  show (fieldCurveData L n k 0).hessianForm (S := LinearMap.ker (topConstraintMap L n k W))
      (fun v => v.1.1) (smoothingIterFibre (smoothingFibreNhd L n k) W)
      (partialGaugedAction L n k k) (chainBottom W) B =
    (fieldCurveData L n k 0).hessianForm (S := LinearMap.ker (topConstraintMap L n k W))
      (fun v => v.1.1) (smoothingIterFibre (smoothingFibreNhd L n k) W)
      (plaquetteAction L n k) (chainBottom W) B + fineOnlyFamilyNorm (contourFamily W B.1) ^ 2
  rw [← eF, ← eA, hnorm, valF, valA, hFk]
end YangMills.Construction.Tower
end
