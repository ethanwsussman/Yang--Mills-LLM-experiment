import YangMills.Construction.Torus.ComplexExtensionOfABoundedRealForm
import YangMills.Construction.Torus.CutOffsEqualToOneOnProjections
import YangMills.Construction.Torus.DistributionOfABoundedComplexForm
import YangMills.Construction.Torus.GradientNormOfACutOffTimesAMode
import YangMills.Construction.Torus.MultilinearFormBoundedInTheGradientNorms
import YangMills.Construction.Torus.NormOfAProductAndMultiplesOfTensors
import YangMills.Construction.Torus.PartialSumsInsideACutOffConverge
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints.BoundedFormDistrib
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem mem_componentSpace_of_mem_testFns {O : Fin n → Set (Pt s .euclidean)} {i : Fin n}
    {f : Pt s .euclidean → ℝ}
    (hf : asFunctionOnOnePoint f ∈ testFns (singletonTuples (O i))) :
    f ∈ entrySpace O i := by
  obtain ⟨hsm, hcpt, hsub⟩ := hf
  have hsm' : IsCnOn Set.univ ⊤ (asFunctionOnOnePoint f ∘ tupleProj s .euclidean 1) := hsm
  have hev : Continuous fun y : Tuple s .euclidean 1 => y 0 := continuous_apply 0
  have himg : IsCompact
      ((fun y : Tuple s .euclidean 1 => y 0) '' closedSupport (asFunctionOnOnePoint f)) :=
    hcpt.image hev
  have hts : tsupport f ⊆
      (fun y : Tuple s .euclidean 1 => y 0) '' closedSupport (asFunctionOnOnePoint f) := by
    intro x hx
    refine ⟨fun _ => x, ?_, rfl⟩
    rw [closedSupport_asFunctionOnOnePoint]
    exact hx
  refine ⟨⟨hsm'.1, fun m _ => hsm'.2 m le_top⟩, himg.of_isClosed_subset (isClosed_tsupport f) hts,
    hts.trans ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hsub hy
theorem cutoffPartialSum_isFiniteTensorSumWithin (hMode : CutoffTimesModeGradNorm)
    (hProd : ProductNorms.ProductBoundsClaim)
    (hOps : TestFnOperations)
    {ρ : ℝ} (hn : 1 ≤ n) (hρ : 0 < ρ) {O : Fin n → Set (Pt s .euclidean)}
    (hOpen : ∀ i, IsOpen (O i)) {χ : Fin n → Pt s .euclidean → ℝ} (hχ : IsCutoff O χ)
    (F : Tuple s .euclidean n → ℂ) (t : ℕ+) :
    IsFiniteTensorSumWithin O χ (cutoffPartialSum (4 * ρ) χ F t) := by
  have hfac : ∀ (k : Fin (4 * n) → ℤ) (i : Fin n),
      ofSinglePoint (cutoffModeTuple (4 * ρ) χ k i) ∈ testFns (singletonTuples (O i)) ∧
        closedSupport (ofSinglePoint (cutoffModeTuple (4 * ρ) χ k i)) ⊆
          closedSupport (asFunctionOnOnePoint (χ i)) := fun k i => by
    have h := hMode s ρ hρ (O i) (χ i) (Torus.FourierBox.blockOf k i) (hOpen i) (hχ i)
    exact ⟨h.1, h.2.1⟩
  have hsmul : ∀ (b : ℂ) (k : Fin (4 * n) → ℤ) (i : Fin n),
      ofSinglePoint (fun x => b * cutoffModeTuple (4 * ρ) χ k i x) ∈
          testFns (singletonTuples (O i)) ∧
        closedSupport (ofSinglePoint fun x => b * cutoffModeTuple (4 * ρ) χ k i x) ⊆
          closedSupport (asFunctionOnOnePoint (χ i)) := by
    intro b k i
    obtain ⟨h1, h2⟩ := hfac k i
    have hopen : IsOpen (singletonTuples (O i)) :=
      (hOpen i).preimage (continuous_apply (0 : Fin 1))
    have hlin := ((hOps s .euclidean 1 le_rfl).2.1 _ hopen).2.1 _ h1 _ h1 b 0
    have heq : b • ofSinglePoint (cutoffModeTuple (4 * ρ) χ k i) +
        (0 : ℂ) • ofSinglePoint (cutoffModeTuple (4 * ρ) χ k i) =
        ofSinglePoint (fun x => b * cutoffModeTuple (4 * ρ) χ k i x) := by
      funext y
      simp [ofSinglePoint]
    rw [heq] at hlin
    exact ⟨hlin.1, hlin.2.trans ((Set.union_self _).subset.trans h2)⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (4 * n) → ℤ), S = Torus.FourierBox.modesWithin (t : ℕ) :=
    ⟨_, rfl⟩
  refine ⟨S.card, fun l => Function.update (cutoffModeTuple (4 * ρ) χ (S.equivFin.symm l).1)
    ⟨0, hn⟩ (fun x => Torus.FourierBox.fourierCoeff (4 * ρ) F (S.equivFin.symm l).1 *
      cutoffModeTuple (4 * ρ) χ (S.equivFin.symm l).1 ⟨0, hn⟩ x), ?_, ?_⟩
  · intro l i
    beta_reduce
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      rw [Function.update_self]
      exact hsmul _ _ _
    · rw [Function.update_of_ne hi]
      exact hfac _ _
  · funext y
    rw [Finset.sum_apply]
    have hterm : ∀ k : Fin (4 * n) → ℤ,
        Torus.FourierBox.fourierCoeff (4 * ρ) F k * tensorProd (cutoffModeTuple (4 * ρ) χ k) y =
          tensorProd (Function.update (cutoffModeTuple (4 * ρ) χ k) ⟨0, hn⟩
            (fun x => Torus.FourierBox.fourierCoeff (4 * ρ) F k *
              cutoffModeTuple (4 * ρ) χ k ⟨0, hn⟩ x)) y := fun k =>
      congrFun ((hProd s .euclidean n hn 0).2.2 (cutoffModeTuple (4 * ρ) χ k)
        (Torus.FourierBox.fourierCoeff (4 * ρ) F k)) y
    simp only [cutoffPartialSum, hterm, ← hS]
    rw [← Finset.sum_coe_sort, ← S.equivFin.symm.sum_comp]
theorem boundedMultilinearFormIsDistribution_holds
    (hExt : ComplexExtension.ExistsComplexExtension)
    (hDist : BoundedComplexFormDistribution)
    (hProj : CutoffsEqualOneOnProjections)
    (hConv : CutoffPartialSumsTendsto)
    (hMode : CutoffTimesModeGradNorm)
    (hProd : ProductNorms.ProductBoundsClaim)
    (hOps : TestFnOperations) : BoundedMultilinearFormIsDistribution := by
  intro s n ρ c O hO hc B hlin hB
  obtain ⟨hn, hρ, hOi⟩ := id hO
  obtain ⟨Bc, hBlin, hBbd, hBB⟩ := hExt s n ρ c O B hO hc hlin hB
  have hC : (0 : ℝ) ≤ 2 ^ n * c := by positivity
  obtain ⟨T, hTord, hTval, hTF, hTuniq⟩ :=
    hDist s n ρ (2 ^ n * c) O Bc hO hC hBlin hBbd
  have hagree : ∀ (φ : Fin n → Pt s .euclidean → ℝ) (hφ : ∀ i, φ i ∈ entrySpace O i),
      Bc (fun i y => (φ i y : ℂ)) = ((B fun i => ⟨φ i, hφ i⟩ : ℝ) : ℂ) :=
    fun φ hφ => hBB fun i => ⟨φ i, hφ i⟩
  have hext : IsDistribExtending B T := by
    refine ⟨hTord.1, fun φ hφ => ?_⟩
    obtain ⟨hF, hv⟩ := hTval φ hφ
    have hent : ∀ i, φ i ∈ entrySpace O i := fun i => mem_componentSpace_of_mem_testFns (hφ i)
    exact ⟨hent, hF, hv.trans (hagree φ hent)⟩
  have huniq : ∀ T', IsDistribExtending B T' → T' = T := by
    intro T' hT'
    refine hTuniq T' hT'.1 fun φ hφ => ?_
    obtain ⟨hent, hF, hv⟩ := hT'.2 φ hφ
    exact ⟨hF, hv.trans (hagree φ hent).symm⟩
  refine ⟨fun F => ⟨(hProj s n ρ O hO).2 F, ?_, fun χ hχ => ?_⟩, ⟨T, hext, huniq⟩,
    fun T' hT' => ?_⟩
  · obtain ⟨χ, hχ, h1⟩ := (hProj s n ρ O hO).1 (closedSupport F.1) F.2.2.1 F.2.2.2
    exact ⟨χ, hχ, h1⟩
  · exact ⟨cutoffPartialSum (4 * ρ) χ F.1,
      fun t => cutoffPartialSum_isFiniteTensorSumWithin hMode hProd hOps hn hρ
        (fun i => (hOi i).1) hχ.1 F.1 t,
      hConv s n ρ O hO F χ hχ⟩
  · obtain rfl := huniq T' hT'
    exact ⟨fun F χ hχ => (hTF F χ hχ).2, hTord⟩
end YangMills.Construction.AmbientPoints.BoundedFormDistrib
