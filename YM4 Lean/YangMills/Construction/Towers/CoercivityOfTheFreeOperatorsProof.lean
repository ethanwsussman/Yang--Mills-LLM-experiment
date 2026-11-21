import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.Towers.SandwichesOfTheFreeOperatorsInCoefficients
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace Tower.FreeCoercivity
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeResolvents
open YangMills.Construction.Tower.PlaneWaves (freqBox)
open YangMills.Construction.Coercivity
open YangMills.Construction.Tower.RealFrequencyFamily
open YangMills.Construction.Tower.FreeSymbolCoefficients
open YangMills.Construction.Tower.FreeSandwiches
section InnerProducts
variable {J : Type} [Finite J] (w : J → ℝ)
omit [Finite J] in
theorem wInner_eq_sum [Fintype J] (u v : J → ℂ) :
    wInner w u v = ∑ i, (w i : ℂ) * (conj (u i) * v i) := by
  simp only [wInner, PeriodicOperators.wPairing, tsum_fintype]
theorem wInner_add_right (u v x : J → ℂ) :
    wInner w u (v + x) = wInner w u v + wInner w u x := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem wInner_sub_right (u v x : J → ℂ) :
    wInner w u (v - x) = wInner w u v - wInner w u x := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem wInner_smul_right (c : ℂ) (u v : J → ℂ) :
    wInner w u (c • v) = c * wInner w u v := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem wInner_add_left (u v x : J → ℂ) :
    wInner w (u + v) x = wInner w u x + wInner w v x := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
theorem wInner_smul_left (c : ℂ) (u v : J → ℂ) :
    wInner w (c • u) v = conj c * wInner w u v := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
end InnerProducts
section SelfAdjoint
variable {I : PeriodicData}
theorem isSelfAdjointQuotHom_add [Finite I.UnitQuot] {A B : QuotHom I I}
    (hA : IsSelfAdjointQuotHom A) (hB : IsSelfAdjointQuotHom B) : IsSelfAdjointQuotHom (A + B) := by
  intro u v
  simp only [LinearMap.add_apply, wInner_add_left, wInner_add_right, hA u v, hB u v]
theorem isSelfAdjointQuotHom_real_smul [Finite I.UnitQuot] {A : QuotHom I I}
    (hA : IsSelfAdjointQuotHom A) (c : ℝ) : IsSelfAdjointQuotHom ((c : ℂ) • A) := by
  intro u v
  simp only [LinearMap.smul_apply, wInner_smul_left, wInner_smul_right, hA u v,
    Complex.conj_ofReal]
theorem isSelfAdjointQuotHom_scalar [Finite I.UnitQuot] (c : ℝ) :
    IsSelfAdjointQuotHom (scalarQuotHom I c) := by
  intro u v
  simp only [scalarQuotHom, LinearMap.smul_apply, LinearMap.id_apply, wInner_smul_left,
    wInner_smul_right, Complex.conj_ofReal]
theorem loewnerLE_of_forms [Finite I.UnitQuot] {A A' : QuotHom I I} (hA : IsSelfAdjointQuotHom A)
    (hA' : IsSelfAdjointQuotHom A') {q q' : (I.UnitQuot → ℂ) → ℝ}
    (hq : ∀ u, wInner (I.quotWeight 1) u (A u) = (q u : ℂ))
    (hq' : ∀ u, wInner (I.quotWeight 1) u (A' u) = (q' u : ℂ))
    (hle : ∀ u, q u ≤ q' u) : LoewnerLE A A' := by
  have hdiff : ∀ u, wInner (I.quotWeight 1) u ((A' - A) u) = ((q' u - q u : ℝ) : ℂ) := by
    intro u
    rw [LinearMap.sub_apply, wInner_sub_right, hq, hq']
    push_cast
    rfl
  refine ⟨hA, hA', fun u => ?_, fun u => ?_⟩
  · rw [hdiff, Complex.ofReal_im]
  · rw [hdiff, Complex.ofReal_re]
    exact sub_nonneg.2 (hle u)
theorem form_real_smul [Finite I.UnitQuot] {A : QuotHom I I} (c : ℝ) {q : (I.UnitQuot → ℂ) → ℝ}
    (hq : ∀ u, wInner (I.quotWeight 1) u (A u) = (q u : ℂ)) (u : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) u (((c : ℂ) • A) u) = ((c * q u : ℝ) : ℂ) := by
  rw [LinearMap.smul_apply, wInner_smul_right, hq]
  push_cast
  rfl
theorem form_add_scalar_one [Finite I.UnitQuot] {A : QuotHom I I} {q r : (I.UnitQuot → ℂ) → ℝ}
    (hq : ∀ u, wInner (I.quotWeight 1) u (A u) = (q u : ℂ))
    (hr : ∀ u, wInner (I.quotWeight 1) u u = (r u : ℂ)) (u : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) u ((A + scalarQuotHom I 1) u) = ((q u + r u : ℝ) : ℂ) := by
  have hone : scalarQuotHom I 1 u = u := by simp [scalarQuotHom]
  rw [LinearMap.add_apply, hone, wInner_add_right, hq, hr]
  push_cast
  rfl
theorem form_scalar [Finite I.UnitQuot] (c : ℝ) {r : (I.UnitQuot → ℂ) → ℝ}
    (hr : ∀ u, wInner (I.quotWeight 1) u u = (r u : ℂ)) (u : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) u (scalarQuotHom I c u) = ((c * r u : ℝ) : ℂ) := by
  simp only [scalarQuotHom, LinearMap.smul_apply, LinearMap.id_apply, wInner_smul_right, hr]
  push_cast
  rfl
theorem quotWeight_pos (hQ : Quotients.QuotientTransposeNorm) {I : PeriodicData}
    (hI : IsPeriodic I) (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.quotWeight_one_pos <;> assumption
theorem quotHomAdjoint_eq (hQ : Quotients.QuotientTransposeNorm) {I I' : PeriodicData}
    (hI : IsPeriodic I) {A : QuotHom I I'} {B : QuotHom I' I}
    (hAB : IsAdjointQuotHom A B) : quotHomAdjoint A = B := by
  classical
  have hspec : IsAdjointQuotHom A (quotHomAdjoint A) := Classical.epsilon_spec ⟨B, hAB⟩
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  refine LinearMap.ext fun v => funext fun c => ?_
  have hc : wInner (I.quotWeight 1) (quotHomAdjoint A v) (Pi.single c 1) =
      wInner (I.quotWeight 1) (B v) (Pi.single c 1) := by
    rw [← hspec (Pi.single c 1) v, ← hAB (Pi.single c 1) v]
  simp only [wInner_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hc
  have hw : ((I.quotWeight 1 c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (quotWeight_pos hQ hI c).ne'
  exact (starRingEnd ℂ).injective (mul_left_cancel₀ hw hc)
end SelfAdjoint
theorem bondSobolevSq_eq_add {ι : Type} (s : Finset ι) (D : ι → ℝ) (b : ι → Fin 4 → ℂ) :
    bondSobolevSq s D b = bondDirichlet s D b + ∑ i ∈ s, bondNormSq b i := by
  simp only [bondSobolevSq, bondDirichlet, add_mul, one_mul, Finset.sum_add_distrib]
theorem siteSobolevSq_eq_add {ι : Type} (s : Finset ι) (D : ι → ℝ) (l : ι → ℂ) :
    siteSobolevSq s D l = siteDirichlet s D l + ∑ i ∈ s, ‖l i‖ ^ 2 := by
  simp only [siteSobolevSq, siteDirichlet, add_mul, one_mul, Finset.sum_add_distrib]
theorem mem_imStrip_of_real {κ : Fin 4 → ℂ} (hκ : κ ∈ realDualPoints) {δ : ℝ} (hδ : 0 < δ) :
    κ ∈ strictImStrip δ := by
  have him : PeriodicOperators.imVec κ = 0 := by
    funext μ
    exact hκ μ
  simpa [strictImStrip, him, TorusMetric.euclidNormVec] using hδ
theorem symbolIsMatrixAt_of_summable (hS : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) {κ : Fin 4 → ℂ} (hs : SymbolSummableAt I I' T κ) :
    SymbolIsMatrixAt I I' T κ := by
  have P := (hS.2.1 I I' hI hI').2.1 T κ hT hs
  exact ⟨hs, P.factorsThroughQuot, P.carrierEntry_symbolHom⟩
theorem isFiniteRangeEntire_of_everyRate (hS : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : FreeOperators.HasFiniteRangeEveryRate I I' T) :
    IsFiniteRangeEntire I I' T :=
  ⟨hT.1, hT.2.1, (hS.2.1 I I' hI hI').1.finiteRange T hT.1 hT.2.1⟩
theorem symbolSummableAt_of_real (hSym : Symbols.Claim)
    (hId : IdKernelFacts.Claim) {I : PeriodicData} (hI : IsPeriodic I)
    {T : I.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I T) {κ : Fin 4 → ℂ}
    (hκ : κ ∈ realDualPoints) : SymbolSummableAt I I T κ := by
  obtain ⟨δ, hδ⟩ := ((hId I hI).2.2.2.2.2.1 I hI T hT).exists_rate
  exact (hSym.1 I I I hI hI hI T T δ hT hδ hT hδ).summable_on_strip κ (mem_imStrip_of_real hκ hδ.1)
theorem freeOperatorsCoercive (hFam : FiniteFamilyCoercivity)
    (hNum : FamilyBoundsHold) (hForms : FreeSymbolForms) (hSand : SandwichFacts)
    (hFree : FreeOperators.FreeOperatorsArePeriodic) (hTow : TowerIndexSets.Claim)
    (hS : StripSymbols.Claim) (hQ : Quotients.QuotientTransposeNorm)
    (hRes : FreeResolventRoots) (hId : IdKernelFacts.Claim) (hSym : Symbols.Claim) :
    FreeOperatorsCoercive := by
  obtain ⟨cXi, hcXi, cY, hcY, cC, hcC, H⟩ := hFam ((2 / Real.pi) ^ 4) ((2 / Real.pi) ^ 5)
    (4 * Real.pi ^ 2) (Real.pi ^ 2 / 48) (by positivity) (by positivity) (by positivity)
    (by positivity)
  refine ⟨cXi, hcXi, cY, hcY, cC, hcC, fun L hL k hk => ?_⟩
  have hV₀ := (hTow L hL k 0 (Nat.zero_le k)).1
  have hE₀ := (hTow L hL k 0 (Nat.zero_le k)).2.1
  have hVk := (hTow L hL k k le_rfl).1
  have hEk := (hTow L hL k k le_rfl).2.1
  obtain ⟨hmaps, hops⟩ := hFree.2 L hL k hk
  obtain ⟨-, -, -, PE, PV, -, -⟩ := hRes L hL k hk
  have pE : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) (edgeResolvent L k) := by
    have heq : edgeResolvent L k = matFunKernel (colourEdges L k 0) (colourEdges L k 0)
        (edgePowMatrix L k (-1)) := PE.inverse_eq
    rw [heq]
    exact PE.periodic (-1) (by simp [resolventExponents])
  have pV : IsPeriodicKernel (colourVertices L k 0) (colourVertices L k 0) (vertexResolvent L k) := by
    have heq : vertexResolvent L k = matFunKernel (colourVertices L k 0) (colourVertices L k 0)
        (vertexPowMatrix L k (-1)) := PV.inverse_eq
    rw [heq]
    exact PV.periodic (-1) (by simp [resolventExponents])
  have op : FiniteRangeOperators L k :=
    ⟨isFiniteRangeEntire_of_everyRate hS hE₀ hE₀ hops.K,
      isFiniteRangeEntire_of_everyRate hS hV₀ hV₀ hops.Delta,
      isFiniteRangeEntire_of_everyRate hS hE₀ hE₀ hops.Xi,
      isFiniteRangeEntire_of_everyRate hS hV₀ hV₀ hops.Y,
      isFiniteRangeEntire_of_everyRate hS hE₀ hEk hmaps.edgeAverage.finite_range,
      isFiniteRangeEntire_of_everyRate hS hV₀ hVk hmaps.vertexAverage.finite_range,
      isFiniteRangeEntire_of_everyRate hS hEk hE₀ hops.edgeAverage_transpose,
      isFiniteRangeEntire_of_everyRate hS hVk hV₀ hops.vertexAverage_transpose⟩
  refine ⟨op, pE, pV, fun κ hκ => ⟨?_, ?_⟩⟩
  · have mat : ∀ {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ},
        IsPeriodic I → IsPeriodic I' →
        IsFiniteRangeEntire I I' T → SymbolIsMatrixAt I I' T κ :=
      fun hI hI' h => symbolIsMatrixAt_of_summable hS hI hI' h.1 (h.2.2 κ (mem_univ κ))
    exact ⟨mat hE₀ hE₀ op.K, mat hV₀ hV₀ op.Delta, mat hE₀ hE₀ op.Xi, mat hV₀ hV₀ op.Y,
      mat hE₀ hEk op.Q, mat hV₀ hVk op.R, mat hEk hE₀ op.Qt, mat hVk hV₀ op.Rt,
      symbolIsMatrixAt_of_summable hS hE₀ hE₀ pE (symbolSummableAt_of_real hSym hId hE₀ pE hκ),
      symbolIsMatrixAt_of_summable hS hV₀ hV₀ pV (symbolSummableAt_of_real hSym hId hV₀ pV hκ)⟩
  · obtain ⟨z, hz⟩ := hNum L hL k hk κ hκ
    obtain ⟨hb, hl, hcb, hcs⟩ := H _ _ z _ _ _ _ _ hz
    have F := hForms L hL k hk κ hκ
    have W := hSand L hL k hk κ hκ
    have : Finite (colourEdges L k 0).UnitQuot := hE₀.finite_quot
    have : Finite (colourVertices L k 0).UnitQuot := hV₀.finite_quot
    have : Finite (colourEdges L k k).UnitQuot := hEk.finite_quot
    have : Finite (colourVertices L k k).UnitQuot := hVk.finite_quot
    have adjQ : quotHomAdjoint
        (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ) =
        symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ :=
      quotHomAdjoint_eq hQ hE₀ fun u v => W.edge_adjoint u v
    have adjR : quotHomAdjoint
        (symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ) =
        symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ :=
      quotHomAdjoint_eq hQ hV₀ fun u v => W.vertex_adjoint u v
    have sK : IsSelfAdjointQuotHom (edgeSymbolAddOne L k κ) :=
      isSelfAdjointQuotHom_add (fun u v => F.K_selfAdjoint u v) (isSelfAdjointQuotHom_scalar 1)
    have sD : IsSelfAdjointQuotHom (vertexSymbolAddOne L k κ) :=
      isSelfAdjointQuotHom_add (fun u v => F.Delta_selfAdjoint u v) (isSelfAdjointQuotHom_scalar 1)
    have qK : ∀ u, wInner ((colourEdges L k 0).quotWeight 1) u (edgeSymbolAddOne L k κ u) =
        ((∑ a, bondSobolevSq (freqBox L k) (symbolSquares L k κ) (edgeColourCoeffs L k u a) : ℝ) : ℂ) := by
      intro u
      have h := form_add_scalar_one (fun u => F.edge_K u) (fun u => F.edge_norm_sq u) u
      simp only [bondSobolevSq_eq_add, Finset.sum_add_distrib]
      exact h
    have qD : ∀ u, wInner ((colourVertices L k 0).quotWeight 1) u (vertexSymbolAddOne L k κ u) =
        ((∑ a, siteSobolevSq (freqBox L k) (symbolSquares L k κ) (vertexColourCoeffs L k u a) : ℝ) : ℂ) := by
      intro u
      have h := form_add_scalar_one (fun u => F.vertex_Delta u) (fun u => F.vertex_norm_sq u) u
      simp only [siteSobolevSq_eq_add, Finset.sum_add_distrib]
      exact h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine loewnerLE_of_forms (isSelfAdjointQuotHom_real_smul sK cXi) (fun u v => F.Xi_selfAdjoint u v)
        (form_real_smul cXi qK) (fun u => F.edge_Xi u) fun u => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun a _ => (hb _).1
    · refine loewnerLE_of_forms (fun u v => F.Xi_selfAdjoint u v) sK (fun u => F.edge_Xi u) qK fun u => ?_
      exact Finset.sum_le_sum fun a _ => (hb _).2
    · refine loewnerLE_of_forms (isSelfAdjointQuotHom_real_smul sD cY) (fun u v => F.Y_selfAdjoint u v)
        (form_real_smul cY qD) (fun u => F.vertex_Y u) fun u => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun a _ => (hl _).1
    · refine loewnerLE_of_forms (fun u v => F.Y_selfAdjoint u v) sD (fun u => F.vertex_Y u) qD fun u => ?_
      exact Finset.sum_le_sum fun a _ => (hl _).2
    · have heq : edgeResolventConjugate L k κ = edgeSandwich L k κ := by
        rw [edgeResolventConjugate, adjQ]
        rfl
      rw [heq]
      refine loewnerLE_of_forms (isSelfAdjointQuotHom_scalar cC) (fun u v => W.edge_hermitian u v)
        (form_scalar cC fun u => W.edge_norm u) (fun u => W.edge_form u) fun u => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_right (hcb μ) (by positivity)
    · have heq : vertexResolventConjugate L k κ = vertexSandwich L k κ := by
        rw [vertexResolventConjugate, adjR]
        rfl
      rw [heq]
      refine loewnerLE_of_forms (isSelfAdjointQuotHom_scalar cC) (fun u v => W.vertex_hermitian u v)
        (form_scalar cC fun u => W.vertex_norm u) (fun u => W.vertex_form u) fun u => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right hcs (by positivity)
end Tower.FreeCoercivity
end YangMills.Construction
end
