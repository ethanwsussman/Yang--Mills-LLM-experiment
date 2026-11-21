import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.NormOfTheColourCoefficients
import YangMills.Construction.Towers.TheInversesThatFormTheResponseProof
import YangMills.Construction.Towers.TheNormsOfTheResponseAtAPoint
import YangMills.Construction.Towers.TheResponseOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseNormBounds
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.PlaneWaveCalculus (posEdgeAt topEdgeComponent topVertexElement)
open YangMills.Construction.Tower.FreeResolvents (edgeResolventSqrt resolventExponents trivialRescaledOperators)
open YangMills.Construction.Tower.ResponseInverses (xiHat)
open YangMills.Construction.Tower.ResponseProperties (responseSymbolForm smoothedDivergence)
open YangMills.Construction.Tower.ResponseOperators (covSymbol respSymbol)
open YangMills.Construction.Tower.FreeStrip (IsAdmissiblePair addScalar)
theorem sum_smul_pauliFamily_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliNorm_sum_smul_sq (hN : PauliCoefficientNorm.Claim) (x : Fin 3 → ℂ) :
    pauliNorm (∑ a, x a • Matrices.ComplexMatrix2.pauliFamily a) ^ 2 = ∑ a, ‖x a‖ ^ 2 := by
  have h := hN.1
  let X : Matrices.ComplexMatrix2.traceless := ⟨_, sum_smul_pauliFamily_mem_traceless x⟩
  have e₁ := h.1 X X x x rfl rfl
  have e₂ : pauliNorm (X : Matrices.ComplexMatrix2) = _ := h.2.1 X
  have e₃ : (PauliCoefficientNorm.halfTraceInner X X).re = ∑ a, ‖x a‖ ^ 2 := by
    rw [e₁, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  show pauliNorm (X : Matrices.ComplexMatrix2) ^ 2 = _
  rw [e₂, e₃, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
section Classes
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem exists_int_coords (L k : ℕ) (x : FullSpace.Vertex L k k) :
    ∃ n : Fin 4 → ℤ, (x : InfiniteLattice.AmbientSpace) = castVec n := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.vertex_integral <;> assumption
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def edgeClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
def vertexClass (L k : ℕ) (a : Fin 3) : (colourVertices L k k).UnitQuot :=
  (colourVertices L k k).mkQuot 1 (a, 0)
theorem exists_eq_edgeClass (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (c : (colourEdges L k k).UnitQuot) :
    ∃ a μ, c = edgeClass L k a μ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.exists_unitEdgeClass <;> assumption
theorem edgeClass_inj (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {a a' : Fin 3} {μ μ' : Fin 4}
    (h : edgeClass L k a μ = edgeClass L k a' μ') : a = a' ∧ μ = μ' := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.unitEdgeClass_injective <;> assumption
theorem exists_eq_vertexClass (hT : TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (c : (colourVertices L k k).UnitQuot) :
    ∃ a, c = vertexClass L k a := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.exists_unitVertexClass <;> assumption
theorem vertexClass_inj {a a' : Fin 3} (h : vertexClass L k a = vertexClass L k a') : a = a' := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.unitVertexClass_injective <;> assumption
theorem quotWeight_edges_eq_one (c : (colourEdges L k k).UnitQuot) :
    (colourEdges L k k).quotWeight 1 c = 1 := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.edge_quotWeight <;> assumption
theorem quotWeight_vertices_eq_one (c : (colourVertices L k k).UnitQuot) :
    (colourVertices L k k).quotWeight 1 c = 1 := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.vertex_quotWeight <;> assumption
theorem wNorm_edges_eq (hN : PauliCoefficientNorm.Claim)
    (hT : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (z : (colourEdges L k k).UnitQuot → ℂ) :
    wNorm ((colourEdges L k k).quotWeight 1) z = pauliFamilyNorm (topEdgeComponent L k z) := by
  let e : Fin 3 × Fin 4 ≃ (colourEdges L k k).UnitQuot :=
    Equiv.ofBijective (fun i => edgeClass L k i.1 i.2)
      ⟨fun i j h => Prod.ext (edgeClass_inj hT hL hk h).1 (edgeClass_inj hT hL hk h).2,
        fun c => by
          obtain ⟨a, μ, rfl⟩ := exists_eq_edgeClass hT hL hk c
          exact ⟨(a, μ), rfl⟩⟩
  rw [wNorm, pauliFamilyNorm]
  congr 1
  rw [← e.tsum_eq, tsum_fintype, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h := pauliNorm_sum_smul_sq hN fun a => z (edgeClass L k a μ)
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [quotWeight_edges_eq_one, one_mul]
  rfl
theorem wNorm_vertices_eq (hN : PauliCoefficientNorm.Claim)
    (hT : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (g : (colourVertices L k k).UnitQuot → ℂ) :
    wNorm ((colourVertices L k k).quotWeight 1) g = pauliNorm (topVertexElement L k g) := by
  let e : Fin 3 ≃ (colourVertices L k k).UnitQuot :=
    Equiv.ofBijective (vertexClass L k)
      ⟨fun _ _ h => vertexClass_inj h, fun c => by
        obtain ⟨a, rfl⟩ := exists_eq_vertexClass hT hL hk c
        exact ⟨a, rfl⟩⟩
  have h := pauliNorm_sum_smul_sq hN fun a => g (vertexClass L k a)
  have e₁ : (∑' c, (colourVertices L k k).quotWeight 1 c * ‖g c‖ ^ 2) =
      pauliNorm (topVertexElement L k g) ^ 2 := by
    rw [← e.tsum_eq, tsum_fintype]
    refine Eq.trans ?_ h.symm
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [quotWeight_vertices_eq_one, one_mul]
    rfl
  rw [wNorm, e₁]
  exact Real.sqrt_sq (Real.sqrt_nonneg _)
end Classes
theorem quotHomInverse_eq_of_sandwich {I : PeriodicData} {G X S : QuotHom I I}
    (hS : S = (G.comp X).comp G) (hSi : IsInvertibleQuotHom S) (hX : IsInvertibleQuotHom X)
    (g : I.UnitQuot → ℂ) :
    quotHomInverse X g = G (quotHomInverse S (G g)) := by
  have hinj : Function.Injective G := fun u v e => by
    refine (hSi (S u)).unique rfl ?_
    rw [hS]
    simp [e]
  obtain ⟨y, hy⟩ : ∃ y, y = quotHomInverse S (G g) := ⟨_, rfl⟩
  have h₁ : S y = G g := by
    rw [hy]
    exact hSi.apply_quotHomInverse _
  rw [hS] at h₁
  have h₂ : X (G y) = g := hinj h₁
  rw [← hy]
  exact (hX g).unique (hX.apply_quotHomInverse g) h₂
theorem wNorm_apply_le (hH : HomNorm.Claim) {I I' : PeriodicData}
    (pI : IsPeriodic I) (pI' : IsPeriodic I') {M : QuotHom I I'} {C c : ℝ}
    (hC : 0 ≤ C) (hM : quotHomNorm M ≤ ENNReal.ofReal C) {f : I.UnitQuot → ℂ}
    (hf : wNorm (I.quotWeight 1) f ≤ c) :
    wNorm (I'.quotWeight 1) (M f) ≤ C * c := by
  have h := ((hH I I' pI pI').2.2.2.2.2.2.1 I pI).1 M f
  have hm := ENNReal.toReal_le_of_le_ofReal hC hM
  have hn : 0 ≤ wNorm (I.quotWeight 1) f := Real.sqrt_nonneg _
  exact h.trans (mul_le_mul hm hf hn hC)
theorem quotHomNorm_sub_id_le (hH : HomNorm.Claim) {I : PeriodicData}
    (pI : IsPeriodic I) {M : QuotHom I I} {C : ℝ} (hC : 0 ≤ C)
    (hM : quotHomNorm M ≤ ENNReal.ofReal C) :
    quotHomNorm (M - LinearMap.id) ≤ ENNReal.ofReal (C + 1) := by
  have h := hH I I pI pI
  have hs := h.2.2.2.2.2.1
  have hu := h.2.2.2.2.2.2.2.1.2
  rw [(h.2.2.2.2.2.2.2.2 M LinearMap.id 0).1]
  refine (hs.2.2.2.1 _ _).trans ?_
  rw [hs.2.2.2.2, ENNReal.ofReal_add hC zero_le_one]
  simp only [norm_neg, norm_one, ENNReal.ofReal_one, mul_one]
  exact add_le_add hM hu
theorem addScalar_zero (I : PeriodicData) (A : I.Carrier → I.Carrier → ℂ) : addScalar I 0 A = A := by apply _root_.YangMills.Construction.Tower.ResponseInverses.addScalar_zero <;> assumption
theorem pointwise_bounds (hI : TowerIndexSets.Claim)
    (hT : TowerTranslations.Claim) (hN : PauliCoefficientNorm.Claim)
    (hH : HomNorm.Claim) (hS : StripSymbols.Claim)
    (hF : FreeOperators.FreeOperatorsArePeriodic) (hP : FreeResolvents.FreeResolventRoots) {δ₀ C : ℝ}
    (hC : 1 ≤ C) (hadm : IsAdmissiblePair δ₀ C) {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hR : ResponseOperators.AtLevel δ₀ L k) {p : Fin 4 → ℂ}
    (hp : p ∈ imStrip (2 * δ₀)) (ε : (colourEdges L k k).UnitQuot → ℂ) :
    wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε) ≤
        C ^ 5 * pauliFamilyNorm (topEdgeComponent L k ε) ∧
      pauliFamilyNorm (topEdgeComponent L k (ResponseProperties.defectSymbol L k p ε)) ≤
        (C + 1) * pauliFamilyNorm (topEdgeComponent L k ε) ∧
      pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)) ≤
        C ^ 6 * pauliFamilyNorm (topEdgeComponent L k ε) := by
  have hC₀ : (0 : ℝ) ≤ C := zero_le_one.trans hC
  obtain ⟨pS, pB, -⟩ := hI L hL k 0 (Nat.zero_le k)
  obtain ⟨pTS, pTB, -⟩ := hI L hL k k le_rfl
  have hAs := hadm.2.2 L hL k hk
  have hB := hAs.1
  have hV := hAs.2 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨O, -, hDO, hOn⟩ := hR.near
  have hpO : p ∈ O := hDO hp
  have perG : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0)
      (edgeResolventSqrt L k) :=
    (hP L hL k hk).2.2.2.1.periodic (-(1 / 2)) (by simp [resolventExponents])
  have forG := hB.edge_sqrt.1 p hp
  have perXi : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).Xi := (hF.2 L hL k hk).2.Xi.1
  have forXi := hR.free_summable.xi p (mem_univ p)
  have facts := fun {I I' : PeriodicData} (a : IsPeriodic I) (b : IsPeriodic I') =>
    (hS.2.1 I I' a b).2.1
  obtain ⟨-, perGX, forGX, eGX⟩ :=
    (facts pB pB _ p perG forG).comp _ pB _ perXi forXi
  obtain ⟨-, -, -, eS⟩ := (facts pB pB _ p perGX forGX).comp _ pB _ perG forG
  obtain ⟨-, -, -, hSq⟩ := hV.edge_add
  rw [addScalar_zero] at hSq
  obtain ⟨hSi, hSn⟩ := hSq p hp
  have hXi : IsInvertibleQuotHom (xiHat L k p) := hOn.xi_isInvertible p hpO
  have hroot := fun g => quotHomInverse_eq_of_sandwich
    (G := symbolHom _ _ (edgeResolventSqrt L k) p) (X := xiHat L k p)
    (eS.trans (by rw [eGX]; rfl)) hSi hXi g
  obtain ⟨-, -, hCq⟩ := hV.edge_avg
  rw [addScalar_zero] at hCq
  have hCn : quotHomNorm (quotHomInverse (covSymbol L k p)) ≤ ENNReal.ofReal C :=
    (hCq.2 p hp).2
  set e := pauliFamilyNorm (topEdgeComponent L k ε) with he
  have hε : wNorm ((colourEdges L k k).quotWeight 1) ε ≤ e :=
    (wNorm_edges_eq hN hT hL hk ε).le
  have h₀ : 0 ≤ e := Real.sqrt_nonneg _
  have hGn : quotHomNorm (symbolHom _ _ (edgeResolventSqrt L k) p) ≤ ENNReal.ofReal C :=
    hB.edge_sqrt.2 p hp
  have h₁ := wNorm_apply_le hH pTB pTB hC₀ hCn hε
  have h₂ := wNorm_apply_le hH pTB pB hC₀ (hB.edge_avgT.2 p hp) h₁
  have h₃ := wNorm_apply_le hH pB pB hC₀ hGn h₂
  have h₄ := wNorm_apply_le hH pB pB hC₀ hSn h₃
  have h₅ := wNorm_apply_le hH pB pB hC₀ hGn h₄
  have eb : responseSymbolForm L k p ε = symbolHom _ _ (edgeResolventSqrt L k) p
      (quotHomInverse (symbolHom _ _ (compKernel (compKernel (edgeResolventSqrt L k)
          (trivialRescaledOperators L k).Xi) (edgeResolventSqrt L k)) p)
        (symbolHom _ _ (edgeResolventSqrt L k) p
          (symbolHom _ _ (trivialRescaledOperators L k).Qt p
            (quotHomInverse (covSymbol L k p) ε)))) := by
    have e₁ : responseSymbolForm L k p ε = respSymbol L k p ε := rfl
    rw [e₁, hOn.resp_eq p hpO]
    exact hroot _
  have hb : wNorm ((colourEdges L k 0).quotWeight 1) (responseSymbolForm L k p ε) ≤ C ^ 5 * e := by
    rw [eb]
    refine h₅.trans (le_of_eq ?_)
    ring
  have hn : pauliFamilyNorm (topEdgeComponent L k (ResponseProperties.defectSymbol L k p ε)) ≤
      (C + 1) * e := by
    rw [← wNorm_edges_eq hN hT hL hk]
    have e₁ : ResponseProperties.defectSymbol L k p ε = ResponseOperators.defectSymbol L k p ε := rfl
    rw [e₁, hOn.defect_eq p hpO]
    exact wNorm_apply_le hH pTB pTB (by linarith) (quotHomNorm_sub_id_le hH pTB hC₀ hCn) hε
  have perD : IsPeriodicKernel (colourEdges L k 0) (colourVertices L k 0)
      (PlaneWaveCalculus.vertexCoboundaryT L k 0) :=
    (hF.2 L hL k hk).2.vertexCoboundary_transpose 0 (Nat.zero_le k) |>.1
  have forD : SymbolSummableAt (colourEdges L k 0) (colourVertices L k 0)
      (PlaneWaveCalculus.vertexCoboundaryT L k 0) p :=
    (hS.2.1 _ _ pB pS).1.finiteRange _ perD
      ((hF.2 L hL k hk).2.vertexCoboundary_transpose 0 (Nat.zero_le k) |>.2.1) p (mem_univ p)
  obtain ⟨-, -, -, eD⟩ := (facts pB pS _ p perD forD).comp _ pB _ perG forG
  have hγ : pauliNorm (topVertexElement L k (smoothedDivergence L k p ε)) ≤ C ^ 6 * e := by
    rw [← wNorm_vertices_eq hN hT hL hk]
    have e₁ : smoothedDivergence L k p ε =
        symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R p
        (symbolHom (colourEdges L k 0) (colourVertices L k 0)
            (compKernel (PlaneWaveCalculus.vertexCoboundaryT L k 0)
            (edgeResolventSqrt L k)) p
          (quotHomInverse (symbolHom (colourEdges L k 0) (colourEdges L k 0)
              (compKernel (compKernel (edgeResolventSqrt L k)
              (trivialRescaledOperators L k).Xi) (edgeResolventSqrt L k)) p)
            (symbolHom (colourEdges L k 0) (colourEdges L k 0) (edgeResolventSqrt L k) p
              (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p
                (quotHomInverse (covSymbol L k p) ε))))) := by
      rw [eD]
      show symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R p
        (symbolHom (colourEdges L k 0) (colourVertices L k 0)
          (PlaneWaveCalculus.vertexCoboundaryT L k 0) p (responseSymbolForm L k p ε)) = _
      rw [eb]
      rfl
    rw [e₁]
    have h₆ := wNorm_apply_le hH pB pS hC₀ (hB.diffT_edge_sqrt.2.2 p hp) h₄
    have h₇ := wNorm_apply_le hH pS pTS hC₀ (hB.vertex_avg.2 p hp) h₆
    refine h₇.trans (le_of_eq ?_)
    ring
  exact ⟨hb, hn, hγ⟩
theorem claim_holds (hI : TowerIndexSets.Claim)
    (hT : TowerTranslations.Claim) (hN : PauliCoefficientNorm.Claim)
    (hH : HomNorm.Claim) (hS : StripSymbols.Claim)
    (hF : FreeOperators.FreeOperatorsArePeriodic) (hP : FreeResolvents.FreeResolventRoots)
    (hA : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) : Claim := by
  obtain ⟨-, -, δ₀, hδ, C, -, -, hC, hadm⟩ := hA
  obtain ⟨δ₁, hδ₁, hRall⟩ := hR
  obtain rfl : δ₁ = δ₀ := Part.mem_unique hδ₁ hδ
  refine ⟨C ^ 6 + C + 1, ?_⟩
  intro δ hδ' L hL k hk p hp ε
  obtain rfl : δ = δ₁ := Part.mem_unique hδ' hδ
  obtain ⟨hb, hn, hγ⟩ := pointwise_bounds hI hT hN hH hS hF hP hC hadm hL hk (hRall L hL k hk) hp.1 ε
  have h₀ : 0 ≤ pauliFamilyNorm (topEdgeComponent L k ε) := Real.sqrt_nonneg _
  have h₅ : C ^ 5 ≤ C ^ 6 := pow_le_pow_right₀ hC (by norm_num)
  have h₆ : 0 ≤ C ^ 6 := by positivity
  refine ⟨hb.trans (mul_le_mul_of_nonneg_right (by linarith) h₀),
    hn.trans (mul_le_mul_of_nonneg_right (by linarith) h₀),
    hγ.trans (mul_le_mul_of_nonneg_right (by linarith) h₀)⟩
end YangMills.Construction.Tower.ResponseNormBounds
end
