import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.TranslationsOnTheIndexSetsOfATower
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbolsProof
import YangMills.Construction.Towers.CoercivityOfTheFreeOperatorsProof
import YangMills.Construction.Towers.PlaquettesOfABondProof
import YangMills.Construction.Towers.TransposesAndRelationsOfTheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.FreeSymbolCoefficients
open PeriodicOperators
open PeriodicOperators.Quotients (conjKernel)
open FreeResolvents
open InfiniteLattice (AmbientSpace)
open PlaneWaves hiding vertexWeight
open PlaneWaveCalculus (posEdgeAt topEdgeComponent topVertexElement EdgeCoeffFacts
  VertexCoeffFacts MultiplierMatrixFacts SymbolFormulas WeightRelations SmoothingSymbols)
open Coercivity
open RealFrequencyFamily
section InnerProducts
variable {J : Type} (w : J → ℝ)
theorem wInner_eq_fintype_sum [Fintype J] (f g : J → ℂ) :
    wInner w f g = ∑ i, (w i : ℂ) * (conj (f i) * g i) := by
  simp only [wInner, PeriodicOperators.wPairing, tsum_fintype]
theorem wInner_self_eq_tsum (h : J → ℂ) :
    wInner w h h = ((∑' i, w i * ‖h i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun i => ?_
  rw [Complex.conj_mul']
  push_cast
  ring
variable [Finite J]
theorem wInner_add_right (f g g' : J → ℂ) :
    wInner w f (g + g') = wInner w f g + wInner w f g' := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_fintype_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem wInner_sub_right (f g g' : J → ℂ) :
    wInner w f (g - g') = wInner w f g - wInner w f g' := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_fintype_sum, ← Finset.sum_sub_distrib, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem wInner_add_left (f f' g : J → ℂ) :
    wInner w (f + f') g = wInner w f g + wInner w f' g := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_fintype_sum, ← Finset.sum_add_distrib, Pi.add_apply, map_add]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem wInner_sub_left (f f' g : J → ℂ) :
    wInner w (f - f') g = wInner w f g - wInner w f' g := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_fintype_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem conj_wInner (f g : J → ℂ) :
    conj (wInner w f g) = wInner w g f := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_fintype_sum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => by ring
end InnerProducts
section SelfAdjointMaps
variable {I I' S T B : PeriodicData}
def IsSelfAdjointMap (M : QuotHom I I) : Prop :=
  ∀ f g : I.UnitQuot → ℂ,
    wInner (I.quotWeight 1) (M f) g = wInner (I.quotWeight 1) f (M g)
def IsAdjointPair (M : QuotHom I I') (A : QuotHom I' I) : Prop :=
  ∀ (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ),
    wInner (I'.quotWeight 1) g (M f) = wInner (I.quotWeight 1) (A g) f
theorem IsAdjointPair.symm_form [Finite I.UnitQuot] [Finite I'.UnitQuot] {M : QuotHom I I'}
    {A : QuotHom I' I} (h : IsAdjointPair M A) (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ) :
    wInner (I'.quotWeight 1) (M f) g = wInner (I.quotWeight 1) f (A g) := by
  rw [← conj_wInner, h f g, conj_wInner]
theorem isSelfAdjointMap_comp_self {A B : QuotHom I I} (hB : IsSelfAdjointMap B)
    (hA : A = B.comp B) : IsSelfAdjointMap A := by
  subst hA
  intro f g
  change wInner _ (B (B f)) g = wInner _ f (B (B g))
  rw [hB (B f) g, hB f (B g)]
theorem wInner_comp_self {A B : QuotHom I I} (hB : IsSelfAdjointMap B) (hA : A = B.comp B)
    (f : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) f (A f) = wInner (I.quotWeight 1) (B f) (B f) := by
  subst hA
  exact (hB f (B f)).symm
theorem edge_decomposition [Finite I.UnitQuot] [Finite S.UnitQuot] [Finite T.UnitQuot]
    [Finite B.UnitQuot] {A X : QuotHom I I} {D : QuotHom S I} {Dt : QuotHom I S}
    {R : QuotHom S T} {Rt : QuotHom T S} {Q : QuotHom I B} {Qt : QuotHom B I}
    (hX : X = A - (D.comp Rt).comp (R.comp Dt) + Qt.comp Q)
    (hD : IsAdjointPair D Dt) (hR : IsAdjointPair R Rt) (hQ : IsAdjointPair Q Qt)
    (f g : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) f (X g) =
        wInner (I.quotWeight 1) f (A g) -
          wInner (T.quotWeight 1) (R (Dt f)) (R (Dt g)) +
          wInner (B.quotWeight 1) (Q f) (Q g) ∧
      wInner (I.quotWeight 1) (X f) g =
        wInner (I.quotWeight 1) (A f) g -
          wInner (T.quotWeight 1) (R (Dt f)) (R (Dt g)) +
          wInner (B.quotWeight 1) (Q f) (Q g) := by
  have e : ∀ h, X h = A h - D (Rt (R (Dt h))) + Qt (Q h) := fun h => by
    subst hX
    simp
  constructor
  · rw [e, wInner_add_right, wInner_sub_right, hD _ f, ← hR.symm_form, ← hQ.symm_form]
  · rw [e, wInner_add_left, wInner_sub_left, hD.symm_form, ← hR, ← hQ]
theorem vertex_decomposition [Finite I.UnitQuot] [Finite T.UnitQuot] {A X : QuotHom I I}
    {R : QuotHom I T} {Rt : QuotHom T I} (hX : X = A + Rt.comp R) (hR : IsAdjointPair R Rt)
    (f g : I.UnitQuot → ℂ) :
    wInner (I.quotWeight 1) f (X g) =
        wInner (I.quotWeight 1) f (A g) +
          wInner (T.quotWeight 1) (R f) (R g) ∧
      wInner (I.quotWeight 1) (X f) g =
        wInner (I.quotWeight 1) (A f) g +
          wInner (T.quotWeight 1) (R f) (R g) := by
  have e : ∀ h, X h = A h + Rt (R h) := fun h => by
    subst hX
    simp
  constructor
  · rw [e, wInner_add_right, ← hR.symm_form]
  · rw [e, wInner_add_left, ← hR]
theorem applyKernel_linearMapEntry {J J' : Type} [Finite J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (f : J → ℂ) : applyKernel (linearMapEntry M) f = M f := by
  classical
  have := Fintype.ofFinite J
  funext c'
  have hf : f = ∑ c, f c • (Pi.single c 1 : J → ℂ) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, applyKernel,
    tsum_fintype, linearMapEntry]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
theorem quotWeight_pos (hTransposeNorm : Quotients.QuotientTransposeNorm) (hI : IsPeriodic I)
    (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotWeight_pos <;> assumption
theorem isSelfAdjointMap_of_transpose (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic I) {M N : QuotHom I I} (htr : quotHomTranspose N = M)
    (hconj : conjKernel (linearMapEntry M) = linearMapEntry N) : IsSelfAdjointMap M := by
  intro f g
  have := hI.finite_quot
  have hadj := ((hTransposeNorm I I hI hI 1 one_pos).2.2.1 1 1 (Or.inl rfl) (Or.inl rfl)).2.2.1
    (linearMapEntry M) g f
  rw [hconj, applyKernel_linearMapEntry] at hadj
  have e : applyKernel (wTranspose (I.quotWeight 1) (I.quotWeight 1) (linearMapEntry N)) f =
      M f := by
    rw [← htr, quotHomTranspose, linearMapOfEntries_eq_applyKernel]
  rw [e] at hadj
  exact hadj
end SelfAdjointMaps
section RealPoints
variable {L k : ℕ} {κ : Fin 4 → ℂ}
theorem mem_openImStrip_of_real (hκ : κ ∈ realDualPoints) : κ ∈ openImStrip 1 := by
  intro μ
  rw [hκ μ]
  simp
theorem conjVec_of_real (hκ : κ ∈ realDualPoints) : PlaneWaveCalculus.conjVec κ = κ := by
  funext μ
  exact Complex.conj_eq_iff_im.mpr (hκ μ)
theorem toComplexVec_re (hκ : κ ∈ realDualPoints) : toComplexVec (fun μ => (κ μ).re) = κ := by
  funext μ
  apply Complex.ext
  · simp [toComplexVec]
  · simpa [toComplexVec] using (hκ μ).symm
theorem mem_imStrip_of_real (hκ : κ ∈ realDualPoints) {δ : ℝ} (hδ : 0 < δ) :
    κ ∈ strictImStrip δ := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.mem_imStrip_of_real <;> assumption
theorem isAdjointPair_of_real {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (facts : SymbolProperties I I' I'' T S 1) (hreal : ∀ ι' ι, (T ι' ι).im = 0)
    (hκ : κ ∈ realDualPoints) :
    IsAdjointPair (symbolHom I I' T κ) (symbolHom I' I (kernelTranspose I I' T) κ) := by
  intro f g
  have := hI.finite_quot
  have := hI'.finite_quot
  have e₁ : symbolHom I I' T κ f = applyKernel (quotSymbol I I' T κ) f :=
    linearMapOfEntries_eq_applyKernel _ _
  have e₂ : symbolHom I' I (kernelTranspose I I' T) κ g =
      applyKernel (quotSymbol I' I (kernelTranspose I I' T) κ) g :=
    linearMapOfEntries_eq_applyKernel _ _
  rw [e₁, e₂, (facts.quotSymbol_kernelTranspose κ (mem_imStrip_of_real hκ one_pos)).2]
  have h := facts.wInner_quotTranspose hreal (fun μ => (κ μ).re) f g
  rw [toComplexVec_re hκ] at h
  exact h.symm
theorem shiftedFreq_of_real (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) :
    shiftedFreq κ m = toComplexVec (fun μ => (κ μ).re + 2 * Real.pi * (m μ : ℝ)) := by
  funext μ
  have e := congrFun (toComplexVec_re hκ) μ
  simp only [toComplexVec] at e
  simp only [PlaneWaves.shiftedFreq, toComplexVec]
  push_cast
  rw [e]
theorem symbolSquare_shiftedFreq (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    (m : Fin 4 → ℤ) :
    symbolSquare L k (shiftedFreq κ m) =
      ((∑ ν, ‖forwardSymbol L k (shiftedFreq κ m) ν‖ ^ 2 : ℝ) : ℂ) := by
  rw [shiftedFreq_of_real hκ m, hf.symbolSquare_ofReal]
  push_cast
  rfl
theorem symbolSquares_nonneg (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    (m : Fin 4 → ℤ) : 0 ≤ symbolSquares L k κ m := by
  unfold symbolSquares
  rw [symbolSquare_shiftedFreq hf hκ m, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => by positivity
def symbolRoot (L k : ℕ) (q : Fin 4 → ℂ) : ℂ :=
  ((Real.sqrt (symbolSquare L k q).re : ℝ) : ℂ)
theorem symbolRoot_mul_self (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    (m : Fin 4 → ℤ) :
    symbolRoot L k (shiftedFreq κ m) * symbolRoot L k (shiftedFreq κ m) =
      symbolSquare L k (shiftedFreq κ m) := by
  have e : (((symbolSquare L k (shiftedFreq κ m)).re : ℝ) : ℂ) =
      symbolSquare L k (shiftedFreq κ m) := by
    rw [symbolSquare_shiftedFreq hf hκ m, Complex.ofReal_re]
  simp only [symbolRoot]
  have h : 0 ≤ (symbolSquare L k (shiftedFreq κ m)).re := symbolSquares_nonneg hf hκ m
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt h, e]
theorem norm_symbolRoot_sq (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    (m : Fin 4 → ℤ) :
    ‖symbolRoot L k (shiftedFreq κ m)‖ ^ 2 = symbolSquares L k κ m := by
  simp only [symbolRoot]
  have h : 0 ≤ (symbolSquare L k (shiftedFreq κ m)).re := symbolSquares_nonneg hf hκ m
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h]
  rfl
theorem symbolRoot_matrix_facts (hTransposeNorm : Quotients.QuotientTransposeNorm) (hf : SymbolFormulas L k)
    {I : PeriodicData} (hI : IsPeriodic I) {ScaleR ScaleD : (Fin 4 → ℂ) → QuotHom I I → Prop}
    {MR MD : (Fin 4 → ℂ) → QuotHom I I}
    (FR : MultiplierMatrixFacts I ScaleR MR 1 (symbolRoot L k))
    (FD : MultiplierMatrixFacts I ScaleD MD 1 (symbolSquare L k))
    (hκ : κ ∈ realDualPoints) (hcomp : ScaleD κ ((MR κ).comp (MR κ))) {A : QuotHom I I}
    (hA : ScaleD κ A) : IsSelfAdjointMap (MR κ) ∧ A = (MR κ).comp (MR κ) := by
  have hs := mem_openImStrip_of_real hκ
  have even : ∀ q ∈ openImStrip 1, symbolRoot L k (-q) = symbolRoot L k q := by
    intro q _
    simp only [symbolRoot, hf.symbolSquare_neg]
  have conjugate : ∀ q ∈ openImStrip 1,
      conj (symbolRoot L k q) = symbolRoot L k (PlaneWaveCalculus.conjVec q) := by
    intro q _
    simp only [symbolRoot, ← hf.conj_symbolSquare, Complex.conj_ofReal, Complex.conj_re]
  refine ⟨?_, ((FD.scales_unique κ hs).2 A hA).trans ((FD.scales_unique κ hs).2 _ hcomp).symm⟩
  refine isSelfAdjointMap_of_transpose hTransposeNorm hI (N := MR (-κ)) (FR.transpose_neg even κ hs) ?_
  have h := FR.conj_entries even conjugate κ hs
  rwa [conjVec_of_real hκ] at h
theorem conj_forwardSymbol (hκ : κ ∈ realDualPoints) (m : Fin 4 → ℤ) (μ : Fin 4) :
    conj (forwardSymbol L k (shiftedFreq κ m) μ) = forwardSymbol L k (-shiftedFreq κ m) μ := by
  rw [shiftedFreq_of_real hκ m]
  simp only [forwardSymbol, toComplexVec, Pi.neg_apply, map_mul, map_inv₀, map_sub, map_one,
    Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  congr 3
  ring
theorem vertexWeights_cast (hrel : WeightRelations L k) (hκ : κ ∈ realDualPoints)
    (m : Fin 4 → ℤ) :
    ((vertexWeights L k κ m : ℝ) : ℂ) = PlaneWaves.vertexWeight L k (shiftedFreq κ m) := by
  apply Complex.ext
  · simp [vertexWeights]
  · rw [Complex.ofReal_im, shiftedFreq_of_real hκ m, hrel.vertexWeight_im]
end RealPoints
section PauliCoefficients
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : Matrices.ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_smul (a : Fin 3) (c : ℂ) {X : Matrices.ComplexMatrix2}
    (h : X ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
theorem pauliCoeff_add (a : Fin 3) {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
theorem pauliCoeff_sum {ι : Type} (a : Fin 3) (s : Finset ι) (X : ι → Matrices.ComplexMatrix2)
    (h : ∀ i ∈ s, X i ∈ Matrices.ComplexMatrix2.traceless) :
    pauliCoeff a (∑ i ∈ s, X i) = ∑ i ∈ s, pauliCoeff a (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pauliCoeff_zero]
  | insert i s hi ih =>
    have h₁ : ∀ j ∈ s, X j ∈ Matrices.ComplexMatrix2.traceless :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      pauliCoeff_add a (h i (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ h₁), ih h₁]
theorem pauliNorm_sq (X : Matrices.ComplexMatrix2) :
    pauliNorm X ^ 2 = ∑ a, ‖pauliCoeff a X‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
variable (L k : ℕ)
theorem fourierCoeff_mem (g : FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2)
    (h : ∀ x, g x ∈ Matrices.ComplexMatrix2.traceless) (m : Fin 4 → ℤ) :
    fourierCoeff L k g m ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.fourierCoeff_mem_traceless <;> assumption
theorem vertexFourierCoeff_mem (l : (colourVertices L k 0).UnitQuot → ℂ) (m : Fin 4 → ℤ) :
    vertexFourierCoeff L k l m ∈ Matrices.ComplexMatrix2.traceless :=
  fourierCoeff_mem L k _ (fun _ => ofPauliCoeffs_mem _ _) m
theorem edgeFourierCoeff_mem (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4)
    (m : Fin 4 → ℤ) : edgeFourierCoeff L k b μ m ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.edgeFourierCoeff_mem_traceless <;> assumption
end PauliCoefficients
section UnitClasses
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem vertex_integral (L k : ℕ) (x : FullSpace.Vertex L k k) :
    ∃ n : Fin 4 → ℤ, (x : AmbientSpace) = castVec n := by
  obtain ⟨n, hn⟩ := x.2
  refine ⟨n, funext fun μ => ?_⟩
  rw [hn μ, meshAt_self, mul_one]
  rfl
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def unitVertexClass (L k : ℕ) (a : Fin 3) : (colourVertices L k k).UnitQuot :=
  (colourVertices L k k).mkQuot 1 (a, (0 : FullSpace.Vertex L k k))
def unitEdgeClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
variable (hT : TowerTranslations.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hk : 1 ≤ k)
include hT hL hk
theorem exists_unitVertexClass (c : (colourVertices L k k).UnitQuot) :
    ∃ a, c = unitVertexClass L k a := by
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨a, x⟩ := ι
    obtain ⟨n, hn⟩ := vertex_integral L k x
    refine ⟨a, Quot.sound ⟨-n, ?_⟩⟩
    have h₁ := (hT L hL k k hk le_rfl (1 • (-n))).2.2.1 a x
    have h₂ := ((hT L hL k k hk le_rfl (1 • (-n))).2.1 x).1
    have hvertex : (FullSpace.vertexImage (intShift (1 • (-n))) x : FullSpace.Vertex L k k) =
        0 := by
      refine Subtype.ext ?_
      rw [h₂, hn]
      funext ν
      simp [castVec]
    rw [h₁, hvertex]
theorem exists_unitEdgeClass (c : (colourEdges L k k).UnitQuot) :
    ∃ a μ, c = unitEdgeClass L k a μ := by
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨a, b⟩ := ι
    obtain ⟨μ, hμ⟩ := b.2
    obtain ⟨n, hn⟩ := vertex_integral L k b.1.initial
    refine ⟨a, μ, Quot.sound ⟨-n, ?_⟩⟩
    have h₁ := (hT L hL k k hk le_rfl (1 • (-n))).2.2.2.1 a b μ hμ
    have h₂ := ((hT L hL k k hk le_rfl (1 • (-n))).2.1 b.1.initial).1
    have hvertex : (FullSpace.vertexImage (intShift (1 • (-n))) b.1.initial :
        FullSpace.Vertex L k k) = 0 := by
      refine Subtype.ext ?_
      rw [h₂, hn]
      funext ν
      simp [castVec]
    rw [h₁, hvertex]
    rfl
theorem unitEdgeClass_injective {a a' : Fin 3} {μ μ' : Fin 4}
    (h : unitEdgeClass L k a μ = unitEdgeClass L k a' μ') : a = a' ∧ μ = μ' := by
  let g : (colourEdges L k k).Carrier → Fin 3 × FullSpace.Vertex L k k :=
    fun ι => (ι.1, ι.2.1.terminal - ι.2.1.initial)
  have hstep : ∀ ι ι' : (colourEdges L k k).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (colourEdges L k k).translate (1 • n) ι) → g ι = g ι' := by
    rintro ⟨c, b⟩ _ ⟨n, rfl⟩
    obtain ⟨ν, hν⟩ := b.2
    rw [(hT L hL k k hk le_rfl (1 • n)).2.2.2.1 c b ν hν]
    simp [g, hν, TowerTranslations.posEdgeForward, InfiniteLattice.Link.forwardFrom]
  have e := congrArg (Quot.lift g hstep) h
  have e₁ : (a, InfiniteLattice.axisStep (meshAt L k k) μ) =
      (a', InfiniteLattice.axisStep (meshAt L k k) μ') := by
    simpa [unitEdgeClass, PeriodicData.mkQuot, g, posEdgeAt, InfiniteLattice.Link.forwardFrom]
      using e
  refine ⟨congrArg Prod.fst e₁, axisStep_injective ?_ (congrArg Prod.snd e₁)⟩
  rw [meshAt_self]
  exact one_ne_zero
omit hT hL hk
theorem unitVertexClass_injective {a a' : Fin 3}
    (h : unitVertexClass L k a = unitVertexClass L k a') : a = a' := by
  let g : (colourVertices L k k).Carrier → Fin 3 := fun ι => ι.1
  have hstep : ∀ ι ι' : (colourVertices L k k).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (colourVertices L k k).translate (1 • n) ι) → g ι = g ι' := by
    rintro ι _ ⟨n, rfl⟩
    rfl
  exact congrArg (Quot.lift g hstep) h
theorem vertex_quotWeight (c : (colourVertices L k k).UnitQuot) :
    (colourVertices L k k).quotWeight 1 c = 1 := by
  induction c using Quot.ind with
  | mk ι =>
    have h := Classical.epsilon_spec
      (p := fun w => ∀ ι', (colourVertices L k k).mkQuot 1 ι' = Quot.mk _ ι →
        (colourVertices L k k).weightOf ι' = w) ⟨meshAt L k k ^ 4, fun _ _ => rfl⟩ ι rfl
    have e : (colourVertices L k k).weightOf ι = 1 := by
      change meshAt L k k ^ 4 = 1
      rw [meshAt_self, one_pow]
    exact h.symm.trans e
theorem edge_quotWeight (c : (colourEdges L k k).UnitQuot) :
    (colourEdges L k k).quotWeight 1 c = 1 := by
  induction c using Quot.ind with
  | mk ι =>
    have h := Classical.epsilon_spec
      (p := fun w => ∀ ι', (colourEdges L k k).mkQuot 1 ι' = Quot.mk _ ι →
        (colourEdges L k k).weightOf ι' = w) ⟨meshAt L k k ^ 4, fun _ _ => rfl⟩ ι rfl
    have e : (colourEdges L k k).weightOf ι = 1 := by
      change meshAt L k k ^ 4 = 1
      rw [meshAt_self, one_pow]
    exact h.symm.trans e
theorem pauliCoeff_topVertexElement (g : (colourVertices L k k).UnitQuot → ℂ) (a : Fin 3) :
    pauliCoeff a (topVertexElement L k g) = g (unitVertexClass L k a) :=
  pauliCoeff_combination (fun a => g (unitVertexClass L k a)) a
theorem pauliCoeff_topEdgeComponent (z : (colourEdges L k k).UnitQuot → ℂ) (a : Fin 3)
    (μ : Fin 4) : pauliCoeff a (topEdgeComponent L k z μ) = z (unitEdgeClass L k a μ) :=
  pauliCoeff_combination (fun a => z (unitEdgeClass L k a μ)) a
include hT hL hk
theorem top_vertex_wInner_self (g : (colourVertices L k k).UnitQuot → ℂ) :
    wInner ((colourVertices L k k).quotWeight 1) g g =
      ((∑ a, ‖pauliCoeff a (topVertexElement L k g)‖ ^ 2 : ℝ) : ℂ) := by
  rw [wInner_self_eq_tsum]
  congr 1
  let e : Fin 3 ≃ (colourVertices L k k).UnitQuot :=
    Equiv.ofBijective (unitVertexClass L k)
      ⟨fun _ _ h => unitVertexClass_injective h,
        fun c => (exists_unitVertexClass hT hL hk c).imp fun _ h => h.symm⟩
  rw [← e.tsum_eq (fun c => (colourVertices L k k).quotWeight 1 c * ‖g c‖ ^ 2), tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [vertex_quotWeight, one_mul, pauliCoeff_topVertexElement]
  rfl
theorem top_edge_wInner_self (z : (colourEdges L k k).UnitQuot → ℂ) :
    wInner ((colourEdges L k k).quotWeight 1) z z =
      ((∑ a, ∑ μ, ‖pauliCoeff a (topEdgeComponent L k z μ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [wInner_self_eq_tsum]
  congr 1
  let e : Fin 3 × Fin 4 ≃ (colourEdges L k k).UnitQuot :=
    Equiv.ofBijective (fun p => unitEdgeClass L k p.1 p.2)
      ⟨fun p p' h => Prod.ext (unitEdgeClass_injective hT hL hk h).1
          (unitEdgeClass_injective hT hL hk h).2,
        fun c => by
          obtain ⟨a, μ, rfl⟩ := exists_unitEdgeClass hT hL hk c
          exact ⟨(a, μ), rfl⟩⟩
  rw [← e.tsum_eq (fun c => (colourEdges L k k).quotWeight 1 c * ‖z c‖ ^ 2), tsum_fintype,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun μ _ => ?_
  rw [edge_quotWeight, one_mul, pauliCoeff_topEdgeComponent]
  rfl
end UnitClasses
section CoefficientForms
variable {L k : ℕ} {κ : Fin 4 → ℂ}
theorem vertexInner_self_eq (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic (colourVertices L k 0)) (cS : VertexCoeffFacts L k)
    (l : (colourVertices L k 0).UnitQuot → ℂ) :
    vertexInner L k l l =
      ((∑ a, ∑ m ∈ freqBox L k, ‖vertexColourCoeffs L k l a m‖ ^ 2 : ℝ) : ℂ) := by
  rw [vertexInner, wInner_self_eq_tsum]
  congr 1
  have h := cS.norm_sq l
  rw [wNorm, Real.sq_sqrt (tsum_nonneg fun c =>
    mul_nonneg (quotWeight_pos hTransposeNorm hI c).le (by positivity))] at h
  rw [h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pauliNorm_sq]
  rfl
theorem edgeInner_self_eq (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic (colourEdges L k 0)) (cB : EdgeCoeffFacts L k)
    (b : (colourEdges L k 0).UnitQuot → ℂ) :
    edgeInner L k b b =
      ((∑ a, ∑ m ∈ freqBox L k, bondNormSq (edgeColourCoeffs L k b a) m : ℝ) : ℂ) := by
  rw [edgeInner, wInner_self_eq_tsum]
  congr 1
  have h := cB.norm_sq b
  rw [wNorm, Real.sq_sqrt (tsum_nonneg fun c =>
    mul_nonneg (quotWeight_pos hTransposeNorm hI c).le (by positivity))] at h
  rw [h]
  simp only [pauliNorm_sq, bondNormSq, edgeColourCoeffs]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := freqBox L k)]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
theorem vertexInner_square_eq (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic (colourVertices L k 0)) (cS : VertexCoeffFacts L k)
    (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    {A B : QuotHom (colourVertices L k 0) (colourVertices L k 0)} (hB : IsSelfAdjointMap B)
    (hA : A = B.comp B)
    (hmul : ScalesVertexCoeffs L k (symbolRoot L k) κ B)
    (l : (colourVertices L k 0).UnitQuot → ℂ) :
    vertexInner L k l (A l) =
      ((∑ a, siteDirichlet (freqBox L k) (symbolSquares L k κ)
        (vertexColourCoeffs L k l a) : ℝ) : ℂ) := by
  rw [vertexInner, wInner_comp_self hB hA, ← vertexInner, vertexInner_self_eq hTransposeNorm hI cS]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m hm => ?_
  simp only [vertexColourCoeffs]
  rw [hmul l m hm, pauliCoeff_smul a _ (vertexFourierCoeff_mem L k l m), norm_mul, mul_pow,
    norm_symbolRoot_sq hf hκ m]
theorem edgeInner_square_eq (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic (colourEdges L k 0)) (cB : EdgeCoeffFacts L k)
    (hf : SymbolFormulas L k) (hκ : κ ∈ realDualPoints)
    {A B : QuotHom (colourEdges L k 0) (colourEdges L k 0)} (hB : IsSelfAdjointMap B)
    (hA : A = B.comp B)
    (hmul : ScalesEdgeCoeffs L k (symbolRoot L k) κ B)
    (b : (colourEdges L k 0).UnitQuot → ℂ) :
    edgeInner L k b (A b) =
      ((∑ a, bondDirichlet (freqBox L k) (symbolSquares L k κ)
        (edgeColourCoeffs L k b a) : ℝ) : ℂ) := by
  rw [edgeInner, wInner_comp_self hB hA, ← edgeInner, edgeInner_self_eq hTransposeNorm hI cB]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m hm => ?_
  simp only [bondNormSq, edgeColourCoeffs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hmul b μ m hm, pauliCoeff_smul a _ (edgeFourierCoeff_mem L k b μ m), norm_mul, mul_pow,
    norm_symbolRoot_sq hf hκ m]
theorem pauliCoeff_smoothing_vertex (hav : SmoothingSymbols L k) (hrel : WeightRelations L k)
    (hκ : κ ∈ realDualPoints) (l : (colourVertices L k 0).UnitQuot → ℂ) (a : Fin 3) :
    pauliCoeff a (topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k)
          (trivialRescaledOperators L k).R κ l)) =
      weightedSiteSum (freqBox L k) (vertexWeights L k κ) (vertexColourCoeffs L k l a) := by
  rw [show topVertexElement L k
      (symbolHom (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R κ l) = _ from hav.R κ l,
    pauliCoeff_sum a _ _ fun m _ => Submodule.smul_mem _ _ (vertexFourierCoeff_mem L k l m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pauliCoeff_smul a _ (vertexFourierCoeff_mem L k l m), vertexWeights_cast hrel hκ m]
  rfl
theorem pauliCoeff_smoothing_edge (hav : SmoothingSymbols L k)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3) (μ : Fin 4) :
    pauliCoeff a (topEdgeComponent L k
        (symbolHom (colourEdges L k 0) (colourEdges L k k)
          (trivialRescaledOperators L k).Q κ b) μ) =
      weightedBondSum (freqBox L k) (edgeWeights L k κ) (edgeColourCoeffs L k b a) μ := by
  rw [show topEdgeComponent L k
      (symbolHom (colourEdges L k 0) (colourEdges L k k)
        (trivialRescaledOperators L k).Q κ b) μ = _ from hav.Q κ b μ,
    pauliCoeff_sum a _ _ fun m _ => Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k b μ m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pauliCoeff_smul a _ (edgeFourierCoeff_mem L k b μ m)]
  rfl
theorem vertexColourCoeffs_coboundaryT (hact : PlaneWaveCalculus.CoboundarySymbols L k)
    (hκ : κ ∈ realDualPoints) (b : (colourEdges L k 0).UnitQuot → ℂ) (a : Fin 3)
    {m : Fin 4 → ℤ} (hm : m ∈ freqBox L k) :
    vertexColourCoeffs L k (symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (PlaneWaveCalculus.vertexCoboundaryT L k 0) κ b) a m =
      familyDivergence (symbols L k κ) (edgeColourCoeffs L k b a) m := by
  simp only [vertexColourCoeffs]
  rw [hact.vertexCoboundary_transpose κ b m hm,
    pauliCoeff_sum a _ _ fun μ _ => Submodule.smul_mem _ _ (edgeFourierCoeff_mem L k b μ m)]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pauliCoeff_smul a _ (edgeFourierCoeff_mem L k b μ m), ← conj_forwardSymbol hκ m μ]
  rfl
end CoefficientForms
section SymbolsAtAPoint
variable (q2 : StripSymbols.Claim)
include q2
theorem symbolSummableAt_of_finiteRange {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : FreeOperators.HasFiniteRangeEveryRate I I' T) (κ : Fin 4 → ℂ) :
    SymbolSummableAt I I' T κ :=
  (q2.2.1 _ _ hI hI').1.finiteRange _ hT.1 hT.2.1 κ (mem_univ κ)
theorem symbolHom_compKernel {I I' I'' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hS : IsPeriodicKernel I'' I S) {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fS : SymbolSummableAt I'' I S κ) :
    IsPeriodicKernel I'' I' (compKernel T S) ∧
      SymbolSummableAt I'' I' (compKernel T S) κ ∧
      symbolHom I'' I' (compKernel T S) κ = (symbolHom I I' T κ).comp (symbolHom I'' I S κ) :=
  (((q2.2.1 I I' hI hI').2.1 T κ hT fT).comp I'' hI'' S hS fS).2
theorem symbolHom_linCombKernel {I I' : PeriodicData} (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T T' : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hT' : IsPeriodicKernel I I' T') {κ : Fin 4 → ℂ}
    (fT : SymbolSummableAt I I' T κ) (fT' : SymbolSummableAt I I' T' κ) (c c' : ℂ) :
    IsPeriodicKernel I I' (StripSymbols.linCombKernel c c' T T') ∧
      SymbolSummableAt I I' (StripSymbols.linCombKernel c c' T T') κ ∧
      symbolHom I I' (StripSymbols.linCombKernel c c' T T') κ =
        c • symbolHom I I' T κ + c' • symbolHom I I' T' κ :=
  ((q2.2.1 I I' hI hI').2.1 T κ hT fT).linComb T' hT' fT' c c'
end SymbolsAtAPoint
theorem freeSymbolForms_holds (hplane : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hfree : FreeOperators.FreeOperatorsArePeriodic) (hidx : TowerIndexSets.Claim)
    (hsym : Symbols.Claim) (q2 : StripSymbols.Claim) (hTransposeNorm : Quotients.QuotientTransposeNorm)
    (hT : TowerTranslations.Claim) (facts : RescaledConditions.Holds) : FreeSymbolForms := by
  intro L hL k hk κ hκ
  obtain ⟨-, cS, cB, -, hf, hact, hav, hrel, hreal, hM⟩ := hplane L hL k hk
  obtain ⟨hmaps, hops⟩ := hfree.2 L hL k hk
  have iS₀ := (hidx L hL k 0 (Nat.zero_le k)).1
  have iB₀ := (hidx L hL k 0 (Nat.zero_le k)).2.1
  have iS := (hidx L hL k k le_rfl).1
  have iB := (hidx L hL k k le_rfl).2.1
  have := iS₀.finite_quot
  have := iB₀.finite_quot
  have := iS.finite_quot
  have := iB.finite_quot
  have hs := mem_openImStrip_of_real hκ
  have root_periodic : ∀ q ∈ openImStrip 1, ∀ e : Fin 4 → ℤ,
      symbolRoot L k (PlaneWaveCalculus.periodShift L k q e) = symbolRoot L k q := by
    intro q _ e
    simp only [symbolRoot, hf.symbolSquare_periodic]
  have square_periodic : ∀ q ∈ openImStrip 1, ∀ e : Fin 4 → ℤ,
      symbolSquare L k (PlaneWaveCalculus.periodShift L k q e) = symbolSquare L k q :=
    fun q _ e => hf.symbolSquare_periodic q e
  obtain ⟨FRs, FRb, -⟩ := hM 1 one_pos _ root_periodic
  obtain ⟨FDs, FDb, -⟩ := hM 1 one_pos _ square_periodic
  obtain ⟨hRootB, eK⟩ := symbolRoot_matrix_facts
      (A := symbolHom (colourEdges L k 0) (colourEdges L k 0)
        (trivialRescaledOperators L k).K κ) hTransposeNorm hf iB₀ FRb FDb hκ (by
    intro b μ m hm
    have h := (FRb.scales_unique κ hs).1
    rw [LinearMap.comp_apply, h _ μ m hm, h b μ m hm, smul_smul, symbolRoot_mul_self hf hκ m])
    (hact.K κ)
  obtain ⟨hRootS, eD⟩ := symbolRoot_matrix_facts
      (A := symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Delta κ) hTransposeNorm hf iS₀ FRs FDs hκ (by
    intro l m hm
    have h := (FRs.scales_unique κ hs).1
    rw [LinearMap.comp_apply, h _ m hm, h l m hm, smul_smul, symbolRoot_mul_self hf hκ m])
    (hact.Delta κ)
  have hK : IsSelfAdjointMap (symbolHom (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).K κ) := isSelfAdjointMap_comp_self hRootB eK
  have hD : IsSelfAdjointMap (symbolHom (colourVertices L k 0) (colourVertices L k 0)
      (trivialRescaledOperators L k).Delta κ) := isSelfAdjointMap_comp_self hRootS eD
  have edgeK := edgeInner_square_eq hTransposeNorm iB₀ cB hf hκ hRootB eK (FRb.scales_unique κ hs).1
  have vertexD := vertexInner_square_eq hTransposeNorm iS₀ cS hf hκ hRootS eD (FRs.scales_unique κ hs).1
  have pQ := hmaps.edgeAverage.finite_range
  have pR := hmaps.vertexAverage.finite_range
  have pQt := hops.edgeAverage_transpose
  have pRt := hops.vertexAverage_transpose
  have pd := (hmaps.vertexCoboundary 0 (Nat.zero_le k)).finite_range
  have pdt := hops.vertexCoboundary_transpose 0 (Nat.zero_le k)
  have adjQ : IsAdjointPair
      (symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ)
      (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ) :=
    isAdjointPair_of_real iB₀ iB
      (hsym.1 _ _ _ iB₀ iB iB _ _ 1 pQ.1 (pQ.2.2 1 one_pos) pQt.1 (pQt.2.2 1 one_pos))
      hreal.Q.2.1 hκ
  have adjR : IsAdjointPair
      (symbolHom (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R κ)
      (symbolHom (colourVertices L k k) (colourVertices L k 0)
        (trivialRescaledOperators L k).Rt κ) :=
    isAdjointPair_of_real iS₀ iS
      (hsym.1 _ _ _ iS₀ iS iS _ _ 1 pR.1 (pR.2.2 1 one_pos) pRt.1 (pRt.2.2 1 one_pos))
      hreal.R.2.1 hκ
  have adjd : IsAdjointPair
      (symbolHom (colourVertices L k 0) (colourEdges L k 0)
        (FullSpace.scaledVertexCoboundaryKernel L k 0) κ)
      (symbolHom (colourEdges L k 0) (colourVertices L k 0)
        (PlaneWaveCalculus.vertexCoboundaryT L k 0) κ) :=
    isAdjointPair_of_real iS₀ iB₀
      (hsym.1 _ _ _ iS₀ iB₀ iB₀ _ _ 1 pd.1 (pd.2.2 1 one_pos) pdt.1 (pdt.2.2 1 one_pos))
      (hreal.vertexCoboundary 0 (Nat.zero_le k)).2.1 hκ
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (facts L hL k hk).2
  have eDk : (trivialRescaledOperators L k).D = FullSpace.scaledVertexCoboundaryKernel L k 0 :=
    hOne.D_eq
  have eDt : (trivialRescaledOperators L k).Dt =
      kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
        (FullSpace.scaledVertexCoboundaryKernel L k 0) := by
    rw [← eDk]
    rfl
  have fd := symbolSummableAt_of_finiteRange q2 iS₀ iB₀ pd κ
  have fdt := symbolSummableAt_of_finiteRange q2 iB₀ iS₀ pdt κ
  have fQ := symbolSummableAt_of_finiteRange q2 iB₀ iB pQ κ
  have fR := symbolSummableAt_of_finiteRange q2 iS₀ iS pR κ
  have fQt := symbolSummableAt_of_finiteRange q2 iB iB₀ pQt κ
  have fRt := symbolSummableAt_of_finiteRange q2 iS iS₀ pRt κ
  have fK := symbolSummableAt_of_finiteRange q2 iB₀ iB₀ hops.K κ
  have fDelta := symbolSummableAt_of_finiteRange q2 iS₀ iS₀ hops.Delta κ
  have eXi : symbolHom (colourEdges L k 0) (colourEdges L k 0)
        (trivialRescaledOperators L k).Xi κ =
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).K κ -
        ((symbolHom (colourVertices L k 0) (colourEdges L k 0)
            (FullSpace.scaledVertexCoboundaryKernel L k 0) κ).comp
          (symbolHom (colourVertices L k k) (colourVertices L k 0)
            (trivialRescaledOperators L k).Rt κ)).comp
        ((symbolHom (colourVertices L k 0) (colourVertices L k k)
            (trivialRescaledOperators L k).R κ).comp
          (symbolHom (colourEdges L k 0) (colourVertices L k 0)
            (PlaneWaveCalculus.vertexCoboundaryT L k 0) κ)) +
        (symbolHom (colourEdges L k k) (colourEdges L k 0)
            (trivialRescaledOperators L k).Qt κ).comp
          (symbolHom (colourEdges L k 0) (colourEdges L k k)
            (trivialRescaledOperators L k).Q κ) := by
    have p₁ := symbolHom_compKernel q2 iS₀ iB₀ iS pd.1 pRt.1 fd fRt
    have p₂ := symbolHom_compKernel q2 iS₀ iS iB₀ pR.1 pdt.1 fR fdt
    have p₃ := symbolHom_compKernel q2 iS iB₀ iB₀ p₁.1 p₂.1 p₁.2.1 p₂.2.1
    have p₄ := symbolHom_compKernel q2 iB iB₀ iB₀ pQt.1 pQ.1 fQt fQ
    have c₁ := symbolHom_linCombKernel q2 iB₀ iB₀ hops.K.1 p₃.1 fK p₃.2.1 1 (-1)
    have c₂ := symbolHom_linCombKernel q2 iB₀ iB₀ c₁.1 p₄.1 c₁.2.1 p₄.2.1 1 1
    have e : (trivialRescaledOperators L k).Xi = StripSymbols.linCombKernel 1 1
        (StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).K
          (compKernel
            (compKernel (FullSpace.scaledVertexCoboundaryKernel L k 0)
              (trivialRescaledOperators L k).Rt)
            (compKernel (trivialRescaledOperators L k).R
              (kernelTranspose (colourVertices L k 0) (colourEdges L k 0)
                (FullSpace.scaledVertexCoboundaryKernel L k 0)))))
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) := by
      rw [← eDt, ← eDk]
      funext ι' ι
      change (trivialRescaledOperators L k).K ι' ι -
        compKernel (compKernel (trivialRescaledOperators L k).D (trivialRescaledOperators L k).Rt)
          (compKernel (trivialRescaledOperators L k).R (trivialRescaledOperators L k).Dt) ι' ι +
        compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q ι' ι = _
      simp only [StripSymbols.linCombKernel]
      ring
    refine (congrArg (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T κ) e).trans
      (c₂.2.2.trans ?_)
    rw [c₁.2.2, p₃.2.2, p₄.2.2, p₁.2.2, p₂.2.2]
    have hneg : ∀ M : QuotHom (colourEdges L k 0) (colourEdges L k 0), (-1 : ℂ) • M = -M :=
      fun M => neg_one_smul ℂ M
    simp only [one_smul, sub_eq_add_neg]
    rw [hneg]
    rfl
  have eY : symbolHom (colourVertices L k 0) (colourVertices L k 0)
        (trivialRescaledOperators L k).Y κ =
      symbolHom (colourVertices L k 0) (colourVertices L k 0)
          (trivialRescaledOperators L k).Delta κ +
        (symbolHom (colourVertices L k k) (colourVertices L k 0)
            (trivialRescaledOperators L k).Rt κ).comp
          (symbolHom (colourVertices L k 0) (colourVertices L k k)
            (trivialRescaledOperators L k).R κ) := by
    have p₁ := symbolHom_compKernel q2 iS iS₀ iS₀ pRt.1 pR.1 fRt fR
    have c₁ := symbolHom_linCombKernel q2 iS₀ iS₀ hops.Delta.1 p₁.1 fDelta p₁.2.1 1 1
    have e : (trivialRescaledOperators L k).Y = StripSymbols.linCombKernel 1 1
        (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) := by
      funext ι' ι
      change (trivialRescaledOperators L k).Delta ι' ι +
        compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R ι' ι = _
      simp only [StripSymbols.linCombKernel]
      ring
    refine (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ)
      e).trans (c₁.2.2.trans ?_)
    rw [p₁.2.2]
    simp only [one_smul]
    rfl
  have partsB := edge_decomposition eXi adjd adjR adjQ
  have partsS := vertex_decomposition eY adjR
  refine
    { K_selfAdjoint := hK
      Delta_selfAdjoint := hD
      Xi_selfAdjoint := fun f g => ?_
      Y_selfAdjoint := fun f g => ?_
      edge_norm_sq := edgeInner_self_eq hTransposeNorm iB₀ cB
      vertex_norm_sq := vertexInner_self_eq hTransposeNorm iS₀ cS
      edge_K := edgeK
      vertex_Delta := vertexD
      edge_Xi := fun b => ?_
      vertex_Y := fun l => ?_ }
  · refine (partsB f g).2.trans (Eq.trans ?_ (partsB f g).1.symm)
    rw [hK f g]
  · refine (partsS f g).2.trans (Eq.trans ?_ (partsS f g).1.symm)
    rw [hD f g]
  · refine (partsB b b).1.trans ?_
    have hKb : wInner ((colourEdges L k 0).quotWeight 1) b
        (symbolHom (colourEdges L k 0) (colourEdges L k 0)
          (trivialRescaledOperators L k).K κ b) = _ :=
      edgeK b
    rw [hKb, top_vertex_wInner_self hT hL hk, top_edge_wInner_self hT hL hk,
      ← Complex.ofReal_sub, ← Complex.ofReal_add]
    congr 1
    have gamma : ∀ a, pauliCoeff a (topVertexElement L k
        (symbolHom (colourVertices L k 0) (colourVertices L k k)
          (trivialRescaledOperators L k).R κ
          (symbolHom (colourEdges L k 0) (colourVertices L k 0)
            (PlaneWaveCalculus.vertexCoboundaryT L k 0) κ b))) =
        weightedSiteSum (freqBox L k) (vertexWeights L k κ)
          (familyDivergence (symbols L k κ) (edgeColourCoeffs L k b a)) := fun a => by
      rw [pauliCoeff_smoothing_vertex hav hrel hκ]
      exact Finset.sum_congr rfl fun m hm => by
        rw [vertexColourCoeffs_coboundaryT hact hκ b a hm]
    simp only [bondQuadraticForm, Finset.sum_add_distrib, Finset.sum_sub_distrib, gamma,
      pauliCoeff_smoothing_edge hav]
  · refine (partsS l l).1.trans ?_
    have hDl : wInner ((colourVertices L k 0).quotWeight 1) l
        (symbolHom (colourVertices L k 0) (colourVertices L k 0)
          (trivialRescaledOperators L k).Delta κ l) = _ :=
      vertexD l
    rw [hDl, top_vertex_wInner_self hT hL hk, ← Complex.ofReal_add]
    congr 1
    simp only [siteQuadraticForm, Finset.sum_add_distrib, pauliCoeff_smoothing_vertex hav hrel hκ]
end YangMills.Construction.Tower.FreeSymbolCoefficients
end
