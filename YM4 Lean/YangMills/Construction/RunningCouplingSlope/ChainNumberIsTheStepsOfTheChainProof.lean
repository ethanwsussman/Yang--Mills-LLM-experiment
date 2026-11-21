import YangMills.Construction.RunningCouplingSlope.ChainNumberIsTheStepsOfTheChain
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheSteps
import YangMills.Construction.RunningCouplingSlope.GaussianNumberThroughLevels
import YangMills.Construction.RunningCouplingSlope.HessiansOfTheStepsArePositive
import YangMills.Construction.RunningCouplingSlope.LengthsOfAChainAreThoseOfItsSteps
import YangMills.Construction.RunningCouplingSlope.LevelMapOfAChain
import YangMills.Construction.RunningCouplingSlope.MovementsOfAChainAreTriangular
import YangMills.Construction.RunningCouplingSlope.SliceOfTheTreesOfAChain
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps ReferenceDensity
  LinearConstraint GaussianConstraint SlopeCoefficient Conventions
namespace ChainLogWeightSteps
private def stepSummand (a ρ : ℝ) (L j s N t : ℕ) (V : TorusField N) : ℝ :=
  stepLogAmplitude (F := torusFrame L j (torusSideBelow L s N)) a ρ
    (readAtLevel (torusFrame L j (torusSideBelow L s N)) (torusFrame L j (torusSideBelow L s N)).top
      (minimizerBelow a ρ L t s N V))
private theorem chainStepLogSum_eq_sum_range (a ρ : ℝ) (L : ℕ) : ∀ (t N : ℕ) (V : TorusField N),
    chainStepLogSum a ρ L t N V =
      ∑ j ∈ Finset.range t, stepSummand a ρ L j (t - (j + 1)) N t V := by
  intro t
  induction t with
  | zero => intro N V; simp [chainStepLogSum]
  | succ t ih =>
    intro N V
    rw [Finset.sum_range_succ]
    have e₁ : stepSummand a ρ L t (t + 1 - (t + 1)) N (t + 1) V =
        stepLogAmplitude (F := torusFrame L t N) a ρ
          (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) := by
      rw [Nat.sub_self]
      rfl
    have e₂ : ∑ j ∈ Finset.range t, stepSummand a ρ L j (t + 1 - (j + 1)) N (t + 1) V =
        chainStepLogSum a ρ L t (N * L) (minimizerOnFinerTorus a ρ L t N V) := by
      rw [ih]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have e : t + 1 - (j + 1) = (t - (j + 1)) + 1 := by omega
      rw [e]
      rfl
    rw [e₁, e₂, chainStepLogSum, add_comm]
private theorem chainStepLogSum_eq_sum_fin (a ρ : ℝ) (L n k : ℕ) (V : TorusField (2 * L ^ n)) :
    chainStepLogSum a ρ L k (2 * L ^ n) V =
      ∑ j : Fin k, stepLogAmplitude (F := frameAtStep L n k j) a ρ (topFieldAtStep a ρ L n k j V) := by
  rw [chainStepLogSum_eq_sum_range, Finset.sum_range]
  rfl
private theorem eq_of_sub_mulVec_eq_of_strictLower {Ω : Type} [Fintype Ω] (lev : Ω → ℕ)
    (N : Matrix Ω Ω ℝ) (h : ∀ e e', lev e ≤ lev e' → N e e' = 0) {y y' : Ω → ℝ}
    (hy : y - Matrix.mulVec N y = y' - Matrix.mulVec N y') : y = y' := by
  have hd : ∀ e, y e - y' e = ∑ e', N e e' * (y e' - y' e') := by
    intro e
    have h₁ := congrFun hy e
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct] at h₁
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have key : ∀ m e, lev e = m → y e - y' e = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro e he
      rw [hd e]
      refine Finset.sum_eq_zero fun e' _ => ?_
      by_cases hle : lev e ≤ lev e'
      · rw [h e e' hle, zero_mul]
      · rw [ih (lev e') (by omega) e' rfl, mul_zero]
  funext e
  exact sub_eq_zero.mp (key _ e rfl)
section BlockDiagonal
variable {J : Type} [Fintype J] [DecidableEq J] {ι : J → Type} [∀ j, Fintype (ι j)]
  [∀ j, DecidableEq (ι j)]
private theorem dotProduct_mulVec_blockDiagonal' (M : ∀ j, Matrix (ι j) (ι j) ℝ)
    (u : (Σ j, ι j) → ℝ) :
    dotProduct u (Matrix.mulVec (Matrix.blockDiagonal' M) u) =
      ∑ j, dotProduct (fun i => u ⟨j, i⟩) (Matrix.mulVec (M j) fun i => u ⟨j, i⟩) := by
  simp only [dotProduct, Matrix.mulVec]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Matrix.blockDiagonal'_apply_eq]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hj'), zero_mul]
  · simp
private theorem posDef_blockDiagonal' (M : ∀ j, Matrix (ι j) (ι j) ℝ) (h : ∀ j, (M j).PosDef) :
    (Matrix.blockDiagonal' M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_blockDiagonal'_iff.mpr fun j => (h j).isHermitian) fun x hx => ?_
  rw [star_trivial, dotProduct_mulVec_blockDiagonal']
  obtain ⟨⟨j, i⟩, hi⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun j' _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · have := (h j').posSemidef.dotProduct_mulVec_nonneg fun i => x ⟨j', i⟩
    rwa [star_trivial] at this
  · have hne : (fun i => x ⟨j, i⟩) ≠ 0 := fun h₀ => hi (congrFun h₀ i)
    have := (h j).dotProduct_mulVec_pos hne
    rwa [star_trivial] at this
private theorem det_blockDiagonal'_eq_prod [LinearOrder J] (M : ∀ j, Matrix (ι j) (ι j) ℝ) :
    (Matrix.blockDiagonal' M).det = ∏ j, (M j).det := by
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e : (Matrix.blockDiagonal' M).toSquareBlock Sigma.fst j =
      (M j).submatrix (Equiv.sigmaSubtype j) (Equiv.sigmaSubtype j) := by
    ext ⟨⟨j₁, i⟩, h⟩ ⟨⟨j₂, i'⟩, h'⟩
    obtain rfl : j₁ = j := h
    obtain rfl : j₂ = j₁ := h'
    simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.blockDiagonal'_apply_eq]
  rw [e, Matrix.det_submatrix_equiv_self]
abbrev _root_.YangMills.SharedProofs.p20357 := @det_blockDiagonal'_eq_prod
end BlockDiagonal
section TwoBlocks
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
private theorem dotProduct_mulVec_fromBlocks_one (H : Matrix α α ℝ) (w : α ⊕ β → ℝ) :
    dotProduct w (Matrix.mulVec (Matrix.fromBlocks H 0 0 (1 : Matrix β β ℝ)) w) =
      dotProduct (fun i => w (Sum.inl i)) (Matrix.mulVec H fun i => w (Sum.inl i)) +
        ∑ i, w (Sum.inr i) ^ 2 := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_def, sq]
private theorem posDef_fromBlocks_one {H : Matrix α α ℝ} (h : H.PosDef) :
    (Matrix.fromBlocks H 0 0 (1 : Matrix β β ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.IsHermitian.fromBlocks h.isHermitian (by simp) Matrix.isHermitian_one) fun x hx => ?_
  rw [star_trivial, dotProduct_mulVec_fromBlocks_one]
  have h₁ := h.posSemidef.dotProduct_mulVec_nonneg fun i => x (Sum.inl i)
  rw [star_trivial] at h₁
  have h₂ : 0 ≤ ∑ i, x (Sum.inr i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨e, he⟩ := Function.ne_iff.mp hx
  cases e with
  | inl i =>
    have hne : (fun i => x (Sum.inl i)) ≠ 0 := fun h₀ => he (congrFun h₀ i)
    have := h.dotProduct_mulVec_pos hne
    rw [star_trivial] at this
    linarith
  | inr i =>
    have : 0 < ∑ i, x (Sum.inr i) ^ 2 :=
      Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
        have : x (Sum.inr i) ≠ 0 := he
        positivity⟩
    linarith
end TwoBlocks
private theorem constrainedGaussianNumberOfCores_eq (hg : GaussianNumberByLevels)
    {E C : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
    (cE : InnerProductSpace.Core ℝ E) (cC : InnerProductSpace.Core ℝ C)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (lev : Ω → ℕ)
    (p : E →ₗ[ℝ] EuclideanSpace ℝ Ω) (q : E →ₗ[ℝ] C) (s : EuclideanSpace ℝ Ω →ₗ[ℝ] E)
    (ι : C →ₗ[ℝ] E) (M : E →ₗ[ℝ] C) (T : QuadraticForm ℝ (LinearMap.ker M))
    (N N' A G : Matrix Ω Ω ℝ)
    (hin : ∀ ξ ξ', cE.inner ξ ξ' =
      dotProduct (WithLp.ofLp (p ξ)) (WithLp.ofLp (p ξ')) + cC.inner (q ξ) (q ξ'))
    (h₁ : p ∘ₗ s = LinearMap.id) (h₂ : q ∘ₗ s = 0) (h₃ : p ∘ₗ ι = 0) (h₄ : q ∘ₗ ι = LinearMap.id)
    (h₅ : M ∘ₗ ι = LinearMap.id)
    (hN : ∀ e e', lev e ≤ lev e' → N e e' = 0) (hN' : ∀ e e', lev e' ≤ lev e → N' e e' = 0)
    (hA : A.det ≠ 0) (hG : G.PosDef)
    (hT : ∀ (ξ : LinearMap.ker M) (y u : Ω → ℝ),
      WithLp.ofLp (p (ξ : E)) = y - Matrix.mulVec N y → y - Matrix.mulVec N' y = Matrix.mulVec A u →
      T ξ = dotProduct u (Matrix.mulVec G u)) :
    constrainedGaussianNumberOfCores cE cC M T =
      (2 * Real.pi) ^ ((Fintype.card Ω : ℝ) / 2) * G.det ^ (-(1 / 2) : ℝ) * |A.det| := by
  letI := cE.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore cE.toCore
  letI := cC.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore cC.toCore
  refine hg E C Ω lev p q s ι M T N N' A G (fun ξ ξ' => ?_) h₁ h₂ h₃ h₄ h₅ hN hN' hA hG hT
  have e : inner ℝ (p ξ) (p ξ') = dotProduct (WithLp.ofLp (p ξ)) (WithLp.ofLp (p ξ')) := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [e]
  exact hin ξ ξ'
variable {L n k : ℕ}
private def blockHessian (a ρ : ℝ) (L n k : ℕ) (V : TorusField (2 * L ^ n)) :
    Matrix (ChainCoord L n k) (ChainCoord L n k) ℝ :=
  open Classical in
  Matrix.blockDiagonal' fun j : Fin k =>
    Matrix.fromBlocks (chartHessianAtStep a ρ L n k j V) 0 0 (1 : Matrix _ _ ℝ)
private theorem det_blockHessian (a ρ : ℝ) (L n k : ℕ) (V : TorusField (2 * L ^ n)) :
    open Classical in
    (blockHessian a ρ L n k V).det = ∏ j : Fin k, (chartHessianAtStep a ρ L n k j V).det := by
  classical
  unfold blockHessian
  rw [det_blockDiagonal'_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e := Matrix.det_fromBlocks_zero₂₁ (chartHessianAtStep a ρ L n k j V) 0
    (1 : Matrix (TreeCoord (frameAtStep L n k j)) (TreeCoord (frameAtStep L n k j)) ℝ)
  rw [Matrix.det_one, mul_one] at e
  convert e
open Classical in
private theorem levelGaussianNumber_eq_det (hg : GaussianNumberByLevels)
    (hsl : SlotCoordsIsometry) (hL : IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (a ρ : ℝ) (V : TorusField (2 * L ^ n)) (X : ChainPoint L n (k + 1))
    (N N' A : Matrix (ChainCoord L n (k + 1)) (ChainCoord L n (k + 1)) ℝ)
    (hN : ∀ e e', coordLevel e ≤ coordLevel e' → N e e' = 0)
    (hNs : ∀ ξ, slotCoords ξ =
      transportCoords X ξ - Matrix.mulVec N (transportCoords X ξ))
    (hNt : ∀ ξ, slotCoords ξ = 0 → topDeriv X ξ = finalNoise ξ)
    (hN' : ∀ e e', coordLevel e' ≤ coordLevel e → N' e e' = 0)
    (hN't : ∀ (j : Fin (k + 1)) (i : TreeCoord (frameAtStep L n (k + 1) j)) e',
      N' ⟨j, .inr i⟩ e' = 0)
    (hF : ∀ (ξ : LinearMap.ker (topDeriv X))
      (x : (j : Fin (k + 1)) → ChartCoord (frameAtStep L n (k + 1) j) → ℝ),
      IsChartPlusGauge a ρ V X x (transportCoords X (ξ : LevelForms L n (k + 1)) -
        Matrix.mulVec N' (transportCoords X (ξ : LevelForms L n (k + 1)))) →
      fibreHessian a X ξ = ∑ j : Fin (k + 1), dotProduct (x j)
        (Matrix.mulVec (chartHessianAtStep a ρ L n (k + 1) j V) (x j)))
    (hA : A.det ≠ 0)
    (hAu : ∀ u : ChainCoord L n (k + 1) → ℝ,
      IsChartPlusGauge a ρ V X (fun j i => u ⟨j, .inl i⟩) (Matrix.mulVec A u) ∧
      ∀ (j : Fin (k + 1)) (i : TreeCoord (frameAtStep L n (k + 1) j)),
        Matrix.mulVec A u ⟨j, .inr i⟩ = u ⟨j, .inr i⟩)
    (hH : ∀ j : Fin (k + 1), (chartHessianAtStep a ρ L n (k + 1) j V).PosDef)
    (l : LevelForms L n (k + 1) →ₗ[ℝ] EuclideanSpace ℝ (TreeChainCoord L n (k + 1)))
    (hl : ∀ ξ e, l ξ e = transportCoords X ξ ⟨e.1, .inr e.2⟩) :
    levelGaussianNumber (topDeriv X)
        (fibreHessian a X + (normSqForm l).comp (LinearMap.ker (topDeriv X)).subtype) =
      (2 * Real.pi) ^ ((Fintype.card (ChainCoord L n (k + 1)) : ℝ) / 2) *
        (blockHessian a ρ L n (k + 1) V).det ^ (-(1 / 2) : ℝ) * |A.det| := by
  obtain ⟨hEA, hEC, p, s, i, hp, hin, hps, hqs, hpi, hqi⟩ := hsl L hL k n hn
  haveI := hEA.1
  haveI := hEC.1
  have eI : ∀ T, levelGaussianNumber (topDeriv X) T =
      constrainedGaussianNumberOfCores hEA.2.choose hEC.2.choose (topDeriv X) T := fun T => by
    unfold levelGaussianNumber
    rw [dif_pos ⟨hEA, hEC⟩]
  rw [eI]
  refine constrainedGaussianNumberOfCores_eq hg hEA.2.choose hEC.2.choose coordLevel p finalNoise
    s i _ _ N N' A _ ?_ hps hqs hpi hqi ?_ hN hN' hA ?_ ?_
  · intro ξ ξ'
    rw [hEA.2.choose_spec ξ ξ', hEC.2.choose_spec, hin ξ ξ']
  · refine LinearMap.ext fun ν => ?_
    have h₀ : slotCoords (i ν) = 0 := by
      rw [← hp]
      have h₁ : p (i ν) = 0 := LinearMap.congr_fun hpi ν
      rw [h₁]
      rfl
    show topDeriv X (i ν) = ν
    rw [hNt _ h₀]
    exact LinearMap.congr_fun hqi ν
  · exact posDef_blockDiagonal' _ fun j => posDef_fromBlocks_one (hH j)
  · intro ξ y u h₁ h₂
    have hy : y = transportCoords X (ξ : LevelForms L n (k + 1)) :=
      eq_of_sub_mulVec_eq_of_strictLower coordLevel N hN ((h₁.symm.trans (hp _)).trans (hNs _))
    subst hy
    have hc := (hAu u).1
    rw [← h₂] at hc
    have hf := hF ξ _ hc
    have hsq : (normSqForm l) (ξ : LevelForms L n (k + 1)) =
        ∑ j : Fin (k + 1), ∑ i : TreeCoord (frameAtStep L n (k + 1) j), u ⟨j, .inr i⟩ ^ 2 := by
      have e₁ : (normSqForm l) (ξ : LevelForms L n (k + 1)) =
          inner ℝ (l (ξ : LevelForms L n (k + 1))) (l (ξ : LevelForms L n (k + 1))) := by
        simp [normSqForm, LinearMap.BilinMap.toQuadraticMap_apply]
      rw [e₁, PiLp.inner_apply, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => ?_
      have e₂ := congrFun h₂ ⟨j, .inr i'⟩
      have e₃ : Matrix.mulVec N' (transportCoords X (ξ : LevelForms L n (k + 1)))
          ⟨j, .inr i'⟩ = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_eq_zero fun e' _ => by rw [hN't, zero_mul]
      simp only [Pi.sub_apply, e₃, sub_zero] at e₂
      rw [(hAu u).2] at e₂
      have e₄ : l (ξ : LevelForms L n (k + 1)) ⟨j, i'⟩ = u ⟨j, .inr i'⟩ := by
        rw [hl]
        exact e₂
      simp [e₄, sq]
    show fibreHessian a X ξ + (normSqForm l) (ξ : LevelForms L n (k + 1)) = _
    rw [hf, hsq]
    unfold blockHessian
    rw [dotProduct_mulVec_blockDiagonal']
    simp only [dotProduct_mulVec_fromBlocks_one]
    rw [Finset.sum_add_distrib]
end ChainLogWeightSteps
open ChainLogWeightSteps in
theorem ChainLogWeightEqStepLogSum.holds
    (hg : GaussianNumberByLevels)
    (hs : SlotCoordsIsometry)
    (hm : TransportCoordsTriangular)
    (hl : ChainLogRadiiAreStepLogRadii)
    (hh : StepChartHessiansPosDef)
    (hA : ExistsLevelFormMap)
    (hc : TreeCoordsTransversalSlice)
    (hf : FibreHessianSumOverSteps) :
    ChainLogWeightEqStepLogSum := by
  classical
  intro a ha L hL k n hk hn ρ h0 h1
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c₁, hc₁, hcE⟩ := hc a ha L hL k n hn ρ h0 h1
  refine ⟨(Fintype.card (ChainCoord L n (k + 1)) : ℝ) / 2 * Real.log (2 * Real.pi) + Real.log c₁, ?_⟩
  filter_upwards [hcE, hA a ha L hL k n hn ρ h0 h1, hf a ha L hL k n hn ρ h0 h1,
    hh a ha L hL (k + 1) n hn ρ h0 h1] with V eC eA eF eH W hW X hX hR
  obtain ⟨A, hdet, hAu⟩ := eA W hW X hX hR
  obtain ⟨N', hN', hN't, hF⟩ := eF W hW X hX hR
  obtain ⟨N, hN, hNs, hNt⟩ := hm L hL k n hn X hX.compact
  obtain ⟨-, -, p, -, -, hp, -⟩ := hs L hL k n hn
  have hslot : ∀ ξ ξ' : LevelForms L n (k + 1),
      slotCoords (ξ + ξ') = slotCoords ξ + slotCoords ξ' := fun ξ ξ' => by
    rw [← hp, ← hp, ← hp, map_add]
    rfl
  have hslots : ∀ (r : ℝ) (ξ : LevelForms L n (k + 1)),
      slotCoords (r • ξ) = r • slotCoords ξ := fun r ξ => by
    rw [← hp, ← hp, map_smul]
    rfl
  have hadd : ∀ ξ ξ' : LevelForms L n (k + 1), transportCoords X (ξ + ξ') =
      transportCoords X ξ + transportCoords X ξ' := fun ξ ξ' =>
    eq_of_sub_mulVec_eq_of_strictLower coordLevel N hN (by
      rw [← hNs, hslot, hNs ξ, hNs ξ', Matrix.mulVec_add]
      abel)
  have hsmul : ∀ (r : ℝ) (ξ : LevelForms L n (k + 1)), transportCoords X (r • ξ) =
      r • transportCoords X ξ := fun r ξ =>
    eq_of_sub_mulVec_eq_of_strictLower coordLevel N hN (by
      rw [← hNs, hslots, hNs ξ, Matrix.mulVec_smul, smul_sub])
  let l : LevelForms L n (k + 1) →ₗ[ℝ] EuclideanSpace ℝ (TreeChainCoord L n (k + 1)) :=
    { toFun := fun ξ => WithLp.toLp 2 fun e => transportCoords X ξ ⟨e.1, .inr e.2⟩
      map_add' := fun ξ ξ' => by
        ext e
        simp [hadd]
      map_smul' := fun r ξ => by
        ext e
        simp [hsmul] }
  have hlv : ∀ ξ e, l ξ e = transportCoords X ξ ⟨e.1, .inr e.2⟩ := fun ξ e => rfl
  obtain ⟨hsl, hvol⟩ := eC W hW X hX hR l hlv
  refine ⟨EuclideanSpace ℝ (TreeChainCoord L n (k + 1)), inferInstance, inferInstance,
    inferInstance, l, hsl, ?_⟩
  have hAne : A.det ≠ 0 := by
    rw [hdet]
    exact (Real.exp_pos _).ne'
  have hH : ∀ j : Fin (k + 1), (chartHessianAtStep a ρ L n (k + 1) j V).PosDef := fun j => eH j j.2
  have hnum := levelGaussianNumber_eq_det hg hs hL hn a ρ V X N N' A hN hNs hNt hN' hN't hF hAne
    hAu hH l hlv
  have hdG := det_blockHessian a ρ L n (k + 1) V
  have hpos : ∀ j : Fin (k + 1), 0 < (chartHessianAtStep a ρ L n (k + 1) j V).det :=
    fun j => (hH j).det_pos
  have hGpos : 0 < (blockHessian a ρ L n (k + 1) V).det := by
    rw [hdG]
    exact Finset.prod_pos fun j _ => hpos j
  have h2π : 0 < 2 * Real.pi := by positivity
  have hstep : ∀ j : Fin (k + 1), stepLogAmplitude (F := frameAtStep L n (k + 1) j) a ρ
      (topFieldAtStep a ρ L n (k + 1) j V) =
      -(1 / 2) * Real.log (chartHessianAtStep a ρ L n (k + 1) j V).det +
        (∑ b, haarLogRatio (minimizerCoordAtStep a ρ L n (k + 1) j V b)) +
        3 / 2 * ∑ c ∈ innerBonds (finiteCells (frameAtStep L n (k + 1) j))
            (frameAtStep L n (k + 1) j).top,
          Real.log ‖contourAverage
            (fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n (k + 1) j V) 0) c‖ := by
    intro j
    unfold stepLogAmplitude chartHessianAtStep minimizerCoordAtStep
    congr!
  unfold chainLogWeight
  rw [hnum, hvol, hl a ρ L hL (k + 1) n hn V X hR, chainStepLogSum_eq_sum_fin,
    Finset.sum_congr rfl fun j _ => hstep j]
  rw [hdet, abs_of_pos (Real.exp_pos _)]
  have e₁ : Real.log ((2 * Real.pi) ^ ((Fintype.card (ChainCoord L n (k + 1)) : ℝ) / 2) *
      (blockHessian a ρ L n (k + 1) V).det ^ (-(1 / 2) : ℝ) *
      Real.exp (∑ j : Fin (k + 1), ∑ b, haarLogRatio (minimizerCoordAtStep a ρ L n (k + 1) j V b)) *
        c₁) =
      (Fintype.card (ChainCoord L n (k + 1)) : ℝ) / 2 * Real.log (2 * Real.pi) +
        -(1 / 2) * ∑ j : Fin (k + 1), Real.log (chartHessianAtStep a ρ L n (k + 1) j V).det +
        (∑ j : Fin (k + 1), ∑ b, haarLogRatio (minimizerCoordAtStep a ρ L n (k + 1) j V b)) +
        Real.log c₁ := by
    rw [Real.log_mul (by positivity) hc₁.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by positivity) (by positivity), Real.log_rpow h2π, Real.log_rpow hGpos,
      Real.log_exp, hdG, Real.log_prod (fun j _ => (hpos j).ne')]
  rw [e₁, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring
end YangMills.Construction.RunningCouplingSlope
end
