import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWhole
import YangMills.Construction.RunningCouplingSlope.SymbolsOfThePlainSaddles
import YangMills.Construction.RunningCouplingSlope.TheFreeFormXIsNonnegative
import YangMills.Construction.RunningCouplingSlope.TheNoiseAtOneOnTheWholeIsPositive
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.StabilityOfTheSaddleSystemNearZeroProof
import YangMills.Construction.Towers.TheIteratedDriftIsGivenByItsKernelProof
import YangMills.Construction.Towers.TheMassiveJetsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FullLattice.SaddleSymbols
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FreeCoercivity
open YangMills.Construction.Tower.FreeResolvents (trivialRescaledOperators)
section WeightedInner
variable {J : Type} [Fintype J] (w : J → ℝ)
private theorem wInner_smul (c : ℂ) (h f : J → ℂ) :
    PeriodicOperators.wInner w h (c • f) = c * PeriodicOperators.wInner w h f := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_smul_right <;> assumption
private theorem wInner_conj (h h' : J → ℂ) :
    starRingEnd ℂ (PeriodicOperators.wInner w h h') = PeriodicOperators.wInner w h' h := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.conj_wInner <;> assumption
private theorem eq_zero_of_wInner_self_re_nonpos {w : J → ℝ} (hw : ∀ i, 0 < w i) {h : J → ℂ}
    (h0 : (PeriodicOperators.wInner w h h).re ≤ 0) : h = 0 := by apply _root_.YangMills.Construction.Tower.SaddleStability.eq_zero_of_re_wInner_self_nonpos <;> assumption
end WeightedInner
private theorem quotWeight_pos {I : PeriodicData} (hI : IsPeriodic I) (c : I.UnitQuot) :
    0 < I.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
section Coercive
variable {A B : PeriodicData}
private theorem eq_zero_of_saddle_system [Finite A.UnitQuot] [Finite B.UnitQuot]
    (hA : ∀ c, 0 < A.quotWeight 1 c) (hB : ∀ c, 0 < B.quotWeight 1 c)
    {P Ξ K G : QuotHom A A} {Q : QuotHom A B} {Qt : QuotHom B A} {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c')
    (hΞ : LoewnerLE ((c : ℂ) • (K + scalarQuotHom A 1)) Ξ)
    (hK : LoewnerLE (scalarQuotHom A 0) K)
    (hadj : IsAdjointQuotHom Q Qt)
    (hS : LoewnerLE (scalarQuotHom B c') (Q.comp (G.comp Qt)))
    (hP : ∀ b, Q b = 0 → P b = Ξ b) {t : ℂ} (ht : t ≠ 0) {b : A.UnitQuot → ℂ} {n : B.UnitQuot → ℂ}
    (h₁ : P b + t • Qt n = 0) (h₂ : Q b = 0) : b = 0 ∧ n = 0 := by
  exact _root_.YangMills.Construction.Tower.SaddleStability.saddle_kernel_trivial
    hA hB hc hc' hΞ hK hadj hS hP ht h₁ h₂
end Coercive
section DisjointSum
variable {A B : PeriodicData}
private def quotSplit : (A.disjSum B).UnitQuot → A.UnitQuot ⊕ B.UnitQuot :=
  Quot.lift (Sum.map (A.mkQuot 1) (B.mkQuot 1)) (by
    rintro (a | a) _ ⟨n, rfl⟩
    · exact congrArg Sum.inl (Quot.sound ⟨n, rfl⟩)
    · exact congrArg Sum.inr (Quot.sound ⟨n, rfl⟩))
private def inlQuot : A.UnitQuot → (A.disjSum B).UnitQuot :=
  Quot.lift (fun a => (A.disjSum B).mkQuot 1 (Sum.inl a)) (by
    rintro a _ ⟨n, rfl⟩
    exact Quot.sound ⟨n, rfl⟩)
private def inrQuot : B.UnitQuot → (A.disjSum B).UnitQuot :=
  Quot.lift (fun a => (A.disjSum B).mkQuot 1 (Sum.inr a)) (by
    rintro a _ ⟨n, rfl⟩
    exact Quot.sound ⟨n, rfl⟩)
private theorem quotSplit_inlQuot (c : A.UnitQuot) : quotSplit (B := B) (inlQuot c) = Sum.inl c := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep c
  rfl
private theorem quotSplit_inrQuot (c : B.UnitQuot) : quotSplit (A := A) (inrQuot c) = Sum.inr c := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep c
  rfl
private def quotSumEquiv : A.UnitQuot ⊕ B.UnitQuot ≃ (A.disjSum B).UnitQuot where
  toFun := Sum.elim inlQuot inrQuot
  invFun := quotSplit
  left_inv := by
    rintro (c | c)
    · exact quotSplit_inlQuot c
    · exact quotSplit_inrQuot c
  right_inv := by
    intro c
    obtain ⟨a | a, rfl⟩ := Quot.exists_rep c
    · rfl
    · rfl
private instance [Finite A.UnitQuot] [Finite B.UnitQuot] : Finite (A.disjSum B).UnitQuot :=
  Finite.of_equiv _ quotSumEquiv
private theorem apply_eq_sum_linearMapEntry {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (b : J → ℂ) (c' : J') : M b c' = ∑ c, linearMapEntry M c' c * b c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
private def blockMatrixEntry (M₁₁ : QuotHom A A) (M₁₂ : QuotHom B A) (M₂₁ : QuotHom A B)
    (M₂₂ : QuotHom B B) : A.UnitQuot ⊕ B.UnitQuot → A.UnitQuot ⊕ B.UnitQuot → ℂ
  | .inl d', .inl d => linearMapEntry M₁₁ d' d
  | .inl d', .inr d => linearMapEntry M₁₂ d' d
  | .inr d', .inl d => linearMapEntry M₂₁ d' d
  | .inr d', .inr d => linearMapEntry M₂₂ d' d
private theorem symbolHom_apply_blocks [Finite A.UnitQuot] [Finite B.UnitQuot]
    {T : (A.disjSum B).Carrier → (A.disjSum B).Carrier → ℂ} {κ : Fin 4 → ℂ}
    {M₁₁ : QuotHom A A} {M₁₂ : QuotHom B A} {M₂₁ : QuotHom A B} {M₂₂ : QuotHom B B}
    (h₁₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inl a) =
      carrierEntry M₁₁ a' a)
    (h₁₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inr a) =
      carrierEntry M₁₂ a' a)
    (h₂₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inl a) =
      carrierEntry M₂₁ a' a)
    (h₂₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inr a) =
      carrierEntry M₂₂ a' a)
    (f : (A.disjSum B).UnitQuot → ℂ) :
    (∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f (inlQuot c') =
      M₁₁ (f ∘ inlQuot) c' + M₁₂ (f ∘ inrQuot) c') ∧
    ∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f (inrQuot c') =
      M₂₁ (f ∘ inlQuot) c' + M₂₂ (f ∘ inrQuot) c' := by
  let := Fintype.ofFinite A.UnitQuot
  let := Fintype.ofFinite B.UnitQuot
  let E : (A.disjSum B).UnitQuot → (A.disjSum B).UnitQuot → ℂ := fun c' c =>
    blockMatrixEntry M₁₁ M₁₂ M₂₁ M₂₂ (quotSplit c') (quotSplit c)
  have hspec : ∀ (c' c : (A.disjSum B).UnitQuot) (ι' ι : (A.disjSum B).Carrier),
      (A.disjSum B).mkQuot 1 ι' = c' → (A.disjSum B).mkQuot 1 ι = c →
      fourierSymbol (A.disjSum B) (A.disjSum B) T κ ι' ι = E c' c := by
    rintro _ _ (a' | a') (a | a) rfl rfl
    · exact h₁₁ a' a
    · exact h₁₂ a' a
    · exact h₂₁ a' a
    · exact h₂₂ a' a
  have hE : descendMatrix (A.disjSum B) (A.disjSum B) 1
      (fourierSymbol (A.disjSum B) (A.disjSum B) T κ) = E := by
    funext c' c
    obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
    obtain ⟨ι, rfl⟩ := Quot.exists_rep c
    have hz : ∃ z, ∀ j' j, (A.disjSum B).mkQuot 1 j' = Quot.mk _ ι' →
        (A.disjSum B).mkQuot 1 j = Quot.mk _ ι →
        fourierSymbol (A.disjSum B) (A.disjSum B) T κ j' j = z := ⟨_, hspec _ _⟩
    have e := Classical.epsilon_spec hz ι' ι rfl rfl
    exact e.symm.trans (hspec _ _ ι' ι rfl rfl)
  have hmap : ∀ c', symbolHom (A.disjSum B) (A.disjSum B) T κ f c' =
      ∑ d : A.UnitQuot ⊕ B.UnitQuot, E c' (quotSumEquiv d) * f (quotSumEquiv d) := by
    intro c'
    rw [symbolHom, hE, linearMapOfEntries_eq_applyKernel, applyKernel,
      ← (quotSumEquiv (A := A) (B := B)).tsum_eq, tsum_fintype]
  constructor
  · intro c'
    rw [hmap, Fintype.sum_sum_type, apply_eq_sum_linearMapEntry M₁₁, apply_eq_sum_linearMapEntry M₁₂]
    congr 1
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ M₂₂ (quotSplit (inlQuot c')) (quotSplit (inlQuot d)) * _ = _
      rw [quotSplit_inlQuot, quotSplit_inlQuot]
      rfl
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ M₂₂ (quotSplit (inlQuot c')) (quotSplit (inrQuot d)) * _ = _
      rw [quotSplit_inlQuot, quotSplit_inrQuot]
      rfl
  · intro c'
    rw [hmap, Fintype.sum_sum_type, apply_eq_sum_linearMapEntry M₂₁, apply_eq_sum_linearMapEntry M₂₂]
    congr 1
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ M₂₂ (quotSplit (inrQuot c')) (quotSplit (inlQuot d)) * _ = _
      rw [quotSplit_inrQuot, quotSplit_inlQuot]
      rfl
    · refine Finset.sum_congr rfl fun d _ => ?_
      show blockMatrixEntry M₁₁ M₁₂ M₂₁ M₂₂ (quotSplit (inrQuot c')) (quotSplit (inrQuot d)) * _ = _
      rw [quotSplit_inrQuot, quotSplit_inrQuot]
      rfl
private theorem isUnit_symbolHom_of_blocks [Finite A.UnitQuot] [Finite B.UnitQuot]
    {T : (A.disjSum B).Carrier → (A.disjSum B).Carrier → ℂ} {κ : Fin 4 → ℂ}
    {M₁₁ : QuotHom A A} {M₁₂ : QuotHom B A} {M₂₁ : QuotHom A B} {M₂₂ : QuotHom B B}
    (h₁₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inl a) =
      carrierEntry M₁₁ a' a)
    (h₁₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inl a') (Sum.inr a) =
      carrierEntry M₁₂ a' a)
    (h₂₁ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inl a) =
      carrierEntry M₂₁ a' a)
    (h₂₂ : ∀ a' a, fourierSymbol (A.disjSum B) (A.disjSum B) T κ (Sum.inr a') (Sum.inr a) =
      carrierEntry M₂₂ a' a)
    (hinj : ∀ b n, M₁₁ b + M₁₂ n = 0 → M₂₁ b + M₂₂ n = 0 → b = 0 ∧ n = 0) :
    IsUnit (symbolHom (A.disjSum B) (A.disjSum B) T κ :
      Module.End ℂ ((A.disjSum B).UnitQuot → ℂ)) := by
  set M := symbolHom (A.disjSum B) (A.disjSum B) T κ with hM
  have hker : ∀ f, M f = 0 → f = 0 := by
    intro f hf
    obtain ⟨hl, hr⟩ := symbolHom_apply_blocks h₁₁ h₁₂ h₂₁ h₂₂ f
    have e₁ : M₁₁ (f ∘ inlQuot) + M₁₂ (f ∘ inrQuot) = 0 := by
      funext c'
      have := hl c'
      rw [← hM, hf] at this
      exact this.symm
    have e₂ : M₂₁ (f ∘ inlQuot) + M₂₂ (f ∘ inrQuot) = 0 := by
      funext c'
      have := hr c'
      rw [← hM, hf] at this
      exact this.symm
    obtain ⟨hb, hn⟩ := hinj _ _ e₁ e₂
    funext c
    obtain ⟨d | d, rfl⟩ := quotSumEquiv.surjective c
    · exact congrFun hb d
    · exact congrFun hn d
  have hinjM : Function.Injective M := by
    intro f f' e
    have := hker (f - f') (by rw [map_sub, e, sub_self])
    exact sub_eq_zero.1 this
  rw [Module.End.isUnit_iff]
  exact ⟨hinjM, LinearMap.injective_iff_surjective.1 hinjM⟩
private theorem carrierEntry_smul {I I' : PeriodicData} (c : ℂ) (M : QuotHom I I') (ι' : I'.Carrier)
    (ι : I.Carrier) : carrierEntry (c • M) ι' ι = c * carrierEntry M ι' ι := by
  simp [carrierEntry, linearMapEntry]
end DisjointSum
section Maps
variable {N N' : Type}
private theorem eq_apply_single_of_represents {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (i' : N') (i : N) : T i' i = M (open Classical in Pi.single i 1) i' := by
  classical
  have h1 := congrFun (h (Pi.single i 1)).2 i'
  rw [← h1, applyKernel, tsum_eq_single i]
  · simp
  · intro j hj
    simp [hj]
abbrev _root_.YangMills.SharedProofs.p81620 := @eq_apply_single_of_represents
private theorem kernelOfMap_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) : kernelOfMap M = T := by apply _root_.YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof.kernelOfMap_eq <;> assumption
private def blockKernel {N N' : Type} (X : KernelMatrix N N) (Mt : KernelMatrix N' N)
    (M : KernelMatrix N N') (G : KernelMatrix N' N') : KernelMatrix (N ⊕ N') (N ⊕ N') :=
  fun ι' ι => match ι', ι with
    | .inl i', .inl i => X i' i
    | .inl i', .inr c => Mt i' c
    | .inr c', .inl i => M c' i
    | .inr c', .inr c => G c' c
end Maps
section Flat
variable {L k : ℕ}
private theorem ofPauliCoeffs_mem_traceless {σ : Type} (f : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs f x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem ofCoeffs_mem_complexEdgeForms (hL : Conventions.IsAdmissibleBlockingFactor L)
    (f : Fin 3 × FullSpace.PositiveEdge (meshAt L k 0) → ℂ) :
    (FullSpace.edgePauliCoordinates L k 0).ofCoeffs f ∈ FullSpace.complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedDriftKernel.ofCoeffs_mem <;> assumption
private theorem gaugeFieldOfForm_zero :
    FullSpace.BackgroundJets.gaugeFieldOfForm L k 0 = fun _ => 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.gaugeFieldOfForm_zero <;> assumption
end Flat
open YangMills.Construction.Tower.FullSpace.RescaledConditions in
private theorem meanKernels_at_trivialField {L k : ℕ} (hP : MeanMapsAtTrivialField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hOne : Tower.RescaledConditions.TrivialRelations (vertexCoordinate (FullSpace.Vertex L k 0))
      (FullSpace.edgePauliCoordinates L k 0) (vertexCoordinate (FullSpace.Vertex L k k)) (FullSpace.edgePauliCoordinates L k k)
      (vertexCoordinate (FullSpace.Face L k 0)) (FullSpace.rescaledOperators L k fun _ => 1)
      FullSpace.scaledVertexCoboundary FullSpace.scaledEdgeCoboundary FullSpace.scaledVertexCoboundary
      (FullSpace.crossingSmoothingIter L k k) (FullSpace.vertexSmoothingIter L k k)) :
    meanKernelQ L k (fun _ => 1) = (trivialRescaledOperators L k).Q ∧
      meanKernelR L k (fun _ => 1) = (trivialRescaledOperators L k).R := by
  obtain ⟨-, -, -, hB, hS⟩ := hP L hL k hk
  constructor
  · have hm : (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L k k)
        (fun B => finestMesh L k • meanCovariant (fun _ => 1) k B) =
        (FullSpace.edgePauliCoordinates L k 0).mapOnCoeffs (FullSpace.edgePauliCoordinates L k k)
          (fun B => (FullSpace.rescaledOperators L k fun _ => 1).eta •
            FullSpace.crossingSmoothingIter L k k B) := by
      funext f
      show (FullSpace.edgePauliCoordinates L k k).coeffs
        (finestMesh L k • meanCovariant (fun _ => 1) k ((FullSpace.edgePauliCoordinates L k 0).ofCoeffs f)) = _
      rw [hB k le_rfl _ (ofCoeffs_mem_complexEdgeForms hL f)]
      rfl
    exact (congrArg kernelOfMap hm).trans (kernelOfMap_eq hOne.Q_represents)
  · have hm : (vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k k))
        (meanCubeAverage (fun _ => 1) k) =
        (vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs (vertexCoordinate (FullSpace.Vertex L k k))
          (FullSpace.vertexSmoothingIter L k k) := by
      funext f
      exact congrArg (vertexCoordinate (FullSpace.Vertex L k k)).coeffs
        (hS k le_rfl _ (fun x _ => ofPauliCoeffs_mem_traceless f x))
    exact (congrArg kernelOfMap hm).trans (kernelOfMap_eq hOne.R_represents)
theorem meanSaddleSymbolsInvertible_of_conditions (hPlain : MeanMapsAtTrivialField)
    (hXn : FreeXSymbolNonneg)
    (hNoise : NoiseCovarianceAtIdentityPositive)
    (hCoercive : Tower.FreeCoercivity.FreeOperatorsCoercive)
    (hReal : Tower.FreeSymbolsAtRealPoints)
    (hFacts : Tower.RescaledConditions.Holds)
    (hIndex : PeriodicOperators.TowerIndexSets.Claim) (hSymbols : PeriodicOperators.StripSymbols.Claim) :
    MeanSaddleSymbolsInvertible := by
  intro a ha L hS k hk κ₀
  have hκ : toComplexVec κ₀ ∈ realDualPoints := fun j => by simp [toComplexVec]
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = toComplexVec κ₀ := ⟨_, rfl⟩
  rw [← hκdef] at hκ ⊢
  obtain ⟨cXi, hcXi, cY, hcY, cC, hcC, hc⟩ := hCoercive
  obtain ⟨hops, -, -, hreal⟩ := hc L hS k hk
  obtain ⟨hS0, hB0, -⟩ := hIndex L hS k 0 (Nat.zero_le k)
  obtain ⟨hSk, hBk, -⟩ := hIndex L hS k k le_rfl
  obtain ⟨-, -, -, -, -, hOne, -⟩ := (hFacts L hS k hk).2
  obtain ⟨eQ, eR⟩ := meanKernels_at_trivialField hPlain hS hk hOne
  have : Finite (colourEdges L k 0).UnitQuot := hB0.finite_quot
  have : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have : Finite (colourVertices L k 0).UnitQuot := hS0.finite_quot
  have : Finite (colourVertices L k k).UnitQuot := hSk.finite_quot
  have facts : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ (T : I'.Carrier → I.Carrier → ℂ), IsPeriodicKernel I I' T →
        SymbolSummableAt I I' T κ → StripSymbols.PointwiseCalculus I I' T κ :=
    fun hI hI' T hT hf => (hSymbols.2.1 _ _ hI hI').2.1 T κ hT hf
  obtain ⟨-, hr⟩ := hreal κ hκ
  refine ⟨?_, ?_⟩
  · obtain ⟨hK, -, hadj, -, hQt, -⟩ := hReal L hS k hk κ hκ
    obtain ⟨hXeq, hXpos⟩ := hXn L hS k hk κ hκ
    obtain ⟨hperN, hN⟩ := hNoise a ha L hS k hk k le_rfl
    obtain ⟨fN, hNform⟩ := hN κ hκ
    have fQ := hops.Q.2.2 κ (Set.mem_univ κ)
    have fQt := hops.Qt.2.2 κ (Set.mem_univ κ)
    have fXi := hops.Xi.2.2 κ (Set.mem_univ κ)
    have FQ := facts hB0 hBk _ hops.Q.1 fQ
    have FQt := facts hBk hB0 _ hops.Qt.1 fQt
    have FXi := facts hB0 hB0 _ hops.Xi.1 fXi
    have FN := facts hBk hBk _ hperN fN
    obtain ⟨-, hper, hform, -⟩ := FQt.comp (colourEdges L k 0) hB0 _ hops.Q.1 fQ
    obtain ⟨hperX, hformX, -⟩ := FXi.linComb _ hper hform 1 (-1)
    have eX : StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).Xi
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) =
        (trivialRescaledOperators L k).X := by
      funext a b
      simp [StripSymbols.linCombKernel, RescaledOperators.X, sub_eq_add_neg]
    have hperX' : IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0)
        (trivialRescaledOperators L k).X :=
      Eq.mp (congrArg (fun T => IsPeriodicKernel (colourEdges L k 0) (colourEdges L k 0) T) eX)
        hperX
    have hformX' : SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0)
        (trivialRescaledOperators L k).X κ :=
      Eq.mp (congrArg (fun T => SymbolSummableAt (colourEdges L k 0) (colourEdges L k 0) T κ) eX)
        hformX
    have FX := facts hB0 hB0 _ hperX' hformX'
    have hav := hr.edge_lower
    unfold edgeResolventConjugate at hav
    rw [hQt] at hav
    have eT : coeffZero (colourEdges L k 0) (FullSpace.vectorIndices L k)
        (FullSpace.vectorIndices L k) (edgeSaddleOfForm a L k) =
        blockKernel (trivialRescaledOperators L k).X (trivialRescaledOperators L k).Qt
          (trivialRescaledOperators L k).Q
          (fun c' c => -noiseCovariance a L k (fun _ => 1) k c' c) := by
      show edgeSaddle a L k (FullSpace.BackgroundJets.gaugeFieldOfForm L k 0) = _
      rw [gaugeFieldOfForm_zero]
      funext ι' ι
      rcases ι' with i' | c' <;> rcases ι with i | c
      · rfl
      · show meshTranspose (finestMesh L k) (meshAt L k k)
          (meanKernelQ L k fun _ => 1) i' c = _
        rw [eQ]
        rfl
      · show meanKernelQ L k (fun _ => 1) c' i = _
        rw [eQ]
        rfl
      · rfl
    rw [eT]
    refine isUnit_symbolHom_of_blocks
      (M₁₁ := symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ)
      (M₁₂ := symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ)
      (M₂₁ := symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ)
      (M₂₂ := (-1 : ℂ) • symbolHom (colourEdges L k k) (colourEdges L k k)
        (noiseCovariance a L k (fun _ => 1) k) κ) ?_ ?_ ?_ ?_ ?_
    · intro i' i
      rw [FX.carrierEntry_symbolHom]
      rfl
    · intro i' i
      rw [FQt.carrierEntry_symbolHom]
      rfl
    · intro i' i
      rw [FQ.carrierEntry_symbolHom]
      rfl
    · intro i' i
      rw [carrierEntry_smul, FN.carrierEntry_symbolHom]
      show (∑' n, symbolSummand _ _ _ κ _ _ n) =
        _ * ∑' n, symbolSummand (colourEdges L k k) (colourEdges L k k)
          (noiseCovariance a L k (fun _ => 1) k) κ i' i n
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      refine (neg_mul _ _).trans ?_
      exact (neg_one_mul _).symm
    · intro b n h₁ h₂
      let := Fintype.ofFinite (colourEdges L k 0).UnitQuot
      let := Fintype.ofFinite (colourEdges L k k).UnitQuot
      have hQb : symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ b =
          symbolHom (colourEdges L k k) (colourEdges L k k)
            (noiseCovariance a L k (fun _ => 1) k) κ n := by
        have e := h₂
        simp only [LinearMap.smul_apply, neg_smul, one_smul] at e
        exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using e)
      have hXb : symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b =
          (-1 : ℂ) • symbolHom (colourEdges L k k) (colourEdges L k 0)
            (trivialRescaledOperators L k).Qt κ n := by
        rw [neg_smul, one_smul]
        exact eq_neg_of_add_eq_zero_left h₁
      have e₁ : PeriodicOperators.wInner ((colourEdges L k 0).quotWeight 1) b
          (symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt κ n) =
          starRingEnd ℂ (PeriodicOperators.wInner ((colourEdges L k k).quotWeight 1) n
            (symbolHom (colourEdges L k k) (colourEdges L k k)
              (noiseCovariance a L k (fun _ => 1) k) κ n)) := by
        rw [← hQb, hadj b n, wInner_conj]
      have e₂ : (PeriodicOperators.wInner ((colourEdges L k 0).quotWeight 1) b
          (symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b)).re =
          -(PeriodicOperators.wInner ((colourEdges L k k).quotWeight 1) n
            (symbolHom (colourEdges L k k) (colourEdges L k k)
              (noiseCovariance a L k (fun _ => 1) k) κ n)).re := by
        rw [hXb, wInner_smul, e₁]
        simp
      have hx := hXpos b
      have hn := (hNform n).2 hk
      have hinv : 0 < a⁻¹ := inv_pos.2 ha
      have hnn : (PeriodicOperators.wInner ((colourEdges L k k).quotWeight 1) n n).re ≤ 0 := by
        by_contra hpos
        have := mul_pos hinv (not_le.1 hpos)
        linarith
      have hn0 : n = 0 := eq_zero_of_wInner_self_re_nonpos (quotWeight_pos hBk) hnn
      have hQ0 : symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q κ b = 0 := by
        rw [hQb, hn0, map_zero]
      have hX0 : symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X κ b = 0 := by
        rw [hXb, hn0, map_zero, smul_zero]
      have hXi0 : symbolHom (colourEdges L k 0) (colourEdges L k 0)
          (trivialRescaledOperators L k).Xi κ b = 0 := by
        have e := LinearMap.congr_fun hXeq b
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, hQ0, map_zero, sub_zero] at e
        exact e.symm.trans hX0
      refine ⟨(eq_zero_of_saddle_system (quotWeight_pos hB0) (quotWeight_pos hBk) hcXi.1 hcC.1
        hr.Xi_lower hK hadj hav (P := symbolHom (colourEdges L k 0) (colourEdges L k 0)
          (trivialRescaledOperators L k).Xi κ) (fun _ _ => rfl) one_ne_zero (n := 0) ?_ hQ0).1, hn0⟩
      simp [hXi0]
  · obtain ⟨-, hK, -, hadj, -, hRt⟩ := hReal L hS k hk κ hκ
    have fR := hops.R.2.2 κ (Set.mem_univ κ)
    have fRt := hops.Rt.2.2 κ (Set.mem_univ κ)
    have fDelta := hops.Delta.2.2 κ (Set.mem_univ κ)
    have FR := facts hS0 hSk _ hops.R.1 fR
    have FRt := facts hSk hS0 _ hops.Rt.1 fRt
    have FDelta := facts hS0 hS0 _ hops.Delta.1 fDelta
    obtain ⟨-, hper, hform, hprod⟩ := FRt.comp (colourVertices L k 0) hS0 _ hops.R.1 fR
    obtain ⟨-, -, hmapY⟩ := FDelta.linComb _ hper hform 1 1
    have eY : StripSymbols.linCombKernel 1 1 (trivialRescaledOperators L k).Delta
        (compKernel (trivialRescaledOperators L k).Rt (trivialRescaledOperators L k).R) =
        (trivialRescaledOperators L k).Y := by
      funext a b
      simp [StripSymbols.linCombKernel, RescaledOperators.Y]
    have hmapY' := (congrArg (fun T => symbolHom (colourVertices L k 0) (colourVertices L k 0) T κ)
      eY).symm.trans hmapY
    have hP : ∀ b, symbolHom (colourVertices L k 0) (colourVertices L k k)
        (trivialRescaledOperators L k).R κ b = 0 →
        symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta κ b =
          symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Y κ b := by
      intro b hb
      rw [hmapY', hprod]
      simp [hb]
    have hav := hr.vertex_lower
    unfold vertexResolventConjugate at hav
    rw [hRt] at hav
    have eT : coeffZero (colourEdges L k 0) (FullSpace.ghostIndices L k)
        (FullSpace.ghostIndices L k) (vertexSaddleOfForm L k) =
        blockKernel (trivialRescaledOperators L k).Delta (trivialRescaledOperators L k).Rt
          (trivialRescaledOperators L k).R (fun _ _ => 0) := by
      show vertexSaddle L k (FullSpace.BackgroundJets.gaugeFieldOfForm L k 0) = _
      rw [gaugeFieldOfForm_zero]
      funext ι' ι
      rcases ι' with i' | c' <;> rcases ι with i | c
      · rfl
      · rfl
      · show meanKernelR L k (fun _ => 1) c' i = _
        rw [eR]
        rfl
      · rfl
    rw [eT]
    refine isUnit_symbolHom_of_blocks
      (M₁₁ := symbolHom (colourVertices L k 0) (colourVertices L k 0) (trivialRescaledOperators L k).Delta κ)
      (M₁₂ := symbolHom (colourVertices L k k) (colourVertices L k 0) (trivialRescaledOperators L k).Rt κ)
      (M₂₁ := symbolHom (colourVertices L k 0) (colourVertices L k k) (trivialRescaledOperators L k).R κ)
      (M₂₂ := 0) ?_ ?_ ?_ ?_ ?_
    · intro a' a
      rw [FDelta.carrierEntry_symbolHom]
      rfl
    · intro a' a
      rw [FRt.carrierEntry_symbolHom]
      rfl
    · intro a' a
      rw [FR.carrierEntry_symbolHom]
      rfl
    · intro a' a
      have e : carrierEntry (0 : QuotHom (colourVertices L k k) (colourVertices L k k)) a' a = 0 := by
        simp [carrierEntry, linearMapEntry]
      rw [e]
      show (∑' n, symbolSummand _ _ _ κ _ _ n) = 0
      refine (tsum_congr fun n => ?_).trans tsum_zero
      exact zero_mul _
    · intro b n h₁ h₂
      refine eq_zero_of_saddle_system (quotWeight_pos hS0) (quotWeight_pos hSk) hcY.1 hcC.1 hr.Y_lower hK
        hadj hav hP one_ne_zero (by simpa using h₁) (by simpa using h₂)
end FullLattice.SaddleSymbols
theorem meanSaddleSymbolsInvertible_holds (hPlain : MeanMapsAtTrivialField)
    (hXn : FreeXSymbolNonneg)
    (hNoise : NoiseCovarianceAtIdentityPositive)
    (hCoercive : Tower.FreeCoercivity.FreeOperatorsCoercive)
    (hReal : Tower.FreeSymbolsAtRealPoints)
    (hFacts : Tower.RescaledConditions.Holds)
    (hIndex : PeriodicOperators.TowerIndexSets.Claim)
    (hSymbols : PeriodicOperators.StripSymbols.Claim) :
    MeanSaddleSymbolsInvertible := by apply _root_.YangMills.Construction.RunningCouplingSlope.FullLattice.SaddleSymbols.meanSaddleSymbolsInvertible_of_conditions <;> assumption
end YangMills.Construction.RunningCouplingSlope
end
