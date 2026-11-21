import YangMills.Construction.Towers.BondsOnWhichTheAveragesDependProof
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinity
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.StepKernelsAreHolomorphicAtTheSideInfinity
import YangMills.Construction.Towers.StepKernelsOfTheIteratedAveragesAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterLocality
open _root_.YangMills.Construction.Matrices
open _root_.YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
open _root_.YangMills.Construction.Tower.SupportOfMeans (DefinedAlike DependsOnlyOn)
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (HasEndpointsIn supportEdges
  baseFields)
open _root_.YangMills.Construction.Tower.FullSpace.StepKernels (singleLinkForm
  IsBoundedTracelessEndo StepKernelsAt positiveDoubleCubeLinks)
open _root_.YangMills.Construction.Tower.FullSpace.StepKernelHolomorphy (kernelCoeff)
theorem pauliFamily_mem_traceless (i : Fin 3) :
    ComplexMatrix2.pauliFamily i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoordinateEquiv_symm_coe (z : Fin 3 → ℂ) :
    ((OneLoop.pauliCoordinateEquiv.symm z : ComplexMatrix2.traceless) : ComplexMatrix2) =
      ∑ i, z i • ComplexMatrix2.pauliFamily i := by
  rw [Fin.sum_univ_three]
  rfl
theorem sum_pauliCoeff_smul {M : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless) :
    ∑ i, pauliCoeff i M • ComplexMatrix2.pauliFamily i = M := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem eq_of_pauliCoeff_eq {M N : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless)
    (hN : N ∈ ComplexMatrix2.traceless) (h : ∀ i, pauliCoeff i M = pauliCoeff i N) : M = N := by
  calc M = ∑ i, pauliCoeff i M • ComplexMatrix2.pauliFamily i := (sum_pauliCoeff_smul hM).symm
    _ = ∑ i, pauliCoeff i N • ComplexMatrix2.pauliFamily i := by simp only [h]
    _ = N := sum_pauliCoeff_smul hN
theorem mapsTo_traceless_of_endo {f : ComplexMatrix2 → ComplexMatrix2} {C : ℝ}
    (h : IsBoundedTracelessEndo f C) {M : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless) :
    f M ∈ ComplexMatrix2.traceless := by
  obtain ⟨T, hT, -⟩ := h
  rw [← hT ⟨M, hM⟩]
  exact (T ⟨M, hM⟩).2
theorem eqOn_traceless_of_coeffs {f g : ComplexMatrix2 → ComplexMatrix2} {C D : ℝ}
    (hf : IsBoundedTracelessEndo f C) (hg : IsBoundedTracelessEndo g D)
    (he : ∀ i' i, pauliCoeff i' (f (ComplexMatrix2.pauliFamily i)) =
      pauliCoeff i' (g (ComplexMatrix2.pauliFamily i)))
    {M : ComplexMatrix2} (hM : M ∈ ComplexMatrix2.traceless) : f M = g M := by
  obtain ⟨T, hT, -⟩ := hf
  obtain ⟨S, hS, -⟩ := hg
  have e : ∀ i, T ⟨ComplexMatrix2.pauliFamily i, pauliFamily_mem_traceless i⟩ =
      S ⟨ComplexMatrix2.pauliFamily i, pauliFamily_mem_traceless i⟩ := fun i =>
    Subtype.ext (eq_of_pauliCoeff_eq (T _).2 (S _).2 fun i' => by
      rw [hT, hS]
      exact he i' i)
  have hs : (⟨M, hM⟩ : ↥ComplexMatrix2.traceless) =
      ∑ i, pauliCoeff i M •
        (⟨ComplexMatrix2.pauliFamily i, pauliFamily_mem_traceless i⟩ : ↥ComplexMatrix2.traceless) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_pauliCoeff_smul hM).symm
  rw [← hT ⟨M, hM⟩, ← hS ⟨M, hM⟩, hs, map_sum, map_sum]
  simp only [map_smul, e]
section OneLattice
variable {a : ℝ}
theorem opposite_isPositivelyOriented_of_not {e : InfiniteLattice.Link a}
    (h : ¬e.IsPositivelyOriented) : e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (e : InfiniteLattice.Link a) : extendOddly f e.opposite = -extendOddly f e := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem complexContourMean_congr (L : ℕ) {a' : ℝ}
    {W W' : InfiniteLattice.Link a' → ComplexMatrix2}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'}
    (h : ∀ σ, ∀ e ∈ contour L y x σ, W e = W' e) :
    complexContourMean L W y x = complexContourMean L W' y x := by
  have hv : contourHolonomies L W y x = contourHolonomies L W' y x := by
    funext σ
    simp only [contourHolonomies, linkHolonomy]
    rw [List.map_congr_left (h σ)]
  simp only [complexContourMean, hv]
end OneLattice
variable {L k : ℕ}
theorem meshAt_pos (hL : IsAdmissibleBlockingFactor L) (j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem covariantSmoothingDeriv_of_not_positive {j : ℕ} (V B : Edge L k j → ComplexMatrix2)
    {c : Edge L k (j + 1)} (hc : ¬c.IsPositivelyOriented) :
    covariantSmoothingDeriv V B c = -covariantSmoothingDeriv V B c.opposite := by
  have hr := opposite_isPositivelyOriented_of_not hc
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv, holLeftDifferential,
    covDiff, Pi.add_apply, extendOddly, if_neg hc, if_pos hr, neg_add]
theorem covariantSmoothingDeriv_opposite (hL : IsAdmissibleBlockingFactor L) {j : ℕ}
    (V B : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1)) :
    covariantSmoothingDeriv V B c.opposite = -covariantSmoothingDeriv V B c := by
  simp only [covariantSmoothingDeriv, complexSmoothingDeriv, holLeftDifferential,
    covDiff, Pi.add_apply]
  rw [extendOddly_opposite (meshAt_pos hL _), extendOddly_opposite (meshAt_pos hL _), neg_add]
theorem remainderGaugeField_congr {A A' : Edge L k 0 → ComplexMatrix2} {e : Edge L k 0}
    (he : e.IsPositivelyOriented) (h : A e = A' e) :
    remainderGaugeField A e = remainderGaugeField A' e := by
  simp only [remainderGaugeField, expForm, expTwist, if_pos he, scaledRemainderForm,
    Pi.smul_apply, h]
theorem polydiscRadius_pos_of_lt {M : ComplexMatrix2}
    (h : ComplexMatrix2.operatorNorm M < polydiscRadius L / 2) : 0 < polydiscRadius L := by
  have h₀ : 0 ≤ ComplexMatrix2.operatorNorm M := norm_nonneg _
  linarith
theorem lt_three_quarters_polydiscRadius {M : ComplexMatrix2}
    (h : ComplexMatrix2.operatorNorm M < polydiscRadius L / 2) :
    ComplexMatrix2.operatorNorm M < 3 / 4 * polydiscRadius L := by
  have := polydiscRadius_pos_of_lt h
  linarith
abbrev IsSmallForm (ρ : ℝ) (A : Edge L k 0 → ComplexMatrix2) : Prop :=
  A ∈ complexEdgeForms (meshAt L k 0) ∧ maxOperatorNorm A ≤ ENNReal.ofReal ρ
section Iterates
variable {ρ : ℝ} (hS : SmallIterates L k ρ)
include hS in
theorem levelwiseMean_eq_some (hP : LevelwiseMeans.Unbounded.UnboundedConditions L k)
    {A : Edge L k 0 → ComplexMatrix2} (hA : IsSmallForm ρ A) {j : ℕ} (hj : j < k) (c : Edge L k j) :
    LevelwiseMeans.Unbounded.levelwiseMean (remainderGaugeField A) j c =
      some (complexIter L k j (remainderGaugeField A) c) := by
  have hV : LevelwiseMeans.Unbounded.IsMeanSequence j
      fun i => complexIter L k i (remainderGaugeField A) :=
    { mem_fields := fun i hi => (hS A hA i (by omega)).1
      norm_sub_one_lt := fun i hi e => by
        have h := (hS A hA i (by omega)).2 e
        have := polydiscRadius_pos_of_lt h
        linarith
      eq_mean := fun i _ c _ => rfl }
  exact hP.sequence_is_levelwise j hj.le _ hV j le_rfl c
include hS in
theorem complexIter_congr (hk : 1 ≤ k) (hP : LevelwiseMeans.Unbounded.UnboundedConditions L k)
    (hR : SupportOfMeans.Unbounded.SideRequirements L k)
    {A A' : Edge L k 0 → ComplexMatrix2} (hA : IsSmallForm ρ A) (hA' : IsSmallForm ρ A') {j : ℕ}
    (hj : j < k) (c : Edge L k j) (h : ∀ e ∈ supportEdges c, A e = A' e) :
    complexIter L k j (remainderGaugeField A) c =
      complexIter L k j (remainderGaugeField A') c := by
  obtain ⟨hfin, -⟩ := hR.finite_nonempty j hj.le c
  have hDep := hR.dependsOnlyOn j hj.le c hfin.toFinset (by simp)
  have hU : remainderGaugeField A ∈ baseFields L k := (hS A hA 0 (by omega)).1
  have hU' : remainderGaugeField A' ∈ baseFields L k := (hS A' hA' 0 (by omega)).1
  have hAl := hDep.definedAlike_of_eqOn _ hU _ hU' fun e he => by
    have he' := hfin.mem_toFinset.1 he
    exact remainderGaugeField_congr he'.1 (h e he')
  exact hAl.2 _ _ (levelwiseMean_eq_some hS hP hA hj c) (levelwiseMean_eq_some hS hP hA' hj c)
end Iterates
theorem mem_cubeOfOrder_zero (y : Vertex L k 0) :
    (y : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) 0 y :=
  ⟨0, by simp, by simp⟩
theorem cubeOfOrder_subset (hZ : BlockPathContourPivotStatement)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y) :
    cubeOfOrder L (meshAt L k 0) j x ⊆ cubeOfOrder L (meshAt L k 0) (j + 1) y := by apply _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded.cubeOfOrder_subset <;> assumption
theorem contour_endpoints_mem_cube (hZ : BlockPathContourPivotStatement)
    (hL : IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) y)
    (σ : ContourOrder L y x) {e : Edge L k j} (he : e ∈ contour L y x σ) :
    (e.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y ∧
      (e.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y := by
  have H := ((hZ L hL k 1 (j + 1) hk (by omega) (by omega)).2.2.2.2.2.2 (by omega)).1
  obtain ⟨ν, hν, hxν⟩ := hx
  obtain ⟨-, -, -, -, hz⟩ := (H.contours y ν (mem_offsetBox_iff.2 hν) x hxν).2 _ ⟨σ, rfl⟩
  exact ⟨hz e.initial (Or.inr (Or.inr ⟨e, he, Or.inl rfl⟩)),
    hz e.terminal (Or.inr (Or.inr ⟨e, he, Or.inr rfl⟩))⟩
structure Setup (L k : ℕ) : Prop where
  paths : BlockPathContourPivotStatement
  admissible : IsAdmissibleBlockingFactor L
  one_le : 1 ≤ k
  means : LevelwiseMeans.Unbounded.UnboundedConditions L k
  support : SupportOfMeans.Unbounded.SideRequirements L k
  kernels : StepKernels.StepKernelBounds
  holomorphic : StepKernelHolomorphy.KernelsHolomorphic
section Induction
variable {ρ : ℝ} (G : Setup L k) (hS : SmallIterates L k ρ)
include hS in
theorem complexIter_small {A : Edge L k 0 → ComplexMatrix2} (hA : IsSmallForm ρ A) {j : ℕ}
    (hj : j < k) :
    complexIter L k j (remainderGaugeField A) ∈
        fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
      ∀ e, ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField A) e - 1) <
        3 / 4 * polydiscRadius L :=
  ⟨(hS A hA j hj).1, fun e => lt_three_quarters_polydiscRadius ((hS A hA j hj).2 e)⟩
include G hS in
theorem iterCovariantDeriv_mem {A : Edge L k 0 → ComplexMatrix2} (hA : IsSmallForm ρ A) :
    ∀ j ≤ k, ∀ B ∈ complexEdgeForms (meshAt L k 0),
      iterCovariantDeriv L k (remainderGaugeField A) j B ∈
        complexEdgeForms (meshAt L k j) := by
  intro j
  induction j with
  | zero => exact fun _ B hB => hB
  | succ j ih =>
    intro hj B hB
    have hC := ih (by omega) B hB
    obtain ⟨h₁, h₂⟩ := complexIter_small hS hA (j := j) (by omega)
    refine ⟨fun c hc => ?_, fun c => covariantSmoothingDeriv_opposite G.admissible _ _ c⟩
    have hKs := G.kernels L G.admissible k j (by omega) c hc _ h₁ h₂
    change covariantSmoothingDeriv _ _ c ∈ ComplexMatrix2.traceless
    rw [hKs.sum_eq_finsum _ hC]
    refine finsum_mem_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
      (fun _ _ => ComplexMatrix2.traceless.add_mem) fun e he => ?_
    exact mapsTo_traceless_of_endo (hKs.kernel_bound e he) (hC.1 e he.2)
include G hS in
theorem iterCovariantDeriv_congr : ∀ j ≤ k, ∀ (c : Edge L k j) (A A' B B' : Edge L k 0 → ComplexMatrix2),
    IsSmallForm ρ A → IsSmallForm ρ A' → B ∈ complexEdgeForms (meshAt L k 0) →
    B' ∈ complexEdgeForms (meshAt L k 0) →
    (∀ e, HasEndpointsIn c e → A e = A' e) → (∀ e, HasEndpointsIn c e → B e = B' e) →
    iterCovariantDeriv L k (remainderGaugeField A) j B c =
      iterCovariantDeriv L k (remainderGaugeField A') j B' c := by
  intro j
  induction j with
  | zero =>
    intro _ c A A' B B' _ _ _ _ _ h
    exact h c ⟨Or.inl (mem_cubeOfOrder_zero c.initial), Or.inr (mem_cubeOfOrder_zero c.terminal)⟩
  | succ j ih =>
    intro hj c A A' B B' hA hA' hB hB' h₁ h₂
    have hjk : j < k := by omega
    have pos : ∀ (c : Edge L k (j + 1)), c.IsPositivelyOriented →
        (∀ e, HasEndpointsIn c e → A e = A' e) → (∀ e, HasEndpointsIn c e → B e = B' e) →
        covariantSmoothingDeriv (complexIter L k j (remainderGaugeField A))
            (iterCovariantDeriv L k (remainderGaugeField A) j B) c =
          covariantSmoothingDeriv (complexIter L k j (remainderGaugeField A'))
            (iterCovariantDeriv L k (remainderGaugeField A') j B') c := by
      intro c hc h₁ h₂
      have hC := iterCovariantDeriv_mem G hS hA j (by omega) B hB
      have hC' := iterCovariantDeriv_mem G hS hA' j (by omega) B' hB'
      obtain ⟨s₁, s₂⟩ := complexIter_small hS hA hjk
      obtain ⟨s₁', s₂'⟩ := complexIter_small hS hA' hjk
      have hKs := G.kernels L G.admissible k j hjk c hc _ s₁ s₂
      have hKs' := G.kernels L G.admissible k j hjk c hc _ s₁' s₂'
      rw [hKs.sum_eq_finsum _ hC, hKs'.sum_eq_finsum _ hC']
      refine finsum_mem_congr rfl fun e he => ?_
      have below : ∀ w, HasEndpointsIn e w → HasEndpointsIn c w := fun w =>
        G.support.hasEndpointsIn_of_doubleBlock j hjk c hc e he.1 w
      rw [ih (by omega) e A A' B B' hA hA' hB hB' (fun w hw => h₁ w (below w hw))
        (fun w hw => h₂ w (below w hw))]
      have hH := G.holomorphic L G.admissible k j hjk c hc
      have small : ∀ V : Edge L k j → ComplexMatrix2,
          V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup →
          (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < 3 / 4 * polydiscRadius L) →
          (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L) →
          V ∈ smallComplexFields L k j ∧
            V ∈ nearIdentityPolydisc L k j (3 / 4 * polydiscRadius L) c :=
        fun V h₁ h₂ h₃ => ⟨⟨h₁, h₃⟩, ⟨fun e _ => h₁.1 e, fun e _ => h₁.2 e⟩, fun e _ => h₂ e⟩
      have hlt : ∀ A₀ : Edge L k 0 → ComplexMatrix2, IsSmallForm ρ A₀ → ∀ e,
          ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField A₀) e - 1) <
            polydiscRadius L := fun A₀ h₀ e => by
        have h := (hS A₀ h₀ j hjk).2 e
        have := polydiscRadius_pos_of_lt h
        linarith
      obtain ⟨v₁, v₂⟩ := small _ s₁ s₂ (hlt A hA)
      obtain ⟨v₁', v₂'⟩ := small _ s₁' s₂' (hlt A' hA')
      have hEq : ∀ e' ∈ doubleCubeLinks L (meshAt L k j) c,
          complexIter L k j (remainderGaugeField A) e' =
            complexIter L k j (remainderGaugeField A') e' := fun e' he' =>
        complexIter_congr hS G.one_le G.means G.support hA hA' hjk e' fun w hw =>
          h₁ w (G.support.hasEndpointsIn_of_doubleBlock j hjk c hc e' he' w hw.2)
      have hconf : DoubleBlockPolydisc.Infinite.fieldOfValues L k j c
            (fun e => complexIter L k j (remainderGaugeField A) e) =
          DoubleBlockPolydisc.Infinite.fieldOfValues L k j c
            (fun e => complexIter L k j (remainderGaugeField A') e) :=
        congrArg _ (funext fun e => hEq e.1 e.2.1)
      refine eqOn_traceless_of_coeffs (hKs.kernel_bound e he) (hKs'.kernel_bound e he)
        (fun i₁ i₂ => ?_) (hC'.1 e he.2)
      have r := hH.local_kernel ⟨e, he.2⟩ he.1 i₂ i₁ _ v₁ v₂
      have r' := hH.local_kernel ⟨e, he.2⟩ he.1 i₂ i₁ _ v₁' v₂'
      exact r.trans ((congrArg (fun V => kernelCoeff V c ⟨e, he.2⟩ i₂ i₁) hconf).trans r'.symm)
    by_cases hc : c.IsPositivelyOriented
    · exact pos c hc h₁ h₂
    · have hr := opposite_isPositivelyOriented_of_not hc
      have sw : ∀ e, HasEndpointsIn c.opposite e → HasEndpointsIn c e := fun e he =>
        ⟨Or.symm he.1, Or.symm he.2⟩
      change covariantSmoothingDeriv _ _ c = covariantSmoothingDeriv _ _ c
      rw [covariantSmoothingDeriv_of_not_positive _ _ hc,
        covariantSmoothingDeriv_of_not_positive _ _ hc,
        pos c.opposite hr (fun e he => h₁ e (sw e he)) fun e he => h₂ e (sw e he)]
include G hS in
theorem iterAdjointCubeAverage_congr : ∀ j ≤ k, ∀ (y : Vertex L k j)
    (A A' : Edge L k 0 → ComplexMatrix2)
    (f f' : Vertex L k 0 → ComplexMatrix2), IsSmallForm ρ A → IsSmallForm ρ A' →
    (∀ x : Vertex L k 0, (x : InfiniteLattice.AmbientSpace) ∈
      cubeOfOrder L (meshAt L k 0) j y → f x = f' x) →
    EqOn A A'
      {e | (e.initial : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) j y ∧
        (e.terminal : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) j y} →
    iterAdjointCubeAverage L k (remainderGaugeField A) j f y =
      iterAdjointCubeAverage L k (remainderGaugeField A') j f' y := by
  intro j
  induction j with
  | zero =>
    intro _ y A A' f f' _ _ h _
    exact h y (mem_cubeOfOrder_zero y)
  | succ j ih =>
    intro hj y A A' f f' hA hA' h₁ h₂
    have hjk : j < k := by omega
    simp only [iterAdjointCubeAverage, adjointCubeAverage]
    refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
    have sub := cubeOfOrder_subset G.paths G.admissible G.one_le hjk (y := y) (x := x) hx
    rw [ih (by omega) x A A' f f' hA hA' (fun z hz => h₁ z (sub hz))
      fun e he => h₂ ⟨sub he.1, sub he.2⟩]
    have hm : complexContourMean L (complexIter L k j (remainderGaugeField A)) y x =
        complexContourMean L (complexIter L k j (remainderGaugeField A')) y x := by
      refine complexContourMean_congr L fun σ e he => ?_
      obtain ⟨e₁, e₂⟩ := contour_endpoints_mem_cube G.paths G.admissible G.one_le hjk hx σ he
      have sub' : ∀ p, p ∈ cubeOfOrder L (meshAt L k 0) j e.initial ∪
            cubeOfOrder L (meshAt L k 0) j e.terminal →
          p ∈ cubeOfOrder L (meshAt L k 0) (j + 1) y := fun p hp =>
        hp.elim (fun h => cubeOfOrder_subset G.paths G.admissible G.one_le hjk e₁ h)
          fun h => cubeOfOrder_subset G.paths G.admissible G.one_le hjk e₂ h
      exact complexIter_congr hS G.one_le G.means G.support hA hA' hjk e fun w hw =>
        h₂ ⟨sub' _ hw.2.1, sub' _ hw.2.2⟩
    rw [hm]
end Induction
theorem iterLocalityHolds_of (hZ : BlockPathContourPivotStatement)
    (hP : LevelwiseMeans.LevelwiseMeansHold)
    (hR : SupportOfMeans.SupportOfMeansHolds)
    (hK : StepKernels.StepKernelBounds)
    (hH : StepKernelHolomorphy.KernelsHolomorphic) : IterLocalityHolds := by
  intro L hL k hk ρ _ hS
  have G : Setup L k := ⟨hZ, hL, hk, (hP L hL k hk).2, (hR L hL k hk).2, hK, hH⟩
  refine ⟨fun c A hA A' hA' B hB B' hB' h₁ h₂ => ?_,
    fun y A hA A' hA' f f' _ _ h₁ h₂ =>
      iterAdjointCubeAverage_congr G hS k le_rfl y A A' f f' hA hA' h₁ h₂⟩
  simp only [Pi.smul_apply]
  rw [iterCovariantDeriv_congr G hS k le_rfl c A A' B B' hA hA' hB hB' (fun e he => h₁ he)
    fun e he => h₂ he]
end YangMills.Construction.Tower.FullSpace.IterLocality
end
