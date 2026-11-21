import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.OneLoopLaw.CoefficientFromALimitKernel
import YangMills.Construction.OneLoopLaw.FunctionalsAsTotalFunctionals
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.KernelStiffness
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.OneLoopLaw.FunctionalStiffness
open YangMills.Construction.EffectiveAction
variable {L : ℕ}
theorem bondRescale_opposite (hL : 0 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ)
    (e : PeriodicLattice.BondAtLevel L m K j) :
    bondRescale hL hj m e.opposite = (bondRescale hL hj m e).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
theorem opposite_opposite {m : ℕ} {i : ℤ} (e : PeriodicLattice.Bond L m i) :
    e.opposite.opposite = e := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem opposite_projectBond_not_positive (hL : 1 < L) {n : ℕ} (hn : 0 < n) (q : IntBond) :
    ¬ (projectBond L n 0 0 q).opposite.IsPositivelyOriented :=
  PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL
    (by simp [PeriodicLattice.levelDepth]; omega) (positiveImage L n q).2
theorem rescaledForm_singleBondForm (hL : 0 < L) (hL' : 1 < L) {K j : ℕ} (hj : j ≤ K) (m : ℕ)
    (hn : 0 < m + (K - j)) (a : Fin 3) (x : IntBond) :
    TorusFamilies.rescaledForm hL hj m
        (EffectiveAction.singleBondForm (projectBond L m K j x) (pauliLieBasis a).toMatrix) =
      liftedPauliForm L (m + (K - j)) a x := by
  have hY := bondRescale_projectBond hL hj m x
  have hopp := opposite_projectBond_not_positive hL' hn x
  have hpos : (projectBond L (m + (K - j)) 0 0 x).IsPositivelyOriented :=
    (positiveImage L (m + (K - j)) x).2
  funext e
  have h₁ : (bondRescale hL hj m).symm e = projectBond L m K j x ↔
      e = projectBond L (m + (K - j)) 0 0 x := by
    rw [Equiv.symm_apply_eq, hY]
  have h₂ : (bondRescale hL hj m).symm e = (projectBond L m K j x).opposite ↔
      e = (projectBond L (m + (K - j)) 0 0 x).opposite := by
    rw [Equiv.symm_apply_eq, bondRescale_opposite, hY]
  simp only [TorusFamilies.rescaledForm, Function.comp_apply,
    EffectiveAction.singleBondForm, liftedPauliForm, FunctionalStiffness.pauliEdgeForm,
    Tower.extendOddly, positiveImage, pauliLieBasis_toMatrix]
  by_cases he : e = projectBond L (m + (K - j)) 0 0 x
  · refine (if_pos (h₁.2 he)).trans ?_
    subst he
    simp [hpos]
  · by_cases he' : e = (projectBond L (m + (K - j)) 0 0 x).opposite
    · refine (if_neg (mt h₁.1 he)).trans ((if_pos (h₂.2 he')).trans ?_)
      subst he'
      simp [hopp, opposite_opposite]
    · refine (if_neg (mt h₁.1 he)).trans ((if_neg (mt h₂.1 he')).trans ?_)
      have he'' : e.opposite ≠ projectBond L (m + (K - j)) 0 0 x := fun h => he' (by
        rw [← h, opposite_opposite])
      by_cases hp : e.IsPositivelyOriented <;> simp [he, he'', hp]
theorem singleBondForm_isBondForm {m : ℕ} {i : ℤ} (X : PeriodicLattice.Bond L m i)
    {A : Matrices.ComplexMatrix2} (hA : A ∈ PeriodicLattice.compactLieAlgebra)
    (hX : X.opposite ≠ X) :
    PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (EffectiveAction.singleBondForm X A) := by
  refine ⟨fun e _ => ?_, fun e => ?_⟩
  · simp only [EffectiveAction.singleBondForm]
    split_ifs
    · exact hA
    · exact neg_mem hA
    · exact zero_mem _
  · simp only [EffectiveAction.singleBondForm]
    by_cases h₁ : e = X
    · subst h₁
      simp [hX]
    · by_cases h₂ : e = X.opposite
      · subst h₂
        simp [opposite_opposite, hX]
      · have h₃ : e.opposite ≠ X := fun h => h₂ (by rw [← h, opposite_opposite])
        have h₄ : e.opposite ≠ X.opposite := fun h => h₁ (by
          rw [← opposite_opposite e, h, opposite_opposite])
        simp [h₁, h₂, h₃, h₄]
theorem singleBondForm_pauli_isBondForm (hL : 0 < L) (hL' : 1 < L) {K j : ℕ} (hj : j ≤ K)
    (m : ℕ) (hn : 0 < m + (K - j)) (a : Fin 3) (x : IntBond) :
    PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (EffectiveAction.singleBondForm (projectBond L m K j x) (pauliLieBasis a).toMatrix) := by
  refine singleBondForm_isBondForm _
    (Subtype.property (p := (· ∈ Matrices.ComplexMatrix2.hermitianTraceless)) (pauliLieBasis a))
    fun h => ?_
  have h₁ := congrArg (bondRescale hL hj m) h
  rw [bondRescale_opposite, bondRescale_projectBond] at h₁
  exact opposite_projectBond_not_positive hL' hn x (h₁ ▸ (positiveImage L (m + (K - j)) x).2)
theorem hasKernelLimit_torusFamily (H : TorusFamilies.TorusFamilyProperties)
    (hadm : Conventions.IsAdmissibleBlockingFactor L) (hL : 0 < L) {F : FieldFamily L}
    (hF : IsLatticeFunctional L F) {P : Fin 4 → Fin 4 → IntPoint → ℝ}
    (hlim : ∀ (x y : IntBond) (a a' : Fin 3),
      Tendsto (fun n => complexHessian F n (liftedPauliForm L n a x) (liftedPauliForm L n a' y))
        atTop (𝓝 (if a = a' then ((P x.2 y.2 (y.1 - x.1) : ℝ) : ℂ) else 0)))
    {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    HasKernelLimit pauliLieBasis (torusFamily hL hj F) P := by
  have hL' : 1 < L := by have := hadm.2; omega
  have hP := ((H L hadm hL F hF).1 K j hK hj).2.2
  intro x y a a'
  have hc : Tendsto (fun m => ((torusPolarization (torusFamily hL hj F) m
      (EffectiveAction.singleBondForm (projectBond L m K j x) (pauliLieBasis a).toMatrix)
      (EffectiveAction.singleBondForm (projectBond L m K j y) (pauliLieBasis a').toMatrix)
        : ℝ) : ℂ)) atTop
      (𝓝 (if a = a' then ((P x.2 y.2 (y.1 - x.1) : ℝ) : ℂ) else 0)) := by
    refine ((hlim x y a a').comp (tendsto_add_atTop_nat (K - j))).congr' ?_
    filter_upwards [hP, eventually_gt_atTop 0] with m hm hm0
    have hn : 0 < m + (K - j) := by omega
    rw [hm _ _ (singleBondForm_pauli_isBondForm hL hL' hj m hn a x)
        (singleBondForm_pauli_isBondForm hL hL' hj m hn a' y),
      rescaledForm_singleBondForm hL hL' hj m hn, rescaledForm_singleBondForm hL hL' hj m hn]
    rfl
  have hr := (Complex.continuous_re.tendsto _).comp hc
  have hval : Complex.re (if a = a' then ((P x.2 y.2 (y.1 - x.1) : ℝ) : ℂ) else 0) =
      if a = a' then P x.2 y.2 (y.1 - x.1) else 0 := by
    split_ifs <;> simp
  rw [hval] at hr
  refine hr.congr fun m => ?_
  simp
theorem hasKernelLimit_unique {K j : ℕ} {t : Fin 3 → Matrices.ComplexMatrix2.LieElement}
    {Φ : TorusFunctional L K j} {P P' : Fin 4 → Fin 4 → IntPoint → ℝ}
    (h : HasKernelLimit t Φ P) (h' : HasKernelLimit t Φ P') (μ ν : Fin 4) (u : IntPoint) :
    P' μ ν u = P μ ν u := by
  have h₁ := h (0, μ) (u, ν) 0 0
  have h₂ := h' (0, μ) (u, ν) 0 0
  simpa using tendsto_nhds_unique h₂ h₁
theorem stiffnessFromKernelLimit_of_torusFamilyProperties
    (h : TorusFamilies.TorusFamilyProperties) : StiffnessFromKernelLimit := by
  intro L hL hadm F hF P c hlim hsum
  have hker : ∀ K j : ℕ, 0 < K → ∀ hj : j ≤ K,
      HasKernelLimit pauliLieBasis (torusFamily hL hj F) P :=
    fun K j hK hj => hasKernelLimit_torusFamily h hadm hL hF hlim hK hj
  have hex : HasStiffnessConstant hL F c := by
    refine ⟨hF, fun K j hK hj => ((h L hadm hL F hF).1 K j hK hj).2.1, fun K j hK hj =>
      ⟨P, hker K j hK hj, fun μ ν hne => ⟨(hsum μ ν hne).summable, (hsum μ ν hne).tsum_eq⟩⟩⟩
  refine ⟨hex, ?_⟩
  have hspec : HasStiffnessConstant hL F (stiffnessConstant hL F) :=
    Classical.epsilon_spec ⟨c, hex⟩
  obtain ⟨P', hP', hs'⟩ := hspec.stiffness 1 0 one_pos (Nat.zero_le 1)
  have hne : (0 : Fin 4) ≠ 1 := by decide
  rw [← (hs' 0 1 hne).2, ← (hsum 0 1 hne).tsum_eq]
  refine tsum_congr fun u => ?_
  rw [hasKernelLimit_unique (hker 1 0 one_pos (Nat.zero_le 1)) hP']
end YangMills.Construction.OneLoopLaw.KernelStiffness
end
