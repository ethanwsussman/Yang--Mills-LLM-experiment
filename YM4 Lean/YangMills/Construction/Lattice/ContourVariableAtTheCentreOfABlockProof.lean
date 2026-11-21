import YangMills.Construction.Averaging.MeanInTheComplexGroup
import YangMills.Construction.Lattice.ContourVariableAtTheCentreOfABlock
import YangMills.Construction.Weighted.LayerCutoffConstruction
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockCentreContour
variable {L m : ℕ} {j j' : ℤ}
theorem torusSupNorm_zero_nonpos {S : ℝ} :
    TorusMetric.torusSupNorm (0 : TorusMetric.Torus4 S) ≤ 0 := by apply _root_.YangMills.Construction.Weighted.LayerCutoff.torusSupNorm_zero_nonpos <;> assumption
theorem int_eq_zero_of_scaled_coe_eq_zero (hL : 0 < L) (hj : 1 ≤ j') (a : ℤ)
    (ha : 2 * |a| ≤ (L : ℤ) - 1)
    (h : (((a : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) = 0) : a = 0 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hsp0 : 0 < meshSize L j' := zpow_pos hL0 _
  have hsp : meshSize L j' ≤ (L : ℝ)⁻¹ := by
    have := zpow_le_zpow_right₀ hLr (show -j' ≤ -1 by omega)
    simpa [meshSize, zpow_neg_one] using this
  have hside : 2 ≤ torusSide L m := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ m := one_le_pow₀ hLr
    unfold torusSide
    linarith
  have : Fact (0 < torusSide L m) := ⟨by linarith⟩
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).1 h
  have habs : |(a : ℝ)| ≤ L := by
    have h1 : |a| ≤ (L : ℤ) := by omega
    have h2 : ((|a| : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by exact_mod_cast h1
    simpa using h2
  have hprod : |(a : ℝ) * meshSize L j'| ≤ 1 := by
    rw [abs_mul, abs_of_pos hsp0]
    calc |(a : ℝ)| * meshSize L j' ≤ L * (L : ℝ)⁻¹ :=
          mul_le_mul habs hsp hsp0.le hL0.le
      _ = 1 := mul_inv_cancel₀ hL0.ne'
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hne
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h2
    rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos (by linarith : 0 < torusSide L m)] at hprod
    nlinarith
  subst hk0
  have hz : (a : ℝ) * meshSize L j' = 0 := by simpa using hk.symm
  have : (a : ℝ) = 0 := (mul_eq_zero.1 hz).resolve_right hsp0.ne'
  exact_mod_cast this
theorem offsetAxes_self_eq_empty (hL : Odd L) (hj : 1 ≤ j') (y : Site L m j)
    (x : Site L m j') (hx : (x : FourTorus L m) = y) : offsetAxes y x = ∅ := by
  have hL0 : 0 < L := hL.pos
  have hspec : IsBlockOffset y x (blockOffset y x) := by
    refine Classical.epsilon_spec (p := IsBlockOffset y x) ⟨0, ?_, fun μ => ?_⟩
    · simp [hx, pointOnAxis]
    · simp only [Pi.zero_apply, abs_zero, mul_zero]
      omega
  obtain ⟨hsum, hbound⟩ := hspec
  rw [hx, sub_self] at hsum
  unfold offsetAxes
  refine Finset.filter_false_of_mem fun ν _ => ?_
  rw [not_not]
  refine int_eq_zero_of_scaled_coe_eq_zero (m := m) hL0 hj _ (hbound ν) ?_
  have := congrFun hsum ν
  simpa [pointOnAxis, Finset.sum_apply, Pi.single_apply] using this.symm
theorem orderedContour_eq_nil (y : Site L m j) (x : Site L m j')
    (hc : (offsetAxes y x).card = 0) (σ : AxisOrdering y x) :
    orderedContour y x σ = [] := by
  unfold orderedContour
  have h : ((List.finRange (offsetAxes y x).card).map
      fun i => ((σ i : offsetAxes y x) : Fin 4)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [hc]
  rw [h]
  rfl
theorem axisOrdering_nonempty (y : Site L m j) (x : Site L m j') :
    Nonempty (AxisOrdering y x) :=
  ⟨(offsetAxes y x).equivFin.symm⟩
theorem axisOrdering_subsingleton (y : Site L m j) (x : Site L m j')
    (hc : (offsetAxes y x).card = 0) : Subsingleton (AxisOrdering y x) :=
  ⟨fun _ _ => Equiv.ext fun i => by
    have := i.2
    omega⟩
theorem familyDiameter_const_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : ι → Matrices.ComplexMatrix2) (hV : ∀ i, V i = 1) :
    Matrices.ComplexMatrix2.familyDiameter V = 0 := by
  unfold Matrices.ComplexMatrix2.familyDiameter
  simp [hV, Matrices.ComplexMatrix2.operatorNorm]
theorem complexLogMean_const_one {ι : Type*} [Fintype ι] [Nonempty ι] [Subsingleton ι]
    (hM : Averaging.ComplexLogMeanProperties 1) (V : ι → Matrices.ComplexMatrix2)
    (hV : ∀ i, V i = 1) :
    complexLogMean V = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hone : (1 : Matrices.ComplexMatrix2) ∈ complexGaugeGroup := by
    simp [complexGaugeGroup, Matrices.ComplexMatrix2.unitDeterminant]
  have hP : (fun W : Matrices.ComplexMatrix2 =>
        Matrices.ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
        ∃ i, Matrices.ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance) =
      fun W : Matrices.ComplexMatrix2 =>
        Matrices.ComplexMatrix2.IsLogMean complexGaugeGroup
          (fun _ : Fin 1 => (1 : Matrices.ComplexMatrix2)) W ∧
        ∃ i, Matrices.ComplexMatrix2.operatorNorm
          ((fun _ : Fin 1 => (1 : Matrices.ComplexMatrix2)) i * W⁻¹ - 1) ≤
            complexMeanTolerance := by
    funext W
    simp only [Matrices.ComplexMatrix2.IsLogMean, Fintype.sum_subsingleton _ i₀, hV]
    simp
  have h := hM.constantFamily 1 hone
  unfold complexLogMean at h ⊢
  rw [hP]
  exact h
theorem contourHolonomyAtBlockCentre_proof (hmean : Averaging.ComplexLogMeanOfSmallFamilies) :
    PeriodicLattice.ContourHolonomyAtBlockCentre := by
  intro L m K n hL _ hn y W _
  have hL0 : 0 < L := hL.1.pos
  have hle : levelDepth K (n + 1) ≤ levelDepth K n := by
    simp only [levelDepth]
    push_cast
    omega
  have hj : 1 ≤ levelDepth K n := by
    simp only [levelDepth]
    omega
  have hx : ((y.toSublattice (levelDepth K n) : Site L m (levelDepth K n)) : FourTorus L m) = y :=
    Classical.epsilon_spec (p := fun x : Site L m (levelDepth K n) => (x : FourTorus L m) = y)
      ⟨⟨y, sublattice_mono hL0 m hle y.2⟩, rfl⟩
  have hc : (offsetAxes y (y.toSublattice (levelDepth K n))).card = 0 := by
    rw [offsetAxes_self_eq_empty hL.1 hj y _ hx, Finset.card_empty]
  have := axisOrdering_nonempty y (y.toSublattice (levelDepth K n))
  have := axisOrdering_subsingleton y (y.toSublattice (levelDepth K n)) hc
  have hV : ∀ σ, contourHolonomies W y (y.toSublattice (levelDepth K n)) σ = 1 := fun σ => by
    simp [contourHolonomies, orderedContour_eq_nil _ _ hc σ, pathHolonomy]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show TorusMetric.torusSupNorm _ ≤ meshSize L _ / 2
    rw [hx, sub_self]
    have : 0 < meshSize L (levelDepth K (n + 1)) := zpow_pos (by exact_mod_cast hL0) _
    linarith [torusSupNorm_zero_nonpos (S := torusSide L m)]
  · refine sublattice_mono hL0 m ?_ (y.toSublattice (levelDepth K n)).2
    simp only [levelDepth]
    push_cast
    omega
  · rw [familyDiameter_const_one _ hV]
    norm_num [Averaging.centreOfMassDiameter]
  · exact complexLogMean_const_one (hmean.2.2.2.1 1 le_rfl) _ hV
end YangMills.Construction.PeriodicLattice.BlockCentreContour
end
