import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Towers.CovariantDifferenceUnderTheChainConstraint
import YangMills.Construction.Towers.HessianOnTheFibreAndGaugeDirections
import YangMills.Construction.Towers.InjectiveCovariantDifferenceAtTheBaseOfAChain
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Tower Matrices
namespace Tower.ChainBottom
variable {L n k : ℕ}
theorem contourLogDeriv_zero (i : ℕ) (V : Edge L n k i → ComplexMatrix2) :
    contourLogDeriv L n k i V 0 = 0 := by
  funext x
  simp only [contourLogDeriv, smul_zero, Pi.zero_apply]
  rw [deriv_const]
  simp
theorem contourFamily_zero (W : Edge L n k k → ComplexMatrix2) :
    contourFamily W (0 : edgeFormSpace L n k 0) = 0 := by
  funext i
  simp [contourFamily, contourLogDeriv_zero]
theorem coe_toSublattice (hL : 0 < L) {i : ℕ} (y : Vertex L n k i) :
    ((y.toSublattice (PeriodicLattice.levelDepth k 0) : Vertex L n k 0) :
      PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.PeriodicLattice.coe_toSublattice_finest <;> assumption
theorem restrictVertexFunction_apply (hL : 0 < L) (l : Vertex L n k 0 → ComplexMatrix2) (i : ℕ)
    (z : Vertex L n k 0)
    (hz : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)) :
    restrictVertexFunction i l ⟨z.1, hz⟩ = l z := by
  have hs : PeriodicLattice.Site.toSublattice (⟨z.1, hz⟩ : Vertex L n k i)
      (PeriodicLattice.levelDepth k 0) = z :=
    Subtype.ext (coe_toSublattice hL _)
  simp [restrictVertexFunction, PeriodicLattice.restrictGaugeMap, hs]
theorem exists_level_between (z : Vertex L n k 0)
    (hz : (z : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)) :
    ∃ i : Fin k, (z : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) ∧
      (z : PeriodicLattice.FourTorus L n) ∉
        PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k ((i : ℕ) + 1)) := by
  classical
  have he : ∃ m : ℕ, (z : PeriodicLattice.FourTorus L n) ∉
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k m) := ⟨k, hz⟩
  have hmk : Nat.find he ≤ k := Nat.find_min' he hz
  have hm0 : Nat.find he ≠ 0 := fun h => by
    have := Nat.find_spec he
    rw [h] at this
    exact this z.2
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) := by
    by_contra hc
    have := Nat.find_min' he hc
    omega
  refine ⟨⟨i, by omega⟩, hmin, ?_⟩
  have := Nat.find_spec he
  rw [hi] at this
  exact this
theorem eq_zero_of_fineOnlyComponents_eq_zero (hL : 0 < L)
    (κ : vertexFunctionsVanishingAtTop L n k)
    (h : fineOnlyComponents (κ : Vertex L n k 0 → ComplexMatrix2) = 0) : κ = 0 := by
  refine Subtype.ext (funext fun z => ?_)
  by_cases ht : (z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k)
  · rw [← restrictVertexFunction_apply hL (κ : Vertex L n k 0 → ComplexMatrix2) k z ht, κ.2.2]
    rfl
  · obtain ⟨i, hi, hi'⟩ := exists_level_between z ht
    have e := congrFun (congrFun h i) ⟨⟨z.1, hi⟩, hi'⟩
    have e' : restrictVertexFunction (i : ℕ) (κ : Vertex L n k 0 → ComplexMatrix2) ⟨z.1, hi⟩ = 0 :=
      e
    rw [restrictVertexFunction_apply hL _ _ z hi] at e'
    exact e'
theorem finite_vertexFunctionsVanishingAtTop (hL : 0 < L) :
    Module.Finite ℝ (vertexFunctionsVanishingAtTop L n k) := by
  have : Finite (Vertex L n k 0) := SeparatedSequences.BaseParameters.site_finite hL _ _
  infer_instance
end Tower.ChainBottom
open Tower.ChainBottom in
theorem Tower.CovDiffInjectiveAtChainBottom.holds
    (hc : Tower.CovDiffUnderTopConstraint)
    (hh : Tower.FibreHessianAndGaugeDirections) :
    Tower.CovDiffInjectiveAtChainBottom := by
  intro L n k hL hn hk
  have hL0 : 0 < L := by have := hL.2; omega
  refine Filter.Eventually.mono
    (Filter.Eventually.and (hc L n k hL hn hk) (hh L n k hL hn hk).2) ?_
  rintro W ⟨hcW, -, D, hD, -, -, T, hT, hdet⟩ hW l hl hl0
  have e := hcW ⟨l, hl⟩ 0 (by simpa using hl0.symm)
  have hr : restrictVertexFunction k l = 0 := by
    refine hW _ (fun y _ => hl _ (Set.mem_univ _)) ?_
    rw [← e]
    simp
  have hDκ : D ⟨l, hl, hr⟩ = 0 := Subtype.ext ((hD _).trans hl0)
  have hTκ : T ⟨l, hl, hr⟩ = 0 := by
    refine eq_zero_of_fineOnlyComponents_eq_zero hL0 _ ?_
    rw [hT, hDκ]
    exact contourFamily_zero W
  have hfin := finite_vertexFunctionsVanishingAtTop (L := L) (n := n) (k := k) hL0
  have hne : LinearMap.det T ≠ 0 := fun h => by simp [h] at hdet
  have hb : LinearMap.ker T = ⊥ := by
    by_contra hk'
    exact hne (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hk')
  have hm : (⟨l, hl, hr⟩ : vertexFunctionsVanishingAtTop L n k) ∈ LinearMap.ker T := hTκ
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm
end YangMills.Construction
end
