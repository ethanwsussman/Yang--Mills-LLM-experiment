import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Cumulants.CumulantLessTheMixedDerivativeOfACounterterm
import YangMills.Construction.Cumulants.GeneratingFunctionIsEntireWithItsPrincipalLogarithm
import YangMills.Construction.Functions.LogarithmOfABoundedHolomorphicFunction
import YangMills.Construction.Lattice.SublevelSetsAndSourceDiscs
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Cumulants.CountertermBound
theorem eq_zero_of_exp_eq_one_of_norm_lt_one {w : ℂ} (hw : Complex.exp w = 1) (hlt : ‖w‖ < 1) :
    w = 0 := by
  obtain ⟨m, rfl⟩ := Complex.exp_eq_one_iff.mp hw
  by_cases hm : m = 0
  · simp [hm]
  · exfalso
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hnm : ‖(m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ = |(m : ℝ)| * (2 * Real.pi) := by
      simp [abs_of_pos Real.pi_pos]
    rw [hnm] at hlt
    nlinarith [Real.pi_gt_three]
theorem continuousAt_of_isHolomorphicScalar {n : ℕ} {U : Set (Coordinates.ComplexCoordinates n)}
    {f : Coordinates.ComplexCoordinates n → ℂ} (hf : ComplexVariables.IsHolomorphicScalar U f)
    {w : Coordinates.ComplexCoordinates n} (hw : w ∈ U) : ContinuousAt f w := by
  obtain ⟨hU, hcont, -⟩ := hf
  have hcomp : ContinuousAt ((Equiv.funUnique (Fin 1) ℂ).symm ∘ f) w :=
    hcont.continuousAt (hU.mem_nhds hw)
  exact ((continuous_apply (0 : Fin 1)).continuousAt).comp hcomp
theorem cumulantNearCountertermDeriv_proof
    (hRules : SeveralComplexVariables.HolomorphicCalculusRules)
    (hGen : GeneratingLog.EntireAndLogCumulant)
    (hSub : SublevelSets.SublevelAndDiskStatement)
    (hLogB : LogBounds.BoundedLogEstimate) :
    CumulantNearCountertermDeriv := by
  intro n a Ω _ ν _ X ℰ Q hX hE hE0 hQ
  have hn : 1 ≤ n := a.one_le
  obtain ⟨hG, -⟩ := hGen Ω ν n X hn hX
  have hU : IsOpen a.unitSet := (hSub.1 n a 1 one_pos).1
  have hMU : ComplexVariables.IsHolomorphicScalar a.unitSet (momentGeneratingFunction ν X) :=
    (hRules n hn univ isOpen_univ _ _ hG.entire hG.entire).2.1 a.unitSet hU (subset_univ _)
  have hneg : ComplexVariables.IsHolomorphicScalar a.unitSet (fun z => -ℰ z) := by
    have hrw : (fun z => -ℰ z) = fun z => ℰ z + (-2 : ℂ) * ℰ z := by
      funext z
      ring
    rw [hrw]
    exact (hRules n hn a.unitSet hU ℰ ℰ hE hE).1.1 (-2)
  have hexpc : ComplexVariables.IsHolomorphicScalar a.unitSet
      (ComplexVariables.expComp fun z => -ℰ z) :=
    (hRules n hn a.unitSet hU _ _ hneg hMU).1.2.2
  have hprod : ComplexVariables.IsHolomorphicScalar a.unitSet
      (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) :=
    (hRules n hn a.unitSet hU _ _ hexpc hMU).1.2.1
  have hprod0 : (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) 0 = 1 := by
    simp [hE0, hG.value_at_zero]
  obtain ⟨hQ1, -, ⟨-, hLh, hLexp, hL0, -, -⟩, hbound⟩ := hLogB n a _ Q hprod hprod0 hQ
  have hinv : 0 < (Q + 1)⁻¹ := by
    apply inv_pos.mpr
    linarith
  have hSl : IsOpen (LogBounds.sublevelSet a Q) :=
    (hSub.1 n a _ hinv).1
  have hSl0 : (0 : Coordinates.ComplexCoordinates n) ∈ LogBounds.sublevelSet a Q :=
    (hSub.1 n a _ hinv).2.1
  set V : Set (Coordinates.ComplexCoordinates n) :=
    LogBounds.sublevelSet a Q ∩ GeneratingLog.nearOneSet ν X with hVdef
  have hV : IsOpen V := hSl.inter hG.isOpen
  have h0V : (0 : Coordinates.ComplexCoordinates n) ∈ V := ⟨hSl0, hG.zero_mem⟩
  have hVU : V ⊆ a.unitSet := by
    intro z hz
    have hlt : a.weightedNorm z < (Q + 1)⁻¹ := hz.1
    have hle : (Q + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    exact lt_of_lt_of_le hlt hle
  have hEV : ComplexVariables.IsHolomorphicScalar V ℰ :=
    (hRules n hn a.unitSet hU ℰ ℰ hE hE).2.1 V hV hVU
  have hLV := (hRules n hn _ hSl _ _ hLh hLh).2.1 V hV inter_subset_left
  have hKV := (hRules n hn _ hG.isOpen _ _ hG.holomorphic hG.holomorphic).2.1 V hV
    inter_subset_right
  obtain ⟨hadd, -, -, -, -, -, -, ⟨hlin, -⟩, -, -⟩ := hRules n hn V hV ℰ _ hEV hLV
  have hsumh := hadd.1 1
  obtain ⟨-, -, -, -, -, -, -, ⟨-, hlocal⟩, -, -⟩ := hRules n hn V hV _ _ hKV hsumh
  have hexpeq : ∀ z ∈ V,
      Complex.exp (GeneratingLog.logOfGenerating ν X z -
        (ℰ z + 1 * LogBounds.logOf
          (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) z)) = 1 := by
    intro z hz
    have hMz := hG.exp_eq z hz.2
    have hnz : momentGeneratingFunction ν X z ≠ 0 := by
      intro hzero
      rw [hzero] at hMz
      exact Complex.exp_ne_zero _ hMz
    rw [Complex.exp_sub, hMz, one_mul, Complex.exp_add, hLexp z hz.1, ← mul_assoc,
      ← Complex.exp_add]
    simp [hnz]
  have hK0 := hG.log_at_zero
  have hclose : ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates n),
      ‖GeneratingLog.logOfGenerating ν X z -
        (ℰ z + 1 * LogBounds.logOf
          (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) z)‖ < 1 := by
    have hct := (continuousAt_of_isHolomorphicScalar hKV h0V).sub
      (continuousAt_of_isHolomorphicScalar hsumh h0V)
    have hdiff0 : GeneratingLog.logOfGenerating ν X 0 -
        (ℰ 0 + 1 * LogBounds.logOf
          (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) 0) = 0 := by
      rw [hK0, hE0, hL0]
      simp
    refine hct.norm.tendsto.eventually_lt_const ?_
    simp only [Pi.sub_apply]
    rw [hdiff0]
    simp
  set W : Set (Coordinates.ComplexCoordinates n) := interior {z | z ∈ V ∧
      ‖GeneratingLog.logOfGenerating ν X z -
        (ℰ z + 1 * LogBounds.logOf
          (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) z)‖ < 1} with hWdef
  have h0W : (0 : Coordinates.ComplexCoordinates n) ∈ W :=
    mem_interior_iff_mem_nhds.mpr
      ((show ∀ᶠ z in 𝓝 (0 : Coordinates.ComplexCoordinates n), z ∈ V from hV.mem_nhds h0V).and
        hclose)
  have hWV : W ⊆ V := fun z hz => (interior_subset hz).1
  have hagree : EqOn (GeneratingLog.logOfGenerating ν X)
      (fun z => ℰ z + 1 * LogBounds.logOf
          (fun z => Complex.exp (-ℰ z) * momentGeneratingFunction ν X z) z) W := by
    intro z hz
    have hz' := interior_subset hz
    exact sub_eq_zero.mp (eq_zero_of_exp_eq_one_of_norm_lt_one (hexpeq z hz'.1) hz'.2)
  have hstep2 := hlocal W isOpen_interior hWV hagree h0W
  have hstep3 := (hlin 1) h0V
  rw [hG.cumulant_eq, hstep2, hstep3]
  have hcancel : ∀ u v : ℂ, u + 1 * v - u = v := fun u v => by ring
  rw [hcancel]
  exact hbound
end YangMills.Construction.Cumulants.CountertermBound
end
