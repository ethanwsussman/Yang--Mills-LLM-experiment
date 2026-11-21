import YangMills.Construction.ColdChainAtEveryLevel.LogarithmNearOne
import YangMills.Construction.ColdStepAtMirrorFrames.MovingTheChartCoordinates
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTopsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open NormedSpace
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames.ChartShift
theorem norm_exp_of_re_eq_zero {q : ℍ[ℝ]} (hq : q.re = 0) : ‖exp q‖ = 1 := by apply _root_.YangMills.Construction.QuaternionLog.norm_exp_of_re_eq_zero <;> assumption
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_exp_add_sub_exp_le {a h : ℍ[ℝ]} (ha : a.re = 0) (hh : h.re = 0) :
    ‖exp (a + h) - exp a‖ ≤ ‖h‖ := by
  set f : ℝ → ℍ[ℝ] := fun s => exp (s • (a + h)) * exp ((1 - s) • a) with hf
  have hd : ∀ s : ℝ, HasDerivAt f (exp (s • (a + h)) * h * exp ((1 - s) • a)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp (s • (a + h))) (exp (s • (a + h)) * (a + h)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (a + h) s
    have h2 : HasDerivAt (fun u : ℝ => exp (u • a)) (a * exp ((1 - s) • a)) (1 - s) :=
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) a (1 - s)
    have h3 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have h4 : HasDerivAt (fun s : ℝ => exp ((1 - s) • a)) ((-1 : ℝ) • (a * exp ((1 - s) • a))) s :=
      h2.scomp s h3
    have h5 := h1.mul h4
    have h6 : HasDerivAt f _ s := h5
    refine h6.congr_deriv ?_
    rw [neg_smul, one_smul]
    noncomm_ring
  have hb : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖exp (s • (a + h)) * h * exp ((1 - s) • a)‖ ≤ ‖h‖ := by
    intro s _
    have e1 : ‖exp (s • (a + h))‖ = 1 := norm_exp_of_re_eq_zero (by simp [ha, hh])
    have e2 : ‖exp ((1 - s) • a)‖ = 1 := norm_exp_of_re_eq_zero (by simp [ha])
    rw [norm_mul, norm_mul, e1, e2]
    simp
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun s => exp (s • (a + h)) * h * exp ((1 - s) • a))
    (fun s _ => (hd s).hasDerivWithinAt) hb
  simpa [hf] using this
variable {F : BlockFrame} {lev : ℕ}
theorem norm_pathHolonomy_sub_le {W W' : F.GaugeField lev} {ε : ℝ}
    (hW : ∀ x i, ‖((W x i : UnitQuaternion) : ℍ[ℝ]) - ((W' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ ε)
    (l : List PathStep) (x : F.Site lev) :
    ‖((pathHolonomy W x l : UnitQuaternion) : ℍ[ℝ]) - ((pathHolonomy W' x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
      l.length * ε := by apply _root_.YangMills.Construction.DerivativeInterpolation.HolonomyPerturbation.norm_sub_pathHolonomy_le <;> assumption
theorem norm_stepCoordinates_le (η : StepVariable (finiteCells F)) {r : ℝ} (hη : ∀ b, ‖η b‖ ≤ r)
    (hr : 0 ≤ r) (x : F.Site F.depth) (i : Fin 4) : ‖stepCoordinates η x i‖ ≤ r := by
  classical
  unfold stepCoordinates
  split_ifs with h
  · have h1 : ‖(toImaginary (η ⟨(x, i), h⟩) : imaginaryQuaternions)‖ ^ 2 = ‖η ⟨(x, i), h⟩‖ ^ 2 := by
      set v := η ⟨(x, i), h⟩ with hv
      have h2 := Quaternion.normSq_eq_norm_mul_self ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])
      rw [Quaternion.normSq_def'] at h2
      have h3 : ‖(toImaginary v : imaginaryQuaternions)‖ =
          ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ := rfl
      rw [h3, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, pow_two]
      simp only [toImaginary, Real.norm_eq_abs, sq_abs] at h2 ⊢
      linarith
    have h2 := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
    rw [h2]
    exact hη _
  · simpa using hr
theorem norm_chartedField_sub_le (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)) {r : ℝ} (hη : ∀ b, ‖η b‖ ≤ r) (hr : 0 ≤ r) (x : F.Site F.depth)
    (i : Fin 4) :
    ‖((chartedField (fun x i => w x i + stepCoordinates η x i) V x i : UnitQuaternion) : ℍ[ℝ]) -
      ((chartedField w V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ r := by
  have hz := norm_stepCoordinates_le η hη hr x i
  have hre : ((w x i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (w x i).2
  have hre' : ((stepCoordinates η x i : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (stepCoordinates η x i).2
  have hexp : ‖((expUnit (w x i + stepCoordinates η x i) : UnitQuaternion) : ℍ[ℝ]) -
      ((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ])‖ ≤ r :=
    (norm_exp_add_sub_exp_le hre hre').trans hz
  unfold chartedField
  by_cases hc : IsCrossingBond (x, i)
  · simp only [hc, if_true, MulMemClass.coe_mul]
    rw [← sub_mul, norm_mul, norm_unitQuaternion, mul_one]
    exact hexp
  · by_cases ht : IsAxialTreeBond (x, i)
    · simp only [hc, ht, if_true, if_false, sub_self, norm_zero]
      exact hr
    · simp only [hc, ht, if_false]
      exact hexp
theorem length_bondContour_le (L : ℕ) (hL : Odd L) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4)
    (hh : h ∈ centredCube L) : ((bondContour L h π i).length : ℝ) ≤ 5 * (L : ℝ) := by
  have hleg : ∀ k : Fin 4, (h (π k)).natAbs * 2 + 1 ≤ L := by
    intro k
    have h1 := Fintype.mem_piFinset.1 hh (π k)
    rw [Finset.mem_Icc] at h1
    obtain ⟨m, hm⟩ := hL
    have h2 : (((L : ℤ) - 1) / 2) = m := by
      subst hm
      push_cast
      omega
    rw [h2] at h1
    omega
  have hfin : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hlen : (axisPath h π).length = (h (π 0)).natAbs + ((h (π 1)).natAbs +
      ((h (π 2)).natAbs + (h (π 3)).natAbs)) := by
    unfold axisPath
    rw [hfin]
    simp [List.flatMap_cons]
  have h0 := hleg 0
  have h1 := hleg 1
  have h2 := hleg 2
  have h3 := hleg 3
  have : (bondContour L h π i).length ≤ 5 * L := by
    simp only [bondContour, reversePath, List.length_append, List.length_replicate,
      List.length_map, List.length_reverse, hlen]
    omega
  exact_mod_cast this
theorem chartShiftLipschitz_holds : ChartShiftLipschitz := by
  intro F V w η r hL hη hr
  have hmove := norm_chartedField_sub_le V w η hη hr
  refine ⟨norm_stepCoordinates_le η hη hr, fun p => ?_, fun c h π hh => ?_⟩
  · have h1 := norm_pathHolonomy_sub_le hmove
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1
    simp only [List.length_cons, List.length_nil] at h1
    unfold plaquetteDefect plaquetteHolonomy
    set A := ((pathHolonomy (chartedField (fun x i => w x i + stepCoordinates η x i) V) p.1
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])
    set B := ((pathHolonomy (chartedField w V) p.1
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])
    calc ‖A - 1‖ = ‖(A - B) + (B - 1)‖ := by congr 1; abel
      _ ≤ ‖A - B‖ + ‖B - 1‖ := norm_add_le _ _
      _ ≤ ‖B - 1‖ + 4 * r := by
          have : ‖A - B‖ ≤ 4 * r := by
            refine h1.trans (le_of_eq ?_)
            norm_num
          linarith
  · have h1 := norm_pathHolonomy_sub_le hmove (bondContour F.blockSide h π c.2) (refineSite c.1)
    have h2 : ((bondContour F.blockSide h π c.2).length : ℝ) * r ≤ 5 * (F.blockSide : ℝ) * r :=
      mul_le_mul_of_nonneg_right (length_bondContour_le F.blockSide hL h π c.2 hh) hr
    unfold contourHolonomyDefect
    set A := ((pathHolonomy (chartedField (fun x i => w x i + stepCoordinates η x i) V) (refineSite c.1)
      (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hA
    set B := ((pathHolonomy (chartedField w V) (refineSite c.1)
      (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) with hB
    set G := (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hG
    have e1 : ((pathHolonomy (chartedField (fun x i => w x i + stepCoordinates η x i) V) (refineSite c.1)
        (bondContour F.blockSide h π c.2) * (V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = A * G := rfl
    have e2 : ((pathHolonomy (chartedField w V) (refineSite c.1) (bondContour F.blockSide h π c.2) *
        (V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = B * G := rfl
    rw [e1, e2]
    have hn : ‖G‖ = 1 := norm_unitQuaternion _
    calc ‖A * G - 1‖ = ‖(A - B) * G + (B * G - 1)‖ := by congr 1; noncomm_ring
      _ ≤ ‖(A - B) * G‖ + ‖B * G - 1‖ := norm_add_le _ _
      _ = ‖A - B‖ + ‖B * G - 1‖ := by rw [norm_mul, hn, mul_one]
      _ ≤ ‖B * G - 1‖ + 5 * (F.blockSide : ℝ) * r := by linarith
end ColdStepAtMirrorFrames.ChartShift
end YangMills.Construction
end
