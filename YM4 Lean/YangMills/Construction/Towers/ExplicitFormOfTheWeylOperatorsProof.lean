import YangMills.Construction.Towers.ExplicitFormOfTheWeylOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
namespace Tower.MagneticWeylFormulas
open MagneticWeyl
variable {L : ℕ}
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by simp [meshAt]
theorem axisStep_coord (μ ν : Fin 4) :
    ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) : AmbientSpace) ν =
      if ν = μ then 1 else 0 := by
  change (Pi.single μ (meshAt L 0 0) : AmbientSpace) ν = _
  by_cases hνμ : ν = μ
  · subst hνμ; simp [meshAt_zero_zero]
  · simp [hνμ]
theorem axisStep_inj_iff (μ ν : Fin 4) :
    (InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) =
      InfiniteLattice.axisStep (meshAt L 0 0) ν ↔ μ = ν := by
  constructor
  · intro heq
    by_contra hne
    have hc := congrArg (fun s : FullSpace.Vertex L 0 0 => (s : AmbientSpace) μ) heq
    simp only [axisStep_coord] at hc
    simp [hne] at hc
  · rintro rfl; rfl
def phaseAngle (φ : ℝ) (μ : Fin 4) (x : FullSpace.Vertex L 0 0) : ℝ :=
  if μ = 1 then φ * (x : AmbientSpace) 0 else 0
theorem two_mul_halfFluxAngle (φ : ℝ) (μ : Fin 4) (x : FullSpace.Vertex L 0 0) :
    2 * halfFluxAngle L φ (FullSpace.forwardEdge x μ) = phaseAngle φ μ x := by
  have hd : (FullSpace.forwardEdge x μ).1.terminal - (FullSpace.forwardEdge x μ).1.initial =
      InfiniteLattice.axisStep (meshAt L 0 0) μ := by
    simp [FullSpace.forwardEdge, InfiniteLattice.Link.forwardFrom]
  unfold halfFluxAngle FullSpace.linearAbelianAngle phaseAngle
  simp only [hd, axisStep_inj_iff]
  by_cases hμ : μ = 1
  · simp only [hμ, if_true]
    have : ((FullSpace.forwardEdge x (1 : Fin 4)).1.initial : AmbientSpace) = (x : AmbientSpace) := rfl
    rw [this]; ring
  · simp [hμ]
theorem magneticTranslation_eq (φ : ℝ) (μ : Fin 4) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0) :
    magneticTranslation L φ μ w x = Complex.exp (Complex.I * (phaseAngle φ μ x : ℂ)) •
      w (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) := by
  have hw : magneticTranslation L φ μ w x =
      Complex.exp (2 * Complex.I * (halfFluxAngle L φ (FullSpace.forwardEdge x μ) : ℂ)) •
        w (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) := rfl
  rw [hw, ← two_mul_halfFluxAngle]
  congr 2
  push_cast
  ring
theorem zpow_phaseTranslation (U : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L)
    (τ : FullSpace.Vertex L 0 0) (f : FullSpace.Vertex L 0 0 → ℝ) (hf : ∀ x, f (x + τ) = f x)
    (hU : ∀ (w : ScalarL2 L) x, U w x = Complex.exp (Complex.I * (f x : ℂ)) • w (x + τ))
    (k : ℤ) : ∀ (w : ScalarL2 L) x,
      (U ^ k) w x = Complex.exp (Complex.I * ((k : ℂ) * (f x : ℂ))) • w (x + k • τ) := by
  refine Int.induction_on k ?_ ?_ ?_
  · intro w x
    simp
  · intro i ih w x
    rw [add_comm (i : ℤ) 1, zpow_one_add, LinearIsometryEquiv.coe_mul, Function.comp_apply, hU,
      ih, hf, smul_smul, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · rw [add_zsmul, one_zsmul, add_assoc]
  · intro i ih w x
    set v := (U ^ (-(i : ℤ) - 1)) w with hv
    have hUv : U v = (U ^ (-(i : ℤ))) w := by
      have hm : U * U ^ (-(i : ℤ) - 1) = U ^ (-(i : ℤ)) := by
        rw [← zpow_one_add]
        congr 1
        ring
      rw [hv, ← hm, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    have e1 := hU v (x - τ)
    rw [hUv, ih, sub_add_cancel] at e1
    have hfx : f (x - τ) = f x := by
      have := hf (x - τ)
      rwa [sub_add_cancel, eq_comm] at this
    rw [hfx] at e1
    have e2 : v x = Complex.exp (-(Complex.I * (f x : ℂ))) •
        Complex.exp (Complex.I * (((-(i : ℤ) : ℤ) : ℂ) * (f x : ℂ))) •
          w (x - τ + (-(i : ℤ)) • τ) := by
      rw [e1, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
    rw [e2, smul_smul, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · have hs : x - τ + (-(i : ℤ)) • τ = x + (-(i : ℤ) - 1) • τ := by
        rw [sub_zsmul, one_zsmul]
        abel
      rw [hs]
theorem phaseAngle_add_axisStep (φ : ℝ) (μ : Fin 4) (x : FullSpace.Vertex L 0 0) :
    phaseAngle φ μ (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) = phaseAngle φ μ x := by
  unfold phaseAngle
  by_cases hμ : μ = 1
  · subst hμ
    have : ((x + InfiniteLattice.axisStep (meshAt L 0 0) 1 : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
        (x : AmbientSpace) 0 + ((InfiniteLattice.axisStep (meshAt L 0 0) 1 : FullSpace.Vertex L 0 0) : AmbientSpace) 0 := rfl
    simp [this, axisStep_coord]
  · simp [hμ]
theorem magneticTranslation_zpow (φ : ℝ) (μ : Fin 4) (k : ℤ) (w : ScalarL2 L)
    (x : FullSpace.Vertex L 0 0) :
    (magneticTranslation L φ μ ^ k) w x = Complex.exp (Complex.I * ((k : ℂ) * (phaseAngle φ μ x : ℂ))) •
      w (x + k • InfiniteLattice.axisStep (meshAt L 0 0) μ) :=
  zpow_phaseTranslation _ _ _ (phaseAngle_add_axisStep φ μ) (magneticTranslation_eq φ μ) k w x
theorem coord_zero_add_axisStep (μ : Fin 4) (x : FullSpace.Vertex L 0 0) :
    ((x + InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
      (x : AmbientSpace) 0 + if μ = 0 then 1 else 0 := by
  have : ((x + InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
      (x : AmbientSpace) 0 + ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) : AmbientSpace) 0 := rfl
  rw [this, axisStep_coord]
  simp [eq_comm]
theorem add_zsmul_axisSteps (n : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    x + n 0 • InfiniteLattice.axisStep (meshAt L 0 0) 0 +
        n 1 • InfiniteLattice.axisStep (meshAt L 0 0) 1 +
        n 2 • InfiniteLattice.axisStep (meshAt L 0 0) 2 +
        n 3 • InfiniteLattice.axisStep (meshAt L 0 0) 3 = x + latticePoint L n := by
  refine Subtype.ext (funext fun μ => ?_)
  have hc : ∀ (k : ℤ) (ν : Fin 4), ((k • InfiniteLattice.axisStep (meshAt L 0 0) ν :
      FullSpace.Vertex L 0 0) : AmbientSpace) μ = (k : ℝ) * (if μ = ν then 1 else 0) := by
    intro k ν
    have : ((k • InfiniteLattice.axisStep (meshAt L 0 0) ν : FullSpace.Vertex L 0 0) : AmbientSpace) μ =
        k • ((InfiniteLattice.axisStep (meshAt L 0 0) ν : FullSpace.Vertex L 0 0) : AmbientSpace) μ := rfl
    rw [this, axisStep_coord, zsmul_eq_mul]
  have hl : ((x + n 0 • InfiniteLattice.axisStep (meshAt L 0 0) 0 +
        n 1 • InfiniteLattice.axisStep (meshAt L 0 0) 1 +
        n 2 • InfiniteLattice.axisStep (meshAt L 0 0) 2 +
        n 3 • InfiniteLattice.axisStep (meshAt L 0 0) 3 : FullSpace.Vertex L 0 0) : AmbientSpace) μ =
      (x : AmbientSpace) μ +
        ((n 0 • InfiniteLattice.axisStep (meshAt L 0 0) 0 : FullSpace.Vertex L 0 0) : AmbientSpace) μ +
        ((n 1 • InfiniteLattice.axisStep (meshAt L 0 0) 1 : FullSpace.Vertex L 0 0) : AmbientSpace) μ +
        ((n 2 • InfiniteLattice.axisStep (meshAt L 0 0) 2 : FullSpace.Vertex L 0 0) : AmbientSpace) μ +
        ((n 3 • InfiniteLattice.axisStep (meshAt L 0 0) 3 : FullSpace.Vertex L 0 0) : AmbientSpace) μ := rfl
  have hr : ((x + latticePoint L n : FullSpace.Vertex L 0 0) : AmbientSpace) μ =
      (x : AmbientSpace) μ + (n μ : ℝ) * meshAt L 0 0 := rfl
  have hs : (n μ : ℝ) * meshAt L 0 0 = n μ := by rw [meshAt_zero_zero, mul_one]
  rw [hl, hr, hc, hc, hc, hc, hs]
  fin_cases μ <;> simp
theorem coord_zero_add_zsmul (k : ℤ) (x : FullSpace.Vertex L 0 0) :
    ((x + k • InfiniteLattice.axisStep (meshAt L 0 0) 0 : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
      (x : AmbientSpace) 0 + k := by
  have : ((x + k • InfiniteLattice.axisStep (meshAt L 0 0) 0 : FullSpace.Vertex L 0 0) : AmbientSpace) 0 =
      (x : AmbientSpace) 0 +
        k • ((InfiniteLattice.axisStep (meshAt L 0 0) 0 : FullSpace.Vertex L 0 0) : AmbientSpace) 0 := rfl
  rw [this, axisStep_coord]
  simp
theorem weylExplicitFormulas_holds : WeylExplicitFormulas := by
  intro L φ
  refine ⟨fun w x => ⟨?_, fun μ hμ => ?_⟩, fun μ => ⟨?_, fun w x => magneticTranslation_apply φ μ w x⟩,
    fun w => ?_, fun μ ν hμν h01 h10 w => ?_, fun n w x => ?_⟩
  · unfold FullSpace.chargedShift
    have ha := two_mul_halfFluxAngle φ (1 : Fin 4) x
    simp only [phaseAngle, if_true] at ha
    congr 2
    have ha' : (2 : ℂ) * (halfFluxAngle L φ (FullSpace.forwardEdge x 1) : ℂ) =
        (φ : ℂ) * (((x : AmbientSpace) 0 : ℝ) : ℂ) := by exact_mod_cast ha
    linear_combination Complex.I * ha'
  · unfold FullSpace.chargedShift
    have ha := two_mul_halfFluxAngle φ μ x
    simp only [phaseAngle, if_neg hμ] at ha
    have ha' : (halfFluxAngle L φ (FullSpace.forwardEdge x μ) : ℂ) = 0 := by
      have : halfFluxAngle L φ (FullSpace.forwardEdge x μ) = 0 := by linarith
      exact_mod_cast this
    rw [ha']
    simp
  · exact ⟨(magneticTranslation L φ μ).toLinearEquiv.bijective,
      fun w => (magneticTranslation L φ μ).norm_map w⟩
  · refine lp.ext (funext fun x => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply]
    simp only [magneticTranslation_eq, smul_smul, ← Complex.exp_add]
    rw [add_right_comm x]
    congr 2
    simp only [phaseAngle, coord_zero_add_axisStep]
    norm_num
    ring
  · refine lp.ext (funext fun x => ?_)
    simp only [magneticTranslation_eq, smul_smul, ← Complex.exp_add]
    rw [add_right_comm x]
    congr 2
    have hsum : phaseAngle φ μ x + phaseAngle φ ν (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) =
        phaseAngle φ ν x + phaseAngle φ μ (x + InfiniteLattice.axisStep (meshAt L 0 0) ν) := by
      simp only [phaseAngle, coord_zero_add_axisStep]
      by_cases hμ1 : μ = 1
      · have hν1 : ν ≠ 1 := fun h => hμν (hμ1.trans h.symm)
        have hν0 : ν ≠ 0 := fun h => h10 ⟨hμ1, h⟩
        simp [hμ1, hν1, hν0]
      · by_cases hν1 : ν = 1
        · have hμ0 : μ ≠ 0 := fun h => h01 ⟨h, hν1⟩
          simp [hμ1, hν1, hμ0]
        · simp [hμ1, hν1]
    have hc : ((phaseAngle φ μ x + phaseAngle φ ν (x + InfiniteLattice.axisStep (meshAt L 0 0) μ) : ℝ) : ℂ) =
        ((phaseAngle φ ν x + phaseAngle φ μ (x + InfiniteLattice.axisStep (meshAt L 0 0) ν) : ℝ) : ℂ) := by
      rw [hsum]
    push_cast at hc
    linear_combination Complex.I * hc
  · have hW : magneticWeyl L φ n w =
        Complex.exp (-Complex.I * (φ : ℂ) * (n 0 : ℂ) * (n 1 : ℂ) / 2) •
          (magneticTranslation L φ 0 ^ n 0) ((magneticTranslation L φ 1 ^ n 1)
            ((magneticTranslation L φ 2 ^ n 2) ((magneticTranslation L φ 3 ^ n 3) w))) :=
      rfl
    rw [hW, lp.coeFn_smul, Pi.smul_apply]
    simp only [magneticTranslation_zpow, smul_smul, ← Complex.exp_add]
    rw [add_zsmul_axisSteps]
    congr 2
    have a0 : ∀ y : FullSpace.Vertex L 0 0, phaseAngle φ 0 y = 0 := fun y => if_neg (by decide)
    have a2 : ∀ y : FullSpace.Vertex L 0 0, phaseAngle φ 2 y = 0 := fun y => if_neg (by decide)
    have a3 : ∀ y : FullSpace.Vertex L 0 0, phaseAngle φ 3 y = 0 := fun y => if_neg (by decide)
    have a1 : phaseAngle φ 1 (x + n 0 • InfiniteLattice.axisStep (meshAt L 0 0) 0) =
        φ * ((x : AmbientSpace) 0 + n 0) := by
      rw [← coord_zero_add_zsmul]
      exact if_pos rfl
    simp only [a0, a1, a2, a3]
    push_cast
    ring
end Tower.MagneticWeylFormulas
end YangMills.Construction
end
