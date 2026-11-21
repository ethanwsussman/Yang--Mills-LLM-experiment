import YangMills.Construction.Lattice.PlaquetteHolonomyTrace
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import Mathlib
open Set
open YangMills.Construction.Matrices
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
namespace PlaquetteHolonomyTraceProof
theorem inv_eq_conjTranspose {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ = g.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem inv_mul_self_of_mem {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    g⁻¹ * g = 1 := by apply _root_.YangMills.SharedProofs.p1227 <;> assumption
theorem mul_eq_inv_mul_mul_mul {g Y : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.specialUnitary) :
    Y * g = g⁻¹ * (g * Y) * g := by
  rw [← Matrix.mul_assoc g⁻¹ g Y, inv_mul_self_of_mem hg, Matrix.one_mul]
theorem one_sub_half_re_fullTrace_mem_Icc (hT : ComplexMatrix2.UnitaryLogarithmProperties)
    {P : ComplexMatrix2} (hP : P ∈ ComplexMatrix2.specialUnitary) :
    1 - (1 / 2) * (ComplexMatrix2.fullTrace P).re ∈ Icc (0 : ℝ) 2 := by
  obtain ⟨⟨t, ht, e⟩, -⟩ := hT.2.1 P hP
  have h2 : ComplexMatrix2.fullTrace P = ((2 * t : ℝ) : ℂ) := by
    have h : ComplexMatrix2.fullTrace P = 2 * ComplexMatrix2.halfTrace P := by
      simp only [ComplexMatrix2.halfTrace]
      ring
    rw [h, e]
    push_cast
    ring
  rw [h2, Complex.ofReal_re]
  constructor <;> linarith [ht.1, ht.2]
theorem re_fullTrace_inv {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace X⁻¹).re = (ComplexMatrix2.fullTrace X).re := by
  rw [inv_eq_conjTranspose hX, ComplexMatrix2.fullTrace, Matrix.trace_conjTranspose]
  simp
theorem pathHolonomy_four (U : Bond L m j → ComplexMatrix2) (x y z w : Bond L m j) :
    pathHolonomy U [x, y, z, w] = U x * U y * U z * U w := by
  simp [pathHolonomy, mul_assoc]
theorem pathHolonomy_reversePath_four (U : Bond L m j → ComplexMatrix2) (x y z w : Bond L m j) :
    pathHolonomy U (reversePath [x, y, z, w]) =
      U w.opposite * U z.opposite * U y.opposite * U x.opposite := by
  simp [pathHolonomy, reversePath, mul_assoc]
theorem reversed_product_eq_inv {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U) {x y z w : Bond L m j}
    (hx : x ∈ ℬ) (hy : y ∈ ℬ) (hz : z ∈ ℬ) (hw : w ∈ ℬ) :
    U w.opposite * U z.opposite * U y.opposite * U x.opposite = (U x * U y * U z * U w)⁻¹ := by
  rw [hU.2 x hx, hU.2 y hy, hU.2 z hz, hU.2 w hw, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev]
  simp only [mul_assoc]
theorem plaquetteHolonomy_eq {p : Plaquette L m j} {b₁ b₂ b₃ b₄ : Bond L m j}
    (h : p.IsBoundedBy b₁ b₂ b₃ b₄) (U : Bond L m j → ComplexMatrix2) :
    plaquetteHolonomy U p = U b₁ * U b₂ * U b₃ * U b₄ := by
  obtain ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨t₃, h₃⟩, ⟨t₄, h₄⟩⟩ := h
  have e₁ : Bond.forwardFrom p.origin p.firstAxis = b₁ := Bond.ext t₁.symm h₁.symm
  have e₂ : Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis = b₂ :=
    Bond.ext t₂.symm h₂.symm
  have e₃ : (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite = b₃ := by
    refine Bond.ext ?_ h₃.symm
    rw [t₃]
    exact add_right_comm _ _ _
  have e₄ : (Bond.forwardFrom p.origin p.secondAxis).opposite = b₄ := Bond.ext t₄.symm h₄.symm
  simp only [plaquetteHolonomy, Plaquette.boundaryBonds, e₁, e₂, e₃, e₄]
  exact pathHolonomy_four U b₁ b₂ b₃ b₄
theorem half_re_fullTrace_of_path {ℬ : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup ℬ U) {x y z w : Bond L m j}
    (hx : x ∈ ℬ) (hy : y ∈ ℬ) (hz : z ∈ ℬ) (hw : w ∈ ℬ) {T : ℂ}
    (hT : ComplexMatrix2.fullTrace (U x * U y * U z * U w) = T) :
    (1 / 2) * (ComplexMatrix2.fullTrace (pathHolonomy U [x, y, z, w])).re = (1 / 2) * T.re ∧
      (1 / 2) * (ComplexMatrix2.fullTrace (pathHolonomy U (reversePath [x, y, z, w]))).re =
        (1 / 2) * T.re := by
  have g : U x * U y * U z * U w ∈ ComplexMatrix2.specialUnitary :=
    mul_mem (mul_mem (mul_mem (hU.1 x hx) (hU.1 y hy)) (hU.1 z hz)) (hU.1 w hw)
  rw [pathHolonomy_four, pathHolonomy_reversePath_four, reversed_product_eq_inv hU hx hy hz hw,
    re_fullTrace_inv g, hT]
  exact ⟨rfl, rfl⟩
theorem plaquetteHolonomyTraceBounds_holds (hT : ComplexMatrix2.UnitaryLogarithmProperties) :
    PlaquetteHolonomyTraceBounds := by
  intro s
  refine ⟨?_, ?_⟩
  · intro j _ p b₁ b₂ b₃ b₄ hp ℬ U _ hU h₁ h₂ h₃ h₄
    have eP := plaquetteHolonomy_eq hp U
    have g₁ : U b₁ ∈ ComplexMatrix2.specialUnitary := hU.1 b₁ h₁
    have g₂ : U b₂ ∈ ComplexMatrix2.specialUnitary := hU.1 b₂ h₂
    have g₃ : U b₃ ∈ ComplexMatrix2.specialUnitary := hU.1 b₃ h₃
    have g₄ : U b₄ ∈ ComplexMatrix2.specialUnitary := hU.1 b₄ h₄
    have g₁₂ : U b₁ * U b₂ ∈ ComplexMatrix2.specialUnitary := mul_mem g₁ g₂
    have g₁₂₃ : U b₁ * U b₂ * U b₃ ∈ ComplexMatrix2.specialUnitary := mul_mem g₁₂ g₃
    have gP : plaquetteHolonomy U p ∈ ComplexMatrix2.specialUnitary := by
      rw [eP]
      exact mul_mem g₁₂₃ g₄
    have rot₂ : U b₂ * U b₃ * U b₄ * U b₁ = (U b₁)⁻¹ * plaquetteHolonomy U p * U b₁ := by
      rw [eP]
      simpa only [mul_assoc] using mul_eq_inv_mul_mul_mul (Y := U b₂ * U b₃ * U b₄) g₁
    have rot₃ : U b₃ * U b₄ * U b₁ * U b₂ =
        (U b₁ * U b₂)⁻¹ * plaquetteHolonomy U p * (U b₁ * U b₂) := by
      rw [eP]
      simpa only [mul_assoc] using mul_eq_inv_mul_mul_mul (Y := U b₃ * U b₄) g₁₂
    have rot₄ : U b₄ * U b₁ * U b₂ * U b₃ =
        (U b₁ * U b₂ * U b₃)⁻¹ * plaquetteHolonomy U p * (U b₁ * U b₂ * U b₃) := by
      rw [eP]
      simpa only [mul_assoc] using mul_eq_inv_mul_mul_mul (Y := U b₄) g₁₂₃
    have rev : U b₄.opposite * U b₃.opposite * U b₂.opposite * U b₁.opposite =
        (plaquetteHolonomy U p)⁻¹ := by
      rw [eP]
      exact reversed_product_eq_inv hU h₁ h₂ h₃ h₄
    have tr₂ : ComplexMatrix2.fullTrace (U b₂ * U b₃ * U b₄ * U b₁) =
        ComplexMatrix2.fullTrace (plaquetteHolonomy U p) := by
      rw [eP, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm]
      simp only [mul_assoc]
    have tr₃ : ComplexMatrix2.fullTrace (U b₃ * U b₄ * U b₁ * U b₂) =
        ComplexMatrix2.fullTrace (plaquetteHolonomy U p) := by
      rw [eP, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, mul_assoc (U b₃ * U b₄),
        Matrix.trace_mul_comm]
      simp only [mul_assoc]
    have tr₄ : ComplexMatrix2.fullTrace (U b₄ * U b₁ * U b₂ * U b₃) =
        ComplexMatrix2.fullTrace (plaquetteHolonomy U p) := by
      rw [eP, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, mul_assoc (U b₄ * U b₁),
        mul_assoc (U b₄), Matrix.trace_mul_comm]
      simp only [mul_assoc]
    refine ⟨⟨eP, gP, (hT.2.1 _ gP).1, one_sub_half_re_fullTrace_mem_Icc hT gP⟩, rot₂, g₁, rot₃,
      g₁₂, rot₄, g₁₂₃, rev, inv_eq_conjTranspose gP, ?_⟩
    intro Γ hΓ
    simp only [cyclicBoundaryPaths, List.mem_cons, List.not_mem_nil, or_false] at hΓ
    rcases hΓ with rfl | rfl | rfl | rfl
    · exact half_re_fullTrace_of_path hU h₁ h₂ h₃ h₄ (by rw [eP])
    · exact half_re_fullTrace_of_path hU h₂ h₃ h₄ h₁ tr₂
    · exact half_re_fullTrace_of_path hU h₃ h₄ h₁ h₂ tr₃
    · exact half_re_fullTrace_of_path hU h₄ h₁ h₂ h₃ tr₄
  · intro p U hU
    have hU' : IsGaugeField compactGaugeGroup univ U := hU
    have gP : plaquetteHolonomy U p ∈ ComplexMatrix2.specialUnitary := by
      simp only [plaquetteHolonomy, Plaquette.boundaryBonds]
      rw [pathHolonomy_four]
      exact mul_mem (mul_mem (mul_mem (hU'.1 _ (mem_univ _)) (hU'.1 _ (mem_univ _)))
        (hU'.1 _ (mem_univ _))) (hU'.1 _ (mem_univ _))
    exact one_sub_half_re_fullTrace_mem_Icc hT gP
end PlaquetteHolonomyTraceProof
end YangMills.Construction.PeriodicLattice
