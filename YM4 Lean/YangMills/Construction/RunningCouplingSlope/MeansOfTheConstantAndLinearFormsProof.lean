import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.RunningCouplingSlope.MeansOfTheConstantAndLinearForms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages hiding stepDisplacement
open YangMills.Construction.LatticePaths YangMills.Construction.FlatPairing YangMills.Construction.FlatLinearization YangMills.Construction.SlopeCoefficient YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.TorusLumps
private theorem lineSum_append (ξ : LatticeOneForm) (z : Fin 4 → ℤ) (l l' : List PathStep) :
    latticeLineSum ξ z (l ++ l') = latticeLineSum ξ z l + latticeLineSum ξ (endpoint z l) l' := by
  induction l generalizing z with
  | nil => simp [latticeLineSum, endpoint]
  | cons st r ih => simp only [List.cons_append, latticeLineSum, endpoint, ih, add_assoc]
private theorem lineSum_reversePath (ξ : LatticeOneForm) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum ξ (endpoint z l) (reversePath l) = - latticeLineSum ξ z l := by
  induction l generalizing z with
  | nil => simp [latticeLineSum, endpoint, reversePath]
  | cons st r ih =>
    rw [reversePath_cons, lineSum_append]
    show latticeLineSum ξ (endpoint (z + stepDisplacement st) r) (reversePath r) +
      latticeLineSum ξ (endpoint (endpoint (z + stepDisplacement st) r) (reversePath r)) [(st.1, !st.2)] = _
    rw [ih, endpoint_reversePath]
    rcases st with ⟨i, b⟩
    cases b
    · simp [latticeLineSum, stepDisplacement, sub_eq_add_neg]
    · simp [latticeLineSum, stepDisplacement]
private theorem lineSum_const_mul (a : ℝ) (ξ : LatticeOneForm) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum (fun b => a * ξ b) z l = a * latticeLineSum ξ z l := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    simp only [latticeLineSum, ih]
    split_ifs <;> ring
private theorem lineSum_add_const_mul (a : ℝ) (ξ η : LatticeOneForm) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum (fun b => ξ b + a * η b) z l = latticeLineSum ξ z l + a * latticeLineSum η z l := by
  induction l generalizing z with
  | nil => simp [latticeLineSum]
  | cons st r ih =>
    simp only [latticeLineSum, ih]
    split_ifs <;> ring
private theorem lineSum_translate (ξ : LatticeOneForm) (w z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum ξ (z + w) l = latticeLineSum (fun b => ξ (b.1 + w, b.2)) z l := by
  induction l generalizing z with
  | nil => rfl
  | cons st r ih =>
    simp only [latticeLineSum]
    rw [← ih, add_right_comm z w (stepDisplacement st), sub_add_eq_add_sub]
private theorem lineSum_constantOneForm (ν : Fin 4) (z : Fin 4 → ℤ) (l : List PathStep) :
    latticeLineSum (constantOneForm ν) z l = ((endpoint z l ν : ℤ) : ℝ) - ((z ν : ℤ) : ℝ) := by
  induction l generalizing z with
  | nil => simp [latticeLineSum, endpoint]
  | cons st r ih =>
    rcases st with ⟨i, b⟩
    simp only [latticeLineSum, endpoint, ih]
    by_cases hi : i = ν
    · subst hi
      cases b <;> simp [constantOneForm, stepDisplacement, basisVector]
      all_goals ring
    · have hi' : ν ≠ i := fun h => hi h.symm
      cases b <;> simp [constantOneForm, stepDisplacement, basisVector, hi, hi']
private theorem endpoint_axisPath (z h : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)) :
    endpoint z (axisPath h σ) = z + h := by
  have e := endpoint_add 0 z (axisPath h σ)
  rw [zero_add, (axisPath_spec h σ).2] at e
  rw [e, add_comm]
private theorem endpoint_bondContour (L : ℕ) (z h : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    endpoint z (bondContour L h σ i) = z + (L : ℤ) • basisVector i := by
  unfold bondContour
  rw [endpoint_append, endpoint_append, endpoint_axisPath, endpoint_replicate]
  have e : z + h + (L : ℤ) • stepDisplacement (i, true) =
      endpoint (z + (L : ℤ) • basisVector i) (axisPath h σ) := by
    rw [endpoint_axisPath]
    simp only [stepDisplacement, if_true]
    abel
  rw [e, endpoint_reversePath]
private theorem lineSum_bondContour (ξ : LatticeOneForm) (L : ℕ) (z h : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4))
    (i : Fin 4) :
    latticeLineSum ξ z (bondContour L h σ i) =
      latticeLineSum ξ z (axisPath h σ) + latticeLineSum ξ (z + h) (List.replicate L (i, true)) -
        latticeLineSum ξ (z + (L : ℤ) • basisVector i) (axisPath h σ) := by
  unfold bondContour
  rw [lineSum_append, lineSum_append, endpoint_append, endpoint_axisPath, endpoint_replicate]
  have e : z + h + (L : ℤ) • stepDisplacement (i, true) =
      endpoint (z + (L : ℤ) • basisVector i) (axisPath h σ) := by
    rw [endpoint_axisPath]
    simp only [stepDisplacement, if_true]
    abel
  rw [e, lineSum_reversePath]
  ring
private theorem lineSum_fineLinearPotential_replicate (L n : ℕ) (i : Fin 4) (u : Fin 4 → ℤ) :
    latticeLineSum (fineLinearPotential L) u (List.replicate n (i, true)) =
      (n : ℝ) * ((L : ℝ)⁻¹ ^ 2 * ((u 0 : ℤ) : ℝ) * constantOneForm secondAxis (u, i)) := by
  induction n generalizing u with
  | zero => simp [latticeLineSum]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [latticeLineSum, if_true, ih]
    have e : (u + stepDisplacement (i, true)) 0 = u 0 ∨ constantOneForm secondAxis (u, i) = 0 := by
      by_cases hi : i = secondAxis
      · left
        subst hi
        simp [stepDisplacement, basisVector, secondAxis]
      · right
        simp [constantOneForm, hi]
    have c : constantOneForm secondAxis (u + stepDisplacement (i, true), i) =
        constantOneForm secondAxis (u, i) := rfl
    rw [c]
    rcases e with e | e
    · rw [e]
      simp only [fineLinearPotential]
      push_cast
      ring
    · simp [fineLinearPotential, e]
private theorem fineLinearPotential_translate (L : ℕ) (hL : (L : ℝ) ≠ 0) (i : Fin 4) :
    (fun b : LatticeBond => fineLinearPotential L (b.1 + (L : ℤ) • basisVector i, b.2)) =
      fun b => fineLinearPotential L b + (if i = 0 then (L : ℝ)⁻¹ else 0) * constantOneForm secondAxis b := by
  funext b
  have c : constantOneForm secondAxis (b.1 + (L : ℤ) • basisVector i, b.2) = constantOneForm secondAxis b := rfl
  simp only [fineLinearPotential, c]
  by_cases hi : i = 0
  · subst hi
    simp [basisVector]
    field_simp
  · have hi' : (0 : Fin 4) ≠ i := fun h => hi h.symm
    simp [basisVector, hi, hi']
private theorem lineSum_fineLinearPotential_bondContour (L : ℕ) (hL : (L : ℝ) ≠ 0) (y h : Fin 4 → ℤ)
    (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    latticeLineSum (fineLinearPotential L) (blockCentreOnLattice L y) (bondContour L h σ i) =
      ((y 0 : ℤ) : ℝ) * constantOneForm secondAxis (y, i) +
        (L : ℝ)⁻¹ * constantOneForm secondAxis (y, i) * ((h 0 : ℤ) : ℝ) -
          (if i = 0 then (L : ℝ)⁻¹ else 0) * ((h 1 : ℤ) : ℝ) := by
  rw [lineSum_bondContour, lineSum_translate (fineLinearPotential L) ((L : ℤ) • basisVector i),
    fineLinearPotential_translate L hL, lineSum_add_const_mul, lineSum_constantOneForm, endpoint_axisPath,
    lineSum_fineLinearPotential_replicate]
  have c : constantOneForm secondAxis (blockCentreOnLattice L y + h, i) = constantOneForm secondAxis (y, i) := rfl
  rw [c]
  have e1 : (secondAxis : Fin 4) = 1 := rfl
  simp only [blockCentreOnLattice, Pi.add_apply, e1]
  push_cast
  field_simp
  ring
private theorem sum_centredCube_coord (L : ℕ) (j : Fin 4) : ∑ h ∈ centredCube L, ((h j : ℤ) : ℝ) = 0 := by
  have e : ∑ h ∈ centredCube L, ((h j : ℤ) : ℝ) = ∑ h ∈ centredCube L, -((h j : ℤ) : ℝ) := by
    refine Finset.sum_nbij' (fun h => -h) (fun h => -h) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      refine (mem_centredCube_iff L _).2 fun μ => ?_
      have := (mem_centredCube_iff L h).1 hh μ
      simp only [Pi.neg_apply]
      omega
    · intro h hh
      refine (mem_centredCube_iff L _).2 fun μ => ?_
      have := (mem_centredCube_iff L h).1 hh μ
      simp only [Pi.neg_apply]
      omega
    · intro h _
      simp
    · intro h _
      simp
    · intro h _
      simp
  rw [Finset.sum_neg_distrib] at e
  linarith
private theorem average_of_affine (L : ℕ) (hodd : Odd L) (hL : (L : ℝ) ≠ 0) (f : (Fin 4 → ℤ) → ℝ) (A B C : ℝ)
    (hf : ∀ h, f h = A + B * ((h 0 : ℤ) : ℝ) - C * ((h 1 : ℤ) : ℝ)) :
    (1 / (24 * (L : ℝ) ^ 4)) * ∑ h ∈ centredCube L, ∑ _σ : Equiv.Perm (Fin 4), f h = A := by
  have hc : ((centredCube L).card : ℝ) = (L : ℝ) ^ 4 := by
    rw [card_centredCube hodd]
    push_cast
    rfl
  have e : ∑ h ∈ centredCube L, ∑ _σ : Equiv.Perm (Fin 4), f h = 24 * ((L : ℝ) ^ 4 * A) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, hf]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_centredCube_coord, sum_centredCube_coord, Finset.sum_const, nsmul_eq_mul, hc]
    norm_num [Nat.factorial]
  rw [e]
  field_simp
theorem contourAveragesOfConstantAndLinear_holds : ContourAveragesOfConstantAndLinear := by
  intro L hLs
  have hodd : Odd L := hLs.1
  have hL : (L : ℝ) ≠ 0 := by
    have : L ≠ 0 := by
      have := hLs.2
      omega
    exact Nat.cast_ne_zero.mpr this
  refine ⟨fun ν c => ?_, fun c => ?_⟩
  · have key : ∀ h σ, latticeLineSum (fun b => (L : ℝ)⁻¹ * constantOneForm ν b) (blockCentreOnLattice L c.1)
        (bondContour L h σ c.2) = constantOneForm ν c := by
      intro h σ
      rw [lineSum_const_mul, lineSum_constantOneForm, endpoint_bondContour]
      by_cases hi : c.2 = ν
      · simp [constantOneForm, basisVector, hi]
        field_simp
      · have hi' : ν ≠ c.2 := fun e => hi e.symm
        simp [constantOneForm, basisVector, hi, hi']
    unfold latticeContourAverage
    simp only [key]
    exact average_of_affine L hodd hL (fun _ => constantOneForm ν c) _ 0 0 (by simp)
  · have key := fun h σ => lineSum_fineLinearPotential_bondContour L hL c.1 h σ c.2
    unfold latticeContourAverage
    simp only [key]
    exact average_of_affine L hodd hL _ _ _ _ (fun h => rfl)
end YangMills.Construction.RunningCouplingSlope
end
