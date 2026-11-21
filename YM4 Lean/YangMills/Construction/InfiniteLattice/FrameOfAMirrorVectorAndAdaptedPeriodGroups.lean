import YangMills.Construction.InfiniteLattice.FramesRectangularPeriodLatticesAndTheBox
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (coordVec)
inductive IsAdaptedQuadruple : AmbientSpace → (Fin 4 → AmbientSpace) → Prop
  | axis {μ ρ ρ' ρ'' : Fin 4} (h₁ : ρ < ρ') (h₂ : ρ' < ρ'') (hρ : ρ ≠ μ) (hρ' : ρ' ≠ μ)
      (hρ'' : ρ'' ≠ μ) :
      IsAdaptedQuadruple (coordVec μ)
        ![coordVec μ, coordVec ρ, coordVec ρ', coordVec ρ'']
  | diff {μ lam ρ ρ' : Fin 4} (hlam : μ < lam) (h : ρ < ρ') (hρμ : ρ ≠ μ) (hρlam : ρ ≠ lam)
      (hρ'μ : ρ' ≠ μ) (hρ'lam : ρ' ≠ lam) :
      IsAdaptedQuadruple (coordVec μ - coordVec lam)
        ![coordVec μ - coordVec lam, coordVec μ + coordVec lam,
          coordVec ρ, coordVec ρ']
  | sum {μ lam ρ ρ' : Fin 4} (hlam : μ < lam) (h : ρ < ρ') (hρμ : ρ ≠ μ) (hρlam : ρ ≠ lam)
      (hρ'μ : ρ' ≠ μ) (hρ'lam : ρ' ≠ lam) :
      IsAdaptedQuadruple (coordVec μ + coordVec lam)
        ![coordVec μ + coordVec lam, coordVec μ - coordVec lam,
          coordVec ρ, coordVec ρ']
theorem coordVec_dot_coordVec_self (μ : Fin 4) :
    coordVec μ ⬝ᵥ coordVec μ = 1 := by
  simp [coordVec]
theorem coordVec_dot_coordVec_of_ne {μ ν : Fin 4} (h : μ ≠ ν) :
    coordVec μ ⬝ᵥ coordVec ν = 0 := by
  simp [coordVec, h]
theorem exists_three_other_axes :
    ∀ μ : Fin 4, ∃ ρ ρ' ρ'' : Fin 4, ρ < ρ' ∧ ρ' < ρ'' ∧ ρ ≠ μ ∧ ρ' ≠ μ ∧ ρ'' ≠ μ := by
  decide
theorem exists_two_other_axes :
    ∀ μ lam : Fin 4, μ < lam → ∃ ρ ρ' : Fin 4, ρ < ρ' ∧ ρ ≠ μ ∧ ρ ≠ lam ∧ ρ' ≠ μ ∧ ρ' ≠ lam := by
  decide
theorem exists_isAdaptedQuadruple {n : AmbientSpace} (hn : IsNormalVector n) :
    ∃ v, IsAdaptedQuadruple n v := by
  rcases hn with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · obtain ⟨ρ, ρ', ρ'', h₁, h₂, h₃, h₄, h₅⟩ := exists_three_other_axes μ
    exact ⟨_, .axis h₁ h₂ h₃ h₄ h₅⟩
  · obtain ⟨ρ, ρ', h₁, h₂, h₃, h₄, h₅⟩ := exists_two_other_axes μ lam hlt
    exact ⟨_, .sum hlt h₁ h₂ h₃ h₄ h₅⟩
  · obtain ⟨ρ, ρ', h₁, h₂, h₃, h₄, h₅⟩ := exists_two_other_axes μ lam hlt
    exact ⟨_, .diff hlt h₁ h₂ h₃ h₄ h₅⟩
namespace IsAdaptedQuadruple
variable {n : AmbientSpace} {v : Fin 4 → AmbientSpace}
theorem apply_zero (h : IsAdaptedQuadruple n v) : v 0 = n := by
  cases h <;> rfl
theorem isNormal (h : IsAdaptedQuadruple n v) (i : Fin 4) : IsNormalVector (v i) := by
  have he : ∀ μ : Fin 4, IsNormalVector (coordVec μ) := fun μ => Or.inl ⟨μ, rfl⟩
  cases h with
  | axis h₁ h₂ hρ hρ' hρ'' => fin_cases i <;> exact he _
  | diff hlam h hρμ hρlam hρ'μ hρ'lam =>
    fin_cases i
    · exact Or.inr ⟨_, _, hlam, Or.inr rfl⟩
    · exact Or.inr ⟨_, _, hlam, Or.inl rfl⟩
    · exact he _
    · exact he _
  | sum hlam h hρμ hρlam hρ'μ hρ'lam =>
    fin_cases i
    · exact Or.inr ⟨_, _, hlam, Or.inl rfl⟩
    · exact Or.inr ⟨_, _, hlam, Or.inr rfl⟩
    · exact he _
    · exact he _
theorem pairwise_orthogonal (h : IsAdaptedQuadruple n v) :
    Pairwise fun i j => v i ⬝ᵥ v j = 0 := by
  have key : ∀ i j : Fin 4, i < j → v i ⬝ᵥ v j = 0 := by
    cases h with
    | axis h₁ h₂ hρ hρ' hρ'' =>
      have a := coordVec_dot_coordVec_of_ne hρ.symm
      have b := coordVec_dot_coordVec_of_ne hρ'.symm
      have c := coordVec_dot_coordVec_of_ne hρ''.symm
      have d := coordVec_dot_coordVec_of_ne h₁.ne
      have e := coordVec_dot_coordVec_of_ne (h₁.trans h₂).ne
      have f := coordVec_dot_coordVec_of_ne h₂.ne
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [a, b, c, d, e, f]
    | @diff μ lam ρ ρ' hlam h hρμ hρlam hρ'μ hρ'lam =>
      have a := coordVec_dot_coordVec_of_ne hρμ.symm
      have b := coordVec_dot_coordVec_of_ne hρlam.symm
      have c := coordVec_dot_coordVec_of_ne hρ'μ.symm
      have d := coordVec_dot_coordVec_of_ne hρ'lam.symm
      have e := coordVec_dot_coordVec_of_ne h.ne
      have f := coordVec_dot_coordVec_of_ne hlam.ne
      have f' := coordVec_dot_coordVec_of_ne hlam.ne'
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact absurd hij (by decide)
        | simp [sub_dotProduct, add_dotProduct, dotProduct_add, coordVec_dot_coordVec_self, a, b, c, d,
            e, f, f']
    | @sum μ lam ρ ρ' hlam h hρμ hρlam hρ'μ hρ'lam =>
      have a := coordVec_dot_coordVec_of_ne hρμ.symm
      have b := coordVec_dot_coordVec_of_ne hρlam.symm
      have c := coordVec_dot_coordVec_of_ne hρ'μ.symm
      have d := coordVec_dot_coordVec_of_ne hρ'lam.symm
      have e := coordVec_dot_coordVec_of_ne h.ne
      have f := coordVec_dot_coordVec_of_ne hlam.ne
      have f' := coordVec_dot_coordVec_of_ne hlam.ne'
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact absurd hij (by decide)
        | simp [sub_dotProduct, add_dotProduct, dotProduct_sub, coordVec_dot_coordVec_self, a, b, c, d,
            e, f, f']
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt
  · rw [dotProduct_comm]
    exact key j i hlt
end IsAdaptedQuadruple
def normalFrame (n : AmbientSpace) (hn : IsNormalVector n) : OrthogonalNormalFrame where
  vec := (exists_isAdaptedQuadruple hn).choose
  isNormal := (exists_isAdaptedQuadruple hn).choose_spec.isNormal
  pairwise_orthogonal := (exists_isAdaptedQuadruple hn).choose_spec.pairwise_orthogonal
theorem isAdaptedQuadruple_normalFrame (n : AmbientSpace) (hn : IsNormalVector n) :
    IsAdaptedQuadruple n (normalFrame n hn).vec :=
  (exists_isAdaptedQuadruple hn).choose_spec
theorem normalFrame_vec_zero (n : AmbientSpace) (hn : IsNormalVector n) :
    (normalFrame n hn).vec 0 = n :=
  (isAdaptedQuadruple_normalFrame n hn).apply_zero
def AdmissibleParams (h J w : ℤ) : Prop := Even h ∧ 2 ≤ h ∧ 1 ≤ J ∧ Even w ∧ 2 ≤ w
def longPeriod (n : AmbientSpace) (h J : ℤ) : AmbientSpace :=
  (2 * (J : ℝ) * (h : ℝ)) • dualVector n
def shortPeriod (n : AmbientSpace) (hn : IsNormalVector n) (w : ℤ) (i : Fin 3) : AmbientSpace :=
  (w : ℝ) • (normalFrame n hn).vec i.succ
def adaptedLattice (n : AmbientSpace) (hn : IsNormalVector n) (h J w : ℤ) :
    AddSubgroup AmbientSpace :=
  AddSubgroup.zmultiples (longPeriod n h J) ⊔
    ⨆ i : Fin 3, AddSubgroup.zmultiples (shortPeriod n hn w i)
theorem mem_adaptedLattice_iff {n : AmbientSpace} {hn : IsNormalVector n} {h J w : ℤ}
    {x : AmbientSpace} :
    x ∈ adaptedLattice n hn h J w ↔
      ∃ (b : ℤ) (c : Fin 3 → ℤ),
        x = b • longPeriod n h J + ∑ i, c i • shortPeriod n hn w i := by
  rw [adaptedLattice, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    have key : ∃ c : Fin 3 → ℤ, z = ∑ i, c i • shortPeriod n hn w i := by
      induction hz using AddSubgroup.iSup_induction' with
      | hp i x hx =>
        obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
        refine ⟨Pi.single i k, ?_⟩
        simp [Pi.single_apply, ite_smul]
      | h1 => exact ⟨0, by simp⟩
      | hadd x y _ _ hx hy =>
        obtain ⟨c, rfl⟩ := hx
        obtain ⟨c', rfl⟩ := hy
        exact ⟨c + c', by simp [add_smul, Finset.sum_add_distrib]⟩
    obtain ⟨c, rfl⟩ := key
    exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨_, AddSubgroup.mem_zmultiples_iff.mpr ⟨b, rfl⟩, _, ?_, rfl⟩
    refine sum_mem fun i _ => ?_
    exact AddSubgroup.mem_iSup_of_mem i
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨c i, rfl⟩)
end YangMills.Construction.NormalFamilies
