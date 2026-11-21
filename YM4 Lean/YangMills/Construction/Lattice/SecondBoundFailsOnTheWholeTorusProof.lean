import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Lattice.RelationOfTheMassiveOperatorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedSequences.WholeTorusWave
theorem exists_latticeInner_adjoint (L t : ℕ) {ι κ : Type} [Finite ι] [Finite κ]
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ∃ T' : (κ → ℝ) →ₗ[ℝ] (ι → ℝ), ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine ⟨Matrix.toLin' (LinearMap.toMatrix' T).transpose, fun f g => ?_⟩
  have hT : T f = (LinearMap.toMatrix' T).mulVec f := (LinearMap.toMatrix'_mulVec T f).symm
  rw [hT, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  simp only [latticeInner, finsum_eq_sum_of_fintype]
  congr 1
  exact Matrix.dotProduct_mulVec g _ f
theorem latticeInner_comm (L t : ℕ) {ι : Type} (f g : ι → ℝ) :
    latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.MassiveRelation.latticeInner_comm <;> assumption
variable (D : BaseParameters)
theorem latticeInner_scalarLaplacian (f : ZeroForms D.L D.m D.K) :
    latticeInner D.L D.t f (scalarLaplacian D.L D.m D.K D.t f) =
      latticeInner D.L D.t (grad D.t f) (grad D.t f) := by
  have : Finite (BareSite D.L D.m D.K) := D.instFiniteLatticeSite 0
  have : Finite (BareBond D.L D.m D.K) := D.instFiniteLevelBond 0
  have h := Classical.epsilon_spec
    (exists_latticeInner_adjoint D.L D.t (grad (L := D.L) (m := D.m) (K := D.K) D.t))
  have hadj : ∀ f g, latticeInner D.L D.t g (grad D.t f) =
      latticeInner D.L D.t (gradAdjoint D.L D.m D.K D.t g) f := h
  rw [hadj f (grad D.t f), latticeInner_comm]
  rfl
theorem lengthInUnits_eq_mul (r : ℝ) :
    D.lengthInUnits r = (D.L : ℝ) ^ levelDepth D.K D.t * r := rfl
theorem lengthInUnits_add (r s : ℝ) :
    D.lengthInUnits (r + s) = D.lengthInUnits r + D.lengthInUnits s := by
  simp only [lengthInUnits_eq_mul, mul_add]
theorem exists_lengthInUnits_torusSide :
    ∃ N : ℤ, D.lengthInUnits (torusSide D.L D.m) = 2 * N := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, levelDepth D.K D.t = (e : ℤ) :=
    ⟨D.K - D.t, by have := D.t_le_K; simp only [levelDepth]; omega⟩
  refine ⟨((D.L ^ e * D.L ^ D.m : ℕ) : ℤ), ?_⟩
  rw [lengthInUnits_eq_mul, he, zpow_natCast, torusSide]
  push_cast
  ring
theorem L_pos_real : (0 : ℝ) < D.L := by apply _root_.YangMills.Construction.SeparatedSequences.LevelWeightMinimum.side_pos <;> assumption
theorem sineWave_periodic (a : ℝ) :
    Function.Periodic (fun r : ℝ => Real.sin (Real.pi * (D.lengthInUnits r - a)))
      (torusSide D.L D.m) := by
  intro r
  obtain ⟨N, hN⟩ := exists_lengthInUnits_torusSide D
  have h : Real.pi * (D.lengthInUnits (r + torusSide D.L D.m) - a) =
      Real.pi * (D.lengthInUnits r - a) + N * (2 * Real.pi) := by
    rw [lengthInUnits_add, hN]
    ring
  show Real.sin _ = Real.sin _
  rw [h]
  exact Real.sin_add_int_mul_two_pi _ _
def sineWave (a : ℝ) : AddCircle (torusSide D.L D.m) → ℝ := (sineWave_periodic D a).lift
def sineZeroForm (a : ℝ) : ZeroForms D.L D.m D.K := fun x => sineWave D a ((x : D.Torus) 0)
def reflectFirst (k : ℤ) (x : BareSite D.L D.m D.K) : BareSite D.L D.m D.K :=
  ⟨Function.update (x : D.Torus) 0
      ((((k : ℝ) * meshSize D.L (levelDepth D.K 0) : ℝ) : AddCircle (torusSide D.L D.m)) -
        (x : D.Torus) 0), by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨Function.update n 0 (k - n 0), fun μ => ?_⟩
    by_cases h : μ = 0
    · subst h
      simp only [Function.update_self]
      rw [hn 0, ← AddCircle.coe_sub]
      congr 1
      push_cast
      ring
    · simp only [Function.update_of_ne h]
      exact hn μ⟩
theorem sum_pointOnAxis (g : Fin 4 → ℝ) :
    ∑ μ, pointOnAxis D.L D.m μ (g μ) = fun μ => (g μ : AddCircle (torusSide D.L D.m)) :=
  Finset.univ_sum_single fun μ => (g μ : AddCircle (torusSide D.L D.m))
end SeparatedSequences.WholeTorusWave
end YangMills.Construction
end
