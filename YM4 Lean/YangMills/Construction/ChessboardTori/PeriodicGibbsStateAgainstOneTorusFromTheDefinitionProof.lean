import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.GibbsStateAgainstOneTorus
import YangMills.Construction.ChessboardTori.PeriodicGibbsStateAgainstOneTorusFromTheDefinition
import YangMills.Construction.ChessboardTori.TranslationsOfPeriodicGibbsStatesInTheGroupOfAGrid
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace observableSupNorm)
namespace PeriodicGibbsBoundOfFiniteIndexProof
theorem isBoundedObservable_of_mem_cellObservables {D : ChessboardSetup} {S : Set AmbientSpace}
    {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) : InfiniteLattice.IsBoundedObservable F := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_of_mem_cellObservables <;> assumption
theorem exists_phase_mul_eq_norm (z : ℂ) :
    ∃ θ : ℝ, Complex.exp (-(Complex.I * θ)) * z = ((‖z‖ : ℝ) : ℂ) := by
  refine ⟨Complex.arg z, ?_⟩
  have hpolar := Complex.norm_mul_exp_arg_mul_I z
  calc Complex.exp (-(Complex.I * (Complex.arg z : ℝ))) * z
      = Complex.exp (-(Complex.I * (Complex.arg z : ℝ))) *
          (((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℝ) * Complex.I)) := by rw [hpolar]
    _ = ((‖z‖ : ℝ) : ℂ) * (Complex.exp (-(Complex.I * (Complex.arg z : ℝ))) *
          Complex.exp ((Complex.arg z : ℝ) * Complex.I)) := by ring
    _ = ((‖z‖ : ℝ) : ℂ) := by
        rw [← Complex.exp_add, mul_comm Complex.I, neg_add_cancel, Complex.exp_zero, mul_one]
theorem toLatticeSym_eq_shift {D : ChessboardSetup} (c : ReflectionGrid D) (r : c.reflectionGroup)
    (k : Fin 4 → ℤ) (hr : (r.1 : AmbientSpace → AmbientSpace) = translate (c.cellOffsetVector k)) :
    c.toLatticeSym r = InfiniteLattice.shift (c.cellOffsetPoint k) := by
  have hfun : (c.toLatticeSym r).toFun = (InfiniteLattice.shift (c.cellOffsetPoint k)).toFun := hr
  generalize c.toLatticeSym r = σ at hfun
  generalize InfiniteLattice.shift (c.cellOffsetPoint k) = τ at hfun
  cases σ
  cases τ
  cases hfun
  rfl
theorem le_add_of_mul_le_mul_add {N H x C a s l Q : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hs : 0 < s)
    (hl : 0 < l) (hQ : 0 < Q) (hN : (l / s / Q) ^ 4 ≤ N)
    (h : N * H ≤ N * x + C * (l / a) ^ 3) :
    H ≤ x + Q ^ 4 * (C * (s / a) ^ 3 * (s / l)) := by
  have hM : 0 < (l / s / Q) ^ 4 := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le hM hN
  have hA : 0 ≤ C * (l / a) ^ 3 := by positivity
  have h1 : H ≤ x + C * (l / a) ^ 3 / N := by
    have e : x + C * (l / a) ^ 3 / N = (N * x + C * (l / a) ^ 3) / N := by
      field_simp
    rw [e, le_div_iff₀ hNpos]
    linarith
  have h2 : C * (l / a) ^ 3 / N ≤ C * (l / a) ^ 3 / (l / s / Q) ^ 4 :=
    div_le_div_of_nonneg_left hA hM hN
  have h3 : C * (l / a) ^ 3 / (l / s / Q) ^ 4 = Q ^ 4 * (C * (s / a) ^ 3 * (s / l)) := by
    field_simp
  linarith
theorem bound_at_torusSide (hroot : GibbsBoundOnOneTorus.Statement)
    (htrans : PeriodicStatesAndGridTranslations.Statement)
    (D : ChessboardSetup) (g : ReflectionGrid D) (hg : g.IsCoarse) (ν : Measure D.GaugeField)
    (hν : ν ∈ D.periodicStates) (O : Set (Set AmbientSpace)) (hO : g.IsFiniteCellFamily O)
    (F : Set AmbientSpace → D.GaugeField → ℂ)
    (hF : ∀ S ∈ O, F S ∈ ReflectionGrid.cellObservables (D := D) S)
    (Γ : AddSubgroup (InfiniteLattice.LatticePoint D.mesh)) (q : ℕ) (hfi : Γ.FiniteIndex)
    (hq : Γ.index = q)
    (hΓ : ∀ v ∈ Γ, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v))
    (hside : 2 * (g.enclosingCoarsening O).cellSide ≤ PeriodicLattice.torusSide D.L D.m)
    (t : ℝ) (ht : 0 < t)
    (ht' : t < (2 * observableSupNorm (ReflectionGrid.cellFamilyProduct O F) + 1)⁻¹) :
    t * ‖∫ U, ReflectionGrid.cellFamilyProduct O F U ∂ν‖ ≤
      t * g.chessboardNormProduct O F +
        (2 * (q : ℝ)) ^ 4 * ((Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          ((g.enclosingCoarsening O).cellSide / D.mesh) ^ 3 *
          ((g.enclosingCoarsening O).cellSide / PeriodicLattice.torusSide D.L D.m)) +
        t ^ 2 * observableSupNorm (ReflectionGrid.cellFamilyProduct O F) ^ 2 := by
  have hgibbs : InfiniteLattice.IsGibbs D.β ν := hν.1
  have : IsProbabilityMeasure ν := hgibbs.1
  have hq0 : q ≠ 0 := hq ▸ hfi.index_ne_zero
  obtain ⟨θ, hθ⟩ := exists_phase_mul_eq_norm (∫ U, ReflectionGrid.cellFamilyProduct O F U ∂ν)
  obtain ⟨⟨-, hmem, -, hlow⟩, hJ⟩ := hroot D g hg O hO F hF hside θ t ht ht'
  have hl := hlow ν inferInstance hθ
  generalize hcdef : g.enclosingCoarsening O = c at *
  have hcg : c.IsCoarse := by
    rw [← hcdef]
    exact ReflectionGrid.IsCoarse.coarsen hg _ _
  obtain ⟨-, hmove, hinvk, hblock⟩ := (htrans D ν hν).2 Γ q hfi hq hΓ c hcg
  obtain ⟨hsub, hfin, hcount⟩ := hblock D.m hside
  have hsub' : c.sparseCells q ⊆ c.cellsWithin c.fundamentalBlock := hsub
  have hfin' : (c.sparseCells q).Finite := hfin
  have hcount' : (c.cellsAcross / (2 * (q : ℝ))) ^ 4 ≤ ((c.sparseCells q).ncard : ℝ) := hcount
  have hJc := (hJ hfin'.toFinset (by simpa using hsub')).2.2 ν hgibbs
  have hterm : ∀ S ∈ hfin'.toFinset,
      ∫ U, (c.baseCellMover S).actOn (ReflectionGrid.logOnePlusRotated θ t O F) U ∂ν =
        ∫ U, ReflectionGrid.logOnePlusRotated θ t O F U ∂ν := by
    intro S hS
    obtain ⟨k, ⟨-, hk⟩, rfl⟩ := hfin'.mem_toFinset.mp hS
    obtain ⟨r, hr, -, huniq⟩ := hmove k hk
    have hmover : c.mover c.baseCell (c.cell k) = r :=
      (huniq _).mp (Classical.epsilon_spec
        (p := fun r' : c.reflectionGroup => r'.1 '' c.baseCell = c.cell k) ⟨r, (huniq r).mpr rfl⟩)
    have hsym : c.baseCellMover (c.cell k) = InfiniteLattice.shift (c.cellOffsetPoint k) := by
      show c.toLatticeSym (c.mover c.baseCell (c.cell k)) = _
      rw [hmover]
      exact toLatticeSym_eq_shift c r k hr
    have h := (hinvk k hk).2 (fun U => ((ReflectionGrid.logOnePlusRotated θ t O F U : ℝ) : ℂ))
      (isBoundedObservable_of_mem_cellObservables hmem)
    have e1 : ∫ U, (InfiniteLattice.shift (c.cellOffsetPoint k)).actOn
          (fun U => ((ReflectionGrid.logOnePlusRotated θ t O F U : ℝ) : ℂ)) U ∂ν =
        ((∫ U, (InfiniteLattice.shift (c.cellOffsetPoint k)).actOn
          (ReflectionGrid.logOnePlusRotated θ t O F) U ∂ν : ℝ) : ℂ) :=
      integral_ofReal
    have e2 : ∫ U, ((ReflectionGrid.logOnePlusRotated θ t O F U : ℝ) : ℂ) ∂ν =
        ((∫ U, ReflectionGrid.logOnePlusRotated θ t O F U ∂ν : ℝ) : ℂ) := integral_ofReal
    rw [e1, e2] at h
    rw [hsym]
    exact_mod_cast h
  rw [hcdef, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at hJc
  have hs : 0 < c.cellSide := c.cellSide_pos
  have hℓ : 0 < PeriodicLattice.torusSide D.L D.m := by linarith
  have hQ : (0 : ℝ) < 2 * (q : ℝ) := by
    have : 0 < q := Nat.pos_of_ne_zero hq0
    positivity
  have hN : (PeriodicLattice.torusSide D.L D.m / c.cellSide / (2 * (q : ℝ))) ^ 4 ≤
      ((hfin'.toFinset.card : ℕ) : ℝ) := by
    rw [← ncard_eq_toFinset_card _ hfin']
    exact hcount'
  have hC : (0 : ℝ) ≤ (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β :=
    mul_nonneg (Nat.cast_nonneg _) D.beta_pos.le
  have hH := le_add_of_mul_le_mul_add hC D.mesh_pos hs hℓ hQ hN
    (H := ∫ U, ReflectionGrid.logOnePlusRotated θ t O F U ∂ν)
    (x := t * g.chessboardNormProduct O F)
    (by linarith)
  linarith
theorem periodicGibbsBound_of_finiteIndex (hroot : GibbsBoundOnOneTorus.Statement)
    (htrans : PeriodicStatesAndGridTranslations.Statement) :
    PeriodicGibbsBoundOfFiniteIndex.Statement := by
  intro D g hg ν hν O hO F hF Γ q hfi hq hΓ m' hside t ht ht'
  exact bound_at_torusSide hroot htrans (D.withExponent m') (g.withExponent m') hg ν hν O hO F hF
    Γ q hfi hq hΓ hside t ht ht'
end PeriodicGibbsBoundOfFiniteIndexProof
end YangMills.Construction.ChessboardTori
end
