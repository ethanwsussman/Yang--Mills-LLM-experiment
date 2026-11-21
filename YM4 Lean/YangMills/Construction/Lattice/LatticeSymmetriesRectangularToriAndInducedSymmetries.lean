import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
open BoxTorus (projection basisVector)
noncomputable section
namespace Conventions.StandingParameters
variable (s : StandingParameters)
abbrev cutoffLevel : ℤ := ((s.K : ℕ) : ℤ)
abbrev latticeSpacing : ℝ := PeriodicLattice.meshSize s.L s.cutoffLevel
theorem thirteen_le_L : (13 : ℝ) ≤ s.L := by
  exact_mod_cast s.isAdmissible.2
theorem latticeSpacing_pos : 0 < s.latticeSpacing :=
  zpow_pos (by linarith [s.thirteen_le_L]) _
theorem pow_eq_mul_latticeSpacing (e : ℕ) :
    (s.L : ℝ) ^ e = ((s.L ^ (e + (s.K : ℕ)) : ℕ) : ℝ) * s.latticeSpacing := by
  have hL : (s.L : ℝ) ≠ 0 := by linarith [s.thirteen_le_L]
  simp only [latticeSpacing, PeriodicLattice.meshSize, cutoffLevel, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem L_le_pow (e : ℕ) : s.L ≤ s.L ^ (e + (s.K : ℕ)) :=
  Nat.le_self_pow (by have := s.K.pos; omega) _
theorem latticeSpacing_le : s.latticeSpacing ≤ 1 / 13 := by
  have h := s.pow_eq_mul_latticeSpacing 0
  have h1 : (s.L : ℝ) ≤ ((s.L ^ (0 + (s.K : ℕ)) : ℕ) : ℝ) := by
    exact_mod_cast s.L_le_pow 0
  have h2 := s.thirteen_le_L
  have h3 := s.latticeSpacing_pos
  rw [pow_zero] at h
  nlinarith
end Conventions.StandingParameters
structure BoxShape (s : Conventions.StandingParameters) where
  cellPower : ℕ
  cellCounts : Fin 4 → ℕ
  cellCounts_pos : ∀ μ, 0 < cellCounts μ
  cellCounts_even : ∀ μ, Even (cellCounts μ)
namespace BoxShape
variable {s : Conventions.StandingParameters} (D : BoxShape s)
def cellSize : ℝ := (s.L : ℝ) ^ D.cellPower
theorem one_le_cellSize : 1 ≤ D.cellSize :=
  one_le_pow₀ (by linarith [s.thirteen_le_L])
variable (s) in
def centreShift : Fin 4 → ℝ := fun _ => -(s.latticeSpacing / 2)
def toCellGrid : CellGrid s.L s.cutoffLevel where
  admissible := s.isAdmissible
  cellLength := D.cellSize
  cellLength_pos := by linarith [D.one_le_cellSize]
  cellLength_div_meshSize := ⟨((s.L ^ (D.cellPower + (s.K : ℕ)) : ℕ) : ℤ), by
    have h := s.latticeSpacing_pos
    rw [cellSize, s.pow_eq_mul_latticeSpacing]
    push_cast
    field_simp⟩
  counts := D.cellCounts
  counts_pos := D.cellCounts_pos
  counts_even := D.cellCounts_even
  four_meshSize_le μ := by
    have h1 := s.latticeSpacing_le
    have h2 := D.one_le_cellSize
    have h3 : (2 : ℝ) ≤ D.cellCounts μ := by
      obtain ⟨c, hc⟩ := D.cellCounts_even μ
      have := D.cellCounts_pos μ
      exact_mod_cast (by omega : 2 ≤ D.cellCounts μ)
    nlinarith
  centre := centreShift s
  centre_mem μ := ⟨-1, by
    simp only [centreShift]
    push_cast
    ring⟩
end BoxShape
inductive TorusShape (s : Conventions.StandingParameters)
  | cubic (m : ℕ) (hm : 0 < m)
  | box (D : BoxShape s)
namespace TorusShape
variable {s : Conventions.StandingParameters} (T : TorusShape s)
def sideLengths : TorusShape s → Fin 4 → ℝ
  | cubic m _ => fun _ => PeriodicLattice.torusSide s.L m
  | box D => D.toCellGrid.sideLengths
abbrev Carrier : Type := BoxTorus.Space T.sideLengths
def cover : AmbientSpace →+ T.Carrier := projection T.sideLengths
theorem exists_sideLengths_eq_mul (μ : Fin 4) :
    ∃ N : ℕ, Even N ∧ 2 * s.L ≤ N ∧ T.sideLengths μ = N * s.latticeSpacing := by
  cases T with
  | cubic m hm =>
    refine ⟨2 * s.L ^ (m + (s.K : ℕ)), even_two_mul _,
      Nat.mul_le_mul_left 2 (s.L_le_pow m), ?_⟩
    show PeriodicLattice.torusSide s.L m = _
    rw [PeriodicLattice.torusSide, s.pow_eq_mul_latticeSpacing]
    push_cast
    ring
  | box D =>
    have h2 : 2 ≤ D.cellCounts μ := by
      obtain ⟨c, hc⟩ := D.cellCounts_even μ
      have := D.cellCounts_pos μ
      omega
    refine ⟨D.cellCounts μ * s.L ^ (D.cellPower + (s.K : ℕ)), (D.cellCounts_even μ).mul_right _,
      Nat.mul_le_mul h2 (s.L_le_pow _), ?_⟩
    show (D.cellCounts μ : ℝ) * D.cellSize = _
    rw [BoxShape.cellSize, s.pow_eq_mul_latticeSpacing]
    push_cast
    ring
theorem sideLengths_lower_bound (μ : Fin 4) :
    2 * (s.L : ℝ) * s.latticeSpacing ≤ T.sideLengths μ ∧
      26 * s.latticeSpacing ≤ 2 * (s.L : ℝ) * s.latticeSpacing := by
  obtain ⟨N, -, hN, h⟩ := T.exists_sideLengths_eq_mul μ
  have ha := s.latticeSpacing_pos
  have hL := s.thirteen_le_L
  have hN' : 2 * (s.L : ℝ) ≤ N := by exact_mod_cast hN
  rw [h]
  constructor <;> nlinarith
theorem sideLengths_pos (μ : Fin 4) : 0 < T.sideLengths μ := by
  have ha := s.latticeSpacing_pos
  linarith [(T.sideLengths_lower_bound μ).1, (T.sideLengths_lower_bound μ).2]
def shortSteps (s : Conventions.StandingParameters) : Set AmbientSpace :=
  {v | v = 0 ∨ ∃ (μ : Fin 4) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧
    v = (σ * s.latticeSpacing) • basisVector μ}
theorem abs_apply_le_of_mem_shortSteps {v : AmbientSpace} (hv : v ∈ shortSteps s) (ν : Fin 4) :
    |v ν| ≤ s.latticeSpacing := by
  have ha := s.latticeSpacing_pos
  rcases hv with rfl | ⟨μ, σ, hσ, rfl⟩
  · simp [ha.le]
  · by_cases h : ν = μ
    · subst h
      rcases hσ with rfl | rfl <;> simp [basisVector, abs_of_pos ha]
    · simp [basisVector, Pi.single_eq_of_ne h, ha.le]
theorem cover_injOn_shortSteps : InjOn T.cover (shortSteps s) := by
  intro v hv w hw h
  have hk : v - w ∈ (projection T.sideLengths).ker := by
    rw [AddMonoidHom.mem_ker, map_sub]
    exact sub_eq_zero.mpr h
  rw [BoxTorus.projection_ker] at hk
  funext μ
  obtain ⟨k, hk⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hk μ (mem_univ μ))
  have hb : |(v - w) μ| ≤ 2 * s.latticeSpacing := by
    have h1 := abs_apply_le_of_mem_shortSteps hv μ
    have h2 := abs_apply_le_of_mem_shortSteps hw μ
    rw [Pi.sub_apply]
    calc |v μ - w μ| ≤ |v μ| + |w μ| := abs_sub _ _
      _ ≤ _ := by linarith
  have hp := T.sideLengths_pos μ
  have hl := (T.sideLengths_lower_bound μ)
  have ha := s.latticeSpacing_pos
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos hp] at hb
    nlinarith [hl.1, hl.2]
  rw [hk0, zero_smul] at hk
  exact sub_eq_zero.mp hk.symm
def cubicCover (s : Conventions.StandingParameters) (m : ℕ) (hm : 0 < m) :
    AmbientSpace →+ PeriodicLattice.FourTorus s.L m :=
  (cubic m hm : TorusShape s).cover
theorem pointOnAxis_eq_cubicCover (m : ℕ) (hm : 0 < m) (μ : Fin 4) (t : ℝ) :
    PeriodicLattice.pointOnAxis s.L m μ t = cubicCover s m hm (t • basisVector μ) := by
  funext ν
  show (Pi.single μ (t : AddCircle (PeriodicLattice.torusSide s.L m)) :
    PeriodicLattice.FourTorus s.L m) ν =
      (((t • basisVector μ) ν : ℝ) : AddCircle (PeriodicLattice.torusSide s.L m))
  by_cases h : ν = μ
  · subst h
    simp [basisVector]
  · simp [basisVector, Pi.single_eq_of_ne h]
theorem unitStep_eq_cubicCover (m : ℕ) (hm : 0 < m) (μ : Fin 4) :
    ((PeriodicLattice.unitStep s.L m s.cutoffLevel μ : PeriodicLattice.Site s.L m s.cutoffLevel) :
      PeriodicLattice.FourTorus s.L m) = cubicCover s m hm (s.latticeSpacing • basisVector μ) :=
  pointOnAxis_eq_cubicCover (s := s) m hm μ _
theorem isPositivelyOriented_or_opposite (m : ℕ) (b : PeriodicLattice.Bond s.L m s.cutoffLevel) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · exact Or.inr ⟨μ, show b.source - b.target = _ by rw [← neg_sub, h, neg_neg]⟩
theorem not_isPositivelyOriented_opposite (m : ℕ) (hm : 0 < m)
    (b : PeriodicLattice.Bond s.L m s.cutoffLevel) (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨ν', e₂⟩
  obtain ⟨ν, e₁⟩ := h
  have ha := s.latticeSpacing_pos
  have e₃ : PeriodicLattice.unitStep s.L m s.cutoffLevel ν =
      -PeriodicLattice.unitStep s.L m s.cutoffLevel ν' := by
    have e₂' : b.source - b.target = PeriodicLattice.unitStep s.L m s.cutoffLevel ν' := e₂
    rw [← e₂', ← e₁]
    abel
  have e₄ := congrArg Subtype.val e₃
  rw [NegMemClass.coe_neg, unitStep_eq_cubicCover (s := s) m hm,
    unitStep_eq_cubicCover (s := s) m hm, ← map_neg] at e₄
  have e₅ : s.latticeSpacing • (basisVector ν : AmbientSpace) =
      -(s.latticeSpacing • basisVector ν') :=
    (cubic m hm).cover_injOn_shortSteps (Or.inr ⟨ν, 1, Or.inl rfl, by simp⟩)
      (Or.inr ⟨ν', -1, Or.inr rfl, by simp⟩) e₄
  have e₆ := congrFun e₅ ν
  by_cases hν : ν = ν'
  · subst hν
    simp [basisVector] at e₆
    linarith
  · simp [basisVector, Pi.single_eq_of_ne hν] at e₆
    linarith
theorem gaugeFieldOfPositive_mem (m : ℕ) (hm : 0 < m)
    (v : PeriodicLattice.PositivelyOrientedBond s.L m s.cutoffLevel →
      Matrices.ComplexMatrix2.specialUnitary) :
    PeriodicLattice.gaugeFieldOfPositive v ∈
      PeriodicLattice.compactGaugeFields s.L m s.cutoffLevel := by
  have hpos : ∀ (b : PeriodicLattice.Bond s.L m s.cutoffLevel) (h : b.IsPositivelyOriented),
      PeriodicLattice.gaugeFieldOfPositive v b = (v ⟨b, h⟩ : Matrices.ComplexMatrix2) :=
    fun b h => dif_pos h
  have hneg : ∀ (b : PeriodicLattice.Bond s.L m s.cutoffLevel) (_ : ¬ b.IsPositivelyOriented)
      (h' : b.opposite.IsPositivelyOriented),
      PeriodicLattice.gaugeFieldOfPositive v b =
        ((v ⟨b.opposite, h'⟩ : Matrices.ComplexMatrix2))⁻¹ :=
    fun b h h' => by rw [PeriodicLattice.gaugeFieldOfPositive, dif_neg h, dif_pos h']
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases h : b.IsPositivelyOriented
    · rw [hpos b h]
      exact (v _).2
    · have h' := (isPositivelyOriented_or_opposite m b).resolve_left h
      rw [hneg b h h', ← InfiniteLattice.specialUnitary_coe_inv]
      exact ((v ⟨b.opposite, h'⟩)⁻¹).2
  · by_cases h : b.IsPositivelyOriented
    · have hr := not_isPositivelyOriented_opposite m hm b h
      have hrr : b.opposite.opposite.IsPositivelyOriented := h
      exact (hneg b.opposite hr hrr).trans (congrArg (·⁻¹) (hpos b h).symm)
    · have h' := (isPositivelyOriented_or_opposite m b).resolve_left h
      rw [hpos b.opposite h', hneg b h h', ← InfiniteLattice.specialUnitary_coe_inv,
        ← InfiniteLattice.specialUnitary_coe_inv, inv_inv]
theorem continuous_gaugeFieldOfPositive (m : ℕ) :
    Continuous (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond s.L m s.cutoffLevel →
        Matrices.ComplexMatrix2.specialUnitary) → _) := by
  refine continuous_pi fun b => ?_
  by_cases h : b.IsPositivelyOriented
  · have e : (fun v : PeriodicLattice.PositivelyOrientedBond s.L m s.cutoffLevel →
          Matrices.ComplexMatrix2.specialUnitary =>
        PeriodicLattice.gaugeFieldOfPositive v b) =
        fun v => ((v ⟨b, h⟩ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) :=
      funext fun v => dif_pos h
    rw [e]
    exact continuous_subtype_val.comp (continuous_apply _)
  · by_cases h' : b.opposite.IsPositivelyOriented
    · have e : (fun v : PeriodicLattice.PositivelyOrientedBond s.L m s.cutoffLevel →
            Matrices.ComplexMatrix2.specialUnitary =>
          PeriodicLattice.gaugeFieldOfPositive v b) =
          fun v => (((v ⟨b.opposite, h'⟩)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2) :=
        funext fun v => by
          rw [PeriodicLattice.gaugeFieldOfPositive, dif_neg h, dif_pos h',
            InfiniteLattice.specialUnitary_coe_inv]
      rw [e]
      exact continuous_subtype_val.comp (continuous_apply _).inv
    · have e : (fun v : PeriodicLattice.PositivelyOrientedBond s.L m s.cutoffLevel →
            Matrices.ComplexMatrix2.specialUnitary =>
          PeriodicLattice.gaugeFieldOfPositive v b) = fun _ => 1 :=
        funext fun v => by rw [PeriodicLattice.gaugeFieldOfPositive, dif_neg h, dif_neg h']
      rw [e]
      exact continuous_const
end TorusShape
end
end YangMills.Construction
