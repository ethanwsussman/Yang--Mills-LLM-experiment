import YangMills.Construction.Lattice.ConstantSequenceAsADatumOfTheSetting
import YangMills.Construction.Lattice.IdentitiesOfTheDirichletOperators
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegionsProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.Lattice.BlocksCorridorsPivotBondsAndTheWeightsOfTheOneStepAverage
import YangMills.Construction.Lattice.BondEnergyCurlAverageBound
import YangMills.Construction.Torus.ScalarProductsTransposesAndProjectionsOfASetting
import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTrees
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric
namespace SeparatedClasses.ParametrizedLowerBound
open SingleSequence SingleSequence.SequenceData GeneralTorus.GaugeSetting
section Torus
variable {ℓ : Fin 4 → ℝ} {S : ℝ}
def torusProjHom (S : ℝ) : (Fin 4 → ℝ) →+ Torus4 S where
  toFun := torusProj S
  map_zero' := by funext μ; simp [torusProj]
  map_add' u v := by funext μ; simp [torusProj]
theorem periodLattice_le_ker (h : ∀ μ, ℓ μ = S) : Lattice.periodLattice ℓ ≤ (torusProjHom S).ker := by
  intro v hv
  rw [AddMonoidHom.mem_ker]
  funext μ
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hv μ (Set.mem_univ μ))
  show ((v μ : ℝ) : AddCircle S) = 0
  rw [← hk, h μ]
  exact (AddCircle.coe_eq_zero_iff S).2 ⟨k, rfl⟩
def toSideTorus (h : ∀ μ, ℓ μ = S) : Lattice.PeriodicTorus ℓ →+ Torus4 S :=
  QuotientAddGroup.lift (Lattice.periodLattice ℓ) (torusProjHom S) (periodLattice_le_ker h)
theorem toSideTorus_mk (h : ∀ μ, ℓ μ = S) (v : Fin 4 → ℝ) :
    toSideTorus h (Lattice.torusMk ℓ v) = torusProj S v := rfl
theorem toSideTorus_injective (h : ∀ μ, ℓ μ = S) : Function.Injective (toSideTorus h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨v, rfl⟩ := Lattice.torusMk_surjective ℓ x
  rw [toSideTorus_mk] at hx
  have h1 : Lattice.torusMk ℓ v = Lattice.torusMk ℓ 0 := by
    rw [Lattice.torusMk_eq_torusMk_iff, sub_zero]
    refine (AddSubgroup.mem_pi _).mpr fun μ _ => ?_
    have h0 := congrFun hx μ
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [h μ]; exact hk⟩
  simpa using h1
theorem toSideTorus_mem_iff (h : ∀ μ, ℓ μ = S) (ε : ℝ) (x : Lattice.PeriodicTorus ℓ) :
    x ∈ Lattice.latticeSubgroup ℓ ε ↔ toSideTorus h x ∈ GeneralTorus.spacingLattice S ε := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hm : ∀ μ, ∃ k : ℤ, k • ε = u μ := fun μ =>
      AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hu μ (Set.mem_univ μ))
    choose k hk using hm
    refine ⟨k, ?_⟩
    show torusProj S u = _
    congr 1
    funext μ
    rw [← hk μ, zsmul_eq_mul, mul_comm]
  · rintro ⟨k, hk⟩
    have h1 : x = Lattice.torusMk ℓ fun μ => ε * (k μ : ℝ) := by
      apply toSideTorus_injective h
      rw [hk, toSideTorus_mk]
    rw [h1]
    refine AddSubgroup.mem_map_of_mem _ ((AddSubgroup.mem_pi _).mpr fun μ _ =>
      AddSubgroup.mem_zmultiples_iff.mpr ⟨k μ, ?_⟩)
    rw [zsmul_eq_mul, mul_comm]
end Torus
section Sites
variable {ℓ : Fin 4 → ℝ} {S : ℝ}
end Sites
section Blocks
variable (C : ClassData) {S : ℝ}
theorem blockOffset_eq_half : ∃ o : ℕ, C.L = 2 * o + 1 ∧ BlockSpin.blockOffset C.centeredBlockParams 1 = o := by
  obtain ⟨o, ho⟩ := C.isAdmissible.1
  refine ⟨o, ho, ?_⟩
  have h1 := BlockSpin.blockOffset_mul C.centeredBlockParams 1
  have h2 : C.centeredBlockParams.offset = o := by
    show (C.L - 1) / 2 = o
    omega
  have h3 : C.centeredBlockParams.L = C.L := rfl
  rw [h2, h3, pow_one] at h1
  have h4 : 0 < C.L - 1 := by
    have := C.isAdmissible.2
    omega
  exact Nat.eq_of_mul_eq_mul_right h4 h1
theorem norm_intCast_le {o : ℕ} {S : ℝ} (hS : 0 < S) (ho : 2 * (o : ℝ) ≤ S) {k : ℤ}
    (hk : |(k : ℝ)| ≤ o) : ‖((k : ℝ) : AddCircle S)‖ ≤ o := by
  have h1 : ‖((k : ℝ) : AddCircle S)‖ = |(k : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff S hS.ne').2 (by
      rw [abs_of_pos hS]
      linarith)
  rw [h1]
  exact hk
variable {C}
theorem mem_blockOf_iff {n : ℕ} (h : ∀ μ, C.levelPeriods n μ = S) {N : ℕ} (hN : S = (N : ℝ))
    (hLS : 2 * (C.L : ℝ) ≤ S) {ε' : ℝ}
    (y : Lattice.LatticeSite (C.levelPeriods n) ε')
    (hy : (y : Lattice.PeriodicTorus (C.levelPeriods n)) ∈ Lattice.latticeSubgroup (C.levelPeriods n) 1)
    (x : Lattice.LatticeSite (C.levelPeriods n) 1) :
    x ∈ BlockSpin.blockOf C.centeredBlockParams 1 1 y ↔
      ∀ ν, ‖(toSideTorus h (x : Lattice.PeriodicTorus (C.levelPeriods n)) -
        toSideTorus h (y : Lattice.PeriodicTorus (C.levelPeriods n))) ν‖ ≤ ((C.L : ℝ) - 1) / 2 := by
  obtain ⟨o, hLo, hoff⟩ := blockOffset_eq_half C
  have hLr : (C.L : ℝ) = 2 * (o : ℝ) + 1 := by exact_mod_cast hLo
  have hhalf : ((C.L : ℝ) - 1) / 2 = o := by rw [hLr]; ring
  have hLpos : (0 : ℝ) < C.L := by rw [hLr]; positivity
  have hSpos : 0 < S := by linarith
  rw [hhalf]
  constructor
  · rintro ⟨σ, hσ, hx⟩ ν
    have h1 : toSideTorus h (x : Lattice.PeriodicTorus (C.levelPeriods n)) -
        toSideTorus h (y : Lattice.PeriodicTorus (C.levelPeriods n)) = torusProj S fun μ => (σ μ : ℝ) * 1 := by
      rw [hx, map_add, add_sub_cancel_left]
      rfl
    rw [h1]
    have h2 := hσ ν
    rw [hoff] at h2
    have h3 : (C.centeredBlockParams.L : ℤ) ^ 1 - 1 - (o : ℤ) = o := by
      show (C.L : ℤ) ^ 1 - 1 - (o : ℤ) = o
      rw [hLo]
      push_cast
      ring
    rw [h3] at h2
    have h4 : |((σ ν : ℤ) : ℝ)| ≤ o := by
      rw [abs_le]
      exact_mod_cast h2
    have h5 : torusProj S (fun μ => (σ μ : ℝ) * 1) ν = (((σ ν : ℤ) : ℝ) : AddCircle S) := by
      simp [torusProj]
    rw [h5]
    exact norm_intCast_le hSpos (by linarith) h4
  · intro hx
    have hxy : (x : Lattice.PeriodicTorus (C.levelPeriods n)) - y ∈
        Lattice.latticeSubgroup (C.levelPeriods n) 1 := sub_mem x.2 hy
    obtain ⟨k, hk⟩ := (toSideTorus_mem_iff h 1 _).1 hxy
    rw [map_sub] at hk
    have hround : ∀ ν, ∃ σ : ℤ, (σ : ℝ) = (k ν : ℝ) - round (S⁻¹ * (k ν : ℝ)) * S := by
      intro ν
      exact ⟨k ν - round (S⁻¹ * (k ν : ℝ)) * N, by rw [hN]; push_cast; ring⟩
    choose σ hσ using hround
    have hcoord : ∀ ν, (toSideTorus h (x : Lattice.PeriodicTorus (C.levelPeriods n)) -
        toSideTorus h (y : Lattice.PeriodicTorus (C.levelPeriods n))) ν = (((k ν : ℤ) : ℝ) : AddCircle S) := by
      intro ν
      rw [hk]
      simp [torusProj]
    have hnorm : ∀ ν, |((σ ν : ℤ) : ℝ)| ≤ o := by
      intro ν
      have h1 := hx ν
      rw [hcoord ν, AddCircle.norm_eq] at h1
      rw [hσ ν]
      exact h1
    refine ⟨σ, ?_, ?_⟩
    · intro μ
      rw [hoff]
      have h3 : (C.centeredBlockParams.L : ℤ) ^ 1 - 1 - (o : ℤ) = o := by
        show (C.L : ℤ) ^ 1 - 1 - (o : ℤ) = o
        rw [hLo]
        push_cast
        ring
      rw [h3]
      have h4 := abs_le.1 (hnorm μ)
      constructor
      · exact_mod_cast h4.1
      · exact_mod_cast h4.2
    · apply toSideTorus_injective h
      rw [map_add]
      have h5 : toSideTorus h (BlockSpin.gridPoint (C.levelPeriods n) 1 σ : Lattice.PeriodicTorus (C.levelPeriods n)) =
          toSideTorus h (x : Lattice.PeriodicTorus (C.levelPeriods n)) -
            toSideTorus h (y : Lattice.PeriodicTorus (C.levelPeriods n)) := by
        funext ν
        rw [hcoord ν]
        show (((σ ν : ℝ) * 1 : ℝ) : AddCircle S) = _
        rw [mul_one, hσ ν, sub_eq_add_neg, AddCircle.coe_add]
        have h6 : (((-(((round (S⁻¹ * (k ν : ℝ)) : ℤ) : ℝ) * S)) : ℝ) : AddCircle S) = 0 :=
          (AddCircle.coe_eq_zero_iff S).2 ⟨-round (S⁻¹ * (k ν : ℝ)), by simp⟩
        rw [h6, add_zero]
      rw [h5]
      abel
end Blocks
section LastLattice
variable {C : ClassData} [hP : BlockSpin.PeriodsMultipleOfBlock C.centeredBlockParams (C.levelPeriods C.t)]
  {D : GeneralTorus.ScaleData} (h : ∀ μ, C.levelPeriods C.t μ = D.torusSide) (unit : D.levelSpacing D.lastLevel = 1)
  (mult : GeneralTorus.IsEvenMultipleOf D.torusSide (D.L : ℝ))
def unitPoint (x : (UnitSpacingLattice.torusLevel D unit mult).Point) : D.Space :=
  ((show D.SiteAt D.lastLevel from x) : D.Space)
end LastLattice
section EvaluationMaps
variable (s : SequenceData)
theorem torusSide_pos : 0 < PeriodicLattice.torusSide s.data.L s.data.m := by
  have h := s.data.isAdmissible.2
  simp only [PeriodicLattice.torusSide]
  positivity
theorem toTorus_eq {S : ℝ} (hS : S ≠ 0) (x : s.data.Point) :
    s.toTorus S x = fun μ => AddCircle.equivAddCircle _ S s.torusSide_ne_zero hS (x μ) :=
  dif_pos hS
theorem toTorus_coe {S : ℝ} (hS : S ≠ 0) (v : Fin 4 → ℝ) :
    s.toTorus S (fun μ => (v μ : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m))) =
      torusProj S fun μ => v μ * ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * S) := by
  rw [toTorus_eq s hS]
  funext μ
  exact AddCircle.equivAddCircle_apply_mk _ _ _ _ (v μ)
theorem toTorus_sub {S : ℝ} (hS : S ≠ 0) (a b : s.data.Point) :
    s.toTorus S (a - b) = s.toTorus S a - s.toTorus S b := by apply _root_.YangMills.Construction.SeparatedClasses.ScalarCorrespondence.toTorus_sub <;> assumption
theorem exists_real_lift (p : s.data.Point) :
    ∃ v : Fin 4 → ℝ, p = fun μ => (v μ : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) := by
  have h1 : ∀ μ, ∃ r : ℝ, (r : AddCircle (PeriodicLattice.torusSide s.data.L s.data.m)) = p μ :=
    fun μ => QuotientAddGroup.mk_surjective (p μ)
  choose v hv using h1
  exact ⟨v, funext fun μ => (hv μ).symm⟩
theorem torusSide_inv_mul_eq :
    (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ *
        (2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + s.data.cutoff - s.data.t)) =
      (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) := by
  have h := s.data.isAdmissible.2
  have ht : s.data.t ≤ s.data.cutoff := s.data.t_le_cutoff
  have hpow : (s.data.L : ℝ) ^ ((s.data.m : ℕ) + s.data.cutoff - s.data.t) =
      (s.data.L : ℝ) ^ (s.data.m : ℕ) * (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [PeriodicLattice.torusSide]
  rw [hpow]
  field_simp
theorem isLevelLift_iff {S : ℝ} (h : ∀ μ, s.data.levelPeriods s.data.t μ = S) (p : s.data.Point)
    (x : Lattice.PeriodicTorus (s.data.levelPeriods s.data.t)) :
    s.data.IsLevelLift s.data.t p x ↔ s.toTorus S p = toSideTorus h x := by
  have hSf : S = 2 * (s.data.L : ℝ) ^ ((s.data.m : ℕ) + s.data.cutoff - s.data.t) :=
    (h (0 : Fin 4)).symm
  have hS : S ≠ 0 := by
    have := s.data.isAdmissible.2
    have hL : (s.data.L : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.data.L ≠ 0)
    rw [hSf]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hL)
  have hr : (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * S =
      (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) := by
    rw [hSf]; exact torusSide_inv_mul_eq s
  constructor
  · rintro ⟨v, rfl, rfl⟩
    rw [toTorus_coe s hS, toSideTorus_mk, hr]
    congr 1
    funext μ
    rw [mul_comm]
  · intro hx
    obtain ⟨v, rfl⟩ := exists_real_lift s p
    refine ⟨v, rfl, ?_⟩
    apply toSideTorus_injective h
    rw [← hx, toTorus_coe s hS, toSideTorus_mk, hr]
    congr 1
    funext μ
    rw [mul_comm]
end EvaluationMaps
section SeriesExpansions
variable (s : SequenceData) {W : GeneralTorus.GaugeSetting} (hW : s.IsGaugeSetting W)
variable {s}
variable (h : ∀ μ, s.data.levelPeriods s.data.t μ = W.data.torusSide)
variable [hP : BlockSpin.PeriodsMultipleOfBlock s.data.centeredBlockParams
  (s.data.levelPeriods s.data.t)]
variable (unit : W.data.levelSpacing W.data.lastLevel = 1)
  (mult : GeneralTorus.IsEvenMultipleOf W.data.torusSide (W.data.L : ℝ))
end SeriesExpansions
section Geometry
variable {s : SequenceData} {W : GeneralTorus.GaugeSetting} (hW : s.IsGaugeSetting W)
  (h : ∀ μ, s.data.levelPeriods s.data.t μ = W.data.torusSide)
  [hP : BlockSpin.PeriodsMultipleOfBlock s.data.centeredBlockParams (s.data.levelPeriods s.data.t)]
  {Θ' : Set (Lattice.LatticeSite (s.data.levelPeriods s.data.t) (s.data.L : ℝ))}
  (hΘ : ClassData.IsInteriorBlockSet s.Ω Θ')
end Geometry
section Norms
variable {s : SequenceData} {W : GeneralTorus.GaugeSetting} (hW : s.IsGaugeSetting W)
  (h : ∀ μ, s.data.levelPeriods s.data.t μ = W.data.torusSide)
  [hP : BlockSpin.PeriodsMultipleOfBlock s.data.centeredBlockParams (s.data.levelPeriods s.data.t)]
  (unit : W.data.levelSpacing W.data.lastLevel = 1)
  (mult : GeneralTorus.IsEvenMultipleOf W.data.torusSide (W.data.L : ℝ))
end Norms
section Final
variable {s : OperatorSetting}
end Final
end SeparatedClasses.ParametrizedLowerBound
end YangMills.Construction
end
