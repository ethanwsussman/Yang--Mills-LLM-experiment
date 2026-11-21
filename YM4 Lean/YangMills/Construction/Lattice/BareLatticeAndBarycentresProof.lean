import YangMills.Construction.Lattice.LatticeSymmetriesRectangularToriAndInducedSymmetries
import YangMills.Construction.Lattice.BareLatticeAndBarycentres
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PlaquetteSupports
noncomputable section
namespace YangMills.Construction.BareLattice
variable (s : Conventions.StandingParameters)
theorem blockFactor_pos : 0 < s.L := by
  have := s.isAdmissible.2
  omega
theorem latticeSpacing_pos : 0 < latticeSpacing s := by apply _root_.YangMills.Construction.Conventions.StandingParameters.latticeSpacing_pos <;> assumption
theorem sideDivSpacing_holds : SideDivSpacing s := by
  refine ⟨?_, Nat.mul_pos (by norm_num) (pow_pos (blockFactor_pos s) _)⟩
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide, latticeSpacing,
    PeriodicLattice.meshSize, latticePointsPerSide]
  push_cast
  rw [zpow_neg, div_inv_eq_mul, zpow_natCast, pow_add]
  ring
theorem sublattice_eq_image_at_cutoff (h : QuotientLattices.TorusAndSpaceLatticeProperties) :
    (PeriodicLattice.sublattice s.L s.m ((s.K : ℕ) : ℤ) : Set s.Torus) =
        TorusMetric.torusProj (PeriodicLattice.torusSide s.L s.m) ''
          (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) :
            Set (Fin 4 → ℝ)) ∧
      Finite (LatticeSite s) := by
  have hq := (h s.L s.isAdmissible s.m 0 s.K s.m.pos (Nat.zero_le _)).2.1
  have hidx : QuotientLattices.refinementIndex (s.K : ℕ) 0 = ((s.K : ℕ) : ℤ) := by
    simp [QuotientLattices.refinementIndex]
  unfold QuotientLattices.IsQuotientLattice at hq
  rw [hidx] at hq
  obtain ⟨-, -, -, -, -, -, -, himg, -, -, hfin, -, -⟩ := hq
  exact ⟨himg, hfin⟩
theorem latticeDescriptions_holds (h : QuotientLattices.TorusAndSpaceLatticeProperties) :
    LatticeDescriptions s := by
  refine ⟨?_, (sublattice_eq_image_at_cutoff s h).1⟩
  ext x
  constructor
  · rintro ⟨k, hk⟩
    refine (AddSubgroup.mem_pi _).2 fun μ _ => AddSubgroup.mem_zmultiples_iff.2 ⟨k μ, ?_⟩
    rw [hk μ, ← zsmul_eq_mul]
    rfl
  · intro hx
    have hmem := fun μ => AddSubgroup.mem_zmultiples_iff.1 ((AddSubgroup.mem_pi _).1 hx μ (mem_univ _))
    choose k hk using hmem
    refine ⟨k, fun μ => ?_⟩
    rw [← hk μ, ← zsmul_eq_mul]
    rfl
variable {s}
theorem barycenterFormula_holds : BarycenterFormula s := by
  rintro y ⟨⟨μ, ν⟩, hμν⟩
  have hne : μ ≠ ν := ne_of_lt hμν
  simp only [PeriodicLattice.Plaquette.barycenter, plaquetteOf, planeDiagonal,
    PeriodicLattice.pointOnAxis, PlaquetteSupports.latticeSpacing]
  funext i
  simp only [Pi.add_apply, TorusMetric.torusProj, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i = μ
  · subst hi
    simp [hne]
  · by_cases hj : i = ν
    · subst hj
      simp [hi]
    · simp [hi, hj]
theorem plaquetteOf_injective (y : LatticeSite s) : Function.Injective (plaquetteOf y) := by
  rintro ⟨⟨μ, ν⟩, hμν⟩ ⟨⟨μ', ν'⟩, hμν'⟩ heq
  simp only [plaquetteOf, PeriodicLattice.Plaquette.mk.injEq, true_and] at heq
  exact Subtype.ext (Prod.ext heq.1 heq.2)
theorem sixPlaquettesPerSite_holds : SixPlaquettesPerSite s := by
  intro y
  refine ⟨?_, fun q => ⟨plaquetteOf y q, ⟨rfl, rfl⟩, ?_⟩⟩
  · have hset : {p : LatticePlaquette s | p.origin = y} = range (plaquetteOf y) := by
      ext p
      constructor
      · intro hp
        exact ⟨⟨(p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩,
          PeriodicLattice.Plaquette.ext hp.symm rfl rfl⟩
      · rintro ⟨q, rfl⟩
        rfl
    rw [hset, ← image_univ, ncard_image_of_injective _ (plaquetteOf_injective y), ncard_univ,
      Nat.card_eq_fintype_card]
    decide
  · rintro p ⟨horig, haxes⟩
    have h1 : p.firstAxis = q.1.1 := congrArg Prod.fst haxes
    have h2 : p.secondAxis = q.1.2 := congrArg Prod.snd haxes
    exact PeriodicLattice.Plaquette.ext horig h1 h2
theorem plaquetteSumDecomposition_holds (h : QuotientLattices.TorusAndSpaceLatticeProperties) :
    PlaquetteSumDecomposition s := by
  intro φ
  have : Finite (LatticeSite s) := (sublattice_eq_image_at_cutoff s h).2
  let : Fintype (LatticeSite s) := Fintype.ofFinite _
  let e : AxisPair × LatticeSite s ≃ LatticePlaquette s :=
    { toFun := fun x => plaquetteOf x.2 x.1
      invFun := fun p => (⟨(p.firstAxis, p.secondAxis), p.firstAxis_lt_secondAxis⟩, p.origin)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype (LatticePlaquette s) := Fintype.ofEquiv _ e
  rw [finsum_eq_sum_of_fintype]
  simp_rw [finsum_eq_sum_of_fintype]
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  rfl
theorem bareLatticeProperties_holds (h : QuotientLattices.TorusAndSpaceLatticeProperties) :
    BareLatticeProperties := fun s =>
  ⟨latticeSpacing_pos s, sideDivSpacing_holds s, latticeDescriptions_holds s h,
    barycenterFormula_holds, sixPlaquettesPerSite_holds, plaquetteSumDecomposition_holds h⟩
end YangMills.Construction.BareLattice
