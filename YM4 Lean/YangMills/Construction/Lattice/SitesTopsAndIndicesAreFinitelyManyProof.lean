import YangMills.Construction.Lattice.CommutationOfTheDifferenceWithTheLaplaciansProof
import YangMills.Construction.Lattice.SitesTopsAndIndicesAreFinitelyMany
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences Matrices
namespace SeparatedRegions.Counting
variable {L m : ℕ}
theorem pointsPerAxis_mul_meshSize (hL : 0 < L) (m d : ℕ) :
    ((2 * L ^ (m + d) : ℕ) : ℝ) * meshSize L (d : ℤ) = torusSide L m := by
  simp only [meshSize, torusSide, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
def siteOfResidues (m d N : ℕ) (c : Fin 4 → ZMod N) : Site L m (d : ℤ) :=
  ⟨fun μ => (((c μ).val : ℝ) * meshSize L (d : ℤ) : ℝ),
    ⟨fun μ => ((c μ).val : ℤ), fun μ => by simp⟩⟩
theorem siteOfResidues_bijective (hL : 0 < L) (m d : ℕ) :
    Function.Bijective (siteOfResidues (L := L) m d (2 * L ^ (m + d))) := by
  set N : ℕ := 2 * L ^ (m + d) with hNdef
  have hN : 0 < N := by positivity
  have : NeZero N := ⟨hN.ne'⟩
  have hside : (N : ℝ) * meshSize L (d : ℤ) = torusSide L m := pointsPerAxis_mul_meshSize hL m d
  have hs : meshSize L (d : ℤ) ≠ 0 := by
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    exact zpow_ne_zero _ hL'
  constructor
  · intro a a' e
    funext μ
    have e1 := congrFun (congrArg Subtype.val e) μ
    simp only [siteOfResidues] at e1
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at e1
    obtain ⟨k, hk⟩ := e1
    rw [← hside, zsmul_eq_mul, ← mul_assoc, ← sub_mul] at hk
    have e2 : (k : ℝ) * N = ((a μ).val : ℝ) - ((a' μ).val : ℝ) := mul_right_cancel₀ hs hk
    have e3 : k * (N : ℤ) = ((a μ).val : ℤ) - ((a' μ).val : ℤ) := by exact_mod_cast e2
    have e4 : (((a μ).val : ℤ) : ZMod N) - (((a' μ).val : ℤ) : ZMod N) = 0 := by
      rw [← Int.cast_sub, ← e3]
      simp
    simpa [sub_eq_zero] using e4
  · rintro ⟨x, n, hn⟩
    refine ⟨fun μ => ((n μ : ℤ) : ZMod N), Subtype.ext (funext fun μ => ?_)⟩
    simp only [siteOfResidues]
    rw [hn μ, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-(n μ / (N : ℤ)), ?_⟩
    have e1 : ((((n μ : ℤ) : ZMod N).val : ℤ)) = n μ % (N : ℤ) := ZMod.val_intCast _
    have e2 : n μ % (N : ℤ) + (N : ℤ) * (n μ / (N : ℤ)) = n μ := Int.emod_add_mul_ediv _ _
    have e3 : ((((n μ : ℤ) : ZMod N).val : ℝ)) + (N : ℝ) * ((n μ / (N : ℤ) : ℤ) : ℝ) =
        (n μ : ℝ) := by
      rw [← e1] at e2
      exact_mod_cast e2
    rw [← hside, zsmul_eq_mul, ← e3]
    push_cast
    ring
theorem natCard_site (hL : 0 < L) (m d : ℕ) :
    Nat.card (Site L m (d : ℤ)) = (2 * L ^ (m + d)) ^ 4 := by
  have hN : 0 < 2 * L ^ (m + d) := by positivity
  have : NeZero (2 * L ^ (m + d)) := ⟨hN.ne'⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ (siteOfResidues_bijective hL m d)),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
theorem site_finite (hL : 0 < L) (m d : ℕ) : Finite (Site L m (d : ℤ)) := by
  have hN : 0 < 2 * L ^ (m + d) := by positivity
  have : NeZero (2 * L ^ (m + d)) := ⟨hN.ne'⟩
  exact Finite.of_equiv _ (Equiv.ofBijective _ (siteOfResidues_bijective hL m d))
theorem bond_finite {j : ℤ} (h : Finite (Site L m j)) : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
theorem plaquette_finite {j : ℤ} (h : Finite (Site L m j)) : Finite (Plaquette L m j) := by apply _root_.YangMills.Construction.GradLaplacianCommutation.plaquette_finite <;> assumption
theorem levelDepth_eq_sub {K n : ℕ} (h : n ≤ K) : levelDepth K n = ((K - n : ℕ) : ℤ) := by
  simp only [levelDepth]
  omega
theorem siteAtLevel_finite (hL : 0 < L) (m : ℕ) {K n : ℕ} (h : n ≤ K) :
    Finite (SiteAtLevel L m K n) := by
  simp only [SiteAtLevel]
  rw [levelDepth_eq_sub h]
  exact site_finite hL m _
theorem tracelessFunctionsOn_finiteDim {ι : Type*} {I : Set ι} (hI : I.Finite) :
    Module.Finite ℂ (tracelessFunctionsOn I) := by
  have : Finite I := hI
  have hinj : Function.Injective
      (LinearMap.funLeft ℂ ComplexMatrix2 (Subtype.val : I → ι) ∘ₗ
        (tracelessFunctionsOn I).subtype) := by
    intro f f' e
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : i ∈ I
    · exact congrFun e ⟨i, hi⟩
    · rw [f.2.2 i hi, f'.2.2 i hi]
  exact Module.Finite.of_injective _ hinj
theorem isFiniteWithFiniteDimFunctions_of_finite {ι : Type*} {I : Set ι} (hI : I.Finite) :
    IsFiniteWithFiniteDimFunctions I :=
  ⟨hI, tracelessFunctionsOn_finiteDim hI⟩
theorem levelLatticeFinite_of_le (hL : 0 < L) (m : ℕ) {K n : ℕ} (h : n ≤ K) :
    LevelLatticeFinite L m K n := by
  have := siteAtLevel_finite hL m h
  refine ⟨?_, bond_finite ‹_›, plaquette_finite ‹_›⟩
  simp only [SiteAtLevel]
  rw [levelDepth_eq_sub h, natCard_site hL m, Nat.add_sub_assoc h]
theorem separatedSequenceFinite_of_pos (hL : 0 < L) (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) :
    SeparatedSequenceFinite S Ω := by
  have hsite : ∀ n, n ≤ S.top → Finite (SiteAtLevel L m S.levels n) := fun n hn =>
    siteAtLevel_finite hL m (hn.trans S.top_le)
  have hfine : Finite (SiteAtLevel L m S.levels 0) := siteAtLevel_finite hL m (Nat.zero_le _)
  have hbond : Finite (FineBond L m S) := bond_finite hfine
  have hlayer : (layerPoints S Ω).Finite := by
    refine (Set.finite_Iic S.top).biUnion fun n hn => ?_
    have := hsite n hn
    exact (Set.toFinite _).image _
  have hidx : (leveledIndexSet S Ω).Finite := by
    have hsub : leveledIndexSet S Ω ⊆ ⋃ j ∈ Iic S.top,
        Set.range (Sigma.mk j : BondAtLevel L m S.levels j → LeveledBond L m S) := by
      rintro ⟨j, c⟩ ⟨⟨-, hc⟩, -⟩
      have hj : j ≤ S.top := by
        rcases hc with hc | ⟨z, hc⟩
        · exact hc.1
        · exact hc.1
      exact Set.mem_biUnion (show j ∈ Iic S.top from hj) ⟨c, rfl⟩
    refine Set.Finite.subset ((Set.finite_Iic S.top).biUnion fun j hj => ?_) hsub
    have : Finite (BondAtLevel L m S.levels j) := bond_finite (hsite j hj)
    exact Set.finite_range _
  exact ⟨fun n hn => isFiniteWithFiniteDimFunctions_of_finite (by have := hsite n hn; exact Set.toFinite _),
    isFiniteWithFiniteDimFunctions_of_finite hlayer,
    isFiniteWithFiniteDimFunctions_of_finite (Set.toFinite _),
    isFiniteWithFiniteDimFunctions_of_finite (Set.toFinite _),
    isFiniteWithFiniteDimFunctions_of_finite (Set.toFinite _),
    isFiniteWithFiniteDimFunctions_of_finite hidx, hlayer.image _⟩
theorem finitenessOfSitesTopsAndIndices_holds : FinitenessOfSitesTopsAndIndices := by
  intro L m hL _
  have hL0 : 0 < L := by
    have := hL.2
    omega
  exact ⟨fun K n _ h => levelLatticeFinite_of_le hL0 m h,
    fun S _ _ Ω _ => separatedSequenceFinite_of_pos hL0 S Ω⟩
end SeparatedRegions.Counting
end YangMills.Construction
