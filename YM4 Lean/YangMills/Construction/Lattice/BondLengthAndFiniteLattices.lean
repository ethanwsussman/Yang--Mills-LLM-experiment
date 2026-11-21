import YangMills.Construction.Lattice.BondEndpointsAndFiniteness
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.DoubleBlockFromItsLowestCornerProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
private theorem isMinimalResidue_of_abs_le_one {N t : ℤ} (hN : 2 ≤ N) (ht : |t| ≤ 1) :
    IsMinimalResidue N t := by
  intro s hs
  by_contra hlt
  have hlt' : |s| < |t| := not_le.mp hlt
  have hs0 : s = 0 := Int.abs_lt_one_iff.mp (lt_of_lt_of_le hlt' ht)
  subst hs0
  have htpos : 0 < |t| := by simpa using hlt'
  have hdvd : N ∣ t := by simpa using hs.dvd
  have hle : N ≤ |t| := Int.le_of_dvd htpos ((dvd_abs N t).mpr hdvd)
  omega
private theorem offsetSite_single (y : Site L m j) (μ : Fin 4) (ε : ℤ) :
    offsetSite y (Pi.single μ ε) = y + ε • unitStep L m j μ := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.offsetSite_single <;> assumption
private theorem supNormVec_single (μ : Fin 4) {ε : ℤ} (hε : |ε| = 1) :
    TorusMetric.supNormVec (fun ν => (((Pi.single μ ε : Fin 4 → ℤ) ν : ℤ) : ℝ)) = 1 := by
  have hε' : |(ε : ℝ)| = 1 := by exact_mod_cast hε
  unfold TorusMetric.supNormVec
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun ν _ => ?_
    by_cases hν : ν = μ
    · subst hν
      simp [hε']
    · simp [Pi.single_eq_of_ne hν]
  · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ μ))
    simp [hε']
private theorem torusSupNorm_source_sub_target (hc : SublatticeCoordinates L m j) (b : Bond L m j) :
    TorusMetric.torusSupNorm ((b.source : FourTorus L m) - (b.target : FourTorus L m)) =
      meshSize L j := by
  obtain ⟨-, hpos, -, -, -, -, -, hnorm⟩ := hc
  have hN : (2 : ℤ) ≤ ((2 * halfPeriod L m j : ℕ) : ℤ) := by
    push_cast
    omega
  obtain ⟨μ, ε, hε, hb⟩ : ∃ (μ : Fin 4) (ε : ℤ), |ε| = 1 ∧
      b.source = b.target + ε • unitStep L m j μ := by
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · refine ⟨μ, -1, by simp, ?_⟩
      rw [neg_smul, one_smul, ← h]
      abel
    · refine ⟨μ, 1, by simp, ?_⟩
      rw [one_smul, ← neg_eq_iff_eq_neg.mpr h]
      abel
  have hleast : ∀ ν, IsMinimalResidue (2 * halfPeriod L m j : ℕ)
      ((Pi.single μ ε : Fin 4 → ℤ) ν) := by
    intro ν
    refine isMinimalResidue_of_abs_le_one hN ?_
    by_cases hν : ν = μ
    · subst hν
      simp [hε]
    · simp [Pi.single_eq_of_ne hν]
  have key := (hnorm b.target (Pi.single μ ε) hleast).1
  rw [offsetSite_single, ← hb, supNormVec_single μ hε, mul_one] at key
  exact key
private theorem finite_site_of_coords (hc : SublatticeCoordinates L m j) : Finite (Site L m j) := by
  obtain ⟨-, hpos, -, hcoord, hcong, -⟩ := hc
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 2 * halfPeriod L m j := ⟨_, rfl⟩
  rw [← hN] at hpos hcong
  have hN0 : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hpos
  let f : (Fin 4 → Fin N) → Site L m j :=
    fun p => offsetSite 0 fun μ => ((p μ : ℕ) : ℤ)
  refine Finite.of_surjective f fun x => ?_
  obtain ⟨n, rfl⟩ := hcoord 0 x
  have hnn : ∀ μ, 0 ≤ n μ % (N : ℤ) := fun μ => Int.emod_nonneg _ hN0.ne'
  have hlt : ∀ μ, n μ % (N : ℤ) < N := fun μ => Int.emod_lt_of_pos _ hN0
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 := hnn μ
    have h2 := hlt μ
    omega
  · refine (hcong 0 _ _).mpr fun μ => ?_
    change (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) ≡ n μ [ZMOD (N : ℤ)]
    rw [Int.toNat_of_nonneg (hnn μ)]
    exact Int.mod_modEq _ _
abbrev _root_.YangMills.SharedProofs.p63828 := @finite_site_of_coords
private theorem finite_bond_of_finite_site [Finite (Site L m j)] : Finite (Bond L m j) := by apply _root_.YangMills.SharedProofs.p19159 <;> assumption
theorem bondEndpointsAndFiniteness_holds (h : CoordinateDescription) :
    BondEndpointsAndFiniteness := by
  intro s
  obtain ⟨hodd, hL13⟩ := s.isAdmissible
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hc : ∀ j : ℤ, -((s.m : ℕ) : ℤ) ≤ j → SublatticeCoordinates s.L s.m j :=
    (h s.L s.m hodd hL13 hm).1
  have hL1 : (1 : ℝ) < (s.L : ℝ) := by
    have : 1 < s.L := by omega
    exact_mod_cast this
  have hne : ∀ j j' : ℤ, -((s.m : ℕ) : ℤ) ≤ j → -((s.m : ℕ) : ℤ) ≤ j' → j' ≠ j →
      ∀ b : Bond s.L s.m j, ¬IsLatticeBond s.L s.m j' b.endpointPair := by
    rintro j j' hj hj' hjj b ⟨b', hb'⟩
    have e1 := torusSupNorm_source_sub_target (hc j hj) b
    have e2 := torusSupNorm_source_sub_target (hc j' hj') b'
    have ht : (b'.source : FourTorus s.L s.m) = b.source := congrArg Prod.fst hb'
    have hh : (b'.target : FourTorus s.L s.m) = b.target := congrArg Prod.snd hb'
    rw [ht, hh, e1] at e2
    unfold meshSize at e2
    have hinj := zpow_right_injective₀ (a := (s.L : ℝ)) (by linarith) hL1.ne' e2
    exact hjj (by omega)
  have hd : ∀ n : ℕ, n ≤ s.K → -((s.m : ℕ) : ℤ) ≤ levelDepth s.K n := by
    intro n hn
    simp only [levelDepth]
    omega
  have hdisj : ∀ n n' : ℕ, n ≤ s.K → n' ≤ s.K → n ≠ n' →
      ∀ p : FourTorus s.L s.m × FourTorus s.L s.m,
        ¬(IsLatticeBond s.L s.m (levelDepth s.K n) p ∧
          IsLatticeBond s.L s.m (levelDepth s.K n') p) := by
    rintro n n' hn hn' hnn p ⟨⟨b, rfl⟩, hb'⟩
    refine hne _ _ (hd n hn) (hd n' hn') ?_ b hb'
    simp only [levelDepth]
    omega
  refine ⟨fun j hj => ⟨torusSupNorm_source_sub_target (hc j hj),
    fun j' hj' hjj b => hne j j' hj hj' hjj b, finite_site_of_coords (hc j hj), ?_⟩, hdisj, ?_⟩
  · have := finite_site_of_coords (hc j hj)
    exact finite_bond_of_finite_site
  · rintro p ⟨n, hn, hb⟩
    refine ⟨n, ⟨hn, hb⟩, ?_⟩
    rintro n' ⟨hn', hb'⟩
    by_contra hnn
    exact hdisj n' n hn' hn hnn p ⟨hb', hb⟩
end YangMills.Construction.PeriodicLattice
