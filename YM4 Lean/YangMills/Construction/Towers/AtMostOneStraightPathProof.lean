import YangMills.Construction.Lattice.AxialPathUniqueness
import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.AtMostOneStraightPath
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AxisPathUniqueness
theorem eq_zero_or_eq_of_single_modEq {H : ℤ} {μ ν : Fin 4} {q q' : ℤ} (hq : 2 * |q| < H)
    (hq' : 2 * |q'| < H)
    (h : ∀ ρ, (Pi.single μ q : Fin 4 → ℤ) ρ ≡ (Pi.single ν q' : Fin 4 → ℤ) ρ [ZMOD H]) :
    (q = 0 ∧ q' = 0) ∨ (μ = ν ∧ q = q') := by
  by_cases hμν : μ = ν
  · subst hμν
    right
    have hd := (h μ).dvd
    simp only [Pi.single_eq_same] at hd
    have hlt : |q' - q| < H := by
      have := abs_sub q' q
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    exact ⟨rfl, by omega⟩
  · left
    have hm := h μ
    have hn := h ν
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hμν, Pi.single_eq_of_ne (Ne.symm hμν)] at hm hn
    have dq : H ∣ q := Int.modEq_zero_iff_dvd.mp hm
    have dq' : H ∣ q' := Int.modEq_zero_iff_dvd.mp hn.symm
    have aq : |q| < H := by have := abs_nonneg q; linarith
    have aq' : |q'| < H := by have := abs_nonneg q'; linarith
    exact ⟨Int.eq_zero_of_abs_lt_dvd dq aq, Int.eq_zero_of_abs_lt_dvd dq' aq'⟩
theorem zsmul_unitStep_coe (L n : ℕ) (j : ℤ) (μ : Fin 4) (q : ℤ) :
    ((q • PeriodicLattice.unitStep L n j μ : PeriodicLattice.Site L n j) :
        PeriodicLattice.FourTorus L n) =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (QuotientLattices.scaledIntVector (PeriodicLattice.meshSize L j) (Pi.single μ q)) := by
  have hs : ((q • PeriodicLattice.unitStep L n j μ : PeriodicLattice.Site L n j) :
      PeriodicLattice.FourTorus L n) =
      q • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L j) := rfl
  rw [hs]
  funext ρ
  by_cases hρ : ρ = μ
  · subst hρ
    simp [PeriodicLattice.pointOnAxis, TorusMetric.torusProj, QuotientLattices.scaledIntVector]
  · simp [PeriodicLattice.pointOnAxis, TorusMetric.torusProj, QuotientLattices.scaledIntVector,
      Pi.single_eq_of_ne hρ]
theorem single_relation_periodic {L n₀ k i : ℕ} (hL : 0 < L)
    (hq : QuotientLattices.IsQuotientLattice L n₀ k i)
    (μ ν : Fin 4) (q q' : ℤ)
    (b : ((|q| : ℤ) : ℝ) * Tower.meshAt L k i < PeriodicLattice.torusSide L n₀ / 2)
    (b' : ((|q'| : ℤ) : ℝ) * Tower.meshAt L k i < PeriodicLattice.torusSide L n₀ / 2)
    (h : q • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) μ =
      q' • PeriodicLattice.unitStep L n₀ (PeriodicLattice.levelDepth k i) ν) :
    (q = 0 ∧ q' = 0) ∨ (μ = ν ∧ q = q') := by
  obtain ⟨-, -, -, -, hH, -, -, -, hcong, -⟩ := hq
  have hmesh : PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k i) =
      Tower.meshAt L k i := Tower.meshSize_levelDepth L k i
  have hpos : 0 < Tower.meshAt L k i := zpow_pos (by exact_mod_cast hL) _
  rw [hmesh] at hH
  have hside : PeriodicLattice.torusSide L n₀ =
      (QuotientLattices.sitesPerAxis L n₀ k i : ℝ) * Tower.meshAt L k i := by
    rw [← hH]; field_simp
  have key : ∀ t : ℤ, ((|t| : ℤ) : ℝ) * Tower.meshAt L k i < PeriodicLattice.torusSide L n₀ / 2 →
      2 * |t| < (QuotientLattices.sitesPerAxis L n₀ k i : ℤ) := by
    intro t ht
    rw [hside] at ht
    have h2 : (2 * ((|t| : ℤ) : ℝ)) * Tower.meshAt L k i <
        (QuotientLattices.sitesPerAxis L n₀ k i : ℝ) * Tower.meshAt L k i := by linarith
    have h3 := lt_of_mul_lt_mul_right h2 hpos.le
    exact_mod_cast h3
  refine eq_zero_or_eq_of_single_modEq (key q b) (key q' b') ((hcong _ _).1 ?_)
  have hc := congrArg
    (fun s : PeriodicLattice.Site L n₀ (PeriodicLattice.levelDepth k i) =>
      (s : PeriodicLattice.FourTorus L n₀)) h
  simpa only [zsmul_unitStep_coe] using hc
theorem onPeriodicLattice_holds {L n₀ k i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n₀) (hi : i ≤ k)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hS : PeriodicLattice.AxialPathUniqueness) :
    OnPeriodicLattice L n₀ k i := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, hQ, hC, -⟩ := hA L hL n₀ i k hn hi
  have hmesh : PeriodicLattice.meshSize L (QuotientLattices.refinementIndex k i) =
      Tower.meshAt L k i := Tower.meshSize_levelDepth L k i
  refine ⟨fun μ ν q q' b b' h => single_relation_periodic hL0 hQ μ ν q q' b b' h, ?_⟩
  intro x x' μ ν q q' e b e' b'
  have hj : -(n₀ : ℤ) ≤ PeriodicLattice.levelDepth k i := by
    have : (i : ℤ) ≤ k := by exact_mod_cast hi
    simp only [PeriodicLattice.levelDepth]
    omega
  have c : ((|q| : ℤ) : ℝ) < (L : ℝ) ^ ((n₀ : ℤ) + PeriodicLattice.levelDepth k i) :=
    (hC q).2 (by rw [hmesh]; exact b)
  have c' : ((|q'| : ℤ) : ℝ) < (L : ℝ) ^ ((n₀ : ℤ) + PeriodicLattice.levelDepth k i) :=
    (hC q').2 (by rw [hmesh]; exact b')
  exact hS L n₀ hL hn _ hj x x' μ ν q q' ⟨e, c⟩ ⟨e', c'⟩
theorem single_relation_fullSpace {a : ℝ} (ha : 0 < a) (μ ν : Fin 4) (q q' : ℤ)
    (h : q • InfiniteLattice.axisStep a μ = q' • InfiniteLattice.axisStep a ν) :
    (q = 0 ∧ q' = 0) ∨ (μ = ν ∧ q = q') := by
  have hc : ∀ ρ, (q : ℝ) * (Pi.single μ a : Fin 4 → ℝ) ρ =
      (q' : ℝ) * (Pi.single ν a : Fin 4 → ℝ) ρ := by
    intro ρ
    have h1 := congrArg
      (fun s : InfiniteLattice.LatticePoint a => (s : InfiniteLattice.AmbientSpace) ρ) h
    simpa [InfiniteLattice.axisStep] using h1
  by_cases hμν : μ = ν
  · subst hμν
    right
    have h1 := hc μ
    simp only [Pi.single_eq_same] at h1
    have h2 : (q : ℝ) = q' := mul_right_cancel₀ ha.ne' h1
    exact ⟨rfl, by exact_mod_cast h2⟩
  · left
    have h1 := hc μ
    have h2 := hc ν
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hμν, Pi.single_eq_of_ne (Ne.symm hμν),
      mul_zero] at h1 h2
    have h3 : (q : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right ha.ne'
    have h4 : (q' : ℝ) = 0 := (mul_eq_zero.mp h2.symm).resolve_right ha.ne'
    exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
theorem signedSteps_eq_fullSpace {a : ℝ} (ha : 0 < a) {x x' : InfiniteLattice.LatticePoint a}
    {μ ν : Fin 4} {q q' : ℤ} (h : Tower.FullSpace.IsAxisDisplacement x x' μ q)
    (h' : Tower.FullSpace.IsAxisDisplacement x x' ν q') :
    Tower.FullSpace.signedSteps x μ q = Tower.FullSpace.signedSteps x ν q' := by
  rcases single_relation_fullSpace ha μ ν q q' (h.symm.trans h') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [Tower.FullSpace.signedSteps, Tower.FullSpace.forwardSteps]
  · rfl
theorem onFullSpace_holds {L k i : ℕ} (hL : 0 < L) : OnFullSpace L k i := by
  have ha : 0 < Tower.meshAt L k i := zpow_pos (by exact_mod_cast hL) _
  refine ⟨single_relation_fullSpace ha, ?_⟩
  intro x x' μ ν q q' h h'
  refine ⟨signedSteps_eq_fullSpace ha h h', ?_⟩
  have hex : ∃ p : Fin 4 × ℤ, Tower.FullSpace.IsAxisDisplacement x x' p.1 p.2 := ⟨(μ, q), h⟩
  rw [Tower.FullSpace.axisPath, dif_pos hex]
  exact signedSteps_eq_fullSpace ha hex.choose_spec h
theorem axisPathsUnique_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hS : PeriodicLattice.AxialPathUniqueness) : AxisPathsUnique := by
  intro L hL k i hi
  have hL0 : 0 < L := by have := hL.2; omega
  exact ⟨fun n₀ hn => onPeriodicLattice_holds hL hn hi hA hS, onFullSpace_holds hL0⟩
end YangMills.Construction.Tower.AxisPathUniqueness
end
