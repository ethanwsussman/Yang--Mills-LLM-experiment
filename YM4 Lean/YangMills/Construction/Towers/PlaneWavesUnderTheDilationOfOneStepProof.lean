import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Towers.PlaneWavesUnderTheDilationOfOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.StepScalingOfFourierModes
open YangMills.Construction.Tower
open YangMills.Construction.PeriodicOperators (dualLattice toComplexVec bilinDot)
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.Tempered.OneStep
variable {L : ℕ}
private abbrev torusClass (L n : ℕ) (w : InfiniteLattice.AmbientSpace) : PeriodicLattice.FourTorus L n :=
  fun μ => (w μ : AddCircle (PeriodicLattice.torusSide L n))
private theorem bilinDot_ofReal (p y : InfiniteLattice.AmbientSpace) :
    bilinDot (toComplexVec p) (toComplexVec y) = ((∑ μ, p μ * y μ : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec]
private theorem exp_bilinDot_eq_of_mk_eq {n : ℕ} (hL : 0 < L) {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) {y w : InfiniteLattice.AmbientSpace}
    (h : torusClass L n y = torusClass L n w) :
    Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec w)) := by
  obtain ⟨k, hk⟩ := hp
  have hc : ∀ μ, ∃ c : ℤ, y μ - w μ = (c : ℝ) * PeriodicLattice.torusSide L n := fun μ => by
    have h1 : (y μ : AddCircle (PeriodicLattice.torusSide L n)) = w μ := congrFun h μ
    have h0 : ((y μ - w μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨c, hc⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    exact ⟨c, by rw [← hc, zsmul_eq_mul]⟩
  choose c hc using hc
  have hr : ∑ μ, p μ * y μ =
      ∑ μ, p μ * w μ + ((∑ μ, k μ * c μ : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hy : y μ = w μ + (c μ : ℝ) * PeriodicLattice.torusSide L n := by linarith [hc μ]
    rw [hy, hk μ]
    simp only [PeriodicLattice.torusSide]
    push_cast
    field_simp
  rw [bilinDot_ofReal, bilinDot_ofReal, hr]
  push_cast
  rw [mul_add, Complex.exp_add]
  have h1 : Complex.I * ((∑ μ, (k μ : ℂ) * (c μ : ℂ)) * (2 * (Real.pi : ℂ))) =
      ((∑ μ, k μ * c μ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
private theorem phase_mk {n : ℕ} (hL : 0 < L) {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (w : InfiniteLattice.AmbientSpace) :
    phase (L := L) (n := n) p (torusClass L n w) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec w)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
private theorem add_two_pi_mul_mem {n : ℕ} (hL : 0 < L) {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (m : Fin 4 → ℤ) :
    (fun ν => p ν + 2 * Real.pi * (m ν : ℝ)) ∈ dualLattice (2 * L ^ n) := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨fun ν => k ν + 2 * (L : ℤ) ^ n * m ν, fun ν => ?_⟩
  simp only [hk ν]
  push_cast
  field_simp
private theorem rescaledMomentum_mem {n : ℕ} (hL : 0 < L) {p : InfiniteLattice.AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (m' : Fin 4 → ℤ) :
    rescaledMomentum L p m' ∈ dualLattice (2 * L ^ (n + 1)) := by
  obtain ⟨k, hk⟩ := add_two_pi_mul_mem hL hp m'
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨k, fun ν => ?_⟩
  have h := hk ν
  simp only at h
  simp only [rescaledMomentum, h]
  push_cast
  field_simp
  ring
private theorem cast_opposite {m m' : ℕ} {d d' : ℤ} (hm : m = m') (hd : d = d')
    (e : PeriodicLattice.Bond L m d = PeriodicLattice.Bond L m' d') (b : PeriodicLattice.Bond L m d) :
    cast e b.opposite = (cast e b).opposite := by
  subst hm hd
  rfl
private theorem cast_source {m m' : ℕ} {d d' : ℤ} (hm : m = m') (hd : d = d')
    (e : PeriodicLattice.Bond L m d = PeriodicLattice.Bond L m' d') (b : PeriodicLattice.Bond L m d)
    (w : InfiniteLattice.AmbientSpace) (h : (b.source : PeriodicLattice.FourTorus L m) = torusClass L m w) :
    ((cast e b).source : PeriodicLattice.FourTorus L m') = torusClass L m' w := by
  subst hm hd
  exact h
private theorem cast_sub_eq_unitStep {m m' : ℕ} {d d' : ℤ} (hm : m = m') (hd : d = d')
    (e : PeriodicLattice.Bond L m d = PeriodicLattice.Bond L m' d') (b : PeriodicLattice.Bond L m d)
    (σ : Fin 4) (h : b.target - b.source = PeriodicLattice.unitStep L m d σ) :
    (cast e b).target - (cast e b).source = PeriodicLattice.unitStep L m' d' σ := by
  subst hm hd
  exact h
private theorem levelDepth_self (i : ℕ) :
    PeriodicLattice.levelDepth i i = PeriodicLattice.levelDepth 0 0 := by
  simp [PeriodicLattice.levelDepth]
private theorem stepEdgeEquiv_eq_cast (hL : 0 < L) (n i : ℕ) (c : Edge L n (i + 1) i) :
    ∃ e : PeriodicLattice.Bond L (scaledExponent n (i + 1) i) (PeriodicLattice.levelDepth i i) =
        PeriodicLattice.Bond L (n + 1) (PeriodicLattice.levelDepth 0 0),
      stepEdgeEquiv hL n i c = cast e (scaleEdge hL (Nat.le_succ i) i c) :=
  let e₁ := congrArg (PeriodicLattice.Bond L (scaledExponent n (i + 1) i)) (levelDepth_self i)
  let e₂ := congrArg (fun m => PeriodicLattice.Bond L m (PeriodicLattice.levelDepth 0 0))
    (scaledExponent_succ_self n i)
  ⟨e₁.trans e₂, cast_cast e₁ e₂ (scaleEdge hL (Nat.le_succ i) i c)⟩
private theorem stepEdgeEquiv_opposite (hL : 0 < L) (n i : ℕ) (c : Edge L n (i + 1) i) :
    stepEdgeEquiv hL n i c.opposite = (stepEdgeEquiv hL n i c).opposite := by
  obtain ⟨e, he⟩ := stepEdgeEquiv_eq_cast hL n i c
  obtain ⟨e', he'⟩ := stepEdgeEquiv_eq_cast hL n i c.opposite
  have h : scaleEdge hL (Nat.le_succ i) i c.opposite =
      (scaleEdge hL (Nat.le_succ i) i c).opposite := PeriodicLattice.Bond.ext rfl rfl
  rw [he, he', h]
  exact cast_opposite (scaledExponent_succ_self n i) (levelDepth_self i) e _
private theorem stepEdgeEquiv_forwardFrom_sub (hL : 0 < L) (n i : ℕ) (y : Vertex L n (i + 1) i)
    (ρ : Fin 4) :
    (stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)).target -
        (stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)).source =
      PeriodicLattice.unitStep L (n + 1) (PeriodicLattice.levelDepth 0 0) ρ := by
  obtain ⟨e, he⟩ := stepEdgeEquiv_eq_cast hL n i (PeriodicLattice.Bond.forwardFrom y ρ)
  rw [he]
  refine cast_sub_eq_unitStep (scaledExponent_succ_self n i) (levelDepth_self i) e _ ρ ?_
  change scaleVertex hL (Nat.le_succ i) i (y + PeriodicLattice.unitStep L n _ ρ) -
    scaleVertex hL (Nat.le_succ i) i y = _
  rw [map_add, scaleVertex_unitStep, add_sub_cancel_left]
private theorem stepEdgeEquiv_forwardFrom_source (hL : 0 < L) (n i : ℕ) (y : Vertex L n (i + 1) i)
    (ρ : Fin 4) (w : InfiniteLattice.AmbientSpace)
    (hy : (y : PeriodicLattice.FourTorus L n) = torusClass L n w) :
    ((stepEdgeEquiv hL n i (PeriodicLattice.Bond.forwardFrom y ρ)).source :
        PeriodicLattice.FourTorus L (n + 1)) =
      torusClass L (n + 1) fun ν => (L : ℝ) * w ν := by
  obtain ⟨e, he⟩ := stepEdgeEquiv_eq_cast hL n i (PeriodicLattice.Bond.forwardFrom y ρ)
  rw [he]
  refine cast_source (scaledExponent_succ_self n i) (levelDepth_self i) e _ _ ?_
  change scaling hL n (i + 1) i (y : PeriodicLattice.FourTorus L n) = _
  rw [hy, scaling_mk hL w]
  funext ν
  simp
private theorem neg_lt_levelDepth (m : ℕ) (hm : 0 < m) :
    -(m : ℤ) < PeriodicLattice.levelDepth 0 0 := by
  simp only [PeriodicLattice.levelDepth]
  push_cast
  omega
private theorem extendOddly_opposite (hL : 2 ≤ L) {m : ℕ} (hm : 0 < m)
    (f : Edge L m 0 0 → Matrices.ComplexMatrix2) (b : Edge L m 0 0) :
    extendOddly (k := 0) (j := 0) f b.opposite = -extendOddly (k := 0) (j := 0) f b := by
  have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL
      (neg_lt_levelDepth m hm) b with ⟨hb, hr⟩ | ⟨hr, hb⟩
  · simp [extendOddly, hb, hr, hrr]
  · simp [extendOddly, hb, hr]
private theorem fourierModeForm_of_unitStep (hL : 2 ≤ L) {m : ℕ} (hm : 0 < m) (a : Fin 3)
    (q : InfiniteLattice.AmbientSpace) (ρ σ : Fin 4) (b : UnitEdge L m)
    (hb : b.target - b.source = PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth 0 0) ρ) :
    fourierModeForm L m a q σ b =
      if σ = ρ then phase q (b.source : PeriodicLattice.FourTorus L m) •
        Matrices.ComplexMatrix2.pauliFamily a else 0 := by
  have hpos : b.IsPositivelyOriented := ⟨ρ, hb⟩
  simp only [fourierModeForm, extendOddly, if_pos hpos]
  by_cases h : σ = ρ
  · subst h
    rw [if_pos hb, if_pos rfl]
  · have hne : b.target - b.source ≠
        PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth 0 0) σ := by
      rw [hb]
      exact PeriodicLattice.MatrixValued.unitStep_ne_unitStep hL (neg_lt_levelDepth m hm) (Ne.symm h)
    rw [if_neg hne, if_neg h]
private theorem vertex_exists_lift {n i : ℕ} (y : Vertex L n (i + 1) i) :
    ∃ a : Fin 4 → ℤ, (y : PeriodicLattice.FourTorus L n) =
      torusClass L n fun ν => (a ν : ℝ) * (L : ℝ)⁻¹ := by
  obtain ⟨a, ha⟩ := y.2
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth (i + 1) i) = (L : ℝ)⁻¹ := by
    have h1 : -PeriodicLattice.levelDepth (i + 1) i = -1 := by
      simp only [PeriodicLattice.levelDepth]
      push_cast
      ring
    rw [PeriodicLattice.meshSize, h1, zpow_neg_one]
  refine ⟨a, funext fun ν => ?_⟩
  rw [ha ν, hs]
theorem claim_holds : Claim := by
  intro L hL hstd n i _
  have hL2 : 2 ≤ L := by
    have := hstd.2
    omega
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨stepEdgeEquiv_opposite hL n i, fun q σ a b => extendOddly_opposite hL2 n.succ_pos _ b,
    fun p hp m => add_two_pi_mul_mem hL hp m, fun p hp m' y ρ σ a => ?_, fun p hp m m' y hm => ?_⟩
  · obtain ⟨c, hc⟩ := vertex_exists_lift y
    rw [fourierModeForm_of_unitStep hL2 n.succ_pos a _ ρ σ _ (stepEdgeEquiv_forwardFrom_sub hL n i y ρ)]
    by_cases h : σ = ρ
    · rw [if_pos h, if_pos h, stepEdgeEquiv_forwardFrom_source hL n i y ρ _ hc, hc,
        phase_mk hL (rescaledMomentum_mem hL hp m'), phase_mk hL (add_two_pi_mul_mem hL hp m')]
      congr 3
      rw [bilinDot_ofReal, bilinDot_ofReal]
      congr 1
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [rescaledMomentum]
      field_simp
    · rw [if_neg h, if_neg h]
  · obtain ⟨c, hc⟩ := vertex_exists_lift y
    rw [hc, phase_mk hL (add_two_pi_mul_mem hL hp m), phase_mk hL (add_two_pi_mul_mem hL hp m')]
    choose t ht using hm
    have hr : ∑ ν, (p ν + 2 * Real.pi * (m ν : ℝ)) * ((c ν : ℝ) * (L : ℝ)⁻¹) =
        ∑ ν, (p ν + 2 * Real.pi * (m' ν : ℝ)) * ((c ν : ℝ) * (L : ℝ)⁻¹) +
          ((∑ ν, t ν * c ν : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have hν : (m ν : ℝ) = m' ν + (L : ℝ) * t ν := by
        have := ht ν
        have h2 : m ν = m' ν + (L : ℤ) * t ν := by linarith
        rw [h2]
        push_cast
        ring
      rw [hν]
      field_simp
      ring
    rw [bilinDot_ofReal, bilinDot_ofReal, hr]
    push_cast
    rw [mul_add, Complex.exp_add]
    have h1 : Complex.I * ((∑ ν, (t ν : ℂ) * (c ν : ℂ)) * (2 * (Real.pi : ℂ))) =
        ((∑ ν, t ν * c ν : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end YangMills.Construction.Tower.StepScalingOfFourierModes
end
