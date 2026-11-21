import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.ClusterExpansionOfAStep.DifferencesOfTheDensities
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps FieldMoves StepSettings
  ExponentialSums TorusMirror DensityDifferences
def MirrorDensities.offset {m : ℕ} (z y : TorusSite m) : Fin 4 → ℤ := fun i => (y i - z i).valMinAbs
open MirrorDensities
theorem MirrorDensities.add_siteOfInt_offset {m : ℕ} [NeZero m] (z y : TorusSite m) : z + siteOfInt (offset z y) = y := by apply _root_.YangMills.DeltaSharedProofs.p500399 <;> assumption
theorem MirrorDensities.natAbs_offset_le {m : ℕ} [NeZero m] (z y : TorusSite m) (i : Fin 4) :
    (offset z y i).natAbs ≤ _root_.YangMills.Construction.TorusFields.supDist y z := (_root_.YangMills.Construction.TorusFields.supDist_le_iff y z _).mp le_rfl i
theorem MirrorDensities.abs_offset_le {m : ℕ} [NeZero m] (z y : TorusSite m) (i : Fin 4) :
    |offset z y i| ≤ (_root_.YangMills.Construction.TorusFields.supDist y z : ℤ) := by
  have := natAbs_offset_le z y i
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this
theorem MirrorDensities.siteOfInt_injective_of_abs_sub_lt {M : ℕ} {g g' : Fin 4 → ℤ}
    (hs : ∀ i, |g i - g' i| < (M : ℤ))
    (e : (siteOfInt g : TorusSite M) = siteOfInt g') : g = g' := by
  funext i
  have h1 : ((g i : ℤ) : ZMod M) = (g' i : ℤ) := congrFun e i
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    simp only [mul_zero] at hk
    omega
  have hk1 : 1 ≤ |k| := Int.one_le_abs hk0
  have hM := hs i
  have h2 : |g i - g' i| = (M : ℤ) * |k| := by
    rw [abs_sub_comm, hk, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (M : ℤ))]
  rw [h2] at hM
  nlinarith [abs_nonneg k, (by positivity : (0 : ℤ) ≤ (M : ℤ))]
theorem MirrorDensities.supDist_le_supDist_mirror {N r : ℕ} [NeZero N] [NeZero (4 * r)] (z : TorusSite N)
    {g g' : Fin 4 → ℤ} (hs : ∀ i, |g i - g' i| ≤ (r : ℤ)) :
    _root_.YangMills.Construction.TorusFields.supDist (z + siteOfInt g) (z + siteOfInt g') ≤ _root_.YangMills.Construction.TorusFields.supDist (siteOfInt g : TorusSite (4 * r)) (siteOfInt g') := by
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  have hr : 0 < r := by
    have : 4 * r ≠ 0 := NeZero.ne _
    omega
  have e1 : (z + siteOfInt g : TorusSite N) i - (z + siteOfInt g' : TorusSite N) i = ((g i - g' i : ℤ) : ZMod N) := by
    simp [siteOfInt]
  rw [e1]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  have e2 : ((siteOfInt g : TorusSite (4 * r)) i - (siteOfInt g' : TorusSite (4 * r)) i) =
      ((g i - g' i : ℤ) : ZMod (4 * r)) := by
    simp [siteOfInt]
  have h3 : ((((g i - g' i : ℤ) : ZMod (4 * r))).valMinAbs) = g i - g' i := by
    have h := ZMod.valMinAbs_spec (((g i - g' i : ℤ) : ZMod (4 * r))) (g i - g' i)
    refine h.mpr ⟨rfl, ?_⟩
    have := abs_le.mp (hs i)
    push_cast
    constructor <;> omega
  have h4 := (_root_.YangMills.Construction.TorusFields.supDist_le_iff (siteOfInt g : TorusSite (4 * r)) (siteOfInt g') _).mp le_rfl i
  rw [e2, h3] at h4
  exact h4
def MirrorDensities.mirrorBond {N : ℕ} (r : ℕ) (z : TorusSite N) (b : TorusBond N) : TorusBond (4 * r) :=
  (siteOfInt (offset z b.1), b.2)
theorem MirrorDensities.fieldsAgreeNear_perturb_mirror {N r : ℕ} [NeZero N] (hr : 2 ≤ r) (hN : 3 * r < N)
    (z : TorusSite N) (W : TorusField N)
    (c : Fin 2 → TorusBond N) (X : Fin 2 → imaginaryQuaternions) (σ : Fin 2 → ℝ) (hc : ∀ l, _root_.YangMills.Construction.TorusFields.supDist (c l).1 z ≤ r / 2)
    (y : TorusSite N) (hy : _root_.YangMills.Construction.TorusFields.supDist y z ≤ r / 2) (m : ℕ) (hm : m + r / 2 ≤ r) :
    FieldsAgreeNear (perturb c X σ W) (perturb (fun l => mirrorBond r z (c l)) X σ (mirrorField r z W))
      y (siteOfInt (offset z y)) m := by
  have : NeZero (4 * r) := ⟨by omega⟩
  rintro ⟨g, i⟩ hb
  set o := offset z y with ho
  have hoy : ∀ j, |o j| ≤ ((r / 2 : ℕ) : ℤ) := fun j =>
    (abs_offset_le z y j).trans (by exact_mod_cast hy)
  have hsum : ∀ a : Fin 4 → ℤ, OffsetInBox m a → OffsetInBox r (o + a) := by
    intro a ha j
    have h1 := hoy j
    have h2 := ha j
    have h3 : ((m : ℤ) + ((r / 2 : ℕ) : ℤ)) ≤ r := by exact_mod_cast hm
    calc |(o + a) j| ≤ |o j| + |a j| := abs_add_le _ _
      _ ≤ r := by linarith
  have hbox : BondOffsetInBox r (o + g, i) := by
    refine ⟨hsum g hb.1, ?_⟩
    have := hsum _ hb.2
    rwa [← add_assoc] at this
  have e1 : (bondFrom y (g, i)).1 = z + siteOfInt (o + g) := by
    simp only [bondFrom]
    rw [add_siteOfInt_add, ho, add_siteOfInt_offset]
  have e2 : (bondFrom (siteOfInt o : TorusSite (4 * r)) (g, i)).1 = siteOfInt (o + g) := by
    simp only [bondFrom]
    rw [siteOfInt_add]
  show perturb c X σ W (bondFrom y (g, i)).1 i = _
  simp only [show (bondFrom (siteOfInt o : TorusSite (4 * r)) (g, i)).2 = i from rfl]
  rw [e1, e2, perturb_apply, perturb_apply, mirrorField_siteOfInt hr z W (o + g, i) hbox]
  congr 2
  unfold bondShift
  refine Finset.sum_congr rfl fun l _ => ?_
  have hoc : ∀ j, |offset z (c l).1 j| ≤ ((r / 2 : ℕ) : ℤ) := fun j =>
    (abs_offset_le z (c l).1 j).trans (by exact_mod_cast hc l)
  have hbd : ∀ j, |offset z (c l).1 j - (o + g) j| ≤ 2 * (r : ℤ) := by
    intro j
    have h1 := hoc j
    have h2 := hsum g hb.1 j
    have h3 : ((r / 2 : ℕ) : ℤ) ≤ r := by exact_mod_cast Nat.div_le_self r 2
    calc _ ≤ |offset z (c l).1 j| + |(o + g) j| := abs_sub _ _
      _ ≤ 2 * (r : ℤ) := by linarith
  have iff1 : c l = (z + siteOfInt (o + g), i) ↔ mirrorBond r z (c l) = (siteOfInt (o + g), i) := by
    unfold mirrorBond
    constructor
    · intro e
      have e3 : (c l).1 = z + siteOfInt (o + g) := congrArg Prod.fst e
      have e4 : (c l).2 = i := congrArg Prod.snd e
      have e5 : (siteOfInt (offset z (c l).1) : TorusSite N) = siteOfInt (o + g) := by
        have := add_siteOfInt_offset z (c l).1
        rw [e3] at this
        rw [e3]
        exact add_left_cancel (a := z) (by rw [add_siteOfInt_offset])
      have e6 := siteOfInt_injective_of_abs_sub_lt (fun j => by
        have := hbd j
        have hNz : (3 * (r : ℤ)) < (N : ℤ) := by exact_mod_cast hN
        have hr0 : (0 : ℤ) ≤ r := by positivity
        linarith) e5
      rw [e6, e4]
    · intro e
      have e3 : (siteOfInt (offset z (c l).1) : TorusSite (4 * r)) = siteOfInt (o + g) := congrArg Prod.fst e
      have e4 : (c l).2 = i := congrArg Prod.snd e
      have e6 := siteOfInt_injective_of_abs_sub_lt (M := 4 * r) (fun j => by
        have := hbd j
        push_cast
        have hr0 : (0 : ℤ) < r := by
          have : 0 < r := by omega
          exact_mod_cast this
        linarith) e3
      have e7 : (c l).1 = z + siteOfInt (o + g) := by
        rw [← e6, add_siteOfInt_offset]
      exact Prod.ext e7 e4
  by_cases hl : c l = (z + siteOfInt (o + g), i)
  · rw [if_pos hl, if_pos (iff1.mp hl)]
  · rw [if_neg hl, if_neg fun e => hl (iff1.mpr e)]
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n}
theorem MirrorDensities.iteratedFDeriv_sub_const_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (hk : k ≠ 0) {p : E}
    {G : E → ℝ} (h : ContDiffAt ℝ k G p) (c : ℝ) :
    iteratedFDeriv ℝ k (fun σ => G σ - c) p = iteratedFDeriv ℝ k G p := by
  have := iteratedFDeriv_sub_const_add_mul hk h (contDiffAt_const (c := (0 : ℝ))) 0 c
  simpa using this
theorem MirrorDensities.supDist_le_supportDiam {m k : ℕ} (y : TorusSite m) (c : Fin k → TorusBond m) (l : Fin k) :
    _root_.YangMills.Construction.TorusFields.supDist y (c l).1 ≤ supportDiam y c :=
  (Finset.le_sup (f := fun l : Fin k => _root_.YangMills.Construction.TorusFields.supDist y (c l).1) (Finset.mem_univ l)).trans (le_max_left _ _)
theorem MirrorDensities.supDist_bonds_le_supportDiam {m k : ℕ} (y : TorusSite m) (c : Fin k → TorusBond m)
    (l l' : Fin k) :
    _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c l').1 ≤ supportDiam y c := by
  refine le_trans ?_ (le_max_right _ _)
  exact (Finset.le_sup (f := fun l' : Fin k => _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c l').1) (Finset.mem_univ l')).trans
    (Finset.le_sup (f := fun l : Fin k => Finset.univ.sup fun l' : Fin k => _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c l').1)
      (Finset.mem_univ l))
theorem MirrorDensities.div_weight_le_mul_exp (ℓ : TorusLumps.StepParameters) {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    A / ℓ.weight m ≤ A * Real.exp (-ℓ.weightRate * m) := by
  unfold TorusLumps.StepParameters.weight
  set w := max 1 (((m : ℝ) / ℓ.n₁) ^ 16000) with hw
  have h1 : 1 ≤ w := le_max_left _ _
  have h2 : 0 < Real.exp (ℓ.weightRate * m) := Real.exp_pos _
  rw [div_le_iff₀ (by positivity)]
  have e : Real.exp (-ℓ.weightRate * m) * Real.exp (ℓ.weightRate * m) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : 0 < Real.exp (-ℓ.weightRate * m) := Real.exp_pos _
  calc A = A * (Real.exp (-ℓ.weightRate * m) * Real.exp (ℓ.weightRate * m)) := by rw [e, mul_one]
    _ ≤ A * (Real.exp (-ℓ.weightRate * m) * (w * Real.exp (ℓ.weightRate * m))) := by
      refine mul_le_mul_of_nonneg_left ?_ hA
      refine mul_le_mul_of_nonneg_left ?_ h3.le
      nlinarith
    _ = A * Real.exp (-ℓ.weightRate * m) * (w * Real.exp (ℓ.weightRate * m)) := by ring
theorem MirrorDensities.centered_alongPair_bounds {ℓ : TorusLumps.StepParameters} {t : ℕ} {x : ℝ} {D : TorusFunctional}
    {f : LocalDensity} (hc : ColdExpansion ℓ t x D f)
    {M : ℕ} [NeZero M] (hM : ℓ.n₀ ≤ M) (y : TorusSite M) {c : Fin 2 → TorusBond M} {X : Fin 2 → imaginaryQuaternions}
    {W : TorusField M}
    (hcomm : CommutingPair c X) {σ : Fin 2 → ℝ} (hcold : IsCold ℓ.threshold (perturb c X σ W)) :
    ContDiffAt ℝ 3 (alongPair (centered f M y) c X W) σ ∧ ∀ (k : ℕ) (ι : Fin k → Fin 2), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |iteratedFDeriv ℝ k (alongPair (centered f M y) c X W) σ fun l => Pi.single (ι l) 1| ≤
        (if k = 3 then ℓ.E₃ else ℓ.E) / ℓ.weight (supportDiam y (c ∘ ι)) := by
  have hs := hc.smooth M hM y (perturb c X σ W) hcold
  have hC : ContDiffAt ℝ 3 (alongPair (centered f M y) c X W) σ :=
    contDiffAt_alongPair hcomm σ ((hs 2 c X).sub contDiffAt_const)
  refine ⟨hC, fun k ι k1 k3 hu => ?_⟩
  have hCk : ContDiffAt ℝ k (alongPair (centered f M y) c X W) σ := hC.of_le (by exact_mod_cast k3)
  rw [← mixedDeriv_perturb_eq_iteratedFDeriv hcomm ι σ hCk]
  have hk : k ≠ 0 := by omega
  have e : mixedDeriv (centered f M y) (perturb c X σ W) (c ∘ ι) (X ∘ ι) =
      mixedDeriv (f M y) (perturb c X σ W) (c ∘ ι) (X ∘ ι) := by
    unfold mixedDeriv centered
    rw [iteratedFDeriv_sub_const_of_ne_zero hk ((hs k (c ∘ ι) (X ∘ ι)).of_le (by exact_mod_cast k3))]
  rw [e]
  exact hc.decay M hM y _ hcold k _ _ k1 k3 fun l => hu (ι l)
def MirrorDensities.nearBall (R : StepSetup) {N : ℕ} [NeZero N] (z : TorusSite N) : Finset (TorusSite N) :=
  Finset.univ.filter fun y => _root_.YangMills.Construction.TorusFields.supDist y z ≤ R.range / 2
def MirrorDensities.mirrorCentered (R : StepSetup) {N : ℕ} (z : TorusSite N) (c : Fin 2 → TorusBond N)
    (X : Fin 2 → imaginaryQuaternions) (W : TorusField N) (y : TorusSite N) :
    (Fin 2 → ℝ) → ℝ :=
  alongPair (centered R.density (4 * R.range) (siteOfInt (offset z y))) (fun l => mirrorBond R.range z (c l)) X
    (mirrorField R.range z W)
def StepSettings.ChartSetting.nearSum (s : ChartSetting R n) (z : TorusSite (n * R.params.side))
    (c : Fin 2 → TorusBond (n * R.params.side)) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField (n * R.params.side)) : (Fin 2 → ℝ) → ℝ :=
  alongPair s.densityAt c X W - fun σ => ∑ y ∈ nearBall R z, mirrorCentered R z c X W y σ
structure StepSettings.ChartSetting.NearFreePair (s : ChartSetting R n) (τ ε θ : ℝ) (W : TorusField (n * R.params.side))
    (c : Fin 2 → TorusBond (n * R.params.side)) (X : Fin 2 → imaginaryQuaternions) : Prop where
  norm_exp_sub_one_le : ∀ a : imaginaryQuaternions, ‖a‖ ≤ 2 * τ → ‖((expUnit a : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε
  θ_pos : 0 < θ
  θ_lt : θ + 4 * ε < R.params.threshold
  isNear : s.IsNear θ W
  mem_free : ∀ l, c l ∈ s.free
  areUnitVectors : AreUnitVectors X
  commuting : CommutingPair c X
  supDist_le : ∀ l, _root_.YangMills.Construction.TorusFields.supDist (c l).1 (c 0).1 ≤ R.range / 2
  support_nonempty : s.support.Nonempty
variable {τ ε θ : ℝ} {W : TorusField (n * R.params.side)} {c : Fin 2 → TorusBond (n * R.params.side)}
  {X : Fin 2 → imaginaryQuaternions}
theorem StepSettings.ChartSetting.NearFreePair.range_large (_p : s.NearFreePair τ ε θ W c X) (h : s.Hypotheses) :
    2 ^ 20 ≤ R.range := by
  have := h.range_large
  omega
theorem StepSettings.ChartSetting.NearFreePair.three_mul_range_lt (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) : 3 * R.range < n * R.params.side := by
  obtain ⟨z₀, hz⟩ := p.support_nonempty
  have h1 := h.isAdmissible.far_from_support (c 0) (p.mem_free 0) z₀ (Finset.mem_union_left _ hz)
  have h2 := two_mul_supDist_le (c 0).1 z₀
  have h3 := h.range_large
  omega
theorem StepSettings.ChartSetting.NearFreePair.isCold_mirrorField (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) :
    IsCold θ (mirrorField R.range (c 0).1 W) := by
  have hr := p.range_large h
  refine TorusMirror.isCold_mirrorField (by omega) _ _ p.θ_pos ?_
  intro a μ ν hlt hb
  have h0 : OffsetInBox R.range a := by simpa using hb 0 (by simp [plaquetteOffsets])
  refine p.isNear.curvature_lt (c 0) (p.mem_free 0) _ μ ν hlt ?_
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  have := _root_.YangMills.Construction.TorusFields.supDist_add_le_of_offsetInBox (c 0).1 h0
  omega
theorem StepSettings.ChartSetting.NearFreePair.isCold_perturb_mirror (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) {σ : Fin 2 → ℝ} (hτ : ∀ l, |σ l| ≤ τ) :
    IsCold R.params.threshold
      (perturb (fun l => mirrorBond R.range (c 0).1 (c l)) X σ (mirrorField R.range (c 0).1 W)) := by
  intro x μ ν hlt
  have a := p.isCold_mirrorField h x μ ν hlt
  have b := curvature_le_add_of_close (norm_perturb_sub_le p.norm_exp_sub_one_le
    (fun l => mirrorBond R.range (c 0).1 (c l)) p.areUnitVectors hτ (mirrorField R.range (c 0).1 W)) x μ ν
  linarith [p.θ_lt]
theorem StepSettings.ChartSetting.NearFreePair.commutingPair_mirror (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) :
    CommutingPair (fun l => mirrorBond R.range (c 0).1 (c l)) X := by
  have hr := p.range_large h
  rcases p.commuting with hc | hc
  · left
    intro e
    apply hc
    have e' : mirrorBond R.range (c 0).1 (c 0) = mirrorBond R.range (c 0).1 (c 1) := e
    have e1 : (siteOfInt (offset (c 0).1 (c 0).1) : TorusSite (4 * R.range)) = siteOfInt (offset (c 0).1 (c 1).1) :=
      congrArg Prod.fst e'
    have e2 : (mirrorBond R.range (c 0).1 (c 0)).2 = (mirrorBond R.range (c 0).1 (c 1)).2 := congrArg Prod.snd e'
    have : NeZero (n * R.params.side) := inferInstance
    have hb : ∀ (l : Fin 2) (j : Fin 4), |offset (c 0).1 (c l).1 j| ≤ ((R.range / 2 : ℕ) : ℤ) := fun l j =>
      (abs_offset_le _ _ j).trans (by exact_mod_cast p.supDist_le l)
    have e3 := siteOfInt_injective_of_abs_sub_lt (M := 4 * R.range) (fun j => by
      have h1 := hb 0 j
      have h2 := hb 1 j
      have h3 : ((R.range / 2 : ℕ) : ℤ) ≤ R.range := by exact_mod_cast Nat.div_le_self _ 2
      have h5 := abs_sub (offset (c 0).1 (c 0).1 j) (offset (c 0).1 (c 1).1 j)
      push_cast
      linarith) e1
    have e4 : (c 0).1 = (c 1).1 := by
      rw [← add_siteOfInt_offset (c 0).1 (c 0).1, e3, add_siteOfInt_offset]
    exact Prod.ext e4 e2
  · right
    exact hc
theorem StepSettings.ChartSetting.NearFreePair.abs_siteDensity_sub_mirrorCentered_le (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) {σ : Fin 2 → ℝ}
    (hτ : ∀ l, |σ l| ≤ τ) {y : TorusSite (n * R.params.side)} (hy : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ R.range / 2) :
    |R.siteDensity (n * R.params.side) y (perturb c X σ W) s.support s.labelling -
        mirrorCentered R (c 0).1 c X W y σ| ≤
      Real.exp (-R.params.decayRate * ((R.range / 2 - 2 : ℕ) : ℝ)) := by
  have hr := p.range_large h
  have hN := p.three_mul_range_lt h
  have hbig := h.range_large
  have : NeZero (4 * R.range) := ⟨by omega⟩
  have hg₁ := h.isNear_perturb p.norm_exp_sub_one_le p.θ_lt.le p.isNear p.mem_free p.areUnitVectors hτ
  set m := R.range / 2 - 2 with hm
  have hmr : (R.range : ℝ) / 64 ≤ (m : ℝ) := by
    have : R.range ≤ 64 * m := by omega
    have h2 : (R.range : ℝ) ≤ 64 * (m : ℝ) := by exact_mod_cast this
    linarith
  have hstates : StatesAgreeNear R.params (perturb c X σ W)
      (perturb (fun l => mirrorBond R.range (c 0).1 (c l)) X σ (mirrorField R.range (c 0).1 W)) s.support ∅
      s.labelling
      (fun z => (Finset.notMem_empty _ z.2).elim) y (siteOfInt (offset (c 0).1 y)) m := by
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
    · exact fieldsAgreeNear_perturb_mirror (by omega) hN _ W c X σ p.supDist_le y hy m (by omega)
    · intro a ha
      have hnot : y + siteOfInt a ∉ s.support := by
        intro hmem
        have h1 := h.isAdmissible.far_from_support (c 0) (p.mem_free 0) _ (Finset.mem_union_left _ hmem)
        have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (c 0).1 y (y + siteOfInt a)
        have h3 := _root_.YangMills.Construction.TorusFields.supDist_add_le_of_offsetInBox y ha
        rw [_root_.YangMills.Construction.TorusFields.supDist_comm (c 0).1 y] at h2
        omega
      simp [hnot]
    · intro a _ _ hz' _
      exact (Finset.notMem_empty _ hz').elim
    · rintro ⟨a, ha, hmem⟩
      exfalso
      have h1 := h.isAdmissible.far_from_support (c 0) (p.mem_free 0) _ (Finset.mem_union_left _ hmem)
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (c 0).1 y (y + siteOfInt a)
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_add_le_of_offsetInBox y ha
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm (c 0).1 y] at h2
      omega
  exact h.hullExpansion.forget_cold (n * R.params.side) (4 * R.range) h.isBlockTorusSide (by omega) _ _ s.support
    s.labelling _ y _ m (hg₁.isHullState h)
    (p.isCold_perturb_mirror h hτ) (h.clusterFactor_ne_zero hg₁) hmr hstates
def MirrorDensities.siteWeight (R : StepSetup) {N : ℕ} (z y : TorusSite N) : ℝ :=
  Real.exp (3 * R.params.decayRate) * Real.exp (-R.params.decayRate * R.range / 4) *
    Real.exp (-(R.params.decayRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y z)
theorem MirrorDensities.exp_le_siteWeight_of_near {N : ℕ} {z y : TorusSite N} (hδ : 0 < R.params.decayRate)
    (hr : 4 ≤ R.range)
    (hy : _root_.YangMills.Construction.TorusFields.supDist y z ≤ R.range / 2) :
    Real.exp (-R.params.decayRate * ((R.range / 2 - 2 : ℕ) : ℝ)) ≤ siteWeight R z y := by
  unfold siteWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : 2 ≤ R.range / 2 := by omega
  have e1 : ((R.range / 2 - 2 : ℕ) : ℝ) = ((R.range / 2 : ℕ) : ℝ) - 2 := by
    rw [Nat.cast_sub h2]
    norm_num
  have e2 : (R.range : ℝ) ≤ 2 * ((R.range / 2 : ℕ) : ℝ) + 1 := by
    have : R.range ≤ 2 * (R.range / 2) + 1 := by omega
    exact_mod_cast this
  have e3 : (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) ≤ ((R.range / 2 : ℕ) : ℝ) := by exact_mod_cast hy
  rw [e1]
  nlinarith
theorem MirrorDensities.exp_le_siteWeight_of_far {N : ℕ} {z y : TorusSite N} (hδ : 0 < R.params.decayRate)
    (hr : 4 ≤ R.range)
    (hy : ¬ _root_.YangMills.Construction.TorusFields.supDist y z ≤ R.range / 2) :
    Real.exp (-R.params.decayRate * ((_root_.YangMills.Construction.TorusFields.supDist y z - 2 : ℕ) : ℝ)) ≤ siteWeight R z y := by
  unfold siteWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : 2 ≤ _root_.YangMills.Construction.TorusFields.supDist y z := by omega
  have e1 : ((_root_.YangMills.Construction.TorusFields.supDist y z - 2 : ℕ) : ℝ) = (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) - 2 := by
    rw [Nat.cast_sub h2]
    norm_num
  have e2 : (R.range : ℝ) ≤ 2 * (_root_.YangMills.Construction.TorusFields.supDist y z : ℝ) := by
    have : R.range ≤ 2 * _root_.YangMills.Construction.TorusFields.supDist y z := by omega
    exact_mod_cast this
  rw [e1]
  nlinarith
theorem MirrorDensities.sum_siteWeight_le {N : ℕ} [NeZero N] (z : TorusSite N) (hδ : 0 < R.params.decayRate) :
    ∑ y : TorusSite N, 4 * siteWeight R z y ≤ R.differenceConstant * Real.exp (-R.params.decayRate * R.range / 4) := by
  have hδ2 : 0 < R.params.decayRate / 2 := by linarith
  have hL := sum_torus_exp_le hδ2 z
  unfold siteWeight StepSetup.differenceConstant
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  calc 4 * (Real.exp (3 * R.params.decayRate) * Real.exp (-R.params.decayRate * R.range / 4) *
        ∑ y : TorusSite N, Real.exp (-(R.params.decayRate / 2) * _root_.YangMills.Construction.TorusFields.supDist y z))
      ≤ 4 * (Real.exp (3 * R.params.decayRate) * Real.exp (-R.params.decayRate * R.range / 4) *
          expLatticeSum (R.params.decayRate / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring
def StepSettings.ChartSetting.nearTerm (s : ChartSetting R n) (z : TorusSite (n * R.params.side))
    (c : Fin 2 → TorusBond (n * R.params.side)) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField (n * R.params.side)) (y : TorusSite (n * R.params.side)) (σ : Fin 2 → ℝ) : ℝ :=
  R.siteDensity (n * R.params.side) y (perturb c X σ W) s.support s.labelling -
    if _root_.YangMills.Construction.TorusFields.supDist y z ≤ R.range / 2 then mirrorCentered R z c X W y σ else 0
theorem StepSettings.ChartSetting.nearSum_eq_sum (s : ChartSetting R n) (z : TorusSite (n * R.params.side))
    (c : Fin 2 → TorusBond (n * R.params.side)) (X : Fin 2 → imaginaryQuaternions)
    (W : TorusField (n * R.params.side)) (σ : Fin 2 → ℝ) :
    s.nearSum z c X W σ = ∑ y, s.nearTerm z c X W y σ := by
  unfold ChartSetting.nearSum ChartSetting.nearTerm nearBall
  simp only [Pi.sub_apply, alongPair, ChartSetting.densityAt, Finset.sum_sub_distrib, Finset.sum_filter]
theorem StepSettings.ChartSetting.NearFreePair.abs_second_difference_nearSum_le (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses) (hδ : 0 < R.params.decayRate)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ τ) :
    |s.nearSum (c 0).1 c X W ![t, t] - s.nearSum (c 0).1 c X W ![t, 0] - s.nearSum (c 0).1 c X W ![0, t] +
        s.nearSum (c 0).1 c X W 0| ≤ R.differenceConstant * Real.exp (-R.params.decayRate * R.range / 4) := by
  have hr := p.range_large h
  have hτ0 : 0 ≤ τ := ht0.trans ht
  have small : ∀ σ : Fin 2 → ℝ, (∀ l, σ l = 0 ∨ σ l = t) → ∀ l, |σ l| ≤ τ := by
    intro σ hσ l
    rcases hσ l with e | e <;> rw [e]
    · simpa using hτ0
    · rwa [abs_of_nonneg ht0]
  have s11 := small ![t, t] (fun l => by fin_cases l <;> simp)
  have s10 := small ![t, 0] (fun l => by fin_cases l <;> simp)
  have s01 := small ![0, t] (fun l => by fin_cases l <;> simp)
  have s00 := small ![0, 0] (fun l => by fin_cases l <;> simp)
  have gd : ∀ σ : Fin 2 → ℝ, (∀ l, |σ l| ≤ τ) → s.IsNear (θ + 4 * ε) (perturb c X σ W) := fun σ hσ =>
    h.isNear_perturb p.norm_exp_sub_one_le p.θ_lt.le p.isNear p.mem_free p.areUnitVectors hσ
  rw [← pair_zero]
  simp only [ChartSetting.nearSum_eq_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun y _ => ?_)
    (sum_siteWeight_le (c 0).1 hδ))
  by_cases hy : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ R.range / 2
  · simp only [ChartSetting.nearTerm, if_pos hy]
    have b := exp_le_siteWeight_of_near (R := R) hδ (by omega) hy
    have b1 := (p.abs_siteDensity_sub_mirrorCentered_le h s11 hy).trans b
    have b2 := (p.abs_siteDensity_sub_mirrorCentered_le h s10 hy).trans b
    have b3 := (p.abs_siteDensity_sub_mirrorCentered_le h s01 hy).trans b
    have b4 := (p.abs_siteDensity_sub_mirrorCentered_le h s00 hy).trans b
    rw [abs_le] at *
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
  · simp only [ChartSetting.nearTerm, if_neg hy, sub_zero]
    have hm2 : (R.range : ℝ) / 64 ≤ ((_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2 : ℕ) : ℝ) := by
      have : R.range ≤ 64 * (_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2) := by omega
      have h2 : (R.range : ℝ) ≤ 64 * ((_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have b := exp_le_siteWeight_of_far (R := R) hδ (by omega) hy
    have b1 := (h.abs_siteDensity_sub_le_of_agree (gd _ s11) (gd _ s01) (c 0)
      (fun x i hne => perturb_corner_fst c X W t t x i hne) y _ (by omega) hm2).trans b
    have b2 := (h.abs_siteDensity_sub_le_of_agree (gd _ s10) (gd _ s00) (c 0)
      (fun x i hne => perturb_corner_fst c X W t 0 x i hne) y _ (by omega) hm2).trans b
    have := abs_second_difference_le b1 b2
    have hs : 0 ≤ siteWeight R (c 0).1 y := by
      unfold siteWeight
      positivity
    linarith
theorem StepSettings.ChartSetting.NearFreePair.abs_first_difference_nearSum_le (p : s.NearFreePair τ ε θ W c X)
    (h : s.Hypotheses)
    (hδ : 0 < R.params.decayRate) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ τ) :
    |s.nearSum (c 0).1 c X W ![t, 0] - s.nearSum (c 0).1 c X W 0| ≤
      R.differenceConstant * Real.exp (-R.params.decayRate * R.range / 4) := by
  have hr := p.range_large h
  have hτ0 : 0 ≤ τ := ht0.trans ht
  have small : ∀ σ : Fin 2 → ℝ, (∀ l, σ l = 0 ∨ σ l = t) → ∀ l, |σ l| ≤ τ := by
    intro σ hσ l
    rcases hσ l with e | e <;> rw [e]
    · simpa using hτ0
    · rwa [abs_of_nonneg ht0]
  have s10 := small ![t, 0] (fun l => by fin_cases l <;> simp)
  have s00 := small ![0, 0] (fun l => by fin_cases l <;> simp)
  have gd : ∀ σ : Fin 2 → ℝ, (∀ l, |σ l| ≤ τ) → s.IsNear (θ + 4 * ε) (perturb c X σ W) := fun σ hσ =>
    h.isNear_perturb p.norm_exp_sub_one_le p.θ_lt.le p.isNear p.mem_free p.areUnitVectors hσ
  rw [← pair_zero]
  simp only [ChartSetting.nearSum_eq_sum]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun y _ => ?_)
    (sum_siteWeight_le (c 0).1 hδ))
  have hs : 0 ≤ siteWeight R (c 0).1 y := by
    unfold siteWeight
    positivity
  by_cases hy : _root_.YangMills.Construction.TorusFields.supDist y (c 0).1 ≤ R.range / 2
  · simp only [ChartSetting.nearTerm, if_pos hy]
    have b := exp_le_siteWeight_of_near (R := R) hδ (by omega) hy
    have b2 := (p.abs_siteDensity_sub_mirrorCentered_le h s10 hy).trans b
    have b4 := (p.abs_siteDensity_sub_mirrorCentered_le h s00 hy).trans b
    rw [abs_le] at *
    constructor <;> linarith [b2.1, b2.2, b4.1, b4.2]
  · simp only [ChartSetting.nearTerm, if_neg hy, sub_zero]
    have hm2 : (R.range : ℝ) / 64 ≤ ((_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2 : ℕ) : ℝ) := by
      have : R.range ≤ 64 * (_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2) := by omega
      have h2 : (R.range : ℝ) ≤ 64 * ((_root_.YangMills.Construction.TorusFields.supDist y (c 0).1 - 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have b := exp_le_siteWeight_of_far (R := R) hδ (by omega) hy
    have b2 := (h.abs_siteDensity_sub_le_of_agree (gd _ s10) (gd _ s00) (c 0)
      (fun x i hne => perturb_corner_fst c X W t 0 x i hne) y _ (by omega) hm2).trans b
    linarith
end YangMills.Construction
end
