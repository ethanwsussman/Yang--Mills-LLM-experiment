import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPaths
import YangMills.Construction.Towers.LinearMapsOnFormsSupportedOnPivotBondsOfTheWholeLattice
import YangMills.Construction.Towers.PivotBondOfABondOfEitherOrientationAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open scoped Classical
namespace YangMills.Construction.Tower.FullSpace
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Tower.TrivialLinearization (pivotScale)
namespace PivotSupportedForms
variable {a a' : ℝ} {L : ℕ}
theorem sum_pi_single_apply (ν : Fin 4 → ℤ) (a' : ℝ) (ρ : Fin 4) :
    (∑ μ, (Pi.single μ ((ν μ : ℝ) * a') : AmbientSpace)) ρ = (ν ρ : ℝ) * a' := by
  simp [Finset.sum_apply, Pi.single_apply]
theorem toFiner_coe (hs : a = L * a') (y : InfiniteLattice.LatticePoint a) :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by
  have hex : ∃ x : InfiniteLattice.LatticePoint a', (x : AmbientSpace) = y := by
    obtain ⟨n, hn⟩ := y.2
    refine ⟨⟨(y : AmbientSpace), fun μ => n μ * L, fun μ => ?_⟩, rfl⟩
    rw [hn μ, hs]
    push_cast
    ring
  exact Classical.epsilon_spec hex
theorem axis_eq_of_axisStep_eq (ha : a ≠ 0) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν ∨
      InfiniteLattice.axisStep a μ = -InfiniteLattice.axisStep a ν) : μ = ν := by
  by_contra hne
  have hv : (InfiniteLattice.axisStep a μ : AmbientSpace) μ = a := by
    simp [InfiniteLattice.axisStep]
  have hw : (InfiniteLattice.axisStep a ν : AmbientSpace) μ = 0 := by
    simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hne]
  rcases h with h | h
  · rw [h, hw] at hv
    exact ha hv.symm
  · rw [h] at hv
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, hw, neg_zero] at hv
    exact ha hv.symm
theorem ne_pivotLink_of_mem_cube (ha : a ≠ 0)
    (hdisj : Pairwise (Function.onFun Disjoint fun y : InfiniteLattice.LatticePoint a => cube L a' y))
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    {y : InfiniteLattice.LatticePoint a} {b : InfiniteLattice.Link a'}
    (h₁ : (b.initial : AmbientSpace) ∈ cube L a' y) (h₂ : (b.terminal : AmbientSpace) ∈ cube L a' y)
    (c : InfiniteLattice.Link a) (hc : c.IsPositivelyOriented) : b ≠ pivotLink L a' c := by
  intro hb
  have hcor : b ∈ linkCorridor L a' c := by
    rw [hb]
    exact (hpiv c).isPivotLink.1
  have e₁ : y = c.initial := by
    by_contra hne
    exact Set.disjoint_left.mp (show Disjoint _ _ from hdisj hne) h₁ hcor.1
  have e₂ : y = c.terminal := by
    by_contra hne
    exact Set.disjoint_left.mp (show Disjoint _ _ from hdisj hne) h₂ hcor.2
  obtain ⟨μ, hμ⟩ := hc
  have h0 : InfiniteLattice.axisStep a μ = 0 := by rw [← hμ, ← e₁, ← e₂, sub_self]
  have hv := congrArg (fun s : InfiniteLattice.LatticePoint a => (s : AmbientSpace) μ) h0
  simp [InfiniteLattice.axisStep] at hv
  exact ha hv
theorem eq_zero_of_mem_cube (ha : a ≠ 0)
    (hdisj : Pairwise (Function.onFun Disjoint fun y : InfiniteLattice.LatticePoint a => cube L a' y))
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace a')
    (hsupp : ∀ b : InfiniteLattice.Link a', b.IsPositivelyOriented →
      (∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → b ≠ pivotLink L a' c) → B b = 0)
    {y : InfiniteLattice.LatticePoint a} {b : InfiniteLattice.Link a'}
    (h₁ : (b.initial : AmbientSpace) ∈ cube L a' y)
    (h₂ : (b.terminal : AmbientSpace) ∈ cube L a' y) : B b = 0 := by
  obtain ⟨-, hrev⟩ := hB
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact hsupp b ⟨μ, h⟩ (ne_pivotLink_of_mem_cube ha hdisj hpiv h₁ h₂)
  · have hr : b.opposite.IsPositivelyOriented := ⟨μ, by
      change b.initial - b.terminal = _
      rw [← neg_sub, h, neg_neg]⟩
    have h0 : B b.opposite = 0 :=
      hsupp b.opposite hr (ne_pivotLink_of_mem_cube (b := b.opposite) ha hdisj hpiv h₂ h₁)
    have h3 := hrev b
    rw [h0] at h3
    exact neg_eq_zero.mp h3.symm
theorem contourAverage_eq_zero {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'}
    (h : ∀ Γ ∈ contourSet L y x, ∀ b ∈ Γ, B b = 0) : contourAverage L B y x = 0 := by
  unfold contourAverage
  rw [Finset.sum_eq_zero, smul_zero]
  intro σ _
  refine List.sum_eq_zero fun v hv => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
  exact h _ ⟨σ, rfl⟩ b hb
theorem sumAlong_forwardSteps (B : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    sumAlong B (forwardSteps x μ n) =
      ∑ i ∈ Finset.range n,
        B (InfiniteLattice.Link.forwardFrom (x + i • InfiniteLattice.axisStep a μ) μ) := by
  induction n generalizing x with
  | zero => simp [sumAlong, forwardSteps]
  | succ n ih =>
    have h := ih (x + InfiniteLattice.axisStep a μ)
    rw [Finset.sum_range_succ']
    simp only [sumAlong, forwardSteps, List.map_cons, List.sum_cons] at h ⊢
    rw [h, zero_nsmul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [succ_nsmul, add_assoc, add_comm (i • InfiniteLattice.axisStep a μ)]
theorem axis_eq_of_zsmul_axisStep_eq (hL : L ≠ 0) (ha' : a' ≠ 0) {μ ν : Fin 4} {t : ℤ}
    (h : t • InfiniteLattice.axisStep a' ν = (L : ℤ) • InfiniteLattice.axisStep a' μ) :
    ν = μ ∧ t = L := by
  have hc : ∀ ρ, (t : ℝ) * (Pi.single ν a' : AmbientSpace) ρ =
      (L : ℝ) * (Pi.single μ a' : AmbientSpace) ρ := by
    intro ρ
    have h1 := congrArg (fun s : InfiniteLattice.LatticePoint a' => (s : AmbientSpace) ρ) h
    simpa [InfiniteLattice.axisStep] using h1
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hν : ν = μ := by
    by_contra hne
    have h1 := hc μ
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne), mul_zero] at h1
    exact (mul_ne_zero hL' ha') h1.symm
  subst hν
  refine ⟨rfl, ?_⟩
  have h1 := hc ν
  rw [Pi.single_eq_same] at h1
  have h2 : (t : ℝ) = L := mul_right_cancel₀ ha' h1
  exact_mod_cast h2
theorem crossingPath_eq_forwardSteps (hL : L ≠ 0) (ha' : a' ≠ 0) (hs : a = L * a')
    {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep a μ)
    (x : InfiniteLattice.LatticePoint a') :
    crossingPath c x = forwardSteps x μ L := by
  have hd : shifted c x - x = (L : ℤ) • InfiniteLattice.axisStep a' μ := by
    apply Subtype.ext
    funext ρ
    have h1 : ((toFiner a' (c.terminal - c.initial) : InfiniteLattice.LatticePoint a') :
        AmbientSpace) = Pi.single μ a := by
      rw [toFiner_coe hs, hc]
      rfl
    have hv : ((shifted c x : InfiniteLattice.LatticePoint a') : AmbientSpace) ρ =
        (x : AmbientSpace) ρ + (Pi.single μ a : AmbientSpace) ρ := by
      change (x : AmbientSpace) ρ +
        ((toFiner a' (c.terminal - c.initial) : InfiniteLattice.LatticePoint a') :
          AmbientSpace) ρ = _
      rw [h1]
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, hv, AddSubgroup.coe_zsmul, Pi.smul_apply,
      InfiniteLattice.axisStep, zsmul_eq_mul]
    by_cases hρ : ρ = μ
    · subst hρ
      simp only [Pi.single_eq_same, hs]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne hρ]
  have hex : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x (shifted c x) q.1 q.2 := ⟨(μ, L), hd⟩
  have hq : shifted c x - x = hex.choose.2 • InfiniteLattice.axisStep a' hex.choose.1 :=
    hex.choose_spec
  obtain ⟨h1, h2⟩ := axis_eq_of_zsmul_axisStep_eq hL ha' (hq.symm.trans hd)
  unfold crossingPath axisPath
  rw [dif_pos hex, h1, h2]
  simp [signedSteps]
theorem shifted_mem_cube (hs : a = L * a') (c : InfiniteLattice.Link a)
    {x : InfiniteLattice.LatticePoint a'} (hx : (x : AmbientSpace) ∈ cube L a' c.initial) :
    ((shifted c x : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈ cube L a' c.terminal := by
  obtain ⟨n, hn, hxe⟩ := hx
  refine ⟨n, hn, ?_⟩
  have h1 : ((shifted c x : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
    change (x : AmbientSpace) +
      ((toFiner a' (c.terminal - c.initial) : InfiniteLattice.LatticePoint a') : AmbientSpace) = _
    rw [toFiner_coe hs, AddSubgroup.coe_sub]
  rw [h1, hxe]
  abel
theorem eq_zero_of_mul_eq_of_small {h : ℕ} (hh : L = 2 * h + 1) {d e : ℤ} (h₁ : d * L = e)
    (h₂ : -(2 * (h : ℤ)) ≤ e ∧ e ≤ 2 * h) : d = 0 := by
  have hz : e = 0 := Int.eq_zero_of_abs_lt_dvd (m := (L : ℤ)) ⟨d, by rw [← h₁]; ring⟩ (by
    rw [abs_lt]
    subst hh
    push_cast
    constructor <;> omega)
  have h0 : d * L = 0 := h₁.trans hz
  rcases mul_eq_zero.mp h0 with h3 | h3
  · exact h3
  · subst hh
    push_cast at h3
    omega
theorem abs_index_le {h : ℕ} (hh : L = 2 * h + 1) {n : ℤ} (hn : 2 * |n| ≤ (L : ℤ) ^ 1 - 1) :
    -(h : ℤ) ≤ n ∧ n ≤ h := by
  subst hh
  rw [pow_one] at hn
  push_cast at hn
  rcases abs_cases n with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] at hn <;> constructor <;> omega
theorem pivotLink_displacement (ha : a ≠ 0)
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep a μ) :
    (pivotLink L a' c).terminal - (pivotLink L a' c).initial = InfiniteLattice.axisStep a' μ := by
  obtain ⟨ν, hν⟩ := (hpiv c).isPositivelyOriented_iff.mpr ⟨μ, hc⟩
  have hd : LinkHasAxis c ν := ((hpiv c).linkHasAxis_iff ν).mp (Or.inl hν)
  have hμν : μ = ν := by
    rcases hd with h | h
    · exact axis_eq_of_axisStep_eq ha (Or.inl (hc.symm.trans h))
    · exact axis_eq_of_axisStep_eq ha (Or.inr (hc.symm.trans h))
  rw [hμν]
  exact hν
theorem apply_forwardFrom_of_mem_cube (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : a = L * a') {h : ℕ}
    (hh : L = 2 * h + 1)
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    (htail : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4),
      c.terminal - c.initial = InfiniteLattice.axisStep a μ →
        ((pivotLink L a' c).initial : AmbientSpace) =
          (c.initial : AmbientSpace) + Pi.single μ ((((L : ℝ) - 1) / 2) * a'))
    {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hsupp : ∀ b : InfiniteLattice.Link a', b.IsPositivelyOriented →
      (∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → b ≠ pivotLink L a' c) → B b = 0)
    {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep a μ)
    {x : InfiniteLattice.LatticePoint a'} (hx : (x : AmbientSpace) ∈ cube L a' c.initial)
    {i : ℕ} (hi : i < L) :
    B (InfiniteLattice.Link.forwardFrom (x + i • InfiniteLattice.axisStep a' μ) μ) =
      if x + i • InfiniteLattice.axisStep a' μ = (pivotLink L a' c).initial then
        B (pivotLink L a' c) else 0 := by
  have hfwd : pivotLink L a' c =
      InfiniteLattice.Link.forwardFrom (pivotLink L a' c).initial μ :=
    InfiniteLattice.Link.ext rfl (eq_add_of_sub_eq' (pivotLink_displacement ha hpiv hc))
  by_cases hz : x + i • InfiniteLattice.axisStep a' μ = (pivotLink L a' c).initial
  · rw [if_pos hz, hz, ← hfwd]
  · rw [if_neg hz]
    refine hsupp _ ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩ fun c' hc' heq => hz ?_
    obtain ⟨ν, hν⟩ := hc'
    have hp' := pivotLink_displacement ha hpiv hν
    rw [← heq] at hp'
    have hμν : μ = ν :=
      axis_eq_of_axisStep_eq ha' (Or.inl (by simpa [InfiniteLattice.Link.forwardFrom] using hp'))
    subst hμν
    have hhalf : ((L : ℝ) - 1) / 2 = h := by
      subst hh
      push_cast
      ring
    have ht := htail c' μ hν
    rw [← heq, hhalf] at ht
    obtain ⟨n, hn, hxe⟩ := hx
    obtain ⟨p, hp⟩ := c.initial.2
    obtain ⟨q, hq⟩ := c'.initial.2
    have key : ∀ ρ, p ρ = q ρ := by
      intro ρ
      have hρ := congrFun ht ρ
      have hz' : ((InfiniteLattice.Link.forwardFrom (x + i • InfiniteLattice.axisStep a' μ)
          μ).initial : AmbientSpace) ρ =
          (x : AmbientSpace) ρ + (i : ℝ) * (Pi.single μ a' : AmbientSpace) ρ := by
        simp [InfiniteLattice.Link.forwardFrom, InfiniteLattice.axisStep]
      have hx' : (x : AmbientSpace) ρ = (p ρ : ℝ) * a + (n ρ : ℝ) * a' := by
        rw [hxe, Pi.add_apply, sum_pi_single_apply, hp]
      rw [hz', hx', Pi.add_apply, hq, hs] at hρ
      have hb := abs_index_le hh (hn ρ)
      have hi' : (i : ℤ) ≤ 2 * h := by omega
      by_cases hμ : ρ = μ
      · subst hμ
        simp only [Pi.single_eq_same] at hρ
        have hre : (((p ρ - q ρ) * L : ℤ) : ℝ) * a' = (((h : ℤ) - i - n ρ : ℤ) : ℝ) * a' := by
          push_cast
          linarith
        have hint : (p ρ - q ρ) * (L : ℤ) = (h : ℤ) - i - n ρ := by
          exact_mod_cast mul_right_cancel₀ ha' hre
        have := eq_zero_of_mul_eq_of_small hh hint (by omega)
        omega
      · simp only [Pi.single_eq_of_ne hμ, mul_zero, add_zero] at hρ
        have hre : (((p ρ - q ρ) * L : ℤ) : ℝ) * a' = ((-n ρ : ℤ) : ℝ) * a' := by
          push_cast
          linarith
        have hint : (p ρ - q ρ) * (L : ℤ) = -n ρ := by
          exact_mod_cast mul_right_cancel₀ ha' hre
        have := eq_zero_of_mul_eq_of_small hh hint (by omega)
        omega
    have htt : c'.initial = c.initial := Subtype.ext (funext fun ρ => by rw [hq, hp, key ρ])
    have hcc : c' = c := InfiniteLattice.Link.ext htt (by
      rw [eq_add_of_sub_eq' hν, eq_add_of_sub_eq' hc, htt])
    rw [hcc] at heq
    exact congrArg InfiniteLattice.Link.initial heq
theorem inverseFourthPowerWeight_mul (hL : L ≠ 0) :
    PeriodicLattice.inverseFourthPowerWeight L * (L : ℂ) = pivotScale L := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have h1 : (L : ℝ) ^ (-4 : ℤ) * (L : ℝ) = (L : ℝ) ^ (-3 : ℤ) := by
    rw [show (-3 : ℤ) = -4 + 1 by norm_num, zpow_add₀ hL', zpow_one]
  unfold PeriodicLattice.inverseFourthPowerWeight pivotScale
  rw [← h1]
  push_cast
  rfl
theorem crossingSmoothing_eq (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : a = L * a') {h : ℕ}
    (hh : L = 2 * h + 1)
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    (htail : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4),
      c.terminal - c.initial = InfiniteLattice.axisStep a μ →
        ((pivotLink L a' c).initial : AmbientSpace) =
          (c.initial : AmbientSpace) + Pi.single μ ((((L : ℝ) - 1) / 2) * a'))
    {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2}
    (hsupp : ∀ b : InfiniteLattice.Link a', b.IsPositivelyOriented →
      (∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → b ≠ pivotLink L a' c) → B b = 0)
    {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep a μ) :
    crossingSmoothing L B c = pivotScale L • B (pivotLink L a' c) := by
  have hL : L ≠ 0 := by omega
  have hhalf : ((L : ℝ) - 1) / 2 = h := by
    subst hh
    push_cast
    ring
  have hinj : ∀ i i' : ℕ, i • InfiniteLattice.axisStep a' μ = i' • InfiniteLattice.axisStep a' μ →
      i = i' := by
    intro i i' he
    have h1 := congrArg (fun s : InfiniteLattice.LatticePoint a' => (s : AmbientSpace) μ) he
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, InfiniteLattice.axisStep, Pi.single_eq_same,
      nsmul_eq_mul] at h1
    have h2 : (i : ℝ) = i' := mul_right_cancel₀ ha' h1
    exact_mod_cast h2
  set t₀ := (pivotLink L a' c).initial with ht₀
  let φ : ℕ → InfiniteLattice.LatticePoint a' := fun i => t₀ - i • InfiniteLattice.axisStep a' μ
  let F : Finset (InfiniteLattice.LatticePoint a') := (Finset.range L).image φ
  have hφ : Set.InjOn φ (Finset.range L : Set ℕ) := by
    intro i _ i' _ he
    exact hinj i i' (sub_right_injective he)
  have hFS : ∀ x ∈ F, x ∈ cubeVertices L a' c.initial := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i < L := Finset.mem_range.mp hi
    refine ⟨Pi.single μ ((h : ℤ) - i), fun ρ => ?_, ?_⟩
    · by_cases hρ : ρ = μ
      · subst hρ
        rw [Pi.single_eq_same, pow_one]
        rcases abs_cases ((h : ℤ) - i) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> omega
      · rw [Pi.single_eq_of_ne hρ, pow_one]
        simp only [abs_zero, mul_zero]
        omega
    · funext ρ
      have h1 := congrFun (htail c μ hc) ρ
      rw [hhalf] at h1
      rw [Pi.add_apply, sum_pi_single_apply]
      have h2 : ((φ i : InfiniteLattice.LatticePoint a') : AmbientSpace) ρ =
          (t₀ : AmbientSpace) ρ - (i : ℝ) * (Pi.single μ a' : AmbientSpace) ρ := by
        simp [φ, InfiniteLattice.axisStep]
      rw [h2, h1, Pi.add_apply]
      by_cases hρ : ρ = μ
      · subst hρ
        simp only [Pi.single_eq_same]
        push_cast
        ring
      · simp [Pi.single_eq_of_ne hρ]
  have hT : ∀ x ∈ cubeVertices L a' c.initial, edgeFormPathSum B (crossingPath c x) =
      if x ∈ F then B (pivotLink L a' c) else 0 := by
    intro x hx
    have hsum : edgeFormPathSum B (crossingPath c x) = ∑ i ∈ Finset.range L,
        if x + i • InfiniteLattice.axisStep a' μ = t₀ then B (pivotLink L a' c) else 0 := by
      rw [edgeFormPathSum, crossingPath_eq_forwardSteps hL ha' hs hc, sumAlong_forwardSteps]
      exact Finset.sum_congr rfl fun i hi =>
        apply_forwardFrom_of_mem_cube ha ha' hs hh hpiv htail hsupp hc hx
          (Finset.mem_range.mp hi)
    rw [hsum]
    by_cases hxF : x ∈ F
    · rw [if_pos hxF]
      obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hxF
      rw [Finset.sum_eq_single i₀]
      · simp [φ]
      · intro i _ hne
        rw [if_neg]
        intro he
        apply hne
        apply hinj
        have h3 : t₀ - i₀ • InfiniteLattice.axisStep a' μ + i • InfiniteLattice.axisStep a' μ =
            t₀ := he
        have h4 : i • InfiniteLattice.axisStep a' μ - i₀ • InfiniteLattice.axisStep a' μ =
            (t₀ - i₀ • InfiniteLattice.axisStep a' μ + i • InfiniteLattice.axisStep a' μ) - t₀ := by
          abel
        rw [h3, sub_self] at h4
        exact sub_eq_zero.mp h4
      · intro hn
        exact absurd hi₀ hn
    · rw [if_neg hxF]
      refine Finset.sum_eq_zero fun i hi => if_neg fun he => hxF ?_
      exact Finset.mem_image.mpr ⟨i, hi, by simp [φ, ← he]⟩
  have hinter : cubeVertices L a' c.initial ∩
      Function.support (fun x => if x ∈ F then B (pivotLink L a' c) else 0) =
      (F : Set (InfiniteLattice.LatticePoint a')) ∩
        Function.support (fun x => if x ∈ F then B (pivotLink L a' c) else 0) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hn
      exact h2 (if_neg hn)
    · rintro ⟨h1, h2⟩
      exact ⟨hFS x h1, h2⟩
  have hcard : F.card = L := by
    rw [Finset.card_image_of_injOn hφ, Finset.card_range]
  unfold crossingSmoothing
  rw [finsum_mem_congr rfl hT, finsum_mem_eq_sum_of_inter_support_eq _ hinter,
    Finset.sum_congr rfl (fun x hx => if_pos hx), Finset.sum_const, hcard,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inverseFourthPowerWeight_mul hL]
theorem main (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : a = L * a') {h : ℕ} (hh : L = 2 * h + 1)
    (hdisj : Pairwise (Function.onFun Disjoint fun y : InfiniteLattice.LatticePoint a => cube L a' y))
    (hcover : (⋃ y : InfiniteLattice.LatticePoint a, cube L a' y) =
      (InfiniteLattice.latticeSubgroup a' : Set AmbientSpace))
    (hcont : ∀ (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a'),
      (x : AmbientSpace) ∈ cube L a' y → ∀ Γ ∈ contourSet L y x, ∀ b ∈ Γ,
        (b.initial : AmbientSpace) ∈ cube L a' y ∧ (b.terminal : AmbientSpace) ∈ cube L a' y)
    (hpiv : ∀ c : InfiniteLattice.Link a, PivotLinkProperties L a' c)
    (htail : ∀ (c : InfiniteLattice.Link a) (μ : Fin 4),
      c.terminal - c.initial = InfiniteLattice.axisStep a μ →
        ((pivotLink L a' c).initial : AmbientSpace) =
          (c.initial : AmbientSpace) + Pi.single μ ((((L : ℝ) - 1) / 2) * a'))
    {B : InfiniteLattice.Link a' → Matrices.ComplexMatrix2} (hB : B ∈ edgeFormSpace a')
    (hsupp : ∀ b : InfiniteLattice.Link a', b.IsPositivelyOriented →
      (∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented → b ≠ pivotLink L a' c) → B b = 0) :
    cubeContourAverage (a := a) L B = 0 ∧ fineOnlyContourAverage (a := a) L B = 0 ∧
      ∀ c : InfiniteLattice.Link a, c.IsPositivelyOriented →
        linearSmoothing L B c = crossingSmoothing L B c ∧
          crossingSmoothing L B c = pivotScale L • B (pivotLink L a' c) := by
  have hzero : ∀ (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a'),
      (x : AmbientSpace) ∈ cube L a' y → contourAverage L B y x = 0 := fun y x hx =>
    contourAverage_eq_zero fun Γ hΓ b hb =>
      eq_zero_of_mem_cube ha hdisj hpiv hB hsupp (hcont y x hx Γ hΓ b hb).1
        (hcont y x hx Γ hΓ b hb).2
  refine ⟨?_, ?_, ?_⟩
  · funext y
    change PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ cubeVertices L a' y, contourAverage L B y x = 0
    have h0 : ∑ᶠ x ∈ cubeVertices L a' y, contourAverage L B y x =
        ∑ᶠ x ∈ cubeVertices L a' y, (0 : Matrices.ComplexMatrix2) :=
      finsum_mem_congr rfl fun x hx => hzero y x hx
    rw [h0]
    simp
  · funext x
    have hex : ∃ y : InfiniteLattice.LatticePoint a,
        x.1 ∈ cubeVertices L a' y ∧ (x.1 : AmbientSpace) ≠ y := by
      have hm : (x.1 : AmbientSpace) ∈ ⋃ y : InfiniteLattice.LatticePoint a, cube L a' y := by
        rw [hcover]
        exact x.1.2
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hm
      exact ⟨y, hy, fun e => x.2 (e ▸ y.2)⟩
    exact hzero _ _ (Classical.epsilon_spec hex).1
  · rintro c ⟨μ, hμ⟩
    refine ⟨?_, crossingSmoothing_eq ha ha' hs hh hpiv htail hsupp hμ⟩
    unfold linearSmoothing crossingSmoothing
    congr 1
    refine finsum_mem_congr rfl fun x hx => ?_
    rw [hzero c.initial x hx, hzero c.terminal _ (shifted_mem_cube hs c hx), zero_add, sub_zero]
    rfl
end PivotSupportedForms
open PivotSupportedForms in
theorem pivotFormsStatement_holds
    (hY : CubesCorridorsPivotEdgesAndPaths)
    (hP : PivotLinkOfAnyOrientation) :
    LinearizationFacts.pivotFormsStatement := by
  intro L hL k j hjk B hB hsupp
  obtain ⟨h, hh⟩ := hL.1
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this
  have ha' : meshAt L k j ≠ 0 := (zpow_pos hLpos _).ne'
  have ha : meshAt L k (j + 1) ≠ 0 := (zpow_pos hLpos _).ne'
  have hs : meshAt L k (j + 1) = L * meshAt L k j := by
    unfold meshAt
    rw [← zpow_one_add₀ hLpos.ne']
    congr 1
    push_cast
    ring
  obtain ⟨hO, -, hS, hC⟩ := hY L hL k (j + 1) 1 (by omega) (by omega) (by omega) le_rfl (by omega)
  have hpiv : ∀ c : Edge L k (j + 1), PivotLinkProperties L (meshAt L k j) c :=
    hP L hL k j hjk
  refine main ha ha' hs (by omega) hO.pairwise_disjoint_cube hO.iUnion_cube ?_ hpiv ?_ hB hsupp
  · intro y x hx Γ hΓ b hb
    exact ⟨hC.contour_vertex_mem y x hx Γ hΓ b.initial (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
      hC.contour_vertex_mem y x hx Γ hΓ b.terminal (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
  · intro c μ hc
    have hv := (hpiv c).isPivotLink
    exact hS.corridorEdge_initial c μ hc _ ⟨hv.2, hv.1⟩
end YangMills.Construction.Tower.FullSpace
