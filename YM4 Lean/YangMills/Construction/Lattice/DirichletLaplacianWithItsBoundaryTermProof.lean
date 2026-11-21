import YangMills.Construction.Lattice.DifferenceOperatorsOfTheBareLattice
import YangMills.Construction.Lattice.DirichletLaplacianWithItsBoundaryTerm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators
variable {L m K : ℕ}
theorem meshSize_coe_ne_zero (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hpos : (0 : ℝ) < L := by linarith
  have hs : 0 < meshSize L j := zpow_pos hpos _
  have hs1 : meshSize L j ≤ 1 := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [meshSize, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hside : 2 ≤ torusSide L m := by
    have := one_le_pow₀ hL1 (n := m)
    simp only [torusSide]
    linarith
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  rw [zsmul_eq_mul] at hn
  rcases lt_trichotomy n 0 with h | h | h
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith
  · subst h
    simp at hn
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith
theorem unitStep_injective (hL : 2 ≤ L) {j : ℤ} (hj : 0 ≤ j) :
    Function.Injective (unitStep L m j) := by
  intro μ ν h
  by_contra hne
  have h' : Pi.single (M := fun _ => AddCircle (torusSide L m)) μ
        ((meshSize L j : ℝ) : AddCircle (torusSide L m)) μ =
      Pi.single (M := fun _ => AddCircle (torusSide L m)) ν
        ((meshSize L j : ℝ) : AddCircle (torusSide L m)) μ :=
    congrArg (fun s : Site L m j => (s : FourTorus L m) μ) h
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h'
  exact meshSize_coe_ne_zero hL hj h'
theorem indicatorMul_apply_of_mem {ι : Type} {X : Set ι} {i : ι} (h : i ∈ X) (f : ι → ℝ) :
    indicatorMul X f i = f i := Set.indicator_of_mem h f
theorem indicatorMul_apply_of_not_mem {ι : Type} {X : Set ι} {i : ι} (h : i ∉ X) (f : ι → ℝ) :
    indicatorMul X f i = 0 := Set.indicator_of_notMem h f
theorem interiorBonds_subset_framedBonds (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) :
    interiorBonds K Ω₀ ⊆ framedBonds K Ω₀ φ := by
  cases φ
  · exact fun b hb => hb
  · exact fun b hb => Or.inl hb.1
theorem siteProjection_zeroFormsOn (Ω₀ : Set (FourTorus L m)) (f : zeroFormsOn K Ω₀) :
    siteProjection K Ω₀ (f : ZeroForms L m K) = f := by
  have hidem : ∀ g : ZeroForms L m K,
      siteProjection K Ω₀ (siteProjection K Ω₀ g) = siteProjection K Ω₀ g := by
    intro g
    funext x
    by_cases h : x ∈ sitesOfRegion K Ω₀
    · exact indicatorMul_apply_of_mem h _
    · exact (indicatorMul_apply_of_not_mem h _).trans (indicatorMul_apply_of_not_mem h _).symm
  obtain ⟨g, hg⟩ := f.2
  rw [← hg]
  exact hidem g
theorem zeroFormsOn_apply_of_not_mem (Ω₀ : Set (FourTorus L m)) (f : zeroFormsOn K Ω₀)
    {x : BareSite L m K} (hx : x ∉ sitesOfRegion K Ω₀) : (f : ZeroForms L m K) x = 0 := by
  rw [← siteProjection_zeroFormsOn Ω₀ f]
  exact indicatorMul_apply_of_not_mem hx _
theorem grad_eq_bondProjection_add_frontierProjection (t : ℕ) (Ω₀ : Set (FourTorus L m))
    (φ : BondFrame) (f : zeroFormsOn K Ω₀) :
    grad t (f : ZeroForms L m K) =
      bondProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) +
        frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) := by
  funext b
  change grad t (f : ZeroForms L m K) b = bondProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b +
    frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b
  by_cases h1 : b ∈ framedBonds K Ω₀ φ
  · have e1 : bondProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b =
        grad t (f : ZeroForms L m K) b :=
      indicatorMul_apply_of_mem h1 _
    have e2 : frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b = 0 :=
      indicatorMul_apply_of_not_mem (fun h => h.2 h1) _
    rw [e1, e2, add_zero]
  · have e1 : bondProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b = 0 :=
      indicatorMul_apply_of_not_mem h1 _
    by_cases h2 : b ∈ starBonds K Ω₀
    · have e2 : frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b =
          grad t (f : ZeroForms L m K) b :=
        indicatorMul_apply_of_mem
          (show b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ from ⟨h2, h1⟩) _
      rw [e1, e2, zero_add]
    · have e2 : frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) b = 0 :=
        indicatorMul_apply_of_not_mem (fun h => h2 h.1) _
      have ht : b.1.source ∉ sitesOfRegion K Ω₀ := fun h => h2 (Or.inl h)
      have hh : b.1.target ∉ sitesOfRegion K Ω₀ := fun h => h2 (Or.inr h)
      have e3 : grad t (f : ZeroForms L m K) b = 0 := by
        change (finestMeshInLevelUnits L t)⁻¹ *
          ((f : ZeroForms L m K) b.1.target - (f : ZeroForms L m K) b.1.source) = 0
        rw [zeroFormsOn_apply_of_not_mem Ω₀ f ht, zeroFormsOn_apply_of_not_mem Ω₀ f hh]
        simp
      rw [e1, e2, e3, add_zero]
theorem dirichletLaplacian_eq_adjoint_comp_add_frontier (t : ℕ) (Ω₀ : Set (FourTorus L m))
    (φ : BondFrame) (f : zeroFormsOn K Ω₀) :
    (dirichletLaplacian K t Ω₀ f : ZeroForms L m K) =
      (dirichletGradAdjoint K t Ω₀ φ (dirichletGrad K t Ω₀ φ f) : ZeroForms L m K) +
        frontierOpN K t Ω₀ φ (f : ZeroForms L m K) := by
  change siteProjection K Ω₀ (gradAdjoint L m K t (grad t (siteProjection K Ω₀
      (f : ZeroForms L m K)))) =
    siteProjection K Ω₀ (gradAdjoint L m K t (bondProjection K Ω₀ φ
      (grad t (f : ZeroForms L m K)))) +
      siteProjection K Ω₀ (gradAdjoint L m K t
        (frontierProjection K Ω₀ φ (grad t (siteProjection K Ω₀ (f : ZeroForms L m K)))))
  rw [siteProjection_zeroFormsOn Ω₀ f, ← map_add, ← map_add,
    ← grad_eq_bondProjection_add_frontierProjection t Ω₀ φ f]
theorem not_source_and_target_mem {Ω₀ : Set (FourTorus L m)} {φ : BondFrame}
    {b : BareBond L m K} (hb : b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ) :
    ¬(b.1.source ∈ sitesOfRegion K Ω₀ ∧ b.1.target ∈ sitesOfRegion K Ω₀) :=
  fun h => hb.2 (interiorBonds_subset_framedBonds Ω₀ φ h)
open Classical in
theorem frontierProjection_grad_bondFrom (t : ℕ) (Ω₀ : Set (FourTorus L m)) (φ : BondFrame)
    (f : zeroFormsOn K Ω₀) {x : BareSite L m K} (hx : x ∈ sitesOfRegion K Ω₀) (μ : Fin 4) :
    frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) (bondFrom x μ) =
      if bondFrom x μ ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ then
        -((finestMeshInLevelUnits L t)⁻¹ * (f : ZeroForms L m K) x) else 0 := by
  split_ifs with h
  · have hh : x + unitStep L m (levelDepth K 0) μ ∉ sitesOfRegion K Ω₀ :=
      fun h' => not_source_and_target_mem h ⟨hx, h'⟩
    refine (indicatorMul_apply_of_mem h _).trans ?_
    change (finestMeshInLevelUnits L t)⁻¹ *
      ((f : ZeroForms L m K) (x + unitStep L m (levelDepth K 0) μ) - (f : ZeroForms L m K) x) = _
    rw [zeroFormsOn_apply_of_not_mem Ω₀ f hh]
    ring
  · exact indicatorMul_apply_of_not_mem h _
open Classical in
theorem frontierProjection_grad_bondFrom_sub (t : ℕ) (Ω₀ : Set (FourTorus L m))
    (φ : BondFrame) (f : zeroFormsOn K Ω₀) {x : BareSite L m K}
    (hx : x ∈ sitesOfRegion K Ω₀) (μ : Fin 4) :
    frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K))
        (bondFrom (x - unitStep L m (levelDepth K 0) μ) μ) =
      if bondFrom (x - unitStep L m (levelDepth K 0) μ) μ ∈
          starBonds K Ω₀ \ framedBonds K Ω₀ φ then
        (finestMeshInLevelUnits L t)⁻¹ * (f : ZeroForms L m K) x else 0 := by
  split_ifs with h
  · have htgt : (bondFrom (x - unitStep L m (levelDepth K 0) μ) μ).1.target = x :=
      sub_add_cancel x (unitStep L m (levelDepth K 0) μ)
    have hsrc : x - unitStep L m (levelDepth K 0) μ ∉ sitesOfRegion K Ω₀ :=
      fun h' => not_source_and_target_mem h ⟨h', by rw [htgt]; exact hx⟩
    refine (indicatorMul_apply_of_mem h _).trans ?_
    change (finestMeshInLevelUnits L t)⁻¹ *
      ((f : ZeroForms L m K) (bondFrom (x - unitStep L m (levelDepth K 0) μ) μ).1.target -
        (f : ZeroForms L m K) (x - unitStep L m (levelDepth K 0) μ)) = _
    rw [htgt, zeroFormsOn_apply_of_not_mem Ω₀ f hsrc]
    ring
  · exact indicatorMul_apply_of_not_mem h _
open Classical in
theorem card_frontier_bonds_at (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) {x : BareSite L m K}
    (hx : x ∈ sitesOfRegion K Ω₀) :
    (Nat.card {b : BareBond L m K //
        b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ ∧ (b.1.source = x ∨ b.1.target = x)} : ℝ) =
      ∑ μ : Fin 4, ((if bondFrom x μ ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ then (1 : ℝ) else 0) +
        (if bondFrom (x - unitStep L m (levelDepth K 0) μ) μ ∈
            starBonds K Ω₀ \ framedBonds K Ω₀ φ then (1 : ℝ) else 0)) := by
  have htgt : ∀ μ, (bondFrom (x - unitStep L m (levelDepth K 0) μ) μ).1.target = x :=
    fun μ => sub_add_cancel x (unitStep L m (levelDepth K 0) μ)
  let g : Fin 4 × Bool → BareBond L m K := fun p =>
    if p.2 then bondFrom x p.1 else bondFrom (x - unitStep L m (levelDepth K 0) p.1) p.1
  have hend : ∀ p, (g p).1.source = x ∨ (g p).1.target = x := by
    rintro ⟨μ, s⟩
    cases s
    · exact Or.inr (htgt μ)
    · exact Or.inl rfl
  have hloop : ∀ (μ ν : Fin 4), bondFrom x μ = bondFrom (x - unitStep L m (levelDepth K 0) ν) ν →
      bondFrom x μ ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ → False := by
    intro μ ν e hb
    refine not_source_and_target_mem hb ⟨hx, ?_⟩
    rw [e, htgt ν]
    exact hx
  let e : {p : Fin 4 × Bool // g p ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ} ≃
      {b : BareBond L m K //
        b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ ∧ (b.1.source = x ∨ b.1.target = x)} :=
    Equiv.ofBijective (fun p => ⟨g p.1, p.2, hend p.1⟩) (by
      constructor
      · rintro ⟨⟨μ, s⟩, hp⟩ ⟨⟨ν, s'⟩, hq⟩ h
        have h' : g (μ, s) = g (ν, s') := congrArg Subtype.val h
        cases s <;> cases s'
        · have ht : x - unitStep L m (levelDepth K 0) μ = x - unitStep L m (levelDepth K 0) ν :=
            congrArg (fun b : BareBond L m K => b.1.source) h'
          have : μ = ν := hs (sub_right_injective ht)
          subst this
          rfl
        · exact (hloop ν μ h'.symm hq).elim
        · exact (hloop μ ν h' hp).elim
        · have ht : x + unitStep L m (levelDepth K 0) μ = x + unitStep L m (levelDepth K 0) ν :=
            congrArg (fun b : BareBond L m K => b.1.target) h'
          have : μ = ν := hs (add_left_cancel ht)
          subst this
          rfl
      · rintro ⟨⟨β, μ, hμ⟩, hC, hb⟩
        rcases hb with hb | hb
        · have hb' : β.source = x := hb
          have hg : g (μ, true) = ⟨β, μ, hμ⟩ := by
            refine Subtype.ext (Bond.ext hb'.symm ?_)
            change x + unitStep L m (levelDepth K 0) μ = β.target
            rw [← hμ, ← hb']
            abel
          exact ⟨⟨(μ, true), hg ▸ hC⟩, Subtype.ext hg⟩
        · have hb' : β.target = x := hb
          have hg : g (μ, false) = ⟨β, μ, hμ⟩ := by
            refine Subtype.ext (Bond.ext ?_ ?_)
            · change x - unitStep L m (levelDepth K 0) μ = β.source
              rw [← hμ, ← hb']
              abel
            · exact (htgt μ).trans hb'.symm
          exact ⟨⟨(μ, false), hg ▸ hC⟩, Subtype.ext hg⟩)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_bool]
  rfl
theorem frontierOpN_apply {t : ℕ}
    (hform : ∀ (A : OneForms L m K) (x : BareSite L m K), gradAdjoint L m K t A x =
      ∑ μ, (finestMeshInLevelUnits L t)⁻¹ *
        (axisComponent A μ (x - unitStep L m (levelDepth K 0) μ) - axisComponent A μ x))
    (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) (f : zeroFormsOn K Ω₀) (x : BareSite L m K) :
    frontierOpN K t Ω₀ φ (f : ZeroForms L m K) x =
      (finestMeshInLevelUnits L t ^ 2)⁻¹ * (Nat.card {b : BareBond L m K //
        b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ ∧ (b.1.source = x ∨ b.1.target = x)} : ℝ) *
        (f : ZeroForms L m K) x := by
  classical
  change siteProjection K Ω₀ (gradAdjoint L m K t
    (frontierProjection K Ω₀ φ (grad t (siteProjection K Ω₀ (f : ZeroForms L m K))))) x = _
  rw [siteProjection_zeroFormsOn Ω₀ f]
  by_cases hx : x ∈ sitesOfRegion K Ω₀
  · refine (indicatorMul_apply_of_mem hx _).trans ?_
    rw [hform, card_frontier_bonds_at hs Ω₀ φ hx, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    change (finestMeshInLevelUnits L t)⁻¹ *
        (frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K))
            (bondFrom (x - unitStep L m (levelDepth K 0) μ) μ) -
          frontierProjection K Ω₀ φ (grad t (f : ZeroForms L m K)) (bondFrom x μ)) = _
    rw [frontierProjection_grad_bondFrom_sub t Ω₀ φ f hx μ,
      frontierProjection_grad_bondFrom t Ω₀ φ f hx μ]
    split_ifs <;> ring
  · rw [zeroFormsOn_apply_of_not_mem Ω₀ f hx, mul_zero]
    exact indicatorMul_apply_of_not_mem hx _
theorem frontierOpN_apply_of_not_mem {t : ℕ}
    (hform : ∀ (A : OneForms L m K) (x : BareSite L m K), gradAdjoint L m K t A x =
      ∑ μ, (finestMeshInLevelUnits L t)⁻¹ *
        (axisComponent A μ (x - unitStep L m (levelDepth K 0) μ) - axisComponent A μ x))
    (hs : Function.Injective (unitStep L m (levelDepth K 0)))
    (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) (f : zeroFormsOn K Ω₀) (x : BareSite L m K)
    (hx : x ∉ frontierSites K Ω₀) : frontierOpN K t Ω₀ φ (f : ZeroForms L m K) x = 0 := by
  rw [frontierOpN_apply hform hs]
  by_cases hS : x ∈ sitesOfRegion K Ω₀
  · have hempty : IsEmpty {b : BareBond L m K //
        b ∈ starBonds K Ω₀ \ framedBonds K Ω₀ φ ∧ (b.1.source = x ∨ b.1.target = x)} := by
      refine ⟨fun b => hx ⟨hS, b.1, ⟨b.2.1.1, fun hin => b.2.1.2
        (interiorBonds_subset_framedBonds Ω₀ φ hin)⟩, ?_⟩⟩
      rcases b.2.2 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    rw [Nat.card_of_isEmpty]
    simp
  · rw [zeroFormsOn_apply_of_not_mem Ω₀ f hS, mul_zero]
theorem statement_holds (h : DirichletOperators.BareLatticeOperators.Statement) : Statement := by
  intro S φ
  obtain ⟨-, hf, -, -, hΩ⟩ := h S.toBaseParameters
  have hform := hf.2.1
  have hs : Function.Injective (unitStep S.L S.m (levelDepth S.K 0)) :=
    unitStep_injective (by have := S.three_le_L; omega) (by simp [levelDepth])
  refine ⟨fun f => dirichletLaplacian_eq_adjoint_comp_add_frontier _ _ φ f, fun f x => ?_,
    fun hφ => ?_, fun f x hx => ?_⟩
  · rw [S.toBaseParameters.levelMeshRatio_zero]
    exact frontierOpN_apply hform hs _ φ f x
  · subst hφ
    have hc := (hΩ (S.region 0)).1.2.1
    simp only [frontierOpN, hc, LinearMap.zero_comp, LinearMap.comp_zero]
  · exact frontierOpN_apply_of_not_mem hform hs _ φ f x hx
end YangMills.Construction.PeriodicLattice.DirichletLaplacianSplitsOffBoundary
