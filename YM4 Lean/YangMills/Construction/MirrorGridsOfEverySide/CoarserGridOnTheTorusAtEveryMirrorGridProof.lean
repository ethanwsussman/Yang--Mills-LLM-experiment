import YangMills.Construction.MirrorGridsOfEverySide.CellsOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnSpaceAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.CoarserGridOnTheTorusAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsAtEveryMirrorGrid
import YangMills.Construction.MirrorGridsOfEverySide.GroupOnTheCellsOfTheTorusAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
namespace CoarseningOnTorus
variable {D : GridSetup}
theorem cellSide_pos (g : ReflectionGrid D) : 0 < g.cellSide :=
  zpow_pos (by linarith [D.one_lt_factor]) _
theorem cellCentre_mem_cell (g : ReflectionGrid D) (k : Fin 4 → ℤ) : g.cellCentre k ∈ g.cell k := by
  intro μ
  have hs := cellSide_pos g
  show g.origin μ + g.cellSide * k μ + g.cellSide / 2 - (g.origin μ + g.cellSide * k μ) ∈ Icc 0 g.cellSide
  constructor <;> linarith
theorem int_eq_zero_of_mul_bounds {N t : ℤ} (hN : 0 < N) (h₁ : -N < N * t) (h₂ : N * t < N) :
    t = 0 := by
  have a : t < 1 := lt_of_mul_lt_mul_left (by linarith) hN.le
  have b : -1 < t := lt_of_mul_lt_mul_left (by linarith) hN.le
  omega
theorem exists_origin_shift {g g' : ReflectionGrid D} (h : g'.wallSet ⊆ g.wallSet) :
    ∃ u : Fin 4 → ℤ, ∀ μ, g'.origin μ = g.origin μ + g.cellSide * u μ := by
  have key : ∀ μ, ∃ i : ℤ, g'.origin μ = g.origin μ + g.cellSide * i := by
    intro μ
    obtain ⟨⟨ν, k⟩, hνk⟩ := h ⟨(μ, 0), rfl⟩
    have hνk' : g.wall ν k = g'.wall μ 0 := hνk
    by_cases hν : ν = μ
    · subst hν
      refine ⟨k, ?_⟩
      have hx : (fun _ => g'.origin ν : AmbientSpace) ∈ g'.wall ν 0 := by
        simp [ReflectionGrid.wall]
      rw [← hνk'] at hx
      have hx' : g'.origin ν = g.origin ν + k * g.cellSide := hx
      rw [hx']
      ring
    · exfalso
      have hx : (Function.update (fun _ => g'.origin μ) ν (g.origin ν + k * g.cellSide + 1) : AmbientSpace) ∈
          g'.wall μ 0 := by
        simp [ReflectionGrid.wall, Function.update_of_ne (Ne.symm hν)]
      rw [← hνk'] at hx
      have hx' : (Function.update (fun _ => g'.origin μ) ν (g.origin ν + k * g.cellSide + 1) : AmbientSpace) ν =
          g.origin ν + k * g.cellSide := hx
      simp at hx'
  choose u hu using key
  exact ⟨u, hu⟩
theorem cell_subset_coarse_cell {g g' : ReflectionGrid D} {N : ℤ} {u k k' : Fin 4 → ℤ}
    (hs : g'.cellSide = N * g.cellSide) (hu : ∀ μ, g'.origin μ = g.origin μ + g.cellSide * u μ)
    (h : ∀ μ, u μ + N * k' μ ≤ k μ ∧ k μ + 1 ≤ u μ + N * k' μ + N) : g.cell k ⊆ g'.cell k' := by
  intro x hx μ
  have hp := cellSide_pos g
  have hxμ : x μ - (g.origin μ + g.cellSide * k μ) ∈ Icc 0 g.cellSide := hx μ
  obtain ⟨a, b⟩ := hxμ
  obtain ⟨c, d⟩ := h μ
  have c' : (u μ : ℝ) + N * k' μ ≤ k μ := by exact_mod_cast c
  have d' : (k μ : ℝ) + 1 ≤ u μ + N * k' μ + N := by exact_mod_cast d
  have e₁ := mul_le_mul_of_nonneg_left c' hp.le
  have e₂ := mul_le_mul_of_nonneg_left d' hp.le
  show x μ - (g'.origin μ + g'.cellSide * k' μ) ∈ Icc 0 g'.cellSide
  rw [hs, hu μ]
  constructor <;> nlinarith
theorem index_bounds_of_cellCentre_mem {g g' : ReflectionGrid D} {N : ℤ} {u k k' : Fin 4 → ℤ}
    (hs : g'.cellSide = N * g.cellSide) (hu : ∀ μ, g'.origin μ = g.origin μ + g.cellSide * u μ)
    (h : g.cellCentre k ∈ g'.cell k') (μ : Fin 4) :
    u μ + N * k' μ ≤ k μ ∧ k μ + 1 ≤ u μ + N * k' μ + N := by
  have hp := cellSide_pos g
  have hμ : g.origin μ + g.cellSide * k μ + g.cellSide / 2 - (g'.origin μ + g'.cellSide * k' μ) ∈
      Icc 0 g'.cellSide := h μ
  rw [hs, hu μ] at hμ
  obtain ⟨a, b⟩ := hμ
  constructor
  · by_contra hlt
    have hlt' : k μ + 1 ≤ u μ + N * k' μ := by omega
    have c : (k μ : ℝ) + 1 ≤ u μ + N * k' μ := by exact_mod_cast hlt'
    have e := mul_le_mul_of_nonneg_left c hp.le
    nlinarith
  · by_contra hlt
    have hlt' : u μ + N * k' μ + N ≤ k μ := by omega
    have c : (u μ : ℝ) + N * k' μ + N ≤ k μ := by exact_mod_cast hlt'
    have e := mul_le_mul_of_nonneg_left c hp.le
    nlinarith
theorem exists_coarse_index {N : ℤ} (hN : 0 < N) (u k : Fin 4 → ℤ) :
    ∃ k' : Fin 4 → ℤ, ∀ μ, u μ + N * k' μ ≤ k μ ∧ k μ + 1 ≤ u μ + N * k' μ + N := by
  refine ⟨fun μ => (k μ - u μ) / N, fun μ => ?_⟩
  have h₁ := Int.emod_def (k μ - u μ) N
  have h₂ := Int.emod_nonneg (k μ - u μ) hN.ne'
  have h₃ := Int.emod_lt_of_pos (k μ - u μ) hN
  constructor <;> linarith
theorem exists_translate_index_inside {g g' : ReflectionGrid D} {N n : ℤ} {u k k' : Fin 4 → ℤ}
    (hs : g'.cellSide = N * g.cellSide) (hu : ∀ μ, g'.origin μ = g.origin μ + g.cellSide * u μ)
    (hℓ : PeriodicLattice.torusSide D.L D.m = n * g.cellSide)
    (h : D.proj '' g.cell k ⊆ D.proj '' g'.cell k') :
    ∃ i : Fin 4 → ℤ, ∀ μ, u μ + N * k' μ ≤ k μ + n * i μ ∧
      k μ + n * i μ + 1 ≤ u μ + N * k' μ + N := by
  obtain ⟨y, hy, hyc⟩ := h ⟨g.cellCentre k, cellCentre_mem_cell g k, rfl⟩
  obtain ⟨i, hi⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq
    (ℓ := PeriodicLattice.torusSide D.L D.m) (v := y) (w := g.cellCentre k) hyc
  refine ⟨i, ?_⟩
  have hc : g.cellCentre (fun μ => k μ + n * i μ) = y := by
    rw [hi]
    funext μ
    simp only [ReflectionGrid.cellCentre, Pi.add_apply, TestFunctions.latticeTranslate, hℓ]
    push_cast
    ring
  exact index_bounds_of_cellCentre_mem hs hu (hc ▸ hy)
theorem coarse_torusCell_unique {g g' : ReflectionGrid D} {N n n' : ℤ} {u k k₁ k₂ : Fin 4 → ℤ}
    (hN : 0 < N) (hs : g'.cellSide = N * g.cellSide)
    (hu : ∀ μ, g'.origin μ = g.origin μ + g.cellSide * u μ)
    (hℓ : PeriodicLattice.torusSide D.L D.m = n * g.cellSide) (hn : n = N * n')
    (hn' : g'.cellsAcross = n')
    (hcells : ∀ k k' : Fin 4 → ℤ, D.proj '' g'.cell k = D.proj '' g'.cell k' ↔
      ∃ j : Fin 4 → ℤ, ∀ μ, ((k μ - k' μ : ℤ) : ℝ) = g'.cellsAcross * j μ)
    (h₁ : D.proj '' g.cell k ⊆ D.proj '' g'.cell k₁)
    (h₂ : D.proj '' g.cell k ⊆ D.proj '' g'.cell k₂) :
    D.proj '' g'.cell k₁ = D.proj '' g'.cell k₂ := by
  obtain ⟨i₁, a₁⟩ := exists_translate_index_inside hs hu hℓ h₁
  obtain ⟨i₂, a₂⟩ := exists_translate_index_inside hs hu hℓ h₂
  refine (hcells _ _).2 ⟨fun μ => i₁ μ - i₂ μ, fun μ => ?_⟩
  obtain ⟨b₁, c₁⟩ := a₁ μ
  obtain ⟨b₂, c₂⟩ := a₂ μ
  subst hn
  have ht : n' * (i₁ μ - i₂ μ) - k₁ μ + k₂ μ = 0 :=
    int_eq_zero_of_mul_bounds hN (by nlinarith) (by nlinarith)
  have e : k₁ μ - k₂ μ = n' * (i₁ μ - i₂ μ) := by linarith
  rw [hn', e]
  push_cast
  ring
theorem image_mem_torusCellSet {g : ReflectionGrid D} (hg : ReflectionGroupActsOnCells g)
    {r' : D.Torus → D.Torus} (hr' : r' ∈ g.inducedTorusMaps) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) : r' '' C ∈ g.torusCellSet := by
  obtain ⟨r, hr, h⟩ := hr'
  obtain ⟨S, hS, rfl⟩ := hC
  refine ⟨r '' S, (hg.1 r hr).2.2.mapsTo hS, ?_⟩
  show D.proj '' (r '' S) = r' '' (D.proj '' S)
  rw [← image_comp, ← image_comp, h]
theorem torusCarrier_image {g : ReflectionGrid D} (hg : ReflectionGroupActsOnCells g)
    (hsimple : ∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet,
      ∃! r', r' ∈ g.inducedTorusMaps ∧ r' '' C = C')
    {r' : D.Torus → D.Torus} (hr' : r' ∈ g.inducedTorusMaps) {C : Set D.Torus}
    (hC : C ∈ g.torusCellSet) : g.torusCarrier C (r' '' C) = r' := by
  obtain ⟨t, -, huniq⟩ := hsimple C hC (r' '' C) (image_mem_torusCellSet hg hr' hC)
  have e := Classical.epsilon_spec (p := fun t : D.Torus → D.Torus =>
    t ∈ g.inducedTorusMaps ∧ t '' C = r' '' C) ⟨r', hr', rfl⟩
  exact (huniq _ e).trans (huniq _ ⟨hr', rfl⟩).symm
end CoarseningOnTorus
open CoarseningOnTorus in
theorem allGridsCoarseningOnTorus_of
    (h₁ : AllGridsCoarseningOnSpace)
    (h₂ : AllGridsTorusCellStructure)
    (h₃ : AllGridsTorusGroupActsOnCells)
    (h₄ : AllGridsReflectionGroupActsOnCells) :
    AllGridsCoarseningOnTorus := by
  intro D g hg g' k₀ hco hk₀ hℓ
  have hp := cellSide_pos g
  have hp' := cellSide_pos g'
  have hL1 : (1 : ℝ) ≤ (D.L : ℝ) ^ k₀ := one_le_pow₀ D.one_lt_factor.le
  have hle : g.cellSide ≤ g'.cellSide := by
    rw [hk₀]
    nlinarith
  have hg' : g'.HasAdmissibleSide := by
    refine ⟨⟨g'.q, rfl⟩, hg.2.trans ?_⟩
    have hL2 : (0 : ℝ) < (D.L : ℝ) ^ 2 := by
      have := D.one_lt_factor
      positivity
    exact div_le_div_of_nonneg_right hle hL2.le
  have hℓ₀ : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m := by linarith
  have hsp := h₁ D g hg g' k₀ hco hk₀
  obtain ⟨⟨n, -, hnn⟩, -, hcells, -, hopen⟩ := h₂ D g hg hℓ₀
  obtain ⟨⟨n', -, hnn'⟩, -, hcells', -, hopen'⟩ := h₂ D g' hg' hℓ
  obtain ⟨-, -, -, hpar, -, hsimple, -⟩ := h₃ D g hg hℓ₀
  obtain ⟨-, -, ⟨H', hH'⟩, -, -, hsimple', -⟩ := h₃ D g' hg' hℓ
  have hgc := h₄ D g hg
  have hgc' := h₄ D g' hg'
  obtain ⟨u, hu⟩ := exists_origin_shift hco.2
  have hN : 0 < (D.L : ℤ) ^ k₀ := by
    have := D.isAdmissible.2
    have hL : (0 : ℤ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
    positivity
  have hs : g'.cellSide = (((D.L : ℤ) ^ k₀ : ℤ) : ℝ) * g.cellSide := by
    rw [hk₀]
    push_cast
    rfl
  have hℓn : PeriodicLattice.torusSide D.L D.m = n * g.cellSide := by
    rw [← hnn]
    exact (div_mul_cancel₀ _ hp.ne').symm
  have hℓn' : PeriodicLattice.torusSide D.L D.m = n' * g'.cellSide := by
    rw [← hnn']
    exact (div_mul_cancel₀ _ hp'.ne').symm
  have hnN : n = (D.L : ℤ) ^ k₀ * n' := by
    have e : (n : ℝ) * g.cellSide = ((((D.L : ℤ) ^ k₀ : ℤ) : ℝ) * n') * g.cellSide := by
      rw [← hℓn, hℓn', hs]
      ring
    exact_mod_cast mul_right_cancel₀ hp.ne' e
  generalize (D.L : ℤ) ^ k₀ = N at hN hs hnN
  have hinside : ∀ {k k' : Fin 4 → ℤ}, D.proj '' g.cell k ⊆ D.proj '' g'.cell k' →
      ∃ k₁ : Fin 4 → ℤ, g.cell k₁ ⊆ g'.cell k' ∧
        D.proj '' g.cell k₁ = D.proj '' g.cell k := by
    intro k k' h
    obtain ⟨i, hi⟩ := exists_translate_index_inside hs hu hℓn h
    refine ⟨fun μ => k μ + n * i μ, cell_subset_coarse_cell hs hu hi, ?_⟩
    refine (hcells _ _).2 ⟨i, fun μ => ?_⟩
    rw [hnn]
    push_cast
    ring
  have hsubG : g'.inducedTorusMaps ⊆ g.inducedTorusMaps := fun r' ⟨r, hr, h⟩ => ⟨r, hsp.2 hr, h⟩
  have hsgn : ∀ r' ∈ g'.inducedTorusMaps, g'.torusSign r' = g.torusSign r' := by
    intro r' hr'
    obtain ⟨r, hr, h⟩ := id hr'
    have hspec : D.proj ∘ (g'.inducingElement r').1 = r' ∘ D.proj :=
      Classical.epsilon_spec (p := fun r : g'.reflectionGroup =>
        D.proj ∘ r.1 = r' ∘ D.proj) ⟨⟨r, hr⟩, h⟩
    exact hpar r' (hsubG hr') ⟨(g'.inducingElement r').1, hsp.2 (g'.inducingElement r').2⟩ hspec
  have hinv : ∀ r' ∈ g'.inducedTorusMaps, ∃ s' ∈ g'.inducedTorusMaps, s' ∘ r' = id ∧ r' ∘ s' = id := by
    intro r' hr'
    rw [← hH'] at hr'
    obtain ⟨e, he, rfl⟩ := hr'
    refine ⟨⇑e⁻¹, ?_, ?_, ?_⟩
    · rw [← hH']
      exact ⟨e⁻¹, H'.inv_mem he, rfl⟩
    · funext x
      simp
    · funext x
      simp
  refine ⟨?_, hsubG, hsgn, ?_, ?_⟩
  · rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
    obtain ⟨hU, hcount, -⟩ := hsp.1 _ ⟨k', rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · refine Subset.antisymm ?_ (sUnion_subset fun C hC => hC.2)
      rintro _ ⟨x, hx, rfl⟩
      rw [hU] at hx
      obtain ⟨S, ⟨hS, hSS⟩, hxS⟩ := hx
      exact ⟨D.proj '' S, ⟨⟨S, hS, rfl⟩, image_mono hSS⟩, mem_image_of_mem _ hxS⟩
    · have hT : {C | C ∈ g.torusCellSet ∧ C ⊆ D.proj '' g'.cell k'} =
          (fun S => D.proj '' S) '' {S | S ∈ g.cellSet ∧ S ⊆ g'.cell k'} := by
        ext C
        constructor
        · rintro ⟨⟨_, ⟨k, rfl⟩, rfl⟩, hsub⟩
          obtain ⟨k₁, hk₁, he⟩ := hinside hsub
          exact ⟨g.cell k₁, ⟨⟨k₁, rfl⟩, hk₁⟩, he⟩
        · rintro ⟨S, ⟨hS, hsub⟩, rfl⟩
          exact ⟨⟨S, hS, rfl⟩, image_mono hsub⟩
      have hinj : InjOn (fun S => D.proj '' S) {S | S ∈ g.cellSet ∧ S ⊆ g'.cell k'} := by
        rintro _ ⟨⟨k₁, rfl⟩, a₁⟩ _ ⟨⟨k₂, rfl⟩, a₂⟩ he
        obtain ⟨j, hj⟩ := (hcells k₁ k₂).1 he
        have hk : k₁ = k₂ := by
          funext μ
          obtain ⟨b₁, c₁⟩ := index_bounds_of_cellCentre_mem hs hu (a₁ (cellCentre_mem_cell g k₁)) μ
          obtain ⟨b₂, c₂⟩ := index_bounds_of_cellCentre_mem hs hu (a₂ (cellCentre_mem_cell g k₂)) μ
          have e : k₁ μ - k₂ μ = N * (n' * j μ) := by
            have e' := hj μ
            rw [hnn, hnN] at e'
            push_cast at e'
            have e'' : ((k₁ μ - k₂ μ : ℤ) : ℝ) = ((N * (n' * j μ) : ℤ) : ℝ) := by
              push_cast
              rw [e']
              ring
            exact_mod_cast e''
          have ht : n' * j μ = 0 :=
            int_eq_zero_of_mul_bounds hN (by linarith) (by linarith)
          rw [ht, mul_zero] at e
          omega
        rw [hk]
      rw [hT, hinj.ncard_image]
      exact hcount
    · rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩ hsub F hF
      obtain ⟨k₁, hk₁, he⟩ := hinside hsub
      have hopn : g.torusCellInterior (D.proj '' g.cell k) ⊆
          g'.torusCellInterior (D.proj '' g'.cell k') := by
        rw [(hopen k k rfl).2.1, (hopen' k' k' rfl).2.1, ← (hopen k₁ k he).1]
        exact image_mono (interior_mono hk₁)
      have hlinks : g.torusCellLinks (D.proj '' g.cell k) ⊆
          g'.torusCellLinks (D.proj '' g'.cell k') :=
        fun b hb => ⟨hopn hb.1, hopn hb.2⟩
      obtain ⟨f, hm, ⟨c, hc⟩, hF⟩ := hF
      exact ⟨fun v => f fun b => v ⟨b.1, hlinks b.2⟩,
        hm.comp (measurable_pi_lambda _ fun b => measurable_pi_apply _),
        ⟨c, fun v => hc _⟩, fun U => hF U⟩
  · intro C' hC' C₁ hC₁
    obtain ⟨_, ⟨k₁, rfl⟩, rfl⟩ := hC₁
    obtain ⟨k'', hk''⟩ := exists_coarse_index hN u k₁
    have hin : g.cell k₁ ⊆ g'.cell k'' := cell_subset_coarse_cell hs hu hk''
    have hC'' : D.proj '' g'.cell k'' ∈ g'.torusCellSet := ⟨_, ⟨k'', rfl⟩, rfl⟩
    obtain ⟨r', ⟨hr', hrC⟩, huniq⟩ := hsimple' C' hC' _ hC''
    obtain ⟨s', hs', hsr, hrs⟩ := hinv r' hr'
    have hcell₁ : D.proj '' g.cell k₁ ∈ g.torusCellSet := ⟨_, ⟨k₁, rfl⟩, rfl⟩
    refine ⟨(r', s' '' (D.proj '' g.cell k₁)), ⟨hr', image_mem_torusCellSet hgc (hsubG hs') hcell₁,
      ?_, ?_⟩, ?_⟩
    · have e : s' '' (r' '' C') = C' := by
        rw [← image_comp, hsr, image_id]
      have h : s' '' (D.proj '' g.cell k₁) ⊆ s' '' (r' '' C') := by
        rw [hrC]
        exact image_mono (image_mono hin)
      rw [e] at h
      exact h
    · show r' '' (s' '' (D.proj '' g.cell k₁)) = _
      rw [← image_comp, hrs, image_id]
    · rintro ⟨r₁, D₁⟩ ⟨a₁, a₂, a₃, a₄⟩
      simp only at a₁ a₂ a₃ a₄
      obtain ⟨_, ⟨k₃, rfl⟩, hk₃⟩ := image_mem_torusCellSet hgc' a₁ hC'
      have hk₃' : D.proj '' g'.cell k₃ = r₁ '' C' := hk₃
      have hsub₃ : D.proj '' g.cell k₁ ⊆ D.proj '' g'.cell k₃ := by
        rw [hk₃', ← a₄]
        exact image_mono a₃
      have heq := coarse_torusCell_unique hN hs hu hℓn hnN hnn' hcells' hsub₃ (image_mono hin)
      have hr₁ : r₁ = r' := huniq r₁ ⟨a₁, hk₃'.symm.trans heq⟩
      subst hr₁
      have hD : D₁ = s' '' (D.proj '' g.cell k₁) := by
        rw [← a₄, ← image_comp, hsr, image_id]
      rw [hD]
  · intro C' hC' r' hr' C hC _ F _ U _
    have e₁ := torusCarrier_image hgc' hsimple' hr' hC'
    have e₂ := torusCarrier_image hgc hsimple (hsubG hr') hC
    simp only [ReflectionGrid.torusTransportTo, e₁, e₂, ReflectionGrid.torusTransport, hsgn r' hr']
end MirrorGridsAllSides
end YangMills.Construction
