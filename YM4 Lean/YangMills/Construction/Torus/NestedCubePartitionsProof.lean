import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.NestedCubePartitions
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.NestedCubes.Refinement
variable {d : ℕ} {S : ℝ}
theorem mem_spacingLattice_iff {σ : ℝ} {x : PeriodicTorus d S} :
    x ∈ spacingLattice d S σ ↔ ∃ k : Fin d → ℤ, x = torusProj d S fun μ => (k μ : ℝ) * σ :=
  Iff.rfl
theorem exists_int_lift_of_mem_spacingLattice {σ' : ℝ} {K : ℕ} (hS : S = (K : ℝ) * σ')
    {v : Fin d → ℝ} (hv : torusProj d S v ∈ spacingLattice d S σ') :
    ∃ j : Fin d → ℤ, ∀ μ, v μ = (j μ : ℝ) * σ' := by
  obtain ⟨k, hk⟩ := mem_spacingLattice_iff.1 hv
  have h : ∀ μ, ∃ j : ℤ, v μ = (j : ℝ) * σ' := by
    intro μ
    have h1 : (v μ : AddCircle S) = (((k μ : ℝ) * σ' : ℝ) : AddCircle S) := congrFun hk μ
    have h2 : ((v μ - (k μ : ℝ) * σ' : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
    refine ⟨k μ + n * K, ?_⟩
    rw [zsmul_eq_mul, hS] at hn
    push_cast
    linarith
  choose j hj using h
  exact ⟨j, hj⟩
theorem exists_int_near_of_abs_le {n : ℕ} {w : ℝ} (hw : |w| ≤ (2 * (n : ℝ) + 1) / 2) :
    ∃ m : ℤ, |(m : ℝ)| ≤ n ∧ |w - m| ≤ 1 / 2 := by
  obtain ⟨hw1, hw2⟩ := abs_le.1 hw
  have hr := abs_sub_round w
  obtain ⟨hr1, hr2⟩ := abs_le.1 hr
  by_cases h1 : round w ≤ -(n : ℤ)
  · refine ⟨-(n : ℤ), ?_, ?_⟩
    · simp
    · have h1' : ((round w : ℤ) : ℝ) ≤ -(n : ℝ) := by exact_mod_cast h1
      rw [abs_le]
      push_cast
      constructor <;> linarith
  by_cases h2 : (n : ℤ) ≤ round w
  · refine ⟨(n : ℤ), ?_, ?_⟩
    · simp
    · have h2' : (n : ℝ) ≤ ((round w : ℤ) : ℝ) := by exact_mod_cast h2
      rw [abs_le]
      push_cast
      constructor <;> linarith
  refine ⟨round w, ?_, hr⟩
  have h1' : -(n : ℝ) ≤ ((round w : ℤ) : ℝ) := by
    have : -(n : ℤ) ≤ round w := by omega
    exact_mod_cast this
  have h2' : ((round w : ℤ) : ℝ) ≤ (n : ℝ) := by
    have : round w ≤ (n : ℤ) := by omega
    exact_mod_cast this
  exact abs_le.2 ⟨h1', h2'⟩
theorem int_abs_le_of_abs_le_half {n : ℕ} {m : ℤ} (h : |(m : ℝ)| ≤ (2 * (n : ℝ) + 1) / 2) :
    |(m : ℝ)| ≤ n := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have h1' : -(n : ℤ) - 1 < m := by
    have : ((-(n : ℤ) - 1 : ℤ) : ℝ) < (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2' : m < (n : ℤ) + 1 := by
    have : (m : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h3 : -(n : ℤ) ≤ m := by omega
  have h4 : m ≤ (n : ℤ) := by omega
  have h3' : -(n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  have h4' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h4
  exact abs_le.2 ⟨h3', h4'⟩
theorem mem_centeredBox_iff {n : ℕ} {m : Fin d → ℤ} :
    m ∈ centeredBox d (2 * (n : ℝ) + 1) ↔ ∀ μ, |(m μ : ℝ)| ≤ n := by
  have h : (2 * (n : ℝ) + 1 - 1) / 2 = n := by ring
  simp only [centeredBox, Set.mem_ofPred_eq, h]
theorem ncard_centeredBox (d n : ℕ) :
    ((centeredBox d (2 * (n : ℝ) + 1)).ncard : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
  have h : centeredBox d (2 * (n : ℝ) + 1) =
      ↑(Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) := by
    ext k
    rw [mem_centeredBox_iff, Finset.mem_coe, Fintype.mem_piFinset]
    refine forall_congr' fun μ => ?_
    rw [abs_le, Finset.mem_Icc]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
    · rintro ⟨a, b⟩
      exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  have hc : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    omega
  rw [h, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp [hc]
theorem cubeAt_offsetPoint_subset (hproj : ProjCubes.ProjFacts d S) {σ' : ℝ} (hσ' : 0 < σ')
    {n : ℕ} (c : Fin d → ℝ) (m : Fin d → ℤ) (hm : ∀ μ, |(m μ : ℝ)| ≤ n) :
    cubeAt (offsetPoint S σ' c m) σ' ⊆ cubeAt (torusProj d S c) ((2 * (n : ℝ) + 1) * σ') := by
  intro p hp
  obtain ⟨v, rfl, hv⟩ :=
    (hproj.mem_cubeAt_iff (fun μ => c μ + σ' * (m μ : ℝ)) σ' p hσ'.le).1 hp
  refine (hproj.mem_cubeAt_iff c _ _ (by positivity)).2 ⟨v, rfl, fun μ => ?_⟩
  have h1 : |v μ - (c μ + σ' * (m μ : ℝ))| ≤ σ' / 2 := hv μ
  have h2 : |σ' * (m μ : ℝ)| ≤ σ' * n := by
    rw [abs_mul, abs_of_pos hσ']
    exact mul_le_mul_of_nonneg_left (hm μ) hσ'.le
  have h3 : v μ - c μ = (v μ - (c μ + σ' * (m μ : ℝ))) + σ' * (m μ : ℝ) := by ring
  have h4 := abs_add_le (v μ - (c μ + σ' * (m μ : ℝ))) (σ' * (m μ : ℝ))
  rw [h3]
  linarith
theorem exists_mem_cubeAt_offsetPoint (hproj : ProjCubes.ProjFacts d S) {σ' : ℝ}
    (hσ' : 0 < σ') {n : ℕ} (c : Fin d → ℝ) {p : PeriodicTorus d S}
    (hp : p ∈ cubeAt (torusProj d S c) ((2 * (n : ℝ) + 1) * σ')) :
    ∃ m : Fin d → ℤ, (∀ μ, |(m μ : ℝ)| ≤ n) ∧ p ∈ cubeAt (offsetPoint S σ' c m) σ' := by
  obtain ⟨v, rfl, hv⟩ := (hproj.mem_cubeAt_iff c _ p (by positivity)).1 hp
  have h : ∀ μ, ∃ m : ℤ, |(m : ℝ)| ≤ n ∧ |(v μ - c μ) / σ' - m| ≤ 1 / 2 := by
    intro μ
    refine exists_int_near_of_abs_le ?_
    rw [abs_div, abs_of_pos hσ', div_le_iff₀ hσ']
    have := hv μ
    linarith
  choose m hm hm' using h
  refine ⟨m, hm, (hproj.mem_cubeAt_iff (fun μ => c μ + σ' * (m μ : ℝ)) σ' _ hσ'.le).2
    ⟨v, rfl, fun μ => ?_⟩⟩
  have h1 : v μ - (c μ + σ' * (m μ : ℝ)) = ((v μ - c μ) / σ' - (m μ : ℝ)) * σ' := by
    field_simp
    ring
  have h2 := mul_le_mul_of_nonneg_right (hm' μ) hσ'.le
  show |v μ - (c μ + σ' * (m μ : ℝ))| ≤ σ' / 2
  rw [h1, abs_mul, abs_of_pos hσ']
  linarith
theorem offsetPoint_mem_spacingLattice {σ' : ℝ} {c : Fin d → ℝ} (j : Fin d → ℤ)
    (hc : ∀ μ, c μ = (j μ : ℝ) * σ') (m : Fin d → ℤ) :
    offsetPoint S σ' c m ∈ spacingLattice d S σ' := by
  refine mem_spacingLattice_iff.2 ⟨j + m, ?_⟩
  unfold offsetPoint
  congr 1
  funext μ
  rw [hc μ]
  push_cast [Pi.add_apply]
  ring
theorem isCenteredGrid_inter_cubeAt (hproj : ProjCubes.ProjFacts d S) {σ' : ℝ} (hσ' : 0 < σ')
    {n K : ℕ} (hSK : S = (K : ℝ) * σ') (hsmall : (n : ℝ) * σ' < S / 2) (z : Fin d → ℝ)
    (hz : torusProj d S z ∈ spacingLattice d S σ') :
    IsCenteredGrid S σ' (2 * (n : ℝ) + 1) z
      ((spacingLattice d S σ' : Set (PeriodicTorus d S)) ∩
        cubeAt (torusProj d S z) ((2 * (n : ℝ) + 1) * σ')) := by
  obtain ⟨j, hj⟩ := exists_int_lift_of_mem_spacingLattice hSK hz
  have hcoef : ∀ (m : Fin d → ℤ), (∀ μ, |(m μ : ℝ)| ≤ n) → ∀ μ, |σ' * (m μ : ℝ)| ≤ n * σ' := by
    intro m hm μ
    rw [abs_mul, abs_of_pos hσ', mul_comm]
    exact mul_le_mul_of_nonneg_right (hm μ) hσ'.le
  refine ⟨?_, ?_, ncard_centeredBox d n⟩
  · ext p
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' := mem_centeredBox_iff.1 hm
      refine ⟨offsetPoint_mem_spacingLattice j hj m, ?_⟩
      refine (hproj.mem_cubeAt_iff z _ _ (by positivity)).2
        ⟨fun μ => z μ + σ' * (m μ : ℝ), rfl, fun μ => ?_⟩
      have h1 := hcoef m hm' μ
      have h2 : z μ + σ' * (m μ : ℝ) - z μ = σ' * (m μ : ℝ) := by ring
      rw [h2]
      linarith
    · rintro ⟨hl, hp⟩
      obtain ⟨v, rfl, hv⟩ := (hproj.mem_cubeAt_iff z _ p (by positivity)).1 hp
      obtain ⟨i, hi⟩ := exists_int_lift_of_mem_spacingLattice hSK (SetLike.mem_coe.1 hl)
      have hvz : ∀ μ, v μ = z μ + σ' * ((i - j) μ : ℝ) := by
        intro μ
        rw [hi μ, hj μ]
        push_cast [Pi.sub_apply]
        ring
      refine ⟨i - j, mem_centeredBox_iff.2 fun μ => int_abs_le_of_abs_le_half ?_, ?_⟩
      · have h1 := hv μ
        rw [hvz μ, add_sub_cancel_left, abs_mul, abs_of_pos hσ'] at h1
        have h2 : σ' * |((i - j) μ : ℝ)| ≤ σ' * ((2 * (n : ℝ) + 1) / 2) := by
          have : σ' * ((2 * (n : ℝ) + 1) / 2) = (2 * (n : ℝ) + 1) * σ' / 2 := by ring
          rw [this]
          exact h1
        exact le_of_mul_le_mul_left h2 hσ'
      · unfold offsetPoint
        congr 1
        funext μ
        exact (hvz μ).symm
  · intro m hm m' hm' h
    have hm1 := mem_centeredBox_iff.1 hm
    have hm2 := mem_centeredBox_iff.1 hm'
    have hin : ∀ (a : Fin d → ℤ), (∀ μ, |(a μ : ℝ)| ≤ n) →
        (fun μ => z μ + σ' * (a μ : ℝ)) ∈ {v : Fin d → ℝ | ∀ μ, |v μ - z μ| < S / 2} := by
      intro a ha μ
      have h1 := hcoef a ha μ
      have h2 : z μ + σ' * (a μ : ℝ) - z μ = σ' * (a μ : ℝ) := by ring
      show |z μ + σ' * (a μ : ℝ) - z μ| < S / 2
      rw [h2]
      linarith
    have h3 := hproj.injOn_cube z S le_rfl (hin m hm1) (hin m' hm2) h
    funext μ
    have h4 : z μ + σ' * (m μ : ℝ) = z μ + σ' * (m' μ : ℝ) := congrFun h3 μ
    have h5 : (m μ : ℝ) = (m' μ : ℝ) := mul_left_cancel₀ hσ'.ne' (add_left_cancel h4)
    exact_mod_cast h5
theorem propertiesOfOddRefinement_holds (h₁ : ProjCubes.ProjFactsHold)
    (h₂ : CubePartition.PropertiesOfIntegerMultiple) : PropertiesOfOddRefinement := by
  intro d S σ σ' N k hd hσ' hN hσ hk hS
  obtain ⟨n, rfl⟩ := hN
  have hNr : (((2 * n + 1 : ℕ)) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [hNr] at hσ
  subst hσ
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hσ0 : 0 < (2 * (n : ℝ) + 1) * σ' := by positivity
  have hSpos : 0 < S := by
    rw [hS]
    exact mul_pos (by linarith) hσ0
  have hproj := h₁ d S hSpos
  have hSK : S = ((k * (2 * n + 1) : ℕ) : ℝ) * σ' := by
    rw [hS]
    push_cast
    ring
  have hK2 : 2 ≤ k * (2 * n + 1) := by nlinarith
  have hcub := h₂ d S σ' (k * (2 * n + 1)) hd hσ' hK2 hSK
  have hsmall : (n : ℝ) * σ' < S / 2 := by
    have h1 : 2 * ((2 * (n : ℝ) + 1) * σ') ≤ (k : ℝ) * ((2 * (n : ℝ) + 1) * σ') :=
      mul_le_mul_of_nonneg_right hk0 hσ0.le
    rw [hS]
    nlinarith
  have hlat : spacingLattice d S ((2 * (n : ℝ) + 1) * σ') ≤ spacingLattice d S σ' := by
    intro x hx
    obtain ⟨j, rfl⟩ := mem_spacingLattice_iff.1 hx
    refine mem_spacingLattice_iff.2 ⟨fun μ => j μ * (2 * (n : ℤ) + 1), ?_⟩
    congr 1
    funext μ
    push_cast
    ring
  have hcube : ∀ Q ∈ cubePartition d S ((2 * (n : ℝ) + 1) * σ'),
      Q = ⋃₀ {Q' ∈ cubePartition d S σ' | Q' ⊆ Q} := by
    rintro Q ⟨c, hc, rfl⟩
    obtain ⟨a, rfl⟩ := mem_spacingLattice_iff.1 hc
    obtain ⟨j, hj⟩ := exists_int_lift_of_mem_spacingLattice hSK (hlat hc)
    refine Subset.antisymm ?_ (sUnion_subset fun Q' h => h.2)
    intro p hp
    obtain ⟨m, hm, hpm⟩ := exists_mem_cubeAt_offsetPoint hproj hσ' _ hp
    exact ⟨_, ⟨⟨_, offsetPoint_mem_spacingLattice j hj m, rfl⟩,
      cubeAt_offsetPoint_subset hproj hσ' _ m hm⟩, hpm⟩
  refine ⟨hlat, hcube, ?_, ?_, ?_⟩
  · rintro X ⟨𝒞, h𝒞, rfl⟩
    refine ⟨{Q' ∈ cubePartition d S σ' | ∃ Q ∈ 𝒞, Q' ⊆ Q}, fun Q' h => h.1, ?_⟩
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨Q, hQ, hp⟩
      rw [hcube Q (h𝒞 hQ)] at hp
      obtain ⟨Q', hQ', hpQ'⟩ := hp
      exact ⟨Q', ⟨hQ'.1, Q, hQ, hQ'.2⟩, hpQ'⟩
    · rintro p ⟨Q', ⟨_, Q, hQ, hQ'⟩, hp⟩
      exact ⟨Q, hQ, hQ' hp⟩
  · rintro z hz z' rfl
    have hratio : (2 * (n : ℝ) + 1) * σ' / σ' = 2 * (n : ℝ) + 1 := by
      field_simp
    rw [hratio]
    exact isCenteredGrid_inter_cubeAt hproj hσ' hSK hsmall z' (hlat hz)
  · intro z hz p hp
    obtain ⟨a, rfl⟩ := mem_spacingLattice_iff.1 hz
    have hgrid := isCenteredGrid_inter_cubeAt hproj hσ' hSK hsmall _ (hlat hz)
    rw [← hgrid.image_eq] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    have hm' := mem_centeredBox_iff.1 hm
    obtain ⟨j, hj⟩ := exists_int_lift_of_mem_spacingLattice hSK (hlat hz)
    exact interior_mono (cubeAt_offsetPoint_subset hproj hσ' _ m hm')
      (hcub.center_mem_interior _ (offsetPoint_mem_spacingLattice j hj m))
end YangMills.Construction.Torus.NestedCubes.Refinement
end
