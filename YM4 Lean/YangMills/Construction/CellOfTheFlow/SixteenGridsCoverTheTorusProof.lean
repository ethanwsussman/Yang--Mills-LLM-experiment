import YangMills.Construction.CellOfTheFlow.SixteenGridsCoverTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
private theorem exists_residue_far_from_walls (l s : ℤ) (r : ℕ) (hl : l = 2 * s + 1) (hr : 128 * (r : ℤ) ≤ l)
    (hs : 0 ≤ s) (u : ℤ) : ∃ (b : Bool) (t : ℤ), 0 ≤ t ∧ t < l ∧ 8 * (r : ℤ) ≤ t + 1 ∧ 8 * (r : ℤ) ≤ l - t ∧
      l ∣ u - (if b then s else 0) - t := by
  have hlpos : 0 < l := by omega
  have h0 : 0 ≤ u % l := Int.emod_nonneg _ hlpos.ne'
  have h1 : u % l < l := Int.emod_lt_of_pos _ hlpos
  have hd : l ∣ u - u % l := Int.dvd_self_sub_emod
  obtain ⟨q, hq⟩ := hd
  by_cases hfar : 8 * (r : ℤ) ≤ u % l + 1 ∧ 8 * (r : ℤ) ≤ l - u % l
  · exact ⟨false, u % l, h0, h1, hfar.1, hfar.2, ⟨q, by simpa using hq⟩⟩
  · by_cases hbelow : u % l < s
    · refine ⟨true, u % l + l - s, by omega, by omega, by omega, by omega, ⟨q - 1, ?_⟩⟩
      simp only [if_true]
      linear_combination hq
    · refine ⟨true, u % l - s, by omega, by omega, by omega, by omega, ⟨q, ?_⟩⟩
      simp only [if_true]
      linear_combination hq
private theorem exists_cell_index_of_dvd (n : ℕ) [NeZero n] (l : ℕ) (hdvd : l ∣ n) (u o t : ℤ)
    (hres : (l : ℤ) ∣ u - o - t) :
    ∃ k : ℤ, 0 ≤ k ∧ k < ((n / l : ℕ) : ℤ) ∧ ((u : ZMod n)) = ((o + (l : ℤ) * k + t : ℤ) : ZMod n) := by
  set v : ℕ := (((u - o - t : ℤ)) : ZMod n).val with hv
  have hvn : v < n := ZMod.val_lt _
  have hcast : ((v : ℤ) : ZMod n) = ((u - o - t : ℤ) : ZMod n) := by
    simp [hv]
  have hmod : (n : ℤ) ∣ (u - o - t) - (v : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Int.cast_sub, hcast, sub_self]
  have hln : (l : ℤ) ∣ (n : ℤ) := by exact_mod_cast hdvd
  have hlv : (l : ℤ) ∣ (v : ℤ) := by
    have h := dvd_sub hres (hln.trans hmod)
    simpa using h
  have hlv' : l ∣ v := by exact_mod_cast hlv
  obtain ⟨k, hk⟩ := hlv'
  refine ⟨(k : ℤ), by positivity, ?_, ?_⟩
  · have hkn : k < n / l := by
      rw [Nat.lt_div_iff_mul_lt' hdvd]
      rw [hk] at hvn
      simpa [Nat.mul_comm] using hvn
    exact_mod_cast hkn
  · have hk' : (v : ℤ) = (l : ℤ) * (k : ℤ) := by exact_mod_cast hk
    have hmul : ((u - o - t : ℤ) : ZMod n) = (((l : ℤ) * (k : ℤ) : ℤ) : ZMod n) := by
      rw [← hcast, hk']
    have h2 : ((u : ℤ) : ZMod n) = (((u - o - t) + o + t : ℤ) : ZMod n) := by
      congr 1
      ring
    rw [h2]
    push_cast at hmul ⊢
    rw [hmul]
    ring
theorem shiftedGridsCoverTorus : shiftedGridsCoverTorusStatement := by
  intro n r _ G hcomp hodd hr x
  obtain ⟨s, hs⟩ := hodd
  have hsideZ : (G.side : ℤ) = 2 * (s : ℤ) + 1 := by exact_mod_cast hs
  have hhalf : ((G.side : ℤ) - 1) / 2 = (s : ℤ) := by omega
  have hrZ : 128 * (r : ℤ) ≤ (G.side : ℤ) := by
    have h : (2 ^ 7 * r : ℕ) ≤ G.side := hr
    have h' : ((2 ^ 7 * r : ℕ) : ℤ) ≤ (G.side : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hdvd : G.side ∣ n := (Dvd.intro_left 2 rfl).trans hcomp.two_mul_side_dvd
  have hu : ∀ i, ∃ u : ℤ, (u : ZMod n) = x i := fun i => ZMod.intCast_surjective (x i)
  choose u hu using hu
  have hch := fun i => exists_residue_far_from_walls (G.side : ℤ) (s : ℤ) r hsideZ hrZ (by positivity)
    (u i - G.offset i)
  choose b t ht0 htl htlo hthi hres using hch
  classical
  refine ⟨Finset.univ.filter fun i => b i = true, ?_⟩
  have hoff : ∀ i, (G.shift (Finset.univ.filter fun i => b i = true)).offset i =
      G.offset i + (if b i = true then (s : ℤ) else 0) := by
    intro i
    by_cases hbi : b i = true
    · simp [CellGrid.shift, hbi, hhalf]
    · simp [CellGrid.shift, hbi]
  have hside : (G.shift (Finset.univ.filter fun i => b i = true)).side = G.side := rfl
  set M := G.shift (Finset.univ.filter fun i => b i = true) with hM
  have hidx := fun i => exists_cell_index_of_dvd n G.side hdvd (u i) (M.offset i) (t i) (by
    have h := hres i
    rw [hoff i]
    have e : u i - (G.offset i + (if b i = true then (s : ℤ) else 0)) - t i =
        u i - G.offset i - (if b i = true then (s : ℤ) else 0) - t i := by ring
    rw [e]
    exact h)
  choose κ hκ0 hκn hκ using hidx
  refine ⟨κ, ?_, ?_⟩
  · simp only [CellGrid.indices, Fintype.mem_piFinset, Finset.mem_Ico, hside]
    exact fun i => ⟨hκ0 i, hκn i⟩
  · have hnear : ∀ w : TorusSite n, (∃ d : Fin 4 → ℤ, (∀ i, 0 ≤ t i - d i ∧ t i - d i < (G.side : ℤ)) ∧
        ∀ i, w i = ((M.offset i + (G.side : ℤ) * κ i + (t i - d i) : ℤ) : ZMod n)) → w ∈ M.cell n κ := by
      rintro w ⟨d, hd, hw⟩
      simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i => t i - d i, hd, ?_⟩
      funext i
      simpa [siteOfInt, hside] using hw i
    simp only [interiorAtDepth, Finset.mem_filter]
    refine ⟨hnear x ⟨0, fun i => by simpa using ⟨ht0 i, htl i⟩, fun i => ?_⟩, ?_⟩
    · have h := hκ i
      rw [hu i] at h
      simpa using h
    · intro w hw
      by_contra hlt
      apply hw
      refine hnear w ⟨fun i => ((x i - w i).valMinAbs), fun i => ?_, fun i => ?_⟩
      · beta_reduce
        have hle : ((x i - w i).valMinAbs).natAbs ≤ supDist x w :=
          Finset.le_sup (f := fun i => ((x i - w i).valMinAbs).natAbs) (Finset.mem_univ i)
        have h1 := ht0 i
        have h3 := htlo i
        have h4 := hthi i
        omega
      · have hx := hκ i
        rw [hu i] at hx
        push_cast at hx ⊢
        linear_combination hx
end YangMills.Construction.CellWindows
end
