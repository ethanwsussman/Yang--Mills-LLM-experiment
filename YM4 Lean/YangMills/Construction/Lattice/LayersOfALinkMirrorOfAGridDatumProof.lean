import YangMills.Construction.Lattice.CellGridPropertiesProofs
import YangMills.Construction.Lattice.LayersOfALinkMirrorOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BoxTorus PeriodicLattice
namespace MirrorLayers
open TorusDescent
variable {L : ℕ} {κ : ℤ}
def scaledPoint (L : ℕ) (κ : ℤ) (n : Fin 4 → ℤ) : Fin 4 → ℝ :=
  fun μ => (n μ : ℝ) * meshSize L κ
theorem meshSize_pos (d : CellGrid L κ) : 0 < meshSize L κ := by apply _root_.YangMills.Construction.GridLattice.meshSize_pos <;> assumption
theorem exists_halfCount (d : CellGrid L κ) (μ : Fin 4) :
    ∃ h : ℕ, 2 ≤ h ∧ d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ := by
  obtain ⟨z, -, hs⟩ := d.exists_sideLengths_eq
  have ha := meshSize_pos d
  obtain ⟨r, hr⟩ := d.counts_even μ
  have hM : d.sideLengths μ = 2 * (((r : ℤ) * z : ℤ) : ℝ) * meshSize L κ := by
    rw [hs μ, hr]
    push_cast
    ring
  have h4 : 4 * meshSize L κ ≤ d.sideLengths μ := d.four_meshSize_le μ
  rw [hM] at h4
  have h2 : (2 : ℝ) ≤ (((r : ℤ) * z : ℤ) : ℝ) := by
    by_contra hn
    have hn := not_le.mp hn
    nlinarith
  have h2' : (2 : ℤ) ≤ (r : ℤ) * z := by exact_mod_cast h2
  refine ⟨((r : ℤ) * z).toNat, by omega, ?_⟩
  rw [hM]
  have e : ((((r : ℤ) * z).toNat : ℤ)) = (r : ℤ) * z := Int.toNat_of_nonneg (by omega)
  have e' : ((((r : ℤ) * z).toNat : ℕ) : ℝ) = (((r : ℤ) * z : ℤ) : ℝ) := by
    exact_mod_cast e
  rw [e']
theorem exists_int_of_projection_eq (d : CellGrid L κ) {w w' : Fin 4 → ℝ}
    (h : projection d.sideLengths w = projection d.sideLengths w') (μ : Fin 4) :
    ∃ k : ℤ, w μ - w' μ = k * d.sideLengths μ := by
  have h1 : ((w μ : ℝ) : AddCircle (d.sideLengths μ)) = (w' μ : ℝ) := congrFun h μ
  have h2 : ((w μ - w' μ : ℝ) : AddCircle (d.sideLengths μ)) = 0 := by
    rw [AddCircle.coe_sub, h1, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp h2
  exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩
theorem projection_eq_of_int (d : CellGrid L κ) {w w' : Fin 4 → ℝ}
    (h : ∀ ν, ∃ k : ℤ, w ν - w' ν = k * d.sideLengths ν) :
    projection d.sideLengths w = projection d.sideLengths w' := by
  funext ν
  obtain ⟨k, hk⟩ := h ν
  show ((w ν : ℝ) : AddCircle (d.sideLengths ν)) = (w' ν : ℝ)
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact ⟨k, by rw [hk, zsmul_eq_mul]⟩
theorem int_diff_of_scaledPoint_eq (d : CellGrid L κ) {μ : Fin 4} {h : ℕ}
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) {n n' : Fin 4 → ℤ}
    (e : projection d.sideLengths (scaledPoint L κ n) = projection d.sideLengths (scaledPoint L κ n')) :
    ∃ k : ℤ, n μ - n' μ = k * (2 * (h : ℤ)) := by
  obtain ⟨k, hk⟩ := exists_int_of_projection_eq d e μ
  refine ⟨k, ?_⟩
  have ha := (meshSize_pos d).ne'
  simp only [scaledPoint] at hk
  rw [hs] at hk
  have h1 : ((n μ - n' μ : ℤ) : ℝ) = ((k * (2 * (h : ℤ)) : ℤ) : ℝ) := by
    push_cast
    apply mul_right_cancel₀ ha
    linarith
  exact_mod_cast h1
def intLift {d : CellGrid L κ} (x : d.GridPoint) : Fin 4 → ℤ := Classical.choose x.2
theorem intLift_spec {d : CellGrid L κ} (x : d.GridPoint) :
    (x : d.Space) = projection d.sideLengths (scaledPoint L κ (intLift x)) :=
  Classical.choose_spec x.2
theorem exists_int_of_projection (d : CellGrid L κ) {μ : Fin 4} {h : ℕ}
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) (x : d.GridPoint) {w : Fin 4 → ℝ}
    (hw : projection d.sideLengths w = (x : d.Space)) : ∃ m : ℤ, w μ = m * meshSize L κ := by
  obtain ⟨k, hk⟩ := exists_int_of_projection_eq d (hw.trans (intLift_spec x)) μ
  refine ⟨intLift x μ + k * (2 * (h : ℤ)), ?_⟩
  simp only [scaledPoint] at hk
  rw [hs] at hk
  push_cast
  linarith
def layer {d : CellGrid L κ} (μ : Fin 4) (z : ℤ) (h : ℕ) (x : d.GridPoint) : ZMod (2 * h) :=
  ((intLift x μ - z : ℤ) : ZMod (2 * h))
theorem two_mul_cast_eq_zero (h : ℕ) : (2 * (h : ZMod (2 * h))) = 0 := by
  exact_mod_cast ZMod.natCast_self (2 * h)
theorem layer_eq {d : CellGrid L κ} {μ : Fin 4} (z : ℤ) {h : ℕ}
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) (x : d.GridPoint) (n : Fin 4 → ℤ)
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n)) :
    layer μ z h x = ((n μ - z : ℤ) : ZMod (2 * h)) := by
  obtain ⟨k, hk⟩ := int_diff_of_scaledPoint_eq d hs ((intLift_spec x).symm.trans hx)
  have e : intLift x μ - z = (n μ - z) + k * (2 * (h : ℤ)) := by linarith
  rw [layer, e]
  push_cast
  rw [two_mul_cast_eq_zero]
  simp
theorem add_unitStep_eq {d : CellGrid L κ} (x : d.GridPoint) (n : Fin 4 → ℤ)
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n)) (ν : Fin 4) :
    ((x + BoxTorus.gridStep L κ d.sideLengths ν : d.GridPoint) : d.Space) =
      projection d.sideLengths (scaledPoint L κ (n + Pi.single ν 1)) := by
  show (x : d.Space) + projection d.sideLengths (meshSize L κ • basisVector ν) = _
  rw [hx, ← map_add]
  congr 1
  funext μ
  by_cases e : μ = ν
  · subst e
    simp [scaledPoint, basisVector]
    ring
  · simp [scaledPoint, basisVector, Pi.single_eq_of_ne e]
theorem sub_unitStep_eq {d : CellGrid L κ} (x : d.GridPoint) (n : Fin 4 → ℤ)
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n)) (ν : Fin 4) :
    ((x - BoxTorus.gridStep L κ d.sideLengths ν : d.GridPoint) : d.Space) =
      projection d.sideLengths (scaledPoint L κ (n - Pi.single ν 1)) := by
  show (x : d.Space) - projection d.sideLengths (meshSize L κ • basisVector ν) = _
  rw [hx, ← map_sub]
  congr 1
  funext μ
  by_cases e : μ = ν
  · subst e
    simp [scaledPoint, basisVector]
    ring
  · simp [scaledPoint, basisVector, Pi.single_eq_of_ne e]
theorem pointImage_eq {d : CellGrid L κ} {g : d.GridSymmetry} {μ : Fin 4} {c : ℝ}
    (hg : d.IsInducedMap g.toFun (coordReflection μ c)) {z : ℤ}
    (hc : c = meshSize L κ * ((z : ℝ) + 1 / 2)) (x : d.GridPoint) (n : Fin 4 → ℤ)
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n)) :
    ((g.pointImage x : d.GridPoint) : d.Space) =
      projection d.sideLengths (scaledPoint L κ (Function.update n μ (2 * z + 1 - n μ))) := by
  show g.toFun (x : d.Space) = _
  rw [hx]
  refine (congrFun hg (scaledPoint L κ n)).trans ?_
  show projection d.sideLengths (coordReflection μ c (scaledPoint L κ n)) = _
  congr 1
  funext ν
  by_cases e : ν = μ
  · subst e
    simp [coordReflection, scaledPoint, basisVector, hc]
    ring
  · simp [coordReflection, scaledPoint, basisVector, Pi.single_eq_of_ne e, Function.update_of_ne e]
theorem gridPoint_eq {d : CellGrid L κ} {μ : Fin 4} {h : ℕ}
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) {x y : d.GridPoint} {n n' : Fin 4 → ℤ}
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n))
    (hy : (y : d.Space) = projection d.sideLengths (scaledPoint L κ n'))
    (hν : ∀ ν, ν ≠ μ → n ν = n' ν) (k : ℤ) (hμ : n μ - n' μ = k * (2 * (h : ℤ))) : x = y := by
  refine Subtype.ext (hx.trans (Eq.trans ?_ hy.symm))
  refine projection_eq_of_int d fun ν => ?_
  by_cases e : ν = μ
  · subst e
    refine ⟨k, ?_⟩
    simp only [scaledPoint]
    rw [hs]
    have h1 : ((n ν : ℝ) - n' ν) = k * (2 * (h : ℝ)) := by exact_mod_cast hμ
    rw [← sub_mul, h1]
    ring
  · exact ⟨0, by simp [scaledPoint, hν ν e]⟩
theorem int_bounds_of_slab (d : CellGrid L κ) {h : ℕ} {e e' : ℝ} {z' m : ℤ}
    (he : e = meshSize L κ * ((z' : ℝ) + 1 / 2)) (he' : e' = e + (h : ℝ) * meshSize L κ)
    (h₁ : e < (m : ℝ) * meshSize L κ) (h₂ : (m : ℝ) * meshSize L κ < e') :
    z' + 1 ≤ m ∧ m ≤ z' + h := by
  have ha := meshSize_pos d
  subst he' he
  have a₁ : (2 * (z' : ℝ) + 1) < 2 * (m : ℝ) := by
    by_contra hn
    have hn := not_lt.mp hn
    nlinarith
  have a₂ : 2 * (m : ℝ) < 2 * (z' : ℝ) + 1 + 2 * (h : ℝ) := by
    by_contra hn
    have hn := not_lt.mp hn
    nlinarith
  have b₁ : 2 * z' + 1 < 2 * m := by exact_mod_cast a₁
  have b₂ : 2 * m < 2 * z' + 1 + 2 * (h : ℤ) := by exact_mod_cast a₂
  omega
theorem mem_slab_iff_exists {d : CellGrid L κ} {μ : Fin 4} {h : ℕ}
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) {e e' : ℝ} {z' : ℤ}
    (he : e = meshSize L κ * ((z' : ℝ) + 1 / 2)) (he' : e' = e + (h : ℝ) * meshSize L κ)
    (x : d.GridPoint) (n : Fin 4 → ℤ)
    (hx : (x : d.Space) = projection d.sideLengths (scaledPoint L κ n)) :
    (x : d.Space) ∈ slab d.sideLengths μ e e' ↔
      ∃ k : ℤ, z' + 1 ≤ n μ + k * (2 * (h : ℤ)) ∧ n μ + k * (2 * (h : ℤ)) ≤ z' + h := by
  have ha := meshSize_pos d
  constructor
  · rintro ⟨w, ⟨h₁, h₂⟩, hw⟩
    obtain ⟨k, hk⟩ := exists_int_of_projection_eq d (hw.trans hx) μ
    refine ⟨k, ?_⟩
    simp only [scaledPoint] at hk
    rw [hs] at hk
    have e₁ : w μ = ((n μ + k * (2 * (h : ℤ)) : ℤ) : ℝ) * meshSize L κ := by
      push_cast
      linarith
    rw [e₁] at h₁ h₂
    exact int_bounds_of_slab d he he' h₁ h₂
  · rintro ⟨k, h₁, h₂⟩
    refine ⟨scaledPoint L κ (Function.update n μ (n μ + k * (2 * (h : ℤ)))), ?_, ?_⟩
    · have c₁ : ((z' : ℝ) + 1) ≤ ((n μ + k * (2 * (h : ℤ)) : ℤ) : ℝ) := by exact_mod_cast h₁
      have c₂ : ((n μ + k * (2 * (h : ℤ)) : ℤ) : ℝ) ≤ (z' : ℝ) + h := by exact_mod_cast h₂
      have e₁ : scaledPoint L κ (Function.update n μ (n μ + k * (2 * (h : ℤ)))) μ =
          ((n μ + k * (2 * (h : ℤ)) : ℤ) : ℝ) * meshSize L κ := by
        simp [scaledPoint]
      show e < _ ∧ _ < e'
      rw [e₁]
      subst he' he
      constructor <;> nlinarith
    · rw [hx]
      refine projection_eq_of_int d fun ν => ?_
      by_cases e₁ : ν = μ
      · subst e₁
        refine ⟨k, ?_⟩
        simp only [scaledPoint, Function.update_self]
        rw [hs]
        push_cast
        ring
      · exact ⟨0, by simp [scaledPoint, Function.update_of_ne e₁]⟩
theorem le_mul_or_mul_le_neg {t P : ℤ} (hP : 0 < P) (ht : t ≠ 0) : P ≤ t * P ∨ t * P ≤ -P := by
  rcases lt_or_gt_of_ne ht with h | h
  · right
    nlinarith
  · left
    nlinarith
theorem exists_residue {h : ℕ} (hh : 2 ≤ h) (n z : ℤ) :
    ∃ r q : ℤ, ((((n - z : ℤ) : ZMod (2 * h)).val : ℕ) : ℤ) = r ∧ 0 ≤ r ∧ r < 2 * (h : ℤ) ∧
      n - z = r + q * (2 * (h : ℤ)) := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have hP : (0 : ℤ) < 2 * (h : ℤ) := by omega
  refine ⟨(n - z) % (2 * (h : ℤ)), (n - z) / (2 * (h : ℤ)), ?_,
    Int.emod_nonneg _ hP.ne', Int.emod_lt_of_pos _ hP, ?_⟩
  · rw [ZMod.val_intCast, Nat.cast_mul, Nat.cast_ofNat]
  · have hq := Int.emod_add_mul_ediv (n - z) (2 * (h : ℤ))
    linarith
theorem val_mem_Icc_iff {h : ℕ} (hh : 2 ≤ h) (n z : ℤ) :
    (∃ k : ℤ, z + 1 ≤ n + k * (2 * (h : ℤ)) ∧ n + k * (2 * (h : ℤ)) ≤ z + h) ↔
      ((n - z : ℤ) : ZMod (2 * h)).val ∈ Finset.Icc 1 h := by
  obtain ⟨r, q, hv, h0, h1, hq⟩ := exists_residue hh n z
  have hP : (0 : ℤ) < 2 * (h : ℤ) := by omega
  generalize ((n - z : ℤ) : ZMod (2 * h)).val = v at hv ⊢
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨k, a₁, a₂⟩
    have e : n + k * (2 * (h : ℤ)) - z = r + (k + q) * (2 * (h : ℤ)) := by linarith
    by_cases ht : k + q = 0
    · rw [ht] at e
      omega
    · have := le_mul_or_mul_le_neg hP ht
      omega
  · rintro ⟨a₁, a₂⟩
    refine ⟨-q, ?_⟩
    have e : n + -q * (2 * (h : ℤ)) - z = r := by linarith
    omega
theorem val_not_mem_Icc_iff {h : ℕ} (hh : 2 ≤ h) (n z : ℤ) :
    (∃ k : ℤ, z - h + 1 ≤ n + k * (2 * (h : ℤ)) ∧ n + k * (2 * (h : ℤ)) ≤ z - h + h) ↔
      ((n - z : ℤ) : ZMod (2 * h)).val ∉ Finset.Icc 1 h := by
  obtain ⟨r, q, hv, h0, h1, hq⟩ := exists_residue hh n z
  have hP : (0 : ℤ) < 2 * (h : ℤ) := by omega
  generalize ((n - z : ℤ) : ZMod (2 * h)).val = v at hv ⊢
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨k, a₁, a₂⟩ ⟨b₁, b₂⟩
    have e : n + k * (2 * (h : ℤ)) - z = r + (k + q) * (2 * (h : ℤ)) := by linarith
    by_cases ht : k + q = 0
    · rw [ht] at e
      omega
    · have := le_mul_or_mul_le_neg hP ht
      omega
  · intro hn
    have hn' : r = 0 ∨ (h : ℤ) + 1 ≤ r := by
      by_contra hc
      exact hn (by omega)
    rcases hn' with e₀ | e₀
    · refine ⟨-q, ?_⟩
      have e : n + -q * (2 * (h : ℤ)) - z = r := by linarith
      omega
    · refine ⟨-q - 1, ?_⟩
      have e : n + (-q - 1) * (2 * (h : ℤ)) - z = r - 2 * (h : ℤ) := by linarith
      omega
theorem liesIn_slab_of_endpoints {d : CellGrid L κ} {μ : Fin 4} {h : ℕ} (hh : 2 ≤ h)
    (hs : d.sideLengths μ = 2 * (h : ℝ) * meshSize L κ) {e e' : ℝ} {z' : ℤ}
    (he : e = meshSize L κ * ((z' : ℝ) + 1 / 2)) (he' : e' = e + (h : ℝ) * meshSize L κ)
    (b : d.DirectedEdge) (h₁ : (b.source : d.Space) ∈ slab d.sideLengths μ e e')
    (h₂ : (b.target : d.Space) ∈ slab d.sideLengths μ e e') :
    b.LiesIn (slab d.sideLengths μ e e') := by
  have ha := meshSize_pos d
  rintro T ⟨ν, σ, hst, rfl⟩ p ⟨t, ⟨t₀, t₁⟩, rfl⟩
  obtain ⟨w₀, ⟨a₀, a₁⟩, hw₀⟩ := h₁
  obtain ⟨w₁, ⟨c₀, c₁⟩, hw₁⟩ := h₂
  refine ⟨w₀ + (t * σ * meshSize L κ) • basisVector ν, ?_, ?_⟩
  · by_cases hν : ν = μ
    · subst hν
      obtain ⟨m₀, hm₀⟩ := exists_int_of_projection d hs b.source hw₀
      obtain ⟨m₁, hm₁⟩ := exists_int_of_projection d hs b.target hw₁
      have hq : projection d.sideLengths w₁ =
          projection d.sideLengths (w₀ + (σ * meshSize L κ) • basisVector ν) := by
        rw [hw₁, hst.2, map_add, hw₀]
        rfl
      obtain ⟨k, hk⟩ := exists_int_of_projection_eq d hq ν
      have hk' : w₁ ν - (w₀ ν + σ * meshSize L κ) = k * d.sideLengths ν := by
        simpa [basisVector] using hk
      rw [hm₀] at a₀ a₁
      rw [hm₁] at c₀ c₁
      obtain ⟨i₀, i₁⟩ := int_bounds_of_slab d he he' a₀ a₁
      obtain ⟨j₀, j₁⟩ := int_bounds_of_slab d he he' c₀ c₁
      have hP : (0 : ℤ) < 2 * (h : ℤ) := by omega
      have hstep : w₁ ν = w₀ ν + σ * meshSize L κ := by
        rw [hs, hm₀, hm₁] at hk'
        have hk₂ : (m₁ : ℝ) - ((m₀ : ℝ) + σ) = k * (2 * (h : ℝ)) := by
          apply mul_right_cancel₀ ha.ne'
          linarith
        have hk₀ : k = 0 := by
          by_contra hne
          have hb := le_mul_or_mul_le_neg hP hne
          rcases hst.1 with es | es
          · rw [es] at hk₂
            have hi : m₁ - (m₀ + 1) = k * (2 * (h : ℤ)) := by exact_mod_cast hk₂
            omega
          · rw [es] at hk₂
            have hi : m₁ - (m₀ + -1) = k * (2 * (h : ℤ)) := by exact_mod_cast hk₂
            omega
        rw [hk₀, Int.cast_zero, zero_mul] at hk'
        rw [hm₀, hm₁]
        linarith
      rw [← hm₀] at a₀ a₁
      rw [← hm₁] at c₀ c₁
      have hco : (w₀ + (t * σ * meshSize L κ) • basisVector ν) ν = w₀ ν + t * σ * meshSize L κ := by
        simp [basisVector]
      show e < _ ∧ _ < e'
      rw [hco]
      rcases hst.1 with es | es
      · rw [es] at hstep ⊢
        constructor <;> nlinarith
      · rw [es] at hstep ⊢
        constructor <;> nlinarith
    · have hco : (w₀ + (t * σ * meshSize L κ) • basisVector ν) μ = w₀ μ := by
        simp [basisVector, Pi.single_eq_of_ne (Ne.symm hν)]
      show e < _ ∧ _ < e'
      rw [hco]
      exact ⟨a₀, a₁⟩
  · rw [map_add, hw₀]
    rfl
theorem endpoints_mem_of_liesIn {d : CellGrid L κ} (b : d.DirectedEdge) {S : Set d.Space}
    (hb : b.LiesIn S) : (b.source : d.Space) ∈ S ∧ (b.target : d.Space) ∈ S := by
  obtain ⟨ν, σ, hst⟩ := b.isNeighbour
  have hT := hb _ ⟨ν, σ, hst, rfl⟩
  constructor
  · refine hT ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    simp [BoxTorus.translate]
  · refine hT ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    rw [hst.2]
    simp
theorem exists_mul_of_cast_eq {h : ℕ} {u v : ℤ}
    (e : ((u : ℤ) : ZMod (2 * h)) = (v : ZMod (2 * h))) : ∃ k : ℤ, u - v = k * (2 * (h : ℤ)) := by
  have h₁ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v (2 * h)).mp e
  obtain ⟨k, hk⟩ := h₁
  refine ⟨-k, ?_⟩
  push_cast at hk
  linarith
theorem layering : LayeringTheorem := by
  intro L κ d g μ c hg
  obtain ⟨⟨z, hc⟩, hind⟩ := hg
  obtain ⟨h, hh, hs⟩ := exists_halfCount d μ
  have hup : ∀ (x : d.GridPoint), (x : d.Space) ∈ posHalf d μ c ↔
      (layer μ z h x).val ∈ Finset.Icc 1 h := fun x => by
    have he' : c + 1 / 2 * d.sideLengths μ = c + (h : ℝ) * meshSize L κ := by rw [hs]; ring
    rw [posHalf, mem_slab_iff_exists hs hc he' x _ (intLift_spec x), layer]
    exact val_mem_Icc_iff hh _ _
  have hlow : ∀ (x : d.GridPoint), (x : d.Space) ∈ negHalf d μ c ↔
      (layer μ z h x).val ∉ Finset.Icc 1 h := fun x => by
    have he : c - 1 / 2 * d.sideLengths μ = meshSize L κ * (((z - h : ℤ) : ℝ) + 1 / 2) := by
      rw [hs, hc]
      push_cast
      ring
    have he' : c = c - 1 / 2 * d.sideLengths μ + (h : ℝ) * meshSize L κ := by rw [hs]; ring
    rw [negHalf, mem_slab_iff_exists hs he he' x _ (intLift_spec x), layer]
    exact val_not_mem_Icc_iff hh _ _
  refine ⟨h, hh, layer μ z h, ?_, ?_, ?_, ?_, ?_, ?_, hup, hlow, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [layer_eq z hs _ _ (add_unitStep_eq x _ (intLift_spec x) μ), layer]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast
    ring
  · intro x ν hν
    rw [layer_eq z hs _ _ (add_unitStep_eq x _ (intLift_spec x) ν), layer]
    simp [Pi.single_eq_of_ne (Ne.symm hν)]
  · intro x
    rw [layer_eq z hs _ _ (pointImage_eq hind hc x _ (intLift_spec x)), layer]
    simp only [Function.update_self]
    push_cast
    ring
  · intro x ν hν
    have l₁ := pointImage_eq hind hc _ _ (add_unitStep_eq x _ (intLift_spec x) ν)
    have l₂ := add_unitStep_eq _ _ (pointImage_eq hind hc x _ (intLift_spec x)) ν
    refine gridPoint_eq hs l₁ l₂ (fun ρ hρ => ?_) 0 ?_
    · simp [Function.update_of_ne hρ]
    · simp [Pi.single_eq_of_ne (Ne.symm hν)]
  · intro x
    have l₁ := pointImage_eq hind hc _ _ (add_unitStep_eq x _ (intLift_spec x) μ)
    have l₂ := sub_unitStep_eq _ _ (pointImage_eq hind hc x _ (intLift_spec x)) μ
    refine gridPoint_eq hs l₁ l₂ (fun ρ hρ => ?_) 0 ?_
    · simp [Function.update_of_ne hρ, Pi.single_eq_of_ne hρ]
    · simp
      ring
  · intro x
    have l₁ := pointImage_eq hind hc _ _ (pointImage_eq hind hc x _ (intLift_spec x))
    refine gridPoint_eq hs l₁ (intLift_spec x) (fun ρ hρ => ?_) 0 ?_
    · simp [Function.update_of_ne hρ]
    · simp
  · intro x hx
    have e : ((intLift x μ - z : ℤ) : ZMod (2 * h)) = ((1 : ℤ) : ZMod (2 * h)) := by
      rw [← layer, hx]
      simp
    obtain ⟨k, hk⟩ := exists_mul_of_cast_eq e
    have l₁ := pointImage_eq hind hc x _ (intLift_spec x)
    have l₂ := sub_unitStep_eq x _ (intLift_spec x) μ
    refine gridPoint_eq hs l₁ l₂ (fun ρ hρ => ?_) (-2 * k) ?_
    · simp [Function.update_of_ne hρ, Pi.single_eq_of_ne hρ]
    · simp only [Function.update_self, Pi.sub_apply, Pi.single_eq_same]
      linarith
  · intro x hx
    have e : ((intLift x μ - z : ℤ) : ZMod (2 * h)) = (((h : ℤ) : ℤ) : ZMod (2 * h)) := by
      rw [← layer, hx]
      simp
    obtain ⟨k, hk⟩ := exists_mul_of_cast_eq e
    have l₁ := pointImage_eq hind hc x _ (intLift_spec x)
    have l₂ := add_unitStep_eq x _ (intLift_spec x) μ
    refine gridPoint_eq hs l₁ l₂ (fun ρ hρ => ?_) (-1 - 2 * k) ?_
    · simp [Function.update_of_ne hρ, Pi.single_eq_of_ne hρ]
    · simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
      linarith
  · intro b
    have he' : c + 1 / 2 * d.sideLengths μ = c + (h : ℝ) * meshSize L κ := by rw [hs]; ring
    exact ⟨endpoints_mem_of_liesIn b,
      fun hb => liesIn_slab_of_endpoints hh hs hc he' b hb.1 hb.2⟩
  · intro b
    have he : c - 1 / 2 * d.sideLengths μ = meshSize L κ * (((z - h : ℤ) : ℝ) + 1 / 2) := by
      rw [hs, hc]
      push_cast
      ring
    have he' : c = c - 1 / 2 * d.sideLengths μ + (h : ℝ) * meshSize L κ := by rw [hs]; ring
    exact ⟨endpoints_mem_of_liesIn b,
      fun hb => liesIn_slab_of_endpoints hh hs he he' b hb.1 hb.2⟩
end MirrorLayers
end YangMills.Construction
end
