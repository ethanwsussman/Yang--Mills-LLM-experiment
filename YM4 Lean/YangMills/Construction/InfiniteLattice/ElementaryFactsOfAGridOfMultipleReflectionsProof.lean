import YangMills.Construction.InfiniteLattice.ElementaryFactsOfAGridOfMultipleReflections
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorusProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
noncomputable section
namespace MultipleReflections
namespace GridFacts
open Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem mesh_eq_spacingAt : CutoffLattice.spacingAt D.L (D.K : ℕ) = D.mesh := rfl
theorem mesh_pos : 0 < D.mesh := by apply _root_.YangMills.Construction.MultipleReflections.TorusPullback.mesh_pos <;> assumption
theorem edgeOverSpacingOdd {p : ℤ} (hp : G.edge = (D.L : ℝ) ^ p) :
    G.EdgeOverSpacingOdd p := by
  have hL := D.one_lt_L
  have hL0 : (D.L : ℝ) ≠ 0 := (zero_lt_one.trans hL).ne'
  have htile : 2 - ((D.K : ℕ) : ℤ) ≤ p :=
    (D.isTileEdge_zpow_iff p).1 (hp ▸ G.isTileEdge_edge)
  have hm : D.mesh = (D.L : ℝ) ^ (-((D.K : ℕ) : ℤ)) := rfl
  have hq : G.edge / D.mesh = (D.L : ℝ) ^ (p + ((D.K : ℕ) : ℤ)) := by
    rw [hp, hm, zpow_add₀ hL0, zpow_neg, div_inv_eq_mul]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, p + ((D.K : ℕ) : ℤ) = (t : ℤ) :=
    ⟨(p + ((D.K : ℕ) : ℤ)).toNat, by omega⟩
  have hodd : Odd (D.L ^ t) := D.isAdmissible.1.pow
  have hpow : (D.L : ℝ) ^ (p + ((D.K : ℕ) : ℤ)) = ((D.L ^ t : ℕ) : ℝ) := by
    rw [ht, zpow_natCast]
    push_cast
    rfl
  obtain ⟨i, hi⟩ := hodd
  refine ⟨hq, ⟨((D.L ^ t : ℕ) : ℤ), ?_, ?_⟩, (i : ℤ), ?_⟩
  · rw [hi]
    exact ⟨(i : ℤ), by push_cast; ring⟩
  · rw [hpow]
    norm_cast
  · have hm0 : D.mesh ≠ 0 := mesh_pos.ne'
    have hs : G.edge = D.mesh * (2 * (i : ℝ) + 1) := by
      have h1 : G.edge / D.mesh = 2 * (i : ℝ) + 1 := by
        rw [hq, hpow, hi]
        push_cast
        ring
      rw [← h1]
      field_simp
    rw [hs]
    push_cast
    ring
theorem exists_half_edge : ∃ i : ℤ, G.edge / 2 = D.mesh * ((i : ℝ) + 1 / 2) := by
  obtain ⟨⟨p, hp⟩, -⟩ := G.isTileEdge_edge
  exact (edgeOverSpacingOdd G hp).2.2
theorem axial_realNormal_dotProduct (α : Fin 4) (x : AmbientSpace) :
    (InfiniteLattice.ReflectionClass.axial α).realNormal ⬝ᵥ x = x α := by
  fin_cases α <;>
    simp [InfiniteLattice.ReflectionClass.realNormal, InfiniteLattice.ReflectionClass.intNormal,
      dotProduct, Fin.sum_univ_four]
theorem wallsBisectLinks : G.WallsBisectLinks := by
  intro α n
  obtain ⟨N, hN⟩ := InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
  obtain ⟨i, hi⟩ := G.shift_mem α
  rw [mesh_eq_spacingAt] at hN hi
  have hshift : G.shift α + (n : ℝ) * G.edge = (((i + n * N : ℤ) : ℝ) + 1 / 2) * D.mesh := by
    rw [hi, hN]
    push_cast
    ring
  refine ⟨⟨.axial α, G.shift α + (n : ℝ) * G.edge, ?_⟩, rfl, ?_, ⟨i + n * N, hshift⟩⟩
  · show ∃ q : ℤ, G.shift α + (n : ℝ) * G.edge = (q : ℝ) * (D.mesh / 2)
    refine ⟨2 * (i + n * N) + 1, ?_⟩
    rw [hshift]
    push_cast
    ring
  · ext x
    show (InfiniteLattice.ReflectionClass.axial α).realNormal ⬝ᵥ x = _ ↔ _
    rw [axial_realNormal_dotProduct]
    rfl
theorem cornerAt_apply (k : Fin 4 → ℤ) (α : Fin 4) :
    G.cornerAt k α = G.shift α + G.edge * (k α : ℝ) := rfl
theorem tileCentersAreSites : G.TileCentersAreSites := by
  intro k
  obtain ⟨N, hN⟩ := InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
  obtain ⟨h, hh⟩ := exists_half_edge G
  choose i hi using G.shift_mem
  rw [mesh_eq_spacingAt] at hN
  simp only [mesh_eq_spacingAt] at hi
  refine ⟨fun α => i α + k α * N + h + 1, fun α => ?_⟩
  have hsum : (∑ μ, InfiniteLattice.ReflectionGrid.basisVec μ : AmbientSpace) α = 1 := by
    fin_cases α <;> simp [InfiniteLattice.ReflectionGrid.basisVec]
  show G.cornerAt k α + (G.edge / 2) * (∑ μ, InfiniteLattice.ReflectionGrid.basisVec μ : AmbientSpace) α = _
  rw [hsum, cornerAt_apply, hh, hi, hN]
  show _ = _ * D.mesh
  push_cast
  ring
variable {G}
theorem IsCoordinateMove.id (α : Fin 4) : G.IsCoordinateMove α id :=
  Or.inl ⟨0, fun y => by simp⟩
theorem IsCoordinateMove.comp {α : Fin 4} {δ δ' : ℝ → ℝ} (h : G.IsCoordinateMove α δ)
    (h' : G.IsCoordinateMove α δ') : G.IsCoordinateMove α (δ ∘ δ') := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ <;> rcases h' with ⟨n', hn'⟩ | ⟨n', hn'⟩
  · exact Or.inl ⟨n + n', fun y => by
      simp only [Function.comp, hn, hn']; push_cast; ring⟩
  · exact Or.inr ⟨n' + n, fun y => by
      simp only [Function.comp, hn, hn']; push_cast; ring⟩
  · exact Or.inr ⟨n - n', fun y => by
      simp only [Function.comp, hn, hn']; push_cast; ring⟩
  · exact Or.inl ⟨n - n', fun y => by
      simp only [Function.comp, hn, hn']; push_cast; ring⟩
theorem IsCoordinateMove.exists_leftInverse {α : Fin 4} {δ : ℝ → ℝ}
    (h : G.IsCoordinateMove α δ) :
    ∃ δ', G.IsCoordinateMove α δ' ∧ ∀ y, δ' (δ y) = y := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨fun y => y + 2 * ((-n : ℤ) : ℝ) * G.edge, Or.inl ⟨-n, fun y => rfl⟩, fun y => ?_⟩
    rw [hn]
    push_cast
    ring
  · exact ⟨δ, Or.inr ⟨n, hn⟩, fun y => by rw [hn, hn]; ring⟩
variable (G)
theorem wallReflect_apply_self (α : Fin 4) (n : ℤ) (x : AmbientSpace) :
    G.wallReflect α n x α = 2 * (G.shift α + (n : ℝ) * G.edge) - x α := by
  simp [InfiniteLattice.ReflectionGrid.wallReflect, InfiniteLattice.ReflectionGrid.basisVec]
  ring
theorem wallReflect_apply_of_ne {α β : Fin 4} (h : β ≠ α) (n : ℤ) (x : AmbientSpace) :
    G.wallReflect α n x β = x β := by
  simp [InfiniteLattice.ReflectionGrid.wallReflect, InfiniteLattice.ReflectionGrid.basisVec,
    Pi.single_eq_of_ne h]
theorem wallReflectEquiv_mem (α : Fin 4) (n : ℤ) :
    G.wallReflectEquiv α n ∈ G.reflectionGroup :=
  Subgroup.subset_closure ⟨(α, n), rfl⟩
theorem exists_mem_of_coordinateMove {α : Fin 4} {δ : ℝ → ℝ} (h : G.IsCoordinateMove α δ) :
    ∃ g ∈ G.reflectionGroup, ∀ (x : AmbientSpace) (β : Fin 4),
      g x β = if β = α then δ (x α) else x β := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨G.wallReflectEquiv α n * G.wallReflectEquiv α 0,
      mul_mem (wallReflectEquiv_mem G α n) (wallReflectEquiv_mem G α 0), fun x β => ?_⟩
    show G.wallReflect α n (G.wallReflect α 0 x) β = _
    split_ifs with hβ
    · subst hβ
      rw [wallReflect_apply_self, wallReflect_apply_self, hn]
      push_cast
      ring
    · rw [wallReflect_apply_of_ne G hβ, wallReflect_apply_of_ne G hβ]
  · refine ⟨G.wallReflectEquiv α n, wallReflectEquiv_mem G α n, fun x β => ?_⟩
    show G.wallReflect α n x β = _
    split_ifs with hβ
    · subst hβ
      rw [wallReflect_apply_self, hn]
    · rw [wallReflect_apply_of_ne G hβ]
theorem exists_element_of_actsCoordinatewise {f : AmbientSpace → AmbientSpace}
    (hf : G.ActsCoordinatewise f) :
    ∃ g : G.reflectionGroup,
      ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) = f := by
  obtain ⟨δ, hδ, hfδ⟩ := hf
  choose e he hx using fun α => exists_mem_of_coordinateMove G (hδ α)
  refine ⟨⟨e 0 * e 1 * e 2 * e 3, mul_mem (mul_mem (mul_mem (he 0) (he 1)) (he 2)) (he 3)⟩, ?_⟩
  funext x
  funext β
  rw [hfδ]
  show e 0 (e 1 (e 2 (e 3 x))) β = _
  fin_cases β <;> simp [hx]
theorem actsCoordinatewise_of_mem {g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace}
    (hg : g ∈ G.reflectionGroup) :
    G.ActsCoordinatewise (g : AmbientSpace → AmbientSpace) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨⟨α, n⟩, rfl⟩ := hg
    refine ⟨fun β => if β = α then fun y => 2 * (G.shift α + (n : ℝ) * G.edge) - y else _root_.id,
      fun β => ?_, fun x β => ?_⟩
    · by_cases hβ : β = α
      · subst hβ
        simp only [if_true]
        exact Or.inr ⟨n, fun y => rfl⟩
      · simp only [if_neg hβ]
        exact IsCoordinateMove.id β
    · show G.wallReflect α n x β = _
      by_cases hβ : β = α
      · subst hβ
        simp only [if_true]
        exact wallReflect_apply_self G β n x
      · simp only [if_neg hβ]
        exact wallReflect_apply_of_ne G hβ n x
  | one => exact ⟨fun _ => _root_.id, fun β => IsCoordinateMove.id β, fun x β => rfl⟩
  | mul g h _ _ hg hh =>
    obtain ⟨δ, hδ, hgδ⟩ := hg
    obtain ⟨δ', hδ', hhδ⟩ := hh
    refine ⟨fun β => δ β ∘ δ' β, fun β => IsCoordinateMove.comp (hδ β) (hδ' β), fun x β => ?_⟩
    show g (h x) β = _
    rw [hgδ, hhδ]
    rfl
  | inv g _ hg =>
    obtain ⟨δ, hδ, hgδ⟩ := hg
    choose δ' hδ' hinv using fun β => IsCoordinateMove.exists_leftInverse (hδ β)
    refine ⟨δ', hδ', fun x β => ?_⟩
    have hx : g (g⁻¹ x) = x := g.apply_symm_apply x
    have h1 := hgδ (g⁻¹ x) β
    rw [hx] at h1
    rw [h1, hinv]
variable {G}
theorem int_le_of_edge_mul_le {a b : ℤ} (h : G.edge * (a : ℝ) ≤ G.edge * (b : ℝ)) : a ≤ b := by
  exact_mod_cast le_of_mul_le_mul_left h G.edge_pos
theorem move_eq_of_endpoints {α : Fin 4} {δ : ℝ → ℝ} (hδ : G.IsCoordinateMove α δ) {k k' : ℤ}
    (h0 : G.shift α + G.edge * (k' : ℝ) ≤ δ (G.shift α + G.edge * (k : ℝ)) ∧
      δ (G.shift α + G.edge * (k : ℝ)) ≤ G.shift α + G.edge * (k' : ℝ) + G.edge)
    (h1 : G.shift α + G.edge * (k' : ℝ) ≤ δ (G.shift α + G.edge * (k : ℝ) + G.edge) ∧
      δ (G.shift α + G.edge * (k : ℝ) + G.edge) ≤ G.shift α + G.edge * (k' : ℝ) + G.edge)
    (y : ℝ) :
    δ y = if Even (k' - k) then y + ((k' - k : ℤ) : ℝ) * G.edge
      else 2 * G.shift α + ((k + k' + 1 : ℤ) : ℝ) * G.edge - y := by
  rcases hδ with ⟨n, hn⟩ | ⟨n, hn⟩
  · simp only [hn] at h0 h1 ⊢
    have ha : k' ≤ k + 2 * n := int_le_of_edge_mul_le (G := G) (by push_cast; linarith [h0.1])
    have hb : k + 2 * n ≤ k' := int_le_of_edge_mul_le (G := G) (by push_cast; linarith [h1.2])
    obtain rfl : k' = k + 2 * n := le_antisymm ha hb
    rw [if_pos ⟨n, by ring⟩]
    push_cast
    ring
  · simp only [hn] at h0 h1 ⊢
    have ha : 2 * n - k ≤ k' + 1 := int_le_of_edge_mul_le (G := G) (by push_cast; linarith [h0.2])
    have hb : k' ≤ 2 * n - k - 1 := int_le_of_edge_mul_le (G := G) (by push_cast; linarith [h1.1])
    obtain rfl : k' = 2 * n - k - 1 := by omega
    rw [if_neg (by intro he; obtain ⟨m, hm⟩ := he; omega)]
    push_cast
    ring
variable (G)
theorem tileReflection_acts (k k' : Fin 4 → ℤ) : G.ActsCoordinatewise (G.tileReflection k k') := by
  refine ⟨fun α y => if Even (k' α - k α) then y + ((k' α - k α : ℤ) : ℝ) * G.edge
    else 2 * G.shift α + ((k α + k' α + 1 : ℤ) : ℝ) * G.edge - y, fun α => ?_, fun x α => rfl⟩
  by_cases h : Even (k' α - k α)
  · have he := h
    obtain ⟨m, hm⟩ := h
    refine Or.inl ⟨m, fun y => ?_⟩
    beta_reduce
    rw [if_pos he, hm]
    push_cast
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, k α + k' α + 1 = 2 * m := by
      rcases Int.even_or_odd (k' α - k α) with he | ⟨t, ht⟩
      · exact absurd he h
      · exact ⟨k α + t + 1, by omega⟩
    refine Or.inr ⟨m, fun y => ?_⟩
    beta_reduce
    rw [if_neg h, hm]
    push_cast
    ring
theorem mem_tile_iff (k : Fin 4 → ℤ) (x : AmbientSpace) :
    x ∈ G.tile k ↔ ∀ α, G.shift α + G.edge * (k α : ℝ) ≤ x α ∧
      x α ≤ G.shift α + G.edge * (k α : ℝ) + G.edge := Iff.rfl
theorem tileReflection_mem_tile (k k' : Fin 4 → ℤ) {x : AmbientSpace} (hx : x ∈ G.tile k) :
    G.tileReflection k k' x ∈ G.tile k' := by
  rw [mem_tile_iff] at hx ⊢
  intro α
  obtain ⟨h0, h1⟩ := hx α
  simp only [tileReflection]
  split_ifs
  · push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith
theorem image_tileReflection (k k' : Fin 4 → ℤ) : G.tileReflection k k' '' G.tile k = G.tile k' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact tileReflection_mem_tile G k k' hx
  · intro hy
    exact ⟨G.tileReflection k' k y, tileReflection_mem_tile G k' k hy, G.tileReflection_tileReflection k' k y⟩
theorem tileSign_cast (k k' : Fin 4 → ℤ) :
    (((tileSign k k' : ℤˣ) : ℤ) : ℝ) = ∏ α, if Even (k' α - k α) then (1 : ℝ) else -1 := by
  have h : ∀ n : ℤ, ((((-1 : ℤˣ) ^ n : ℤˣ) : ℤ) : ℝ) = if Even n then 1 else -1 := by
    intro n
    split_ifs with hn
    · obtain ⟨m, rfl⟩ := hn
      rw [zpow_add, ← mul_zpow]
      simp
    · obtain ⟨m, rfl⟩ := Int.not_even_iff_odd.1 hn
      rw [zpow_add, zpow_mul]
      simp
  simp only [tileSign]
  rw [Fin.sum_univ_four, Fin.prod_univ_four, zpow_add, zpow_add, zpow_add]
  simp only [Units.val_mul, Int.cast_mul]
  rw [h, h, h, h]
theorem orientation_of_tileReflection (k k' : Fin 4 → ℤ) (g : G.reflectionGroup)
    (hg : ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) = G.tileReflection k k') :
    G.orientation g = (((tileSign k k' : ℤˣ) : ℤ) : ℝ) := by
  have hlin : ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear : AmbientSpace →ₗ[ℝ] AmbientSpace) =
      Matrix.toLin' (Matrix.diagonal fun α => if Even (k' α - k α) then (1 : ℝ) else -1) := by
    apply LinearMap.ext
    intro v
    funext α
    have h := (g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).map_vadd (0 : AmbientSpace) v
    rw [hg] at h
    simp only [vadd_eq_add, add_zero] at h
    have h' := congrFun h α
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    simp only [Pi.add_apply, tileReflection, Pi.zero_apply] at h'
    show ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace).linear v) α = _
    split_ifs at h' ⊢ <;> linarith
  rw [InfiniteLattice.ReflectionGrid.orientation, hlin, LinearMap.det_toLin', Matrix.det_diagonal,
    tileSign_cast]
theorem uniqueElementBetweenTiles : G.UniqueElementBetweenTiles := by
  intro k k'
  obtain ⟨g, hg⟩ := exists_element_of_actsCoordinatewise G (tileReflection_acts G k k')
  refine ⟨g, fun h => ⟨fun himg => ?_, fun hh => ?_⟩, hg, orientation_of_tileReflection G k k' g hg⟩
  · obtain ⟨δ, hδ, hx⟩ := actsCoordinatewise_of_mem G h.2
    have hin : ∀ p ∈ G.tile k,
        ((h : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) p ∈ G.tile k' :=
      fun p hp => himg ▸ ⟨p, hp, rfl⟩
    have hl := G.edge_pos
    have hp0 : G.cornerAt k ∈ G.tile k := fun μ => ⟨le_rfl, by linarith⟩
    have hp1 : (fun μ => G.cornerAt k μ + G.edge) ∈ G.tile k := fun μ => ⟨by
      show G.cornerAt k μ ≤ G.cornerAt k μ + G.edge
      linarith, le_rfl⟩
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    show ((h : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) x =
      ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) x
    rw [hg]
    funext α
    rw [hx]
    have e0 := (mem_tile_iff G k' _).1 (hin _ hp0) α
    have e1 := (mem_tile_iff G k' _).1 (hin _ hp1) α
    rw [hx] at e0 e1
    exact move_eq_of_endpoints (hδ α) e0 e1 (x α)
  · rw [hh, hg]
    exact image_tileReflection G k k'
end GridFacts
theorem gridElementaryFacts_holds : GridElementaryFacts := fun _ G _ hp =>
  ⟨GridFacts.edgeOverSpacingOdd G hp,
    GridFacts.wallsBisectLinks G,
    GridFacts.tileCentersAreSites G,
    GridFacts.uniqueElementBetweenTiles G,
    fun g => GridFacts.actsCoordinatewise_of_mem G g.2,
    fun _ hf => GridFacts.exists_element_of_actsCoordinatewise G hf⟩
end MultipleReflections
end
end YangMills.Construction
