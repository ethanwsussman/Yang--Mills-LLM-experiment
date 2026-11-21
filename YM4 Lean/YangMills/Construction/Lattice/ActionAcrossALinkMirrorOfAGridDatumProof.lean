import YangMills.Construction.Lattice.ActionAcrossALinkMirrorOfAGridDatum
import YangMills.Construction.Lattice.FaceBoundaryHolonomy
import YangMills.Construction.Lattice.LayersOfALinkMirrorOfAGridDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorActionSplit
open BoxTorus GridMirror TorusDescent MirrorLayers BoxTorus.FaceBoundary
section Arithmetic
theorem eq_or_eq_add_of_mod_eq {s t n : ℕ} (hs : s < 2 * n) (e : s % n = t) :
    s = t ∨ s = t + n := by
  by_cases hn : s < n
  · left
    rw [Nat.mod_eq_of_lt hn] at e
    exact e
  · right
    have hsub : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
theorem val_add_val_cases {n : ℕ} [NeZero n] {a b : ZMod n} {t : ℕ} (ht : t < n)
    (e : a + b = (t : ZMod n)) : a.val + b.val = t ∨ a.val + b.val = t + n := by
  have e' : ((a.val + b.val : ℕ) : ZMod n) = (t : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    exact e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ht] at e'
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  exact eq_or_eq_add_of_mod_eq (by omega) e'
theorem val_one_sub_mem_Icc_iff {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h)) :
    (1 - j).val ∈ Finset.Icc 1 h ↔ j.val ∉ Finset.Icc 1 h := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have e : (1 - j) + j = ((1 : ℕ) : ZMod (2 * h)) := by simp
  have h₀ := val_add_val_cases (by omega) e
  have h₁ := ZMod.val_lt j
  have h₂ := ZMod.val_lt (1 - j)
  simp only [Finset.mem_Icc]
  omega
theorem eq_half_of_exit {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h))
    (h₁ : j.val ∈ Finset.Icc 1 h) (h₂ : (j + 1).val ∉ Finset.Icc 1 h) :
    j = (h : ZMod (2 * h)) := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have : Fact (1 < 2 * h) := ⟨by omega⟩
  have e : j + 1 = (((j + 1).val : ℕ) : ZMod (2 * h)) := (ZMod.natCast_zmod_val _).symm
  have h₀ := val_add_val_cases (ZMod.val_lt (j + 1)) e
  rw [ZMod.val_one] at h₀
  have h₃ := ZMod.val_lt j
  simp only [Finset.mem_Icc] at h₁ h₂
  have hv : j.val = h := by omega
  have e₃ := ZMod.natCast_zmod_val j
  rw [hv] at e₃
  exact e₃.symm
theorem add_one_eq_one_of_not_mem_of_add_one_mem {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h))
    (h₁ : j.val ∉ Finset.Icc 1 h) (h₂ : (j + 1).val ∈ Finset.Icc 1 h) : j + 1 = 1 := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have : Fact (1 < 2 * h) := ⟨by omega⟩
  have e : j + 1 = (((j + 1).val : ℕ) : ZMod (2 * h)) := (ZMod.natCast_zmod_val _).symm
  have h₀ := val_add_val_cases (ZMod.val_lt (j + 1)) e
  rw [ZMod.val_one] at h₀
  have h₃ := ZMod.val_lt j
  simp only [Finset.mem_Icc] at h₁ h₂
  have hv : (j + 1).val = 1 := by omega
  rw [← ZMod.natCast_zmod_val (j + 1), hv, Nat.cast_one]
theorem false_of_eq_one_sub {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h)) (e : j = 1 - j) :
    False := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have e' : j + j = ((1 : ℕ) : ZMod (2 * h)) := by
    rw [Nat.cast_one]
    nth_rewrite 1 [e]
    ring
  have h₀ := val_add_val_cases (by omega) e'
  omega
theorem eq_one_of_eq_one_sub_add_one {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h))
    (h₁ : j.val ∈ Finset.Icc 1 h) (e : j = 1 - j + 1) : j = 1 := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have e' : j + j = ((2 : ℕ) : ZMod (2 * h)) := by
    rw [Nat.cast_ofNat]
    nth_rewrite 1 [e]
    ring
  have h₀ := val_add_val_cases (by omega) e'
  simp only [Finset.mem_Icc] at h₁
  have hv : j.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val j, hv, Nat.cast_one]
theorem eq_half_of_one_sub_eq_add_one {h : ℕ} (h2 : 2 ≤ h) (j : ZMod (2 * h))
    (h₁ : j.val ∈ Finset.Icc 1 h) (e : 1 - j = j + 1) : j = (h : ZMod (2 * h)) := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have e' : j + j = ((0 : ℕ) : ZMod (2 * h)) := by
    have e₂ : j + j + 1 = 1 := by
      calc j + j + 1 = j + (j + 1) := by ring
        _ = j + (1 - j) := by rw [e]
        _ = 1 := by ring
    rw [Nat.cast_zero]
    exact add_eq_right.mp e₂
  have h₀ := val_add_val_cases (by omega) e'
  simp only [Finset.mem_Icc] at h₁
  have hv : j.val = h := by omega
  have e₃ := ZMod.natCast_zmod_val j
  rw [hv] at e₃
  exact e₃.symm
end Arithmetic
theorem range_vecCons_four {α : Type*} (a b c e : α) :
    Set.range ![a, b, c, e] = {a, b, c, e} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
theorem injective_of_ncard_range_eq_four {α : Type*} {z : Fin 4 → α}
    (h : (Set.range z).ncard = 4) : Function.Injective z := by
  classical
  have hi : ((Finset.univ.image z : Finset α) : Set α) = Set.range z := by simp
  have hc : (Finset.univ.image z).card = (Finset.univ : Finset (Fin 4)).card := by
    rw [← Set.ncard_coe_finset, hi, h]
    simp
  have hj := Finset.card_image_iff.1 hc
  simpa using hj
variable {L : ℕ} {κ : ℤ} {d : CellGrid L κ} {g : d.GridSymmetry} {μ : Fin 4}
  {c : ℝ} {h : ℕ} {layer : d.GridPoint → ZMod (2 * h)}
theorem mem_posHalf_iff (hl : IsMirrorLayering g μ c h layer) (x : d.GridPoint) :
    (x : d.Space) ∈ posHalf d μ c ↔ (layer x).val ∈ Finset.Icc 1 h :=
  hl.2.2.2.2.2.2.1 x
theorem mem_negHalf_iff_not_mem_posHalf (hl : IsMirrorLayering g μ c h layer)
    (x : d.GridPoint) :
    (x : d.Space) ∈ negHalf d μ c ↔ (x : d.Space) ∉ posHalf d μ c := by
  rw [hl.2.2.2.2.2.2.2.1 x, mem_posHalf_iff hl x]
theorem pointImage_mem_posHalf_iff (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    (x : d.GridPoint) :
    ((g.pointImage x : d.GridPoint) : d.Space) ∈ posHalf d μ c ↔
      (x : d.Space) ∉ posHalf d μ c := by
  rw [mem_posHalf_iff hl, mem_posHalf_iff hl, hl.2.2.1 x]
  exact val_one_sub_mem_Icc_iff h2 _
theorem pointImage_mem_negHalf_iff (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    (x : d.GridPoint) :
    ((g.pointImage x : d.GridPoint) : d.Space) ∈ negHalf d μ c ↔
      (x : d.Space) ∈ posHalf d μ c := by
  rw [mem_negHalf_iff_not_mem_posHalf hl, pointImage_mem_posHalf_iff h2 hl, not_not]
theorem add_gridStep_mem_posHalf_iff (hl : IsMirrorLayering g μ c h layer) {ν : Fin 4}
    (hν : ν ≠ μ) (x : d.GridPoint) :
    ((x + gridStep L κ d.sideLengths ν : d.GridPoint) : d.Space) ∈ posHalf d μ c ↔
      (x : d.Space) ∈ posHalf d μ c := by
  rw [mem_posHalf_iff hl, mem_posHalf_iff hl, hl.2.1 x ν hν]
theorem eq_add_gridStep_of_isNeighbourStep {x x' : d.GridPoint} {ν : Fin 4}
    (hs : IsNeighbourStep x x' ν 1) : x' = x + gridStep L κ d.sideLengths ν := by
  apply Subtype.ext
  rw [hs.2]
  simp [BoxTorus.translate, gridStep]
theorem isNeighbourStep_add_gridStep (x : d.GridPoint) (ν : Fin 4) :
    IsNeighbourStep x (x + gridStep L κ d.sideLengths ν) ν 1 :=
  ⟨Or.inl rfl, by simp [BoxTorus.translate, gridStep]⟩
theorem edgeFrom_isForward (x : d.GridPoint) (ν : Fin 4) :
    (edgeFrom x ν : d.DirectedEdge).IsForward :=
  ⟨ν, isNeighbourStep_add_gridStep x ν⟩
theorem exists_face_vertexSet (x : d.GridPoint) {ν ν' : Fin 4} (hne : ν' ≠ ν) :
    ∃ p : d.Face, p.vertexSet = {x, x + gridStep L κ d.sideLengths ν,
      x + gridStep L κ d.sideLengths ν + gridStep L κ d.sideLengths ν',
      x + gridStep L κ d.sideLengths ν'} := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨⟨x, ν', ν, hlt⟩, ?_⟩
    ext z
    simp only [Face.vertexSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [add_right_comm x (gridStep L κ d.sideLengths ν') (gridStep L κ d.sideLengths ν)]
    tauto
  · exact ⟨⟨x, ν, ν', hlt⟩, rfl⟩
theorem face_axis_cases (p : d.Face) (μ : Fin 4) :
    (∃ l, l ≠ μ ∧ p.vertexSet = {p.corner, p.corner + gridStep L κ d.sideLengths μ,
      p.corner + gridStep L κ d.sideLengths μ + gridStep L κ d.sideLengths l,
      p.corner + gridStep L κ d.sideLengths l}) ∨
      (p.dir₁ ≠ μ ∧ p.dir₂ ≠ μ) := by
  by_cases h₁ : p.dir₁ = μ
  · left
    refine ⟨p.dir₂, ?_, ?_⟩
    · intro e
      have hlt := p.dir₁_lt_dir₂
      rw [h₁, e] at hlt
      exact lt_irrefl _ hlt
    · rw [← h₁]
      rfl
  · by_cases h₂ : p.dir₂ = μ
    · left
      refine ⟨p.dir₁, h₁, ?_⟩
      rw [← h₂]
      ext z
      simp only [Face.vertexSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [add_right_comm p.corner (gridStep L κ d.sideLengths p.dir₁)
        (gridStep L κ d.sideLengths p.dir₂)]
      tauto
    · exact Or.inr ⟨h₁, h₂⟩
theorem exists_face_image (hl : IsMirrorLayering g μ c h layer) (p : d.Face) :
    ∃ p' : d.Face, p'.vertexSet = g.pointImage '' p.vertexSet := by
  rcases face_axis_cases p μ with ⟨l, hlm, hc⟩ | ⟨h₁, h₂⟩
  · obtain ⟨p', hp'⟩ :=
      exists_face_vertexSet (g.pointImage p.corner - gridStep L κ d.sideLengths μ) hlm
    refine ⟨p', ?_⟩
    rw [hp', hc]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [hl.2.2.2.1 _ l hlm, hl.2.2.2.2.1 p.corner, hl.2.2.2.1 _ l hlm, sub_add_cancel]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · refine ⟨⟨g.pointImage p.corner, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩, ?_⟩
    simp only [Face.vertexSet, Set.image_insert_eq, Set.image_singleton]
    rw [hl.2.2.2.1 _ _ h₂, hl.2.2.2.1 _ _ h₂, hl.2.2.2.1 _ _ h₁]
theorem range_cornerCycle (p : d.Face) : Set.range (cornerCycle p) = p.vertexSet :=
  range_vecCons_four _ _ _ _
theorem faceEnergy_pullback_of_image (hHol : FaceBoundaryProperty)
    (hLat : GridLattice.Properties) (hl : IsMirrorLayering g μ c h layer) {p p' : d.Face}
    (hc : p'.vertexSet = g.pointImage '' p.vertexSet) (U : d.GaugeConfig) :
    faceEnergy (g.pullback U) p = faceEnergy U p' := by
  obtain ⟨-, hLP, hCfg, hDist, -⟩ := hLat L κ d
  obtain ⟨hlinks, -, -⟩ := hHol L κ d p
  have hany := (hHol L κ d p').2.1
  choose b hb using hlinks.1
  have hv := hlinks.2.2 b (fun i => hb i) (g.pullback U)
  have hinv : Function.Injective g.pointImage :=
    Function.LeftInverse.injective (g := g.pointImage) hl.2.2.2.2.2.1
  have hinj : Function.Injective (cornerCycle p) :=
    injective_of_ncard_range_eq_four (by rw [range_cornerCycle]; exact hLP.2.2.1 p)
  have hr : Set.range (g.pointImage ∘ cornerCycle p) = p'.vertexSet := by
    rw [Set.range_comp, range_cornerCycle, hc]
  have hj : EdgesJoinCycle (g.pointImage ∘ cornerCycle p) (fun i => g.edgeImage (b i)) := by
    intro i
    have e := g.edgeImage_endpoints hDist (b i)
    refine ⟨e.1.trans ?_, e.2.trans ?_⟩
    · rw [(hb i).1]
      rfl
    · rw [(hb i).2]
      rfl
  rw [hany _ _ (hinv.comp hinj) hr hj U, faceEnergy, hv]
  simp only [cycleProduct, g.edgeVariable_pullback hCfg]
theorem halfAction_pullback_eq (hHol : FaceBoundaryProperty)
    (hLat : GridLattice.Properties) (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    (U : d.GaugeConfig) :
    halfAction d (posHalf d μ c) (g.pullback U) =
      ∑ᶠ p ∈ halfFaces d (negHalf d μ c), faceEnergy U p := by
  obtain ⟨-, hLP, -, -, -⟩ := hLat L κ d
  choose θ hθ using fun p : d.Face => exists_face_image hl (g := g) p
  have hinv : ∀ p, θ (θ p) = p := fun p => hLP.2.2.2.2 _ _ (by
    rw [hθ, hθ, Set.image_image]
    simp [hl.2.2.2.2.2.1])
  have hm₁ : Set.MapsTo θ (halfFaces d (posHalf d μ c)) (halfFaces d (negHalf d μ c)) := by
    intro p hp z hz
    rw [hθ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (pointImage_mem_negHalf_iff h2 hl x).2 (hp x hx)
  have hm₂ : Set.MapsTo θ (halfFaces d (negHalf d μ c)) (halfFaces d (posHalf d μ c)) := by
    intro p hp z hz
    rw [hθ] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (pointImage_mem_posHalf_iff h2 hl x).2
      ((mem_negHalf_iff_not_mem_posHalf hl x).1 (hp x hx))
  have hbij : Set.BijOn θ (halfFaces d (posHalf d μ c)) (halfFaces d (negHalf d μ c)) :=
    Set.InvOn.bijOn ⟨fun p _ => hinv p, fun p _ => hinv p⟩ hm₁ hm₂
  rw [halfAction, finsum_set_coe_eq_finsum_mem (f := fun p => faceEnergy (g.pullback U) p) _]
  exact finsum_mem_eq_of_bijOn θ hbij fun p _ =>
    faceEnergy_pullback_of_image hHol hLat hl (hθ p) U
theorem layer_of_mem_mirrorPairedPoints (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    {y : d.GridPoint} (hy : y ∈ mirrorPairedPoints g (posHalf d μ c)) :
    layer y = 1 ∨ layer y = (h : ZMod (2 * h)) := by
  obtain ⟨hup, b, h₁, h₂⟩ := hy
  obtain ⟨ν, σ, hs⟩ := b.isNeighbour
  rw [h₁, h₂] at hs
  have hj := (mem_posHalf_iff hl y).1 hup
  have hg := hl.2.2.1 y
  rcases hs.1 with e | e
  · rw [e] at hs
    have hy' := eq_add_gridStep_of_isNeighbourStep hs
    by_cases hν : ν = μ
    · rw [hν] at hy'
      have e₁ := hl.1 (g.pointImage y)
      rw [← hy', hg] at e₁
      exact Or.inl (eq_one_of_eq_one_sub_add_one h2 _ hj e₁)
    · have e₁ := hl.2.1 (g.pointImage y) ν hν
      rw [← hy', hg] at e₁
      exact (false_of_eq_one_sub h2 _ e₁).elim
  · have hs' := hs.symm
    rw [e, neg_neg] at hs'
    have hy' := eq_add_gridStep_of_isNeighbourStep hs'
    by_cases hν : ν = μ
    · rw [hν] at hy'
      have e₁ := hl.1 y
      rw [← hy', hg] at e₁
      exact Or.inr (eq_half_of_one_sub_eq_add_one h2 _ hj e₁)
    · have e₁ := hl.2.1 y ν hν
      rw [← hy', hg] at e₁
      exact (false_of_eq_one_sub h2 _ e₁.symm).elim
theorem mem_mirrorPairedPoints (hl : IsMirrorLayering g μ c h layer) {y : d.GridPoint}
    (hy : (y : d.Space) ∈ posHalf d μ c)
    (hj : layer y = 1 ∨ layer y = (h : ZMod (2 * h))) :
    y ∈ mirrorPairedPoints g (posHalf d μ c) := by
  refine ⟨hy, ?_⟩
  rcases hj with hj | hj
  · refine ⟨edgeFrom (g.pointImage y) μ, rfl, ?_⟩
    show g.pointImage y + gridStep L κ d.sideLengths μ = y
    rw [hl.2.2.2.2.2.2.2.2.1 y hj, sub_add_cancel]
  · refine ⟨(edgeFrom y μ).flip, ?_, rfl⟩
    show y + gridStep L κ d.sideLengths μ = g.pointImage y
    rw [hl.2.2.2.2.2.2.2.2.2.1 y hj]
theorem exists_transverse_face (hl : IsMirrorLayering g μ c h layer) (y : d.GridPoint)
    {ν : Fin 4} (hν : ν ≠ μ) (hj : layer y = 1 ∨ layer y = (h : ZMod (2 * h))) :
    ∃ p : d.Face, p.vertexSet =
      {y, y + gridStep L κ d.sideLengths ν, g.pointImage (y + gridStep L κ d.sideLengths ν),
        g.pointImage y} := by
  have hlay : layer (y + gridStep L κ d.sideLengths ν) = layer y := hl.2.1 y ν hν
  rcases hj with hj | hj
  · obtain ⟨p, hp⟩ := exists_face_vertexSet (y - gridStep L κ d.sideLengths μ) hν
    refine ⟨p, ?_⟩
    rw [hp, hl.2.2.2.2.2.2.2.2.1 y hj, hl.2.2.2.2.2.2.2.2.1 _ (hlay.trans hj), sub_add_cancel,
      sub_add_eq_add_sub]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · obtain ⟨p, hp⟩ := exists_face_vertexSet y hν
    refine ⟨p, ?_⟩
    rw [hp, hl.2.2.2.2.2.2.2.2.2.1 y hj, hl.2.2.2.2.2.2.2.2.2.1 _ (hlay.trans hj),
      add_right_comm y (gridStep L κ d.sideLengths μ) (gridStep L κ d.sideLengths ν)]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
theorem transverseEdge_target_eq (b : TransverseEdge g (posHalf d μ c) μ) :
    ∃ ν, ν ≠ μ ∧ b.1.1.1.target = b.1.1.1.source + gridStep L κ d.sideLengths ν := by
  obtain ⟨ν, hν⟩ := b.1.1.2
  refine ⟨ν, ?_, eq_add_gridStep_of_isNeighbourStep hν⟩
  intro e
  rw [e] at hν
  exact b.2.2.2 ⟨1, hν⟩
theorem exists_face_of_transverseEdge (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    (b : TransverseEdge g (posHalf d μ c) μ) :
    ∃ p : d.Face, p.vertexSet = {b.1.1.1.source, b.1.1.1.target,
      g.pointImage b.1.1.1.target, g.pointImage b.1.1.1.source} := by
  obtain ⟨ν, hν, e⟩ := transverseEdge_target_eq b
  have hc := exists_transverse_face hl b.1.1.1.source hν
    (layer_of_mem_mirrorPairedPoints h2 hl b.2.1)
  rw [← e] at hc
  exact hc
theorem faceEnergy_eq_mirrorFaceEnergy (hHol : FaceBoundaryProperty)
    (hLat : GridLattice.Properties) (b : TransverseEdge g (posHalf d μ c) μ) {p : d.Face}
    (hp : p.vertexSet = {b.1.1.1.source, b.1.1.1.target, g.pointImage b.1.1.1.target,
      g.pointImage b.1.1.1.source}) (U : d.GaugeConfig) :
    faceEnergy U p = mirrorFaceEnergy U b := by
  obtain ⟨-, hLP, hCfg, hDist, -⟩ := hLat L κ d
  have hany := (hHol L κ d p).2.1
  have hr : Set.range ![b.1.1.1.source, b.1.1.1.target, g.pointImage b.1.1.1.target,
      g.pointImage b.1.1.1.source] = p.vertexSet := by
    rw [hp]
    exact range_vecCons_four _ _ _ _
  have hinj := injective_of_ncard_range_eq_four (by rw [hr]; exact hLP.2.2.1 p)
  have hE := g.edgeImage_endpoints hDist b.1.1.1
  have hj : EdgesJoinCycle ![b.1.1.1.source, b.1.1.1.target, g.pointImage b.1.1.1.target,
      g.pointImage b.1.1.1.source] ![b.1.1.1, (mirrorEdge b.finish).flip,
      (g.edgeImage b.1.1.1).flip, mirrorEdge b.start] := by
    intro i
    fin_cases i
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨hE.2, hE.1⟩
    · exact ⟨rfl, rfl⟩
  rw [hany _ _ hinj hr hj U]
  have e : cycleProduct U ![b.1.1.1, (mirrorEdge b.finish).flip,
      (g.edgeImage b.1.1.1).flip, mirrorEdge b.start] = mirrorHolonomy U b := by
    show edgeVariable U b.1.1.1 * edgeVariable U (mirrorEdge b.finish).flip *
      edgeVariable U (g.edgeImage b.1.1.1).flip * edgeVariable U (mirrorEdge b.start) = _
    rw [hCfg.1 U, hCfg.1 U]
    rfl
  rw [e]
  rfl
theorem exists_transverseEdge (hLat : GridLattice.Properties)
    (hl : IsMirrorLayering g μ c h layer) {y : d.GridPoint} {l : Fin 4} (hlm : l ≠ μ)
    (hy : (y : d.Space) ∈ posHalf d μ c)
    (hj : layer y = 1 ∨ layer y = (h : ZMod (2 * h))) :
    ∃ b : TransverseEdge g (posHalf d μ c) μ, b.1.1.1.source = y ∧
      b.1.1.1.target = y + gridStep L κ d.sideLengths l := by
  obtain ⟨-, hLP, -, -, -⟩ := hLat L κ d
  have hy' := (add_gridStep_mem_posHalf_iff hl hlm y).2 hy
  have hj' : layer (y + gridStep L κ d.sideLengths l) = 1 ∨
      layer (y + gridStep L κ d.sideLengths l) = (h : ZMod (2 * h)) := by
    rw [hl.2.1 y l hlm]
    exact hj
  have fwd := edgeFrom_isForward y l
  have inside : (edgeFrom y l : d.DirectedEdge).LiesIn (posHalf d μ c) :=
    (hl.2.2.2.2.2.2.2.2.2.2.1 _).2 ⟨hy, hy'⟩
  have notAxis : ¬ (edgeFrom y l : d.DirectedEdge).HasAxis μ := by
    intro hd
    have hu := (hLP.2.1 (edgeFrom y l)).1
    exact hlm (hu.unique ⟨1, isNeighbourStep_add_gridStep y l⟩ hd)
  exact ⟨⟨⟨⟨edgeFrom y l, fwd⟩, inside⟩, mem_mirrorPairedPoints hl hy hj,
    mem_mirrorPairedPoints hl hy' hj', notAxis⟩, rfl, rfl⟩
theorem ends_subset_of_vertexSet_eq (h2 : 2 ≤ h) (hl : IsMirrorLayering g μ c h layer)
    (b b' : TransverseEdge g (posHalf d μ c) μ)
    (hc : ({b.1.1.1.source, b.1.1.1.target, g.pointImage b.1.1.1.target,
        g.pointImage b.1.1.1.source} : Set d.GridPoint) =
      {b'.1.1.1.source, b'.1.1.1.target, g.pointImage b'.1.1.1.target,
        g.pointImage b'.1.1.1.source}) :
    b.1.1.1.ends ⊆ b'.1.1.1.ends := by
  have key : ∀ x : d.GridPoint, (x : d.Space) ∈ posHalf d μ c →
      x ∈ ({b'.1.1.1.source, b'.1.1.1.target, g.pointImage b'.1.1.1.target,
        g.pointImage b'.1.1.1.source} : Set d.GridPoint) → x ∈ b'.1.1.1.ends := by
    rintro x hx (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ((pointImage_mem_posHalf_iff h2 hl _).1 hx b'.2.2.1.1).elim
    · exact ((pointImage_mem_posHalf_iff h2 hl _).1 hx b'.2.1.1).elim
  rintro x (rfl | rfl)
  · exact key _ b.2.1.1 (hc ▸ Or.inl rfl)
  · exact key _ b.2.2.1.1 (hc ▸ Or.inr (Or.inl rfl))
theorem bijOn_transverse_faces (hLat : GridLattice.Properties) (h2 : 2 ≤ h)
    (hl : IsMirrorLayering g μ c h layer) (pb : TransverseEdge g (posHalf d μ c) μ → d.Face)
    (hpb : ∀ b, (pb b).vertexSet = {b.1.1.1.source, b.1.1.1.target,
      g.pointImage b.1.1.1.target, g.pointImage b.1.1.1.source}) :
    Set.BijOn pb Set.univ
      (halfFaces d (posHalf d μ c) ∪ halfFaces d (negHalf d μ c))ᶜ := by
  obtain ⟨-, hLP, -, -, -⟩ := hLat L κ d
  refine ⟨?_, ?_, ?_⟩
  · intro b _
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have h₁ := hp (g.pointImage b.1.1.1.source) (by rw [hpb]; simp)
      exact (pointImage_mem_posHalf_iff h2 hl _).1 h₁ b.2.1.1
    · have h₁ := hp b.1.1.1.source (by rw [hpb]; simp)
      exact (mem_negHalf_iff_not_mem_posHalf hl _).1 h₁ b.2.1.1
  · intro b _ b' _ e
    have hc := hpb b
    rw [e, hpb b'] at hc
    have hends : b.1.1.1.ends = b'.1.1.1.ends :=
      Set.Subset.antisymm (ends_subset_of_vertexSet_eq h2 hl b b' hc.symm)
        (ends_subset_of_vertexSet_eq h2 hl b' b hc)
    exact Subtype.ext (Subtype.ext (Subtype.ext (hLP.2.2.2.1 _ _ b.1.1.2 b'.1.1.2 hends)))
  · intro p hp
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hp
    obtain ⟨hnu, hnl⟩ := hp
    have allNeg : ∀ x : d.GridPoint, (x : d.Space) ∉ posHalf d μ c →
        (x : d.Space) ∈ negHalf d μ c := fun x hx =>
      (mem_negHalf_iff_not_mem_posHalf hl x).2 hx
    rcases face_axis_cases p μ with ⟨l, hlm, hc⟩ | ⟨h₁, h₂⟩
    · have a₁ := add_gridStep_mem_posHalf_iff hl hlm p.corner
      have a₂ := add_gridStep_mem_posHalf_iff hl hlm (p.corner + gridStep L κ d.sideLengths μ)
      by_cases hx : (p.corner : d.Space) ∈ posHalf d μ c <;>
        by_cases hxm : ((p.corner + gridStep L κ d.sideLengths μ : d.GridPoint) : d.Space) ∈
          posHalf d μ c
      · refine (hnu fun z hz => ?_).elim
        rw [hc] at hz
        rcases hz with rfl | rfl | rfl | rfl
        exacts [hx, hxm, a₂.2 hxm, a₁.2 hx]
      · have hjh : layer p.corner = (h : ZMod (2 * h)) := by
          refine eq_half_of_exit h2 _ ((mem_posHalf_iff hl _).1 hx) ?_
          rw [← hl.1 p.corner]
          exact fun hm => hxm ((mem_posHalf_iff hl _).2 hm)
        obtain ⟨b, hb₁, hb₂⟩ := exists_transverseEdge hLat hl hlm hx (Or.inr hjh)
        refine ⟨b, Set.mem_univ _, hLP.2.2.2.2 _ _ ?_⟩
        have hlay : layer (p.corner + gridStep L κ d.sideLengths l) = (h : ZMod (2 * h)) :=
          (hl.2.1 p.corner l hlm).trans hjh
        rw [hpb, hc, hb₁, hb₂, hl.2.2.2.2.2.2.2.2.2.1 _ hjh,
          hl.2.2.2.2.2.2.2.2.2.1 _ hlay,
          add_right_comm p.corner (gridStep L κ d.sideLengths l) (gridStep L κ d.sideLengths μ)]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      · have hj1 : layer (p.corner + gridStep L κ d.sideLengths μ) = 1 := by
          rw [hl.1 p.corner]
          refine add_one_eq_one_of_not_mem_of_add_one_mem h2 _ (fun hm => hx ((mem_posHalf_iff hl _).2 hm)) ?_
          rw [← hl.1 p.corner]
          exact (mem_posHalf_iff hl _).1 hxm
        obtain ⟨b, hb₁, hb₂⟩ := exists_transverseEdge hLat hl hlm hxm (Or.inl hj1)
        refine ⟨b, Set.mem_univ _, hLP.2.2.2.2 _ _ ?_⟩
        have hlay : layer (p.corner + gridStep L κ d.sideLengths μ +
            gridStep L κ d.sideLengths l) = 1 :=
          (hl.2.1 _ l hlm).trans hj1
        rw [hpb, hc, hb₁, hb₂, hl.2.2.2.2.2.2.2.2.1 _ hj1, hl.2.2.2.2.2.2.2.2.1 _ hlay,
          add_sub_cancel_right,
          add_right_comm p.corner (gridStep L κ d.sideLengths μ) (gridStep L κ d.sideLengths l),
          add_sub_cancel_right]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rw [add_right_comm p.corner (gridStep L κ d.sideLengths l) (gridStep L κ d.sideLengths μ)]
        tauto
      · refine (hnl fun z hz => ?_).elim
        rw [hc] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact allNeg _ hx
        · exact allNeg _ hxm
        · exact allNeg _ fun hm => hxm (a₂.1 hm)
        · exact allNeg _ fun hm => hx (a₁.1 hm)
    · have a₁ := add_gridStep_mem_posHalf_iff hl h₁ p.corner
      have a₂ := add_gridStep_mem_posHalf_iff hl h₂ p.corner
      have a₃ := add_gridStep_mem_posHalf_iff hl h₂ (p.corner + gridStep L κ d.sideLengths p.dir₁)
      by_cases hx : (p.corner : d.Space) ∈ posHalf d μ c
      · refine (hnu fun z hz => ?_).elim
        rcases hz with rfl | rfl | rfl | rfl
        exacts [hx, a₁.2 hx, a₃.2 (a₁.2 hx), a₂.2 hx]
      · refine (hnl fun z hz => ?_).elim
        rcases hz with rfl | rfl | rfl | rfl
        · exact allNeg _ hx
        · exact allNeg _ fun hm => hx (a₁.1 hm)
        · exact allNeg _ fun hm => hx (a₁.1 (a₃.1 hm))
        · exact allNeg _ fun hm => hx (a₂.1 hm)
theorem edgeVariable_edgeFrom_eq (hl : IsMirrorLayering g μ c h layer)
    {U U' : d.GaugeConfig} (hU : ∀ b : HalfEdge d (posHalf d μ c), U b.1 = U' b.1)
    {x : d.GridPoint} {ν : Fin 4} (hx : (x : d.Space) ∈ posHalf d μ c)
    (hx' : ((x + gridStep L κ d.sideLengths ν : d.GridPoint) : d.Space) ∈ posHalf d μ c) :
    edgeVariable U (edgeFrom x ν) = edgeVariable U' (edgeFrom x ν) := by
  have fwd := edgeFrom_isForward x ν
  have inside : (edgeFrom x ν : d.DirectedEdge).LiesIn (posHalf d μ c) :=
    (hl.2.2.2.2.2.2.2.2.2.2.1 _).2 ⟨hx, hx'⟩
  rw [edgeVariable, dif_pos fwd, edgeVariable, dif_pos fwd]
  exact hU ⟨⟨_, fwd⟩, inside⟩
theorem faceEnergy_congr (hl : IsMirrorLayering g μ c h layer) {U U' : d.GaugeConfig}
    (hU : ∀ b : HalfEdge d (posHalf d μ c), U b.1 = U' b.1) {p : d.Face}
    (hp : p ∈ halfFaces d (posHalf d μ c)) :
    faceEnergy U p = faceEnergy U' p := by
  have c₀ : (p.corner : d.Space) ∈ posHalf d μ c := hp _ (Or.inl rfl)
  have c₁ : ((p.corner + gridStep L κ d.sideLengths p.dir₁ : d.GridPoint) : d.Space) ∈
      posHalf d μ c :=
    hp _ (Or.inr (Or.inl rfl))
  have c₂ : ((p.corner + gridStep L κ d.sideLengths p.dir₁ +
      gridStep L κ d.sideLengths p.dir₂ : d.GridPoint) : d.Space) ∈ posHalf d μ c :=
    hp _ (Or.inr (Or.inr (Or.inl rfl)))
  have c₃ : ((p.corner + gridStep L κ d.sideLengths p.dir₂ : d.GridPoint) : d.Space) ∈
      posHalf d μ c :=
    hp _ (Or.inr (Or.inr (Or.inr rfl)))
  have c₂' : ((p.corner + gridStep L κ d.sideLengths p.dir₂ +
      gridStep L κ d.sideLengths p.dir₁ : d.GridPoint) : d.Space) ∈ posHalf d μ c := by
    rw [add_right_comm]
    exact c₂
  rw [faceEnergy, faceEnergy, faceHolonomy, faceHolonomy,
    edgeVariable_edgeFrom_eq hl hU c₀ c₁, edgeVariable_edgeFrom_eq hl hU c₁ c₂,
    edgeVariable_edgeFrom_eq hl hU c₃ c₂', edgeVariable_edgeFrom_eq hl hU c₀ c₃]
theorem actionSplitsAcrossMirror (hLayers : LayeringTheorem)
    (hHol : FaceBoundaryProperty) (hLat : GridLattice.Properties) :
    ActionSplitsAcrossMirror := by
  intro L κ d g μ c hg
  obtain ⟨h, h2, layer, hl⟩ := hLayers L κ d g μ c hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : Fintype ↥(halfFaces d (posHalf d μ c)) := Fintype.ofFinite _
    have e : halfAction d (posHalf d μ c) =
        fun U => ∑ p : ↥(halfFaces d (posHalf d μ c)), faceEnergy U p.1 := by
      funext U
      exact finsum_eq_sum_of_fintype _
    rw [e]
    exact continuous_finsetSum _ fun p _ => (hHol L κ d p.1).2.2.1
  · intro U
    exact finsum_nonneg fun p => ((hHol L κ d p.1).2.2.2.1 U).1
  · intro U U' hU
    exact finsum_congr fun p => faceEnergy_congr hl hU p.2
  · intro U
    obtain ⟨-, hLP, -, -, -⟩ := hLat L κ d
    choose pb hpb using exists_face_of_transverseEdge (g := g) (c := c) h2 hl
    have e₁ : halfAction d (posHalf d μ c) U =
        ∑ᶠ p ∈ halfFaces d (posHalf d μ c), faceEnergy U p :=
      finsum_set_coe_eq_finsum_mem (f := fun p => faceEnergy U p) _
    have e₃ : ∑ᶠ b : TransverseEdge g (posHalf d μ c) μ, mirrorFaceEnergy U b =
        ∑ᶠ p ∈ (halfFaces d (posHalf d μ c) ∪
          halfFaces d (negHalf d μ c))ᶜ, faceEnergy U p := by
      rw [← finsum_mem_univ (fun b => mirrorFaceEnergy U b)]
      exact finsum_mem_eq_of_bijOn pb (bijOn_transverse_faces hLat h2 hl pb hpb) fun b _ =>
        (faceEnergy_eq_mirrorFaceEnergy hHol hLat b (hpb b) U).symm
    have hdisj : Disjoint (halfFaces d (posHalf d μ c)) (halfFaces d (negHalf d μ c)) :=
      Set.disjoint_left.2 fun p h₁ h₂ =>
        (mem_negHalf_iff_not_mem_posHalf hl p.corner).1 (h₂ _ (Or.inl rfl)) (h₁ _ (Or.inl rfl))
    rw [e₁, halfAction_pullback_eq hHol hLat h2 hl U, e₃,
      ← finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _),
      ← finsum_mem_union disjoint_compl_right (Set.toFinite _) (Set.toFinite _),
      Set.union_compl_self, finsum_mem_univ]
    rfl
end YangMills.Construction.MirrorActionSplit
end
