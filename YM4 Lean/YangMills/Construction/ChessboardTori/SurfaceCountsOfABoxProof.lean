import YangMills.Construction.ChessboardTori.SurfaceCountsOfABox
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.ChessboardTori.BoxBoundaryCount
theorem ncard_le_card_of_surj {X Y : Type*} {S : Set X} (T : Finset Y) (Φ : Y → X)
    (h : ∀ x ∈ S, ∃ y ∈ T, Φ y = x) : S.ncard ≤ T.card := by
  have hs : S ⊆ Φ '' (T : Set Y) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := h x hx
    exact ⟨y, hy, rfl⟩
  calc S.ncard ≤ (Φ '' (T : Set Y)).ncard := Set.ncard_le_ncard hs (T.finite_toSet.image Φ)
    _ ≤ (T : Set Y).ncard := Set.ncard_image_le T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
abbrev AxisPair : Type := {d : Fin 4 × Fin 4 // d.1 < d.2}
theorem card_axisPair : Fintype.card AxisPair = 6 := by decide
def slabIndices (E I : Finset ℤ) (κ : Fin 4) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun μ => if μ = κ then E else I
theorem mem_slabIndices {E I : Finset ℤ} {κ : Fin 4} {i : Fin 4 → ℤ}
    (h₁ : i κ ∈ E) (h₂ : ∀ μ, μ ≠ κ → i μ ∈ I) : i ∈ slabIndices E I κ := by
  refine Fintype.mem_piFinset.mpr fun μ => ?_
  by_cases h : μ = κ
  · subst h
    simpa using h₁
  · simpa [h] using h₂ μ h
theorem card_slabIndices (E I : Finset ℤ) (κ : Fin 4) :
    (slabIndices E I κ).card = E.card * I.card ^ 3 := by
  simp only [slabIndices, Fintype.card_piFinset, apply_ite Finset.card]
  fin_cases κ <;> simp [Fin.prod_univ_four] <;> ring
def pairSlabIndices (E I : Finset ℤ) : Finset (Σ _ : AxisPair, Fin 4 → ℤ) :=
  Finset.univ.sigma fun d => slabIndices E I d.1.1 ∪ slabIndices E I d.1.2
theorem card_pairSlabIndices_le (E I : Finset ℤ) :
    (pairSlabIndices E I).card ≤ 12 * (E.card * I.card ^ 3) := by
  have h : ∀ d : AxisPair, (slabIndices E I d.1.1 ∪ slabIndices E I d.1.2).card ≤
      2 * (E.card * I.card ^ 3) := fun d => by
    refine (Finset.card_union_le _ _).trans ?_
    rw [card_slabIndices, card_slabIndices]
    omega
  rw [pairSlabIndices, Finset.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ _ fun d _ => h d).trans ?_
  simp only [Finset.card_univ, card_axisPair, smul_eq_mul]
  omega
def InCube (q : ℤ) (i : Fin 4 → ℤ) : Prop := ∀ μ, 1 ≤ i μ ∧ i μ ≤ q
def bump (i : Fin 4 → ℤ) (κ ν : Fin 4) (s t : ℤ) : Fin 4 → ℤ :=
  fun μ => i μ + (if μ = κ then s else 0) + (if μ = ν then t else 0)
theorem inCube_bump_iff {q : ℤ} {i : Fin 4 → ℤ} {κ ν : Fin 4} (h : κ ≠ ν) (s t : ℤ) :
    InCube q (bump i κ ν s t) ↔ (∀ μ, μ ≠ κ → μ ≠ ν → 1 ≤ i μ ∧ i μ ≤ q) ∧
      (1 ≤ i κ + s ∧ i κ + s ≤ q) ∧ (1 ≤ i ν + t ∧ i ν + t ≤ q) := by
  constructor
  · intro hw
    refine ⟨fun μ h₁ h₂ => ?_, ?_, ?_⟩
    · simpa [bump, h₁, h₂] using hw μ
    · simpa [bump, h] using hw κ
    · simpa [bump, h.symm] using hw ν
  · rintro ⟨hF, h₁, h₂⟩ μ
    by_cases e₁ : μ = κ
    · subst e₁
      simpa [bump, h] using h₁
    · by_cases e₂ : μ = ν
      · subst e₂
        simpa [bump, e₁] using h₂
      · simpa [bump, e₁, e₂] using hF μ e₁ e₂
theorem mem_slabs_of_crossing {q : ℤ} {i : Fin 4 → ℤ} {κ ν : Fin 4} (h : κ ≠ ν)
    (hin : (InCube q (bump i κ ν 0 0) ∧ InCube q (bump i κ ν 1 0)) ∨
      (InCube q (bump i κ ν 1 0) ∧ InCube q (bump i κ ν 1 1)) ∨
      (InCube q (bump i κ ν 0 1) ∧ InCube q (bump i κ ν 1 1)) ∨
      (InCube q (bump i κ ν 0 0) ∧ InCube q (bump i κ ν 0 1)))
    (hout : ¬ (InCube q (bump i κ ν 0 0) ∧ InCube q (bump i κ ν 1 0) ∧
      InCube q (bump i κ ν 0 1) ∧ InCube q (bump i κ ν 1 1))) :
    i ∈ slabIndices {0, q} (Finset.Icc 1 q) κ ∪ slabIndices {0, q} (Finset.Icc 1 q) ν := by
  simp only [inCube_bump_iff h] at hin hout
  have hF : ∀ μ, μ ≠ κ → μ ≠ ν → 1 ≤ i μ ∧ i μ ≤ q := by
    rcases hin with ⟨⟨hF, -⟩, -⟩ | ⟨⟨hF, -⟩, -⟩ | ⟨⟨hF, -⟩, -⟩ | ⟨⟨hF, -⟩, -⟩ <;> exact hF
  have hc : ((i κ = 0 ∨ i κ = q) ∧ 1 ≤ i ν ∧ i ν ≤ q) ∨
      ((i ν = 0 ∨ i ν = q) ∧ 1 ≤ i κ ∧ i κ ≤ q) := by
    have hout' : ¬ ((1 ≤ i κ ∧ i κ + 1 ≤ q) ∧ 1 ≤ i ν ∧ i ν + 1 ≤ q) := fun hh =>
      hout ⟨⟨hF, by omega⟩, ⟨hF, by omega⟩, ⟨hF, by omega⟩, ⟨hF, by omega⟩⟩
    rcases hin with ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ | ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ | ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ |
      ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩ <;> omega
  rw [Finset.mem_union]
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine Or.inl (mem_slabIndices (by simpa using h₁) fun μ hμ => ?_)
    by_cases e : μ = ν
    · subst e
      simpa using h₂
    · simpa using hF μ hμ e
  · refine Or.inr (mem_slabIndices (by simpa using h₁) fun μ hμ => ?_)
    by_cases e : μ = κ
    · subst e
      simpa using h₂
    · simpa using hF μ e hμ
theorem mem_topSlabs {q : ℤ} {i : Fin 4 → ℤ} {κ ν : Fin 4} (h : κ ≠ ν) (hw : InCube q i)
    (hout : ¬ (InCube q (bump i κ ν 0 0) ∧ InCube q (bump i κ ν 1 0) ∧
      InCube q (bump i κ ν 0 1) ∧ InCube q (bump i κ ν 1 1))) :
    i ∈ slabIndices {q} (Finset.Icc 1 q) κ ∪ slabIndices {q} (Finset.Icc 1 q) ν := by
  simp only [inCube_bump_iff h] at hout
  have hF : ∀ μ, μ ≠ κ → μ ≠ ν → 1 ≤ i μ ∧ i μ ≤ q := fun μ _ _ => hw μ
  have hκ := hw κ
  have hν := hw ν
  have hc : i κ = q ∨ i ν = q := by
    by_contra hh
    refine hout ⟨⟨hF, by omega⟩, ⟨hF, by omega⟩, ⟨hF, by omega⟩, ⟨hF, by omega⟩⟩
  rw [Finset.mem_union]
  rcases hc with hc | hc
  · exact Or.inl (mem_slabIndices (by simpa using hc) fun μ _ => by simpa using hw μ)
  · exact Or.inr (mem_slabIndices (by simpa using hc) fun μ _ => by simpa using hw μ)
variable {D : ChessboardSetup}
def pointOf (D : ChessboardSetup) (n : Fin 4 → ℤ) : LatticePoint D.mesh :=
  ⟨fun μ => (n μ : ℝ) * D.mesh, n, fun _ => rfl⟩
def HasCoords (c j : Fin 4 → ℤ) (y : LatticePoint D.mesh) : Prop :=
  ∀ μ, (y : AmbientSpace) μ = ((c μ + j μ : ℤ) : ℝ) * D.mesh
theorem exists_coords (c : Fin 4 → ℤ) (y : LatticePoint D.mesh) :
    ∃ j, HasCoords c j y ∧ y = pointOf D (c + j) := by
  obtain ⟨n, hn⟩ := y.2
  refine ⟨n - c, fun μ => ?_, Subtype.ext (funext fun μ => ?_)⟩
  · simp [hn μ]
  · simp [pointOf, hn μ]
theorem hasCoords_pointOf (c j : Fin 4 → ℤ) : HasCoords c j (pointOf D (c + j)) := fun _ => rfl
theorem hasCoords_bump_zero {c i : Fin 4 → ℤ} {y : LatticePoint D.mesh} (κ ν : Fin 4)
    (h : HasCoords c i y) : HasCoords c (bump i κ ν 0 0) y := fun μ => by
  simpa [bump] using h μ
theorem hasCoords_step_first {c i : Fin 4 → ℤ} {y : LatticePoint D.mesh} {κ ν : Fin 4}
    {s s' t : ℤ} (hs : s' = s + 1) (h : HasCoords c (bump i κ ν s t) y) :
    HasCoords c (bump i κ ν s' t) (y + axisStep D.mesh κ) := fun μ => by
  subst hs
  have hy := h μ
  by_cases e : μ = κ
  · subst e
    simp only [AddSubgroup.coe_add, Pi.add_apply, hy]
    simp only [axisStep, bump, Pi.single_eq_same, if_true]
    push_cast
    ring
  · simp only [AddSubgroup.coe_add, Pi.add_apply, hy]
    simp only [axisStep, bump, Pi.single_eq_of_ne e, if_neg e]
    simp
theorem hasCoords_step_second {c i : Fin 4 → ℤ} {y : LatticePoint D.mesh} {κ ν : Fin 4}
    {s t t' : ℤ} (ht : t' = t + 1) (h : HasCoords c (bump i κ ν s t) y) :
    HasCoords c (bump i κ ν s t') (y + axisStep D.mesh ν) := fun μ => by
  subst ht
  have hy := h μ
  by_cases e : μ = ν
  · subst e
    simp only [AddSubgroup.coe_add, Pi.add_apply, hy]
    simp only [axisStep, bump, Pi.single_eq_same, if_true]
    push_cast
    ring
  · simp only [AddSubgroup.coe_add, Pi.add_apply, hy]
    simp only [axisStep, bump, Pi.single_eq_of_ne e, if_neg e]
    simp
def IsCubeOf (B : Set AmbientSpace) (c : Fin 4 → ℤ) (q : ℤ) : Prop :=
  ∀ (j : Fin 4 → ℤ) (y : LatticePoint D.mesh), HasCoords c j y → ((y : AmbientSpace) ∈ B ↔ InCube q j)
theorem exists_cube (g : ReflectionGrid D) (k : Fin 4 → ℤ) {q : ℤ}
    (hq : PeriodicLattice.torusSide D.L D.m = (q : ℝ) * D.mesh) :
    ∃ c : Fin 4 → ℤ, IsCubeOf (D := D) (g.block k) c q := by
  choose i₀ hi using g.origin_mem
  refine ⟨fun μ => i₀ μ + g.cellRatio * k μ, fun j y hy => ?_⟩
  have ha := D.mesh_pos
  simp only [ReflectionGrid.block, mem_ofPred_eq, mem_Icc, InCube]
  refine forall_congr' fun μ => ?_
  have e : (y : AmbientSpace) μ - (g.origin μ + g.cellSide * (k μ : ℝ)) =
      ((j μ : ℝ) - 1 / 2) * D.mesh := by
    rw [hy μ, hi μ, g.cellSide_eq]
    push_cast
    ring
  rw [e, hq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : (0 : ℝ) ≤ (j μ : ℝ) - 1 / 2 := by
      by_contra hh
      have hh' := not_le.mp hh
      nlinarith
    have h₂' : (j μ : ℝ) - 1 / 2 ≤ q := le_of_mul_le_mul_right h₂ ha
    have h₃ : (0 : ℝ) < (j μ : ℝ) := by linarith
    have h₄ : (j μ : ℝ) < (q : ℝ) + 1 := by linarith
    have h₅ : (0 : ℤ) < j μ := by exact_mod_cast h₃
    have h₆ : j μ < q + 1 := by exact_mod_cast h₄
    omega
  · rintro ⟨h₁, h₂⟩
    have h₃ : (1 : ℝ) ≤ (j μ : ℝ) := by exact_mod_cast h₁
    have h₄ : (j μ : ℝ) ≤ q := by exact_mod_cast h₂
    constructor <;> nlinarith
theorem finite_positiveLinksWithin {B : Set AmbientSpace} {c : Fin 4 → ℤ} {q : ℤ}
    (hB : IsCubeOf (D := D) B c q) : (positiveLinksWithin D.mesh B).Finite := by
  classical
  refine ((Finset.finite_toSet ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc 1 q) ×ˢ
    (Finset.univ : Finset (Fin 4)))).image
      fun x => (Link.forwardFrom (pointOf D (c + x.1)) x.2 : Link D.mesh)).subset ?_
  rintro b ⟨⟨x, κ, rfl⟩, ht, -⟩
  obtain ⟨j, hj, rfl⟩ := exists_coords c x
  refine ⟨(j, κ), ?_, rfl⟩
  have hw := (hB j _ hj).mp ht
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset,
    Finset.mem_Icc, Finset.mem_univ, and_true]
  exact hw
theorem forwardFrom_mem_boxLinks_iff {B : Set AmbientSpace} {c : Fin 4 → ℤ} {q : ℤ}
    (hB : IsCubeOf (D := D) B c q) {y : LatticePoint D.mesh} {κ : Fin 4} {j j' : Fin 4 → ℤ}
    (h : HasCoords c j y) (h' : HasCoords c j' (y + axisStep D.mesh κ)) :
    Link.forwardFrom y κ ∈ D.boxLinks B ↔ InCube q j ∧ InCube q j' := by
  rw [← Finset.mem_coe, D.coe_boxLinks (finite_positiveLinksWithin hB)]
  have hp : Link.forwardFrom y κ ∈ positiveLinkSet D.mesh := ⟨y, κ, rfl⟩
  simp only [positiveLinksWithin, mem_inter_iff, hp, true_and, linksWithin, mem_ofPred_eq]
  exact and_congr (hB _ _ h) (hB _ _ h')
theorem edges_mem_boxLinks_facts {B : Set AmbientSpace} {c : Fin 4 → ℤ} {q : ℤ}
    (hB : IsCubeOf (D := D) B c q) {p : D.Plaquette} {i : Fin 4 → ℤ}
    (hi : HasCoords c i p.corner) :
    ((∃ b ∈ p.edges, b ∈ D.boxLinks B) →
      (InCube q (bump i p.lowAxis p.highAxis 0 0) ∧
          InCube q (bump i p.lowAxis p.highAxis 1 0)) ∨
        (InCube q (bump i p.lowAxis p.highAxis 1 0) ∧
          InCube q (bump i p.lowAxis p.highAxis 1 1)) ∨
        (InCube q (bump i p.lowAxis p.highAxis 0 1) ∧
          InCube q (bump i p.lowAxis p.highAxis 1 1)) ∨
        (InCube q (bump i p.lowAxis p.highAxis 0 0) ∧
          InCube q (bump i p.lowAxis p.highAxis 0 1))) ∧
    ((InCube q (bump i p.lowAxis p.highAxis 0 0) ∧ InCube q (bump i p.lowAxis p.highAxis 1 0) ∧
        InCube q (bump i p.lowAxis p.highAxis 0 1) ∧
        InCube q (bump i p.lowAxis p.highAxis 1 1)) →
      ∀ b ∈ p.edges, b ∈ D.boxLinks B) := by
  have i₀₀ := hasCoords_bump_zero p.lowAxis p.highAxis hi
  have i₁₀ : HasCoords c (bump i p.lowAxis p.highAxis 1 0) (p.corner + axisStep D.mesh p.lowAxis) :=
    hasCoords_step_first (by norm_num) i₀₀
  have i₀₁ : HasCoords c (bump i p.lowAxis p.highAxis 0 1)
      (p.corner + axisStep D.mesh p.highAxis) :=
    hasCoords_step_second (by norm_num) i₀₀
  have i₁₁ : HasCoords c (bump i p.lowAxis p.highAxis 1 1)
      (p.corner + axisStep D.mesh p.lowAxis + axisStep D.mesh p.highAxis) :=
    hasCoords_step_second (by norm_num) i₁₀
  have i₁₁' : HasCoords c (bump i p.lowAxis p.highAxis 1 1)
      (p.corner + axisStep D.mesh p.highAxis + axisStep D.mesh p.lowAxis) :=
    hasCoords_step_first (by norm_num) i₀₁
  have b₁ := forwardFrom_mem_boxLinks_iff hB i₀₀ i₁₀
  have b₂ := forwardFrom_mem_boxLinks_iff hB i₁₀ i₁₁
  have b₃ := forwardFrom_mem_boxLinks_iff hB i₀₁ i₁₁'
  have b₄ := forwardFrom_mem_boxLinks_iff hB i₀₀ i₀₁
  constructor
  · rintro ⟨b, hb, hm⟩
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl (b₁.mp hm)
    · exact Or.inr (Or.inl (b₂.mp hm))
    · exact Or.inr (Or.inr (Or.inl (b₃.mp hm)))
    · exact Or.inr (Or.inr (Or.inr (b₄.mp hm)))
  · rintro ⟨w₀₀, w₁₀, w₀₁, w₁₁⟩ b hb
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact b₁.mpr ⟨w₀₀, w₁₀⟩
    · exact b₂.mpr ⟨w₁₀, w₁₁⟩
    · exact b₃.mpr ⟨w₀₁, w₁₁⟩
    · exact b₄.mpr ⟨w₀₀, w₀₁⟩
def faceOf (D : ChessboardSetup) (c : Fin 4 → ℤ) (x : Σ _ : AxisPair, Fin 4 → ℤ) :
    D.Plaquette :=
  ⟨pointOf D (c + x.2), x.1.1.1, x.1.1.2, x.1.2⟩
theorem boundaryPlaquetteCount_le {B : Set AmbientSpace} {c : Fin 4 → ℤ} {q : ℤ}
    (hB : IsCubeOf (D := D) B c q) :
    D.boundaryPlaquetteCount B ≤ (pairSlabIndices {0, q} (Finset.Icc 1 q)).card := by
  refine ncard_le_card_of_surj _ (faceOf D c) ?_
  rintro p ⟨hin, b, hb, hout⟩
  obtain ⟨i, hi, hcorner⟩ := exists_coords c p.corner
  obtain ⟨f₁, f₂⟩ := edges_mem_boxLinks_facts hB (p := p) hi
  refine ⟨⟨⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩, i⟩, ?_, ?_⟩
  · simp only [pairSlabIndices, Finset.mem_sigma, Finset.mem_univ, true_and]
    exact mem_slabs_of_crossing p.lowAxis_lt_highAxis.ne (f₁ hin) fun hh => hout (f₂ hh b hb)
  · exact ElementaryPlaquette.ext hcorner.symm rfl rfl
theorem exists_cube_representative {q : ℤ} (hq : 0 < q) (n : ℤ) :
    ∃ i r : ℤ, 1 ≤ i ∧ i ≤ q ∧ i = n - q * r := by
  refine ⟨(n - 1) % q + 1, (n - 1) / q, ?_, ?_, ?_⟩
  · have := Int.emod_nonneg (n - 1) hq.ne'
    omega
  · have := Int.emod_lt_of_pos (n - 1) hq
    omega
  · have := Int.emod_add_mul_ediv (n - 1) q
    linarith
theorem torusBoundaryPlaquetteCount_le {B : Set AmbientSpace} {c : Fin 4 → ℤ} {q : ℤ}
    (hq₀ : 0 < q) (hq : PeriodicLattice.torusSide D.L D.m = (q : ℝ) * D.mesh)
    (hB : IsCubeOf (D := D) B c q) :
    D.torusBoundaryPlaquetteCount B ≤ (pairSlabIndices {q} (Finset.Icc 1 q)).card := by
  refine ncard_le_card_of_surj _ (fun x => CutoffLattice.projectFace D.L D.m D.K
    (faceOf D c x)) ?_
  intro p' hp'
  obtain ⟨N, hN⟩ := p'.origin.2
  choose i r h₁ h₂ h₃ using fun μ => exists_cube_representative hq₀ (N μ - c μ)
  have hw : InCube q i := fun μ => ⟨h₁ μ, h₂ μ⟩
  set x : Σ _ : AxisPair, Fin 4 → ℤ :=
    ⟨⟨(p'.firstAxis, p'.secondAxis), p'.firstAxis_lt_secondAxis⟩, i⟩ with hx
  have hcover : CutoffLattice.projectFace D.L D.m D.K (faceOf D c x) = p' := by
    refine PeriodicLattice.Plaquette.ext (Subtype.ext (funext fun μ => ?_)) rfl rfl
    have e : ((c + i) μ : ℝ) * D.mesh =
        (N μ : ℝ) * D.mesh - (r μ : ℝ) * PeriodicLattice.torusSide D.L D.m := by
      rw [hq]
      have : ((c + i) μ : ℤ) = N μ - q * r μ := by
        simp only [Pi.add_apply, h₃ μ]
        ring
      rw [this]
      push_cast
      ring
    have key : ((CutoffLattice.projectFace D.L D.m D.K (faceOf D c x)).origin :
        PeriodicLattice.FourTorus D.L D.m) μ =
        ((((c + i) μ : ℝ) * D.mesh : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) := rfl
    have hz : ((((c + i) μ : ℝ) * D.mesh : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
        (((N μ : ℝ) * D.mesh : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) := by
      rw [e, AddCircle.coe_sub, sub_eq_self]
      exact (AddCircle.coe_eq_zero_iff _).mpr ⟨r μ, by simp⟩
    exact key.trans (hz.trans (hN μ).symm)
  refine ⟨x, ?_, hcover⟩
  simp only [pairSlabIndices, Finset.mem_sigma, Finset.mem_univ, true_and, hx]
  refine mem_topSlabs p'.firstAxis_lt_secondAxis.ne hw fun hh => hp' ?_
  exact ⟨faceOf D c x, (edges_mem_boxLinks_facts hB (p := faceOf D c x)
    (hasCoords_pointOf c i)).2 hh, hcover⟩
def linearSize (D : ChessboardSetup) : ℕ := 2 * D.L ^ ((D.m : ℕ) + (D.K : ℕ))
theorem torusSide_eq_linearSize_mul (D : ChessboardSetup) :
    PeriodicLattice.torusSide D.L D.m = ((linearSize D : ℤ) : ℝ) * D.mesh := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  simp only [PeriodicLattice.torusSide, linearSize, ChessboardSetup.mesh,
    PeriodicLattice.meshSize]
  push_cast
  rw [pow_add, zpow_neg, zpow_natCast]
  field_simp
theorem linearSize_pos (D : ChessboardSetup) : 0 < linearSize D := by
  have hL : 0 < D.L := by
    have := D.one_lt_factor
    have h : (0 : ℝ) < D.L := by linarith
    exact_mod_cast h
  exact Nat.mul_pos two_pos (pow_pos hL _)
theorem statement_holds : Statement := by
  intro D g _ _ B hB
  obtain ⟨k, rfl⟩ := hB
  have hq := torusSide_eq_linearSize_mul D
  have hq₀ : (0 : ℤ) < (linearSize D : ℤ) := by exact_mod_cast linearSize_pos D
  obtain ⟨c, hc⟩ := exists_cube g k hq
  have hI : (Finset.Icc (1 : ℤ) (linearSize D : ℤ)).card = linearSize D := by simp
  have h₁ := (boundaryPlaquetteCount_le hc).trans (card_pairSlabIndices_le _ _)
  have h₂ := (torusBoundaryPlaquetteCount_le hq₀ hq hc).trans (card_pairSlabIndices_le _ _)
  have hE : ({0, (linearSize D : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  rw [hI] at h₁ h₂
  rw [Finset.card_singleton] at h₂
  have h₃ : D.boundaryPlaquetteCount (g.block k) + D.torusBoundaryPlaquetteCount (g.block k) ≤
      36 * linearSize D ^ 3 := by
    have := Nat.mul_le_mul_right (linearSize D ^ 3) hE
    omega
  have hr : PeriodicLattice.torusSide D.L D.m / D.mesh = (linearSize D : ℝ) := by
    rw [hq, mul_div_assoc, div_self D.mesh_pos.ne', mul_one]
    simp
  rw [hr]
  have h₄ : ((D.boundaryPlaquetteCount (g.block k) + D.torusBoundaryPlaquetteCount (g.block k) :
      ℕ) : ℝ) ≤ ((36 * linearSize D ^ 3 : ℕ) : ℝ) := by exact_mod_cast h₃
  simpa [boxBoundaryConstant] using h₄
end YangMills.Construction.ChessboardTori.BoxBoundaryCount
end
