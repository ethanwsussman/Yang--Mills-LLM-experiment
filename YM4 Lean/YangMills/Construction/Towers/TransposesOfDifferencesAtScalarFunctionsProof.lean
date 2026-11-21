import YangMills.Construction.Towers.TransposesOfDifferencesAtScalarFunctions
import Mathlib
set_option autoImplicit false
open Function (support)
noncomputable section
namespace YangMills.Construction.Tower.DifferenceAdjoints
open FullSpace
section Supports
variable {ι : Type} {R : Type} [CommRing R]
theorem support_sub_finite {f g : ι → R} (hf : (support f).Finite) (hg : (support g).Finite) :
    (support fun x => f x - g x).Finite := by
  refine (hf.union hg).subset fun x hx => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact (Function.mem_support.1 hx) (by simp [h.1, h.2])
theorem support_add_finite {f g : ι → R} (hf : (support f).Finite) (hg : (support g).Finite) :
    (support fun x => f x + g x).Finite := by
  refine (hf.union hg).subset fun x hx => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact (Function.mem_support.1 hx) (by simp [h.1, h.2])
theorem support_mul_finite_of_right {w v : ι → R} (hv : (support v).Finite) :
    (support fun x => w x * v x).Finite := by
  refine hv.subset fun x hx => ?_
  by_contra h
  simp only [Function.mem_support, not_not] at h
  exact (Function.mem_support.1 hx) (by simp [h])
theorem finsum_sum_mul_comm {κ : Type} [Fintype κ] (h : κ → ι → R) (c : ι → R)
    (hc : (support c).Finite) :
    ∑ᶠ x, (∑ ν, h ν x) * c x = ∑ ν, ∑ᶠ x, h ν x * c x := by
  simp only [Finset.sum_mul]
  exact finsum_sum_comm _ _ fun ν _ => support_mul_finite_of_right hc
theorem funext_of_finsum_mul (f f' : ι → R)
    (h : ∀ v : ι → R, (support v).Finite → ∑ᶠ x, f x * v x = ∑ᶠ x, f' x * v x) : f = f' := by
  classical
  funext x
  have hfin : (support (Pi.single x 1 : ι → R)).Finite := by
    refine (Set.finite_singleton x).subset fun y hy => ?_
    by_contra hne
    exact (Function.mem_support.1 hy) (Pi.single_eq_of_ne hne _)
  have key := h _ hfin
  rw [finsum_eq_single _ x (fun y hy => by simp [Pi.single_eq_of_ne hy]),
    finsum_eq_single _ x (fun y hy => by simp [Pi.single_eq_of_ne hy])] at key
  simpa using key
end Supports
variable {a : ℝ} {R : Type} [CommRing R]
theorem support_comp_add_finite {v : InfiniteLattice.LatticePoint a → R} (hv : (support v).Finite)
    (s : InfiniteLattice.LatticePoint a) :
    (support fun x => v (x + s)).Finite := by
  have := hv.preimage (f := fun x : InfiniteLattice.LatticePoint a => x + s) (add_left_injective s).injOn
  exact this.subset fun x hx => hx
theorem finsum_sub_shift_mul (s : InfiniteLattice.LatticePoint a) (w v : InfiniteLattice.LatticePoint a → R)
    (hv : (support v).Finite) :
    ∑ᶠ x, (w (x - s) - w x) * v x = ∑ᶠ x, w x * (v (x + s) - v x) := by
  have h1 : (support fun x => w (x - s) * v x).Finite := support_mul_finite_of_right hv
  have h2 : (support fun x => w x * v x).Finite := support_mul_finite_of_right hv
  have h3 : (support fun x => w x * v (x + s)).Finite :=
    support_mul_finite_of_right (support_comp_add_finite hv s)
  have h4 : ∑ᶠ x, w (x - s) * v x = ∑ᶠ x, w x * v (x + s) :=
    (finsum_comp_equiv (Equiv.addRight s) (f := fun x => w (x - s) * v x)).symm.trans
      (finsum_congr fun x => by simp)
  simp only [sub_mul, mul_sub]
  rw [finsum_sub_distrib h1 h2, finsum_sub_distrib h3 h2, h4]
theorem axisStep_injective (ha : a ≠ 0) : Function.Injective (InfiniteLattice.axisStep a) := by
  intro μ ν h
  by_contra hne
  have h' : (Pi.single μ a : InfiniteLattice.AmbientSpace) μ = (Pi.single ν a : InfiniteLattice.AmbientSpace) μ :=
    congrArg (fun s : InfiniteLattice.LatticePoint a => (s : InfiniteLattice.AmbientSpace) μ) h
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h'
  exact ha h'
theorem forwardEdge_bijective (ha : a ≠ 0) :
    Function.Bijective fun q : Fin 4 × InfiniteLattice.LatticePoint a => forwardEdge q.2 q.1 := by
  constructor
  · rintro ⟨μ, x⟩ ⟨ν, y⟩ h
    have h1 : x = y := congrArg (fun b : FullSpace.PositiveEdge a => b.1.initial) h
    have h2 : x + InfiniteLattice.axisStep a μ = y + InfiniteLattice.axisStep a ν :=
      congrArg (fun b : FullSpace.PositiveEdge a => b.1.terminal) h
    subst h1
    have h3 := axisStep_injective ha (add_left_cancel h2)
    subst h3
    rfl
  · rintro ⟨b, μ, hb⟩
    refine ⟨(μ, b.initial), Subtype.ext (InfiniteLattice.Link.ext rfl ?_)⟩
    show b.initial + InfiniteLattice.axisStep a μ = b.terminal
    rw [← hb]
    abel
def axisPointEquivEdge (ha : a ≠ 0) : Fin 4 × InfiniteLattice.LatticePoint a ≃ FullSpace.PositiveEdge a :=
  Equiv.ofBijective _ (forwardEdge_bijective ha)
theorem axisPointEquivEdge_symm_forwardEdge (ha : a ≠ 0) (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    (axisPointEquivEdge ha).symm (forwardEdge x μ) = (μ, x) :=
  (axisPointEquivEdge ha).symm_apply_apply (μ, x)
theorem finsum_edges (ha : a ≠ 0) (f : FullSpace.PositiveEdge a → R) (hf : (support f).Finite) :
    ∑ᶠ b, f b = ∑ μ : Fin 4, ∑ᶠ x, f (forwardEdge x μ) := by
  have hfin : (support fun q : Fin 4 × InfiniteLattice.LatticePoint a => f (axisPointEquivEdge ha q)).Finite := by
    have := hf.preimage (f := axisPointEquivEdge ha) (axisPointEquivEdge ha).injective.injOn
    exact this.subset fun x hx => hx
  rw [← finsum_comp_equiv (axisPointEquivEdge ha), finsum_curry _ hfin, finsum_eq_sum_of_fintype]
  rfl
theorem forwardEdge_injective (μ : Fin 4) :
    Function.Injective fun x : InfiniteLattice.LatticePoint a => forwardEdge x μ :=
  fun _ _ h => congrArg (fun b : FullSpace.PositiveEdge a => b.1.initial) h
theorem support_forwardEdge_finite {c : FullSpace.PositiveEdge a → R} (hc : (support c).Finite) (μ : Fin 4) :
    (support fun x => c (forwardEdge x μ)).Finite := by
  have := hc.preimage (f := fun x : InfiniteLattice.LatticePoint a => forwardEdge x μ)
    (forwardEdge_injective μ).injOn
  exact this.subset fun x hx => hx
theorem support_finite_of_axes (ha : a ≠ 0) (f : FullSpace.PositiveEdge a → R)
    (h : ∀ μ, (support fun x => f (forwardEdge x μ)).Finite) : (support f).Finite := by
  refine (Set.finite_iUnion fun μ => (h μ).image fun x => forwardEdge x μ).subset fun b hb => ?_
  obtain ⟨⟨μ, x⟩, rfl⟩ := (axisPointEquivEdge ha).surjective b
  exact Set.mem_iUnion.2 ⟨μ, x, hb, rfl⟩
theorem support_vertexDifference_finite (ha : a ≠ 0) {v : InfiniteLattice.LatticePoint a → R}
    (hv : (support v).Finite) :
    (support (vertexDifference v)).Finite :=
  support_finite_of_axes ha _ fun μ =>
    support_sub_finite (support_comp_add_finite hv (InfiniteLattice.axisStep a μ)) hv
def vertexAdjointFormula (c : FullSpace.PositiveEdge a → R) (x : InfiniteLattice.LatticePoint a) : R :=
  ∑ μ : Fin 4, (c (forwardEdge (x - InfiniteLattice.axisStep a μ) μ) - c (forwardEdge x μ))
theorem isVertexAdjoint_vertexAdjointFormula (ha : a ≠ 0) :
    IsVertexAdjoint (vertexAdjointFormula (a := a) (R := R)) := by
  intro c v hv
  have hv' : (support v).Finite := hv
  rw [finsum_edges ha (fun b => c b * vertexDifference v b)
    (support_mul_finite_of_right (support_vertexDifference_finite ha hv'))]
  simp only [vertexAdjointFormula]
  rw [finsum_sum_mul_comm _ v hv']
  exact Finset.sum_congr rfl fun μ _ =>
    finsum_sub_shift_mul (InfiniteLattice.axisStep a μ) (fun x => c (forwardEdge x μ)) v hv'
theorem vertexAdjointFormula_isLinearMap : IsLinearMap R (vertexAdjointFormula (a := a) (R := R)) where
  map_add c c' := by
    funext x
    simp only [vertexAdjointFormula, Pi.add_apply, add_sub_add_comm, Finset.sum_add_distrib]
  map_smul r c := by
    funext x
    simp only [vertexAdjointFormula, Pi.smul_apply, smul_eq_mul, ← mul_sub, ← Finset.mul_sum]
theorem vertexAdjointProperties_of_ne_zero (ha : a ≠ 0) : VertexAdjointProperties R a := by
  have hF := isVertexAdjoint_vertexAdjointFormula (R := R) ha
  have huniq : ∀ T : (FullSpace.PositiveEdge a → R) → InfiniteLattice.LatticePoint a → R,
      IsVertexAdjoint T → T = vertexAdjointFormula := by
    intro T hT
    funext c
    exact funext_of_finsum_mul _ _ fun v hv => (hT c v hv).trans (hF c v hv).symm
  have hspec : IsVertexAdjoint (vertexAdjoint (a := a) (R := R)) :=
    Classical.epsilon_spec ⟨_, hF⟩
  have heq := huniq _ hspec
  refine ⟨fun v hv => support_vertexDifference_finite ha hv, ⟨vertexAdjointFormula, hF, huniq⟩, hspec, ?_, ?_⟩
  · rw [heq]
    exact vertexAdjointFormula_isLinearMap
  · intro c x
    rw [heq]
    rfl
abbrev AxisPair : Type := {q : Fin 4 × Fin 4 // q.1 < q.2}
def faceAt (q : AxisPair) (x : InfiniteLattice.LatticePoint a) : InfiniteLattice.ElementaryPlaquette a :=
  ⟨x, q.1.1, q.1.2, q.2⟩
def axisPairEquivFace : AxisPair × InfiniteLattice.LatticePoint a ≃ InfiniteLattice.ElementaryPlaquette a where
  toFun q := faceAt q.1 q.2
  invFun p := (⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩, p.corner)
  left_inv := by
    rintro ⟨⟨⟨μ, ν⟩, h⟩, x⟩
    rfl
  right_inv := by
    rintro ⟨x, μ, ν, h⟩
    rfl
theorem finsum_faces (f : InfiniteLattice.ElementaryPlaquette a → R) (hf : (support f).Finite) :
    ∑ᶠ p, f p = ∑ q : AxisPair, ∑ᶠ x, f (faceAt q x) := by
  have hfin : (support fun q : AxisPair × InfiniteLattice.LatticePoint a => f (axisPairEquivFace q)).Finite := by
    have := hf.preimage (f := axisPairEquivFace) axisPairEquivFace.injective.injOn
    exact this.subset fun x hx => hx
  rw [← finsum_comp_equiv axisPairEquivFace, finsum_curry _ hfin, finsum_eq_sum_of_fintype]
  rfl
theorem support_finite_of_axisPairs (f : InfiniteLattice.ElementaryPlaquette a → R)
    (h : ∀ q, (support fun x => f (faceAt q x)).Finite) : (support f).Finite := by
  refine (Set.finite_iUnion fun q => (h q).image (faceAt q)).subset fun p hp => ?_
  obtain ⟨⟨q, x⟩, rfl⟩ := axisPairEquivFace.surjective p
  exact Set.mem_iUnion.2 ⟨q, x, hp, rfl⟩
theorem support_edgeDifference_finite {c : FullSpace.PositiveEdge a → R} (hc : (support c).Finite) :
    (support (edgeDifference c)).Finite :=
  support_finite_of_axisPairs _ fun q =>
    support_sub_finite (support_sub_finite (support_add_finite (support_forwardEdge_finite hc q.1.1)
      (support_comp_add_finite (support_forwardEdge_finite hc q.1.2) (InfiniteLattice.axisStep a q.1.1)))
      (support_comp_add_finite (support_forwardEdge_finite hc q.1.1) (InfiniteLattice.axisStep a q.1.2)))
      (support_forwardEdge_finite hc q.1.2)
theorem finsum_mul_edgeDifference_plane (g : InfiniteLattice.ElementaryPlaquette a → R)
    {c : FullSpace.PositiveEdge a → R} (hc : (support c).Finite) (q : AxisPair) :
    ∑ᶠ x, g (faceAt q x) * edgeDifference c (faceAt q x) =
      ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.2))) * c (forwardEdge x q.1.1) -
      ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.1))) * c (forwardEdge x q.1.2) := by
  have h1 := support_forwardEdge_finite hc q.1.1
  have h2 := support_forwardEdge_finite hc q.1.2
  have e1 := finsum_sub_shift_mul (InfiniteLattice.axisStep a q.1.2) (fun x => g (faceAt q x))
    (fun x => c (forwardEdge x q.1.1)) h1
  have e2 := finsum_sub_shift_mul (InfiniteLattice.axisStep a q.1.1) (fun x => g (faceAt q x))
    (fun x => c (forwardEdge x q.1.2)) h2
  have n1 : ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.2))) *
        c (forwardEdge x q.1.1) =
      -∑ᶠ x, (g (faceAt q (x - InfiniteLattice.axisStep a q.1.2)) - g (faceAt q x)) *
        c (forwardEdge x q.1.1) := by
    rw [← finsum_neg_distrib]
    exact finsum_congr fun x => by ring
  have n2 : ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.1))) *
        c (forwardEdge x q.1.2) =
      -∑ᶠ x, (g (faceAt q (x - InfiniteLattice.axisStep a q.1.1)) - g (faceAt q x)) *
        c (forwardEdge x q.1.2) := by
    rw [← finsum_neg_distrib]
    exact finsum_congr fun x => by ring
  have hA : (support fun x => g (faceAt q x) *
      (c (forwardEdge (x + InfiniteLattice.axisStep a q.1.1) q.1.2) - c (forwardEdge x q.1.2))).Finite :=
    support_mul_finite_of_right (support_sub_finite (support_comp_add_finite h2 _) h2)
  have hB : (support fun x => g (faceAt q x) *
      (c (forwardEdge (x + InfiniteLattice.axisStep a q.1.2) q.1.1) - c (forwardEdge x q.1.1))).Finite :=
    support_mul_finite_of_right (support_sub_finite (support_comp_add_finite h1 _) h1)
  have hpoint : ∑ᶠ x, g (faceAt q x) * edgeDifference c (faceAt q x) =
      ∑ᶠ x, (g (faceAt q x) *
          (c (forwardEdge (x + InfiniteLattice.axisStep a q.1.1) q.1.2) - c (forwardEdge x q.1.2)) -
        g (faceAt q x) *
          (c (forwardEdge (x + InfiniteLattice.axisStep a q.1.2) q.1.1) - c (forwardEdge x q.1.1))) :=
    finsum_congr fun x => by
      show g (faceAt q x) * (c (forwardEdge x q.1.1) +
        c (forwardEdge (x + InfiniteLattice.axisStep a q.1.1) q.1.2) -
        c (forwardEdge (x + InfiniteLattice.axisStep a q.1.2) q.1.1) -
        c (forwardEdge x q.1.2)) = _
      ring
  rw [hpoint, finsum_sub_distrib hA hB, n1, n2, e1, e2]
  ring
theorem sum_axisPair_by_low {M : Type} [AddCommMonoid M] (T : AxisPair → M) :
    ∑ ρ : Fin 4, ∑ ν : {ν : Fin 4 // ρ < ν}, T ⟨(ρ, ν.1), ν.2⟩ = ∑ q, T q := by
  let e : (Σ ρ : Fin 4, {ν : Fin 4 // ρ < ν}) ≃ AxisPair :=
    { toFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
      invFun := fun q => ⟨q.1.1, q.1.2, q.2⟩
      left_inv := by rintro ⟨ρ, ν, h⟩; rfl
      right_inv := by rintro ⟨⟨μ, ν⟩, h⟩; rfl }
  exact (Fintype.sum_sigma (fun z : Σ ρ : Fin 4, {ν : Fin 4 // ρ < ν} => T (e z))).symm.trans
    (Fintype.sum_equiv e _ _ fun _ => rfl)
theorem sum_axisPair_by_high {M : Type} [AddCommMonoid M] (T : AxisPair → M) :
    ∑ ρ : Fin 4, ∑ ν : {ν : Fin 4 // ν < ρ}, T ⟨(ν.1, ρ), ν.2⟩ = ∑ q, T q := by
  let e : (Σ ρ : Fin 4, {ν : Fin 4 // ν < ρ}) ≃ AxisPair :=
    { toFun := fun z => ⟨(z.2.1, z.1), z.2.2⟩
      invFun := fun q => ⟨q.1.2, q.1.1, q.2⟩
      left_inv := by rintro ⟨ρ, ν, h⟩; rfl
      right_inv := by rintro ⟨⟨μ, ν⟩, h⟩; rfl }
  exact (Fintype.sum_sigma (fun z : Σ ρ : Fin 4, {ν : Fin 4 // ν < ρ} => T (e z))).symm.trans
    (Fintype.sum_equiv e _ _ fun _ => rfl)
def faceAdjointFormulaAt (g : InfiniteLattice.ElementaryPlaquette a → R) (x : InfiniteLattice.LatticePoint a)
    (μ : Fin 4) : R :=
  (∑ ν : {ν : Fin 4 // μ < ν},
    (g ⟨x, μ, ν.1, ν.2⟩ - g ⟨x - InfiniteLattice.axisStep a ν.1, μ, ν.1, ν.2⟩)) -
  ∑ ν : {ν : Fin 4 // ν < μ},
    (g ⟨x, ν.1, μ, ν.2⟩ - g ⟨x - InfiniteLattice.axisStep a ν.1, ν.1, μ, ν.2⟩)
def faceAdjointFormula (ha : a ≠ 0) (g : InfiniteLattice.ElementaryPlaquette a → R)
    (b : FullSpace.PositiveEdge a) : R :=
  faceAdjointFormulaAt g ((axisPointEquivEdge ha).symm b).2 ((axisPointEquivEdge ha).symm b).1
theorem faceAdjointFormula_forwardEdge (ha : a ≠ 0) (g : InfiniteLattice.ElementaryPlaquette a → R)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    faceAdjointFormula ha g (forwardEdge x μ) = faceAdjointFormulaAt g x μ := by
  simp only [faceAdjointFormula, axisPointEquivEdge_symm_forwardEdge]
theorem isFaceAdjoint_faceAdjointFormula (ha : a ≠ 0) :
    IsFaceAdjoint (faceAdjointFormula (R := R) ha) := by
  intro g c hc
  have hc' : (support c).Finite := hc
  rw [finsum_edges ha (fun b => faceAdjointFormula ha g b * c b) (support_mul_finite_of_right hc'),
    finsum_faces (fun p => g p * edgeDifference c p)
      (support_mul_finite_of_right (support_edgeDifference_finite hc')),
    Finset.sum_congr rfl fun q _ => finsum_mul_edgeDifference_plane g hc' q, Finset.sum_sub_distrib,
    ← sum_axisPair_by_low (fun q => ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.2))) *
      c (forwardEdge x q.1.1)),
    ← sum_axisPair_by_high (fun q => ∑ᶠ x, (g (faceAt q x) - g (faceAt q (x - InfiniteLattice.axisStep a q.1.1))) *
      c (forwardEdge x q.1.2)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hρ := support_forwardEdge_finite hc' ρ
  simp only [faceAdjointFormula_forwardEdge, faceAdjointFormulaAt, sub_mul (∑ ν : {ν : Fin 4 // ρ < ν}, _)]
  rw [finsum_sub_distrib (support_mul_finite_of_right hρ) (support_mul_finite_of_right hρ),
    finsum_sum_mul_comm _ _ hρ, finsum_sum_mul_comm _ _ hρ]
  rfl
theorem faceAdjointFormula_isLinearMap (ha : a ≠ 0) : IsLinearMap R (faceAdjointFormula (R := R) ha) where
  map_add g g' := by
    funext b
    simp only [faceAdjointFormula, faceAdjointFormulaAt, Pi.add_apply, add_sub_add_comm,
      Finset.sum_add_distrib]
  map_smul r g := by
    funext b
    simp only [faceAdjointFormula, faceAdjointFormulaAt, Pi.smul_apply, smul_eq_mul, ← mul_sub,
      ← Finset.mul_sum]
theorem faceAdjointProperties_of_ne_zero (ha : a ≠ 0) : FaceAdjointProperties R a := by
  have hF := isFaceAdjoint_faceAdjointFormula (R := R) ha
  have huniq : ∀ T : (InfiniteLattice.ElementaryPlaquette a → R) → FullSpace.PositiveEdge a → R,
      IsFaceAdjoint T → T = faceAdjointFormula ha := by
    intro T hT
    funext g
    exact funext_of_finsum_mul _ _ fun c hc => (hT g c hc).trans (hF g c hc).symm
  have hspec : IsFaceAdjoint (faceAdjoint (a := a) (R := R)) :=
    Classical.epsilon_spec ⟨_, hF⟩
  have heq := huniq _ hspec
  refine ⟨fun c hc => support_edgeDifference_finite hc, ⟨faceAdjointFormula ha, hF, huniq⟩, hspec, ?_, ?_⟩
  · rw [heq]
    exact faceAdjointFormula_isLinearMap ha
  · intro g x μ
    rw [heq]
    exact faceAdjointFormula_forwardEdge ha g x μ
theorem realValuedProperties_of_ne_zero (ha : a ≠ 0) : RealValuedProperties a := by
  have hvert : vertexAdjoint (a := a) (R := ℂ) = vertexAdjointFormula := by
    funext c
    refine funext_of_finsum_mul _ _ fun v hv => ?_
    exact ((vertexAdjointProperties_of_ne_zero (R := ℂ) ha).2.2.1 c v hv).trans
      (isVertexAdjoint_vertexAdjointFormula ha c v hv).symm
  have hface : faceAdjoint (a := a) (R := ℂ) = faceAdjointFormula ha := by
    funext g
    refine funext_of_finsum_mul _ _ fun c hc => ?_
    exact ((faceAdjointProperties_of_ne_zero (R := ℂ) ha).2.2.1 g c hc).trans
      (isFaceAdjoint_faceAdjointFormula ha g c hc).symm
  refine ⟨fun v hv b => ?_, fun c hc p => ?_, fun c hc x => ?_, fun g hg b => ?_,
    vertexAdjointProperties_of_ne_zero ha, faceAdjointProperties_of_ne_zero ha⟩
  · simp [vertexDifference, hv _]
  · simp [edgeDifference, hc _]
  · rw [hvert]
    simp [vertexAdjointFormula, Complex.im_sum, hc _]
  · rw [hface]
    simp [faceAdjointFormula, faceAdjointFormulaAt, Complex.im_sum, hg _]
theorem scalarDifferenceAdjoints_holds : ScalarDifferenceAdjoints := by
  intro L _
  have ha : meshAt L 0 0 ≠ 0 := by simp [meshAt]
  exact ⟨vertexAdjointProperties_of_ne_zero ha, faceAdjointProperties_of_ne_zero ha,
    realValuedProperties_of_ne_zero ha⟩
end YangMills.Construction.Tower.DifferenceAdjoints
end
