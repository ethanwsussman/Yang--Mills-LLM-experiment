import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.QuotientCarriesTheLinearObjects
import YangMills.Construction.Towers.QuotientOfATowerCarriesSetsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open InfiniteLattice (AmbientSpace)
namespace ProjectionSmoothing
variable {L n k i j : ℕ}
section Flows
variable (ends : ∀ b : Edge L k i,
  (projEdge L n k i b).source = projVertex L n k i b.initial ∧
    (projEdge L n k i b).target = projVertex L n k i b.terminal)
include ends
theorem map_projEdge_stepsInOrder (ν : Fin 4 → ℤ) (x : Vertex L k i) (l : List (Fin 4)) :
    (stepsInOrder ν x l).map (projEdge L n k i) =
      PeriodicLattice.stepsThroughAxes ν (projVertex L n k i x) l := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.map_stepsInOrder <;> assumption
end Flows
def axisList {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) : List (Fin 4) :=
  (List.finRange _).map fun i => ((σ i : S) : Fin 4)
theorem sum_axisList_congr {M : Type*} [AddCommMonoid M] {S S' : Finset (Fin 4)} (h : S = S')
    [i : Fintype (Fin S.card ≃ S)] [i' : Fintype (Fin S'.card ≃ S')] (f f' : List (Fin 4) → M)
    (hf : ∀ σ : Fin S.card ≃ S, f (axisList σ) = f' (axisList σ)) :
    ∑ σ : Fin S.card ≃ S, f (axisList σ) = ∑ σ : Fin S'.card ≃ S', f' (axisList σ) ∧
      Fintype.card (Fin S.card ≃ S) = Fintype.card (Fin S'.card ≃ S') := by
  subst h
  obtain rfl := Subsingleton.elim i i'
  exact ⟨Finset.sum_congr rfl fun σ _ => hf σ, rfl⟩
theorem meshAt_pos (hL : 0 < L) : 0 < Tower.meshAt L k j := by
  unfold Tower.meshAt
  positivity
theorem meshAt_le_one (hL : 0 < L) (hjk : j < k) : Tower.meshAt L k j ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact zpow_le_one_of_nonpos₀ h1 (by omega)
theorem toSublattice_projVertex (hL : 0 < L) (y : Vertex L k (j + 1)) :
    (projVertex L n k (j + 1) y).toSublattice (PeriodicLattice.levelDepth k j) =
      projVertex L n k j (toFiner (Tower.meshAt L k j) y) := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.toSublattice_projVertex <;> assumption
theorem isCubeOffset_cubeOffset {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k j) y) :
    IsCubeOffset L y x (cubeOffset L y x) := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.isCubeOffset_of_mem <;> assumption
theorem sum_pointOnAxis_apply (s : Fin 4 → ℝ) (μ : Fin 4) :
    (∑ ν, PeriodicLattice.pointOnAxis L n ν (s ν)) μ =
      ((s μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.sum_pointOnAxis_apply <;> assumption
theorem isBlockOffset_projVertex {y : Vertex L k (j + 1)} {x : Vertex L k j}
    {ν : Fin 4 → ℤ} (h : IsCubeOffset L y x ν) :
    PeriodicLattice.IsBlockOffset (projVertex L n k (j + 1) y) (projVertex L n k j x) ν := by apply _root_.YangMills.Construction.Tower.FieldProjection.isBlockOffset_projVertex <;> assumption
theorem isBlockOffset_unique (hL : 0 < L) (hn : 0 < n) (hjk : j < k)
    {y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1))}
    {x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)} {ν ν' : Fin 4 → ℤ}
    (h : PeriodicLattice.IsBlockOffset y x ν) (h' : PeriodicLattice.IsBlockOffset y x ν') :
    ν = ν' := by
  funext μ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha := meshAt_pos (k := k) (j := j) hL
  have ha1 := meshAt_le_one (k := k) hL hjk
  have e : (((ν μ : ℝ) * Tower.meshAt L k j : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
      (((ν' μ : ℝ) * Tower.meshAt L k j : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    have e₁ := congrFun h.1 μ
    have e₂ := congrFun h'.1 μ
    rw [sum_pointOnAxis_apply, Tower.meshSize_levelDepth] at e₁ e₂
    exact e₁.symm.trans e₂
  have e₀ : ((((ν μ - ν' μ : ℤ) : ℝ) * Tower.meshAt L k j : ℝ) :
      AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
    push_cast
    rw [sub_mul, AddCircle.coe_sub, e, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 e₀
  have hside : (L : ℝ) ≤ PeriodicLattice.torusSide L n := by
    have : (L : ℝ) ^ 1 ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 hn
    unfold PeriodicLattice.torusSide
    nlinarith
  have hD : |((ν μ - ν' μ : ℤ) : ℝ)| ≤ (L : ℝ) - 1 := by
    have b₁ := h.2 μ
    have b₂ := h'.2 μ
    have : |ν μ - ν' μ| ≤ (L : ℤ) - 1 := by
      rw [abs_le] at *
      have c₁ := abs_le.1 (le_refl |ν μ|)
      have c₂ := abs_le.1 (le_refl |ν' μ|)
      constructor <;> omega
    have h' : ((|ν μ - ν' μ| : ℤ) : ℝ) ≤ (((L : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hm0 : m = 0 := by
    by_contra hne
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hne
    have hs0 : 0 ≤ PeriodicLattice.torusSide L n := le_trans (by linarith) hside
    have habs : |(m : ℝ)| * PeriodicLattice.torusSide L n =
        |((ν μ - ν' μ : ℤ) : ℝ)| * Tower.meshAt L k j := by
      have hmm := congrArg abs hm
      rwa [zsmul_eq_mul, abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_pos ha] at hmm
    have l₁ : PeriodicLattice.torusSide L n ≤ |(m : ℝ)| * PeriodicLattice.torusSide L n :=
      le_mul_of_one_le_left hs0 hm1
    have l₂ : |((ν μ - ν' μ : ℤ) : ℝ)| * Tower.meshAt L k j ≤ (L : ℝ) - 1 := by
      calc _ ≤ |((ν μ - ν' μ : ℤ) : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left ha1 (abs_nonneg _)
        _ ≤ (L : ℝ) - 1 := by simpa using hD
    linarith
  rw [hm0, zero_smul] at hm
  have hz : ((ν μ - ν' μ : ℤ) : ℝ) = 0 := by
    rcases mul_eq_zero.1 hm.symm with h0 | h0
    · exact h0
    · exact absurd h0 ha.ne'
  have : ν μ - ν' μ = 0 := by exact_mod_cast hz
  omega
theorem blockOffset_projVertex (hL : 0 < L) (hn : 0 < n) (hjk : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k j) y) :
    PeriodicLattice.blockOffset (projVertex L n k (j + 1) y) (projVertex L n k j x) =
      cubeOffset L y x := by
  have h := isBlockOffset_projVertex (n := n) (isCubeOffset_cubeOffset hx)
  exact isBlockOffset_unique hL hn hjk
    (Classical.epsilon_spec (p := PeriodicLattice.IsBlockOffset _ _) ⟨_, h⟩) h
theorem pushforwardForm_projEdge {ℬ : Set (Edge L k j)}
    (hinj : InjOn (projEdge L n k j) ℬ) (B : Edge L k j → Matrices.ComplexMatrix2)
    {b : Edge L k j} (hb : b ∈ ℬ) :
    pushforwardForm L n k j ℬ B (projEdge L n k j b) = B b := by
  have h : ∃ b' ∈ ℬ, projEdge L n k j b' = projEdge L n k j b := ⟨b, hb, rfl⟩
  unfold pushforwardForm
  rw [dif_pos h, hinj h.choose_spec.1 hb h.choose_spec.2]
theorem bondFormSumAlong_map_projEdge {ℬ : Set (Edge L k j)}
    (hinj : InjOn (projEdge L n k j) ℬ) (B : Edge L k j → Matrices.ComplexMatrix2)
    {Γ : List (Edge L k j)} (hΓ : ∀ b ∈ Γ, b ∈ ℬ) :
    PeriodicLattice.bondFormSumAlong (pushforwardForm L n k j ℬ B) (Γ.map (projEdge L n k j)) =
      sumAlong B Γ := by
  unfold PeriodicLattice.bondFormSumAlong sumAlong
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun b hb => pushforwardForm_projEdge hinj B (hΓ b hb)
theorem contourFormAverage_projVertex (hL : 0 < L) (hn : 0 < n) (hjk : j < k)
    (ends : ∀ b : Edge L k j,
      (projEdge L n k j b).source = projVertex L n k j b.initial ∧
        (projEdge L n k j b).target = projVertex L n k j b.terminal)
    {ℬ : Set (Edge L k j)} (hinj : InjOn (projEdge L n k j) ℬ)
    (B : Edge L k j → Matrices.ComplexMatrix2) {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k j) y)
    (hpath : ∀ σ, ∀ b ∈ contour L y x σ, b ∈ ℬ) :
    PeriodicLattice.contourFormAverage (pushforwardForm L n k j ℬ B)
        (projVertex L n k (j + 1) y) (projVertex L n k j x) =
      contourAverage L B y x := by
  have hd := blockOffset_projVertex (n := n) hL hn hjk hx
  have hS : offsetSupport L y x =
      PeriodicLattice.offsetAxes (projVertex L n k (j + 1) y)
        (projVertex L n k j x) := by
    unfold offsetSupport PeriodicLattice.offsetAxes
    rw [hd]
  obtain ⟨hsum, hcard⟩ := sum_axisList_congr hS
    (f := fun l => sumAlong B
      (stepsInOrder (cubeOffset L y x) (toFiner (Tower.meshAt L k j) y) l))
    (f' := fun l => PeriodicLattice.bondFormSumAlong (pushforwardForm L n k j ℬ B)
      (PeriodicLattice.stepsThroughAxes
        (PeriodicLattice.blockOffset (projVertex L n k (j + 1) y) (projVertex L n k j x))
        ((projVertex L n k (j + 1) y).toSublattice (PeriodicLattice.levelDepth k j)) l))
    (fun σ => by
      show _ = PeriodicLattice.bondFormSumAlong _ (PeriodicLattice.stepsThroughAxes _ _ _)
      rw [hd, toSublattice_projVertex hL, ← map_projEdge_stepsInOrder ends]
      exact (bondFormSumAlong_map_projEdge hinj B (hpath σ)).symm)
  unfold PeriodicLattice.contourFormAverage contourAverage
  have e₁ : ∑ σ : ContourOrder L y x, sumAlong B (contour L y x σ) =
      ∑ σ : PeriodicLattice.AxisOrdering (projVertex L n k (j + 1) y) (projVertex L n k j x),
        PeriodicLattice.bondFormSumAlong (pushforwardForm L n k j ℬ B)
          (PeriodicLattice.orderedContour _ _ σ) := hsum
  rw [e₁]
  have e₂ : Fintype.card (ContourOrder L y x) =
      Fintype.card
        (PeriodicLattice.AxisOrdering (projVertex L n k (j + 1) y) (projVertex L n k j x)) :=
    hcard
  rw [e₂]
theorem shifted_mem_cubeVertices (hL : 0 < L) (c : Edge L k (j + 1)) {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (Tower.meshAt L k j) c.initial) :
    shifted c x ∈ cubeVertices L (Tower.meshAt L k j) c.terminal := by apply _root_.YangMills.Construction.Tower.FullSpace.ScalingOfValues.shifted_mem_cubeVertices <;> assumption
end ProjectionSmoothing
open ProjectionSmoothing in
theorem projectionCommutesWithSmoothing
    (hQ : Tower.EdgeProjectionProperties)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hB : CubesCorridorsPivotEdgesAndPaths) :
    ProjectionCommutesWithSmoothing := by
  intro L k j n hL hjk hn c hc B
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : ProjPreservesStructures L n k j c :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk n hn).2 j hjk c hc
  have ends : ∀ b : Edge L k j,
      (projEdge L n k j b).source = projVertex L n k j b.initial ∧
        (projEdge L n k j b).target = projVertex L n k j b.terminal := fun b =>
    ⟨((hQ L n k j hL hn hjk.le).1 b).1, ((hQ L n k j hL hn hjk.le).1 b).2.1⟩
  obtain ⟨hdt, hdh, -, -⟩ := (hQ L n k (j + 1) hL hn hjk).1 c
  have hcubes := hB L hL k (j + 1) 1 hk (by omega) hjk le_rfl (by omega)
  have hpaths : PathsStayInCubes L k (j + 1) := hcubes.2.2.2
  have hpart : CubesOfOrderPartition L k (j + 1) 1 := hcubes.1
  have hinj : InjOn (projEdge L n k j) (doubleCubeLinks L (Tower.meshAt L k j) c) := by
    intro b hb b' hb' h
    have ht : projVertex L n k j b.initial = projVertex L n k j b'.initial := by
      rw [← (ends b).1, ← (ends b').1, h]
    have hh : projVertex L n k j b.terminal = projVertex L n k j b'.terminal := by
      rw [← (ends b).2, ← (ends b').2, h]
    exact InfiniteLattice.Link.ext
      (Subtype.ext (Q.injOn_doubleCube hb.1 hb'.1 (congrArg Subtype.val ht)))
      (Subtype.ext (Q.injOn_doubleCube hb.2 hb'.2 (congrArg Subtype.val hh)))
  have hcontour : ∀ y : Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
      ∀ x ∈ cubeVertices L (Tower.meshAt L k j) y, ∀ σ, ∀ b ∈ contour L y x σ,
        b ∈ doubleCubeLinks L (Tower.meshAt L k j) c := by
    intro y hy x hx σ b hb
    have hsite : ∀ z : Vertex L k j, (z = b.initial ∨ z = b.terminal) →
        (z : AmbientSpace) ∈ doubleCube L (Tower.meshAt L k j) c := by
      intro z hz
      have hm : (z : AmbientSpace) ∈ cube L (Tower.meshAt L k j) y :=
        hpaths.contour_vertex_mem y x hx _ ⟨σ, rfl⟩ z (Or.inr (Or.inr ⟨b, hb, hz⟩))
      rcases hy with rfl | rfl
      · exact Or.inl hm
      · exact Or.inr hm
    exact ⟨hsite _ (Or.inl rfl), hsite _ (Or.inr rfl)⟩
  have hmean : ∀ y : Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
      ∀ x ∈ cubeVertices L (Tower.meshAt L k j) y,
        PeriodicLattice.contourFormAverage
            (pushforwardForm L n k j (doubleCubeLinks L (Tower.meshAt L k j) c) B)
            (projVertex L n k (j + 1) y) (projVertex L n k j x) =
          contourAverage L B y x := fun y hy x hx =>
    contourFormAverage_projVertex hL0 hn hjk ends hinj B hx (hcontour y hy x hx)
  refine ⟨hmean, ?_⟩
  have hcross : ∀ x ∈ cubeVertices L (Tower.meshAt L k j) c.initial, ∀ b ∈ crossingPath c x,
      b ∈ doubleCubeLinks L (Tower.meshAt L k j) c := fun x hx b hb =>
    ⟨hpaths.crossing_vertex_mem c x hx _ (Or.inr (Or.inr ⟨b, hb, Or.inl rfl⟩)),
      hpaths.crossing_vertex_mem c x hx _ (Or.inr (Or.inr ⟨b, hb, Or.inr rfl⟩))⟩
  have hbij : BijOn (projVertex L n k j) (cubeVertices L (Tower.meshAt L k j) c.initial)
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (projEdge L n k (j + 1) c).source) := by
    refine ⟨fun x hx => ?_, fun x hx x' hx' h => ?_, fun x' hx' => ?_⟩
    · show ((projVertex L n k j x : Tower.Vertex L n k j) : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.unitBlock (projEdge L n k (j + 1) c).source
      rw [← Q.cube_initial]
      exact ⟨_, hx, rfl⟩
    · exact Subtype.ext (Q.injOn_doubleCube (Or.inl hx) (Or.inl hx') (congrArg Subtype.val h))
    · have hx'' : (x' : PeriodicLattice.FourTorus L n) ∈
          PeriodicLattice.unitBlock (projEdge L n k (j + 1) c).source := hx'
      rw [← Q.cube_initial] at hx''
      obtain ⟨p, hp, he⟩ := hx''
      have hps : p ∈ (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) : Set AmbientSpace) := by
        have hu := hpart.iUnion_cube
        have : p ∈ ⋃ y : Vertex L k (j + 1), cubeOfOrder L (Tower.meshAt L k j) 1 y :=
          mem_iUnion.2 ⟨c.initial, hp⟩
        exact hu ▸ this
      exact ⟨⟨p, hps⟩, hp, Subtype.ext he⟩
  show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
        (projEdge L n k (j + 1) c).source,
      (PeriodicLattice.contourFormAverage
          (pushforwardForm L n k j (doubleCubeLinks L (Tower.meshAt L k j) c) B)
          (projEdge L n k (j + 1) c).source x +
        PeriodicLattice.bondFormSumAlong
          (pushforwardForm L n k j (doubleCubeLinks L (Tower.meshAt L k j) c) B)
          (PeriodicLattice.crossingPath (projEdge L n k (j + 1) c) x) -
        PeriodicLattice.contourFormAverage
          (pushforwardForm L n k j (doubleCubeLinks L (Tower.meshAt L k j) c) B)
          (projEdge L n k (j + 1) c).target
          (PeriodicLattice.shiftAcross (projEdge L n k (j + 1) c) x)) =
    PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ cubeVertices L (Tower.meshAt L k j) c.initial,
      (contourAverage L B c.initial x + sumAlong B (crossingPath c x) -
        contourAverage L B c.terminal (shifted c x))
  congr 1
  refine (finsum_mem_eq_of_bijOn (projVertex L n k j) hbij fun x hx => ?_).symm
  rw [← Q.shifted_eq x hx, ← Q.crossingPath_eq x hx, hdt, hdh,
    hmean c.initial (Or.inl rfl) x hx,
    hmean c.terminal (Or.inr rfl) _ (shifted_mem_cubeVertices hL0 c hx)]
  congr 2
  exact (bondFormSumAlong_map_projEdge hinj B (hcross x hx)).symm
end YangMills.Construction.Tower.FullSpace
end
