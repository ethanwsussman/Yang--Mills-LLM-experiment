import YangMills.Construction.Towers.ContourFamiliesAtTheSideInfinity
import YangMills.Construction.Towers.DilationCarriesObjectsAtAnIndexOfATower
import YangMills.Construction.Towers.DilationCarriesSetsAtAStepOfTheWholeSpace
import YangMills.Construction.Towers.DilationCarriesValuesAtAStepOfTheWholeSpace
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScalingOfValues
variable {L k j i : ℕ}
theorem meshAt_ne_zero (hL : 0 < L) (k i : ℕ) : meshAt L k i ≠ 0 :=
  zpow_ne_zero _ (by exact_mod_cast hL.ne')
theorem meshAt_succ (hL : 0 < L) (k i : ℕ) :
    meshAt L k (i + 1) = (L : ℝ) * meshAt L k i := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.meshAt_succ <;> assumption
theorem exists_vertex_of_coarser (hL : 0 < L) (p : Vertex L k (i + 1)) :
    ∃ q : Vertex L k i, (q : AmbientSpace) = p := by
  obtain ⟨m, hm⟩ := p.2
  refine ⟨⟨p.1, fun μ => (L : ℤ) * m μ, fun μ => ?_⟩, rfl⟩
  rw [hm μ, meshAt_succ hL]
  push_cast
  ring
theorem toFiner_eq {a a' : ℝ} (p : InfiniteLattice.LatticePoint a)
    (q : InfiniteLattice.LatticePoint a') (hq : (q : AmbientSpace) = p) : toFiner a' p = q := by
  have hex : ∃ z : InfiniteLattice.LatticePoint a', (z : AmbientSpace) = p := ⟨q, hq⟩
  exact Subtype.ext ((Classical.epsilon_spec hex).trans hq.symm)
theorem coe_toFiner (hL : 0 < L) (p : Vertex L k (i + 1)) :
    (toFiner (meshAt L k i) p : AmbientSpace) = p := by
  obtain ⟨q, hq⟩ := exists_vertex_of_coarser (i := i) hL p
  rw [toFiner_eq p q hq, hq]
section Transport
variable {a b : ℝ}
theorem linkHolonomy_map (e : InfiniteLattice.Link a ≃ InfiniteLattice.Link b)
    (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2) (γ : List (InfiniteLattice.Link a)) :
    linkHolonomy (transportTotal e U) (γ.map e) = linkHolonomy U γ := by
  have hcomp : transportTotal e U ∘ e = U := funext (transportTotal_apply e U)
  simp only [linkHolonomy, List.map_map, hcomp]
theorem sumAlong_map (e : InfiniteLattice.Link a ≃ InfiniteLattice.Link b)
    (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2) (γ : List (InfiniteLattice.Link a)) :
    sumAlong (transportTotal e U) (γ.map e) = sumAlong U γ := by
  have hcomp : transportTotal e U ∘ e = U := funext (transportTotal_apply e U)
  simp only [sumAlong, List.map_map, hcomp]
theorem isFieldOn_iff_image (e : InfiniteLattice.Link a ≃ InfiniteLattice.Link b)
    (he : ∀ l, e l.opposite = (e l).opposite) (G : Set Matrices.ComplexMatrix2)
    (S : Set (InfiniteLattice.Link a)) (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    IsFieldOn G S U ↔ IsFieldOn G (e '' S) (transportTotal e U) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨l, hl, rfl⟩
      rw [transportTotal_apply]
      exact h₁ l hl
    · rintro _ ⟨l, hl, rfl⟩
      rw [← he, transportTotal_apply, transportTotal_apply]
      exact h₂ l hl
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have hv := h₁ (e l) ⟨l, hl, rfl⟩
      rwa [transportTotal_apply] at hv
    · have hv := h₂ (e l) ⟨l, hl, rfl⟩
      rwa [← he, transportTotal_apply, transportTotal_apply] at hv
end Transport
theorem cubeOffset_unique {a a' : ℝ} (ha : a' ≠ 0) {p : InfiniteLattice.LatticePoint a}
    {q : InfiniteLattice.LatticePoint a'} {ν ν' : Fin 4 → ℤ} (h : IsCubeOffset L p q ν)
    (h' : IsCubeOffset L p q ν') : ν = ν' := by
  funext μ
  have hμ := congrFun (h.1.symm.trans h'.1) μ
  simpa [Finset.sum_apply, Pi.single_apply, ha] using hμ
theorem cubeOffset_spec {a a' : ℝ} {p : InfiniteLattice.LatticePoint a}
    {q : InfiniteLattice.LatticePoint a'} (hq : q ∈ cubeVertices L a' p) :
    IsCubeOffset L p q (cubeOffset L p q) := by
  obtain ⟨ν, hν, hpq⟩ := hq
  refine Classical.epsilon_spec (p := IsCubeOffset L p q) ⟨ν, ?_, ?_⟩
  · rw [hpq]
    exact add_sub_cancel_left _ _
  · simpa using hν
section Scaling
variable (hL : 0 < L) (hj : j ≤ k)
theorem scaleEdge_opposite (l : Edge L k i) :
    scaleEdge hL hj i l.opposite = (scaleEdge hL hj i l).opposite :=
  InfiniteLattice.Link.ext rfl rfl
theorem scaleEdge_forwardFrom (q : Vertex L k i) (μ : Fin 4) :
    scaleEdge hL hj i (InfiniteLattice.Link.forwardFrom q μ) =
      InfiniteLattice.Link.forwardFrom (scaleVertex hL hj i q) μ :=
  InfiniteLattice.Link.ext rfl (by
    show scaleVertex hL hj i (q + InfiniteLattice.axisStep (meshAt L k i) μ) =
      scaleVertex hL hj i q + InfiniteLattice.axisStep (meshAt L j i) μ
    rw [map_add, scaleVertex_axisStep])
theorem scaleEdge_backwardLink (q : Vertex L k i) (μ : Fin 4) :
    scaleEdge hL hj i (backwardLink q μ) = backwardLink (scaleVertex hL hj i q) μ :=
  InfiniteLattice.Link.ext rfl (by
    show scaleVertex hL hj i (q - InfiniteLattice.axisStep (meshAt L k i) μ) =
      scaleVertex hL hj i q - InfiniteLattice.axisStep (meshAt L j i) μ
    rw [map_sub, scaleVertex_axisStep])
theorem map_forwardSteps (μ : Fin 4) (n : ℕ) (q : Vertex L k i) :
    (forwardSteps q μ n).map (scaleEdge hL hj i) =
      forwardSteps (scaleVertex hL hj i q) μ n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [forwardSteps, List.map_cons, ih, scaleEdge_forwardFrom, map_add,
      scaleVertex_axisStep]
theorem map_backwardSteps (μ : Fin 4) (n : ℕ) (q : Vertex L k i) :
    (backwardSteps q μ n).map (scaleEdge hL hj i) =
      backwardSteps (scaleVertex hL hj i q) μ n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [backwardSteps, List.map_cons, ih, scaleEdge_backwardLink, map_sub,
      scaleVertex_axisStep]
theorem map_signedSteps (μ : Fin 4) (n : ℤ) (q : Vertex L k i) :
    (signedSteps q μ n).map (scaleEdge hL hj i) =
      signedSteps (scaleVertex hL hj i q) μ n := by
  unfold signedSteps
  split_ifs with hn
  · exact map_forwardSteps hL hj μ _ q
  · exact map_backwardSteps hL hj μ _ q
theorem map_stepsInOrder (ν : Fin 4 → ℤ) (axes : List (Fin 4)) (q : Vertex L k i) :
    (stepsInOrder ν q axes).map (scaleEdge hL hj i) =
      stepsInOrder ν (scaleVertex hL hj i q) axes := by
  induction axes generalizing q with
  | nil => rfl
  | cons μ axes ih =>
    simp only [stepsInOrder, List.map_append, map_signedSteps, ih, map_add, map_zsmul,
      scaleVertex_axisStep]
theorem scaleVertex_toFiner (p : Vertex L k (i + 1)) :
    scaleVertex hL hj i (toFiner (meshAt L k i) p) =
      toFiner (meshAt L j i) (scaleVertex hL hj (i + 1) p) := by
  symm
  apply toFiner_eq
  rw [coe_scaleVertex, coe_scaleVertex, coe_toFiner hL]
theorem isCubeOffset_scale {p : Vertex L k (i + 1)} {q : Vertex L k i} {ν : Fin 4 → ℤ}
    (h : IsCubeOffset L p q ν) :
    IsCubeOffset L (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q) ν := by
  refine ⟨?_, h.2⟩
  funext μ
  have hμ : (q : AmbientSpace) μ - (p : AmbientSpace) μ = (ν μ : ℝ) * meshAt L k i := by
    simpa [Finset.sum_apply, Pi.single_apply] using congrFun h.1 μ
  have hμ' : ((L : ℝ) ^ (k - j)) * (q : AmbientSpace) μ -
      ((L : ℝ) ^ (k - j)) * (p : AmbientSpace) μ = (ν μ : ℝ) * meshAt L j i := by
    rw [← mul_sub, hμ, ← pow_mul_meshAt hL hj i]
    ring
  simpa [Finset.sum_apply, Pi.single_apply, coe_scaleVertex, scaling_apply] using hμ'
variable {hL hj}
theorem scaleVertex_mem_cubeVertices_iff (hB : PreservesAtLevel hL hj (i + 1))
    (p : Vertex L k (i + 1)) (q : Vertex L k i) :
    scaleVertex hL hj i q ∈ cubeVertices L (meshAt L j i) (scaleVertex hL hj (i + 1) p) ↔
      q ∈ cubeVertices L (meshAt L k i) p := by
  have hc := hB.cubeOfOrder_image 1 (by omega) p
  simp only [Nat.add_sub_cancel] at hc
  show scaling hL k j (q : AmbientSpace) ∈
      cubeOfOrder L (meshAt L j i) 1 (scaleVertex hL hj (i + 1) p) ↔
    (q : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) 1 p
  rw [← hc]
  exact (scaling hL k j).injective.mem_set_image
theorem bijOn_cubeVertices (hB : PreservesAtLevel hL hj (i + 1)) (p : Vertex L k (i + 1)) :
    BijOn (scaleVertex hL hj i) (cubeVertices L (meshAt L k i) p)
      (cubeVertices L (meshAt L j i) (scaleVertex hL hj (i + 1) p)) := by
  refine ⟨fun q hq => (scaleVertex_mem_cubeVertices_iff hB p q).2 hq,
    (scaleVertex hL hj i).injective.injOn, fun z hz => ?_⟩
  refine ⟨(scaleVertex hL hj i).symm z, (scaleVertex_mem_cubeVertices_iff hB p _).1 ?_, by simp⟩
  simpa using hz
theorem forall_cubeVertices_iff (hB : PreservesAtLevel hL hj (i + 1))
    (p : Vertex L k (i + 1)) {P : Vertex L k i → Prop} {Q : Vertex L j i → Prop}
    (h : ∀ q ∈ cubeVertices L (meshAt L k i) p, P q ↔ Q (scaleVertex hL hj i q)) :
    (∀ q ∈ cubeVertices L (meshAt L k i) p, P q) ↔
      ∀ q ∈ cubeVertices L (meshAt L j i) (scaleVertex hL hj (i + 1) p), Q q := by
  constructor
  · intro hP z hz
    obtain ⟨q, hq, rfl⟩ := (bijOn_cubeVertices hB p).surjOn hz
    exact (h q hq).1 (hP q hq)
  · intro hQ q hq
    exact (h q hq).2 (hQ _ ((bijOn_cubeVertices hB p).mapsTo hq))
theorem contour_congr (hB : PreservesAtLevel hL hj (i + 1)) {E X : Type*}
    (W : List (Edge L k i) → E) (W' : List (Edge L j i) → E)
    (hW : ∀ γ, W' (γ.map (scaleEdge hL hj i)) = W γ)
    (F : ∀ ν : Fin 4 → ℤ, (Fin (supportAxes ν).card ≃ supportAxes ν → E) → X)
    {p : Vertex L k (i + 1)} {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) p) :
    F (cubeOffset L (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q))
        (fun σ => W' (contour L (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q) σ)) =
      F (cubeOffset L p q) (fun σ => W (contour L p q σ)) := by
  have hν : cubeOffset L (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q) =
      cubeOffset L p q :=
    cubeOffset_unique (meshAt_ne_zero hL j i)
      (cubeOffset_spec ((scaleVertex_mem_cubeVertices_iff hB p q).2 hq))
      (isCubeOffset_scale hL hj (cubeOffset_spec hq))
  have key : ∀ ν ν' : Fin 4 → ℤ, ν' = ν →
      F ν' (fun σ => W' (stepsInOrder ν'
          (toFiner (meshAt L j i) (scaleVertex hL hj (i + 1) p))
          ((List.finRange _).map fun n => ((σ n : supportAxes ν') : Fin 4)))) =
        F ν (fun σ => W (stepsInOrder ν (toFiner (meshAt L k i) p)
          ((List.finRange _).map fun n => ((σ n : supportAxes ν) : Fin 4)))) := by
    rintro ν _ rfl
    congr 1
    funext σ
    rw [← hW, map_stepsInOrder, scaleVertex_toFiner]
  exact key _ _ hν
theorem familyDiameter_contourHolonomies_eq (hB : PreservesAtLevel hL hj (i + 1))
    (U : Edge L k i → Matrices.ComplexMatrix2) {p : Vertex L k (i + 1)} {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) p) :
    Matrices.ComplexMatrix2.familyDiameter (contourHolonomies L (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q)) =
      Matrices.ComplexMatrix2.familyDiameter (contourHolonomies L U p q) :=
  contour_congr hB (linkHolonomy U) (linkHolonomy (transportTotal (scaleEdge hL hj i) U))
    (linkHolonomy_map _ U) (fun _ g => Matrices.ComplexMatrix2.familyDiameter g) hq
theorem complexContourMean_scale (hB : PreservesAtLevel hL hj (i + 1))
    (U : Edge L k i → Matrices.ComplexMatrix2) {p : Vertex L k (i + 1)} {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) p) :
    complexContourMean L (transportTotal (scaleEdge hL hj i) U)
        (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q) =
      complexContourMean L U p q :=
  contour_congr hB (linkHolonomy U) (linkHolonomy (transportTotal (scaleEdge hL hj i) U))
    (linkHolonomy_map _ U) (fun _ g => PeriodicLattice.complexLogMean g) hq
theorem contourAverage_scale (hB : PreservesAtLevel hL hj (i + 1))
    (A : Edge L k i → Matrices.ComplexMatrix2) {p : Vertex L k (i + 1)} {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) p) :
    contourAverage L (transportTotal (scaleEdge hL hj i) A)
        (scaleVertex hL hj (i + 1) p) (scaleVertex hL hj i q) =
      contourAverage L A p q :=
  contour_congr hB (sumAlong A) (sumAlong (transportTotal (scaleEdge hL hj i) A))
    (sumAlong_map _ A)
    (fun ν g => (((Fintype.card (Fin (supportAxes ν).card ≃ supportAxes ν) : ℝ)⁻¹ : ℝ) :
      ℂ) • ∑ σ, g σ) hq
theorem exists_axisDisplacement_of_edge (hL : 0 < L) (l : Edge L k (i + 1)) (q q' : Vertex L k i)
    (h : (q' : AmbientSpace) - q = (l.terminal : AmbientSpace) - l.initial) :
    ∃ (μ : Fin 4) (n : ℤ), IsAxisDisplacement q q' μ n := by
  obtain ⟨μ, hadj⟩ := l.isAdjacent
  have key : ∀ (s : ℤ), (l.terminal : AmbientSpace) - l.initial =
      s • (Pi.single μ (meshAt L k (i + 1)) : AmbientSpace) →
      IsAxisDisplacement q q' μ (s * L) := by
    intro s hs
    apply Subtype.ext
    funext ν
    have hν := congrFun (h.trans hs) ν
    by_cases hμ : ν = μ
    · subst hμ
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same] at hν
      simp only [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_zsmul, InfiniteLattice.axisStep,
        Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same]
      rw [hν, meshAt_succ hL]
      simp only [zsmul_eq_mul]
      push_cast
      ring
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hμ, smul_zero] at hν
      simp only [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_zsmul, InfiniteLattice.axisStep,
        Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hμ, smul_zero]
      exact hν
  rcases hadj with hadj | hadj
  · refine ⟨μ, _, key 1 ?_⟩
    have hv := congrArg (Subtype.val) hadj
    simpa [InfiniteLattice.axisStep] using hv
  · refine ⟨μ, _, key (-1) ?_⟩
    have hv := congrArg (Subtype.val) hadj
    simpa [InfiniteLattice.axisStep] using hv
theorem coe_shifted (hL : 0 < L) (l : Edge L k (i + 1)) (q : Vertex L k i) :
    (shifted l q : AmbientSpace) = (q : AmbientSpace) + ((l.terminal : AmbientSpace) - l.initial) := by
  have hc := coe_toFiner (i := i) hL (l.terminal - l.initial)
  show (q : AmbientSpace) + (toFiner (meshAt L k i) (l.terminal - l.initial) : AmbientSpace) = _
  rw [hc]
  rfl
theorem scaleVertex_shifted (l : Edge L k (i + 1)) (q : Vertex L k i) :
    scaleVertex hL hj i (shifted l q) =
      shifted (scaleEdge hL hj (i + 1) l) (scaleVertex hL hj i q) := by
  show scaleVertex hL hj i (q + toFiner _ (l.terminal - l.initial)) =
    scaleVertex hL hj i q + toFiner _
      (scaleVertex hL hj (i + 1) l.terminal - scaleVertex hL hj (i + 1) l.initial)
  rw [map_add, scaleVertex_toFiner, map_sub]
theorem shifted_mem_cubeVertices (hL : 0 < L) (l : Edge L k (i + 1)) {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) l.initial) :
    shifted l q ∈ cubeVertices L (meshAt L k i) l.terminal := by
  obtain ⟨ν, hν, hpq⟩ := hq
  refine ⟨ν, hν, ?_⟩
  rw [coe_shifted hL, hpq]
  abel
theorem map_crossingPath (hA : PreservesAtLevel hL hj i) (l : Edge L k (i + 1))
    (q : Vertex L k i) :
    (crossingPath l q).map (scaleEdge hL hj i) =
      crossingPath (scaleEdge hL hj (i + 1) l) (scaleVertex hL hj i q) := by
  obtain ⟨μ, n, h⟩ := exists_axisDisplacement_of_edge hL l q (shifted l q) (by
    rw [coe_shifted hL]
    abel)
  have hp := hA.axisPath_image q (shifted l q) μ n h
  rw [scaleVertex_shifted] at hp
  exact hp
theorem map_axisPath (hA : PreservesAtLevel hL hj i) (l : Edge L k (i + 1)) :
    (axisPath (toFiner (meshAt L k i) l.initial)
        (toFiner (meshAt L k i) l.terminal)).map (scaleEdge hL hj i) =
      axisPath (toFiner (meshAt L j i) (scaleEdge hL hj (i + 1) l).initial)
        (toFiner (meshAt L j i) (scaleEdge hL hj (i + 1) l).terminal) := by
  obtain ⟨μ, n, h⟩ := exists_axisDisplacement_of_edge hL l (toFiner (meshAt L k i) l.initial)
    (toFiner (meshAt L k i) l.terminal) (by rw [coe_toFiner hL, coe_toFiner hL])
  have hp := hA.axisPath_image _ _ μ n h
  rw [scaleVertex_toFiner, scaleVertex_toFiner] at hp
  exact hp
theorem transportAlong_scale (hA : PreservesAtLevel hL hj i)
    (U : Edge L k i → Matrices.ComplexMatrix2) (l : Edge L k (i + 1)) :
    transportAlong (transportTotal (scaleEdge hL hj i) U) (scaleEdge hL hj (i + 1) l) =
      transportAlong U l := by
  unfold transportAlong
  rw [← map_axisPath hA l, linkHolonomy_map]
theorem crossingDefect_scale (hA : PreservesAtLevel hL hj i)
    (hB : PreservesAtLevel hL hj (i + 1)) (U : Edge L k i → Matrices.ComplexMatrix2)
    (l : Edge L k (i + 1)) {q : Vertex L k i}
    (hq : q ∈ cubeVertices L (meshAt L k i) l.initial) :
    crossingDefect L (transportTotal (scaleEdge hL hj i) U)
        (scaleEdge hL hj (i + 1) l) (scaleVertex hL hj i q) =
      crossingDefect L U l q := by
  unfold crossingDefect
  rw [transportAlong_scale hA, ← map_crossingPath hA, linkHolonomy_map, ← scaleVertex_shifted]
  have h₁ := complexContourMean_scale hB U hq
  have h₂ := complexContourMean_scale hB U (shifted_mem_cubeVertices hL l hq)
  have hi : (scaleEdge hL hj (i + 1) l).initial = scaleVertex hL hj (i + 1) l.initial := rfl
  have ht : (scaleEdge hL hj (i + 1) l).terminal = scaleVertex hL hj (i + 1) l.terminal := rfl
  rw [hi, ht, h₁, h₂]
theorem isPositivelyOriented_scaleEdge {l : Edge L k (i + 1)} (hl : l.IsPositivelyOriented) :
    (scaleEdge hL hj (i + 1) l).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hl
  refine ⟨μ, ?_⟩
  show scaleVertex hL hj (i + 1) l.terminal - scaleVertex hL hj (i + 1) l.initial = _
  rw [← map_sub, h, scaleVertex_axisStep]
theorem preservesValuesAtStep (hS : PreservesSetsAtStep hL hj i) (hA : PreservesAtLevel hL hj i)
    (hB : PreservesAtLevel hL hj (i + 1)) : PreservesValuesAtStep hL hj i where
  mem_complexDomain_iff := fun l U => by
    have hfield : IsFieldOn PeriodicLattice.complexGaugeGroup
          (doubleCubeLinks L (meshAt L k i) l) U ↔
        IsFieldOn PeriodicLattice.complexGaugeGroup
          (doubleCubeLinks L (meshAt L j i) (scaleEdge hL hj (i + 1) l))
          (transportTotal (scaleEdge hL hj i) U) := by
      rw [← hS.doubleCubeLinks_image l]
      exact isFieldOn_iff_image _ (scaleEdge_opposite hL hj) _ _ U
    have hdiam : ∀ p : Vertex L k (i + 1),
        (∀ q ∈ cubeVertices L (meshAt L k i) p,
          Matrices.ComplexMatrix2.familyDiameter (contourHolonomies L U p q) <
            Averaging.centreOfMassDiameter) ↔
        ∀ q ∈ cubeVertices L (meshAt L j i) (scaleVertex hL hj (i + 1) p),
          Matrices.ComplexMatrix2.familyDiameter
            (contourHolonomies L (transportTotal (scaleEdge hL hj i) U)
              (scaleVertex hL hj (i + 1) p) q) < Averaging.centreOfMassDiameter := fun p =>
      forall_cubeVertices_iff hB p fun q hq => by
        rw [familyDiameter_contourHolonomies_eq hB U hq]
    have hdefect : (∀ q ∈ cubeVertices L (meshAt L k i) l.initial,
          Matrices.ComplexMatrix2.operatorNorm (crossingDefect L U l q - 1) < 1) ↔
        ∀ q ∈ cubeVertices L (meshAt L j i) (scaleVertex hL hj (i + 1) l.initial),
          Matrices.ComplexMatrix2.operatorNorm
            (crossingDefect L (transportTotal (scaleEdge hL hj i) U)
              (scaleEdge hL hj (i + 1) l) q - 1) < 1 :=
      forall_cubeVertices_iff hB l.initial fun q hq => by
        rw [crossingDefect_scale hA hB U l hq]
    exact and_congr (and_congr hfield (and_congr (hdiam l.initial) (hdiam l.terminal))) hdefect
  contourAverage_eq := fun _ _ A hq => contourAverage_scale hB A hq
  linearSmoothing_eq := fun A => by
    funext l'
    obtain ⟨l, rfl⟩ := (scaleEdge hL hj (i + 1)).surjective l'
    rw [transportTotal_apply]
    unfold linearSmoothing
    congr 1
    refine finsum_mem_eq_of_bijOn (scaleVertex hL hj i) (bijOn_cubeVertices hB l.initial) ?_
    intro q hq
    have h₁ := contourAverage_scale hB A hq
    have h₂ := contourAverage_scale hB A (shifted_mem_cubeVertices hL l hq)
    have hi : (scaleEdge hL hj (i + 1) l).initial = scaleVertex hL hj (i + 1) l.initial := rfl
    have ht : (scaleEdge hL hj (i + 1) l).terminal = scaleVertex hL hj (i + 1) l.terminal := rfl
    rw [← map_crossingPath hA, sumAlong_map, ← scaleVertex_shifted, hi, ht, h₁, h₂]
  complexContourMean_eq := fun _ _ U hq _ _ => complexContourMean_scale hB U hq
  complexSmoothing_eq := fun l U hl _ => by
    have hl' := isPositivelyOriented_scaleEdge (hL := hL) (hj := hj) hl
    simp only [complexSmoothing, if_pos hl, if_pos hl', complexSmoothingPositive]
    rw [transportAlong_scale hA]
    congr 3
    refine (finsum_mem_eq_of_bijOn (scaleVertex hL hj i) (bijOn_cubeVertices hB l.initial) ?_).symm
    intro q hq
    rw [crossingDefect_scale hA hB U l hq]
end Scaling
end YangMills.Construction.Tower.FullSpace.ScalingOfValues
namespace YangMills.Construction.Tower
theorem fullSpaceScalingPreservesValues_holds
    (hSets : FullSpaceScalingPreservesStepSets.Statement)
    (hLevel : ScalingPreservesObjectsAtLevel.Statement) :
    FullSpaceScalingPreservesValues :=
  fun L hL hs k j hj h₁ i hi =>
    FullSpace.ScalingOfValues.preservesValuesAtStep (hSets L hL hs k j hj h₁ i hi)
      (hLevel L hL hs k j hj h₁ i hi.le).2 (hLevel L hL hs k j hj h₁ (i + 1) hi).2
end YangMills.Construction.Tower
end
