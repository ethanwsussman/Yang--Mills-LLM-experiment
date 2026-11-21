import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPathsProof
import YangMills.Construction.Towers.ContourFamiliesAtTheSideInfinity
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StaircaseContours
open InfiniteLattice (AmbientSpace)
variable {a a' : ℝ}
theorem isLinkPath_cons {b : InfiniteLattice.Link a'} {Γ : List (InfiniteLattice.Link a')}
    {r : AmbientSpace} (hΓ : IsLinkPath Γ) (hr : LinksJoin (b.terminal : AmbientSpace) r Γ) :
    IsLinkPath (b :: Γ) := by
  cases Γ with
  | nil => exact List.isChain_singleton b
  | cons c Γ => exact List.isChain_cons_cons.2 ⟨Subtype.ext hr.1.symm, hΓ⟩
theorem linksJoin_append {Γ Γ' : List (InfiniteLattice.Link a')} {p q r : AmbientSpace}
    (hΓ : IsLinkPath Γ) (hpq : LinksJoin p q Γ) (hΓ' : IsLinkPath Γ') (hqr : LinksJoin q r Γ') :
    IsLinkPath (Γ ++ Γ') ∧ LinksJoin p r (Γ ++ Γ') := by
  induction Γ generalizing p with
  | nil =>
    have h : p = q := hpq
    subst h
    exact ⟨hΓ', hqr⟩
  | cons b Γ ih =>
    obtain ⟨h1, h2⟩ := hpq
    obtain ⟨h3, h4⟩ := ih (List.IsChain.tail hΓ) h2
    exact ⟨isLinkPath_cons h3 h4, h1, h4⟩
theorem forwardSteps_linksJoin (x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℕ) :
    IsLinkPath (forwardSteps x μ n) ∧
      LinksJoin (x : AmbientSpace) ((x + (n : ℤ) • InfiniteLattice.axisStep a' μ :
        InfiniteLattice.LatticePoint a') : AmbientSpace) (forwardSteps x μ n) := by
  induction n generalizing x with
  | zero =>
    refine ⟨List.isChain_nil, ?_⟩
    simp [forwardSteps, LinksJoin]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (x + InfiniteLattice.axisStep a' μ)
    have e : x + InfiniteLattice.axisStep a' μ + (n : ℤ) • InfiniteLattice.axisStep a' μ =
        x + ((n + 1 : ℕ) : ℤ) • InfiniteLattice.axisStep a' μ := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e] at h2
    exact ⟨isLinkPath_cons (b := InfiniteLattice.Link.forwardFrom x μ) h1 h2, rfl, h2⟩
theorem backwardSteps_linksJoin (x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℕ) :
    IsLinkPath (backwardSteps x μ n) ∧
      LinksJoin (x : AmbientSpace) ((x + (-(n : ℤ)) • InfiniteLattice.axisStep a' μ :
        InfiniteLattice.LatticePoint a') : AmbientSpace) (backwardSteps x μ n) := by
  induction n generalizing x with
  | zero =>
    refine ⟨List.isChain_nil, ?_⟩
    simp [backwardSteps, LinksJoin]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (x - InfiniteLattice.axisStep a' μ)
    have e : x - InfiniteLattice.axisStep a' μ + (-(n : ℤ)) • InfiniteLattice.axisStep a' μ =
        x + (-((n + 1 : ℕ) : ℤ)) • InfiniteLattice.axisStep a' μ := by
      push_cast
      rw [neg_add, add_smul, neg_smul, neg_smul, one_smul]
      abel
    rw [e] at h2
    exact ⟨isLinkPath_cons (b := backwardLink x μ) h1 h2, rfl, h2⟩
theorem signedSteps_linksJoin (x : InfiniteLattice.LatticePoint a') (μ : Fin 4) (n : ℤ) :
    IsLinkPath (signedSteps x μ n) ∧
      LinksJoin (x : AmbientSpace) ((x + n • InfiniteLattice.axisStep a' μ :
        InfiniteLattice.LatticePoint a') : AmbientSpace) (signedSteps x μ n) := by
  unfold signedSteps
  split_ifs with h
  · have h' := forwardSteps_linksJoin x μ n.toNat
    rwa [Int.toNat_of_nonneg h] at h'
  · have h' := backwardSteps_linksJoin x μ (-n).toNat
    rwa [Int.toNat_of_nonneg (by omega), neg_neg] at h'
theorem stepsInOrder_linksJoin (ν : Fin 4 → ℤ) (l : List (Fin 4))
    (x : InfiniteLattice.LatticePoint a') :
    IsLinkPath (stepsInOrder ν x l) ∧
      LinksJoin (x : AmbientSpace) ((x + (l.map fun μ => ν μ • InfiniteLattice.axisStep a' μ).sum :
        InfiniteLattice.LatticePoint a') : AmbientSpace) (stepsInOrder ν x l) := by
  induction l generalizing x with
  | nil =>
    refine ⟨List.isChain_nil, ?_⟩
    simp [stepsInOrder, LinksJoin]
  | cons μ l ih =>
    obtain ⟨h1, h2⟩ := signedSteps_linksJoin x μ (ν μ)
    obtain ⟨h3, h4⟩ := ih (x + ν μ • InfiniteLattice.axisStep a' μ)
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact linksJoin_append h1 h2 h3 h4
theorem sum_map_supportAxes_equiv (ν : Fin 4 → ℤ)
    (σ : Fin (supportAxes ν).card ≃ supportAxes ν) :
    (((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4)).map
      fun μ => ν μ • InfiniteLattice.axisStep a' μ).sum =
        ∑ μ, ν μ • InfiniteLattice.axisStep a' μ := by
  rw [List.map_map]
  have h := Fin.sum_univ_def fun i =>
    (fun μ => ν μ • InfiniteLattice.axisStep a' μ) ((σ i : supportAxes ν) : Fin 4)
  refine h.symm.trans ?_
  rw [Equiv.sum_comp σ (fun s : supportAxes ν =>
      ν (s : Fin 4) • InfiniteLattice.axisStep a' (s : Fin 4)),
    Finset.sum_coe_sort (supportAxes ν) (fun μ => ν μ • InfiniteLattice.axisStep a' μ)]
  unfold supportAxes
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h0
  · rfl
  · simp [not_not.1 h0]
theorem coe_sum_axisStep (ν : Fin 4 → ℤ) :
    ((∑ μ, ν μ • InfiniteLattice.axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      ∑ μ, Pi.single μ ((ν μ : ℝ) * a') := by
  rw [AddSubgroup.val_finsetSum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ext ρ
  by_cases h : ρ = μ
  · subst h
    simp [InfiniteLattice.axisStep]
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h]
theorem offset_injective (ha : a' ≠ 0) {ν ν' : Fin 4 → ℤ}
    (h : (∑ μ, Pi.single μ ((ν μ : ℝ) * a') : AmbientSpace) =
      ∑ μ, Pi.single μ ((ν' μ : ℝ) * a')) :
    ν = ν' := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coordVec_injective <;> assumption
theorem coe_toFiner {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem stepsInOrder_isStaircasePath {L : ℕ} {ν : Fin 4 → ℤ} {y : InfiniteLattice.LatticePoint a}
    {s : InfiniteLattice.LatticePoint a'}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a')
    (hν : IsCubeOffset L y s ν) (σ : Fin (supportAxes ν).card ≃ supportAxes ν) :
    IsStaircasePath ν y s σ (stepsInOrder ν (toFiner a' y)
      ((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4))) := by
  obtain ⟨h1, h2⟩ := stepsInOrder_linksJoin ν
    ((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4)) (toFiner a' y)
  rw [sum_map_supportAxes_equiv] at h2
  have e : ((toFiner a' y + ∑ μ, ν μ • InfiniteLattice.axisStep a' μ :
      InfiniteLattice.LatticePoint a') : AmbientSpace) = s := by
    rw [AddSubgroup.coe_add, coe_toFiner hy, coe_sum_axisStep, ← hν.1]
    abel
  rw [e, coe_toFiner hy] at h2
  exact ⟨h1, h2, toFiner a' y, coe_toFiner hy, rfl⟩
theorem eq_stepsInOrder_of_isStaircasePath {ν : Fin 4 → ℤ} {y : InfiniteLattice.LatticePoint a}
    {s : InfiniteLattice.LatticePoint a'}
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a')
    {σ : Fin (supportAxes ν).card ≃ supportAxes ν}
    {Γ : List (InfiniteLattice.Link a')} (h : IsStaircasePath ν y s σ Γ) :
    Γ = stepsInOrder ν (toFiner a' y)
      ((List.finRange _).map fun i => ((σ i : supportAxes ν) : Fin 4)) := by
  obtain ⟨-, -, y', hy', rfl⟩ := h
  have e : y' = toFiner a' y := Subtype.ext (hy'.trans (coe_toFiner hy).symm)
  rw [e]
theorem staircaseFamily_of_isCubeOffset {L : ℕ} {ν : Fin 4 → ℤ}
    {y : InfiniteLattice.LatticePoint a} {s : InfiniteLattice.LatticePoint a'} (ha : a' ≠ 0)
    (hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a')
    (hν : IsCubeOffset L y s ν) :
    (∃! 𝒢, IsStaircaseFamily L y s 𝒢) ∧ IsStaircaseFamily L y s (contourSet L y s) ∧
      (∀ Γ ∈ contourSet L y s, IsLinkPath Γ) ∧ (contourSet L y s).Nonempty ∧
      (contourSet L y s).Finite := by
  have h₀ : IsCubeOffset L y s (cubeOffset L y s) :=
    Classical.epsilon_spec (p := IsCubeOffset L y s) ⟨ν, hν⟩
  have hone : ∀ ν', IsCubeOffset L y s ν' → ν' = cubeOffset L y s :=
    fun ν' h => offset_injective ha (h.1.symm.trans h₀.1)
  have hset : contourSet L y s =
      {Γ | ∃ σ, IsStaircasePath (cubeOffset L y s) y s σ Γ} := by
    ext Γ
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨σ, stepsInOrder_isStaircasePath hy h₀ σ⟩
    · rintro ⟨σ, h⟩
      exact ⟨σ, (eq_stepsInOrder_of_isStaircasePath hy h).symm⟩
  have hfam : IsStaircaseFamily L y s (contourSet L y s) :=
    ⟨_, h₀, fun σ => ⟨_, stepsInOrder_isStaircasePath hy h₀ σ,
      fun _ h => eq_stepsInOrder_of_isStaircasePath hy h⟩, hset⟩
  refine ⟨⟨_, hfam, ?_⟩, hfam, ?_, ?_, Set.finite_range _⟩
  · rintro 𝒢 ⟨ν', h, -, rfl⟩
    rw [hone ν' h, hset]
  · intro Γ hΓ
    rw [hset] at hΓ
    obtain ⟨σ, h⟩ := hΓ
    exact h.1
  · exact ⟨_, (offsetSupport L y s).equivFin.symm, rfl⟩
theorem staircaseContoursWellDefined_holds : StaircaseContoursWellDefined := by
  intro L k j hL hk hj hjk y x hx
  have hL0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  have ha : meshAt L k (j - 1) ≠ 0 := zpow_ne_zero _ hL0
  have hmul : meshAt L k j = L * meshAt L k (j - 1) := by
    unfold meshAt
    rw [← zpow_one_add₀ hL0]
    congr 1
    omega
  have hy : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by
    obtain ⟨n, hn⟩ := y.2
    refine ⟨fun μ => n μ * L, fun μ => ?_⟩
    rw [hn μ, hmul]
    push_cast
    ring
  obtain ⟨ν, hν, rfl⟩ := hx
  have hsum : (∑ μ, Pi.single μ ((ν μ : ℝ) * meshAt L k (j - 1)) : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by
    rw [← coe_sum_axisStep]
    exact SetLike.coe_mem _
  refine ⟨⟨_, add_mem hy hsum⟩, rfl, ?_⟩
  refine staircaseFamily_of_isCubeOffset (ν := ν) ha hy ⟨?_, ?_⟩
  · simp
  · simpa using hν
end YangMills.Construction.Tower.FullSpace.StaircaseContours
end
