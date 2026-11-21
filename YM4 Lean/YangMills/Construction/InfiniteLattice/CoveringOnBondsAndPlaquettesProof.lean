import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtensionProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set InfiniteLattice InfiniteLattice.PeriodicExtensions
noncomputable section
namespace InfiniteLattice.Covering
section Points
variable {L m : ℕ} {j : ℤ}
theorem projectPoint_add (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem projectPoint_eq_iff (x x' : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j x = projectPoint L m j x' ↔
      (x : AmbientSpace) - (x' : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_eq_iff <;> assumption
theorem projectLink_forwardFrom (x : LatticePoint (PeriodicLattice.meshSize L j)) (κ : Fin 4) :
    projectLink L m j (Link.forwardFrom x κ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint L m j x) κ := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectLink_forwardFrom <;> assumption
end Points
theorem exists_eq_forwardFrom_of_isPositivelyOriented {a : ℝ} {b : Link a}
    (hb : b.IsPositivelyOriented) : ∃ μ, b = Link.forwardFrom b.initial μ := by
  obtain ⟨μ, hμ⟩ := hb
  refine ⟨μ, Link.ext rfl ?_⟩
  show b.terminal = b.initial + axisStep a μ
  rw [← hμ]
  abel
theorem one_lt_factor {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : (1 : ℝ) < L := by
  have h : 1 < L := by
    have := hL.2
    omega
  exact_mod_cast h
theorem torusSide_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (m : ℕ) :
    0 < PeriodicLattice.torusSide L m := by
  have h := one_lt_factor hL
  unfold PeriodicLattice.torusSide
  exact mul_pos two_pos (pow_pos (by linarith) _)
theorem unitStep_injective (hA : QuotientLattices.TorusAndSpaceLatticeProperties) {L m K : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep L m (K : ℤ) μ = PeriodicLattice.unitStep L m (K : ℤ) ν) :
    μ = ν := by
  obtain ⟨-, -, -, -, -, hN, -⟩ := hA L hL m 0 K hm (Nat.zero_le K)
  have hi : QuotientLattices.refinementIndex K 0 = (K : ℤ) := by
    simp [QuotientLattices.refinementIndex]
  have hs : ∀ κ, QuotientLattices.torusAxisSteps L m K 0 κ =
      (PeriodicLattice.unitStep L m (K : ℤ) κ : PeriodicLattice.FourTorus L m) := by
    intro κ
    unfold QuotientLattices.torusAxisSteps
    rw [hi]
  have e := hN.2.1 (a₁ := some (1, μ)) (a₂ := some (1, ν))
    (by simp [QuotientLattices.unitStepsWithZero, hs, h])
  simpa using e
theorem axis_eq_and_projectPoint_eq (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L m K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m)
    {x x' : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))} {μ μ' : Fin 4}
    (h : projectLink L m (K : ℤ) (Link.forwardFrom x μ) =
      projectLink L m (K : ℤ) (Link.forwardFrom x' μ')) :
    μ = μ' ∧ projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) x' := by
  rw [projectLink_forwardFrom, projectLink_forwardFrom] at h
  have ht : projectPoint L m (K : ℤ) x = projectPoint L m (K : ℤ) x' :=
    congrArg PeriodicLattice.Bond.source h
  have hh : projectPoint L m (K : ℤ) x + PeriodicLattice.unitStep L m (K : ℤ) μ =
      projectPoint L m (K : ℤ) x' + PeriodicLattice.unitStep L m (K : ℤ) μ' :=
    congrArg PeriodicLattice.Bond.target h
  rw [ht] at hh
  exact ⟨unitStep_injective hA hL hm (add_left_cancel hh), ht⟩
theorem projectsPlaquetteEdges_holds (L m K : ℕ) : ProjectsPlaquetteEdges L m K := by apply _root_.YangMills.Construction.PeriodicExtension.projectsPlaquetteEdges_of <;> assumption
theorem faceEnergyOfLift_holds (L m K : ℕ) : FaceEnergyOfLift L m K := by apply _root_.YangMills.Construction.PeriodicExtension.faceEnergyOfLift_of <;> assumption
theorem periodLattice_le_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L m K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) :
    PeriodLattice_le L m K := by apply _root_.YangMills.Construction.PeriodicExtension.periodLattice_le_of <;> assumption
theorem projectLink_translateLink {L m K : ℕ} (b : Link (CutoffLattice.spacingAt L K))
    (v : LatticePoint (CutoffLattice.spacingAt L K))
    (hv : (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m)) :
    projectLink L m (K : ℤ) (CutoffLattice.translateLink b v) = projectLink L m (K : ℤ) b := by
  have e : ∀ x : LatticePoint (CutoffLattice.spacingAt L K),
      projectPoint L m (K : ℤ) (x + v) = projectPoint L m (K : ℤ) x := fun x =>
    (projectPoint_eq_iff _ _).mpr (by simpa using hv)
  exact PeriodicLattice.Bond.ext (e _) (e _)
theorem projectInvariantUnderPeriods_holds (L m K : ℕ) :
    ProjectInvariantUnderPeriods L m K := by
  intro b v hv
  have h := projectLink_translateLink b v hv
  exact ⟨h, fun U => by rw [liftCompactField_apply, liftCompactField_apply, h]⟩
theorem sameProjectionDifferByPeriod_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L m K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) :
    SameProjectionDifferByPeriod L m K := by
  rintro _ ⟨x, κ, rfl⟩ _ ⟨x', ρ, rfl⟩ h
  obtain ⟨rfl, hs⟩ := axis_eq_and_projectPoint_eq hA hL hm h
  refine ⟨x' - x, (projectPoint_eq_iff x' x).mp hs.symm, Link.ext ?_ ?_⟩
  · show x' = x + (x' - x)
    abel
  · show x' + axisStep _ κ = x + axisStep _ κ + (x' - x)
    abel
theorem latticeSubgroup_torusSide_antitone {L n n' : ℕ} (hle : n ≤ n') :
    latticeSubgroup (PeriodicLattice.torusSide L n') ≤
      latticeSubgroup (PeriodicLattice.torusSide L n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
  rintro x ⟨k, hk⟩
  refine ⟨fun μ => k μ * (L : ℤ) ^ r, fun μ => ?_⟩
  rw [hk μ]
  simp only [PeriodicLattice.torusSide]
  push_cast
  ring
theorem le_of_torusSide_le {L n n' : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (h : PeriodicLattice.torusSide L n ≤ PeriodicLattice.torusSide L n') : n ≤ n' := by
  simp only [PeriodicLattice.torusSide] at h
  exact (pow_le_pow_iff_right₀ (one_lt_factor hL)).mp (by linarith)
theorem translateLink_eq_self_of_small {L K n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (b : Link (CutoffLattice.spacingAt L K)) (v : LatticePoint (CutoffLattice.spacingAt L K))
    (hv : (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L n))
    (hsmall : ∀ μ, |(v : AmbientSpace) μ| < PeriodicLattice.torusSide L n) :
    CutoffLattice.translateLink b v = b := by
  obtain ⟨k, hk⟩ := hv
  have hpos := torusSide_pos hL n
  have hzero : ∀ μ, (v : AmbientSpace) μ = 0 := by
    intro μ
    by_contra hne
    have hk0 : k μ ≠ 0 := by
      intro h0
      exact hne (by rw [hk μ, h0]; simp)
    have h1 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
      have : 1 ≤ |k μ| := Int.one_le_abs hk0
      exact_mod_cast this
    have h2 := hsmall μ
    rw [hk μ, abs_mul, abs_of_pos hpos] at h2
    nlinarith
  have hv0 : v = 0 := Subtype.ext (funext hzero)
  subst hv0
  exact Link.ext (add_zero _) (add_zero _)
theorem exists_initial_bound {a : ℝ} {S : Set (Link a)} (hS : S.Finite) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ b ∈ S, ∀ μ, |(b.initial : AmbientSpace) μ| ≤ r := by
  obtain ⟨r, hr⟩ := (hS.image fun b : Link a => ∑ μ, |(b.initial : AmbientSpace) μ|).bddAbove
  refine ⟨max r 0, le_max_right _ _, fun b hb μ => ?_⟩
  have h1 : ∑ ν, |(b.initial : AmbientSpace) ν| ≤ r := hr (mem_image_of_mem _ hb)
  have h2 : |(b.initial : AmbientSpace) μ| ≤ ∑ ν, |(b.initial : AmbientSpace) ν| :=
    Finset.single_le_sum (f := fun ν => |(b.initial : AmbientSpace) ν|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ μ)
  exact (h2.trans h1).trans (le_max_left _ _)
theorem eventuallyInjective_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : EventuallyInjective L K := by
  intro S hS hfin
  have hL1 := one_lt_factor hL
  constructor
  · obtain ⟨r, hr0, hr⟩ := exists_initial_bound hfin
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r hL1
    have hbig : 2 * r < PeriodicLattice.torusSide L (n + 1) := by
      have : (L : ℝ) ^ n ≤ (L : ℝ) ^ (n + 1) := pow_le_pow_right₀ hL1.le (Nat.le_succ n)
      simp only [PeriodicLattice.torusSide]
      linarith
    refine ⟨_, n + 1, Nat.succ_pos n, rfl, fun b hb b' hb' h => ?_⟩
    obtain ⟨v, hv, rfl⟩ :=
      sameProjectionDifferByPeriod_holds hA hL (Nat.succ_pos n) b (hS hb) b' (hS hb') h
    refine (translateLink_eq_self_of_small hL b v hv fun μ => ?_).symm
    have h1 := hr _ hb' μ
    have h2 := hr _ hb μ
    have h3 : ((CutoffLattice.translateLink b v).initial : AmbientSpace) μ =
        (b.initial : AmbientSpace) μ + (v : AmbientSpace) μ := rfl
    rw [h3] at h1
    have h4 : |(v : AmbientSpace) μ| ≤
        |(b.initial : AmbientSpace) μ + (v : AmbientSpace) μ| + |(b.initial : AmbientSpace) μ| := by
      have := abs_sub ((b.initial : AmbientSpace) μ + (v : AmbientSpace) μ)
        ((b.initial : AmbientSpace) μ)
      simpa using this
    linarith
  · rintro _ ⟨n, hn, rfl, hinj⟩ _ ⟨n', hn', rfl⟩ hle
    refine ⟨n', hn', rfl, fun b hb b' hb' h => ?_⟩
    obtain ⟨v, hv, rfl⟩ := sameProjectionDifferByPeriod_holds hA hL hn' b (hS hb) b' (hS hb') h
    exact hinj hb hb'
      (projectLink_translateLink b v
        (latticeSubgroup_torusSide_antitone (le_of_torusSide_le hL hle) hv)).symm
section Windows
variable {L K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
theorem mem_links_union_rim {p : ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ))}
    (hp : p ∈ W.faces) {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b ∈ p.edges) :
    b ∈ (W.links : Set _) ∪ W.rim := by
  by_cases h : b ∈ W.links
  · exact Or.inl h
  · exact Or.inr ⟨⟨p, hp, hb⟩, h⟩
theorem links_union_rim_subset :
    (W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim ⊆
      CutoffLattice.positiveLinksAt L K := by
  rintro b (hb | ⟨⟨p, -, hb⟩, -⟩)
  · obtain ⟨μ, hμ⟩ := exists_eq_forwardFrom_of_isPositivelyOriented (W.isPositive b hb)
    exact ⟨_, μ, hμ⟩
  · simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
theorem links_union_rim_finite :
    ((W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim).Finite := by
  refine W.links.finite_toSet.union ?_
  have hP : W.faces.Finite := WilsonOperator.facesTouching_finite W.links
  refine (hP.biUnion fun p _ => List.finite_toSet p.edges).subset ?_
  rintro b ⟨⟨p, hp, hb⟩, -⟩
  exact mem_biUnion hp hb
theorem leastTorusSideIsAttained_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : LeastTorusSideIsAttained W := by
  classical
  have hI := eventuallyInjective_holds (K := K) hA hL _ (links_union_rim_subset W)
    (links_union_rim_finite W)
  have hE : W.torusSidesOfInjection =
      injectiveSides L K ((W.links : Set (Link (PeriodicLattice.meshSize L (K : ℤ)))) ∪ W.rim) :=
    rfl
  have hne : W.torusSidesOfInjection.Nonempty := hE ▸ hI.1
  have hex : ∃ n : ℕ, 0 < n ∧ W.InjectsIntoTorus n := by
    obtain ⟨_, n, hn, -, he⟩ := hne
    exact ⟨n, hn, he⟩
  obtain ⟨h0, h1⟩ := Nat.find_spec hex
  have hleast : IsLeast W.torusSidesOfInjection (PeriodicLattice.torusSide L (Nat.find hex)) := by
    refine ⟨⟨_, h0, rfl, h1⟩, ?_⟩
    rintro _ ⟨n, hn, rfl, he⟩
    have hle : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn, he⟩
    have hL1 := one_lt_factor hL
    simp only [PeriodicLattice.torusSide]
    have := pow_le_pow_right₀ hL1.le hle
    linarith
  have hval : W.leastTorusSide =
      ((PeriodicLattice.torusSide L (Nat.find hex) : ℝ) : EReal) := by
    unfold LinkWindow.leastTorusSide
    rw [if_pos hne, hleast.csInf_eq]
  refine ⟨⟨_, ⟨_, h0, rfl⟩, hval⟩, ?_⟩
  ext s
  constructor
  · intro h
    obtain ⟨n, hn, rfl, -⟩ := id h
    refine ⟨⟨n, hn, rfl⟩, ?_⟩
    rw [hval]
    exact EReal.coe_le_coe_iff.mpr (hleast.2 h)
  · rintro ⟨hs, hle⟩
    rw [hval] at hle
    rw [hE]
    exact hI.2 _ (hE ▸ hleast.1) s hs (EReal.coe_le_coe_iff.mp hle)
theorem injectsIntoTorus_of_le (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {m : ℕ} (hm : 0 < m)
    (h : W.leastTorusSide ≤ ((PeriodicLattice.torusSide L m : ℝ) : EReal)) :
    W.InjectsIntoTorus m := by
  have hmem : PeriodicLattice.torusSide L m ∈ W.torusSidesOfInjection := by
    rw [(leastTorusSideIsAttained_holds W hA hL).2]
    exact ⟨⟨m, hm, rfl⟩, h⟩
  obtain ⟨n, -, hs, he⟩ := hmem
  have hnm : n = m := le_antisymm (le_of_torusSide_le hL hs.le) (le_of_torusSide_le hL hs.ge)
  exact hnm ▸ he
end Windows
section Faithful
variable {L m K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
theorem exists_lift_of_mem_links (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m)
    {b : Link (PeriodicLattice.meshSize L (K : ℤ))} (hb : b ∈ W.links)
    (y : PeriodicLattice.Site L m (K : ℤ)) (w : LatticePoint (PeriodicLattice.meshSize L (K : ℤ)))
    (ρ : Fin 4)
    (h : projectLink L m (K : ℤ) b =
      PeriodicLattice.Bond.forwardFrom (y + projectPoint L m (K : ℤ) w) ρ) :
    ∃ x, projectPoint L m (K : ℤ) x = y ∧ b = Link.forwardFrom (x + w) ρ := by
  obtain ⟨μ, hμ⟩ := exists_eq_forwardFrom_of_isPositivelyOriented (W.isPositive b hb)
  have hc : ∃ z, projectPoint L m (K : ℤ) z = y := by
    obtain ⟨u, n, hn⟩ := y
    refine ⟨⟨fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L (K : ℤ), n, fun _ => rfl⟩, ?_⟩
    refine Subtype.ext (funext fun μ => ?_)
    simp [projectPoint, TorusMetric.torusProj, hn]
  obtain ⟨z, rfl⟩ := hc
  have h' : projectLink L m (K : ℤ) (Link.forwardFrom b.initial μ) =
      projectLink L m (K : ℤ) (Link.forwardFrom (z + w) ρ) := by
    rw [← hμ, h, projectLink_forwardFrom, projectPoint_add]
  obtain ⟨rfl, hs⟩ := axis_eq_and_projectPoint_eq hA hL hm h'
  refine ⟨b.initial - w, ?_, ?_⟩
  · rw [projectPoint_sub, hs, projectPoint_add]
    abel
  · rw [sub_add_cancel]
    exact hμ
theorem windowProjectsFaithfully_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 1 ≤ m) :
    WindowProjectsFaithfully L m K W := by
  intro hemb
  have hfour := projectsPlaquetteEdges_holds L m K
  refine ⟨Set.BijOn.mk ?_ ?_ ?_, ?_⟩
  · rintro p ⟨b, hb, hW⟩
    obtain ⟨h1, h2, h3, h4⟩ := hfour p
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, hW, h1⟩
    · exact Or.inr (Or.inl ⟨_, hW, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, hW, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨_, hW, h4⟩))
  · intro p hp p' hp' h
    have hf : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis h
    have hs : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis h
    have e1 : projectLink L m (K : ℤ) (firstEdge p) = projectLink L m (K : ℤ) (firstEdge p') := by
      rw [(hfour p).1, (hfour p').1, h]
    have hb : firstEdge p ∈ p.edges := by simp [firstEdge, ElementaryPlaquette.edges]
    have hb' : firstEdge p' ∈ p'.edges := by simp [firstEdge, ElementaryPlaquette.edges]
    have e2 := hemb (mem_links_union_rim W hp hb) (mem_links_union_rim W hp' hb') e1
    have hcorner : p.corner = p'.corner := congrArg Link.initial e2
    exact ElementaryPlaquette.ext hcorner hf hs
  · rintro P (⟨b, hb, h⟩ | ⟨b, hb, h⟩ | ⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    · obtain ⟨x, hx, hbx⟩ := exists_lift_of_mem_links W hA hL hm hb P.origin 0 P.firstAxis
        (by rw [h, ← sub_self (0 : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))),
          projectPoint_sub, sub_self, add_zero]; rfl)
      rw [add_zero] at hbx
      refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hb⟩, ?_⟩
      · rw [hbx]
        simp [ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hx rfl rfl
    · obtain ⟨x, hx, hbx⟩ := exists_lift_of_mem_links W hA hL hm hb P.origin
        (axisStep _ P.firstAxis) P.secondAxis (by rw [h, projectPoint_axisStep]; rfl)
      refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hb⟩, ?_⟩
      · rw [hbx]
        simp [ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hx rfl rfl
    · obtain ⟨x, hx, hbx⟩ := exists_lift_of_mem_links W hA hL hm hb P.origin
        (axisStep _ P.secondAxis) P.firstAxis (by rw [h, projectPoint_axisStep]; rfl)
      refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hb⟩, ?_⟩
      · rw [hbx]
        simp [ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hx rfl rfl
    · obtain ⟨x, hx, hbx⟩ := exists_lift_of_mem_links W hA hL hm hb P.origin 0 P.secondAxis
        (by rw [h, ← sub_self (0 : LatticePoint (PeriodicLattice.meshSize L (K : ℤ))),
          projectPoint_sub, sub_self, add_zero]; rfl)
      rw [add_zero] at hbx
      refine ⟨⟨x, P.firstAxis, P.secondAxis, P.firstAxis_lt_secondAxis⟩, ⟨b, ?_, hb⟩, ?_⟩
      · rw [hbx]
        simp [ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hx rfl rfl
  · refine eq_empty_iff_forall_notMem.mpr ?_
    rintro _ ⟨⟨b, hb, rfl⟩, ⟨b', hb', h⟩⟩
    have e : b' = b := hemb (Or.inr hb') (Or.inl hb) h
    exact hb'.2 (e ▸ hb)
end Faithful
theorem axialTranslatesExit_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    {L m K : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ))) : AxialTranslatesExit L m K W := by
  intro b hb
  have hpos := torusSide_pos hL m
  constructor
  · let f : Link (PeriodicLattice.meshSize L (K : ℤ)) → ℝ := fun b' =>
      ((b'.initial : AmbientSpace) 0 - (b.initial : AmbientSpace) 0) / PeriodicLattice.torusSide L m
    have hfin : ((Int.cast : ℤ → ℝ) ⁻¹' (f '' (W.links : Set _))).Finite :=
      Set.Finite.preimage Int.cast_injective.injOn (W.links.finite_toSet.image f)
    refine hfin.subset ?_
    rintro k ⟨b', hb', v, hv, rfl⟩
    refine ⟨_, hb', ?_⟩
    have h0 : (v : AmbientSpace) 0 = (k : ℝ) * PeriodicLattice.torusSide L m := by
      rw [hv]
      simp
    have h1 : ((CutoffLattice.translateLink b v).initial : AmbientSpace) 0 =
        (b.initial : AmbientSpace) 0 + (v : AmbientSpace) 0 := rfl
    simp only [f]
    rw [h1, h0, add_sub_cancel_left, mul_div_assoc, div_self hpos.ne', mul_one]
  · rintro hle _ ⟨v, hv, rfl⟩ hmem
    have hemb := injectsIntoTorus_of_le W hA hL hm hle
    have hper : (v : AmbientSpace) ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by
      refine ⟨Pi.single 0 1, fun μ => ?_⟩
      rw [hv]
      by_cases h : μ = 0
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have e := hemb (Or.inl hmem) (Or.inl hb) (projectLink_translateLink b v hper)
    have ht : b.initial + v = b.initial := congrArg Link.initial e
    have hv0 : v = 0 := add_left_cancel (ht.trans (add_zero _).symm)
    have h0 : (v : AmbientSpace) 0 = ((1 : ℤ) : ℝ) * PeriodicLattice.torusSide L m := by
      rw [hv]
      simp
    rw [hv0] at h0
    simp at h0
    exact hpos.ne' h0.symm
theorem coveringProperties_of (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    CoveringProperties := by
  intro s
  have hL := s.isAdmissible
  have hm : 1 ≤ (s.m : ℕ) := s.m.pos
  exact ⟨projectsPlaquetteEdges_holds _ _ _, faceEnergyOfLift_holds _ _ _,
    periodLattice_le_holds hA hL hm, projectInvariantUnderPeriods_holds _ _ _,
    sameProjectionDifferByPeriod_holds hA hL hm, eventuallyInjective_holds hA hL, fun W =>
      ⟨windowProjectsFaithfully_holds W hA hL hm, leastTorusSideIsAttained_holds W hA hL,
        axialTranslatesExit_holds hA hL hm W⟩⟩
end InfiniteLattice.Covering
end
end YangMills.Construction
