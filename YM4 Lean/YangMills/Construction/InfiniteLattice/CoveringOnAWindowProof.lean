import YangMills.Construction.InfiniteLattice.CoveringOfTheLatticeOfACutoff
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.CoveringOnAWindow
import YangMills.Construction.InfiniteLattice.PlaquettesAndWindows
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set InfiniteLattice
namespace CutoffLinks
namespace WindowProjection
theorem projectPoint_add (L m : ℕ) (j : ℤ) (x y : LatticePoint (PeriodicLattice.meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem abs_le_supNormVec (r : AmbientSpace) (μ : Fin 4) : |r μ| ≤ PeriodicLattice.supNormVec r :=
  Finset.le_sup' (fun ν => |r ν|) (Finset.mem_univ μ)
variable (d : CutoffData)
theorem one_lt_L : (1 : ℝ) < d.L := by
  have hadm := d.isAdmissible.2
  exact_mod_cast (by omega : 1 < d.L)
theorem side_pos : 0 < d.side := by
  have hgt := one_lt_L d
  have hpow : 0 < (d.L : ℝ) ^ (d.m : ℕ) := pow_pos (by linarith) _
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  linarith
theorem projectPoint_eq_iff (x x' : LatticePoint d.spacing) :
    projectPoint d.L d.m ((d.K : ℕ) : ℤ) x = projectPoint d.L d.m ((d.K : ℕ) : ℤ) x' ↔
      (x : AmbientSpace) - (x' : AmbientSpace) ∈ latticeSubgroup d.side := by
  constructor
  · intro hproj
    have key : ∀ μ, ∃ k : ℤ, k • PeriodicLattice.torusSide d.L d.m =
        (x : AmbientSpace) μ - (x' : AmbientSpace) μ := by
      intro μ
      refine (AddCircle.coe_eq_zero_iff _).mp ?_
      have hcoord := congrFun (congrArg Subtype.val hproj) μ
      have hcirc : (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide d.L d.m)) =
        (((x' : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide d.L d.m)) := hcoord
      rw [AddCircle.coe_sub, hcirc, sub_self]
    choose k hk using key
    refine ⟨k, fun μ => ?_⟩
    have hμ := hk μ
    rw [zsmul_eq_mul] at hμ
    exact hμ.symm
  · rintro ⟨k, hk⟩
    refine Subtype.ext (funext fun μ => ?_)
    show (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide d.L d.m)) =
      (((x' : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide d.L d.m))
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    refine (AddCircle.coe_eq_zero_iff _).mpr ⟨k μ, ?_⟩
    rw [zsmul_eq_mul]
    exact (hk μ).symm
theorem projectPoint_surjective :
    Function.Surjective (projectPoint d.L d.m ((d.K : ℕ) : ℤ)) := by
  rintro ⟨y, k, hk⟩
  refine ⟨⟨fun μ => (k μ : ℝ) * PeriodicLattice.meshSize d.L ((d.K : ℕ) : ℤ), k, fun _ => rfl⟩, ?_⟩
  exact Subtype.ext (funext fun μ => (hk μ).symm)
theorem two_le_L : 2 ≤ d.L := by
  have hadm := d.isAdmissible.2
  omega
theorem neg_m_lt_K : -((d.m : ℕ) : ℤ) < ((d.K : ℕ) : ℤ) := by
  have hK := d.K.pos
  have hm := d.m.pos
  omega
theorem forwardFrom_injective {y y' : d.PeriodicSite} {μ μ' : Fin 4}
    (hfw : (PeriodicLattice.Bond.forwardFrom y μ : d.PeriodicBond) =
      PeriodicLattice.Bond.forwardFrom y' μ') :
    y = y' ∧ μ = μ' := by
  have hsrc : y = y' := congrArg PeriodicLattice.Bond.source hfw
  subst hsrc
  refine ⟨rfl, ?_⟩
  by_contra hne
  have htgt : y + PeriodicLattice.unitStep d.L d.m ((d.K : ℕ) : ℤ) μ =
      y + PeriodicLattice.unitStep d.L d.m ((d.K : ℕ) : ℤ) μ' :=
    congrArg PeriodicLattice.Bond.target hfw
  exact PeriodicLattice.MatrixValued.unitStep_ne_unitStep (two_le_L d) (neg_m_lt_K d) hne
    (add_left_cancel htgt)
theorem projLink_forwardFrom_eq (x : LatticePoint d.spacing) (μ : Fin 4) :
    d.projLink (Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint d.L d.m ((d.K : ℕ) : ℤ) x) μ := by apply _root_.YangMills.Construction.CutoffLinks.CutoffData.projLink_forwardFrom <;> assumption
theorem projLink_forwardFrom_eq_iff (x x' : LatticePoint d.spacing) (μ μ' : Fin 4) :
    d.projLink (Link.forwardFrom x μ) = d.projLink (Link.forwardFrom x' μ') ↔
      μ = μ' ∧ (x : AmbientSpace) - (x' : AmbientSpace) ∈ latticeSubgroup d.side := by
  rw [projLink_forwardFrom_eq, projLink_forwardFrom_eq]
  constructor
  · intro hfw
    obtain ⟨h₁, h₂⟩ := forwardFrom_injective d hfw
    exact ⟨h₂, (projectPoint_eq_iff d x x').mp h₁⟩
  · rintro ⟨rfl, hmem⟩
    rw [(projectPoint_eq_iff d x x').mpr hmem]
theorem image_links : d.projLink '' d.links = d.positiveLinkSet := by
  ext l
  constructor
  · rintro ⟨_, ⟨x, μ, rfl⟩, rfl⟩
    exact ⟨_, μ, projLink_forwardFrom_eq d x μ⟩
  · rintro ⟨y, μ, rfl⟩
    obtain ⟨x, rfl⟩ := projectPoint_surjective d y
    exact ⟨_, ⟨x, μ, rfl⟩, projLink_forwardFrom_eq d x μ⟩
theorem projFace_surjective : Function.Surjective d.projFace := by
  rintro ⟨y, μ, μ', hne⟩
  obtain ⟨x, rfl⟩ := projectPoint_surjective d y
  exact ⟨⟨x, μ, μ', hne⟩, rfl⟩
theorem periodicEdgeList_projFace (p : ElementaryPlaquette d.spacing) :
    WilsonOperator.periodicEdgeList (d.projFace p) = p.edges.map d.projLink := by
  simp only [ElementaryPlaquette.edges, List.map_cons, List.map_nil, projLink_forwardFrom_eq,
    projectPoint_add, projectPoint_axisStep]
  rfl
theorem image_containsLink (p : ElementaryPlaquette d.spacing) :
    d.projLink '' {b | ContainsLink p b} =
      {l | CutoffData.FaceContains (d := d) (d.projFace p) l} := by
  ext l
  simp only [CutoffData.FaceContains, periodicEdgeList_projFace, List.mem_map, mem_image,
    mem_ofPred_eq, ContainsLink]
theorem coe_liftField (U : d.PeriodicFields) (b : Link d.spacing) :
    ((d.liftField U b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      U.1 (d.projLink b) :=
  liftField_apply_of_mem U.2 b
theorem faceHolonomy_liftField (U : d.PeriodicFields) (p : ElementaryPlaquette d.spacing) :
    ((faceHolonomy (d.liftField U) p : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2) =
      PeriodicLattice.plaquetteHolonomy U.1 (d.projFace p) := by
  have hcoe : ∀ (g h k l : Matrices.ComplexMatrix2.specialUnitary),
      ((g * h * k⁻¹ * l⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2) * (h : Matrices.ComplexMatrix2) *
        (k : Matrices.ComplexMatrix2)⁻¹ * (l : Matrices.ComplexMatrix2)⁻¹ := by
    intro g h k l
    rw [← specialUnitary_coe_inv, ← specialUnitary_coe_inv]
    rfl
  have e1 := projLink_forwardFrom_eq d p.corner p.lowAxis
  have e2 := projLink_forwardFrom_eq d (p.corner + axisStep d.spacing p.lowAxis) p.highAxis
  have e3 := projLink_forwardFrom_eq d (p.corner + axisStep d.spacing p.highAxis) p.lowAxis
  have e4 := projLink_forwardFrom_eq d p.corner p.highAxis
  rw [projectPoint_add, projectPoint_axisStep] at e2 e3
  have hrev : ∀ b, U.1 b.opposite = (U.1 b)⁻¹ := fun b => U.2.2 b (mem_univ b)
  simp only [faceHolonomy, hcoe, coe_liftField]
  rw [e1, e2, e3, e4]
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, hrev, mul_one, mul_assoc]
  rfl
theorem faces_meeting_image {d : CutoffData} (W : d.CutoffWindow) :
    {P : d.PeriodicPlaquette | ∃ l ∈ d.projLinks W.links, CutoffData.FaceContains (d := d) P l} =
      d.projFace '' W.faces := by
  ext P
  constructor
  · rintro ⟨l, ⟨b, hb, rfl⟩, hl⟩
    obtain ⟨x, κ, rfl⟩ := W.subset_links hb
    obtain ⟨y, μ, μ', hne⟩ := P
    simp only [CutoffData.FaceContains, WilsonOperator.periodicEdgeList, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rw [projLink_forwardFrom_eq] at hl
    rcases hl with hl | hl | hl | hl
    · obtain ⟨hy, rfl⟩ := forwardFrom_injective d hl
      refine ⟨⟨x, κ, μ', hne⟩, ⟨_, hb, ?_⟩, ?_⟩
      · simp [ContainsLink, ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hy rfl rfl
    · obtain ⟨hy, rfl⟩ := forwardFrom_injective d hl
      refine ⟨⟨x - axisStep d.spacing μ, μ, κ, hne⟩, ⟨_, hb, ?_⟩, ?_⟩
      · simp [ContainsLink, ElementaryPlaquette.edges]
      · refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
        show projectPoint d.L d.m ((d.K : ℕ) : ℤ) (x - axisStep d.spacing μ) = y
        rw [projectPoint_sub, projectPoint_axisStep, hy, add_sub_cancel_right]
    · obtain ⟨hy, rfl⟩ := forwardFrom_injective d hl
      refine ⟨⟨x - axisStep d.spacing μ', κ, μ', hne⟩, ⟨_, hb, ?_⟩, ?_⟩
      · simp [ContainsLink, ElementaryPlaquette.edges]
      · refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
        show projectPoint d.L d.m ((d.K : ℕ) : ℤ) (x - axisStep d.spacing μ') = y
        rw [projectPoint_sub, projectPoint_axisStep, hy, add_sub_cancel_right]
    · obtain ⟨hy, rfl⟩ := forwardFrom_injective d hl
      refine ⟨⟨x, μ, κ, hne⟩, ⟨_, hb, ?_⟩, ?_⟩
      · simp [ContainsLink, ElementaryPlaquette.edges]
      · exact PeriodicLattice.Plaquette.ext hy rfl rfl
  · rintro ⟨p, ⟨b, hb, hpb⟩, rfl⟩
    refine ⟨d.projLink b, ⟨b, hb, rfl⟩, ?_⟩
    have hmem : d.projLink b ∈ d.projLink '' {b | ContainsLink p b} := ⟨b, hpb, rfl⟩
    rw [image_containsLink] at hmem
    exact hmem
theorem mem_links_union_rim {d : CutoffData} (W : d.CutoffWindow) {p : ElementaryPlaquette d.spacing}
    (hp : p ∈ W.faces) {b : Link d.spacing} (hb : ContainsLink p b) : b ∈ W.links ∪ W.rim := by
  by_cases hin : b ∈ W.links
  · exact Or.inl hin
  · exact Or.inr ⟨⟨p, hp, hb⟩, hin⟩
theorem links_union_rim_subset {d : CutoffData} (W : d.CutoffWindow) : W.links ∪ W.rim ⊆ d.links :=
  union_subset W.subset_links W.rim_subset_links
theorem image_links_inter_image_rim {d : CutoffData} (W : d.CutoffWindow)
    (hinj : W.EmbedsInPeriodicLattice) :
    d.projLinks W.links ∩ d.projLinks W.rim = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro l ⟨⟨b, hb, rfl⟩, ⟨b', hb', he⟩⟩
  have heq : b' = b := hinj (Or.inr hb') (Or.inl hb) he
  exact hb'.2 (heq ▸ hb)
theorem injOn_faces {d : CutoffData} (W : d.CutoffWindow) (hinj : W.EmbedsInPeriodicLattice) :
    InjOn d.projFace W.faces := by
  intro p hp p' hp' he
  have hc : (projectPoint d.L d.m ((d.K : ℕ) : ℤ) p.corner) =
      projectPoint d.L d.m ((d.K : ℕ) : ℤ) p'.corner :=
    congrArg PeriodicLattice.Plaquette.origin he
  have hf : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis he
  have hs : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis he
  have m1 : Link.forwardFrom p.corner p.lowAxis ∈ W.links ∪ W.rim :=
    mem_links_union_rim W hp (by simp [ContainsLink, ElementaryPlaquette.edges])
  have m2 : Link.forwardFrom p'.corner p'.lowAxis ∈ W.links ∪ W.rim :=
    mem_links_union_rim W hp' (by simp [ContainsLink, ElementaryPlaquette.edges])
  have e : d.projLink (Link.forwardFrom p.corner p.lowAxis) =
      d.projLink (Link.forwardFrom p'.corner p'.lowAxis) := by
    rw [projLink_forwardFrom_eq, projLink_forwardFrom_eq, hc, hf]
  have hx : p.corner = p'.corner := congrArg Link.initial (hinj m1 m2 e)
  exact ElementaryPlaquette.ext hx hf hs
theorem latticeSubgroup_antitone (ℓ ℓ' : d.sideSet) (hle : (ℓ : ℝ) ≤ ℓ') :
    latticeSubgroup (ℓ' : ℝ) ≤ latticeSubgroup (ℓ : ℝ) := by
  obtain ⟨q, -, hq⟩ := ℓ.2
  obtain ⟨q', -, hq'⟩ := ℓ'.2
  have hL := one_lt_L d
  have hqq : q ≤ q' := by
    rw [hq, hq'] at hle
    simp only [PeriodicLattice.torusSide] at hle
    exact (pow_le_pow_iff_right₀ hL).mp (by linarith)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hqq
  rintro x ⟨k, hk⟩
  refine ⟨fun μ => k μ * (d.L : ℤ) ^ r, fun μ => ?_⟩
  rw [hk μ, hq, hq']
  simp only [PeriodicLattice.torusSide]
  push_cast
  ring
theorem injOn_of_side_le {S : Set (Link d.spacing)} (hS : S ⊆ d.links) (ℓ ℓ' : d.sideSet)
    (hle : (ℓ : ℝ) ≤ ℓ')
    (hinj : InjOn (d.withSide ℓ).projLink S) : InjOn (d.withSide ℓ').projLink S := by
  intro b hb b' hb' he
  obtain ⟨x, μ, rfl⟩ := hS hb
  obtain ⟨x', μ', rfl⟩ := hS hb'
  obtain ⟨hμ, hx⟩ := (projLink_forwardFrom_eq_iff (d.withSide ℓ') x x' μ μ').mp he
  rw [d.side_withSide] at hx
  have hx' := latticeSubgroup_antitone d ℓ ℓ' hle hx
  rw [← d.side_withSide ℓ] at hx'
  exact hinj hb hb' ((projLink_forwardFrom_eq_iff (d.withSide ℓ) x x' μ μ').mpr ⟨hμ, hx'⟩)
theorem injOn_of_bounded {S : Set (Link d.spacing)} (hS : S ⊆ d.links) (ϱ : ℝ)
    (hE : ∀ b ∈ S, ∀ x ∈ linkEndpoints b, PeriodicLattice.supNormVec (x : AmbientSpace) ≤ ϱ)
    (hs : d.side / 2 > ϱ) : InjOn d.projLink S := by
  intro b hb b' hb' he
  obtain ⟨x, μ, rfl⟩ := hS hb
  obtain ⟨x', μ', rfl⟩ := hS hb'
  obtain ⟨rfl, k, hk⟩ := (projLink_forwardFrom_eq_iff d x x' μ μ').mp he
  have hx := hE _ hb x (by simp [linkEndpoints, Link.forwardFrom])
  have hx' := hE _ hb' x' (by simp [linkEndpoints, Link.forwardFrom])
  have hpos := side_pos d
  have hzero : ∀ ν, k ν = 0 := by
    intro ν
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k ν : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have h2 := (abs_le_supNormVec (x : AmbientSpace) ν).trans hx
    have h3 := (abs_le_supNormVec (x' : AmbientSpace) ν).trans hx'
    have h4 : (x : AmbientSpace) ν - (x' : AmbientSpace) ν = (k ν : ℝ) * d.side := hk ν
    have h5 : |(k ν : ℝ) * d.side| = |(k ν : ℝ)| * d.side := by
      rw [abs_mul, abs_of_pos hpos]
    have h6 : |(x : AmbientSpace) ν - (x' : AmbientSpace) ν| ≤
        |(x : AmbientSpace) ν| + |(x' : AmbientSpace) ν| :=
      abs_sub _ _
    rw [h4, h5] at h6
    nlinarith
  have hxx : x = x' := by
    refine Subtype.ext (funext fun ν => ?_)
    have h4 : (x : AmbientSpace) ν - (x' : AmbientSpace) ν = (k ν : ℝ) * d.side := hk ν
    rw [hzero ν] at h4
    simp only [Int.cast_zero, zero_mul] at h4
    exact sub_eq_zero.mp h4
  rw [hxx]
variable {d}
theorem exists_bound (hP : FacesOfWindows.Statement) (W : d.CutoffWindow) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ W.BoundedBy ϱ := by
  have hfin : (W.links ∪ W.rim).Finite := (hP d W).2.2.2.1.2.1
  obtain ⟨M, hM⟩ := (hfin.image fun b : Link d.spacing =>
    max (PeriodicLattice.supNormVec (b.initial : AmbientSpace))
      (PeriodicLattice.supNormVec (b.terminal : AmbientSpace))).bddAbove
  refine ⟨max M 0 + 1, by positivity, fun b hb x hx => ?_⟩
  have h1 := hM (mem_image_of_mem _ hb)
  have h2 : M ≤ max M 0 + 1 := (le_max_left _ _).trans (by linarith)
  rcases hx with rfl | rfl
  · exact ((le_max_left _ _).trans h1).trans h2
  · exact ((le_max_right _ _).trans h1).trans h2
theorem mem_injectiveSides_of_bounded (W : d.CutoffWindow) {ϱ : ℝ} (hE : W.BoundedBy ϱ) {ℓ' : ℝ}
    (hmem : ℓ' ∈ d.sideSet) (hs : ℓ' / 2 > ϱ) : ℓ' ∈ W.injectiveSides := by
  refine ⟨hmem, injOn_of_bounded (d.withSide ⟨ℓ', hmem⟩) (links_union_rim_subset W) ϱ hE ?_⟩
  rw [d.side_withSide]
  exact hs
theorem injectiveSides_nonempty (hP : FacesOfWindows.Statement) (W : d.CutoffWindow) :
    W.injectiveSides.Nonempty := by
  obtain ⟨ϱ, -, hE⟩ := exists_bound hP W
  have hL := one_lt_L d
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt ϱ hL
  have hpow : (d.L : ℝ) ^ q ≤ (d.L : ℝ) ^ (q + 1) :=
    pow_le_pow_right₀ hL.le (Nat.le_succ q)
  refine ⟨PeriodicLattice.torusSide d.L (q + 1), mem_injectiveSides_of_bounded W hE
    ⟨q + 1, Nat.succ_pos q, rfl⟩ ?_⟩
  simp only [PeriodicLattice.torusSide]
  linarith
theorem isLeast_minSide (hP : FacesOfWindows.Statement) (W : d.CutoffWindow) :
    IsLeast W.injectiveSides W.minSide := by
  classical
  have hL := one_lt_L d
  have hex : ∃ q : ℕ, PeriodicLattice.torusSide d.L q ∈ W.injectiveSides := by
    obtain ⟨ℓ, hℓ⟩ := injectiveSides_nonempty hP W
    obtain ⟨⟨q, -, rfl⟩, -⟩ := id hℓ
    exact ⟨q, hℓ⟩
  obtain ⟨q₀, hq₀, hmin⟩ : ∃ q₀, PeriodicLattice.torusSide d.L q₀ ∈ W.injectiveSides ∧
      ∀ q, PeriodicLattice.torusSide d.L q ∈ W.injectiveSides → q₀ ≤ q :=
    ⟨Nat.find hex, Nat.find_spec hex, fun q hq => Nat.find_min' hex hq⟩
  have hleast : IsLeast W.injectiveSides (PeriodicLattice.torusSide d.L q₀) := by
    refine ⟨hq₀, ?_⟩
    rintro ℓ hℓ
    obtain ⟨⟨q, -, rfl⟩, -⟩ := id hℓ
    have hpow := pow_le_pow_right₀ hL.le (hmin q hℓ)
    simp only [PeriodicLattice.torusSide]
    linarith
  have heq : W.minSide = PeriodicLattice.torusSide d.L q₀ := hleast.csInf_eq
  rw [heq]
  exact hleast
theorem injectiveAtSide_mono (W : d.CutoffWindow) (ℓ ℓ' : d.sideSet) (hle : (ℓ : ℝ) ≤ ℓ')
    (hinj : W.InjectiveAtSide ℓ) : W.InjectiveAtSide ℓ' :=
  injOn_of_side_le d (links_union_rim_subset W) ℓ ℓ' hle hinj
theorem injectiveSides_eq (hP : FacesOfWindows.Statement) (W : d.CutoffWindow) :
    W.injectiveSides = {ℓ' | ℓ' ∈ d.sideSet ∧ ℓ' ≥ W.minSide} := by
  have hl := isLeast_minSide hP W
  ext ℓ'
  constructor
  · intro hmem
    exact ⟨hmem.1, hl.2 hmem⟩
  · rintro ⟨hmem, hge⟩
    obtain ⟨h₀, hE⟩ := hl.1
    exact ⟨hmem, injectiveAtSide_mono W ⟨_, h₀⟩ ⟨ℓ', hmem⟩ hge hE⟩
theorem injectiveSides_withExpCoupling (W : d.CutoffWindow) (m' : ℕ+) (β' : ℝ) (hβ' : 0 < β') :
    (W.withExpCoupling m' β' hβ').injectiveSides = W.injectiveSides := by
  ext ℓ'
  constructor
  · rintro ⟨hmem, hE⟩
    exact ⟨hmem, hE⟩
  · rintro ⟨hmem, hE⟩
    exact ⟨hmem, hE⟩
end WindowProjection
open WindowProjection in
theorem windowProjectionProperties_of_facesOfWindows (hP : FacesOfWindows.Statement) :
    WindowProjectionProperties := by
  intro d
  refine ⟨⟨image_links d, projFace_surjective d, fun p => image_containsLink d p,
    fun y y' μ μ' h => forwardFrom_injective d h, fun y μ => ?_,
    fun x x' μ μ' => projLink_forwardFrom_eq_iff d x x' μ μ',
    fun U b _ => liftCompactField_apply U b, fun U p => faceHolonomy_liftField d U p,
    continuous_liftCompactField⟩, fun W => ?_⟩
  · exact PeriodicLattice.opposite_notMem_positiveBonds (two_le_L d) (neg_m_lt_K d) ⟨y, μ, rfl⟩
  · have hl := isLeast_minSide hP W
    refine ⟨faces_meeting_image W, fun h => ⟨image_links_inter_image_rim W h, injOn_faces W h,
      fun ℓ' hle => injectiveAtSide_mono W ⟨d.side, d.side_mem_sideSet⟩ ℓ' hle
        (W.injectiveAtSide_side_iff.mpr h)⟩, exists_bound hP W, fun ϱ _ hE hs => ?_,
      injectiveSides_nonempty hP W, hl, injectiveSides_eq hP W, fun m' β' hβ' => ?_,
      fun ℓ' h ϱ _ hE hs => hl.2 (mem_injectiveSides_of_bounded W hE h hs)⟩
    · exact injOn_of_bounded d (links_union_rim_subset W) ϱ hE hs
    · show sInf _ = sInf _
      rw [injectiveSides_withExpCoupling]
end CutoffLinks
end YangMills.Construction
