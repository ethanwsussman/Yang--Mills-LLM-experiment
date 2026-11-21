import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.Lattice.ElementarySquareCorners
import YangMills.Construction.Lattice.PlaquetteHolonomyTraceProof
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerate
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy
variable (D : CutoffMirrors.MirrorData)
theorem blockingFactor_pos : (0 : ℝ) < (D.L : ℝ) := by
  have h := D.isAdmissible.2
  exact_mod_cast (by omega : 0 < D.L)
theorem meshSpacing_pos : 0 < D.spacing := by
  unfold CutoffMirrors.MirrorData.spacing meshSize
  exact zpow_pos (blockingFactor_pos D) _
theorem torusSide_eq : torusSide D.L D.m = 2 * (D.sitesPerSide : ℝ) * D.spacing := by
  have hL := (blockingFactor_pos D).ne'
  show 2 * (D.L : ℝ) ^ (D.m : ℕ) =
    2 * ((D.L ^ ((D.m : ℕ) + (D.K : ℕ)) : ℕ) : ℝ) * (D.L : ℝ) ^ (-(((D.K : ℕ) : ℤ)))
  rw [zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem two_le_sitesPerSide : 2 ≤ D.sitesPerSide := by
  have h := D.isAdmissible.2
  have hm := D.m.pos
  calc 2 ≤ D.L ^ 1 := by rw [pow_one]; omega
    _ ≤ D.L ^ ((D.m : ℕ) + (D.K : ℕ)) := Nat.pow_le_pow_right (by omega) (by omega)
theorem circleCoord_eq_zero_iff (z : ℤ) :
    (((z : ℝ) * D.spacing : ℝ) : D.CircleCoord) = 0 ↔
      ∃ k : ℤ, z = 2 * (D.sitesPerSide : ℤ) * k := by
  have ha := (meshSpacing_pos D).ne'
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [torusSide_eq D, zsmul_eq_mul] at hk
    have h1 : ((k : ℝ) * (2 * (D.sitesPerSide : ℝ))) * D.spacing = (z : ℝ) * D.spacing := by
      rw [← hk]; ring
    have h2 := mul_right_cancel₀ ha h1
    have h3 : (z : ℝ) = ((2 * (D.sitesPerSide : ℤ) * k : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h3
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [torusSide_eq D, zsmul_eq_mul]
    push_cast
    ring
def latticePoint (n : Fin 4 → ℤ) : D.Torus := D.proj (meshPoint D n)
theorem latticePoint_apply (n : Fin 4 → ℤ) (ν : Fin 4) :
    latticePoint D n ν = ((D.spacing * (n ν : ℝ) : ℝ) : D.CircleCoord) := rfl
theorem latticePoint_add (n n' : Fin 4 → ℤ) :
    latticePoint D (n + n') = latticePoint D n + latticePoint D n' := by
  funext ν
  rw [Pi.add_apply, latticePoint_apply, latticePoint_apply, latticePoint_apply,
    ← AddCircle.coe_add]
  congr 1
  simp [mul_add]
theorem latticePoint_eq_iff (n n' : Fin 4 → ℤ) :
    latticePoint D n = latticePoint D n' ↔
      ∃ k : Fin 4 → ℤ, ∀ ν, n ν - n' ν = 2 * (D.sitesPerSide : ℤ) * k ν := by
  have hcoord : ∀ ν, latticePoint D n ν = latticePoint D n' ν ↔
      ∃ k : ℤ, n ν - n' ν = 2 * (D.sitesPerSide : ℤ) * k := by
    intro ν
    rw [← circleCoord_eq_zero_iff, ← sub_eq_zero, latticePoint_apply, latticePoint_apply,
      ← AddCircle.coe_sub,
      show D.spacing * (n ν : ℝ) - D.spacing * (n' ν : ℝ) = ((n ν - n' ν : ℤ) : ℝ) * D.spacing by
        push_cast; ring]
  constructor
  · intro h
    choose k hk using fun ν => (hcoord ν).1 (congrFun h ν)
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact funext fun ν => (hcoord ν).2 ⟨k ν, hk ν⟩
theorem eq_of_latticePoint_eq {n n' : Fin 4 → ℤ} (h : latticePoint D n = latticePoint D n')
    (hs : ∀ ν, |n ν - n' ν| ≤ 3) : n = n' := by
  obtain ⟨k, hk⟩ := (latticePoint_eq_iff D n n').1 h
  have h2 := two_le_sitesPerSide D
  funext ν
  have h0 := Int.eq_zero_of_abs_lt_dvd (Dvd.intro (k ν) (hk ν).symm)
    (lt_of_le_of_lt (hs ν) (by omega))
  omega
theorem card_latticeSubgroup : Nat.card D.latticeSubgroup = (2 * D.sitesPerSide) ^ 4 := by
  have h2 := two_le_sitesPerSide D
  let f : (Fin 4 → Fin (2 * D.sitesPerSide)) → D.latticeSubgroup := fun r =>
    ⟨latticePoint D fun ν => ((r ν : ℕ) : ℤ), fun ν => ((r ν : ℕ) : ℤ), fun ν => by
      rw [latticePoint_apply, mul_comm]; rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro r r' h
      obtain ⟨k, hk⟩ := (latticePoint_eq_iff D _ _).1 (congrArg Subtype.val h)
      funext ν
      have h1 := (r ν).2
      have h3 := (r' ν).2
      have h0 := Int.eq_zero_of_abs_lt_dvd (Dvd.intro (k ν) (hk ν).symm) (by
        rw [abs_lt]; constructor <;> omega)
      exact Fin.ext (by omega)
    · rintro ⟨x, n, hn⟩
      have hpos : 0 < 2 * (D.sitesPerSide : ℤ) := by omega
      have hnn : ∀ ν, 0 ≤ n ν % (2 * (D.sitesPerSide : ℤ)) :=
        fun ν => Int.emod_nonneg _ hpos.ne'
      have hlt : ∀ ν, n ν % (2 * (D.sitesPerSide : ℤ)) < 2 * (D.sitesPerSide : ℤ) :=
        fun ν => Int.emod_lt_of_pos _ hpos
      refine ⟨fun ν => ⟨(n ν % (2 * (D.sitesPerSide : ℤ))).toNat, ?_⟩, ?_⟩
      · have h1 := hnn ν
        have h3 := hlt ν
        omega
      · apply Subtype.ext
        have hx : x = latticePoint D n := by
          funext ν
          rw [latticePoint_apply, hn ν, mul_comm]
          rfl
        show latticePoint D _ = x
        rw [hx]
        refine (latticePoint_eq_iff D _ _).2
          ⟨fun ν => -(n ν / (2 * (D.sitesPerSide : ℤ))), fun ν => ?_⟩
        have h1 := Int.emod_add_mul_ediv (n ν) (2 * (D.sitesPerSide : ℤ))
        simp only [Int.toNat_of_nonneg (hnn ν)]
        linarith
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm]
  simp [Nat.card_eq_fintype_card]
theorem lift_mem_latticeSubgroup (x : D.Torus) (hx : x ∈ D.latticeSubgroup) (y : Fin 4 → ℝ)
    (hy : D.IsLiftOf x y) : y ∈ InfiniteLattice.latticeSubgroup D.spacing := by
  obtain ⟨n, hn⟩ := hx
  have h : ∀ μ, ∃ k : ℤ, y μ = ((n μ + 2 * (D.sitesPerSide : ℤ) * k : ℤ) : ℝ) * D.spacing := by
    intro μ
    have h1 : ((y μ : ℝ) : D.CircleCoord) = (((n μ : ℝ) * D.spacing : ℝ) : D.CircleCoord) :=
      (congrFun hy μ).trans (hn μ)
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, torusSide_eq D] at hk
    push_cast
    linear_combination -hk
  choose k hk using h
  exact ⟨fun μ => n μ + 2 * (D.sitesPerSide : ℤ) * k μ, hk⟩
theorem meshAndSiteCount : MeshAndSiteCount D := by
  have hn := two_le_sitesPerSide D
  have hside : D.side = 2 * (D.sitesPerSide : ℝ) * D.spacing := torusSide_eq D
  have ha := meshSpacing_pos D
  refine ⟨?_, hn, ?_, ?_, ?_, ?_, ?_, card_latticeSubgroup D, lift_mem_latticeSubgroup D, ?_⟩
  · simp [CutoffMirrors.MirrorData.sitesPerSide]
  · rw [hside]; ring
  · rw [hside]; field_simp
  · have h2 : (2 : ℝ) ≤ (D.sitesPerSide : ℝ) := by exact_mod_cast hn
    linarith
  · rintro x ⟨n, hn'⟩
    refine ⟨fun μ => n μ * (2 * (D.sitesPerSide : ℤ)), fun μ => ?_⟩
    rw [hn' μ, hside]
    push_cast
    ring
  · ext x
    constructor
    · rintro ⟨n, hn'⟩
      refine ⟨meshPoint D n, ⟨n, fun μ => ?_⟩, ?_⟩
      · simp [meshPoint, mul_comm]
      · funext μ
        show ((D.spacing * (n μ : ℝ) : ℝ) : D.CircleCoord) = x μ
        rw [hn' μ, mul_comm]
        rfl
    · rintro ⟨y, ⟨n, hn'⟩, rfl⟩
      refine ⟨n, fun μ => ?_⟩
      show ((y μ : ℝ) : D.CircleCoord) = _
      rw [hn' μ]
      rfl
  · exact latticePoint_eq_iff D
theorem proj_signedAxisStep (q : Fin 4 × ℤˣ) :
    D.proj (signedAxisStep D q) = latticePoint D (Pi.single q.1 (q.2 : ℤ)) := by
  congr 1
  funext ν
  by_cases h : ν = q.1
  · subst h
    simp [signedAxisStep, meshPoint, coordVec]
    ring
  · simp [signedAxisStep, meshPoint, coordVec, Pi.single_eq_of_ne h]
theorem unitStep_coe (μ : Fin 4) :
    ((unitStep D.L D.m ((D.K : ℕ) : ℤ) μ : CutoffSite D) : D.Torus) =
      latticePoint D (Pi.single μ 1) := by
  funext ν
  rw [latticePoint_apply]
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis, CutoffMirrors.MirrorData.spacing]
  · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h]
theorem neg_unitStep_coe (μ : Fin 4) :
    -((unitStep D.L D.m ((D.K : ℕ) : ℤ) μ : CutoffSite D) : D.Torus) =
      latticePoint D (Pi.single μ (-1)) := by
  rw [unitStep_coe]
  funext ν
  rw [Pi.neg_apply, latticePoint_apply, latticePoint_apply, ← AddCircle.coe_neg]
  congr 1
  by_cases h : ν = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
theorem abs_single_unit_le (ν μ : Fin 4) (ε : ℤˣ) :
    |(Pi.single ν (ε : ℤ) : Fin 4 → ℤ) μ| ≤ 1 := by
  by_cases h : μ = ν
  · subst h
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  · simp [Pi.single_eq_of_ne h]
theorem single_unit_injective {q q' : Fin 4 × ℤˣ}
    (h : (Pi.single q.1 (q.2 : ℤ) : Fin 4 → ℤ) = Pi.single q'.1 (q'.2 : ℤ)) : q = q' := by
  by_cases hν : q.1 = q'.1
  · have h1 := congrFun h q.1
    rw [Pi.single_eq_same, hν, Pi.single_eq_same] at h1
    exact Prod.ext hν (Units.ext h1)
  · have h1 := congrFun h q.1
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hν] at h1
    exact absurd h1 q.2.ne_zero
theorem proj_signedAxisStep_injective :
    Function.Injective (fun q : Fin 4 × ℤˣ => D.proj (signedAxisStep D q)) := by
  intro q q' h
  simp only [proj_signedAxisStep] at h
  refine single_unit_injective (eq_of_latticePoint_eq D h fun ν => ?_)
  have h1 := abs_single_unit_le q.1 ν q.2
  have h2 := abs_single_unit_le q'.1 ν q'.2
  rw [abs_le] at h1 h2 ⊢
  omega
theorem not_opposite_positive (b : CutoffBond D) (h : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨μ', h'⟩
  obtain ⟨μ, h⟩ := h
  have e1 : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single μ 1) := by
    rw [← unitStep_coe, ← h]; rfl
  have e2 : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single μ' (-1)) := by
    rw [← neg_unitStep_coe, ← h']
    show _ = -(((b.source : D.Torus)) - b.target)
    abel
  have e3 := e1.symm.trans e2
  have h1 : (Pi.single μ ((1 : ℤˣ) : ℤ) : Fin 4 → ℤ) = Pi.single μ' ((-1 : ℤˣ) : ℤ) := by
    refine eq_of_latticePoint_eq D (by simpa using e3) fun ν => ?_
    have h1 := abs_single_unit_le μ ν 1
    have h2 := abs_single_unit_le μ' ν (-1)
    rw [abs_le] at h1 h2 ⊢
    omega
  have h2 := @single_unit_injective (μ, 1) (μ', -1) h1
  have h3 : (1 : ℤˣ) = -1 := congrArg Prod.snd h2
  exact absurd h3 (by decide)
theorem bondAxisAndSign : BondAxisAndSign D := by
  refine ⟨proj_signedAxisStep_injective D, fun b => ⟨?_, ?_⟩⟩
  · have hex : ∃ q : Fin 4 × ℤˣ,
        D.DiffEq (b.target : D.Torus) (b.source : D.Torus) (signedAxisStep D q) := by
      obtain ⟨μ, h | h⟩ := b.isNeighbour
      · refine ⟨(μ, 1), ?_⟩
        show (b.target : D.Torus) = b.source + D.proj (signedAxisStep D (μ, 1))
        rw [proj_signedAxisStep]
        have e : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single μ 1) := by
          rw [← unitStep_coe, ← h]; rfl
        simp only [Units.val_one]
        rw [← e]
        abel
      · refine ⟨(μ, -1), ?_⟩
        show (b.target : D.Torus) = b.source + D.proj (signedAxisStep D (μ, -1))
        rw [proj_signedAxisStep]
        have e : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single μ (-1)) := by
          rw [← neg_unitStep_coe, ← AddSubgroup.coe_neg, ← h]; rfl
        simp only [Units.val_neg, Units.val_one]
        rw [← e]
        abel
    obtain ⟨q, hq⟩ := hex
    refine ⟨q, hq, fun q' hq' => ?_⟩
    apply proj_signedAxisStep_injective D
    exact add_left_cancel (hq'.symm.trans hq)
  · obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact Or.inl ⟨⟨μ, h⟩, not_opposite_positive D b ⟨μ, h⟩⟩
    · have hr : b.opposite.IsPositivelyOriented := ⟨μ, by
        show b.source - b.target = _
        rw [← neg_sub, h, neg_neg]⟩
      exact Or.inr ⟨hr, fun hb => not_opposite_positive D b hb hr⟩
theorem plaquetteVerticesDistinct (hc : ElementarySquare.ElementarySquareStatement) :
    PlaquetteVerticesDistinct D := by
  have hA := (hc D.L D.isAdmissible (D.m : ℕ) 0 (D.K : ℕ) D.m.pos (Nat.zero_le _)).1
  have hd : levelDepth (D.K : ℕ) 0 = ((D.K : ℕ) : ℤ) := by simp [levelDepth]
  rw [hd] at hA
  have hlist : ∀ q : CutoffPlaquette D,
      (vertexList D q).map (fun s : CutoffSite D => (s : D.Torus)) =
        ElementarySquare.vertexList (pointOnAxis D.L D.m)
          (meshSize D.L ((D.K : ℕ) : ℤ)) (q.origin : D.Torus) q.firstAxis q.secondAxis :=
    fun q => rfl
  have hset : ∀ q : CutoffPlaquette D,
      {c | c ∈ ElementarySquare.vertexList (pointOnAxis D.L D.m)
          (meshSize D.L ((D.K : ℕ) : ℤ)) (q.origin : D.Torus) q.firstAxis q.secondAxis} =
        (fun s : CutoffSite D => (s : D.Torus)) '' q.vertices := by
    intro q
    ext c
    rw [← hlist q]
    simp only [mem_ofPred_eq, List.mem_map, mem_image, mem_vertexList]
  intro p
  refine ⟨?_, fun p' h => ?_⟩
  · have h1 := (hA p.origin p.origin.2 p.origin p.origin.2 p.firstAxis p.secondAxis p.firstAxis
      p.secondAxis p.firstAxis_lt_secondAxis p.firstAxis_lt_secondAxis).1.2
    rw [← hlist p] at h1
    exact List.Nodup.of_map _ h1
  · have h1 := (hA p.origin p.origin.2 p'.origin p'.origin.2 p.firstAxis p.secondAxis p'.firstAxis
      p'.secondAxis p.firstAxis_lt_secondAxis p'.firstAxis_lt_secondAxis).2.1
        (by rw [hset, hset, h])
    exact Plaquette.ext (Subtype.ext h1.1) h1.2.1 h1.2.2
def loopEdge (p : CutoffPlaquette D) : Fin 4 → CutoffBond D :=
  ![bottomEdge D p, rightEdge D p, (topEdge D p).opposite, (leftEdge D p).opposite]
theorem plaquetteHolonomy_eq_loop (p : CutoffPlaquette D) (U : CutoffBond D → Matrices.ComplexMatrix2) :
    plaquetteHolonomy U p =
      U (loopEdge D p 0) * U (loopEdge D p 1) * U (loopEdge D p 2) * U (loopEdge D p 3) := by
  simp [plaquetteHolonomy, pathHolonomy, Plaquette.boundaryBonds, loopEdge, bottomEdge,
    rightEdge, topEdge, leftEdge, mul_assoc]
theorem holonomyOfPositiveEdges : HolonomyOfPositiveEdges D := by
  intro p
  refine ⟨⟨p.firstAxis, by simp [bottomEdge, Bond.forwardFrom]⟩,
    ⟨p.secondAxis, by simp [rightEdge, Bond.forwardFrom]⟩,
    ⟨p.firstAxis, by simp [topEdge, Bond.forwardFrom]⟩,
    ⟨p.secondAxis, by simp [leftEdge, Bond.forwardFrom]⟩,
    add_right_comm _ _ _, fun U hU => ?_⟩
  rw [plaquetteHolonomy_eq_loop]
  have h2 : U (loopEdge D p 2) = (U (topEdge D p))⁻¹ := hU.2 _ (mem_univ _)
  have h3 : U (loopEdge D p 3) = (U (leftEdge D p))⁻¹ := hU.2 _ (mem_univ _)
  rw [h2, h3]
  rfl
def firstOffset (i : Fin 4) : ℤ := if i = 1 ∨ i = 2 then 1 else 0
def secondOffset (i : Fin 4) : ℤ := if i = 2 ∨ i = 3 then 1 else 0
def vertexOffset (p : CutoffPlaquette D) (i : Fin 4) : Fin 4 → ℤ :=
  firstOffset i • Pi.single p.firstAxis 1 + secondOffset i • Pi.single p.secondAxis 1
def loopVertex (p : CutoffPlaquette D) : Fin 4 → CutoffSite D :=
  ![p.origin, p.origin + unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis,
    p.origin + unitStep D.L D.m ((D.K : ℕ) : ℤ) p.firstAxis +
      unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis,
    p.origin + unitStep D.L D.m ((D.K : ℕ) : ℤ) p.secondAxis]
theorem fin_four_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by apply _root_.YangMills.Construction.GaugeFixing.fin_four_cases <;> assumption
theorem loopEdge_source (p : CutoffPlaquette D) (i : Fin 4) :
    (loopEdge D p i).source = loopVertex D p i := by
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact add_right_comm _ _ _
  · rfl
theorem loopEdge_target (p : CutoffPlaquette D) (i : Fin 4) :
    (loopEdge D p i).target = loopVertex D p (i + 1) := by
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
theorem loopVertex_mem (p : CutoffPlaquette D) (i : Fin 4) : loopVertex D p i ∈ p.vertices := by
  rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> simp [loopVertex, Plaquette.vertices]
theorem exists_loopVertex (p : CutoffPlaquette D) (c : CutoffSite D) (h : c ∈ p.vertices) :
    ∃ i, c = loopVertex D p i := by
  simp only [Plaquette.vertices, mem_insert_iff, mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
theorem loopVertex_coe (p : CutoffPlaquette D) (i : Fin 4) :
    ((loopVertex D p i : CutoffSite D) : D.Torus) = p.origin + latticePoint D (vertexOffset D p i) := by
  have h0 : latticePoint D 0 = 0 := by
    funext ν
    simp [latticePoint_apply]
  rcases fin_four_cases i with rfl | rfl | rfl | rfl
  · have : vertexOffset D p 0 = 0 := by simp [vertexOffset, firstOffset, secondOffset]
    rw [this, h0, add_zero]
    rfl
  · have : vertexOffset D p 1 = Pi.single p.firstAxis 1 := by
      simp [vertexOffset, firstOffset, secondOffset]
    rw [this, ← unitStep_coe]
    rfl
  · have : vertexOffset D p 2 = Pi.single p.firstAxis 1 + Pi.single p.secondAxis 1 := by
      simp [vertexOffset, firstOffset, secondOffset]
    rw [this, latticePoint_add, ← unitStep_coe, ← unitStep_coe, ← add_assoc]
    rfl
  · have : vertexOffset D p 3 = Pi.single p.secondAxis 1 := by
      simp [vertexOffset, firstOffset, secondOffset]
    rw [this, ← unitStep_coe]
    rfl
theorem vertexOffset_apply (p : CutoffPlaquette D) (i ν : Fin 4) :
    vertexOffset D p i ν = (if ν = p.firstAxis then firstOffset i else 0) +
      (if ν = p.secondAxis then secondOffset i else 0) := by
  simp [vertexOffset, Pi.single_apply]
theorem vertexOffset_firstAxis (p : CutoffPlaquette D) (i : Fin 4) :
    vertexOffset D p i p.firstAxis = firstOffset i := by
  simp [vertexOffset_apply, p.firstAxis_lt_secondAxis.ne]
theorem vertexOffset_secondAxis (p : CutoffPlaquette D) (i : Fin 4) :
    vertexOffset D p i p.secondAxis = secondOffset i := by
  simp [vertexOffset_apply, p.firstAxis_lt_secondAxis.ne']
theorem vertexOffset_bounds (p : CutoffPlaquette D) (i ν : Fin 4) :
    0 ≤ vertexOffset D p i ν ∧ vertexOffset D p i ν ≤ 1 := by
  have hs : ∀ i : Fin 4, 0 ≤ firstOffset i ∧ firstOffset i ≤ 1 := by decide
  have ht : ∀ i : Fin 4, 0 ≤ secondOffset i ∧ secondOffset i ≤ 1 := by decide
  have h1 := hs i
  have h2 := ht i
  rw [vertexOffset_apply]
  split_ifs with e1 e2
  · exact absurd (e1.symm.trans e2) p.firstAxis_lt_secondAxis.ne
  · omega
  · omega
  · omega
theorem loopVertex_injective (p : CutoffPlaquette D) {i j : Fin 4}
    (h : loopVertex D p i = loopVertex D p j) : i = j := by
  have h1 := congrArg Subtype.val h
  rw [loopVertex_coe, loopVertex_coe] at h1
  have hv := eq_of_latticePoint_eq D (add_left_cancel h1) fun ν => by
    have a1 := vertexOffset_bounds D p i ν
    have a2 := vertexOffset_bounds D p j ν
    rw [abs_le]
    omega
  have hs := congrFun hv p.firstAxis
  have ht := congrFun hv p.secondAxis
  rw [vertexOffset_firstAxis, vertexOffset_firstAxis] at hs
  rw [vertexOffset_secondAxis, vertexOffset_secondAxis] at ht
  have hdec : ∀ i j : Fin 4, firstOffset i = firstOffset j →
      secondOffset i = secondOffset j → i = j := by decide
  exact hdec i j hs ht
theorem loopVertex_adjacent (p : CutoffPlaquette D) {i j : Fin 4} (b : CutoffBond D)
    (ht : b.source = loopVertex D p i) (hh : b.target = loopVertex D p j) :
    j = i + 1 ∨ j = i - 1 := by
  have hkey : ∃ (ρ : Fin 4) (ε : ℤˣ), latticePoint D (vertexOffset D p j) =
      latticePoint D (vertexOffset D p i + Pi.single ρ (ε : ℤ)) := by
    obtain ⟨ρ, h | h⟩ := b.isNeighbour
    · refine ⟨ρ, 1, ?_⟩
      have e : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single ρ 1) := by
        rw [← unitStep_coe, ← h]; rfl
      rw [hh, ht, loopVertex_coe, loopVertex_coe] at e
      rw [latticePoint_add, Units.val_one, ← e]
      abel
    · refine ⟨ρ, -1, ?_⟩
      have e : ((b.target : D.Torus) - b.source) = latticePoint D (Pi.single ρ (-1)) := by
        rw [← neg_unitStep_coe, ← AddSubgroup.coe_neg, ← h]; rfl
      rw [hh, ht, loopVertex_coe, loopVertex_coe] at e
      rw [latticePoint_add, Units.val_neg, Units.val_one, ← e]
      abel
  obtain ⟨ρ, ε, hp⟩ := hkey
  have hv := eq_of_latticePoint_eq D hp fun ν => by
    have a1 := vertexOffset_bounds D p i ν
    have a2 := vertexOffset_bounds D p j ν
    have a3 := abs_single_unit_le ρ ν ε
    rw [abs_le] at a3
    rw [Pi.add_apply, abs_le]
    omega
  have h1 := congrFun hv p.firstAxis
  have h2 := congrFun hv p.secondAxis
  have h3 := congrFun hv ρ
  rw [Pi.add_apply, vertexOffset_firstAxis, vertexOffset_firstAxis] at h1
  rw [Pi.add_apply, vertexOffset_secondAxis, vertexOffset_secondAxis] at h2
  rw [Pi.add_apply, Pi.single_eq_same] at h3
  have hdec : ∀ i j : Fin 4,
      ((firstOffset j = firstOffset i + 1 ∨ firstOffset j = firstOffset i - 1) ∧
        secondOffset j = secondOffset i) ∨
      (firstOffset j = firstOffset i ∧
        (secondOffset j = secondOffset i + 1 ∨
          secondOffset j = secondOffset i - 1)) → j = i + 1 ∨ j = i - 1 := by decide
  have hne := p.firstAxis_lt_secondAxis.ne
  apply hdec i j
  by_cases e1 : ρ = p.firstAxis
  · subst e1
    rw [Pi.single_eq_same] at h1
    rw [Pi.single_eq_of_ne hne.symm, add_zero] at h2
    refine Or.inl ⟨?_, h2⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact Or.inl h1
    · right
      rw [h1]
      simp [sub_eq_add_neg]
  · by_cases e2 : ρ = p.secondAxis
    · subst e2
      rw [Pi.single_eq_same] at h2
      rw [Pi.single_eq_of_ne hne, add_zero] at h1
      refine Or.inr ⟨h1, ?_⟩
      rcases Int.units_eq_one_or ε with rfl | rfl
      · exact Or.inl h2
      · right
        rw [h2]
        simp [sub_eq_add_neg]
    · exfalso
      rw [vertexOffset_apply, vertexOffset_apply, if_neg e1, if_neg e2, if_neg e1, if_neg e2] at h3
      exact ε.ne_zero (by omega)
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem closed_walk_orientation : ∀ i₀ i₁ i₂ i₃ : Fin 4,
    (∀ t : Fin 4, t = i₀ ∨ t = i₁ ∨ t = i₂ ∨ t = i₃) →
    (i₁ = i₀ + 1 ∨ i₁ = i₀ - 1) → (i₂ = i₁ + 1 ∨ i₂ = i₁ - 1) →
    (i₃ = i₂ + 1 ∨ i₃ = i₂ - 1) → (i₀ = i₃ + 1 ∨ i₀ = i₃ - 1) →
    (i₁ = i₀ + 1 ∧ i₂ = i₀ + 2 ∧ i₃ = i₀ + 3) ∨ (i₁ = i₀ + 3 ∧ i₂ = i₀ + 2 ∧ i₃ = i₀ + 1) := by
  decide
theorem trace_cyclic_four (g : Fin 4 → Matrices.ComplexMatrix2) (a : Fin 4) :
    Matrices.ComplexMatrix2.fullTrace (g a * g (a + 1) * g (a + 2) * g (a + 3)) =
      Matrices.ComplexMatrix2.fullTrace (g 0 * g 1 * g 2 * g 3) := by
  have rot : ∀ A B C E : Matrices.ComplexMatrix2,
      Matrices.ComplexMatrix2.fullTrace (A * B * C * E) =
        Matrices.ComplexMatrix2.fullTrace (B * C * E * A) := by
    intro A B C E
    rw [show A * B * C * E = A * (B * C * E) by simp only [mul_assoc]]
    exact Matrix.trace_mul_comm _ _
  rcases fin_four_cases a with rfl | rfl | rfl | rfl
  · simp only [zero_add]
  · rw [show (1 : Fin 4) + 1 = 2 by decide, show (1 : Fin 4) + 2 = 3 by decide,
      show (1 : Fin 4) + 3 = 0 by decide]
    exact (rot _ _ _ _).symm
  · rw [show (2 : Fin 4) + 1 = 3 by decide, show (2 : Fin 4) + 2 = 0 by decide,
      show (2 : Fin 4) + 3 = 1 by decide]
    exact ((rot _ _ _ _).trans (rot _ _ _ _)).symm
  · rw [show (3 : Fin 4) + 1 = 0 by decide, show (3 : Fin 4) + 2 = 1 by decide,
      show (3 : Fin 4) + 3 = 2 by decide]
    exact (((rot _ _ _ _).trans (rot _ _ _ _)).trans (rot _ _ _ _)).symm
theorem re_trace_inv_of_specialUnitary {V : Matrices.ComplexMatrix2}
    (hV : V ∈ Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace V⁻¹).re = (Matrices.ComplexMatrix2.fullTrace V).re := by apply _root_.YangMills.Construction.PeriodicLattice.PlaquetteHolonomyTraceProof.re_fullTrace_inv <;> assumption
theorem eq_loopEdge (p : CutoffPlaquette D) (b : CutoffBond D) {i j : Fin 4}
    (ht : b.source = loopVertex D p i) (hh : b.target = loopVertex D p j) (hj : j = i + 1) :
    b = loopEdge D p i :=
  Bond.ext (ht.trans (loopEdge_source D p i).symm)
    (hh.trans (by rw [hj, loopEdge_target]))
theorem eq_loopEdge_opposite (p : CutoffPlaquette D) (b : CutoffBond D) {i j : Fin 4}
    (ht : b.source = loopVertex D p i) (hh : b.target = loopVertex D p j) (hi : i = j + 1) :
    b = (loopEdge D p j).opposite :=
  Bond.ext (ht.trans (by rw [hi, ← loopEdge_target]; rfl))
    (hh.trans ((loopEdge_source D p j).symm))
theorem traceIndependentOfTraversal : TraceIndependentOfTraversal D := by
  intro p z₀ z₁ z₂ z₃ b₀ b₁ b₂ b₃ hset ht₀ hh₀ ht₁ hh₁ ht₂ hh₂ ht₃ hh₃ U hU
  have hz : ∀ z, z ∈ ({z₀, z₁, z₂, z₃} : Set (CutoffSite D)) → ∃ i, z = loopVertex D p i :=
    fun z h => exists_loopVertex D p z (hset ▸ h)
  obtain ⟨i₀, rfl⟩ := hz z₀ (by simp)
  obtain ⟨i₁, rfl⟩ := hz z₁ (by simp)
  obtain ⟨i₂, rfl⟩ := hz z₂ (by simp)
  obtain ⟨i₃, rfl⟩ := hz z₃ (by simp)
  have hsurj : ∀ t : Fin 4, t = i₀ ∨ t = i₁ ∨ t = i₂ ∨ t = i₃ := by
    intro t
    have h := loopVertex_mem D p t
    rw [← hset] at h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h | h
    · exact Or.inl (loopVertex_injective D p h)
    · exact Or.inr (Or.inl (loopVertex_injective D p h))
    · exact Or.inr (Or.inr (Or.inl (loopVertex_injective D p h)))
    · exact Or.inr (Or.inr (Or.inr (loopVertex_injective D p h)))
  have hf : ∀ a : Fin 4, a + 2 = a + 1 + 1 ∧ a + 3 = a + 2 + 1 ∧ a = a + 3 + 1 := by decide
  have hU₀ : ∀ i, U (loopEdge D p i) ∈ Matrices.ComplexMatrix2.specialUnitary :=
    fun i => hU.1 _ (mem_univ _)
  have hrev : ∀ i, U (loopEdge D p i).opposite = (U (loopEdge D p i))⁻¹ :=
    fun i => hU.2 _ (mem_univ _)
  have hrot := trace_cyclic_four (fun i => U (loopEdge D p i)) i₀
  beta_reduce at hrot
  rcases closed_walk_orientation i₀ i₁ i₂ i₃ hsurj (loopVertex_adjacent D p b₀ ht₀ hh₀)
      (loopVertex_adjacent D p b₁ ht₁ hh₁) (loopVertex_adjacent D p b₂ ht₂ hh₂)
      (loopVertex_adjacent D p b₃ ht₃ hh₃) with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [eq_loopEdge D p b₀ ht₀ hh₀ rfl, eq_loopEdge D p b₁ ht₁ hh₁ (hf i₀).1,
      eq_loopEdge D p b₂ ht₂ hh₂ (hf i₀).2.1, eq_loopEdge D p b₃ ht₃ hh₃ (hf i₀).2.2,
      plaquetteHolonomy_eq_loop, hrot]
  · rw [eq_loopEdge_opposite D p b₀ ht₀ hh₀ (hf i₀).2.2,
      eq_loopEdge_opposite D p b₁ ht₁ hh₁ (hf i₀).2.1,
      eq_loopEdge_opposite D p b₂ ht₂ hh₂ (hf i₀).1,
      eq_loopEdge_opposite D p b₃ ht₃ hh₃ rfl, hrev, hrev, hrev, hrev,
      plaquetteHolonomy_eq_loop, ← hrot]
    have hV : U (loopEdge D p i₀) * U (loopEdge D p (i₀ + 1)) *
        U (loopEdge D p (i₀ + 2)) * U (loopEdge D p (i₀ + 3)) ∈
          Matrices.ComplexMatrix2.specialUnitary :=
      mul_mem (mul_mem (mul_mem (hU₀ _) (hU₀ _)) (hU₀ _)) (hU₀ _)
    rw [← re_trace_inv_of_specialUnitary hV]
    simp only [Matrix.mul_inv_rev, mul_assoc]
theorem nondegeneracy (hc : ElementarySquare.ElementarySquareStatement) :
    NondegeneracyStatement := fun D =>
  ⟨meshAndSiteCount D, bondAxisAndSign D, plaquetteVerticesDistinct D hc,
    holonomyOfPositiveEdges D, traceIndependentOfTraversal D⟩
end YangMills.Construction.ReflectionPositivity.PlaquetteNondegeneracy
end
