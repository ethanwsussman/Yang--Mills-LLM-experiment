import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Matrices.SpecialUnitaryAngles
import YangMills.Construction.Towers.AveragesAtTheSideInfinityNearTheTrivialConfiguration
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace.NearIdentitySmoothing
theorem operatorNorm_mul_four_sub_one_lt (hG : Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds)
    {A B C D : Matrices.ComplexMatrix2} {r : ℝ}
    (hA : A ∈ Matrices.ComplexMatrix2.specialUnitary) (hB : B ∈ Matrices.ComplexMatrix2.specialUnitary)
    (hC : C ∈ Matrices.ComplexMatrix2.specialUnitary) (hD : D ∈ Matrices.ComplexMatrix2.specialUnitary)
    (a : Matrices.ComplexMatrix2.operatorNorm (A - 1) < r)
    (b : Matrices.ComplexMatrix2.operatorNorm (B - 1) < r)
    (c : Matrices.ComplexMatrix2.operatorNorm (C - 1) < r)
    (d : Matrices.ComplexMatrix2.operatorNorm (D - 1) < r) :
    Matrices.ComplexMatrix2.operatorNorm (A * (B * (C * D)) - 1) < 4 * r := by
  have h := (hG.2.2.2.2.2.1 4 ![A, B, C, D] (fun _ => 1)
    (fun i => by fin_cases i <;> simpa) (fun _ => one_mem _)).2
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Fin.sum_univ_four,
    inv_one, mul_one] at h
  simp at h
  linarith
theorem plaquetteHolonomy_sub_one_lt (hG : Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds)
    {L m : ℕ} {j j' : ℤ}
    (c : PeriodicLattice.Bond L m j) (W : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2) {r : ℝ}
    (hWb : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')),
      W b ∈ PeriodicLattice.compactGaugeGroup ∧ Matrices.ComplexMatrix2.operatorNorm (W b - 1) < r)
    (p : PeriodicLattice.Plaquette L m j')
    (hp : p ∈ (PeriodicLattice.doubleBlockPlaquettes c : Set (PeriodicLattice.Plaquette L m j'))) :
    Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy W p - 1) < 4 * r := by
  have hvert : ∀ x ∈ p.vertices,
      (x : PeriodicLattice.FourTorus L m) ∈ PeriodicLattice.bondDoubleBlock c := hp
  have v₀ := hvert p.origin (Or.inl rfl)
  have v₁ := hvert (p.origin + PeriodicLattice.unitStep L m j' p.firstAxis) (Or.inr (Or.inl rfl))
  have v₂ := hvert (p.origin + PeriodicLattice.unitStep L m j' p.firstAxis +
      PeriodicLattice.unitStep L m j' p.secondAxis) (Or.inr (Or.inr (Or.inl rfl)))
  have v₃ := hvert (p.origin + PeriodicLattice.unitStep L m j' p.secondAxis)
    (Or.inr (Or.inr (Or.inr rfl)))
  have e : p.origin + PeriodicLattice.unitStep L m j' p.secondAxis +
      PeriodicLattice.unitStep L m j' p.firstAxis =
      p.origin + PeriodicLattice.unitStep L m j' p.firstAxis +
        PeriodicLattice.unitStep L m j' p.secondAxis :=
    add_right_comm _ _ _
  have h₁ : PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) := ⟨v₀, v₁⟩
  have h₂ : PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L m j' p.firstAxis) p.secondAxis ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) := ⟨v₁, v₂⟩
  have h₃ : PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L m j' p.secondAxis) p.firstAxis ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) :=
    ⟨v₃, by show ((p.origin + PeriodicLattice.unitStep L m j' p.secondAxis +
        PeriodicLattice.unitStep L m j' p.firstAxis : PeriodicLattice.Site L m j') :
          PeriodicLattice.FourTorus L m) ∈ _
            rw [e]; exact v₂⟩
  have h₄ : PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) := ⟨v₀, v₃⟩
  have h₅ : (PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L m j' p.secondAxis) p.firstAxis).opposite ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) := ⟨h₃.2, h₃.1⟩
  have h₆ : (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis).opposite ∈
      (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')) := ⟨h₄.2, h₄.1⟩
  obtain ⟨a₁, a₂⟩ := hWb _ h₁
  obtain ⟨b₁, b₂⟩ := hWb _ h₂
  obtain ⟨d₁, d₂⟩ := hWb _ h₅
  obtain ⟨e₁, e₂⟩ := hWb _ h₆
  have key := operatorNorm_mul_four_sub_one_lt hG a₁ b₁ d₁ e₁ a₂ b₂ d₂ e₂
  simpa [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds] using key
theorem doubleBlockCurvature_lt (hG : Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds)
    {L m : ℕ} {j j' : ℤ}
    [Finite (PeriodicLattice.Plaquette L m j')]
    (c : PeriodicLattice.Bond L m j) (W : PeriodicLattice.Bond L m j' → Matrices.ComplexMatrix2)
    {ω : ℝ} (hω : 0 < ω)
    (hWb : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (PeriodicLattice.Bond L m j')),
      W b ∈ PeriodicLattice.compactGaugeGroup ∧
        Matrices.ComplexMatrix2.operatorNorm (W b - 1) < ω / 4) :
    PeriodicLattice.doubleBlockCurvature W c < ω := by
  unfold PeriodicLattice.doubleBlockCurvature
  rcases isEmpty_or_nonempty ↥(PeriodicLattice.doubleBlockPlaquettes c :
      Set (PeriodicLattice.Plaquette L m j')) with he | he
  · rw [Real.iSup_of_isEmpty]
    exact hω
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite
      (f := fun p : ↥(PeriodicLattice.doubleBlockPlaquettes c :
        Set (PeriodicLattice.Plaquette L m j')) =>
          Matrices.ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy W p.1 - 1))
    rw [← hp]
    have := plaquetteHolonomy_sub_one_lt hG c W hWb p.1 p.2
    have h4 : 4 * (ω / 4) = ω := by ring
    rwa [h4] at this
theorem smoothing_mem_of_supDistOne_lt
    (hS : PeriodicLattice.AveragingSchemeProperties)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds)
    {L k i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hik : i < k)
    (V : Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2)
    (hV : V ∈ Tower.FullSpace.fieldSpace L k i)
    (hd : Tower.FullSpace.supDistOne V < ENNReal.ofReal (Averaging.smoothingRadius L / 4))
    (c : Tower.FullSpace.Edge L k (i + 1)) (hc : c.IsPositivelyOriented) :
    V ∈ Tower.FullSpace.complexDomainNearOne L c ∧
      Tower.FullSpace.complexSmoothing L V c ∈ PeriodicLattice.compactGaugeGroup ∧
      ∀ y : Tower.FullSpace.Vertex L k (i + 1), y = c.initial ∨ y = c.terminal →
        ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k i) y,
          Tower.FullSpace.complexContourMean L V y x ∈ PeriodicLattice.compactGaugeGroup := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hk : 1 ≤ k := by omega
  have Q : Tower.FullSpace.ProjPreservesStructures L 1 k i c :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 i hik c hc
  obtain ⟨hdt, hdh, hdp, -⟩ := (hQ L 1 k (i + 1) hL one_pos hik).1 c
  have hVb : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup ∧
      Matrices.ComplexMatrix2.operatorNorm (V b - 1) < Averaging.smoothingRadius L / 4 :=
    fun b => by
    refine ⟨hV.1 b, ?_⟩
    have h : ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (V b - 1)) <
        ENNReal.ofReal (Averaging.smoothingRadius L / 4) :=
      lt_of_le_of_lt
        (le_iSup (fun b => ENNReal.ofReal (Matrices.ComplexMatrix2.operatorNorm (V b - 1))) b) hd
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h
  have hcV : Tower.FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup
      (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V :=
    ⟨fun b _ => (Matrix.mem_specialUnitaryGroup_iff.mp (hV.1 b)).2, fun b _ => hV.2 b⟩
  have hWc := Q.projField_spec V hcV
  set W := Tower.FullSpace.projField L 1 k i
    (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c) V with hW
  set d := Tower.FullSpace.projEdge L 1 k (i + 1) c with hdef
  have hWb : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock d : Set (Tower.Edge L 1 k i)),
      W b ∈ PeriodicLattice.compactGaugeGroup ∧
        Matrices.ComplexMatrix2.operatorNorm (W b - 1) < Averaging.smoothingRadius L / 4 := by
    intro b hb
    rw [← Q.doubleCubeLinks_image] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    rw [hWc.1 b₀ hb₀]
    exact hVb b₀
  have hWreal : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup
      (PeriodicLattice.bondsInDoubleBlock d) W :=
    ⟨fun b hb => (hWb b hb).1, hWc.2.2⟩
  have hplaq : Finite (PeriodicLattice.Plaquette L 1 (PeriodicLattice.levelDepth k i)) := by
    have := (hA L hL 1 i k (by norm_num) hik.le).2.1
    exact this.2.2.2.2.2.2.2.2.2.2.2.2
  have hsize : PeriodicLattice.doubleBlockCurvature W d < Averaging.smoothingRadius L :=
    doubleBlockCurvature_lt hG d W hω hWb
  have hsch := (hS L hL 1 k i one_pos hik .centred).2.1 d (hdp hc)
  have hmean := hsch.2.2.2.2.1 W hWreal hsize
  have hval := hsch.2.2.2.1 W hmean.mem_domain hWreal
  have hdom : W ∈ (PeriodicLattice.complexAveragingDomainNearOne d :
      Set (Tower.Edge L 1 k i → Matrices.ComplexMatrix2)) := by
    rw [← hsch.2.2.1.domain_eq]
    exact hmean.mem_domain
  have hVO : V ∈ Tower.FullSpace.complexDomainNearOne L c :=
    (Q.mem_complexDomain_iff V hcV).2 hdom
  refine ⟨hVO, ?_, ?_⟩
  · rw [Q.complexSmoothing_eq V hVO, ← hsch.2.2.1.average_eq W hmean.mem_domain]
    exact hval.average_mem
  · intro y hy x hx
    rw [Q.complexContourMean_eq V hVO y hy x hx]
    have hyd : Tower.FullSpace.projVertex L 1 k (i + 1) y ∈
        ({d.source, d.target} : Set (Tower.Vertex L 1 k (i + 1))) := by
      rcases hy with rfl | rfl
      · exact Or.inl hdt.symm
      · exact Or.inr hdh.symm
    have hxd : Tower.FullSpace.projVertex L 1 k i x ∈
        PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i)
          (Tower.FullSpace.projVertex L 1 k (i + 1) y) := by
      rcases hy with rfl | rfl
      · have := Q.cube_initial
        rw [← hdt]
        show ((Tower.FullSpace.projVertex L 1 k i x : Tower.Vertex L 1 k i) :
          PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.unitBlock d.source
        rw [← this]
        exact ⟨_, hx, rfl⟩
      · have := Q.cube_terminal
        rw [← hdh]
        show ((Tower.FullSpace.projVertex L 1 k i x : Tower.Vertex L 1 k i) :
          PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.unitBlock d.target
        rw [← this]
        exact ⟨_, hx, rfl⟩
    exact hval.contour_mem _ hyd _ hxd
theorem smoothingNearIdentity_holds
    (hS : PeriodicLattice.AveragingSchemeProperties)
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hG : Matrices.ComplexMatrix2.SpecialUnitaryAngleBounds) :
    Tower.FullSpace.SmoothingNearIdentity := by
  intro L k j hL _ hj hjk V hV hd c hc
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact smoothing_mem_of_supDistOne_lt hS hF hQ hA hG hL (by omega) V hV hd c hc
end Tower.FullSpace.NearIdentitySmoothing
end YangMills.Construction
end
