import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Towers.AveragingMapCovariantOnTheComplexDomain
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower.SmoothingCovariantOnComplexDomain
open PeriodicLattice (complexGaugeGroup compactGaugeGroup)
theorem compact_mem_complex {X : Matrices.ComplexMatrix2} (hX : X ∈ compactGaugeGroup) :
    X ∈ complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hX).2
theorem inv_conj_eq {A X B : Matrices.ComplexMatrix2} (hB : B ∈ complexGaugeGroup) :
    (A * X * B⁻¹)⁻¹ = B * X⁻¹ * A⁻¹ := by
  have h : IsUnit B.det := by
    rw [show B.det = 1 from hB]
    exact isUnit_one
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ h, mul_assoc]
theorem conj_mem_complex {A X B : Matrices.ComplexMatrix2} (hA : A ∈ complexGaugeGroup)
    (hX : X ∈ complexGaugeGroup) (hB : B ∈ complexGaugeGroup) :
    A * X * B⁻¹ ∈ complexGaugeGroup := by
  have h₁ : A.det = 1 := hA
  have h₂ : X.det = 1 := hX
  have h₃ : B.det = 1 := hB
  show (A * X * B⁻¹).det = 1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, h₁, h₂, h₃, Ring.inverse_one]
  simp
theorem periodic_case (hS : PeriodicLattice.AveragingSchemeProperties) {L m k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j < k)
    (c : Edge L m k (j + 1)) (hc : c.IsPositivelyOriented) :
    ComplexSmoothingCovariantOnDomain c := by
  intro V hV u hu
  obtain ⟨-, -, hM, -, -, hcov⟩ := (hS L hL m k j hm hj .centred).2.1 c hc
  have hC := hcov u V hu hV.1.1
  have hVm : V ∈ (PeriodicLattice.schemeHolomorphyDomain .centred c :
      Set (Edge L m k j → Matrices.ComplexMatrix2)) := by
    rw [hM.domain_eq]
    exact hV
  have hdef : PeriodicLattice.IsSchemeAverageDefined .centred V c := hVm
  have hgm : PeriodicLattice.gaugeTransform u V ∈
      (PeriodicLattice.schemeHolomorphyDomain .centred c :
        Set (Edge L m k j → Matrices.ComplexMatrix2)) :=
    hC.average_defined_iff.2 hdef
  refine ⟨by rw [← hM.domain_eq]; exact hgm, ?_, ?_⟩
  · have h := hC.average_eq hdef
    rw [hM.average_eq _ hgm, hM.average_eq _ hVm] at h
    exact h
  · intro y hy x hx
    have hd : PeriodicLattice.IsContourHolonomyDefined .centred V y x := by
      rcases hy with rfl | hy
      · exact hdef.2.1.1 x hx
      · rw [mem_singleton_iff] at hy
        subst hy
        exact hdef.2.1.2 x hx
    exact hC.contour_eq y hy x hx hd
theorem isFieldOn_gaugeAct {a : ℝ} {ℬ : Set (InfiniteLattice.Link a)}
    {V : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    {u : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2}
    (hV : FullSpace.IsFieldOn complexGaugeGroup ℬ V)
    (hu : ∀ b ∈ ℬ, u b.initial ∈ complexGaugeGroup ∧ u b.terminal ∈ complexGaugeGroup) :
    FullSpace.IsFieldOn complexGaugeGroup ℬ (FullSpace.gaugeAct u V) := by
  refine ⟨fun b hb => conj_mem_complex (hu b hb).1 (hV.1 b hb) (hu b hb).2, fun b hb => ?_⟩
  show u b.terminal * V b.opposite * (u b.initial)⁻¹ = (u b.initial * V b * (u b.terminal)⁻¹)⁻¹
  rw [hV.2 b hb, inv_conj_eq (hu b hb).2]
theorem mem_cube_self {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {a : ℝ} (a' : ℝ)
    (y : InfiniteLattice.LatticePoint a) : (y : AmbientSpace) ∈ FullSpace.cube L a' y := by
  have h13 := hL.2
  refine ⟨0, fun μ => ?_, ?_⟩
  · simp only [Pi.zero_apply, abs_zero, mul_zero, pow_one]
    omega
  · simp
theorem fullSpace_case (hS : PeriodicLattice.AveragingSchemeProperties)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hB : EdgeProjectionProperties)
    (hR : PeriodicLattice.ComplexAverageIsLocal) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (c : FullSpace.Edge L k (j + 1))
    (hc : c.IsPositivelyOriented) : FullSpace.ComplexSmoothingCovariantOnDomain L k j c := by
  classical
  intro V hV u hu
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨-, hnest, -, -, -, -, hquot⟩ := hT L hL0 hL k
  have hQ := (hquot (by omega) 1 one_pos).2 j hj c hc
  have hfine := (hB L 1 k j hL one_pos hj.le).1
  have hcoarse := (hB L 1 k (j + 1) hL one_pos hj).1
  obtain ⟨hinit, hterm, hpos, -⟩ := hcoarse c
  set c' : Edge L 1 k (j + 1) := FullSpace.projEdge L 1 k (j + 1) c with hc'def
  have hc' : c'.IsPositivelyOriented := hpos hc
  obtain ⟨W, hWdef⟩ : ∃ W, W = FullSpace.projField L 1 k j
      (FullSpace.doubleCubeLinks L (meshAt L k j) c) V := ⟨_, rfl⟩
  let u' : Vertex L 1 k j → Matrices.ComplexMatrix2 := fun x' =>
    if h : ∃ x : FullSpace.Vertex L k j, (x : AmbientSpace) ∈ FullSpace.doubleCube L (meshAt L k j) c ∧
      FullSpace.projVertex L 1 k j x = x' then u h.choose else 1
  have hu'eq : ∀ x : FullSpace.Vertex L k j,
      (x : AmbientSpace) ∈ FullSpace.doubleCube L (meshAt L k j) c →
      u' (FullSpace.projVertex L 1 k j x) = u x := by
    intro x hx
    have hex : ∃ z : FullSpace.Vertex L k j,
        (z : AmbientSpace) ∈ FullSpace.doubleCube L (meshAt L k j) c ∧
        FullSpace.projVertex L 1 k j z = FullSpace.projVertex L 1 k j x := ⟨x, hx, rfl⟩
    have hs := hex.choose_spec
    have he : hex.choose = x :=
      Subtype.ext (hQ.injOn_doubleCube hs.1 hx (congrArg Subtype.val hs.2))
    simp only [u', dif_pos hex, he]
  have hu'real : ∀ x' : Vertex L 1 k j,
      (x' : PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.bondDoubleBlock c' →
      u' x' ∈ compactGaugeGroup := by
    intro x' _
    by_cases h : ∃ x : FullSpace.Vertex L k j,
        (x : AmbientSpace) ∈ FullSpace.doubleCube L (meshAt L k j) c ∧
        FullSpace.projVertex L 1 k j x = x'
    · simp only [u', dif_pos h]
      exact hu _ h.choose_spec.1
    · simp only [u', dif_neg h]
      exact one_mem _
  have hVc : FullSpace.IsFieldOn complexGaugeGroup
      (FullSpace.doubleCubeLinks L (meshAt L k j) c) V := hV.1.1
  have hVg : FullSpace.IsFieldOn complexGaugeGroup
      (FullSpace.doubleCubeLinks L (meshAt L k j) c) (FullSpace.gaugeAct u V) :=
    isFieldOn_gaugeAct hVc fun b hb =>
      ⟨compact_mem_complex (hu _ hb.1), compact_mem_complex (hu _ hb.2)⟩
  obtain ⟨W', hW'def⟩ : ∃ W', W' = FullSpace.projField L 1 k j
      (FullSpace.doubleCubeLinks L (meshAt L k j) c) (FullSpace.gaugeAct u V) := ⟨_, rfl⟩
  have hW : W ∈ (PeriodicLattice.complexAveragingDomainNearOne c' :
      Set (Edge L 1 k j → Matrices.ComplexMatrix2)) :=
    hWdef ▸ (hQ.mem_complexDomain_iff V hVc).1 hV
  obtain ⟨hgD, hgA, hgC⟩ := periodic_case hS hL one_pos hj c' hc' W hW u' hu'real
  have agree : ∀ b' ∈ (PeriodicLattice.bondsInDoubleBlock c' : Set (Edge L 1 k j)),
      PeriodicLattice.gaugeTransform u' W b' = W' b' := by
    intro b' hb'
    rw [← hQ.doubleCubeLinks_image] at hb'
    obtain ⟨b, hb, rfl⟩ := hb'
    have e₁ := (hQ.projField_spec V hVc).1 b hb
    have e₂ := (hQ.projField_spec _ hVg).1 b hb
    rw [← hWdef] at e₁
    rw [← hW'def] at e₂
    obtain ⟨fs, ft, -, -⟩ := hfine b
    show u' (FullSpace.projEdge L 1 k j b).source * W (FullSpace.projEdge L 1 k j b) *
      (u' (FullSpace.projEdge L 1 k j b).target)⁻¹ = W' (FullSpace.projEdge L 1 k j b)
    rw [e₁, e₂, fs, ft, hu'eq _ hb.1, hu'eq _ hb.2]
    rfl
  have hread := hR L 1 k j hL.1 hL.2 one_pos hj c' hc'
  have hW' : W' ∈ (PeriodicLattice.complexAveragingDomainNearOne c' :
      Set (Edge L 1 k j → Matrices.ComplexMatrix2)) :=
    (hread.mem_domain_iff _ _ agree).1 hgD
  have hVgD := (hQ.mem_complexDomain_iff _ hVg).2 (hW'def ▸ hW')
  have hsite : ∀ y : FullSpace.Vertex L k (j + 1),
      (FullSpace.projVertex L 1 k (j + 1) y).toSublattice (PeriodicLattice.levelDepth k j) =
        FullSpace.projVertex L 1 k j (FullSpace.toFiner (meshAt L k j) y) := by
    intro y
    have hmem : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) :=
      hnest j (j + 1) (by omega) hj y.2
    have hz : ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) = y :=
      Classical.epsilon_spec
        (p := fun x : InfiniteLattice.LatticePoint (meshAt L k j) => (x : AmbientSpace) = y)
        ⟨⟨y, hmem⟩, rfl⟩
    have hq : ((FullSpace.projVertex L 1 k j (FullSpace.toFiner (meshAt L k j) y) : Vertex L 1 k j) :
        PeriodicLattice.FourTorus L 1) =
          (FullSpace.projVertex L 1 k (j + 1) y : Vertex L 1 k (j + 1)) := by
      show TorusMetric.torusProj _ _ = TorusMetric.torusProj _ _
      rw [hz]
    have hw := Classical.epsilon_spec
      (p := fun x : Vertex L 1 k j => (x : PeriodicLattice.FourTorus L 1) =
        (FullSpace.projVertex L 1 k (j + 1) y : Vertex L 1 k (j + 1))) ⟨_, hq⟩
    exact Subtype.ext (hw.trans hq.symm)
  have hselfSite : ∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) ∈
        FullSpace.doubleCube L (meshAt L k j) c := by
    intro y hy
    have hmem : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) :=
      hnest j (j + 1) (by omega) hj y.2
    have hz : ((FullSpace.toFiner (meshAt L k j) y : FullSpace.Vertex L k j) : AmbientSpace) = y :=
      Classical.epsilon_spec
        (p := fun x : InfiniteLattice.LatticePoint (meshAt L k j) => (x : AmbientSpace) = y)
        ⟨⟨y, hmem⟩, rfl⟩
    rw [hz]
    rcases hy with rfl | rfl
    · exact Or.inl (mem_cube_self hL _ _)
    · exact Or.inr (mem_cube_self hL _ _)
  have hcoarseSite : ∀ y : FullSpace.Vertex L k (j + 1), (y = c.initial ∨ y = c.terminal) →
      u' ((FullSpace.projVertex L 1 k (j + 1) y).toSublattice (PeriodicLattice.levelDepth k j)) =
        u (FullSpace.toFiner (meshAt L k j) y) := by
    intro y hy
    rw [hsite, hu'eq _ (hselfSite y hy)]
  refine ⟨hVgD, ?_, ?_⟩
  · have a₁ := hQ.complexSmoothing_eq _ hVgD
    have a₂ := hQ.complexSmoothing_eq V hV
    rw [← hW'def] at a₁
    rw [← hWdef] at a₂
    have a₃ : PeriodicLattice.complexBlockAverage W' c' =
        PeriodicLattice.complexBlockAverage (PeriodicLattice.gaugeTransform u' W) c' := by
      simp only [PeriodicLattice.complexBlockAverage, if_pos hc']
      exact (hread.average_eq _ _ agree).symm
    have hi := hcoarseSite c.initial (Or.inl rfl)
    have ht := hcoarseSite c.terminal (Or.inr rfl)
    rw [← hinit] at hi
    rw [← hterm] at ht
    rw [a₁, a₃, hgA, ← a₂, hi, ht]
  · intro y hy x hx
    have hy₂ : y = c.initial ∨ y = c.terminal := by
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (mem_singleton_iff.1 hy)
    have hxD : (x : AmbientSpace) ∈ FullSpace.doubleCube L (meshAt L k j) c := by
      rcases hy₂ with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    set y' := FullSpace.projVertex L 1 k (j + 1) y with hy'def
    set x' := FullSpace.projVertex L 1 k j x with hx'def
    have hy' : y' = c'.source ∨ y' = c'.target := by
      rcases hy₂ with rfl | rfl
      · exact Or.inl hinit.symm
      · exact Or.inr hterm.symm
    have hcube : (x' : PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.unitBlock y' := by
      rcases hy₂ with rfl | rfl
      · rw [hy'def, ← hinit, ← hQ.cube_initial]
        exact ⟨x, hx, rfl⟩
      · rw [hy'def, ← hterm, ← hQ.cube_terminal]
        exact ⟨x, hx, rfl⟩
    have hx' : x' ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y' := hcube
    have hyset : y' ∈ ({c'.source, c'.target} : Set (Vertex L 1 k (j + 1))) := by
      rcases hy' with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hinner : ∀ b ∈ (PeriodicLattice.bondsInside (PeriodicLattice.unitBlock y') :
        Set (Edge L 1 k j)), b ∈ (PeriodicLattice.bondsInDoubleBlock c' : Set (Edge L 1 k j)) := by
      intro b hb
      rcases hy' with h | h
      · rw [h] at hb
        exact ⟨Or.inl hb.1, Or.inl hb.2⟩
      · rw [h] at hb
        exact ⟨Or.inr hb.1, Or.inr hb.2⟩
    have hdef : PeriodicLattice.IsContourHolonomyDefined .centred
        (PeriodicLattice.gaugeTransform u' W) y' x' := by
      refine ⟨hx', ⟨fun b hb => hgD.1.1.1 b (hinner b hb),
        fun b hb => hgD.1.1.2 b (hinner b hb)⟩, ?_⟩
      rcases hy' with h | h
      · rw [h] at hx' ⊢
        exact hgD.1.2.1 x' hx'
      · rw [h] at hx' ⊢
        exact hgD.1.2.2 x' hx'
    have hloc := ((hS L hL 1 k j one_pos hj .centred).1 y' x' hx').2
      (PeriodicLattice.gaugeTransform u' W) W' fun b hb => agree b (hinner b hb)
    have hvalue : PeriodicLattice.complexMeanContourHolonomy
        (PeriodicLattice.gaugeTransform u' W) y' x' =
          PeriodicLattice.complexMeanContourHolonomy W' y' x' := hloc.2 hdef
    have b₁ := hQ.complexContourMean_eq _ hVgD y hy₂ x hx
    have b₂ := hQ.complexContourMean_eq V hV y hy₂ x hx
    rw [← hW'def] at b₁
    rw [← hWdef] at b₂
    rw [b₁, ← hvalue, hgC y' hyset x' hx', ← b₂, hcoarseSite y hy₂, hu'eq x hxD]
theorem statement_holds (hA : SmoothingNearIdentity)
    (hS : PeriodicLattice.AveragingSchemeProperties)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hB : EdgeProjectionProperties)
    (hR : PeriodicLattice.ComplexAverageIsLocal) :
    SmoothingCovariantOnComplexDomain.Statement := by
  intro L hL
  obtain ⟨hper, hfull, hρ⟩ := hA.1 L hL
  refine ⟨fun m k j hm hj => ?_, fun k j hj => ?_, hρ⟩
  · obtain ⟨h₁, h₂, h₃⟩ := hper m k j hm hj
    exact ⟨h₁, h₂, h₃, fun c hc => periodic_case hS hL hm hj c hc⟩
  · obtain ⟨h₁, h₂, h₃⟩ := hfull k j hj
    exact ⟨h₁, h₂, h₃, fun c hc => fullSpace_case hS hT hB hR hL hj c hc⟩
end Tower.SmoothingCovariantOnComplexDomain
end YangMills.Construction
end
