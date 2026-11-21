import YangMills.Construction.InequalityOnMirroredCopies.SimilarityCarriesTheArray
import YangMills.Construction.MirrorGridsOfEverySide.SimilaritiesOfTheLattices
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.BoxTorus
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open MirrorGridsAllSides (ScalingMap)
private structure TorusScaling (L : ℕ) (κ κ' : ℤ) (ℓ ℓ' : Fin 4 → ℝ) where
  r : ℝ
  r_ne : r ≠ 0
  length_ne : ∀ μ, ℓ μ ≠ 0
  length_eq : ∀ μ, ℓ' μ = r * ℓ μ
  mesh_eq : PeriodicLattice.meshSize L κ' = r * PeriodicLattice.meshSize L κ
namespace TorusScaling
variable {L : ℕ} {κ κ' : ℤ} {ℓ ℓ' : Fin 4 → ℝ} (A : TorusScaling L κ κ' ℓ ℓ')
include A in
private theorem length_ne' (μ : Fin 4) : ℓ' μ ≠ 0 := by
  rw [A.length_eq]
  exact mul_ne_zero A.r_ne (A.length_ne μ)
private def spaceEquiv : Space ℓ ≃+ Space ℓ' where
  toFun x μ := AddCircle.equivAddCircle (ℓ μ) (ℓ' μ) (A.length_ne μ) (A.length_ne' μ) (x μ)
  invFun y μ := (AddCircle.equivAddCircle (ℓ μ) (ℓ' μ) (A.length_ne μ) (A.length_ne' μ)).symm (y μ)
  left_inv _ := funext fun _ => AddEquiv.symm_apply_apply _ _
  right_inv _ := funext fun _ => AddEquiv.apply_symm_apply _ _
  map_add' _ _ := funext fun _ => map_add _ _ _
private theorem spaceEquiv_projection (x : Fin 4 → ℝ) :
    A.spaceEquiv (projection ℓ x) = projection ℓ' (A.r • x) := by
  funext μ
  change AddCircle.equivAddCircle (ℓ μ) (ℓ' μ) (A.length_ne μ) (A.length_ne' μ) ((x μ : ℝ) : AddCircle (ℓ μ)) =
    ((A.r * x μ : ℝ) : AddCircle (ℓ' μ))
  rw [AddCircle.equivAddCircle_apply_mk]
  congr 1
  have h := A.length_ne μ
  rw [A.length_eq μ]
  field_simp
private theorem smul_gridVector (n : Fin 4 → ℤ) :
    A.r • (fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L κ) =
      fun μ => (n μ : ℝ) * PeriodicLattice.meshSize L κ' := by
  funext μ
  simp only [Pi.smul_apply, smul_eq_mul, A.mesh_eq]
  ring
private theorem spaceEquiv_mem {x : Space ℓ} (hx : x ∈ gridSubgroup L κ ℓ) :
    A.spaceEquiv x ∈ gridSubgroup L κ' ℓ' := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨n, by rw [A.spaceEquiv_projection, A.smul_gridVector]⟩
private theorem spaceEquiv_symm_mem {y : Space ℓ'} (hy : y ∈ gridSubgroup L κ' ℓ') :
    A.spaceEquiv.symm y ∈ gridSubgroup L κ ℓ := by
  obtain ⟨n, rfl⟩ := hy
  refine ⟨n, ?_⟩
  rw [AddEquiv.symm_apply_eq, A.spaceEquiv_projection, A.smul_gridVector]
private def pointEquiv : GridPoint L κ ℓ ≃ GridPoint L κ' ℓ' where
  toFun x := ⟨A.spaceEquiv x, A.spaceEquiv_mem x.2⟩
  invFun y := ⟨A.spaceEquiv.symm y, A.spaceEquiv_symm_mem y.2⟩
  left_inv _ := Subtype.ext (A.spaceEquiv.symm_apply_apply _)
  right_inv _ := Subtype.ext (A.spaceEquiv.apply_symm_apply _)
private theorem pointEquiv_coe (x : GridPoint L κ ℓ) :
    ((A.pointEquiv x : GridPoint L κ' ℓ') : Space ℓ') = A.spaceEquiv x := rfl
private theorem pointEquiv_add (x y : GridPoint L κ ℓ) :
    A.pointEquiv (x + y) = A.pointEquiv x + A.pointEquiv y :=
  Subtype.ext (map_add A.spaceEquiv _ _)
private theorem spaceEquiv_stepVector (ν : Fin 4) (σ : ℝ) :
    A.spaceEquiv (projection ℓ ((σ * PeriodicLattice.meshSize L κ) • BoxTorus.basisVector ν)) =
      projection ℓ' ((σ * PeriodicLattice.meshSize L κ') • BoxTorus.basisVector ν) := by
  rw [A.spaceEquiv_projection, smul_smul, A.mesh_eq]
  congr 2
  ring
private theorem pointEquiv_gridStep (ν : Fin 4) :
    A.pointEquiv (gridStep L κ ℓ ν) = gridStep L κ' ℓ' ν := by
  apply Subtype.ext
  have h := A.spaceEquiv_stepVector ν 1
  simp only [one_mul] at h
  exact h
private theorem isNeighbourStep_iff (x x' : GridPoint L κ ℓ) (ν : Fin 4) (σ : ℝ) :
    IsNeighbourStep (A.pointEquiv x) (A.pointEquiv x') ν σ ↔ IsNeighbourStep x x' ν σ := by
  unfold IsNeighbourStep
  refine and_congr_right fun _ => ?_
  rw [A.pointEquiv_coe, A.pointEquiv_coe, BoxTorus.translate, BoxTorus.translate, ← A.spaceEquiv_stepVector, ← map_add]
  exact A.spaceEquiv.injective.eq_iff
private def edgeMap (b : DirectedEdge L κ ℓ) : DirectedEdge L κ' ℓ' where
  source := A.pointEquiv b.source
  target := A.pointEquiv b.target
  isNeighbour := by
    obtain ⟨ν, σ, h⟩ := b.isNeighbour
    exact ⟨ν, σ, (A.isNeighbourStep_iff _ _ _ _).mpr h⟩
private def edgeEquiv : DirectedEdge L κ ℓ ≃ DirectedEdge L κ' ℓ' where
  toFun := A.edgeMap
  invFun b' :=
    { source := A.pointEquiv.symm b'.source
      target := A.pointEquiv.symm b'.target
      isNeighbour := by
        obtain ⟨ν, σ, h⟩ := b'.isNeighbour
        refine ⟨ν, σ, (A.isNeighbourStep_iff _ _ _ _).mp ?_⟩
        simpa only [Equiv.apply_symm_apply] using h }
  left_inv b := DirectedEdge.ext (A.pointEquiv.symm_apply_apply _) (A.pointEquiv.symm_apply_apply _)
  right_inv b' := DirectedEdge.ext (A.pointEquiv.apply_symm_apply _) (A.pointEquiv.apply_symm_apply _)
private theorem isForward_iff (b : DirectedEdge L κ ℓ) :
    (A.edgeMap b).IsForward ↔ b.IsForward :=
  exists_congr fun _ => A.isNeighbourStep_iff _ _ _ _
private def forwardEquiv : ForwardEdge L κ ℓ ≃ ForwardEdge L κ' ℓ' :=
  A.edgeEquiv.subtypeEquiv fun b => (A.isForward_iff b).symm
private def pullField (U' : GaugeConfig L κ' ℓ') : GaugeConfig L κ ℓ := U' ∘ A.forwardEquiv
private theorem edgeVariable_pullField (U' : GaugeConfig L κ' ℓ') (b : DirectedEdge L κ ℓ) :
    edgeVariable (A.pullField U') b = edgeVariable U' (A.edgeMap b) := by
  unfold edgeVariable
  by_cases h : b.IsForward
  · rw [dif_pos h, dif_pos ((A.isForward_iff b).mpr h)]
    rfl
  · rw [dif_neg h, dif_neg (mt (A.isForward_iff b).mp h)]
    rfl
private theorem edgeMap_edgeFrom (x : GridPoint L κ ℓ) (ν : Fin 4) :
    A.edgeMap (edgeFrom x ν) = edgeFrom (A.pointEquiv x) ν :=
  DirectedEdge.ext rfl (by
    change A.pointEquiv (x + gridStep L κ ℓ ν) = A.pointEquiv x + gridStep L κ' ℓ' ν
    rw [A.pointEquiv_add, A.pointEquiv_gridStep])
private def faceEquiv : Face L κ ℓ ≃ Face L κ' ℓ' where
  toFun p := ⟨A.pointEquiv p.corner, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩
  invFun p' := ⟨A.pointEquiv.symm p'.corner, p'.dir₁, p'.dir₂, p'.dir₁_lt_dir₂⟩
  left_inv _ := Face.ext (A.pointEquiv.symm_apply_apply _) rfl rfl
  right_inv _ := Face.ext (A.pointEquiv.apply_symm_apply _) rfl rfl
private theorem faceHolonomy_pullField (U' : GaugeConfig L κ' ℓ') (p : Face L κ ℓ) :
    faceHolonomy (A.pullField U') p = faceHolonomy U' (A.faceEquiv p) := by
  simp only [faceHolonomy, edgeVariable_pullField, edgeMap_edgeFrom, pointEquiv_add, pointEquiv_gridStep]
  rfl
private theorem wilsonAction_pullField (U' : GaugeConfig L κ' ℓ') :
    wilsonAction (A.pullField U') = wilsonAction U' := by
  unfold wilsonAction
  rw [← finsum_comp_equiv A.faceEquiv]
  refine finsum_congr fun p => ?_
  simp only [faceEnergy, faceHolonomy_pullField]
private theorem integral_pullField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GaugeConfig L κ ℓ → E) :
    ∫ U, f U ∂haarConfigMeasure L κ ℓ =
      ∫ U', f (A.pullField U') ∂haarConfigMeasure L κ' ℓ' := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ => (Conventions.StandingParameters.gaugeGroup : Type)) A.forwardEquiv.symm)
      (haarConfigMeasure L κ' ℓ') (haarConfigMeasure L κ ℓ) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    unfold haarConfigMeasure Matrices.ComplexMatrix2.haarPi
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ => Matrices.ComplexMatrix2.haarProb) A.forwardEquiv.symm
  have hfun : ∀ U' : GaugeConfig L κ' ℓ',
      MeasurableEquiv.piCongrLeft (fun _ => (Conventions.StandingParameters.gaugeGroup : Type)) A.forwardEquiv.symm U' =
        A.pullField U' := by
    intro U'
    funext b
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => (Conventions.StandingParameters.gaugeGroup : Type))
      A.forwardEquiv.symm U' (A.forwardEquiv b)
    rw [Equiv.symm_apply_apply] at h
    exact h
  rw [← hmp.integral_comp' f]
  exact integral_congr_ae (Filter.Eventually.of_forall fun U' => congrArg f (hfun U'))
end TorusScaling
section Groups
variable {D : ChessboardSetup} (S : ScalingMap D) (P : PeriodSubgroup D) (P' : PeriodSubgroup S.image)
private def scalingOf (hs : ∀ μ, P'.mult μ = P.mult μ) :
    TorusScaling D.L ((D.K : ℕ) : ℤ) ((S.image.K : ℕ) : ℤ) P.sideLengths P'.sideLengths where
  r := S.scale
  r_ne := S.scale_pos.ne'
  length_ne μ := by
    have h4 : (4 : ℝ) ≤ (P.mult μ : ℝ) := by exact_mod_cast P.four_le_mult μ
    exact mul_ne_zero (by linarith) D.mesh_pos.ne'
  length_eq μ := by
    change ((P'.mult μ : ℤ) : ℝ) * S.image.mesh = S.scale * (((P.mult μ : ℤ) : ℝ) * D.mesh)
    rw [hs, S.image_mesh]
    ring
  mesh_eq := S.image_mesh
private theorem periodAction_pullField (hs : ∀ μ, P'.mult μ = P.mult μ) (U' : P'.GaugeConfig) :
    P.wilsonAction ((scalingOf S P P' hs).pullField U') = P'.wilsonAction U' :=
  (scalingOf S P P' hs).wilsonAction_pullField U'
private theorem liftGaugeField_pullField (hq : ProjOnEdgesAndFaces.Statement)
    (hv : S.shift = 0) (hs : ∀ μ, P'.mult μ = P.mult μ) (U' : P'.GaugeConfig) :
    P.liftGaugeField ((scalingOf S P P' hs).pullField U') =
      S.pullback (P'.liftGaugeField U') := by
  have h := (hq D P).2.2.1 ((scalingOf S P P' hs).pullField U')
  have h' := (hq S.image P').2.2.1 U'
  have e₁ : P.liftGaugeField ((scalingOf S P P' hs).pullField U') =
      ⟨P.liftField ((scalingOf S P P' hs).pullField U'), h⟩ := dif_pos h
  have e₂ : P'.liftGaugeField U' = ⟨P'.liftField U', h'⟩ := dif_pos h'
  rw [e₁, e₂]
  apply Subtype.ext
  funext b
  change BoxTorus.edgeVariable ((scalingOf S P P' hs).pullField U') (P.projEdge b) =
    BoxTorus.edgeVariable U' (P'.projEdge (S.linkMap b))
  refine ((scalingOf S P P' hs).edgeVariable_pullField U' (P.projEdge b)).trans
    (congrArg (BoxTorus.edgeVariable U') ?_)
  have hpoint : ∀ x : InfiniteLattice.LatticePoint D.mesh,
      (scalingOf S P P' hs).pointEquiv (P.projPoint x) = P'.projPoint (S.pointMap x) := by
    intro x
    apply Subtype.ext
    change (scalingOf S P P' hs).spaceEquiv (BoxTorus.projection P.sideLengths x) =
      BoxTorus.projection P'.sideLengths (S.toFun x)
    rw [TorusScaling.spaceEquiv_projection]
    congr 1
    funext μ
    simp [ScalingMap.toFun, hv, scalingOf]
  exact DirectedEdge.ext (hpoint _) (hpoint _)
end Groups
private theorem cellRatio_gridImage {D : ChessboardSetup} (S : ScalingMap D) (g : ReflectionGrid D) :
    (S.gridImage g).cellRatio = g.cellRatio := by
  have h : (S.gridImage g).q + (((S.image.K : ℕ+) : ℕ) : ℤ) = g.q + ((D.K : ℕ) : ℤ) := by
    have hb := S.power_lt
    change g.q + (S.power : ℤ) + (((D.K : ℕ) - S.power : ℕ) : ℤ) = g.q + ((D.K : ℕ) : ℤ)
    omega
  unfold ReflectionGrid.cellRatio
  rw [h]
  rfl
theorem similarityPreservesTiledIntegral_holds (hSim : MirrorGridsAllSides.ScalingMapTheorem)
    (hq : ProjOnEdgesAndFaces.Statement) :
    SimilarityPreservesTiledIntegral := by
  intro D g hg hneg
  have hK := g.one_sub_K_le_q
  let S : ScalingMap D :=
    ⟨(-g.q).toNat, by omega, 0, (D.gridPoints).zero_mem⟩
  have hb : (S.power : ℤ) = -g.q := Int.toNat_of_nonneg (by omega)
  have hv : S.shift = 0 := rfl
  obtain ⟨-, -, -, -, hSO, hgrid⟩ := hSim D S
  obtain ⟨hside, -, ⟨hcg, hcf⟩, -⟩ := hgrid g hg
  have hs : ∀ n : EvenIndexVector, ∀ μ,
      (gridPeriods (S.gridImage g) n).mult μ = (gridPeriods g n).mult μ := by
    intro n μ
    change n.coord μ * (S.gridImage g).cellRatio = n.coord μ * g.cellRatio
    rw [cellRatio_gridImage]
  refine ⟨S.image, S.gridImage g, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ g.q + (S.power : ℤ)
    omega
  · change S.image.IsAdmissibleSide (S.gridImage g).cellSide
    rw [hside]
    exact (hSO.1 g.cellSide hg).1
  · intro n
    unfold torusPartition
    change ∫ U, Real.exp (-D.β * BoxTorus.wilsonAction U) ∂(BoxTorus.haarConfigMeasure _ _ _) =
      ∫ U, Real.exp (-D.β * BoxTorus.wilsonAction U) ∂(BoxTorus.haarConfigMeasure _ _ _)
    rw [(scalingOf S (gridPeriods g n) (gridPeriods (S.gridImage g) n) (hs n)).integral_pullField]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
    change Real.exp (-D.β * BoxTorus.wilsonAction _) = Real.exp (-D.β * BoxTorus.wilsonAction U')
    rw [TorusScaling.wilsonAction_pullField]
  · rintro _ ⟨k₀, rfl⟩
    refine ⟨S.toFun '' g.cell k₀, ⟨k₀, (hcg.1 k₀).symm⟩, fun F => F ∘ S.pullback, ?_⟩
    intro F hF
    refine ⟨?_, ?_⟩
    · rw [← hcf.1 _ ⟨k₀, rfl⟩]
      exact ⟨F, hF, rfl⟩
    · intro n
      unfold tiledIntegral
      change ∫ U, _ ∂(BoxTorus.haarConfigMeasure _ _ _) =
        ∫ U, _ ∂(BoxTorus.haarConfigMeasure _ _ _)
      rw [(scalingOf S (gridPeriods g n) (gridPeriods (S.gridImage g) n) (hs n)).integral_pullField]
      refine integral_congr_ae (Filter.Eventually.of_forall fun U' => ?_)
      have hact := periodAction_pullField S (gridPeriods g n) (gridPeriods (S.gridImage g) n) (hs n) U'
      have hext := liftGaugeField_pullField S (gridPeriods g n) (gridPeriods (S.gridImage g) n) hq hv (hs n) U'
      have hprod : ∀ k, g.transportTo (g.cell k₀) (g.cell k) F
            ((gridPeriods g n).liftGaugeField
              ((scalingOf S (gridPeriods g n) (gridPeriods (S.gridImage g) n) (hs n)).pullField U')) =
          (S.gridImage g).transportTo (S.toFun '' g.cell k₀) ((S.gridImage g).cell k)
            (F ∘ S.pullback) ((gridPeriods (S.gridImage g) n).liftGaugeField U') := by
        intro k
        rw [hext, ← hcg.1 k, ← hcf.2 _ ⟨k₀, rfl⟩ _ ⟨k, rfl⟩ F hF]
        rfl
      change (∏ k ∈ n.indexBox, _) * Complex.exp (-(D.β : ℂ) * ((gridPeriods g n).wilsonAction _ : ℂ)) =
        (∏ k ∈ n.indexBox, _) * Complex.exp (-(D.β : ℂ) * ((gridPeriods (S.gridImage g) n).wilsonAction U' : ℂ))
      rw [hact]
      congr 1
      exact Finset.prod_congr rfl fun k _ => hprod k
end YangMills.Construction.ReflectedCopies
end
