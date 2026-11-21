import YangMills.Construction.Continuum.DistributionsOnOpenSetsOfPowersOfFourSpace
import YangMills.Construction.Continuum.TensorProductOfDistributions
import YangMills.Construction.Torus.ProductOfDistributionsOverTheBlocksOfAPartition
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Continuum.BlockProducts
open TopologicalSpace YangMills.Construction.ReflectionSpaces.Euclidean YangMills.Construction.SetPartition YangMills.Construction.AmbientPoints YangMills.Construction.Continuum.TensorProduct
def pointCoordEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))
def pointAt {n : ℕ} (x : Coord (4 * n)) (i : Fin n) : Fin 4 → ℝ :=
  fun μ => x (pointCoordEquiv n (i, μ))
theorem continuous_pointAt {n : ℕ} (i : Fin n) :
    Continuous fun x : Coord (4 * n) => pointAt x i :=
  continuous_pi fun _ => continuous_apply _
def configSpace (n : ℕ) : Opens (Coord (4 * n)) where
  carrier := {x | pointAt x ∈ YangMills.Construction.TestFunctions.injectiveTuples (Fin 4 → ℝ) n}
  is_open' := (YangMills.Construction.Distributions.isOpen_injectiveTuples n).preimage
    (continuous_pi continuous_pointAt)
abbrev DistribFamily : Type := ∀ n : ℕ, 2 ≤ n → Distribution (configSpace n)
variable {Q : ℕ} (P : PartitionsFin Q)
def blockMemberCoordsEquiv :
    (Σ i : Fin (blockCount P), Fin (orderedBlockCard P i) × Fin 4) ≃
      (Σ i : Fin (blockCount P), Fin (orderedBlockCard P i)) × Fin 4 where
  toFun z := (⟨z.1, z.2.1⟩, z.2.2)
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def blockCoordEquiv : Fin (∑ i, 4 * orderedBlockCard P i) ≃ Fin (4 * Q) :=
  finSigmaFinEquiv.symm.trans <|
    (Equiv.sigmaCongrRight fun i => (pointCoordEquiv (orderedBlockCard P i)).symm).trans <|
      (blockMemberCoordsEquiv P).trans <|
        ((Equiv.ofBijective _ (blockMemberIndex_bijective P)).prodCongr (Equiv.refl _)).trans
          (pointCoordEquiv Q)
def regroup : Coord (4 * Q) ≃ₜ Coord (∑ i, 4 * orderedBlockCard P i) where
  toFun x := x ∘ blockCoordEquiv P
  invFun y := y ∘ (blockCoordEquiv P).symm
  left_inv x := by
    funext k
    simp
  right_inv y := by
    funext k
    simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _
theorem pointAt_blockComponent_regroup (x : Coord (4 * Q))
    (i : Fin (blockCount P)) (a : Fin (orderedBlockCard P i)) :
    pointAt
        (blockComponent (fun i => 4 * orderedBlockCard P i) (regroup P x) i) a =
      pointAt x (blockMemberIndex P ⟨i, a⟩) := by
  funext μ
  simp [pointAt, blockComponent, regroup, blockCoordEquiv, blockMemberCoordsEquiv]
def distinctWithinBlocks : Opens (Coord (4 * Q)) where
  carrier := {x | ∀ B ∈ P.parts, ∀ l ∈ B, ∀ l' ∈ B, l ≠ l' →
    pointAt x l ≠ pointAt x l'}
  is_open' := by
    simp only [Set.ofPred_forall]
    refine isOpen_biInter_finset fun B _ => isOpen_iInter_of_finite fun l =>
      isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun l' =>
        isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => ?_
    exact isOpen_ne_fun (continuous_pointAt l) (continuous_pointAt l')
theorem configSpace_le_distinctWithinBlocks : configSpace Q ≤ distinctWithinBlocks P :=
  fun _ hx _ _ _ _ _ _ hne heq => hne (hx heq)
abbrev blockConfigProd : Opens (Coord (∑ i, 4 * orderedBlockCard P i)) :=
  prodOpens (fun i => 4 * orderedBlockCard P i) fun i => configSpace (orderedBlockCard P i)
theorem regroup_mem_blockConfigProd_iff (x : Coord (4 * Q)) :
    regroup P x ∈ blockConfigProd P ↔ x ∈ distinctWithinBlocks P := by
  constructor
  · intro h B hB l hl l' hl' hne heq
    obtain ⟨i, rfl⟩ := exists_orderedBlock_eq P hB
    have hr : ∀ {k}, k ∈ orderedBlock P i → ∃ a, blockMemberIndex P ⟨i, a⟩ = k := fun {k} hk => by
      have : k ∈ Set.range ((orderedBlock P i).orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hk
      exact this
    obtain ⟨a, rfl⟩ := hr hl
    obtain ⟨a', rfl⟩ := hr hl'
    have hinj : Function.Injective
        (pointAt (blockComponent (fun i => 4 * orderedBlockCard P i) (regroup P x) i)) := h i
    refine hne (congrArg _ (congrArg _ (hinj ?_)))
    rw [pointAt_blockComponent_regroup, pointAt_blockComponent_regroup]
    exact heq
  · intro h i a a' heq
    rw [pointAt_blockComponent_regroup,
      pointAt_blockComponent_regroup] at heq
    by_contra hne
    refine h _ (orderedBlock_mem P i) _ (Finset.orderEmbOfFin_mem _ rfl a) _
      (Finset.orderEmbOfFin_mem _ rfl a') (fun hl => hne ?_) heq
    exact ((orderedBlock P i).orderEmbOfFin rfl).injective hl
theorem comp_regroup_symm_mem {f : Coord (4 * Q) → ℂ}
    (hf : f ∈ testFunctionSpace (distinctWithinBlocks P)) :
    f ∘ (regroup P).symm ∈ testFunctionSpace (blockConfigProd P) := by
  obtain ⟨hs, hc, hW⟩ := hf
  refine ⟨hs.comp (contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _), hc.comp_homeomorph _, ?_⟩
  rw [tsupport_comp_eq_preimage]
  intro y hy
  have h := (regroup_mem_blockConfigProd_iff P ((regroup P).symm y)).2 (hW hy)
  simpa using h
def regroupTest :
    testFunctionSpace (distinctWithinBlocks P) →ₗ[ℂ] testFunctionSpace (blockConfigProd P) where
  toFun f := ⟨f.1 ∘ (regroup P).symm, comp_regroup_symm_mem P f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {P}
theorem two_le_orderedBlockCard (hP : P ∈ nonSingletonPartitions Q) (i : Fin (blockCount P)) :
    2 ≤ orderedBlockCard P i :=
  (Finset.mem_filter.1 hP).2 _ (orderedBlock_mem P i)
def partitionForm (u : DistribFamily) (hP : P ∈ nonSingletonPartitions Q) :
    Module.Dual ℂ (testFunctionSpace (distinctWithinBlocks P)) :=
  (tensorDist fun i => u (orderedBlockCard P i) (two_le_orderedBlockCard hP i)).form ∘ₗ regroupTest P
def assembledForm (Q : ℕ) (u : DistribFamily) :
    Module.Dual ℂ (testFunctionSpace (configSpace Q)) :=
  ∑ P ∈ (nonSingletonPartitions Q).attach,
    partitionForm u P.2 ∘ₗ inclusionMap (configSpace_le_distinctWithinBlocks P.1)
def assembledFormZero : ℂ →ₗ[ℂ] ℂ := LinearMap.id
end YangMills.Construction.Continuum.BlockProducts
end
