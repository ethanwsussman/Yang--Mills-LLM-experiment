import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJetsProof
import YangMills.Construction.PeriodicOperators.BlockMatricesOfLocalOperatorFunctionsAndOfJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJetProof
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheBonds
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RescaledEdgeSaddleJetProof
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad (EqAsJet IsJet)
section EqualJets
variable {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
theorem eqAsJet_refl (T : JetQuad I I') : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_of_eq {T S : JetQuad I I'} (h : T = S) : EqAsJet δ p T S := by
  rw [h]
  exact eqAsJet_refl _
theorem eqAsJet_trans {T S R : JetQuad I I'} (h : EqAsJet δ p T S) (h' : EqAsJet δ p S R) :
    EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
theorem eqAsJet_add {T T' S S' : JetQuad I I'} (h : EqAsJet δ p T T') (h' : EqAsJet δ p S S') :
    EqAsJet δ p (T.add S) (T'.add S') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_add <;> assumption
theorem eqAsJet_smul (z : ℂ) {T T' : JetQuad I I'} (h : EqAsJet δ p T T') :
    EqAsJet δ p (JetQuad.smul z T) (JetQuad.smul z T') := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.eqAsJet_smul <;> assumption
theorem eqAsJet_blockJet (J : Fin 2 → PeriodicData) {T S : ∀ i j, JetQuad (J j) (J i)}
    (h : ∀ i j, EqAsJet δ p (T i j) (S i j)) :
    EqAsJet δ p (blockJet J T) (blockJet J S) :=
  ⟨fun _ hκ => congrArg (blockQuotHom J) (funext fun i => funext fun j => (h i j).1 hκ),
    fun _ hκ => congrArg (blockQuotHom J) (funext fun i => funext fun j => (h i j).2.1 hκ),
    fun _ hκ => congrArg (blockQuotHom J) (funext fun i => funext fun j => (h i j).2.2.1 hκ),
    fun _ hκ => congrArg (blockQuotHom J) (funext fun i => funext fun j => (h i j).2.2.2 hκ)⟩
theorem add_add_neg_sub_cancel (K A M : JetQuad I I) :
    (K.add (A.add (JetQuad.smul (-1) M))).add (JetQuad.smul (-1) A) =
      K.add (JetQuad.smul (-1) M) := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [JetQuad.add, JetQuad.smul, Pi.add_apply, Pi.smul_apply] <;> module
theorem smul_zero_eq_zeroJet (T : JetQuad I I') : JetQuad.smul 0 T = JetQuad.zeroJet I I' := by
  apply JetQuad.ext <;> funext κ <;>
    simp [JetQuad.smul, JetQuad.zeroJet]
end EqualJets
section Generic
variable {F B₀ B S₀ S : PeriodicData}
def saddleBlocks (X : (F.Carrier → ℂ) → B₀.Carrier → B₀.Carrier → ℂ)
    (Qt : (F.Carrier → ℂ) → B₀.Carrier → B.Carrier → ℂ)
    (Q : (F.Carrier → ℂ) → B.Carrier → B₀.Carrier → ℂ)
    (Z : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) :
    ∀ i j : Fin 2, (F.Carrier → ℂ) → (pairData B₀ B i).Carrier → (pairData B₀ B j).Carrier → ℂ
  | 0, 0 => X
  | 0, 1 => Qt
  | 1, 0 => Q
  | 1, 1 => Z
theorem gram_sandwich_local_and_jet
    (hL : JetDomains.OpFunJetTheory) (hC : JetCalculus.Claim)
    (hA : JetArgumentsAndEqualJets)
    (hF : IsPeriodic F) (hB₀ : IsPeriodic B₀) (hS₀ : IsPeriodic S₀)
    (hS : IsPeriodic S) {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    (a b : F.UnitQuot → ℂ)
    (D : (F.Carrier → ℂ) → B₀.Carrier → S₀.Carrier → ℂ)
    (R : (F.Carrier → ℂ) → S.Carrier → S₀.Carrier → ℂ)
    (hD : IsLocalOpFun F S₀ B₀ D) (hR : IsLocalOpFun F S₀ S R) :
    IsLocalOpFun F B₀ B₀
        (opFunComp (opFunComp D (opFunTranspose R)) (opFunComp R (opFunTranspose D))) ∧
      EqAsJet δ p
        (jetAlong F B₀ B₀
          (opFunComp (opFunComp D (opFunTranspose R)) (opFunComp R (opFunTranspose D)))
          p a b)
        (JetQuad.mul p
          (JetQuad.mul p (jetAlong F S₀ B₀ D p a b)
            (JetQuad.mul p (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))
              (jetAlong F S₀ S R p a b)))
          (JetQuad.transposeAt p (jetAlong F S₀ B₀ D p a b))) := by
  obtain ⟨hProd, -, hJ, -⟩ := hC δ p hδ hp
  have hd : IsJet δ p (jetAlong F S₀ B₀ D p a b) :=
    (hL.2.1 F S₀ B₀ hF hS₀ hB₀ D hD).isJet δ hδ p hp a b
  have hr : IsJet δ p (jetAlong F S₀ S R p a b) :=
    (hL.2.1 F S₀ S hF hS₀ hS R hR).isJet δ hδ p hp a b
  have hdt : IsJet δ p (JetQuad.transposeAt p (jetAlong F S₀ B₀ D p a b)) :=
    (hL.2.2 S₀ B₀ B₀ hS₀ hB₀ hB₀ δ p hδ hp).transpose_isJet _ hd
  have hrt : IsJet δ p (JetQuad.transposeAt p (jetAlong F S₀ S R p a b)) :=
    (hL.2.2 S₀ S S hS₀ hS hS δ p hδ hp).transpose_isJet _ hr
  have lRt : IsLocalOpFun F S S₀ (opFunTranspose R) :=
    ((hL.1 F S₀ S S hF hS₀ hS hS).2.2) R hR
  have lDt : IsLocalOpFun F B₀ S₀ (opFunTranspose D) :=
    ((hL.1 F S₀ B₀ B₀ hF hS₀ hB₀ hB₀).2.2) D hD
  have lDR : IsLocalOpFun F S B₀ (opFunComp D (opFunTranspose R)) :=
    ((hL.1 F S₀ B₀ S hF hS₀ hB₀ hS).2.1) D _ hD lRt
  have lRD : IsLocalOpFun F B₀ S (opFunComp R (opFunTranspose D)) :=
    ((hL.1 F S₀ S B₀ hF hS₀ hS hB₀).2.1) R _ hR lDt
  have lW := ((hL.1 F S B₀ B₀ hF hS hB₀ hB₀).2.1) _ _ lDR lRD
  refine ⟨lW, ?_⟩
  have jRt := (hJ F S S₀ S hF hS hS₀ hS a b).2.2 R hR
  have jDt := (hJ F B₀ S₀ S hF hB₀ hS₀ hS a b).2.2 D hD
  have jDR := (hJ F B₀ S₀ S hF hB₀ hS₀ hS a b).2.1 D _ hD lRt
  have jRD := (hJ F S S₀ B₀ hF hS hS₀ hB₀ a b).2.1 R _ hR lDt
  have jW := (hJ F B₀ S B₀ hF hB₀ hS hB₀ a b).2.1 _ _ lDR lRD
  have hjRt : IsJet δ p (jetAlong F S S₀ (opFunTranspose R) p a b) :=
    (hL.2.1 F S S₀ hF hS hS₀ _ lRt).isJet δ hδ p hp a b
  have hjDt : IsJet δ p (jetAlong F B₀ S₀ (opFunTranspose D) p a b) :=
    (hL.2.1 F B₀ S₀ hF hB₀ hS₀ _ lDt).isJet δ hδ p hp a b
  have hjDR : IsJet δ p (jetAlong F S B₀ (opFunComp D (opFunTranspose R)) p a b) :=
    (hL.2.1 F S B₀ hF hS hB₀ _ lDR).isJet δ hδ p hp a b
  have hjRD : IsJet δ p (jetAlong F B₀ S (opFunComp R (opFunTranspose D)) p a b) :=
    (hL.2.1 F B₀ S hF hB₀ hS _ lRD).isJet δ hδ p hp a b
  have mDR : IsJet δ p (JetQuad.mul p (jetAlong F S₀ B₀ D p a b)
      (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))) :=
    (hL.2.2 S₀ B₀ S hS₀ hB₀ hS δ p hδ hp).mul_isJet _ _ hd hrt
  have mRD : IsJet δ p (JetQuad.mul p (jetAlong F S₀ S R p a b)
      (JetQuad.transposeAt p (jetAlong F S₀ B₀ D p a b))) :=
    (hL.2.2 S₀ S B₀ hS₀ hS hB₀ δ p hδ hp).mul_isJet _ _ hr hdt
  have mRR : IsJet δ p (JetQuad.mul p (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))
      (jetAlong F S₀ S R p a b)) :=
    (hL.2.2 S S₀ S₀ hS hS₀ hS₀ δ p hδ hp).mul_isJet _ _ hrt hr
  have mDRR : IsJet δ p (JetQuad.mul p (JetQuad.mul p (jetAlong F S₀ B₀ D p a b)
      (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))) (jetAlong F S₀ S R p a b)) :=
    (hL.2.2 S B₀ S₀ hS hB₀ hS₀ δ p hδ hp).mul_isJet _ _ mDR hr
  have mDRR' : IsJet δ p (JetQuad.mul p (jetAlong F S₀ B₀ D p a b)
      (JetQuad.mul p (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))
        (jetAlong F S₀ S R p a b))) :=
    (hL.2.2 S₀ B₀ S₀ hS₀ hB₀ hS₀ δ p hδ hp).mul_isJet _ _ hd mRR
  have eDR := ((hA.2.1 δ p S₀ B₀ hS₀ hB₀ _ _ hd hd (eqAsJet_refl _)).2.2.2.2 S hS _ _ hjRt hrt jRt)
  have eRD := ((hA.2.1 δ p S₀ S hS₀ hS _ _ hr hr (eqAsJet_refl _)).2.2.2.2 B₀ hB₀ _ _ hjDt hdt jDt)
  have eDR' := eqAsJet_trans jDR eDR
  have eRD' := eqAsJet_trans jRD eRD
  have e1 := (hA.2.1 δ p S B₀ hS hB₀ _ _ hjDR mDR eDR').2.2.2.2 B₀ hB₀ _ _ hjRD mRD eRD'
  have a1 := ((hProd B₀ S S₀ B₀ hB₀ hS hS₀ hB₀ _ _ _ mDR hr hdt).1)
  have a2 := ((hProd B₀ S₀ S S₀ hB₀ hS₀ hS hS₀ _ _ _ hd hrt hr).1)
  have e2 := (hA.2.1 δ p S₀ B₀ hS₀ hB₀ _ _ mDRR mDRR' a2).2.2.2.2 B₀ hB₀ _ _ hdt hdt (eqAsJet_refl _)
  refine eqAsJet_trans jW (eqAsJet_trans e1 (eqAsJet_trans ?_ e2))
  exact ⟨a1.1.symm, a1.2.1.symm, a1.2.2.1.symm, a1.2.2.2.symm⟩
theorem saddleBlocks_local_and_jet
    (hL : JetDomains.OpFunJetTheory) (hC : JetCalculus.Claim)
    (hA : JetArgumentsAndEqualJets)
    (hBl : BlockJets.AllConditions)
    (hF : IsPeriodic F) (hB₀ : IsPeriodic B₀) (hB : IsPeriodic B)
    (hS₀ : IsPeriodic S₀) (hS : IsPeriodic S)
    {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) (a b : F.UnitQuot → ℂ)
    (K : (F.Carrier → ℂ) → B₀.Carrier → B₀.Carrier → ℂ)
    (D : (F.Carrier → ℂ) → B₀.Carrier → S₀.Carrier → ℂ)
    (R : (F.Carrier → ℂ) → S.Carrier → S₀.Carrier → ℂ)
    (Q : (F.Carrier → ℂ) → B.Carrier → B₀.Carrier → ℂ)
    (hK : IsLocalOpFun F B₀ B₀ K) (hD : IsLocalOpFun F S₀ B₀ D)
    (hR : IsLocalOpFun F S₀ S R) (hQ : IsLocalOpFun F B₀ B Q) :
    IsLocalOpFun F (PeriodicData.sigma (pairData B₀ B)) (PeriodicData.sigma (pairData B₀ B))
        (blockKernelFun (pairData B₀ B)
          (saddleBlocks
            (opFunAdd K fun ζ => (-1 : ℂ) •
              opFunComp (opFunComp D (opFunTranspose R))
                (opFunComp R (opFunTranspose D)) ζ)
            (opFunTranspose Q) Q fun _ _ _ => 0)) ∧
      EqAsJet δ p
        (jetAlong F (PeriodicData.sigma (pairData B₀ B)) (PeriodicData.sigma (pairData B₀ B))
          (blockKernelFun (pairData B₀ B)
            (saddleBlocks
              (opFunAdd K fun ζ => (-1 : ℂ) •
                opFunComp (opFunComp D (opFunTranspose R))
                  (opFunComp R (opFunTranspose D)) ζ)
              (opFunTranspose Q) Q fun _ _ _ => 0)) p a b)
        (saddleJet p
          (subGramJet p
            ((jetAlong F B₀ B₀ K p a b).add
              ((JetQuad.mul p (JetQuad.transposeAt p (jetAlong F B₀ B Q p a b))
                  (jetAlong F B₀ B Q p a b)).add
                (JetQuad.smul (-1)
                  (JetQuad.mul p
                    (JetQuad.mul p (jetAlong F S₀ B₀ D p a b)
                      (JetQuad.mul p (JetQuad.transposeAt p (jetAlong F S₀ S R p a b))
                        (jetAlong F S₀ S R p a b)))
                    (JetQuad.transposeAt p (jetAlong F S₀ B₀ D p a b))))))
            (jetAlong F B₀ B Q p a b))
          (jetAlong F B₀ B Q p a b)) := by
  obtain ⟨-, -, hJ, -⟩ := hC δ p hδ hp
  obtain ⟨hMult, hBlock, -⟩ := hBl.2 F hF δ p hδ hp a b
  have hPair : ∀ i, IsPeriodic (pairData B₀ B i) := fun i =>
    match i with
    | 0 => hB₀
    | 1 => hB
  obtain ⟨-, -, hBF⟩ := hBlock _ hPair
  obtain ⟨lW, jW⟩ := gram_sandwich_local_and_jet hL hC hA hF hB₀ hS₀ hS hδ hp a b D R hD hR
  obtain ⟨lcW, jcW⟩ := hMult B₀ B₀ hB₀ hB₀ _ lW (-1)
  have lX := ((hL.1 F B₀ B₀ B₀ hF hB₀ hB₀ hB₀).1) K _ hK lcW
  have jX := (hJ F B₀ B₀ B₀ hF hB₀ hB₀ hB₀ a b).1 K _ hK lcW
  have lQt : IsLocalOpFun F B B₀ (opFunTranspose Q) :=
    ((hL.1 F B₀ B B hF hB₀ hB hB).2.2) Q hQ
  have jQt := (hJ F B B₀ B hF hB hB₀ hB a b).2.2 Q hQ
  have lQQ : IsLocalOpFun F B B (opFunComp Q (opFunTranspose Q)) :=
    ((hL.1 F B₀ B B hF hB₀ hB hB).2.1) Q _ hQ lQt
  obtain ⟨lZ, jZ⟩ := hMult B B hB hB _ lQQ 0
  have zeroFn : (fun ζ => (0 : ℂ) • opFunComp Q (opFunTranspose Q) ζ) =
      (fun _ _ _ => 0 : (F.Carrier → ℂ) → B.Carrier → B.Carrier → ℂ) := by
    funext ζ ι' ι
    simp
  rw [zeroFn, smul_zero_eq_zeroJet] at jZ
  rw [zeroFn] at lZ
  obtain ⟨lBlock, jBlock⟩ := hBF
    (saddleBlocks
      (opFunAdd K fun ζ => (-1 : ℂ) •
        opFunComp (opFunComp D (opFunTranspose R)) (opFunComp R (opFunTranspose D)) ζ)
      (opFunTranspose Q) Q fun _ _ _ => 0)
    (fun i j => match i, j with
      | 0, 0 => lX
      | 0, 1 => lQt
      | 1, 0 => hQ
      | 1, 1 => lZ)
  refine ⟨lBlock, eqAsJet_trans jBlock (eqAsJet_blockJet _ fun i j => ?_)⟩
  match i, j with
  | 0, 0 =>
    refine eqAsJet_trans jX (eqAsJet_trans (eqAsJet_add (eqAsJet_refl _)
      (eqAsJet_trans jcW (eqAsJet_smul _ jW))) ?_)
    exact eqAsJet_of_eq (add_add_neg_sub_cancel (I := B₀) _ _ _).symm
  | 0, 1 => exact jQt
  | 1, 0 => exact eqAsJet_refl _
  | 1, 1 => exact jZ
end Generic
abbrev edgeOperatorFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).K
abbrev gradientFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k 0).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).D
abbrev vertexMeanFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R
abbrev edgeMeanFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourEdges L k k).Carrier → (colourEdges L k 0).Carrier → ℂ :=
  fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q
theorem rescaledEdgeSaddleJet_holds
    (hL : JetDomains.OpFunJetTheory) (hC : JetCalculus.Claim)
    (hA : JetArgumentsAndEqualJets)
    (hBl : BlockJets.AllConditions)
    (hO : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hI : IteratedSmallFieldMeans.IteratedMeansClaim) : RescaledEdgeSaddleJet := by
  intro L hs k hk
  obtain ⟨hOp, -⟩ := hO.1 L hs k hk
  obtain ⟨hS₀, hB₀, -, hS, hB⟩ := hOp.periodic
  have hK := hOp.K_local.1
  have hD := hOp.D_local.1
  have hQ : IsLocalOpFun (remainderIndex L k) (colourEdges L k 0)
      (colourEdges L k k) (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).Q) := by
    obtain ⟨ρ, R, h, -⟩ := hOp.Q_local _ _ (hI.1 L hs)
    exact ⟨ρ, R, h⟩
  have hR : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) (fun ζ => (rescaledOperators L k (gaugeFieldOfForm L k ζ)).R) := by
    obtain ⟨ρ, R, h, -⟩ := hOp.R_local _ _ (hI.1 L hs)
    exact ⟨ρ, R, h⟩
  have evalOnSigma : readOnSigma (rescaledEdgeSaddle L k) =
      blockKernelFun (pairData (colourEdges L k 0) (colourEdges L k k))
        (saddleBlocks
          (opFunAdd (edgeOperatorFun L k) fun ζ => (-1 : ℂ) •
            opFunComp
              (opFunComp (gradientFun L k) (opFunTranspose (vertexMeanFun L k)))
              (opFunComp (vertexMeanFun L k) (opFunTranspose (gradientFun L k))) ζ)
          (opFunTranspose (edgeMeanFun L k)) (edgeMeanFun L k)
          fun _ _ _ => 0) := by
    funext ζ ι' ι
    obtain ⟨i, x⟩ := ι'
    obtain ⟨j, y⟩ := ι
    revert x y
    match i, j with
    | 0, 0 =>
      intro x y
      show (rescaledOperators L k (gaugeFieldOfForm L k ζ)).X x y = _
      have hX : ∀ P : RescaledOperators (Vertex L k 0) (PositiveEdge (meshAt L k 0))
          (Vertex L k k) (PositiveEdge (meshAt L k k)),
          P.X = P.K + (-1 : ℂ) • compKernel (compKernel P.D P.Rt) (compKernel P.R P.Dt) := by
        intro P
        funext ι' ι
        show (P.K - compKernel (compKernel P.D P.Rt) (compKernel P.R P.Dt) +
          compKernel P.Qt P.Q - compKernel P.Qt P.Q) ι' ι = _
        rw [add_sub_cancel_right]
        simp [sub_eq_add_neg]
      rw [hX]
      rfl
    | 0, 1 => intro x y; rfl
    | 1, 0 => intro x y; rfl
    | 1, 1 => intro x y; rfl
  rw [evalOnSigma]
  have main := fun (δ : ℝ) (p : Fin 4 → ℂ) (hδ : 0 < δ) (hp : p ∈ imStrip δ)
      (a b : (remainderIndex L k).UnitQuot → ℂ) =>
    saddleBlocks_local_and_jet hL hC hA hBl hB₀ hB₀ hB hS₀ hS hδ hp a b _ _ _ _ hK hD hR hQ
  refine ⟨(main 1 0 one_pos (fun μ => by simp [zero_le_one]) 0 0).1, ?_⟩
  intro δ p μPlus μMinus hδ hp
  exact (main δ p hδ hp _ _).2
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RescaledEdgeSaddleJetProof
end
