import YangMills.Construction.Averaging.EverySmallRadiusServesProof
import YangMills.Construction.SourcesAndGluing.ConfigurationsUnderLatticeSimilaritiesOfTori
import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.ScalingOfLatticeSimilaritiesOfTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusLifts TorusMetric Matrices
namespace SourcesAndGluing.FieldsUnderScaledMotionsOfTori
open PeriodicLattice (Bond Plaquette plaquetteHolonomy)
section Matrices
variable {g : ComplexMatrix2}
theorem inv_eq_star_of_mem (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    g⁻¹ = star g := by apply _root_.YangMills.Construction.Averaging.SmallRadiusProof.inv_eq_star_of_mem_specialUnitary <;> assumption
theorem inv_mem_specialUnitary (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    g⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p33390 <;> assumption
theorem inv_inv_of_mem_specialUnitary
    (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : g⁻¹⁻¹ = g := by apply _root_.YangMills.Construction.Averaging.SmallFieldAnalyticity.inv_inv_of_mem_specialUnitary <;> assumption
theorem re_fullTrace_inv (hg : g ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    (ComplexMatrix2.fullTrace g⁻¹).re = (ComplexMatrix2.fullTrace g).re := by
  rw [inv_eq_star_of_mem hg, Matrix.star_eq_conjTranspose, ComplexMatrix2.fullTrace,
    Matrix.trace_conjTranspose]
  simp
end Matrices
section Loop
variable {L m : ℕ} {j : ℤ}
def squareLoop (U : Bond L m j → ComplexMatrix2) (z : PeriodicLattice.Site L m j) (κ₁ κ₂ : Fin 4) :
    ComplexMatrix2 :=
  U (Bond.forwardFrom z κ₁) * U (Bond.forwardFrom (z + PeriodicLattice.unitStep L m j κ₁) κ₂) *
    (U (Bond.forwardFrom (z + PeriodicLattice.unitStep L m j κ₂) κ₁))⁻¹ *
      (U (Bond.forwardFrom z κ₂))⁻¹
variable {U : Bond L m j → ComplexMatrix2}
  (hU : PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U)
include hU
theorem plaquetteHolonomy_eq_squareLoop (p : Plaquette L m j) :
    plaquetteHolonomy U p = squareLoop U p.origin p.firstAxis p.secondAxis := by
  have hopp : ∀ b, U (Bond.opposite b) = (U b)⁻¹ := fun b => hU.2 b trivial
  simp [plaquetteHolonomy, PeriodicLattice.pathHolonomy, Plaquette.boundaryBonds, hopp, squareLoop,
    mul_assoc]
theorem squareLoop_mem (z : PeriodicLattice.Site L m j) (κ₁ κ₂ : Fin 4) :
    squareLoop U z κ₁ κ₂ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
  mul_mem (mul_mem (mul_mem (hU.1 _ trivial) (hU.1 _ trivial))
    (inv_mem_specialUnitary (hU.1 _ trivial))) (inv_mem_specialUnitary (hU.1 _ trivial))
theorem squareLoop_swap (z : PeriodicLattice.Site L m j) (κ₁ κ₂ : Fin 4) :
    squareLoop U z κ₂ κ₁ = (squareLoop U z κ₁ κ₂)⁻¹ := by
  simp only [squareLoop, Matrix.mul_inv_rev, inv_inv_of_mem_specialUnitary (hU.1 _ trivial),
    mul_assoc]
end Loop
theorem re_fullTrace_signed_loops {a₀ a₁ b₀ b₁ : ComplexMatrix2}
    (ha₀ : a₀ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (ha₁ : a₁ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hb₀ : b₀ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2))
    (hb₁ : b₁ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    (ComplexMatrix2.fullTrace (a₀⁻¹ * b₀ * a₁⁻¹⁻¹ * b₁⁻¹)).re =
        (ComplexMatrix2.fullTrace (a₀ * b₁ * a₁⁻¹ * b₀⁻¹)).re ∧
      (ComplexMatrix2.fullTrace (a₁ * b₁⁻¹ * a₀⁻¹ * b₀⁻¹⁻¹)).re =
        (ComplexMatrix2.fullTrace (a₀ * b₁ * a₁⁻¹ * b₀⁻¹)).re ∧
      (ComplexMatrix2.fullTrace (a₁⁻¹ * b₀⁻¹ * a₀⁻¹⁻¹ * b₁⁻¹⁻¹)).re =
        (ComplexMatrix2.fullTrace (a₀ * b₁ * a₁⁻¹ * b₀⁻¹)).re := by
  have hQ : a₀ * b₁ * a₁⁻¹ * b₀⁻¹ ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    mul_mem (mul_mem (mul_mem ha₀ hb₁) (inv_mem_specialUnitary ha₁)) (inv_mem_specialUnitary hb₀)
  have hinv : (a₀ * b₁ * a₁⁻¹ * b₀⁻¹)⁻¹ = b₀ * (a₁ * (b₁⁻¹ * a₀⁻¹)) := by
    simp only [Matrix.mul_inv_rev, inv_inv_of_mem_specialUnitary hb₀,
      inv_inv_of_mem_specialUnitary ha₁, mul_assoc]
  rw [inv_inv_of_mem_specialUnitary ha₁, inv_inv_of_mem_specialUnitary hb₀,
    inv_inv_of_mem_specialUnitary ha₀, inv_inv_of_mem_specialUnitary hb₁]
  refine ⟨?_, ?_, ?_⟩
  · rw [← re_fullTrace_inv hQ, hinv, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, mul_assoc,
      mul_assoc, Matrix.trace_mul_comm]
    simp only [mul_assoc]
  · rw [← re_fullTrace_inv hQ, hinv, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_mul_comm]
    simp only [mul_assoc]
  · rw [ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, mul_assoc, mul_assoc,
      Matrix.trace_mul_comm]
    rw [mul_assoc, Matrix.trace_mul_comm]
variable {D : GluingSetup} {e : ScaleExponent D} {Φ : ScaledLatticeMotion e}
abbrev latticeStep (D : GluingSetup) (μ : Fin 4) :
    PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) :=
  PeriodicLattice.unitStep D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) μ
theorem smul_stdBasis (a : ℝ) (μ : Fin 4) :
    a • stdBasis μ = (Pi.single μ a : Fin 4 → ℝ) := by
  funext κ
  by_cases hκ : κ = μ
  · subst hκ
    simp [stdBasis]
  · simp [stdBasis, Pi.single_eq_of_ne hκ]
theorem translateBy_single (X : GluingSetup) (u : X.Torus) (κ : Fin 4) :
    X.translateBy u (Pi.single κ X.mesh) =
      u + ((latticeStep X κ : PeriodicLattice.Site _ _ _) : X.Torus) :=
  congrArg (u + ·) (torusProj_single X.L (X.m : ℕ) κ X.mesh)
theorem translateBy_neg_single (X : GluingSetup) (u : X.Torus) (κ : Fin 4) :
    X.translateBy u (-Pi.single κ X.mesh) =
      u - ((latticeStep X κ : PeriodicLattice.Site _ _ _) : X.Torus) := by
  have hproj : X.proj (Pi.single κ X.mesh) =
      ((latticeStep X κ : PeriodicLattice.Site _ _ _) : X.Torus) :=
    torusProj_single X.L (X.m : ℕ) κ X.mesh
  change u + X.proj (-Pi.single κ X.mesh) = _
  rw [map_neg, hproj, sub_eq_add_neg]
theorem onTorusSite_add_of_sign_one (h : Φ.IsDilatingBijectionOfTori)
    (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) (μ : Fin 4) (hε : Φ.signs μ = 1) :
    Φ.onTorusSite (x + latticeStep D μ) = Φ.onTorusSite x + latticeStep e.target (Φ.perm μ) := by
  apply Subtype.ext
  have h₄ := h.2.2.2.1 (x : D.Torus) μ
  rw [hε] at h₄
  simp only [Units.val_one, Int.cast_one, one_mul, smul_stdBasis] at h₄
  rw [translateBy_single, translateBy_single] at h₄
  exact h₄
theorem onTorusSite_add_of_sign_neg_one (h : Φ.IsDilatingBijectionOfTori)
    (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) (μ : Fin 4) (hε : Φ.signs μ = -1) :
    Φ.onTorusSite (x + latticeStep D μ) = Φ.onTorusSite x - latticeStep e.target (Φ.perm μ) := by
  apply Subtype.ext
  have h₄ := h.2.2.2.1 (x : D.Torus) μ
  rw [hε] at h₄
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_smul,
    smul_stdBasis] at h₄
  rw [translateBy_single, translateBy_neg_single] at h₄
  exact h₄
theorem onTorusLink_of_sign_one (hS : Φ.IsDilatingBijectionOfTori) {μ : Fin 4}
    (hε : Φ.signs μ = 1) {x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)}
    {w : PeriodicLattice.Site e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)}
    (hx : Φ.onTorusSite x = w) :
    Φ.onTorusLink (Bond.forwardFrom x μ) = Bond.forwardFrom w (Φ.perm μ) := by
  subst hx
  exact Bond.ext rfl (onTorusSite_add_of_sign_one hS x μ hε)
theorem onTorusLink_of_sign_neg_one (hS : Φ.IsDilatingBijectionOfTori) {μ : Fin 4}
    (hε : Φ.signs μ = -1) {x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)}
    {w : PeriodicLattice.Site e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)}
    (hx : Φ.onTorusSite x = w + latticeStep e.target (Φ.perm μ)) :
    Φ.onTorusLink (Bond.forwardFrom x μ) = (Bond.forwardFrom w (Φ.perm μ)).opposite := by
  refine Bond.ext hx ?_
  change Φ.onTorusSite (x + latticeStep D μ) = w
  rw [onTorusSite_add_of_sign_neg_one hS x μ hε, hx, add_sub_cancel_right]
theorem projectPoint_defect_of_sign_one (X : GluingSetup) {ε : ℤˣ} (hε : ε = 1) (κ : Fin 4) :
    InfiniteLattice.projectPoint X.L (X.m : ℕ) ((X.K : ℕ) : ℤ)
      ⟨_, signDefect_smul_axisStep_mem ε X.mesh κ⟩ = 0 := by
  subst hε
  refine Subtype.ext (funext fun μ => ?_)
  simp [InfiniteLattice.projectPoint, signDefect, torusProj]
theorem projectPoint_defect_of_sign_neg_one (X : GluingSetup) {ε : ℤˣ} (hε : ε = -1) (κ : Fin 4) :
    InfiniteLattice.projectPoint X.L (X.m : ℕ) ((X.K : ℕ) : ℤ)
      ⟨_, signDefect_smul_axisStep_mem ε X.mesh κ⟩ = latticeStep X κ := by
  subst hε
  have hd : signDefect (-1) = 1 := by norm_num [signDefect]
  refine Subtype.ext ?_
  simp only [InfiniteLattice.projectPoint, hd, one_smul]
  exact torusProj_single X.L (X.m : ℕ) κ X.mesh
theorem re_fullTrace_squareLoop_pull (hS : Φ.IsDilatingBijectionOfTori)
    {U' : e.target.PeriodicLink → ComplexMatrix2} (hU : U' ∈ e.target.gaugeFields)
    (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) (μ ν : Fin 4) :
    (ComplexMatrix2.fullTrace (squareLoop (Φ.pullTorusField U') x μ ν)).re =
      (ComplexMatrix2.fullTrace
        (squareLoop U' (Φ.torusPlaquetteOrigin x μ ν) (Φ.perm μ) (Φ.perm ν))).re := by
  have hopp : ∀ b, U' (Bond.opposite b) = (U' b)⁻¹ := fun b => hU.2 b trivial
  have hmem : ∀ b, U' b ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) :=
    fun b => hU.1 b trivial
  have hloop : squareLoop (Φ.pullTorusField U') x μ ν =
      U' (Φ.onTorusLink (Bond.forwardFrom x μ)) *
        U' (Φ.onTorusLink (Bond.forwardFrom (x + latticeStep D μ) ν)) *
        (U' (Φ.onTorusLink (Bond.forwardFrom (x + latticeStep D ν) μ)))⁻¹ *
        (U' (Φ.onTorusLink (Bond.forwardFrom x ν)))⁻¹ := rfl
  have horigin : Φ.torusPlaquetteOrigin x μ ν = Φ.onTorusSite x -
      InfiniteLattice.projectPoint e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)
        ⟨_, signDefect_smul_axisStep_mem (Φ.signs μ) e.target.mesh (Φ.perm μ)⟩ -
      InfiniteLattice.projectPoint e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)
        ⟨_, signDefect_smul_axisStep_mem (Φ.signs ν) e.target.mesh (Φ.perm ν)⟩ := rfl
  rw [hloop]
  generalize hz : Φ.torusPlaquetteOrigin x μ ν = z at horigin ⊢
  simp only [squareLoop]
  rcases Int.units_eq_one_or (Φ.signs μ) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (Φ.signs ν) with h₂ | h₂
  · have hy : Φ.onTorusSite x = z := by
      rw [horigin, projectPoint_defect_of_sign_one e.target h₁,
        projectPoint_defect_of_sign_one e.target h₂]
      abel
    have s₁ : Φ.onTorusSite (x + latticeStep D μ) = z + latticeStep e.target (Φ.perm μ) := by
      rw [onTorusSite_add_of_sign_one hS x μ h₁, hy]
    have s₃ : Φ.onTorusSite (x + latticeStep D ν) = z + latticeStep e.target (Φ.perm ν) := by
      rw [onTorusSite_add_of_sign_one hS x ν h₂, hy]
    rw [onTorusLink_of_sign_one hS h₁ hy, onTorusLink_of_sign_one hS h₂ s₁,
      onTorusLink_of_sign_one hS h₁ s₃, onTorusLink_of_sign_one hS h₂ hy]
  · have hy : Φ.onTorusSite x = z + latticeStep e.target (Φ.perm ν) := by
      rw [horigin, projectPoint_defect_of_sign_one e.target h₁,
        projectPoint_defect_of_sign_neg_one e.target h₂]
      abel
    have s₁ : Φ.onTorusSite (x + latticeStep D μ) =
        z + latticeStep e.target (Φ.perm μ) + latticeStep e.target (Φ.perm ν) := by
      rw [onTorusSite_add_of_sign_one hS x μ h₁, hy]
      abel
    have s₃ : Φ.onTorusSite (x + latticeStep D ν) = z := by
      rw [onTorusSite_add_of_sign_neg_one hS x ν h₂, hy]
      abel
    rw [onTorusLink_of_sign_one hS h₁ hy, onTorusLink_of_sign_neg_one hS h₂ s₁,
      onTorusLink_of_sign_one hS h₁ s₃, onTorusLink_of_sign_neg_one hS h₂ hy]
    simp only [hopp]
    exact (re_fullTrace_signed_loops (hmem _) (hmem _) (hmem _) (hmem _)).2.1
  · have hy : Φ.onTorusSite x = z + latticeStep e.target (Φ.perm μ) := by
      rw [horigin, projectPoint_defect_of_sign_neg_one e.target h₁,
        projectPoint_defect_of_sign_one e.target h₂]
      abel
    have s₁ : Φ.onTorusSite (x + latticeStep D μ) = z := by
      rw [onTorusSite_add_of_sign_neg_one hS x μ h₁, hy]
      abel
    have s₃ : Φ.onTorusSite (x + latticeStep D ν) =
        z + latticeStep e.target (Φ.perm ν) + latticeStep e.target (Φ.perm μ) := by
      rw [onTorusSite_add_of_sign_one hS x ν h₂, hy]
      abel
    rw [onTorusLink_of_sign_neg_one hS h₁ hy, onTorusLink_of_sign_one hS h₂ s₁,
      onTorusLink_of_sign_neg_one hS h₁ s₃, onTorusLink_of_sign_one hS h₂ hy]
    simp only [hopp]
    exact (re_fullTrace_signed_loops (hmem _) (hmem _) (hmem _) (hmem _)).1
  · have hy : Φ.onTorusSite x =
        z + latticeStep e.target (Φ.perm μ) + latticeStep e.target (Φ.perm ν) := by
      rw [horigin, projectPoint_defect_of_sign_neg_one e.target h₁,
        projectPoint_defect_of_sign_neg_one e.target h₂]
      abel
    have hy' : Φ.onTorusSite x =
        z + latticeStep e.target (Φ.perm ν) + latticeStep e.target (Φ.perm μ) := by
      rw [hy]
      abel
    have s₁ : Φ.onTorusSite (x + latticeStep D μ) = z + latticeStep e.target (Φ.perm ν) := by
      rw [onTorusSite_add_of_sign_neg_one hS x μ h₁, hy]
      abel
    have s₃ : Φ.onTorusSite (x + latticeStep D ν) = z + latticeStep e.target (Φ.perm μ) := by
      rw [onTorusSite_add_of_sign_neg_one hS x ν h₂, hy]
      abel
    rw [onTorusLink_of_sign_neg_one hS h₁ hy', onTorusLink_of_sign_neg_one hS h₂ s₁,
      onTorusLink_of_sign_neg_one hS h₁ s₃, onTorusLink_of_sign_neg_one hS h₂ hy]
    simp only [hopp]
    exact (re_fullTrace_signed_loops (hmem _) (hmem _) (hmem _) (hmem _)).2.2
theorem plaquetteEnergy_pull (hS : Φ.IsDilatingBijectionOfTori)
    {U' : e.target.PeriodicLink → ComplexMatrix2} (hU : U' ∈ e.target.gaugeFields)
    (hU₀ : Φ.pullTorusField U' ∈ D.gaugeFields) (p : D.PeriodicPlaquette) :
    PeriodicLattice.plaquetteCost (Φ.pullTorusField U') p =
      PeriodicLattice.plaquetteCost U' (Φ.onTorusPlaquette p) := by
  have hsource := plaquetteHolonomy_eq_squareLoop hU₀ p
  have htarget : (ComplexMatrix2.fullTrace (plaquetteHolonomy U' (Φ.onTorusPlaquette p))).re =
      (ComplexMatrix2.fullTrace (squareLoop U' (Φ.torusPlaquetteOrigin p.origin p.firstAxis
        p.secondAxis) (Φ.perm p.firstAxis) (Φ.perm p.secondAxis))).re := by
    rcases lt_or_gt_of_ne (Φ.perm.injective.ne p.firstAxis_lt_secondAxis.ne) with h | h
    · have hv : plaquetteHolonomy U' (Φ.onTorusPlaquette p) =
          squareLoop U' (Φ.torusPlaquetteOrigin p.origin p.firstAxis p.secondAxis)
            (Φ.perm p.firstAxis) (Φ.perm p.secondAxis) := by
        rw [plaquetteHolonomy_eq_squareLoop hU]
        simp only [ScaledLatticeMotion.onTorusPlaquette, min_eq_left h.le, max_eq_right h.le]
      rw [hv]
    · have hv : plaquetteHolonomy U' (Φ.onTorusPlaquette p) =
          squareLoop U' (Φ.torusPlaquetteOrigin p.origin p.firstAxis p.secondAxis)
            (Φ.perm p.secondAxis) (Φ.perm p.firstAxis) := by
        rw [plaquetteHolonomy_eq_squareLoop hU]
        simp only [ScaledLatticeMotion.onTorusPlaquette, min_eq_right h.le, max_eq_left h.le]
      rw [hv, squareLoop_swap hU, re_fullTrace_inv (squareLoop_mem hU _ _ _)]
  simp only [PeriodicLattice.plaquetteCost]
  rw [htarget, hsource, re_fullTrace_squareLoop_pull hS hU]
theorem transport_apply {X Y : GluingSetup} (h : X = Y) (U : X.PeriodicLink → ComplexMatrix2)
    (c : X.PeriodicLink) :
    transport (F := fun Z : GluingSetup => Z.PeriodicLink → ComplexMatrix2) h U
      (transport (F := fun Z : GluingSetup => Z.PeriodicLink) h c) = U c := by
  subst h
  rfl
theorem transport_link_ext {X Y : GluingSetup} (h : X = Y) {c : X.PeriodicLink}
    {c' : Y.PeriodicLink}
    (hs : (c'.source : Y.Torus) =
      transport (F := fun Z : GluingSetup => Z.Torus) h (c.source : X.Torus))
    (ht : (c'.target : Y.Torus) =
      transport (F := fun Z : GluingSetup => Z.Torus) h (c.target : X.Torus)) :
    c' = transport (F := fun Z : GluingSetup => Z.PeriodicLink) h c := by
  subst h
  exact Bond.ext (Subtype.ext hs) (Subtype.ext ht)
theorem onTorusLink_inverse (hS : Φ.IsDilatingBijectionOfTori) {Ψ : ScaledLatticeMotion e.neg}
    (hΨ : Ψ.onTorus = Φ.torusInv) (c : D.PeriodicLink) :
    Ψ.onTorusLink (Φ.onTorusLink c) =
      transport (F := fun Z : GluingSetup => Z.PeriodicLink) e.target_neg.symm c := by
  have hpoint : ∀ u : D.Torus, Ψ.onTorus (Φ.onTorus u) =
      transport (F := fun Z : GluingSetup => Z.Torus) e.target_neg.symm u := fun u => by
    rw [hΨ, ScaledLatticeMotion.torusInv, Function.leftInverse_invFun hS.1.1 u]
  exact transport_link_ext _ (hpoint _) (hpoint _)
theorem onTorusLink_comp {e₂ : ScaleExponent e.target} {Φ₂ : ScaledLatticeMotion e₂}
    {Φ₃ : ScaledLatticeMotion (e.add e₂)} (h₃ : Φ₃.onTorus = Φ.torusComp Φ₂)
    (c : D.PeriodicLink) :
    Φ₃.onTorusLink c = transport (F := fun Z : GluingSetup => Z.PeriodicLink) (e.target_add e₂)
      (Φ₂.onTorusLink (Φ.onTorusLink c)) := by
  have hpoint : ∀ u : D.Torus, Φ₃.onTorus u =
      transport (F := fun Z : GluingSetup => Z.Torus) (e.target_add e₂)
        (Φ₂.onTorus (Φ.onTorus u)) := fun u => by
    rw [h₃]
    rfl
  exact transport_link_ext _ (hpoint _) (hpoint _)
theorem statement_holds (hLinks : ScaledMotionLinksOfToriClaim)
    (hScaling : TorusDilationOfScaledMotions.Statement) : Statement := by
  intro D e Φ
  have hS := hScaling D e Φ
  obtain ⟨hbij, hopp, -⟩ := hLinks D e Φ
  have hmaps : ∀ U' ∈ e.target.gaugeFields, Φ.pullTorusField U' ∈ D.gaugeFields :=
    fun U' hU =>
    ⟨fun _ _ => hU.1 _ trivial, fun b _ => by
      change U' (Φ.onTorusLink b.opposite) = (U' (Φ.onTorusLink b))⁻¹
      rw [hopp]
      exact hU.2 _ trivial⟩
  have hinj : InjOn Φ.pullTorusField e.target.gaugeFields := fun U₁ _ U₂ _ h => by
    funext b
    obtain ⟨c, rfl⟩ := hbij.2 b
    exact congrFun h c
  have hsurj : SurjOn Φ.pullTorusField e.target.gaugeFields D.gaugeFields := by
    intro U hU
    let E := Equiv.ofBijective Φ.onTorusLink hbij
    have hE : ∀ c, E.symm (Φ.onTorusLink c) = c := fun c => E.symm_apply_apply c
    refine ⟨fun b => U (E.symm b), ⟨fun _ _ => hU.1 _ trivial, fun b _ => ?_⟩, funext fun c => ?_⟩
    · obtain ⟨c, rfl⟩ := hbij.2 b
      change U (E.symm (Φ.onTorusLink c).opposite) = (U (E.symm (Φ.onTorusLink c)))⁻¹
      rw [← hopp, hE, hE]
      exact hU.2 _ trivial
    · change U (E.symm (Φ.onTorusLink c)) = U c
      rw [hE]
  refine ⟨hmaps, ⟨hmaps, hinj, hsurj⟩,
    (continuous_pi fun c => continuous_apply _).continuousOn, fun Ψ hΨ => ⟨fun U _ => ?_,
      fun U' _ => ?_⟩, fun e₂ Φ₂ Φ₃ h₃ U'' _ => ?_, fun p U' hU =>
      plaquetteEnergy_pull hS hU (hmaps U' hU) p⟩
  · funext c
    change transport (F := fun Z : GluingSetup => Z.PeriodicLink → ComplexMatrix2)
      e.target_neg.symm U (Ψ.onTorusLink (Φ.onTorusLink c)) = U c
    rw [onTorusLink_inverse hS hΨ, transport_apply]
  · funext b
    obtain ⟨c, rfl⟩ := hbij.2 b
    change transport (F := fun Z : GluingSetup => Z.PeriodicLink → ComplexMatrix2)
      e.target_neg.symm (Φ.pullTorusField U') (Ψ.onTorusLink (Φ.onTorusLink c)) =
        U' (Φ.onTorusLink c)
    rw [onTorusLink_inverse hS hΨ, transport_apply]
    rfl
  · funext c
    change transport (F := fun Z : GluingSetup => Z.PeriodicLink → ComplexMatrix2)
      (e.target_add e₂) U'' (Φ₃.onTorusLink c) = U'' (Φ₂.onTorusLink (Φ.onTorusLink c))
    rw [onTorusLink_comp h₃, transport_apply]
end SourcesAndGluing.FieldsUnderScaledMotionsOfTori
end YangMills.Construction
end
