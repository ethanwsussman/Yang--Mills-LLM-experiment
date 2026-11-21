import YangMills.Construction.SourcesAndGluing.LatticeSimilarities
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def transport {F : GluingSetup → Type*} {D D' : GluingSetup} (h : D = D') (x : F D) : F D' :=
  h ▸ x
theorem transport_symm_transport {F : GluingSetup → Type*} {D D' : GluingSetup} (h : D = D')
    (x : F D) : transport (F := F) h.symm (transport h x) = x := by
  subst h
  rfl
namespace GluingSetup
abbrev PeriodicPlaquette (D : GluingSetup) : Type :=
  PeriodicLattice.Plaquette D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)
theorem withCutoffAndSide_self (D : GluingSetup) {K' m' : ℕ+} (hK : K' = D.K) (hm : m' = D.m) :
    D.withCutoffAndSide K' m' = D := by
  subst hK hm
  rfl
end GluingSetup
namespace ScaleExponent
variable {D : GluingSetup} (e : ScaleExponent D)
def neg : ScaleExponent e.target where
  shift := -e.shift
  one_le_cutoff_sub := by
    have h := e.target_K
    have hK := D.K.pos
    omega
  one_le_side_add := by
    have h := e.target_m
    have hm := D.m.pos
    omega
theorem target_neg : e.neg.target = D := by
  have hK : ((e.neg.targetCutoff : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) := by
    have h := e.target_K
    have h' : ((e.neg.targetCutoff : ℕ) : ℤ) = ((e.target.K : ℕ) : ℤ) - -e.shift :=
      e.neg.target_K
    omega
  have hm : ((e.neg.targetSideExponent : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) := by
    have h := e.target_m
    have h' : ((e.neg.targetSideExponent : ℕ) : ℤ) = ((e.target.m : ℕ) : ℤ) + -e.shift :=
      e.neg.target_m
    omega
  exact GluingSetup.withCutoffAndSide_self D (PNat.eq (by exact_mod_cast hK))
    (PNat.eq (by exact_mod_cast hm))
def add (e₂ : ScaleExponent e.target) : ScaleExponent D where
  shift := e.shift + e₂.shift
  one_le_cutoff_sub := by
    have h := e.target_K
    have h₂ := e₂.one_le_cutoff_sub
    omega
  one_le_side_add := by
    have h := e.target_m
    have h₂ := e₂.one_le_side_add
    omega
theorem target_add (e₂ : ScaleExponent e.target) : e₂.target = (e.add e₂).target := by
  have hK : e₂.targetCutoff = (e.add e₂).targetCutoff := by
    refine PNat.eq ?_
    have h := e.target_K
    have h₁ : ((e₂.targetCutoff : ℕ) : ℤ) = ((e.target.K : ℕ) : ℤ) - e₂.shift := e₂.target_K
    have h₂ : (((e.add e₂).targetCutoff : ℕ) : ℤ) = ((D.K : ℕ) : ℤ) - (e.shift + e₂.shift) :=
      (e.add e₂).target_K
    omega
  have hm : e₂.targetSideExponent = (e.add e₂).targetSideExponent := by
    refine PNat.eq ?_
    have h := e.target_m
    have h₁ : ((e₂.targetSideExponent : ℕ) : ℤ) = ((e.target.m : ℕ) : ℤ) + e₂.shift :=
      e₂.target_m
    have h₂ : (((e.add e₂).targetSideExponent : ℕ) : ℤ) = ((D.m : ℕ) : ℤ) + (e.shift + e₂.shift) :=
      (e.add e₂).target_m
    omega
  change D.withCutoffAndSide e₂.targetCutoff e₂.targetSideExponent =
    D.withCutoffAndSide (e.add e₂).targetCutoff (e.add e₂).targetSideExponent
  rw [hK, hm]
end ScaleExponent
namespace ScaledLatticeMotion
variable {D : GluingSetup} {e : ScaleExponent D} (Φ : ScaledLatticeMotion e)
def torusInv : e.target.Torus → e.neg.target.Torus :=
  fun v => transport (F := fun X : GluingSetup => X.Torus) e.target_neg.symm
    (Function.invFun Φ.onTorus v)
def torusComp {e₂ : ScaleExponent e.target} (Φ₂ : ScaledLatticeMotion e₂) :
    D.Torus → (e.add e₂).target.Torus :=
  fun u => transport (F := fun X : GluingSetup => X.Torus) (e.target_add e₂) (Φ₂.onTorus (Φ.onTorus u))
def IsDilatingBijectionOfSpace : Prop :=
  Function.Bijective Φ.onSpace ∧
    (∀ x y, euclidNorm (Φ.onSpace x - Φ.onSpace y) =
      (D.L : ℝ) ^ e.shift * euclidNorm (x - y)) ∧
    (∀ x z, Φ.onSpace (x + z) = Φ.onSpace x + (D.L : ℝ) ^ e.shift • Φ.rotation z) ∧
    (∀ x μ, Φ.onSpace (x + D.mesh • stdBasis μ) =
      Φ.onSpace x + ((((Φ.signs μ : ℤˣ) : ℤ) : ℝ) * e.target.mesh) • stdBasis (Φ.perm μ)) ∧
    Φ.onSpace '' (D.gridPoints : Set InfiniteLattice.AmbientSpace) = e.target.gridPoints
def IsDilatingBijectionOfTori : Prop :=
  Function.Bijective Φ.onTorus ∧
    (∀ u v, TorusMetric.torusEuclidNorm (Φ.onTorus u - Φ.onTorus v) =
      (D.L : ℝ) ^ e.shift * TorusMetric.torusEuclidNorm (u - v)) ∧
    (∀ u z, Φ.onTorus (D.translateBy u z) =
      e.target.translateBy (Φ.onTorus u) ((D.L : ℝ) ^ e.shift • Φ.rotation z)) ∧
    (∀ u μ, Φ.onTorus (D.translateBy u (D.mesh • stdBasis μ)) =
      e.target.translateBy (Φ.onTorus u)
        (((((Φ.signs μ : ℤˣ) : ℤ) : ℝ) * e.target.mesh) • stdBasis (Φ.perm μ))) ∧
    Φ.onTorus '' (D.periodicLattice : Set D.Torus) = e.target.periodicLattice
def RotationDetermined : Prop :=
  (∀ (e' : ScaleExponent D) (Φ' : ScaledLatticeMotion e'), Φ'.onSpace = Φ.onSpace →
    Φ'.rotation = Φ.rotation) ∧
  ∀ Φ' : ScaledLatticeMotion e, Φ'.onTorus = Φ.onTorus → Φ'.rotation = Φ.rotation
def InvIsScaledMotion : Prop :=
  IsScaledMotionOfSpace e.neg Φ.rotation⁻¹ (Function.invFun Φ.onSpace) ∧
    IsScaledMotionOfTori e.neg Φ.rotation⁻¹ Φ.torusInv
def CompIsScaledMotion : Prop :=
  ∀ (e₂ : ScaleExponent e.target) (Φ₂ : ScaledLatticeMotion e₂),
    IsScaledMotionOfSpace (e.add e₂) (Φ₂.rotation * Φ.rotation) (Φ₂.onSpace ∘ Φ.onSpace) ∧
      IsScaledMotionOfTori (e.add e₂) (Φ₂.rotation * Φ.rotation) (Φ.torusComp Φ₂)
def MapsLinksOfSpace : Prop :=
  Function.Bijective Φ.onLink ∧
    (∀ c, Φ.onLink c.opposite = (Φ.onLink c).opposite) ∧
    ∀ (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4),
      (Φ.signs μ = 1 → (Φ.onLink (InfiniteLattice.Link.forwardFrom x μ)).IsPositivelyOriented) ∧
        (Φ.signs μ = -1 →
          (Φ.onLink (InfiniteLattice.Link.forwardFrom x μ)).opposite.IsPositivelyOriented)
def MapsLinksOfTori : Prop :=
  Function.Bijective Φ.onTorusLink ∧
    (∀ c, Φ.onTorusLink c.opposite = (Φ.onTorusLink c).opposite) ∧
    ∀ (x : PeriodicLattice.Site D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) (μ : Fin 4),
      (Φ.signs μ = 1 →
          (Φ.onTorusLink (PeriodicLattice.Bond.forwardFrom x μ)).IsPositivelyOriented) ∧
        (Φ.signs μ = -1 →
          (Φ.onTorusLink (PeriodicLattice.Bond.forwardFrom x μ)).opposite.IsPositivelyOriented)
def MapsPlaquettesOfSpace : Prop :=
  (∀ p, TorusLifts.plaquetteVertexSet (Φ.onPlaquette p) =
      Φ.onPoint '' TorusLifts.plaquetteVertexSet p) ∧
    Function.Bijective Φ.onPlaquette ∧
    (∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onSpace = Function.invFun Φ.onSpace →
      (∀ p, transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh)
          e.target_neg (Ψ.onPlaquette (Φ.onPlaquette p)) = p) ∧
        ∀ p', Φ.onPlaquette
          (transport (F := fun X : GluingSetup => InfiniteLattice.ElementaryPlaquette X.mesh)
            e.target_neg (Ψ.onPlaquette p')) = p') ∧
    ∀ p, (Φ.onPlaquette p).center = Φ.onSpace p.center
def MapsPlaquettesOfTori : Prop :=
  (∀ p, (Φ.onTorusPlaquette p).vertices = Φ.onTorusSite '' p.vertices) ∧
    Function.Bijective Φ.onTorusPlaquette ∧
    (∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onTorus = Φ.torusInv →
      (∀ p, transport (F := fun X : GluingSetup => X.PeriodicPlaquette) e.target_neg
          (Ψ.onTorusPlaquette (Φ.onTorusPlaquette p)) = p) ∧
        ∀ p', Φ.onTorusPlaquette (transport (F := fun X : GluingSetup => X.PeriodicPlaquette)
          e.target_neg (Ψ.onTorusPlaquette p')) = p') ∧
    ∀ p, (Φ.onTorusPlaquette p).barycenter = Φ.onTorus p.barycenter
def PullsFieldsOfSpace : Prop :=
  Function.Bijective Φ.pullField ∧ Continuous Φ.pullField ∧
    (∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onSpace = Function.invFun Φ.onSpace →
      (∀ U : D.GridField, Φ.pullField (Ψ.pullField
          (transport (F := fun X : GluingSetup => X.GridField) e.target_neg.symm U)) = U) ∧
        ∀ U' : e.target.GridField,
          Ψ.pullField (transport (F := fun X : GluingSetup => X.GridField)
            e.target_neg.symm (Φ.pullField U')) = U') ∧
    (∀ (e₂ : ScaleExponent e.target) (Φ₂ : ScaledLatticeMotion e₂)
      (Φ₃ : ScaledLatticeMotion (e.add e₂)), Φ₃.onSpace = Φ₂.onSpace ∘ Φ.onSpace →
        ∀ U'' : e₂.target.GridField,
          Φ₃.pullField (transport (F := fun X : GluingSetup => X.GridField)
            (e.target_add e₂) U'') = Φ.pullField (Φ₂.pullField U'')) ∧
    ∀ (p : InfiniteLattice.ElementaryPlaquette D.mesh) (U' : e.target.GridField),
      InfiniteLattice.faceEnergy (Φ.pullField U').1 p =
        InfiniteLattice.faceEnergy U'.1 (Φ.onPlaquette p)
def PullsFieldsOfTori : Prop :=
  (∀ U' ∈ e.target.gaugeFields, Φ.pullTorusField U' ∈ D.gaugeFields) ∧
    BijOn Φ.pullTorusField e.target.gaugeFields D.gaugeFields ∧
    ContinuousOn Φ.pullTorusField e.target.gaugeFields ∧
    (∀ Ψ : ScaledLatticeMotion e.neg, Ψ.onTorus = Φ.torusInv →
      (∀ U ∈ D.gaugeFields, Φ.pullTorusField (Ψ.pullTorusField
          (transport (F := fun X : GluingSetup => X.PeriodicLink → Matrices.ComplexMatrix2)
            e.target_neg.symm U)) = U) ∧
        ∀ U' ∈ e.target.gaugeFields,
          Ψ.pullTorusField
            (transport (F := fun X : GluingSetup => X.PeriodicLink → Matrices.ComplexMatrix2)
              e.target_neg.symm (Φ.pullTorusField U')) = U') ∧
    (∀ (e₂ : ScaleExponent e.target) (Φ₂ : ScaledLatticeMotion e₂)
      (Φ₃ : ScaledLatticeMotion (e.add e₂)), Φ₃.onTorus = Φ.torusComp Φ₂ →
        ∀ U'' ∈ e₂.target.gaugeFields,
          Φ₃.pullTorusField
            (transport (F := fun X : GluingSetup => X.PeriodicLink → Matrices.ComplexMatrix2)
              (e.target_add e₂) U'') = Φ.pullTorusField (Φ₂.pullTorusField U'')) ∧
    ∀ (p : D.PeriodicPlaquette), ∀ U' ∈ e.target.gaugeFields,
      PeriodicLattice.plaquetteCost (Φ.pullTorusField U') p =
        PeriodicLattice.plaquetteCost U' (Φ.onTorusPlaquette p)
def PullsObservablesOfSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ f : InfiniteLattice.AmbientSpace → E, InfiniteLattice.IsBoundedBorelCompactlySupported f →
    ∀ U' : e.target.GridField,
      InfiniteLattice.smearedEnergy f (Φ.pullField U') =
        InfiniteLattice.smearedEnergy (f ∘ Function.invFun Φ.onSpace) U'
def PullsObservablesOfTori (E : Type) [AddCommMonoid E] [Module ℝ E] : Prop :=
  ∀ f : D.Torus → E, ∀ U' ∈ e.target.gaugeFields,
    D.smeared f (Φ.pullTorusField U') =
      e.target.smeared (f ∘ Function.invFun Φ.onTorus) U'
def PreservesAction : Prop :=
  ∀ U' ∈ e.target.gaugeFields,
    D.action (Φ.pullTorusField U') = e.target.action U'
def PreservesMeasures : Prop :=
  ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, InfiniteLattice.IsPeriodicObservable F →
    ∀ β : ℝ, 0 < β →
    (∫ U', F (Φ.pullTorusField U')
        ∂PeriodicLattice.productHaarMeasure e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) =
      ∫ U, F U ∂PeriodicLattice.productHaarMeasure D.L (D.m : ℕ) ((D.K : ℕ) : ℤ)) ∧
    PeriodicLattice.gibbsExpectation e.target.L (e.target.m : ℕ) (e.target.K : ℕ) β
        (F ∘ Φ.pullTorusField) =
      PeriodicLattice.gibbsExpectation D.L (D.m : ℕ) (D.K : ℕ) β F
def CommutesWithLift : Prop :=
  ∀ U' ∈ e.target.gaugeFields,
    Φ.pullField (InfiniteLattice.liftField e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)
        U') =
      InfiniteLattice.liftField D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) (Φ.pullTorusField U')
end ScaledLatticeMotion
end YangMills.Construction.SourcesAndGluing
end
