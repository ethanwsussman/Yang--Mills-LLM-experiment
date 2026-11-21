import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace StepGas
open BlockAverages TorusFields TorusLumps StepSettings
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
structure GasGround.ReadsComponentsAt (G : GasGround R n) (Y : TorusSite n) (F : G.Config → ℝ) : Prop where
  measurable : Measurable F
  abs_le_one : ∀ σ, |F σ| ≤ 1
  eq_of_agree : ∀ σ σ', (∀ i : G.GasSpin, i.1.Meets Y → σ i = σ' i) → F σ = F σ'
  eq_zero_of_none : ∀ σ, σ ∈ G.NoSpinMeets Y → F σ = 0
structure SameSupportNear (θ : GasSupport R n) (θ' : GasSupport R n') (Y : TorusSite n) (Y' : TorusSite n')
    (m : ℕ) : Prop where
  core_mem : ∀ y ∈ θ.core, ∃ h, OffsetInBox m h ∧ y = Y + siteOfInt h
  core_mem' : ∀ y ∈ θ'.core, ∃ h, OffsetInBox m h ∧ y = Y' + siteOfInt h
  bad_iff : ∀ q, IsNearIndex R.params.side m q →
    (nearBond R.params.side Y q ∈ θ.1 ↔ nearBond R.params.side Y' q ∈ θ'.1)
  sites_iff : ∀ h o, OffsetInBox m h → o ∈ centredCube R.params.side →
    (fineSite R.params.side Y h o ∈ θ.2 ↔ fineSite R.params.side Y' h o ∈ θ'.2)
structure SameStateNear (θ : GasSupport R n) (θ' : GasSupport R n') (s : SupportState θ) (s' : SupportState θ')
    (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ) : Prop where
  field_eq : ∀ q (hb : nearBond R.params.side Y q ∈ θ.coreBonds) (hb' : nearBond R.params.side Y' q ∈ θ'.coreBonds),
    IsNearIndex R.params.side m q → s.1 ⟨_, hb⟩ = s'.1 ⟨_, hb'⟩
  label_eq : ∀ h o (hz : fineSite R.params.side Y h o ∈ θ.2) (hz' : fineSite R.params.side Y' h o ∈ θ'.2),
    OffsetInBox m h → o ∈ centredCube R.params.side → s.2.1 ⟨_, hz⟩ = s'.2.1 ⟨_, hz'⟩
  base_eq : ∀ h (hy : Y + siteOfInt h ∈ θ.core) (hy' : Y' + siteOfInt h ∈ θ'.core), OffsetInBox m h →
    s.2.2 ⟨_, hy⟩ = s'.2.2 ⟨_, hy'⟩
def ComponentIn (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ)
    (σ : G.Config) (σ' : G'.Config) (i : G.GasSpin) (i' : G'.GasSpin) : Prop :=
  SameSupportNear i.1 i'.1 Y Y' m ∧ ∃ s s', σ i = Sum.inr s ∧ σ' i' = Sum.inr s' ∧
    SameStateNear i.1 i'.1 s.1 s'.1 Y Y' m
def ComponentsMatch (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n') (m : ℕ)
    (σ : G.Config) (σ' : G'.Config) : Prop :=
  (∀ i : G.GasSpin, i.1.Meets Y → σ i ≠ Sum.inl () →
      ∃ i' : G'.GasSpin, i'.1.Meets Y' ∧ ComponentIn G G' Y Y' m σ σ' i i') ∧
    ∀ i' : G'.GasSpin, i'.1.Meets Y' → σ' i' ≠ Sum.inl () →
      ∃ i : G.GasSpin, i.1.Meets Y ∧ ComponentIn G G' Y Y' m σ σ' i i'
end StepGas
end YangMills.Construction
end
