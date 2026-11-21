import YangMills.Construction.BackgroundField.SitePropagatorBounds
import Mathlib
noncomputable section
namespace YangMills.Construction.BackgroundField
def chosenSiteGreenConstants (L : ℕ) : SiteGreenConstants :=
  Classical.epsilon (AreSiteGreenConstants L)
end YangMills.Construction.BackgroundField
