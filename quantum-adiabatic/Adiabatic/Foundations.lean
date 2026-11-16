import Adiabatic.Foundations.PrefixMultipleChoice
import Adiabatic.Foundations.PrefixSupport
import Adiabatic.Foundations.SwapExtraction
import Adiabatic.Foundations.SwapScalarEvolution
import Adiabatic.Foundations.StrongSwapObstruction
import Adiabatic.Foundations.StrongSwapInverse
import Adiabatic.Foundations.TrajectoryAssembly
import Adiabatic.Foundations.DoubledSwap

/-!
# Analytic and combinatorial components of the choice investigation

These modules use ordinary mathlib foundations, including `Classical.choice`.
They formalize prefix-support extraction and the actual strong-propagator
obstruction used in the written ZF reduction to countable multiple choice.
They do not formalize a ZF model or assert that the full theorem is choice-free.
The separately audited `Adiabatic.ChoiceReduction` modules retain their stricter
foundation requirement.
-/
