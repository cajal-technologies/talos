import Project.GcdStdio.Adequacy

/-!
# Correctness of the compiled GCD kernel

The Rust driver deliberately keeps `gcd_u64` out of line. Rustc consequently
emits the already verified register-only `num-integer` kernel as `func1`; the
proof below transports the existing total small-step theorem across the checked
body equality.
-/

namespace Project.GcdStdio.Proof

open Wasm

@[proves Project.GcdStdio.Spec.KernelSpecification]
theorem kernel_correct : Project.GcdStdio.Spec.KernelSpecification := by
  intro a b
  have hconfig : Project.GcdStdio.Spec.kernelConfig a b =
      Project.NumIntegerOpt3.Spec.gcdConfig a b := by
    unfold Project.GcdStdio.Spec.kernelConfig
      Project.NumIntegerOpt3.Spec.gcdConfig
    rw [Project.GcdStdio.Spec.kernel_body_eq]
  rw [hconfig]
  exact Project.NumIntegerOpt3.Spec.mod3_gcd_smallStep_total a b

@[proves Project.GcdStdio.Spec.PublicEntrySpecification]
theorem gcd_correct : Project.GcdStdio.Spec.PublicEntrySpecification :=
  Project.GcdStdio.Adequacy.entry_adequacy

end Project.GcdStdio.Proof
