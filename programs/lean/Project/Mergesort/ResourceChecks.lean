import Project.Mergesort.ExecutionBudget

/-!
# Axiom checks for the compiled mergesort resource certificates

Keep diagnostic commands in this check module, separate from the public proof
imports. Check the complete growing-memory and numerical-work endpoints, plus
the output certificates and their concrete caller-context regressions.
-/

#print axioms Project.Mergesort.OutputCost.output_body_generated
#print axioms Project.Mergesort.OutputCost.write_shim_body
#print axioms Project.Mergesort.OutputCost.write_shim_cost
#print axioms Project.Mergesort.OutputCost.iteration_prefix_cost
#print axioms Project.Mergesort.OutputCost.iteration_continue_cost
#print axioms Project.Mergesort.OutputCost.iteration_exit_segment
#print axioms Project.Mergesort.OutputCost.loop_segment_serializes
#print axioms Project.Mergesort.OutputCost.output_loop_segment_serializes
#print axioms Project.Mergesort.OutputCost.iteration_exit_cost
#print axioms Project.Mergesort.OutputCost.loop_exact_cost
#print axioms Project.Mergesort.OutputCost.output_loop_exact_cost
#print axioms Project.Mergesort.OutputCost.output_loop_with_post
#print axioms Project.Mergesort.OutputCost.two_words_cost
#print axioms Project.Mergesort.OutputCost.two_words_runner
#print axioms Project.Mergesort.OutputCost.two_words_context_cost
#print axioms Project.Mergesort.OutputCost.two_words_context_runner

#print axioms Project.Mergesort.GrowingTotalProof.mergesort_growing_memory_correct
#print axioms Project.Mergesort.GrowingTotalProof.export_pages_bounded_at_every_prefix
#print axioms Project.Mergesort.ExportWorkProof.export_cost
#print axioms Project.Mergesort.ExportWorkProof.named_export_work
#print axioms Project.Mergesort.ExportWorkProof.workBound_no_growth

#print axioms Project.Mergesort.ExecutionBudget.run_export_sorted
