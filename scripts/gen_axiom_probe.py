#!/usr/bin/env python3
"""Generate the axiom-census probes: one `#print axioms` line per headline declaration.

Scans the SP1Clean tree for the released theorem set (chip soundness/completeness, Sail
bridges + `kind` registrations, faithfulness anchors, witness-conformance anchors, the
timed-grounding capstone layer, deterministic completeness agreement/non-vacuity headlines, and
the coverage guards), resolving each declaration's fully qualified name by tracking
`namespace`/`end` blocks. A wrong FQN fails to elaborate. The existing probe files also record the
required inventory: generation fails before writing either file if a recorded declaration stops
matching, even when another declaration still matches the same target pattern.

Two probe files are emitted, one per library, so each elaborates against exactly the
oleans its build target produces (the CI `audit` job builds only `SP1Clean`; the `test`
job additionally builds `SP1CleanTest` via `lake test`):

- `scripts/axiom_probe.lean` — the main library (`import SP1Clean` only);
- `scripts/axiom_probe_test.lean` — the `SP1CleanTest` conformance and executable
  audit anchors (the native_decide quarantine), importing each test module explicitly.

Usage: `python3 scripts/gen_axiom_probe.py` (from the repo root); then
`lake env lean scripts/axiom_probe.lean` / `... scripts/axiom_probe_test.lean`
(see `scripts/run_audit.sh`). `--check` checks byte identity without writing. Use
`--allow-removals` only to regenerate an intentionally reduced or renamed inventory, and review
the resulting probe diff before updating the axiom snapshots.
"""

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_MAIN = ROOT / "scripts" / "axiom_probe.lean"
OUT_TEST = ROOT / "scripts" / "axiom_probe_test.lean"

# Release/audit headlines are deliberately one target per declaration.  Do not fold these into
# an alternation: target validation is per tuple, so a grouped regex would let one surviving theorem
# hide a renamed or deleted sibling.  This list is the fail-closed inventory for the source-backed
# preprocessing boundary, exact integer-balance transport, the native artifact, and deterministic
# semantic-execution completeness.
# Entries may name theorem or definition headlines; in particular functional-completeness maps are
# deliberately proof-independent definitions whose proof fields are retained by the structure.
EXACT_REQUIRED_THEOREMS = [
    # Complete 32-byte host buffers, constructive completeness, and exact ledgers.
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "circuit_localLength"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "channelsWithGuarantees_eq"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "channelsWithRequirements_eq"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Content.lean", "spec_of_cells"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Content.lean", "Spec.cell_addresses"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Content.lean", "Spec.cell_addresses_nodup"),
    ("SP1Clean/Proofs/Operations/HostBuffer32.lean", "soundness"),
    ("SP1Clean/Proofs/Operations/HostBuffer32.lean", "completeness"),
    ("SP1Clean/Proofs/Operations/HostBuffer32.lean", "circuit"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Populate.lean", "selectedOffset"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Populate.lean", "readAt"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Populate.lean", "populate"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Populate.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Ledger.lean", "main_read_interactions"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Ledger.lean", "main_buffer_interactions"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Ledger.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Ledger.lean", "read_values"),
    ("SP1Clean/Proofs/Operations/HostBuffer32/Ledger.lean", "buffer_values"),
    ("SP1CleanTest/Core/HostBuffer32.lean", "allAlignments"),
    ("SP1CleanTest/Core/HostBuffer32.lean", "windowBounds"),
    ("SP1CleanTest/Core/HostBuffer32.lean", "rejectsChangedMessage"),
    ("SP1CleanTest/Core/HostBuffer32.lean", "rejectsChangedCells"),
    ("SP1CleanTest/Core/HostBuffer32.lean", "overlappingBuffers"),
    # Canonical host-read bytes, exact decoder ledger, and defined-word slice semantics.
    ("SP1Clean/Math/ByteWord.lean", "bytesValue_extract"),
    ("SP1Clean/Math/ByteWord.lean", "toBitVec64_ofByteFields"),
    ("SP1Clean/Model/Core/HostReadWords.lean", "readBytes_of_word"),
    ("SP1Clean/Model/Core/HostReadWords.lean", "readBytes_of_cells"),
    ("SP1Clean/Model/Core/HostReadWords.lean", "readGuest_of_cells"),
    ("SP1Clean/FormalModel/Contracts/HostRamRead.lean", "Spec.message"),
    ("SP1Clean/Native/Operations/HostRamBytes.lean", "populate"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "soundness"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "completeness"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "circuit"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "Spec.readBytes"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "main_read_interactions"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Operations/HostRamBytes.lean", "read_values"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostRamBytes_read_of_word"),
    ("SP1CleanTest/Core/HostRamBytes.lean", "decodesBytes"),
    ("SP1CleanTest/Core/HostRamBytes.lean", "sharedDecoderLedger"),
    ("SP1CleanTest/Core/HostRamBytes.lean", "rejectsMalformed"),
    ("SP1CleanTest/Core/HostRamBytes.lean", "rejectsWrongReadKey"),
    ("SP1CleanTest/Core/HostRamBytes.lean", "spanReads"),
    # Shared physical host reads and exact two-buffer multiplicities.
    ("SP1Clean/Model/Core/HostReadPlan.lean", "physical_cells"),
    ("SP1Clean/Model/Core/HostReadPlan.lean", "physical_nodup"),
    ("SP1Clean/Model/Core/HostReadPlan.lean", "logical_cells_perm"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Formal.lean", "soundness"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Formal.lean", "completeness"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Formal.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "main_access_interactions"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "main_read_interactions"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "memory_values"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "access_values"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "read_values"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Ledger.lean", "access_balance"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populate"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populateSpans"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populateSpans_assumptions"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populateSpans_addresses"),
    ("SP1Clean/Proofs/Chips/HostRamReadChip/Populate.lean", "populateSpans_addresses_nodup"),
    ("SP1CleanTest/Core/HostRamRead.lean", "compiledSpans"),
    ("SP1CleanTest/Core/HostRamRead.lean", "sharedLedger"),
    ("SP1CleanTest/Core/HostRamRead.lean", "rejectsMalformed"),
    ("SP1CleanTest/Core/HostRamRead.lean", "rejectsWrongSharing"),
    ("SP1CleanTest/Core/HostRamRead.lean", "rejectsWrongReads"),
    # Native control handlers, semantic constructors, and exact instruction-range compatibility.
    ("SP1Clean/Proofs/Chips/HostHaltChip/Formal.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/HostHaltChip/Bridge.lean", "exit_value_of_spec"),
    ("SP1Clean/Proofs/Chips/HostHaltChip/Bridge.lean", "executeKind_of_spec"),
    ("SP1Clean/Proofs/Chips/HostHaltChip/Bridge.lean", "run_of_spec"),
    ("SP1Clean/Proofs/Chips/HostHaltChip/Bridge.lean", "stopped_after"),
    ("SP1Clean/Proofs/Chips/HostEnterChip/Bridge.lean", "run_of_spec"),
    ("SP1Clean/Proofs/Chips/HostControlLedger.lean", "main_host_interactions"),
    ("SP1Clean/Proofs/Chips/HostControlLedger.lean", "host_values"),
    ("SP1Clean/Proofs/Chips/HostControlLedger.lean", "main_other_interactions"),
    ("SP1Clean/Proofs/Chips/HostControlLedger.lean", "component_spec_of_byte"),
    ("SP1Clean/Proofs/Chips/HostControlLedger.lean", "component_spec_of_constraints"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "message_clock"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "message_values"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "halt"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "enter"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "halt_assumptions_of_run"),
    ("SP1Clean/Proofs/Chips/HostControlPopulate.lean", "enter_assumptions_of_run"),
    ("SP1Clean/Proofs/Chips/HostControlCompatibility.lean", "exitCodeValid_iff_below_sp1"),
    ("SP1Clean/Proofs/Chips/HostControlCompatibility.lean", "exit_bound_iff"),
    ("SP1Clean/Proofs/Chips/HostControlCompatibility.lean", "instruction_exit_of_spec"),
    ("SP1CleanTest/Core/HostControl.lean", "canonicalExits"),
    ("SP1CleanTest/Core/HostControl.lean", "unusedArguments"),
    ("SP1CleanTest/Core/HostControl.lean", "rejectsMalformed"),
    ("SP1CleanTest/Core/HostControl.lean", "jointLedgers"),
    ("SP1CleanTest/Core/HostControl.lean", "handoffTampering"),
    ("SP1CleanTest/Core/HostControl.lean", "interpreterEffects"),
    ("SP1CleanTest/Core/HostControl.lean", "compiledControls"),
    # Public commitment-bank boundaries and physical ensemble closure.
    ("ToClean/Air/ChannelClosure.lean", "channelGuarantees_of_trivial"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "terminal"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "verifier"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "terminal_interactions"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "verifier_interactions"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "terminal_values"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "verifier_values"),
    ("SP1Clean/Native/Operations/HostCommitBoundary.lean", "terminal_strict"),
    ("SP1Clean/Soundness/HostCommitBank.lean", "terminalView"),
    ("SP1Clean/Soundness/HostCommitBank.lean", "view"),
    ("SP1Clean/Soundness/HostCommitBank.lean", "components_length"),
    ("SP1Clean/Soundness/HostCommitBank.lean", "view_spec_of_byte"),
    ("SP1Clean/Soundness/HostCommitBank.lean", "ordered_history"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "ensemble"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "tables_aligned"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "auxiliary_silent"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "interactions_eq"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "byte_guarantees"),
    ("SP1Clean/Soundness/HostCommitEnsemble.lean", "sound"),
    ("SP1CleanTest/Core/HostCommitBoundary.lean", "emptyBanks"),
    ("SP1CleanTest/Core/HostCommitBoundary.lean", "repeatedBanks"),
    ("SP1CleanTest/Core/HostCommitBoundary.lean", "boundaryTampering"),
    ("SP1CleanTest/Core/HostCommitBoundary.lean", "terminalClocks"),
    ("SP1CleanTest/Core/HostCommitBoundary.lean", "interleavedBanks"),
    # Mutable native commitment calls and their physical bank histories.
    ("SP1Clean/Native/Operations/ClockOrder.lean", "soundness"),
    ("SP1Clean/Native/Operations/ClockOrder.lean", "completeness"),
    ("SP1Clean/Native/Operations/ClockOrder.lean", "circuit"),
    ("SP1Clean/Native/Operations/BoundedWord.lean", "soundness"),
    ("SP1Clean/Native/Operations/BoundedWord.lean", "completeness"),
    ("SP1Clean/Native/Operations/BoundedWord.lean", "circuit"),
    ("SP1Clean/Native/Operations/BoundedWord.lean", "populate"),
    ("SP1Clean/Native/Operations/BoundedWord.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Formal.lean", "soundness"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Formal.lean", "completeness"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Formal.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Ledger.lean", "main_host_interactions"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Ledger.lean", "main_state_interactions"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Ledger.lean", "main_public_interactions"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Ledger.lean", "host_values"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Ledger.lean", "state_values"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Bridge.lean", "next_decode"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Bridge.lean", "executeKind_of_spec"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Populate.lean", "populate"),
    ("SP1Clean/Proofs/Chips/HostCommitChip/Populate.lean", "populate_assumptions"),
    ("SP1Clean/Soundness/HostCommitHistory.lean", "view"),
    ("SP1Clean/Soundness/HostCommitHistory.lean", "ordered_history"),
    ("SP1CleanTest/Core/HostCommit.lean", "validUpdates"),
    ("SP1CleanTest/Core/HostCommit.lean", "clockChecks"),
    ("SP1CleanTest/Core/HostCommit.lean", "rejectsMalformed"),
    ("SP1CleanTest/Core/HostCommit.lean", "jointLedgers"),
    ("SP1CleanTest/Core/HostCommit.lean", "repeatedWrites"),
    ("SP1CleanTest/Core/HostCommit.lean", "brokenHistories"),
    # Generic native-ensemble interfaces and executable input/host boundaries.
    ("SP1Clean/Model/MemoryClock.lean", "lt_of_register_gap"),
    ("SP1Clean/Model/MemoryClock.lean", "gap_encoding"),
    ("SP1Clean/Native/Readers/RegisterRead.lean", "soundness"),
    ("SP1Clean/Native/Readers/RegisterRead.lean", "completeness"),
    ("SP1Clean/Native/Readers/RegisterRead.lean", "circuit"),
    ("SP1Clean/Native/Readers/RegisterReadLedger.lean", "main_memory_interactions"),
    ("SP1Clean/Native/Readers/RegisterReadPopulate.lean", "populate"),
    ("SP1Clean/Native/Readers/RegisterReadPopulate.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Formal.lean", "soundness"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Formal.lean", "completeness"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Formal.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "instruction_of_constraints"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "selector_of_constraints"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "main_host_interactions"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "main_other_interactions"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Ledger.lean", "host_values_of_constraints"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Populate.lean", "populate"),
    ("SP1Clean/Proofs/Chips/HostCallChip/Populate.lean", "populate_assumptions"),
    ("SP1CleanTest/Core/HostCall.lean", "supportedCalls"),
    ("SP1CleanTest/Core/HostCall.lean", "writeLedger"),
    ("SP1CleanTest/Core/HostCall.lean", "otherCallLedgers"),
    ("SP1CleanTest/Core/HostCall.lean", "rejectedReads"),
    ("SP1CleanTest/Core/HostCall.lean", "gatedReads"),
    ("SP1CleanTest/Core/HostCall.lean", "rejectedAliases"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Formal.lean", "soundness"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Formal.lean", "completeness"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Formal.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Ledger.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Ledger.lean", "main_host_interactions"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Ledger.lean", "memory_values"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Ledger.lean", "host_values"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Populate.lean", "populate"),
    ("SP1Clean/Proofs/Chips/HostRamAccessChip/Populate.lean", "populate_assumptions"),
    ("SP1CleanTest/Core/HostRamAccess.lean", "validTransfers"),
    ("SP1CleanTest/Core/HostRamAccess.lean", "rejectsMalformedWords"),
    ("SP1CleanTest/Core/HostRamAccess.lean", "rejectsMalformedTimes"),
    ("SP1CleanTest/Core/HostRamAccess.lean", "retainedLedgers"),
    ("ToClean/Air/CompleteEnsemble.lean", "CompleteEnsemble.statement_iff"),
    ("ToClean/Air/CompleteEnsemble.lean", "EnsembleCompiler.succeeds_iff"),
    ("ToClean/Air/CompleteEnsemble.lean", "EnsembleCompiler.toCompleteEnsemble"),
    ("ToClean/Air/EnsembleExport.lean", "FiniteLookup.ofStatic"),
    ("ToClean/Air/EnsembleExport.lean", "Component.export_constraints_iff"),
    ("ToClean/Air/EnsembleExport.lean", "Component.export_interactions"),
    ("ToClean/Air/EnsembleExport.lean", "EnsembleExport.containsFixed_iff"),
    ("ToClean/Air/EnsembleExport.lean", "EnsembleExport.interactionsNamed_eq"),
    ("SP1Clean/Model/Core/Memory.lean", "readBytes_writeBytes"),
    ("SP1Clean/Model/Core/Memory.lean", "read_writeBytes_of_readOnly"),
    ("SP1Clean/Model/Core/HostIO.lean", "HostIO.readHint_eq_some_iff"),
    ("SP1Clean/Model/Core/HostIO.lean", "HostIO.readHint_preserves_readOnly"),
    ("SP1Clean/Model/Core/HostIO.lean", "HostIO.applyHook_eq_some_iff"),
    ("ToMathlib/ListMapMOption.lean", "mapM_option_eq_some_iff"),
    ("SP1Clean/Model/Core/HostExecution.lean", "HostState.run"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostReadContext.readBytes?_eq_some_iff"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostReadContext.readGuest?_eq_some_iff"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostState.run_eq_some_iff"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostState.execute_write_iff"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostState.execute_hintRead_iff"),
    ("SP1Clean/Model/Core/HostExecutionLaws.lean", "HostState.executeKind_write_permitted"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostMemoryWrite.read_written"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostMemoryWrite.read_outside"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostMemoryWrite.preserves_readOnly"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostExecution.register_frame"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostExecution.rowLaw"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostExecution.matchesStates"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostExecution.preserves_readOnly"),
    ("SP1Clean/Model/Core/HostSail.lean", "HostState.step_sound"),
    ("SP1CleanTest/Core/HostExecution.lean", "allCalls"),
    ("SP1CleanTest/Core/HostExecution.lean", "observedWrite"),
    ("SP1CleanTest/Core/HostExecution.lean", "descriptorDispatch"),
    ("SP1CleanTest/Core/HostExecution.lean", "hookReplies"),
    ("SP1CleanTest/Core/HostExecution.lean", "commitmentUpdates"),
    ("SP1CleanTest/Core/HostExecution.lean", "proofObservations"),
    ("SP1CleanTest/Core/HostExecution.lean", "terminality"),
    ("SP1CleanTest/Core/HostExecution.lean", "paddedHintMemory"),
    ("SP1CleanTest/Core/HostExecution.lean", "sailAdapter"),
    ("SP1CleanTest/Core/HostExecution.lean", "committedDispatch"),
    ("SP1CleanTest/Core/HostExecution.lean", "statefulSequence"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "mem_cells"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "nodup_cells"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "byte_cell_mem"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "byte_outside"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "cell_in_window"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "mem_unionCells"),
    ("SP1Clean/Model/Core/MemorySpan.lean", "nodup_unionCells"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostExecution.footprint?"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostExecution.footprint?_eq_some_iff"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostExecution.footprint_nodup"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostExecution.write_covered"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostState.run_footprint"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostState.readSpans_observed"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostState.footprint_in_window"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostReadContext.readGuest?_congr"),
    ("SP1Clean/Model/Core/HostFootprint.lean", "HostState.run_congr_of_footprint"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostLocations_canonical_nodup"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostReadContext_agrees_of_words"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostRun_of_wordAgreement"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostExecution_ram_frame"),
    ("SP1Clean/Soundness/HostFootprint.lean", "hostExecution_written_word"),
    ("SP1CleanTest/Core/HostFootprint.lean", "byteCovers"),
    ("SP1CleanTest/Core/HostFootprint.lean", "dispatchFootprints"),
    ("SP1CleanTest/Core/HostFootprint.lean", "paddedWriteFootprints"),
    ("SP1CleanTest/Core/HostFootprint.lean", "observedDependency"),
    ("SP1CleanTest/Core/HostFootprint.lean", "failedWordsDoNotAuthenticateBytes"),
    ("SP1CleanTest/Core/HostFootprint.lean", "writtenWordMeaning"),
    ("SP1Clean/Math/WordEquality.lean", "eq_of_toNat_eq"),
    ("SP1Clean/Math/WordEquality.lean", "eq_of_toBitVec64_eq"),
    ("SP1Clean/Model/Core/SyscallCode.lean", "code_injective"),
    ("SP1Clean/Model/Core/SyscallCode.lean", "decode?_eq_some_iff"),
    ("SP1Clean/Model/Core/SyscallCode.lean", "decode?_isSome_iff"),
    ("SP1Clean/Model/Core/SyscallTable.lean", "fixedTable_spec"),
    ("SP1Clean/Model/Core/SyscallTable.lean", "encode_spec"),
    ("SP1Clean/Native/Operations/SyscallCodeGuard.lean", "soundness"),
    ("SP1Clean/Native/Operations/SyscallCodeGuard.lean", "completeness"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Formal.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Bridge.lean", "profile_of_constraints"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Bridge.lean", "constraints_profile"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Bridge.lean", "constraints_original"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Bridge.lean", "interactions_original"),
    ("SP1Clean/Proofs/Chips/CoreSyscallChip/Bridge.lean", "width_original"),
    ("SP1CleanTest/Core/SyscallCode.lean", "exportedInventory"),
    ("SP1CleanTest/Core/SyscallCode.lean", "supportedCodes"),
    ("SP1CleanTest/Core/SyscallCode.lean", "rejectedCodes"),
    ("SP1CleanTest/Core/SyscallCode.lean", "padding"),
    ("SP1CleanTest/Core/SyscallCode.lean", "chipProfileWiring"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "toGuestProgram_wellFormed"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "check_isSome_iff"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "fetchWord_of_mem"),
    ("SP1Clean/Proofs/Chips/FixedProgramProvider.lean", "circuit"),
    # Executable program decoding, computed fixed ROM, and whole-row constructors.
    ("SP1Clean/Model/Core/InstructionDecode.lean", "decode_supported"),
    ("SP1Clean/Model/Core/InstructionDecode.lean", "decode_reservedHint"),
    ("SP1Clean/Proofs/Sail/InstructionDecode.lean", "instructionDecode_agrees"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "row_pc"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "row_address"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "message_rowSpec"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "row_isSome_iff"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "row_committed_of_decode"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "checkProgram_isSome_iff"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "mem_programRows"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "programRows_rowSpec"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "programRows_length"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "programTable_spec"),
    ("SP1Clean/Model/Core/ProgramTable.lean", "programTable_rowSpec"),
    ("SP1Clean/Proofs/Chips/DecodedProgramProvider.lean", "populate_isSome_iff"),
    ("SP1Clean/Proofs/Chips/DecodedProgramProvider.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/DecodedProgramProvider/Bridge.lean", "spec_committed"),
    ("SP1Clean/Proofs/Chips/DecodedProgramProvider/Bridge.lean", "constraints_committed"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "opcodeCoverage"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "literalEncodings"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "operandEdges"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "rejectedEncodings"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "hintAliases"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "sailHintPriority"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "checkedProgram"),
    ("SP1CleanTest/Core/InstructionDecode.lean", "fixedProgramConstraints"),
    # Checked boot and image-derived native byte/word memory circuits.
    ("ToClean/Circuit/StaticTable.lean", "ofRows"),
    ("SP1Clean/Math/ByteWord.lean", "ofBytes_isU64"),
    ("SP1Clean/Math/ByteWord.lean", "toBitVec64_ofBytes"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "initialMemory_rom"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "initialMemory_image"),
    ("SP1Clean/Model/Core/ProgramImage.lean", "initialMemory_zero"),
    ("SP1Clean/Model/Core/SailMemory.lean", "toSailMemory_get?"),
    ("SP1Clean/Model/Core/SailMemory.lean", "toSailMemory_write"),
    ("SP1Clean/Model/Core/MemoryWord.lean", "ramWord64?_of_bytes"),
    ("SP1Clean/Model/Core/Boot.lean", "initialSailState_memory"),
    ("SP1Clean/Model/Core/Boot.lean", "initialSailState_word"),
    ("SP1Clean/Model/Core/Boot.lean", "initialSailState_registersZero"),
    ("SP1Clean/Model/Core/Boot.lean", "initialSailState_loaded"),
    ("SP1Clean/Model/Core/Boot.lean", "hasInitialState"),
    ("SP1Clean/Model/Core/Boot.lean", "dataOf_statementFor"),
    ("SP1Clean/Model/Core/MemoryIntervals.lean", "intervals_count"),
    ("SP1Clean/Model/Core/MemoryIntervals.lean", "intervals_length_le"),
    ("SP1Clean/Model/Core/MemoryIntervals.lean", "intervals_iff"),
    ("SP1Clean/Model/Core/MemoryIntervals.lean", "intervalAt?_sound"),
    ("SP1Clean/Model/Core/MemoryIntervals.lean", "intervalAt?_isSome_iff"),
    ("SP1Clean/Model/Core/MemoryTable.lean", "ByteMemory.fixedTable_sound"),
    ("SP1Clean/Model/Core/MemoryTable.lean", "ByteMemory.fixedTable_read"),
    ("SP1Clean/Native/Operations/InitialMemoryLookup.lean", "circuit"),
    ("SP1Clean/Native/Operations/InitialMemoryLookup.lean", "populate?_sound"),
    ("SP1Clean/Native/Operations/InitialMemoryLookup.lean", "populate?_isSome_iff"),
    ("SP1Clean/Native/Operations/InitialMemoryRead.lean", "circuit"),
    ("SP1Clean/Native/Operations/InitialMemoryRead.lean", "populate?_sound"),
    ("SP1Clean/Native/Operations/InitialMemoryRead.lean", "populate?_isSome_iff"),
    ("SP1Clean/FormalModel/Contracts/InitialMemoryRead.lean", "Spec.initialSailState"),
    ("SP1CleanTest/Core/ProgramImage.lean", "checkedImage_boot"),
    ("SP1CleanTest/Core/InitialMemoryLookup.lean", "constructedRows"),
    ("SP1CleanTest/Core/InitialMemoryLookup.lean", "rejectsForgedRows"),
    ("SP1CleanTest/Core/InitialMemoryRead.lean", "constructedWordRows"),
    ("SP1CleanTest/Core/InitialMemoryRead.lean", "rejectsWrongOffset"),
    # Authenticated native initial records, ordered control keys, and constructive row domains.
    ("SP1Clean/Proofs/Chips/InitialRamProvider.lean", "initialSpec"),
    ("SP1Clean/Proofs/Chips/InitialRamProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/InitialRamProvider.lean", "populate?_sound"),
    ("SP1Clean/Proofs/Chips/InitialRamProvider.lean", "populate?_isSome_iff"),
    ("SP1Clean/Proofs/Chips/InitialRegisterProvider.lean", "initialSpec"),
    ("SP1Clean/Proofs/Chips/InitialRegisterProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/InitialRegisterProvider.lean", "populate_assumptions"),
    ("SP1Clean/Native/Operations/OrderedBoundary.lean", "circuit"),
    ("SP1Clean/Native/Operations/OrderedBoundary.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "populateRam?_sound"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "populateRam?_isSome_iff"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "populateRegister_assumptions"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "ramCircuit"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "registerCircuit"),
    ("SP1Clean/Soundness/RankedGrounding.lean", "targets_nodup_of_endpointBalanced"),
    ("SP1Clean/Soundness/RankedGrounding.lean", "EndpointBalanced.map"),
    ("SP1Clean/Soundness/RankedGrounding.lean", "keys_nodup_of_endpointBalanced"),
    ("SP1Clean/Soundness/InitialMemoryBoundary.lean", "locations_nodup"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "constructedRamRows"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "constructedRegisterRows"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsUnrelatedKeys"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsInvalidBoundaryRows"),
    # Combined image-authenticated native assembly and provider closure.
    ("ToClean/Air/ChannelClosure.lean", "Component.weakSoundness_of_no_guarantees"),
    ("ToClean/Air/ChannelClosure.lean", "EnsembleWitness.channelGuarantees_of_requirements"),
    ("ToClean/Air/ChannelClosure.lean", "EnsembleWitness.channelGuarantees_of_component_requirements"),
    ("SP1Clean/Soundness/NativeCoreEnsemble.lean", "verifier"),
    ("SP1Clean/Soundness/NativeCoreEnsemble.lean", "tables_length"),
    ("SP1Clean/Soundness/NativeCoreEnsemble.lean", "finishedChannel_guarantees"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "initialTables_spec"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "initial_records_authentic"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "afterInitialTables_silent"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "initialWitness_interactions"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "initial_records_locations_nodup"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "public_boot"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "programTable_component"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "program_row_committed"),
    ("SP1Clean/Soundness/NativeCoreBoundaries.lean", "initial_memory_interactions"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "finalTables_spec"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "final_records_canonical"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "afterFinalTables_silent"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "finalWitness_interactions"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "final_records_locations_nodup"),
    ("SP1Clean/Soundness/NativeCoreFinalBoundary.lean", "final_memory_interactions"),
    ("SP1Clean/Soundness/NativeCoreProgram.lean", "component_program_source"),
    ("SP1Clean/Soundness/NativeCoreProgram.lean", "program_pull_committed"),
    ("SP1Clean/Soundness/NativeCoreDecode.lean", "instructionTables_aligned"),
    ("SP1Clean/Soundness/NativeCoreDecode.lean", "instructionRows_constraints"),
    ("SP1Clean/Soundness/NativeCoreDecode.lean", "instructionRows_interaction_mem"),
    ("SP1Clean/Soundness/NativeCoreDecode.lean", "instructionRows_finished_guarantees"),
    ("SP1Clean/Soundness/NativeCoreDecode.lean", "instructionRows_program_committed"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "interior_memoryBinary"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memoryInterior_raw"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memory_interactions"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memoryInterior_signedBinary"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memory_signedBinary"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memory_records_perm"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memory_frontier_balance"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memoryInitialFrontier_authentic"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memoryFinalFrontier_canonical"),
    ("SP1Clean/Soundness/NativeCoreMemory.lean", "memoryInitialFrontier_liveOK"),
    # Exact mixed ordinary/HALT/syscall Memory inventory and conditional refresh elimination.
    ("SP1Clean/Soundness/BumpDecode.lean", "memoryBumpTable_typedMemory_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "haltTable_typedMemory_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "syscallInstrsRow_typedMemory_of_component"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "memoryBumpRow_binary"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "haltRow_binary"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "syscallRow_binary"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "memoryBumpRows_projection"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "haltRows_projection"),
    ("SP1Clean/Soundness/SystemMemoryRows.lean", "syscallRows_projection"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "systemTable_component"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "systemTable_mem"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "systemTable_constraints"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "memoryInterior_split"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "activeInstructionRows_memory"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "executionRows_memory_projection"),
    ("SP1Clean/Soundness/NativeCoreRows.lean", "executionRows_memory_balance"),
    ("SP1Clean/Soundness/NativeCoreRowBalance.lean", "RowMemoryPermutation.refl"),
    ("SP1Clean/Soundness/NativeCoreRowBalance.lean", "RowMemoryPermutation.of_alignsWith"),
    ("SP1Clean/Soundness/NativeCoreRowBalance.lean", "memory_balance_of_row_projection"),
    ("SP1Clean/Soundness/NativeCoreRowBalance.lean", "memoryRefreshes_preserve"),
    ("SP1Clean/Soundness/NativeCoreRowBalance.lean", "memory_refresh_free_of_chronology"),
    # Native mixed State ordering and local touch alignment, before Memory grounding.
    ("SP1Clean/Soundness/BumpDecode.lean", "stateBumpTable_typedState_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "haltTable_typedState_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "syscallInstrsTable_typedState_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "stateBumpTable_spec_of_component"),
    ("SP1Clean/Soundness/BumpDecode.lean", "syscallInstrsRow_typedProgram_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "haltRow_cpuState_bounds_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "syscallInstrsRow_cpuState_bounds_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "syscallInstrsRow_pcArm_spec_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "haltRow_accessTimestamp_bounds_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "syscallInstrsRow_accessTimestamp_bounds_of_component"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipGroundingContracts.rowAligned"),
    ("SP1Clean/Soundness/ChipContracts.lean", "supportedChip_groundingContracts"),
    ("SP1Clean/Soundness/SystemStateRows.lean", "statePairs_projection"),
    ("SP1Clean/Soundness/SystemStateRows.lean", "statePairs_signedBinary"),
    ("SP1Clean/Soundness/SystemStateRows.lean", "stateBumpRow_binary"),
    ("SP1Clean/Soundness/StateChronology.lean", "good_and_bumps_cancel"),
    ("SP1Clean/Soundness/StateChronology.lean", "exhaustiveTrail"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "ExecutionRow.edge_eq_facts"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "state_interiors"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "verifier_state_interactions"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "state_interactions"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "state_signedBinary"),
    ("SP1Clean/Soundness/NativeCoreState.lean", "state_endpointBalanced"),
    ("SP1Clean/Soundness/NativeCoreOrder.lean", "executionRows_advancing"),
    ("SP1Clean/Soundness/NativeCoreOrder.lean", "executionRows_good"),
    ("SP1Clean/Soundness/NativeCoreOrder.lean", "executionRows_ordered"),
    ("SP1Clean/Soundness/NativeCoreOrder.lean", "ordered_rows_timing"),
    ("SP1Clean/Soundness/SystemTouches.lean", "touches_spec"),
    ("SP1Clean/Soundness/NativeCoreTouches.lean", "AlignedFacts.rowOKCore"),
    ("SP1Clean/Soundness/NativeCoreTouches.lean", "syscall_program_committed"),
    ("SP1Clean/Soundness/NativeCoreTouches.lean", "executionRows_aligned"),
    ("SP1Clean/Soundness/NativeCoreTouches.lean", "ordered_aligned_rows"),
    # Prior-record bounds and strict refresh chronology from the native AIR.
    ("SP1Clean/Soundness/ChipContracts.lean", "memoryBump_evidence_of_component"),
    ("SP1Clean/Soundness/ChipContracts.lean", "memoryBump_pushedMessage_clkFacts_of_component"),
    ("SP1Clean/Soundness/ChipContracts.lean", "memoryBump_isRefresh_of_component"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "ordered_rows_window_bound"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "memoryRefreshes_push_bounds"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "memory_consumed_bounds"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "ordered_rows_chronology"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "ordered_memory_rows"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "executionRows_prior_bounds"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "memoryRefreshes_ordered"),
    ("SP1Clean/Soundness/NativeCoreMemoryOrder.lean", "memory_refresh_free"),
    # Mixed read-window transport, canonical carrier, and its derived grounding timeline.
    ("SP1Clean/Model/Semantics/DurationTime.lean", "ofDurations"),
    ("SP1Clean/Model/Semantics/DurationTime.lean", "ofDurations_start_le"),
    ("SP1Clean/Model/Semantics/DurationTime.lean", "ofDurations_start_zero"),
    ("SP1Clean/Model/Semantics/DurationTime.lean", "ofDurations_step"),
    ("SP1Clean/Model/Semantics/DurationTime.lean", "ofDurations_end"),
    ("SP1Clean/Soundness/RefreshWiring.lean", "rowOKCore_alignedOf_pullRewrite"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "RowOKCore.readsInWindow"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "WindowAligned.pullCurrency"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "WindowAligned.stepFact"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "WindowAligned.frameFact"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "WindowAligned.pullRewrite"),
    ("SP1Clean/Soundness/MixedRowTransport.lean", "WindowAligned.stateRespell"),
    ("SP1Clean/Soundness/WalkTimeline.lean", "rowTimeline"),
    ("SP1Clean/Soundness/WalkTimeline.lean", "rowTimeline_start"),
    ("SP1Clean/Soundness/WalkTimeline.lean", "rowTimeline_step_of_walk"),
    ("SP1Clean/Soundness/WalkTimeline.lean", "rowTimeline_end_of_walk"),
    ("SP1Clean/Soundness/NativeCoreTransport.lean", "executionRows_readsInWindow"),
    ("SP1Clean/Soundness/NativeCoreTransport.lean", "AlignedFacts.windowAligned"),
    ("SP1Clean/Soundness/NativeCoreTransport.lean", "grounding_carrier"),
    ("SP1Clean/Soundness/NativeCoreTransport.lean", "GroundingCarrier.stateBalance"),
    ("SP1Clean/Soundness/NativeCoreTransport.lean", "GroundingCarrier.engineFacts"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.timeline"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.timeline_start"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.timeStep"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.finalClock"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.initialStateTruth"),
    ("SP1Clean/Soundness/NativeCoreGrounding.lean", "GroundingCarrier.ground_of_steps"),
    # Component-local ordinary execution and the reduced native grounding boundary.
    ("SP1Clean/Soundness/RowSoundness.lean", "decodedRowStaticInputs_of_witness"),
    ("SP1Clean/Soundness/RowSoundness.lean", "DecodedRowStaticInputs.channels"),
    ("SP1Clean/Soundness/RowSoundness.lean", "DecodedRowStaticInputs.programRowSpec"),
    ("SP1Clean/Soundness/RowSoundness.lean", "DecodedRowStaticInputs.chipSpec"),
    ("SP1Clean/Soundness/RowSoundness.lean", "DecodedRowStaticInputs.fullRequirements"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipReadinessLocalContract"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipAssumptionsLocalContract"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipGroundingContracts.wiring"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipGroundingContracts.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipGroundingContracts.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ChipGroundingContracts.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "RTypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "RTypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "RTypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ITypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ITypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ITypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ALUTypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ALUTypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ALUTypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableALUTypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableALUTypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableALUTypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "JTypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "JTypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "JTypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ConditionalITypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ConditionalITypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ConditionalITypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableITypeChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableITypeChipGroundingData.routing"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableITypeChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "LoadMemoryChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "LoadMemoryChipGroundingData.routingFlag"),
    ("SP1Clean/Soundness/ChipContracts.lean", "LoadMemoryChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableLoadMemoryChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableLoadMemoryChipGroundingData.routingFlag"),
    ("SP1Clean/Soundness/ChipContracts.lean", "ImmutableLoadMemoryChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "StoreMemoryChipGroundingData.assumptions"),
    ("SP1Clean/Soundness/ChipContracts.lean", "StoreMemoryChipGroundingData.readiness"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalChip_assumptionsLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalChip_routingLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalChip_readinessLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "uTypeChip_assumptionsLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "uTypeChip_routingLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "uTypeChip_readinessLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalrChip_assumptionsLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalrChip_routingLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "jalrChip_readinessLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "branchChip_assumptionsLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "branchChip_routingLocal"),
    ("SP1Clean/Soundness/ChipContracts.lean", "branchChip_readinessLocal"),
    ("SP1Clean/Soundness/SyscallGrounding.lean", "ordinaryStepFactG_of_advanceOnTrajectory"),
    ("SP1Clean/Soundness/SyscallGrounding.lean", "ordinaryFrameFactG_of_advanceOnTrajectory"),
    ("SP1Clean/Soundness/SyscallWiring.lean", "ChipGroundingContracts.engineFactsLocalG"),
    ("SP1Clean/Soundness/NativeCoreInstructionExecution.lean", "instructionRows_staticInputs"),
    ("SP1Clean/Soundness/NativeCoreInstructionExecution.lean", "GroundingCarrier.originalTimeStep"),
    ("SP1Clean/Soundness/NativeCoreInstructionExecution.lean", "GroundingCarrier.instruction_engineFacts"),
    ("SP1Clean/Soundness/NativeCoreInstructionExecution.lean", "GroundingCarrier.ground_of_system_steps"),
    # The mixed trajectory, exact event positions, and derived HALT execution.
    ("SP1Clean/Model/Machine/Shard.lean", "withHalt"),
    ("SP1Clean/Model/Machine/Shard.lean", "withHalt_run_zero"),
    ("SP1Clean/Model/Machine/Shard.lean", "withHalt_run_nonzero"),
    ("SP1Clean/Soundness/WalkTimeline.lean", "rowTimeline_pullTime_of_getElem?"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "haltEventOfRow"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "ExecutionRow.event"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.events"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.trajectory"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.trajectory_zero"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.ordered_at"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.event_at"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.trajectory_ordinary"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.trajectory_halt"),
    ("SP1Clean/Soundness/HaltGrounding.lean", "HaltChip.codeZero_of_shallow"),
    ("SP1Clean/Soundness/HaltGrounding.lean", "halt_engineFactsG"),
    ("SP1Clean/Soundness/NativeCoreHaltExecution.lean", "haltRows_staticFacts"),
    ("SP1Clean/Soundness/NativeCoreHaltExecution.lean", "GroundingCarrier.halt_engineFacts"),
    ("SP1Clean/Soundness/NativeCoreHaltExecution.lean", "GroundingCarrier.ground_of_host_steps"),
    # Component-local syscall laws and semantic events on the native mixed trajectory.
    ("SP1Clean/Soundness/BumpDecode.lean", "syscallInstrsRow_spec_of_component"),
    ("SP1Clean/Soundness/TypedTimeContracts.lean", "syscallInstrsRow_opAValue_isU64_of_component"),
    ("SP1Clean/Soundness/SyscallInputs.lean", "syscallInstrsRow_memoryGuarantees_of_component"),
    ("SP1Clean/Soundness/SyscallInputs.lean", "syscallInstrsRow_programRowSpec_of_component"),
    ("SP1Clean/Soundness/SyscallInputs.lean", "syscallInstrsRow_contract_of_component"),
    ("SP1Clean/Soundness/SyscallInputs.lean", "syscallRow_sourceValues"),
    ("SP1Clean/Soundness/SyscallRowSemantics.lean", "arm_pcAdvance_of_pcBound"),
    ("SP1Clean/Soundness/SyscallRowSemantics.lean", "rowLaw_of_spec_and_pulledFacts"),
    ("SP1Clean/Soundness/NativeCoreTrajectory.lean", "GroundingCarrier.trajectory_syscall"),
    ("SP1Clean/Soundness/NativeCoreSyscallSemantics.lean", "syscallRows_contract"),
    ("SP1Clean/Soundness/NativeCoreSyscallSemantics.lean", "syscallRows_rowLaw"),
    ("SP1Clean/Soundness/NativeCoreSyscallSemantics.lean", "syscallRows_sourceValues"),
    ("SP1Clean/Soundness/NativeCoreSyscallSemantics.lean", "GroundingCarrier.syscall_eventStep_of_currency"),
    ("SP1Clean/Soundness/NativeCoreSyscallSemantics.lean", "GroundingCarrier.syscall_eventStep_of_grounded"),
    ("SP1CleanTest/Audit/MixedMemoryRows.lean", "syscallKeepsMixedReadTimes"),
    ("SP1CleanTest/Audit/MixedMemoryRows.lean", "syscallPcArmCrossesLimb"),
    ("SP1Clean/Soundness/TypedSelectors.lean", "MemoryBumpChip.selectorBinary_of_shallow"),
    ("SP1Clean/Soundness/TypedMemorySelectors.lean", "signedVal_binary_of_selector_gated"),
    ("SP1Clean/Soundness/WitnessDecode.lean", "InstructionTablesAligned.of_components"),
    ("SP1Clean/Proofs/Chips/ProgramProviderChip.lean", "main_program_interactions"),
    ("SP1Clean/Proofs/Chips/FixedProgramProvider.lean", "program_interaction_payload"),
    ("SP1Clean/Proofs/Chips/DecodedProgramProvider/Bridge.lean", "program_interaction_payload"),
    ("ToClean/Circuit/EmittedInteraction.lean", "eval_emitted"),
    ("SP1Clean/Soundness/OrderedBoundaryEnsemble.lean", "keys_nodup_of_tables"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "indexedRows_spec_of_tables"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "records_valid_of_tables"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "records_locations_nodup_of_tables"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "nativeVerifierEndpoints"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsForgedBoot"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "nativeBoundaryInventories"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "finalizersDeferMemoryGuarantees"),
    # Fixed native memory-inventory endpoints and the physical Clean control ledger.
    ("ToMathlib/ListFilterMap.lean", "nodup_filterMap_of_nodup_map"),
    ("ToClean/Air/UnitBalance.lean", "transitionLedger_perm"),
    ("ToClean/Air/UnitBalance.lean", "balanced_unit_iff"),
    ("ToClean/Air/UnitBalance.lean", "transitionLedger_balanced_iff"),
    ("ToClean/Air/TransitionView.lean", "readRows_interactions"),
    ("ToClean/Air/TransitionView.lean", "readRows_spec"),
    ("ToClean/Air/TransitionView.lean", "readRows_eq_indexed"),
    ("ToClean/Air/TransitionView.lean", "readIndexedRows_spec"),
    ("ToClean/Air/TransitionView.lean", "readIndexedRows_keys_nodup"),
    ("SP1Clean/Native/Operations/OrderedBoundary.lean", "main_interactions"),
    ("SP1Clean/Native/Operations/OrderedBoundary.lean", "subcircuit_interactions"),
    ("SP1Clean/Native/Operations/OrderedBoundary.lean", "interactionValues"),
    ("SP1Clean/Native/Operations/OrderedBoundaryEnd.lean", "circuit"),
    ("SP1Clean/Native/Operations/OrderedBoundaryEnd.lean", "populate_assumptions"),
    ("SP1Clean/Native/Operations/OrderedBoundaryEnd.lean", "main_interactions"),
    ("SP1Clean/Native/Operations/OrderedBoundaryEnd.lean", "interactionValues"),
    ("SP1Clean/Native/Operations/OrderedBoundaryVerifier.lean", "circuit"),
    ("SP1Clean/Native/Operations/OrderedBoundaryVerifier.lean", "main_interactions"),
    ("SP1Clean/Native/Operations/OrderedBoundaryVerifier.lean", "interactionValues"),
    ("SP1Clean/Proofs/Chips/OrderedInitialProvider.lean", "main_interactions"),
    ("SP1Clean/Soundness/RankedGrounding.lean", "rankedKeys_nodup_list"),
    ("SP1Clean/Soundness/OrderedBoundaryEnsemble.lean", "interactions_eq"),
    ("SP1Clean/Soundness/OrderedBoundaryEnsemble.lean", "endpointBalanced"),
    ("SP1Clean/Soundness/OrderedBoundaryEnsemble.lean", "exhaustiveTrail"),
    ("SP1Clean/Soundness/OrderedBoundaryEnsemble.lean", "keys_nodup_of_specs"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "providerView"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "terminalView"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "keys_nodup"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "records_authentic"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "records_locations_nodup"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "emptyInventory"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "mixedInventory"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsMalformedInventories"),
    # Canonical finalization and the shared physical Memory-inventory proof.
    ("SP1Clean/FormalModel/Contracts/MemoryBoundary.lean", "InitialSpec.canonical"),
    ("SP1Clean/FormalModel/Contracts/MemoryBoundary.lean", "ram_location_of_key"),
    ("ToClean/Air/TransitionView.lean", "readIndexedRows_interactions"),
    ("SP1Clean/Proofs/Chips/OrderedMemoryProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/OrderedMemoryProvider.lean", "main_interactions"),
    ("SP1Clean/Proofs/Chips/OrderedMemoryProvider.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/OrderedMemoryProvider.lean", "populate_assumptions"),
    ("SP1Clean/Proofs/Chips/InitialRegisterProvider.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/InitialRamProvider.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/FinalRegisterProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/FinalRegisterProvider.lean", "canonical"),
    ("SP1Clean/Proofs/Chips/FinalRegisterProvider.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/FinalRamProvider.lean", "circuit"),
    ("SP1Clean/Proofs/Chips/FinalRamProvider.lean", "canonical"),
    ("SP1Clean/Proofs/Chips/FinalRamProvider.lean", "proverAssumptions_iff"),
    ("SP1Clean/Proofs/Chips/FinalRamProvider.lean", "main_memory_interactions"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "registerCircuit"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "ramCircuit"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "populateRegister?_sound"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "populateRam?_sound"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "populateRegister?_isSome_iff"),
    ("SP1Clean/Proofs/Chips/OrderedFinalProvider.lean", "populateRam?_isSome_iff"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "providerView"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "terminalView"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "terminalView_memory_interactions"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "records_valid"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "records_locations_nodup"),
    ("SP1Clean/Soundness/OrderedMemoryEnsemble.lean", "memory_interactions_eq"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "inventory"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "recordFor_interactions"),
    ("SP1Clean/Soundness/InitialMemoryEnsemble.lean", "memory_interactions_eq"),
    ("SP1Clean/Soundness/FinalMemoryEnsemble.lean", "inventory"),
    ("SP1Clean/Soundness/FinalMemoryEnsemble.lean", "records_valid"),
    ("SP1Clean/Soundness/FinalMemoryEnsemble.lean", "records_locations_nodup"),
    ("SP1Clean/Soundness/FinalMemoryEnsemble.lean", "recordFor_interactions"),
    ("SP1Clean/Soundness/FinalMemoryEnsemble.lean", "memory_interactions_eq"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "constructedFinalRows"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsInvalidFinalRows"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "finalInventories"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "rejectsMalformedFinalInventories"),
    ("SP1CleanTest/Core/MemoryBoundary.lean", "pairedMemoryBoundary"),
    # One production field spelling and the common shard/bus representation laws.
    ("SP1Clean/Model/SP1Field.lean", "sp1Prime_prime"),
    ("SP1Clean/Model/SP1Field.lean", "pow17_lt_sp1Prime"),
    ("SP1Clean/Model/SP1Field.lean", "pow24_lt_sp1Prime"),
    ("SP1Clean/Model/SP1Field.lean", "pow25_lt_sp1Prime"),
    ("SP1Clean/Model/InteractionBus.lean", "balanced_toSigned"),
    ("SP1Clean/Model/Machine/Shard.lean",
     "CoreShardSemanticWitness.trace?_ofOrdinaryTrace"),
    ("SP1Clean/Model/Machine/Shard.lean",
     "CoreShardSemanticWitness.evaluatedTrace_initialState"),
    ("SP1Clean/FormalModel/CoreShard.lean", "executionTrace"),
    # Source-backed canonical preprocessing inventory and its literal Clean ledger.
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "inventoryPreprocessedKeys_eq_inventoryRows"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "inventoryPreprocessedKeys_nodup"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalByteRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalRangeRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean", "canonicalProgramRows_mem_source"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "extractedPreprocessedProviderTables_constraints"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "extractedPreprocessedProviderTables_cleanAccesses"),
    ("SP1Clean/Composition/PreprocessedProviders.lean",
     "skeleton_append_recountedPreprocessedProviderAccesses_balanced"),
    # Boundary/system providers and the exact provider segment.
    ("SP1Clean/Composition/MemoryBoundary.lean", "memoryGlobalInitMultiplicity_bool"),
    ("SP1Clean/Composition/MemoryBoundary.lean", "memoryGlobalFinalizeMultiplicity_bool"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "memoryBoundaryProviderContract_of_relation"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "extractedMemoryBoundaryTables_constraints"),
    ("SP1Clean/Composition/MemoryBoundary.lean",
     "extractedMemoryBoundaryTables_activeAccesses"),
    ("SP1Clean/Composition/SystemTables.lean", "extractedBumpTables_constraints"),
    ("SP1Clean/Composition/SystemTables.lean", "extractedBumpTables_accesses"),
    # Shared transition/compiler vocabulary and the exact-row semantic fan-out. These are kept
    # explicit so a direction-specific replacement or a silently dropped system endpoint fails
    # generation rather than merely shrinking the census.
    ("SP1Clean/Model/Semantics/TransitionView.lean",
     "projectSP1Transition?_components"),
    ("SP1Clean/Soundness/LocalExecution.lean",
     "GroundedRow.supportedSP1Transition"),
    ("SP1Clean/Proofs/Completeness/ExecutionCompiler.lean",
     "compileLocatedTransitions?_exists_of_views"),
    ("SP1Clean/Proofs/Completeness/ExecutionCompiler.lean",
     "SupportedCoreShardExecutionValid.compileExecution?_exists_of_instructionEventsReady"),
    ("SP1Clean/FormalModel/CoreAIRRelation.lean",
     "System.localValid_of_relationFor"),
    ("SP1Clean/FormalModel/CoreAIRRelation.lean",
     "System.execution_of_shardRelation"),
    ("SP1Clean/FormalModel/CoreAIRRelation.lean",
     "System.memoryBoundary_of_shardRelation"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "transportMemoryBumpRow_input"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "transportStateBumpRow_input"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "syscallCore_assertions_iff"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "syscallCore_syscall_receive_mem"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "syscallCore_rowFacts_of_relation"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "syscallInstrs_syscall_send_mem"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "memoryLocal_assertions_iff"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "memoryLocal_memory_endpoints_mem"),
    ("SP1Clean/Composition/CoreSystemSemantics.lean", "memoryLocal_rowFacts_of_relation"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_components"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_constraints"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTableBundle_constraints"),
    ("SP1Clean/Composition/ProviderSegment.lean", "exactProviderTables_cleanAccesses"),
    # Complete native table assembly, literal-ledger recount, and public semantic capstones.
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_init_u8Pair"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_final_u8Pair"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeBoundary_limbBounds"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTables_components"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTableBundle_components"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeTables_constraints"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeEnsembleWitness_verifierTable"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeEnsembleWitness_constraints"),
    ("SP1Clean/Composition/CoreEnsemble.lean",
     "exactNativeAllCleanAccesses_eq_interactions"),
    ("SP1Clean/Composition/CoreEnsemble.lean", "exactNativeAllCleanAccesses_perm"),
    ("SP1Clean/Composition/CoreEnsemble.lean",
     "exactNativeAllCleanAccesses_preprocessedBalance"),
    ("SP1Clean/Composition/CoreArtifact.lean",
     "exactNativeEnsembleWitness_preprocessedIntegerBalance"),
    ("SP1Clean/Composition/CoreArtifact.lean", "exactNativeEnsembleWitness_balancedChannels"),
    ("SP1Clean/Composition/CoreArtifact.lean",
     "exactNativeArtifact_supportedCoreNativeRelation"),
    ("SP1Clean/Composition/CoreArtifact.lean", "exactNativeArtifact_sailExecution"),
    # The representation and semantic agreement seams used by the deterministic native compiler.
    # Keep these exact (rather than one alternation per file): deleting one side of an agreement
    # layer must fail generation even when a sibling theorem survives.
    ("SP1Clean/Proofs/Completeness/NativeStateAgreement.lean",
     "nativeTrace_stateAgreement"),
    ("SP1Clean/Proofs/Completeness/NativeStateAgreement.lean",
     "NativeTraceReady.stateLedgerPerm"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryLedgerPermHandoffChains"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "NativeTraceReady.memoryLedgerPerm"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryInitProviderUnique"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryFinalizeProviderUnique"),
    ("SP1Clean/Proofs/Completeness/NativeMemoryAgreement.lean",
     "nativeTrace_memoryInitProviderBound"),
    ("SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean",
     "nativeProgramKey_decodedInROM"),
    ("SP1Clean/Proofs/Completeness/NativeProgramAgreement.lean",
     "nativeTrace_programProviderBound"),
    ("SP1Clean/Proofs/Completeness/NativeBoundaryAgreement.lean",
     "NativeTraceReady.semanticBoundary"),
    # Deterministic common-shard -> native ensemble completeness and paired correctness surface.
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "supported_core_native_functionalCompleteness"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "supported_core_native_shard_functionalCompleteness"),
    ("SP1Clean/Soundness/NativeCompleteness.lean", "supported_core_native_complete"),
    ("SP1Clean/Soundness/NativeCompleteness.lean", "supported_core_native_shard_complete"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "supported_core_native_shard_correct_of_totality"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "supported_core_native_shard_language_eq_of_totality"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     "sp1Ensemble_statement_of_supported_execution"),
    # Executable joint-premise regression for the exact admissible source and both capstones.
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_nativeTraceReady"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorSemanticWitness_trace"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_admissible"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_yields_airWitness"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_yields_ensembleStatement"),
    ("SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean",
     "anchorExecution_bounded_roundTrip"),
    # Joined active-path regression: one official Sail step, its exact deterministic compiler
    # event, the nonempty bounded AIR witness, and soundness back into the shared semantic language.
    ("SP1CleanTest/Audit/JointNonVacuity.lean", "anchorStep"),
    ("SP1CleanTest/Audit/ActiveNativeCompleteness.lean",
     "activeView_compiled_event_exists"),
    ("SP1CleanTest/Audit/ActiveNativeCompleteness.lean", "activeExecution_semantic"),
    ("SP1CleanTest/Audit/ActiveNativeCompleteness.lean",
     "activeTrace_boundedNativeRelation"),
    ("SP1CleanTest/Audit/ActiveNativeCompleteness.lean", "activeTrace_bounded_roundTrip"),
]

EXACT_REQUIRED_TARGETS = [
    (path, rf"(?:theorem|def)\s+({re.escape(name)})(?=\s|[({{:]|$)")
    for path, name in EXACT_REQUIRED_THEOREMS
]

# (glob, declaration-name regex) → collect matching theorems/defs with their namespace.
TARGETS = [
    ("SP1Clean/Proofs/Chips/*/Formal.lean",
     # Probe the bundled circuit as well as its named proof fields.  In particular, a deferred
     # channel-law field lives only inside `circuit`, and every deferred completeness proof is
     # retained transitively by that structure even when a soundness consumer never projects it.
     r"(?:theorem|def)\s+(soundness|completeness|contractSoundness|evidenceSoundness|circuit)\b"),
    # Branch isolates its heavy soundness/completeness proofs in `Core.lean`; `Formal.circuit`
    # retains both, but direct probes keep the audit ledger readable.
    ("SP1Clean/Proofs/Chips/BranchChip/Core.lean",
     r"theorem\s+(soundness|completeness)\b"),
    # DivRem keeps its heavyweight completeness driver outside `Formal.lean`; without this explicit
    # target the textual admission gate saw the `stop`, but the axiom census silently skipped the
    # declaration itself.
    ("SP1Clean/Proofs/Chips/DivRemChip/Completeness/Driver.lean",
     r"theorem\s+(completeness)\b"),
    # DivRem's isolated, circuit-independent contract and evidence layer is a first-class audit
    # surface: probe every named theorem rather than only the admitted whole-chip extraction seam.
    # Dotted capture: `theorem Unsigned64Evidence.total` must probe the theorem, not collapse to
    # the (already-probed) structure name at the first `.`.
    ("SP1Clean/FormalModel/Contracts/DivRem.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/DivRemChip/Cases.lean", r"(?:theorem|lemma)\s+([\w.]+)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"theorem\s+(correct_\w+|\w*reaches_sail\w*)\b"),
    ("SP1Clean/Proofs/Chips/*/Bridge.lean", r"def\s+(kind)\b"),
    ("SP1Clean/Faithful/*.lean", r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/DivRemChip/Exact.lean",
     r"(?:theorem|def)\s+(\w*faithful\w*)\b"),
    ("SP1Clean/Faithful/SupportedMachine.lean",
     r"(?:theorem|def)\s+(supportedChipFaithfulness\w*|"
     r"instructionOracleMainWidth|instructionOracleMainWidth_isSome_iff|"
     r"supportedInstructionMainWidths)\b"),
    # W6: the transport layer — the generic per-table transport and all three public theorem
    # families for each of its twenty-five instantiations, plus the aggregate identity that makes
    # the transported tables the ensemble's own.
    # These are the declarations that put `Faithful/` inside a live import closure.
    # buildRow_input_get / eval_var_buildRow_input_get moved down to Model/CleanLedger.lean in
    # 2026-08 (pure Clean Component/ProvableType vocabulary; the completeness layer needs them too).
    ("SP1Clean/Model/CleanLedger.lean",
     r"theorem\s+(buildRow_input_get|eval_var_buildRow_input_get)\b"),
    ("SP1Clean/Composition/Table.lean",
     r"theorem\s+(signedVal_eq_zero_iff|transportTable_constraints|"
     r"transportTable_accesses_perm|transportTable_spec)\b"),
    ("SP1Clean/Composition/Chips.lean",
     r"theorem\s+(\w+Chip_transportTable_(?:constraints|accesses|spec))\b"),
    ("SP1Clean/Composition/Ensemble.lean",
     r"theorem\s+(transported_map_component|transportedInstructionActiveAccesses_perm|"
     r"transported_constraints)\b"),
    ("SP1Clean/Composition/Extracted.lean",
     r"theorem\s+(extractedInstructionRows_valid|extracted_instructionTables_constraints)\b"),
    ("SP1Clean/Composition/Balance.lean",
     r"theorem\s+(signedSum_eq_sent_sub_received|signedSum_eq_zero)\b"),
    *EXACT_REQUIRED_TARGETS,
    ("SP1Clean/Soundness/CoreAIRSyscallFree.lean",
     r"theorem\s+(publicCommitOperand|deferredCommitOperand|publicCommitSetsFlag|"
     r"deferredCommitSetsFlag|syscallTranscript)\b"),
    # The real-row satisfiability battery: every named anchor (28 per-chip rows + the Spec-level
    # companions + the nonempty-assert-list guard) is census-visible so its native_decide trust is
    # disclosed per-declaration like the conformance anchors.
    ("SP1CleanTest/NonVacuityReal.lean", r"theorem\s+(\w+)\b"),
    # Independent audit regressions freeze the full native constraint checks and exact evaluated
    # bus footprints.  The active-trace declarations additionally keep the generated one-row trace,
    # its particular native witness, and the official-Sail consequence census-visible end to end.
    ("SP1CleanTest/Audit/*.lean",
     r"theorem\s+(constraints_hold|interactions_exact|program_projection|"
     r"bytePaddingTable_constraints|bytePaddingTable_busNeutral|"
     r"byteAggregateTable_constraints|byteAggregateTable_preservesMultiplicity|"
     r"rangeAggregateTable_constraints|rangeAggregateTable_preservesMultiplicity|"
     r"programAggregateTable_constraints|programAggregateTable_preservesMultiplicity|"
     r"byteAggregateTable_accesses|byteAggregateLedger_accesses|"
     r"byteAggregate_signedVal|byteAggregateLedger_integerBalanced|"
     r"byteAggregateLedger_balancedInteractions|"
     r"memoryInitTable_constraints|memoryInitTable_booleanBranches|"
     r"memoryFinalizeTable_constraints|memoryFinalizeTable_booleanBranches|"
     r"supportedCoreNativeRelation_nonvacuous|traceGeneratableRelation_nonvacuous|"
     r"anchorTrace_yields_airWitness|activeTrace_traceGeneratable|activeTrace_nativeRelation|"
     r"verifierBytePulls_asymmetricClockOrder|"
     r"active_instruction_count|active_decoded_instruction_row_count|"
     r"active_real_decoded_instruction_row_count|"
     r"activeTrace_yields_airWitness|activeTrace_yields_sailExecution|"
     r"activeTrace_suppliesDemand|activeTrace_stateHandoff|activeTrace_memoryHandoff|"
     r"activePaddedTrace_stateHandoff|activePaddedTrace_stateHandoff_raw_false)\b"),
    # The W4 completeness layer's provider/ledger half: the built provider and verifier tables'
    # constraint theorems, and the generic push/pull balance bridge the W5 assembly consumes.
    ("SP1Clean/Proofs/Completeness/Providers.lean",
     r"(?:theorem|lemma)\s+(traceTable_constraints|"
     r"ByteEntry\.signedVal_multiplicity|RangeEntry\.signedVal_multiplicity|"
     r"RomEntry\.signedVal_multiplicity)\b"),
    ("SP1Clean/Proofs/Completeness/Ledger.lean",
     r"theorem\s+(balancedInteractions_of_signed_perm|balancedInteractions_of_flatMap_perm|"
     r"balanceOf_eq_pushed_sub_pulled)\b"),
    # The provider closure. The ledger-level balance theorem and the key-selection lemmas that make
    # its two side conditions structural rather than caller-supplied; plus the trace-level
    # instantiation and the two conservativeness results that pin the closure out of State/Memory.
    # The ledger-level half of the provider closure moved to Model/InteractionBus.lean in 2026-08
    # (its namespace already said so); the trace-level half stayed in Closure.lean.
    # Tier 1 of the provider closure: what one built provider row emits, in Clean orientation.
    ("SP1Clean/Proofs/Completeness/ProviderInteractions.lean",
     r"theorem\s+(interactions_eq_interactionsWith_of_onlyChannel|"
     r"u8Range_interactionsWith_byte|u8Range_buildRow_cleanAccesses|"
     r"msb_buildRow_result|msb_buildRow_cleanAccesses|"
     r"and_buildRow_result_val|and_buildRow_cleanAccesses|"
     r"or_buildRow_cleanAccesses|xor_buildRow_cleanAccesses|"
     r"ltu_buildRow_cleanAccesses|range_buildRow_cleanAccesses|"
     r"program_buildRow_cleanAccesses)\b"),
    # Tier 2: a whole provider table's ledger is exactly its occurrence list.
    # Tier 3: the provider lists a shard's demand determines, and the balance that follows.
    ("SP1Clean/Proofs/Completeness/ClosureRealization.lean",
     r"theorem\s+(family_ledger_eq|family_multiplicitySum|program_round|"
     r"closureRange_contribution|providerLedger_multiplicitySum|"
     r"fullLedger_multiplicitySum|byteProgram_balanced|"
     r"fullLedger_multiplicitySum_channel|channelLedger_isConsistentBalanced|"
     r"channelLedger_isConsistentBalanced_of_handoff)\b"),
    # The ensemble's own channel discipline, which the orientation bridge rests on.
    # The two `_core` spellings are the syscall-table wave's: the syscall chip speaks on seven
    # buses, so the provider/all-tables statements gained a disjunct and were renamed.  Naming the
    # current spellings matters — `\b` after an alternation does *not* match a `_core` suffix, so
    # the old names went on matching nothing and the census silently lost both probes.
    ("SP1Clean/Soundness/EnsembleChannels.lean",
     r"theorem\s+(sp1Tables_channels_subset|sp1ProviderTables_channels_subset_core|"
     r"sp1AllTables_channels_subset_core|sp1Ensemble_allTables_channels_subset|"
     r"channel_eq_of_name_eq)\b"),
    # Phase 3: the clock bridge, the generator's shadow bookkeeping, and the ALU fold.
    ("SP1Clean/FormalModel/TraceGen/ClockBridge.lean",
     r"theorem\s+(ordinarySchedule_duration_eq|accessOffsets_ordered|"
     r"clockAt_ordinary_eq|clockAt_ordinary_mod)\b"),
    ("SP1Clean/FormalModel/TraceGen/GenState.lean",
     r"theorem\s+(initial_bounded|prevTs_lt|stepRType_bounded)\b"),
    ("SP1Clean/FormalModel/TraceGen/AluGenerator.lean",
     r"theorem\s+(aluEvents_wellFormed|witnessStep_wellFormed|"
     r"witnessEvents_wellFormed)\b"),
    ("SP1Clean/FormalModel/TraceGen/SailAlu.lean",
     r"theorem\s+(aluStepOfState_wellFormed|aluStepOfState_isSome|"
     r"aluStepsFrom_wellFormed|aluStepsFrom_length_le)\b"),
    ("SP1Clean/Proofs/Completeness/AluGeneration.lean",
     r"theorem\s+(aluEvents_addTable_constraints|aluEvents_addTable_guarantees|"
     r"aluEvents_subTable_constraints|sailRun_addTable_constraints|"
     r"sailRun_subTable_constraints|sailRun_rows_le)\b"),
    # Phase 2: the two system tables' rows are built from crossings, not supplied.
    ("SP1Clean/FormalModel/TraceGen/Bump.lean",
     r"theorem\s+(stateBump_spec|memoryBump_spec|stateBumpTraceInputs_spec|"
     r"memoryBumpTraceInputs_spec|stateBumpEvent_wellFormed_witness|"
     r"memoryBumpEvent_wellFormed_witness)\b"),
    ("SP1Clean/Proofs/Completeness/ProviderTables.lean",
     r"theorem\s+(u8Range_traceTable_cleanAccesses|msb_traceTable_cleanAccesses|"
     r"and_traceTable_cleanAccesses|or_traceTable_cleanAccesses|"
     r"xor_traceTable_cleanAccesses|ltu_traceTable_cleanAccesses|"
     r"range_traceTable_cleanAccesses|program_traceTable_cleanAccesses)\b"),
    # A1: a built instruction table's State ledger — registry-wide, no case split.
    ("SP1Clean/Proofs/Completeness/ChipLedger.lean",
     r"theorem\s+(supportedChip_table_mem_allTables|tableStateLedger_eq_nil|"
     r"tableStateLedger_eq_of_component|stateLedger_eq_flatMap|"
     r"busLedger_eq_channelLedger|stateLedger_eq_channelLedger|"
     r"memoryLedger_eq_channelLedger|active_stateLedger_eq|"
     r"stateLedger_perm_handoff|memoryLedger_eq|memoryLedger_perm_handoff|"
     r"stateLedger_perm_handoff_singleChain|hnonpos_of_consumersOnlyPull)\b"),
    ("SP1Clean/Soundness/EnsembleChannels.lean",
     r"theorem\s+(channel_eq_of_kindOf_eq|interactions_channel_eq_of_kindOf)\b"),
    # A0: the ledger decomposition a per-chip sweep peels with.
    ("SP1Clean/Model/CleanLedger.lean",
     r"theorem\s+(tablesCleanAccesses_cons|tableCleanAccesses_buildHinted|"
     r"tableCleanAccesses_filterKind)\b"),
    ("SP1Clean/Model/InteractionBus.lean",
     r"theorem\s+(multiplicitySum_append_closingAccesses|multiplicitySum_append_closing|"
     r"multiplicitySum_closingAccesses|mem_closingKeys_of_multiplicitySum_ne_zero|"
     r"multiplicitySum_closingAccesses_of_not_select|multiplicitySum_handoff|"
     r"multiplicitySum_of_perm_handoff|isConsistentBalanced_of_perm_handoff|"
     r"multiplicitySum_filterKind|chainLedger_perm_handoff|"
     r"multiplicitySum_chainLedger|active_append|active_flatMap_gatedPair|"
     r"handoff_append|multiChainLedger_perm_handoff|multiplicitySum_nonpos)\b"),
    ("SP1Clean/Proofs/Completeness/Closure.lean",
     r"theorem\s+(closingAccesses_balances|closingAccesses_not_preprocessed|"
     r"closingAccesses_state|closingAccesses_memory|"
     r"preprocessedProviderTables_eq|preprocessedProviderLedger_eq)\b"),
    # W5: the machine-level assembly and its completeness capstone. The assembly's constraint
    # theorem is the join of all 54 tables' own theorems (53 ensemble tables plus verifier), so a
    # regression anywhere in the
    # completeness layer surfaces here first.
    ("SP1Clean/Proofs/Completeness/Assembly.lean",
     r"theorem\s+(witness_constraints|tables_map_component)\b"),
    ("SP1Clean/Soundness/AIRCompleteness.lean",
     r"(?:theorem|def)\s+(supported_core_generated_trace_functionalCompleteness|"
     r"supported_core_generated_trace_complete|"
     r"sp1Ensemble_statement_of_generated_trace|"
     r"balancedOn_of_signed_perm|witness_balancedChannels|balancedOn_of_closure|"
     r"balancedOn_of_handoff|balanced_of_closure_and_handoff|"
     r"sp1Ensemble_statement_of_structural_balance)\b"),
    # The deterministic semantic-execution -> native-trace compiler and the final converse
    # capstone.  Keep the trace-map readiness lemmas separate from the stratum-10 channel join so
    # the census mirrors the architectural boundary.
    ("SP1Clean/Proofs/Completeness/NativeTraceCompiler.lean",
     r"theorem\s+(nativeBaseTraceOfCompiled_wellFormed|"
     r"nativeInitialClock_encodable)\b"),
    ("SP1Clean/Soundness/NativeCompleteness.lean",
     r"(?:theorem|def)\s+(supported_core_native_functionalCompleteness|"
     r"supported_core_native_complete|"
     r"sp1Ensemble_statement_of_supported_execution)\b"),
    # The W4 completeness layer: each chip's trace-table constraint/guarantee theorems and its
    # event-to-prover-assumptions discharge. Probed from the pilot onward so the rollout cannot
    # silently introduce a compiler-trusted or deferred step.
    ("SP1Clean/Proofs/Chips/*/Complete.lean",
     r"theorem\s+(traceTable_constraints|traceTable_guarantees|proverAssumptions_of_event)\b"),
    # The abstract walk/trail core (live — used by AIR + RankedGrounding).
    ("SP1Clean/Soundness/Walk.lean", r"theorem\s+(exists_trail)\b"),
    # The W3 generic engines: the goodness filter + self-loop cancellation (StateBump) and the
    # refresh elimination (MemoryBump). Keystones probed like Walk's `exists_trail`.
    ("SP1Clean/Soundness/GoodnessFilter.lean",
     r"theorem\s+(endpointBalanced_of_cancel_loops|good_of_endpointBalanced)\b"),
    ("SP1Clean/Soundness/RefreshElimination.lean", r"theorem\s+(eliminate)\b"),
    # The field⇒ℤ balance bridge (relocated in W11 Phase 5).
    ("SP1Clean/Model/BalanceBridge.lean",
     r"theorem\s+(isConsistentBalanced_of_intCast_zero|intCast_multiplicitySum_map_toAccess|"
     r"intCast_multiplicitySum_map_toAccess_eq_balanceOf|"
     r"isConsistentBalanced_of_balancedInteractions|"
     r"balancedInteractions_of_isConsistentBalanced)\b"),
    ("SP1Clean/Model/InteractionProjection.lean",
     r"lemma\s+(signedVal_natCast_of_twice_le)\b"),
    ("SP1Clean/Model/InteractionProjection.lean",
     r"theorem\s+(toAccess_pulledIfValue|toAccess_pushedIfValue)\b"),
    ("SP1Clean/Soundness/SP1Ensemble.lean",
     r"(?:theorem|def)\s+((?:sp1|balanced)\w*\??)(?=\s|\()"),
    ("SP1Clean/Soundness/GroundingInternal.lean",
     r"theorem\s+(statePullAlign8_of_stateWalk|"
     r"supportedCore_groundingObligations_of_constraints|"
     r"supportedCore_orderedRows_dynamic_of_obligations|"
     r"supportedCore_orderedRows_dynamic|supported_core_witness_grounding)\b"),
    ("SP1Clean/Soundness/AIR.lean",
     r"theorem\s+(supported_core_native_grounding|supported_core_native_sound|"
     r"supported_core_native_sound_scheduled|"
     r"supported_core_native_shard_execution|supported_core_native_shard_execution_halted|"
     r"supported_core_native_shard_sound)\b"),
    # The halt-table wave: the Exit hand-off's forcing theorems, the per-chip fetch discriminant
    # that re-bases Program truth on the committed fragment, and the halted-shard Sail conclusion.
    ("SP1Clean/Soundness/ExitAccounting.lean",
     r"theorem\s+(witness_exitMessages_eq|witness_exit_code_zero_of_haltFree|"
     r"witness_realHaltRows_eq_of_mem|witness_haltTable_table_eq_of_mem)\b"),
    ("SP1Clean/Soundness/FetchDiscriminant.lean",
     r"theorem\s+(supportedChip_fetchDiscriminantShape|"
     r"witness_realDecodedInstructionRows_opcodeNeEcall)\b"),
    ("SP1Clean/Soundness/HaltExecution.lean",
     r"theorem\s+(haltedSail_of_haltGrounding|haltedExecution_of_haltGrounding)\b"),
    # The first whole-execution claim: one shard that both boots and halts.
    ("SP1Clean/Soundness/BootHalt.lean",
     r"theorem\s+(supported_core_boot_to_halt_single_shard)\b"),
    # Exact v6.4.0 table/profile guards and the public ArkLib-facing Core AIR capstone.  These are
    # release headlines: adding a new capstone file must not silently leave it outside the census.
    ("SP1Clean/FormalModel/CoreProfile.lean",
     r"theorem\s+(checkedIn_semanticRevision|coreCluster_matchesExtracted|"
     r"coreClusterShapes_matchExtracted|memoryBoundaryCluster_matchesExtracted|"
     r"memoryBoundaryClusterShapes_matchExtracted|publicValuesWidth_matchesExtracted)\b"),
    # The opcode-alphabet cross-check: the hand-maintained `Model/Opcode.lean` mirror against the
    # extracted `Opcode` enum discriminant table (trust-gap F8 closure).
    ("SP1Clean/FormalModel/OpcodeTable.lean",
     r"theorem\s+(opcodeTable_matchesExtracted)\b"),
    ("SP1Clean/Faithful/CoreAIR.lean", r"theorem\s+(system_isCurrent)\b"),
    ("SP1Clean/Soundness/CoreAIR.lean",
     r"(?:theorem|def)\s+(sp1_air_refinement_of_obligations|sp1_air_sound_of_obligations)\b"),
    # The base execution relation deliberately excludes COMMIT-row existence. Probe the persistence,
    # terminal-digest, and optional program-contract theorems separately so a future output theorem
    # cannot hide an admission behind wrapper or verifying-key terminology.
    ("SP1Clean/FormalModel/Contracts/PublicValues.lean",
     r"theorem\s+(SP1PublicValues\.committedDigest_eq_last_of_flag)\b"),
    ("SP1Clean/FormalModel/Execution.lean",
     r"theorem\s+(finalCommitRowsMatch_of_layout|finalCommitRowsMatch_of_execution|"
     r"completeCommitDigestMatches_of_coveredExecution|commitCovered_of_standardWrapper|"
     r"commitCovered_of_commitCoveringVerifyingKey)\b"),
    ("SP1Clean/Soundness/TimedGrounding.lean", r"theorem\s+(walk)\b"),
    ("SP1Clean/Soundness/FinishedChannels.lean", r"theorem\s+(sp1_finishedChannel_guarantees)\b"),
    ("SP1Clean/Soundness/ChipRegistry.lean", r"(?:theorem|def)\s+(allChipKinds\w*)\b"),
    ("SP1Clean/Soundness/Coverage.lean",
     r"theorem\s+(coverage_kinds_eq_registry|coverage_length|covered_iff_routed|"
     r"wired_subset_reachable|reachable_subset_wired)\b"),
    ("SP1Clean/Soundness/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|sailConfigured_nonempty)\b"),
    # C1/Move-2: the decode projection, guards, ∃I∀s `decodedInROM`, its accessor, the 16 collapsed
    # `decodes<T>` producers, and the `instrToProgramRow(_inv)_*` inversions all live here (Model layer).
    ("SP1Clean/Model/Semantics/Decode.lean",
     r"(?:theorem|def)\s+(decodedInROM[\w.]*|decodes[A-Z]\w*|instrToProgramRow\w*|"
     r"mulOpCanonical|loadWidthOK|storeWidthOK|mulOp_canonical_inj|"
     r"loadOpcode_\w+|storeOpcode_\w+)\b"),
    ("SP1Clean/Model/SailDecode.lean",
     r"theorem\s+(run_bind_ok_\w+|decode_\w+)\b"),
    ("SP1Clean/FormalModel/Trace/Witness.lean",
     r"(?:theorem|lemma)\s+(isInitialState_nonvacuous)\b"),
    ("SP1Clean/Model/Machine/ConfiguredState.lean",
     r"(?:theorem|lemma)\s+(cfgState_[\w?]+|mem_fullRegs)\b"),
]

NS_RE = re.compile(r"^namespace\s+([\w.]+)")
END_RE = re.compile(r"^end\b\s*([\w.]+)?")
SECTION_RE = re.compile(r"^section\b\s*([\w.]+)?")


def fqns_in(path: Path, decl_re: re.Pattern) -> list[str]:
    stack: list[tuple[str, str]] = []  # (kind, name) — kind ∈ {ns, sec}
    out = []
    comment_depth = 0
    for line in path.read_text().splitlines():
        if comment_depth > 0:
            comment_depth += line.count("/-") - line.count("-/")
            continue
        opens = line.count("/-") - line.count("-/")
        if opens > 0:
            comment_depth = opens
            continue
        if m := NS_RE.match(line):
            for part in m.group(1).split("."):
                stack.append(("ns", part))
        elif m := SECTION_RE.match(line):
            stack.append(("sec", m.group(1) or ""))
        elif m := END_RE.match(line):
            parts = (m.group(1) or "").split(".") if m.group(1) else [""]
            for part in reversed(parts):
                if stack and (stack[-1][1] == part or (stack[-1][0] == "sec" and not part)):
                    stack.pop()
        elif m := decl_re.search(line):
            stripped = line.lstrip()
            if not stripped.startswith("--") and not stripped.startswith("private "):
                ns = ".".join(p for k, p in stack if k == "ns")
                out.append(f"{ns}.{m.group(1)}" if ns else m.group(1))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="check committed probes without writing")
    mode.add_argument(
        "--allow-removals", action="store_true",
        help="regenerate after an intentional removal or rename; review the probe diff",
    )
    args = parser.parse_args()
    main_fqns: list[str] = []
    test_fqns: list[str] = []
    test_imports: list[str] = []  # `SP1CleanTest.*` modules, imported explicitly in the test probe
    seen_imports: set[str] = set()
    missing_targets: list[tuple[str, str]] = []
    for glob, pattern in TARGETS:
        decl_re = re.compile(pattern)
        target_count = 0
        for path in sorted(ROOT.glob(glob)):
            found = fqns_in(path, decl_re)
            if not found:
                continue
            target_count += len(found)
            # `import SP1Clean` (the umbrella) covers every main-library declaration, but NOT the
            # `SP1CleanTest` conformance anchors (that test library is not imported by the umbrella —
            # it is the native_decide quarantine). Those go to the separate test probe, importing
            # each module explicitly so its FQNs resolve there.
            rel = path.relative_to(ROOT)
            if rel.parts[0] == "SP1CleanTest":
                test_fqns.extend(found)
                mod = ".".join(rel.with_suffix("").parts)
                if mod not in seen_imports:
                    seen_imports.add(mod)
                    test_imports.append(mod)
            else:
                main_fqns.extend(found)
        if target_count == 0:
            missing_targets.append((glob, pattern))

    if missing_targets:
        print("FAIL: axiom-census target(s) matched no declarations:")
        for glob, pattern in missing_targets:
            print(f"  {glob}: {pattern}")
        raise SystemExit(1)

    def dedupe(fqns: list[str]) -> list[str]:
        seen, ordered = set(), []
        for f in fqns:
            if f not in seen:
                seen.add(f)
                ordered.append(f)
        return ordered

    main_ordered = dedupe(main_fqns)
    lines = ["import SP1Clean",
             "",
             "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
             "Main-library census probe (elaborates against the `SP1Clean` oleans only).",
             "Run via `lake env lean scripts/axiom_probe.lean` (see `scripts/run_audit.sh`). -/",
             ""]
    lines += [f"#print axioms {f}" for f in main_ordered]
    main_text = "\n".join(lines) + "\n"

    test_ordered = dedupe(test_fqns)
    lines = [f"import {m}" for m in test_imports]
    lines += ["",
              "/-! Auto-generated by `scripts/gen_axiom_probe.py` — do not edit by hand.",
              "Test-library census probe (the `SP1CleanTest` conformance anchors; requires the",
              "test-library oleans — run `lake test` first).",
              "Run via `lake env lean scripts/axiom_probe_test.lean` (see `scripts/run_audit.sh`). -/",
              ""]
    lines += [f"#print axioms {f}" for f in test_ordered]
    test_text = "\n".join(lines) + "\n"

    outputs = [(OUT_MAIN, main_text, main_ordered), (OUT_TEST, test_text, test_ordered)]
    failures = []
    for path, generated, names in outputs:
        recorded = path.read_text() if path.exists() else ""
        previous_names = set(re.findall(r"^#print axioms (\S+)$", recorded, re.M))
        removed = sorted(previous_names - set(names))
        if removed and not args.allow_removals:
            failures.append(
                f"{path.relative_to(ROOT)} lost recorded axiom probes:\n  " + "\n  ".join(removed)
            )
        if args.check and (not path.exists() or recorded != generated):
            failures.append(f"{path.relative_to(ROOT)} differs from the source inventory")

    # Validate both libraries before writing either: a test-scope failure must not modify the
    # main probe and make a subsequent audit appear to start from a different inventory.
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        print("Restore missing targets, or regenerate an intentional change and review the probe diff.")
        print("Intentional removals require: python3 scripts/gen_axiom_probe.py --allow-removals")
        raise SystemExit(1)

    if args.check:
        print(f"PASS: axiom probes match source inventory ({len(main_ordered)} main, "
              f"{len(test_ordered)} test)")
    else:
        for path, generated, names in outputs:
            path.write_text(generated)
            print(f"wrote {path.relative_to(ROOT)} with {len(names)} probes")


if __name__ == "__main__":
    main()
