#!/usr/bin/env python3
"""Check compiled capstone target types and their definition-dependency manifest.

Default builds the target first. --no-build is for the release harness after its full build.
--update explicitly refreshes the manifest after reviewing the semantic/type delta; it never
changes Lean source or the allowed axioms. A fresh output file is required even on exit zero
because the Lean frontend can return zero after a stack overflow.
"""

import argparse
import difflib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT = ROOT / "docs/snapshots/capstone-contract.json"
EXPECTED_ROOTS = {
    "SP1Clean.Soundness.Shard." + name
    for name in ("statement_iff", "SoundnessTarget", "CompilerTarget", "SailTrace", "Endpoint", "sail_trace")
} | {"SP1Clean.FormalModel.Shard." + name
     for name in ("Executes", "nativeProfile", "AdmissibleExecution", "ReleaseAdmissibleExecution",
                  "ReleaseStatementExecution", "sp1Machine")} | {
    "SP1Clean.FormalModel.StockPublicOutput.acceptsCore",
    "SP1Clean.FormalModel.StockPublicOutput.commitment_projection",
    "SP1Clean.Export.InstalledAssembly.proverStatement_iff",
    "SP1Clean.Export.InstalledAssembly.statement_iff_fixedCursor",
    "SP1Clean.Export.InstalledAssembly.trace_of_statement",
    "SP1Clean.Export.InstalledAssembly.execution_of_statement",
    "SP1Clean.Export.InstalledAssembly.header_of_statement",
    "SP1Clean.Export.InstalledAssembly.native_short_soundnessTarget",
    "SP1Clean.Export.InstalledAssembly.native_resources_of_statement",
    "SP1Clean.Export.InstalledAssembly.release_statement_iff_of_statement",
    "SP1Clean.Export.InstalledAssembly.native_release_statement_iff_peak",
    "SP1Clean.Export.InstalledAssembly.native_release_of_short_statement",
    "SP1Clean.Export.InstalledAssembly.native_release_of_short_halt",
    "SP1Clean.Export.InstalledAssembly.AcceptedChain.short_release",
    "SP1Clean.Export.InstalledAssembly.soundness",
    "SP1Clean.Export.InstalledAssembly.AcceptedChain.soundness",
    "SP1Clean.Export.InstalledAssembly.AcceptedChain.boot_to_halt",
    "SP1Clean.TraceGen.statementExecution_headerChecks",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_base_fits",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_capacity",
    "SP1Clean.Export.InstalledAssembly.interactionsFit_grow_iff",
    "SP1Clean.HostCallChip.main_host_interactions",
    "SP1Clean.HostCallChip.main_other_interactions",
    "SP1Clean.Soundness.HostLocalCore.memoryInterior_eq",
    "SP1Clean.TraceGen.WriteObservations.read?_eq_some_iff",
    "SP1Clean.TraceGen.WriteObservations.of_admissibleExecution",
    "SP1Clean.TraceGen.WriteObservations.packets_at",
    "SP1Clean.Export.WriteObservationAssembly.statement_iff",
    "SP1Clean.Export.WriteObservationAssembly.table_count",
    "SP1Clean.Export.WriteObservationAssembly.queue_slots",
    "SP1Clean.Semantics.HintQueue.node?_prepend_at",
    "SP1Clean.Export.WriteObservationAssembly.allocation_slots",
    "SP1Clean.Export.WriteObservationAssembly.allocation_word_slots",
    "SP1Clean.WriteAllocation.open_ledger",
    "SP1Clean.WriteAllocation.step_ledger",
    "SP1Clean.WriteAllocation.Batch.openRow_valid",
    "SP1Clean.WriteAllocation.Batch.steps_at",
    "SP1Clean.WriteAllocation.native_allocation_ticket_at",
    "SP1Clean.WriteAllocation.native_store_at",
    "SP1Clean.WriteAllocation.Batch.publishes_prepend",
    "SP1Clean.WriteAllocation.Words.populate_word",
    "SP1Clean.WriteAllocation.Words.walk_words",
    "SP1Clean.WriteAllocation.Words.populate_hook_available",
    "SP1Clean.WriteAllocation.Words.populate_direct_group",
    "SP1Clean.WriteAllocation.Words.walk_table_valid",
    "SP1Clean.WriteAllocation.Words.word_supply",
    "SP1Clean.WriteAllocation.Words.guarded_word_valid",
    "SP1Clean.WriteEffects.Witness.native_collect",
    "SP1Clean.WriteEffects.Witness.native_position",
    "SP1Clean.WriteEffects.Witness.native_inputs",
    "SP1Clean.WriteEffects.StreamCounts.advance_correct",
    "SP1Clean.WriteEffects.Witness.native_node_count",
    "SP1Clean.WriteEffects.Witness.native_word_capacity",
    "SP1Clean.WriteEffects.Witness.native_allocation_assembly",
    "SP1Clean.WriteEffects.Witness.allocation_occurrences",
    "SP1Clean.WriteEffects.Witness.native_private_matches",
    "SP1Clean.Export.WriteObservationAssembly.native_installed_allocation_matches",
    "SP1Clean.Export.WriteObservationAssembly.assembled_hint_read_origins",
    "SP1Clean.Export.WriteObservationAssembly.assembled_hint_word_data",
    "SP1Clean.Export.WriteObservationAssembly.outgoing_queue_read_origins",
    "SP1Clean.Export.WriteObservationAssembly.outgoing_queue_of_allocations",
    "SP1Clean.WriteEffects.Witness.native_block_tables",
    "SP1Clean.Export.WriteObservationAssembly.withCursors_ledger",
    "SP1Clean.Export.WriteObservationAssembly.effect_lookupFree",
    "SP1Clean.WriteEffects.groups_of_admissibleExecution",
    "SP1Clean.WriteEffects.placement_occurrences",
    "SP1Clean.WriteEffects.admissible_placement_heights",
    "SP1Clean.WriteEffects.admissible_fixed_heights",
    "SP1Clean.WriteEffects.Group.populate_valid",
    "SP1Clean.WriteEffects.Group.populate_match_iff",
    "SP1Clean.WriteEffects.block_authenticates",
    "SP1Clean.WriteEffects.metadata_available",
    "SP1Clean.WriteEffects.group_ledger",
    "SP1Clean.Export.WriteObservationAssembly.statement_iff_of_execution",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_stream_height",
    "SP1Clean.Export.InstalledAssembly.admissible_hint_snapshot_tables",
    "SP1Clean.Export.InstalledAssembly.hint_snapshot_occurrences",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_hint_snapshot_height",
    "SP1Clean.HostHintSnapshot.tableFor_closed",
    "SP1Clean.HostHintSnapshot.Seal.tableFor_ledger",
    "SP1Clean.Export.WriteObservationAssembly.assembled_read_origin",
    "SP1Clean.Export.WriteObservationAssembly.assembled_hint_word_bytes",
    "SP1Clean.Export.WriteObservationAssembly.counted_packet_tables",
    "SP1Clean.Export.WriteSourceRegistry.physical_cut_values",
    "SP1Clean.Export.WriteObservationAssembly.native_hint_walk",
    "SP1Clean.Export.WriteObservationAssembly.outgoing_queue_of_immutable_reads",
    "SP1Clean.WriteEffects.native_destination_groups",
    "SP1Clean.Export.WriteSourceRegistry.routable_physical_cuts",
    "SP1Clean.Export.WriteBoundaryBuild.build_sparse_covers",
    "SP1Clean.Export.WriteBoundaryBuild.compiled_sparse_read",
    "SP1Clean.Export.WriteBoundaryBuild.sources_of_admissibleExecution",
    "SP1Clean.TraceGen.MixedMemoryHistory.record_chronology",
    "SP1Clean.TraceGen.MixedMemoryHistory.heldAt_cut",
    "SP1Clean.Export.WriteBoundaryBuild.readDemand_heldAt",
    "SP1Clean.Export.WriteBoundaryBuild.compiled_read_source",
    "SP1Clean.Export.WriteSourceRegistry.generated_ordinary",
    "SP1Clean.Export.WriteSourceRegistry.classify_predecessor",
    "SP1Clean.Export.WriteMixedSourceTables.heights",
    "SP1Clean.Export.WriteMixedSourceTables.valid",
    "SP1Clean.Export.WriteMixedSourceTables.ofExecution_constraints",
    "SP1Clean.Export.WriteMixedSourceTables.read_funded",
    "SP1Clean.Export.WriteMixedSourceTables.route_exists",
    "SP1Clean.Export.WriteMixedSourceTables.compiledSource_valid",
    "SP1Clean.Export.WriteMixedSourceTables.compiled_records",
    "SP1Clean.Export.WriteMixedSourceTables.compiled_supply_fit",
    "SP1Clean.Export.WriteMixedSourceTables.compiled_funded",
    "SP1Clean.Export.WriteMixedSourceTables.compiled_route_exists",
    "SP1Clean.Export.WriteMixedHostTables.remaining_count",
    "SP1Clean.Export.WriteMixedHostTables.installed_at",
    "SP1Clean.Export.WriteMixedHostTables.bank_state_balanced",
    "SP1Clean.Export.WriteMixedHostTables.installed_bank_balances",
    "SP1Clean.Export.WriteObservationAssembly.compiled_read_constraints",
    "SP1Clean.Export.WriteObservationAssembly.compiled_read_balances",
    "SP1Clean.TraceGen.admissibleExecution_untouched",
    "SP1Clean.TraceGen.ordinary_plan_values",
    "SP1Clean.TraceGen.MixedMemoryHistory.canonical",
    "SP1Clean.TraceGen.MixedMemoryHistory.hint_tables_memory",
    "SP1Clean.TraceGen.MixedMemoryHistory.heldAt_of_posts",
    "SP1Clean.WriteEffects.native_dispatch_at",
    "SP1Clean.WriteEffects.native_dispatch_table",
    "SP1Clean.WriteEffects.native_dispatch_replay",
    "SP1Clean.TraceGen.MixedMemoryHistory.posts_of_priors",
    "SP1Clean.TraceGen.MixedMemoryHistory.syscall_pulls",
    "SP1Clean.TraceGen.MixedMemoryHistory.syscall_posts",
    "SP1Clean.TraceGen.admissibleExecution_hintSnapshot",
    "SP1Clean.TraceGen.admissibleExecution_writePacket",
    "SP1Clean.WriteBuffer.tables_cursor_closed",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_write_probe_bound",
    "SP1Clean.TraceGen.releaseAdmissibleExecution_instructionBuckets",
    "SP1Clean.TraceGen.releaseAdmissibleExecution_instructionTables",
    "SP1Clean.TraceGen.InstalledInstructionTables.generation_padding",
    "SP1Clean.TraceGen.InstalledInstructionTables.table_receipts",
    "SP1Clean.TraceGen.InstalledInstructionTables.receipt_weights",
    "SP1Clean.TraceGen.WriteObservations.installed_cuts",
    "SP1Clean.Soundness.WriteObservationHistory.versionIntervals_effects",
    "SP1Clean.TraceGen.WriteObservations.installed_versions",
    "SP1Clean.TraceGen.WriteObservations.checkPacket_iff_versions",
    "SP1Clean.TraceGen.MemoryHistoryAccess.matchingValues_of_balance",
    "SP1Clean.TraceGen.MemoryLocationHistory.heldAt_interval",
    "SP1Clean.TraceGen.MemoryLocationHistory.heldAt_final",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_ordinary_capacity",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_ordinary_base_fits",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_compiled_ordinary_fits",
    "SP1Clean.Export.InstalledAssembly.observation_constructed_heights",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_observation_base_fits",
    "SP1Clean.TraceGen.admissibleExecution_syscallPushedState",
    "SP1Clean.TraceGen.admissibleExecution_ordinaryPushedState",
    "SP1Clean.TraceGen.MixedBumpInput.stateBump?_eq_none_iff",
    "SP1Clean.TraceGen.routeBumpInputs?_at",
    "SP1Clean.TraceGen.admissibleExecution_routeMixedRows",
    "SP1Clean.TraceGen.routeMixedRows?_at",
    "SP1Clean.TraceGen.admissibleExecution_syscallInstruction",
    "SP1Clean.TraceGen.admissibleExecution_syscallInputs",
    "SP1Clean.TraceGen.syscallInstruction_stateMessages",
    "SP1Clean.TraceGen.admissibleExecution_mixedBumpInventory",
    "SP1Clean.Export.InstalledAssembly.bump_constructed_tables",
    "SP1Clean.Export.InstalledAssembly.ExecutionFacts.prefix_boundary_growth",
    "SP1Clean.Export.InstalledAssembly.fixedProvider_native_soundnessTarget",
    "SP1Clean.Export.InstalledAssembly.native_soundnessTarget_of_boundary_budget",
    "SP1Clean.Export.InstalledAssembly.fixedProviderPreset_bump_base_fits",
    "SP1CleanTest.MixedStateBumpEdges.low_pc_carry_at_full_upper_limbs",
    "SP1CleanTest.MixedStateBumpEdges.clock_carry_into_last_window",
    "SP1CleanTest.MixedStateBumpEdges.pc_carry_into_last_top_limb",
    "SP1CleanTest.MixedStateBumpEdges.clock_carry_past_last_window",
    "SP1CleanTest.MixedStateBumpEdges.pc_carry_past_last_top_limb",
    "SP1Clean.FormalModel.Shard.Executes.header_halt",
    "SP1Clean.TraceGen.HintReadTransfers.of_admissibleExecution",
    "SP1Clean.TraceGen.HintReadTransfers.tables_cursor_closed",
    "SP1Clean.TraceGen.admissibleExecution_compile_from_prefix",
    "SP1Clean.TraceGen.releaseAdmissibleExecution_compile_from_prefix",
    "SP1Clean.TraceGen.admissibleExecution_historicalHintCapacity",
    "SP1Clean.TraceGen.admissibleExecution_observationWitness",
    "SP1Clean.TraceGen.admissibleExecution_observationData",
    "SP1Clean.TraceGen.admissibleExecution_observationFits",
    "SP1Clean.TraceGen.admissibleExecution_hintInventory",
    "SP1Clean.HostControl.noop_spec_of_run",
    "SP1Clean.HostNoopChip.run_of_spec",
    "SP1Clean.HostControl.choice_spec_of_run",
    "SP1Clean.Soundness.HostRegisteredCalls.noopTable_component",
    "SP1Clean.Soundness.HostRegisteredCalls.receipt_heights",
    "SP1Clean.Soundness.HostRegisteredCalls.classified",
    "SP1Clean.Semantics.HostReceiptProfile.installed_code_iff",
    "SP1Clean.Export.InstalledAssembly.enter_verify_slot",
    "SP1Clean.TraceGen.routed_successor_at",
    "SP1Clean.FormalModel.Shard.Executes.dynamicMatch",
    "SP1Clean.Export.InstalledAssembly.executionFlag_iff_identity",
    "SP1Clean.Export.InstalledAssembly.target_ram_changes_of_statement",
    "SP1Clean.Semantics.ByteMemory.intervals_length_minimal",
    "SP1Clean.Semantics.ByteMemory.intervals_congr",
    "SP1Clean.Export.fixedProgram_occurrences",
    "SP1Clean.Export.fixedPermission_occurrences",
    "SP1Clean.Export.fixed_hint_occurrences",
    "SP1Clean.FormalModel.Shard.AdmissibleExecution.fixed_hint_capacity",
    "SP1Clean.Semantics.HintReadDemand.writeBytes",
    "SP1Clean.TraceGen.HintReadCapacity.table_counts",
    "SP1Clean.TraceGen.HintReadCapacity.padded_counts_le",
    "SP1Clean.FormalModel.Shard.AdmissibleExecution.fixed_image_capacity",
    "SP1CleanTest.FixedRamCapacity.empty_large_ram_provider_height",
    "SP1Clean.FormalModel.Shard.AdmissibleExecution.endpoint_ram_capacity",
    "SP1CleanTest.FixedRamCapacity.empty_release_without_raw_statement",
    "Air.Flat.Realizes",
}


def validate_manifest(data):
    roots = data.get("roots", [])
    if (data.get("version") != 1 or len(roots) != len(EXPECTED_ROOTS)
            or set(roots) != EXPECTED_ROOTS or not data.get("declarations")):
        raise ValueError("incomplete capstone contract manifest")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.no_build:
        subprocess.run(
            ["lake", "--no-cache", "build", "--wfail", "--iofail",
             "SP1Clean.Soundness.Shard.Contract", "SP1Clean.Export.ShortShardChain", "SP1Clean.Export.InstalledBoundaryGrowth",
             "SP1Clean.FormalModel.Contracts.StockPublicOutput",
             "SP1Clean.Export.WriteObservationAssembly", "SP1Clean.Proofs.Completeness.WritePlacementCapacity",
             "SP1Clean.Proofs.Completeness.WriteWindowTape",
             "SP1Clean.Export.HintSnapshotCapacity",
             "SP1Clean.Export.WriteObservationReadBuild",
             "SP1Clean.Proofs.Completeness.WriteAllocationStore",
             "SP1Clean.Proofs.Completeness.WriteAllocationWordTables",
             "SP1Clean.Proofs.Completeness.WriteWitnessAllocationCounts",
             "SP1Clean.Export.WriteInstalledAllocations",
             "SP1Clean.Proofs.Completeness.WriteNativeBlockBalance",
             "SP1Clean.Export.WriteObservationReads",
             "SP1Clean.Export.WriteObservationByte",
             "SP1Clean.Export.WritePhysicalCuts",
             "SP1Clean.Export.HintSnapshotWalk",
             "SP1Clean.Export.WriteBoundaryDemand",
             "SP1Clean.Export.WriteMixedReadFunding",
             "SP1Clean.Export.WritePhysicalRouting",
             "SP1Clean.Proofs.Completeness.WriteDestination",
             "SP1Clean.Proofs.Completeness.MixedMemoryPosts",
             "SP1Clean.Proofs.Completeness.WriteDispatchReplay",
             "SP1Clean.Proofs.Completeness.MixedMemorySyscall",
             "SP1Clean.Export.WriteStreamCapacity",
             "SP1Clean.Proofs.Completeness.HintQueueSnapshot",
             "SP1Clean.Proofs.Completeness.WritePacketHandoff",
             "SP1Clean.Proofs.Completeness.WriteBufferTables",
             "SP1Clean.Export.InstalledHintCompleteness", "SP1Clean.Soundness.HostRegisteredCalls",
             "SP1Clean.Proofs.Completeness.PublicHeader", "SP1Clean.Proofs.Completeness.MixedInstructionBuckets",
             "SP1Clean.Proofs.Completeness.MixedInstructionTables", "SP1Clean.Proofs.Completeness.WriteObservationCuts",
             "SP1Clean.Export.CompiledOrdinaryPreset", "SP1Clean.Proofs.Completeness.MixedSyscallRows",
             "SP1Clean.Proofs.Completeness.HintReadLedger",
             "SP1Clean.Proofs.Completeness.MixedAccessFrontier",
             "SP1Clean.Proofs.Completeness.HistoricalHintCapacity",
             "SP1Clean.Proofs.Completeness.HintInventory", "SP1Clean.Proofs.Chips.HostControlPopulate",
             "SP1CleanTest.Alignment.Core.FixedRamCapacity", "SP1Clean.Export.FixedImageCapacity",
             "SP1Clean.Export.InstalledBumpTables", "SP1CleanTest.Alignment.Core.MixedStateBumpEdges",
             "SP1Clean.Export.WriteProbeCapacity", "SP1Clean.Proofs.Completeness.MemoryVersionHistory",
             "SP1Clean.Export.FixedHintCapacity", "SP1Clean.Proofs.Completeness.HintReadCapacity",
             "SP1Clean.Proofs.Completeness.ObservationCapacity", "SP1Clean.Proofs.Completeness.ObservationData"],
            cwd=ROOT, check=True,
        )
    with tempfile.TemporaryDirectory(prefix="sp1-capstone-contract-") as temporary:
        output = Path(temporary) / "contract.json"
        environment = {**os.environ, "CAPSTONE_SURFACE_OUT": str(output)}
        result = subprocess.run(
            ["lake", "env", "lean", "scripts/capstoneContract.lean"],
            cwd=ROOT, env=environment, capture_output=True, text=True,
        )
        diagnostics = result.stdout + result.stderr
        if result.returncode or diagnostics.strip() or not output.is_file():
            print(diagnostics, end="")
            print("FAIL: compiled capstone contract check did not complete cleanly")
            return 1
        data = json.loads(output.read_text())
        try:
            validate_manifest(data)
        except ValueError as error:
            print(f"FAIL: {error}")
            return 1
        fresh = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if args.update:
        SNAPSHOT.write_text(fresh)
        print(f"Updated {SNAPSHOT.relative_to(ROOT)}; review all semantic/type changes")
    elif not SNAPSHOT.is_file() or SNAPSHOT.read_text() != fresh:
        old = SNAPSHOT.read_text() if SNAPSHOT.is_file() else ""
        sys.stdout.writelines(difflib.unified_diff(
            old.splitlines(keepends=True), fresh.splitlines(keepends=True),
            fromfile=str(SNAPSHOT.relative_to(ROOT)), tofile="compiled contract",
        ))
        print("FAIL: capstone contract drift; review before an explicit --update")
        return 1
    print(f"PASS: capstone target types and {len(data['declarations'])} definition dependencies")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
