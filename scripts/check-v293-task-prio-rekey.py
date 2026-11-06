#!/usr/bin/env python3
"""Local physical priority-table writes; not full API/GOOD_OS evidence."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CODE = 'certiucos/v293/code/V293OSTaskChangePrio.v'
PROOF = 'certiucos/v293/proofs/V293TaskPrioRekey.v'
PROBE = 'audit/probes/V293TaskPrioRekeyProbe.v'
SOURCES = [CODE, PROOF]
ROOT_COUNT = 6
spec = importlib.util.spec_from_file_location('cache_local_check', ROOT / 'scripts/check-v293-storage-prefix.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


def checked_assumptions(output, root_count=ROOT_COUNT):
    if output.count('Axioms:') + output.count('Closed under the global context') != root_count:
        raise ValueError(f'{root_count} actual root assumption prints required')
    return CHECK.TRUST.check_assumptions(
        output.replace('Closed under the global context', ''), CHECK.TRUST.ALLOWED)


def mutations(proof, bitmap=False, physical=False, tcb=False, guard=False, prefix=False, event=False, event_body=False, event_prefix=False, tcb_update=False, null_update=False, nonnull_frame=False, coordinates=False, generic_update=False, entry=False, reserved=False, entry_update=False, entry_null=False):
    def header(declaration, old, new):
        start = proof.index(declaration)
        end = proof.index('Proof.', start)
        return proof[:start] + CHECK.replace_once(proof[start:end], old, new) + proof[end:]
    if entry_null:
        execution = 'Theorem V293_task_prio_entry_null_update_execution :'
        return {
            'entry-null-pointer-write-permission-omitted-only': (header(execution,
                'V293_bytes_writable M bc 0%Z 4 ->', 'True ->'), execution),
            'entry-null-internal-event-load-omitted-only': (header(execution,
                'load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->', 'True ->'), execution),
            'entry-null-program-claimed-suffix-only': (header(execution,
                'V293_task_prio_entry_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi\n    current reserved cpu_sr exit_id',
                'V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi'), execution),
            'entry-null-final-event-claimed-tcb-pointer-only': (header(execution,
                'load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull',
                'load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (bt,Int.repr base))'), execution),
        }
    if entry_update:
        execution = 'Theorem V293_task_prio_entry_update_execution :'
        return {
            'entry-update-pointer-write-permission-omitted-only': (header(execution,
                'V293_bytes_writable M bc 0%Z 4 ->', 'True ->'), execution),
            'entry-update-resource-separation-omitted-only': (header(execution,
                '(forall c, In c [b;bn;bt;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx] ->\n    c <> bo /\\ c <> bc) ->',
                'True ->'), execution),
            'entry-update-program-claimed-suffix-only': (header(execution,
                'V293_task_prio_entry_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi\n    current reserved cpu_sr exit_id',
                'V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi'), execution),
            'entry-update-final-old-slot-claimed-pointer-only': (header(execution,
                'load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some Vnull',
                'load (Tptr V293_tcb_type) Mh (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base))'), execution),
        }
    if reserved:
        execution = 'Theorem V293_task_prio_entry_reserved_execution :'
        return {
            'reserved-global-binding-omitted-only': (header(execution,
                'get ge reserved = Some (br,Tint8) ->', 'True ->'), execution),
            'reserved-noncollision-omitted-only': (header(execution,
                'next <> (br,Int.zero) ->', 'True ->'), execution),
            'reserved-program-claimed-skip-only': (header(execution,
                'V293_task_prio_entry_reserved table oldprio newprio ptcb current reserved cpu_sr exit_id',
                'sskip None'), execution),
            'reserved-final-pointer-claimed-null-only': (header(execution,
                'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)',
                'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some Vnull'), execution),
        }
    if entry:
        execution = 'Theorem V293_task_prio_entry_lookup_execution :'
        return {
            'entry-pointer-write-permission-omitted-only': (header(execution,
                'V293_bytes_writable M bc 0%Z 4 ->', 'True ->'), execution),
            'entry-old-slot-read-omitted-only': (header(execution,
                'load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr next) ->',
                'True ->'), execution),
            'entry-program-claimed-skip-only': (header(execution,
                'V293_task_prio_entry_lookup table oldprio newprio ptcb current cpu_sr exit_id',
                'sskip None'), execution),
            'entry-final-pointer-claimed-null-only': (header(execution,
                'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)',
                'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some Vnull'), execution),
        }
    if generic_update:
        execution = 'Theorem V293_task_prio_coordinates_update_execution :'
        return {
            'generic-coordinate-write-permission-omitted-only': (header(execution,
                '(forall c, c=ny \/ c=bi \/ c=nby \/ c=nbx ->\n'
                '    exists v, get M (c,0%Z) = Some (true,v)) ->', 'True ->'), execution),
            'generic-coordinate-resource-isolation-omitted-only': (header(execution,
                '(forall c, c=ny \\/ c=bi \\/ c=nby \\/ c=nbx ->\n    c <> b /\\ c <> bo /\\ c <> bn /\\ c <> bc /\\ c <> bt /\\\n    c <> dy /\\ c <> dby /\\ c <> dx /\\ c <> br /\\ c <> bg /\\ c <> bp /\\ c <> be) ->', 'True ->'), execution),
            'generic-coordinate-program-claimed-suffix-only': (header(execution,
                'V293_task_prio_coordinates_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi',
                'V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi'), execution),
            'generic-coordinate-internal-event-claimed-null-only': (header(execution,
                'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase))',
                'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull'), execution),
        }
    if coordinates:
        execution = 'Theorem V293_task_prio_coordinates_execution :'
        return {
            'coordinate-write-permission-omitted-only': (header(execution,
                '(forall b, b=dy \/ b=di \/ b=dby \/ b=dbx -> exists v, get M (b,0%Z) = Some (true,v)) ->', 'True ->'), execution),
            'coordinate-source-isolation-omitted-only': (header(execution,
                '(forall b, b=dy \/ b=di \/ b=dby \/ b=dbx -> b <> bn) ->', 'True ->'), execution),
            'coordinate-program-claimed-skip-only': (header(execution,
                'V293_task_prio_coordinates newprio yn xi byn xn', 'sskip None'), execution),
            'coordinate-index-claimed-mask-only': (header(execution,
                "load Tint8 M' (di,0%Z) = Some (V293_byteval (V293_prio_bit p))",
                "load Tint8 M' (di,0%Z) = Some (V293_byteval (2 ^ V293_prio_bit p))"), execution),
        }
    if nonnull_frame:
        execution = 'Theorem V293_task_prio_prefix_event_update_preserves :'
        return {
            'nonnull-tcb-event-isolation-omitted-only': (header(execution,
                'bt <> bp -> bt <> be ->', 'bt <> bp -> True ->'), execution),
            'nonnull-internal-event-claimed-null-only': (header(execution,
                'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase))',
                'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull'), execution),
            'nonnull-frame-claims-prio-untouched-only': (header(execution,
                '(i < base+50)%Z \/ (base+54 < i)%Z', '(i < base+51)%Z \/ (base+54 < i)%Z'), execution),
            'nonnull-program-claimed-five-only': (header(execution,
                'V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi',
                'V293_task_prio_tcb_update ptcb newprio yn xi byn xn'), execution),
        }
    if null_update:
        execution = 'Theorem V293_task_prio_prefix_null_update_execution :'
        return {
            'null-entry-event-read-omitted-only': (header(execution,
                'load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->', 'True ->'), execution),
            'null-pointer-tcb-isolation-omitted-only': (header(execution,
                'bc <> bt -> bc <> bp -> bt <> bp ->', 'True -> bc <> bp -> bt <> bp ->'), execution),
            'null-continuous-program-claimed-five-only': (header(execution,
                'V293_task_prio_prefix_event_update table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent xi',
                'V293_task_prio_tcb_update ptcb newprio yn xi byn xn'), execution),
            'null-final-event-local-claimed-nonnull-only': (header(execution,
                'load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull',
                'load (Tptr V293_event_type) Mh (bp,0%Z) = Some (Vptr (bt,Int.repr base))'), execution),
        }
    if tcb_update:
        execution = 'Theorem V293_task_prio_tcb_update_execution :'
        operands = 'V293_rekey_locals ge le M bt bt (V293_tcb_update_bindings newprio yn xi byn xn new) ->'
        no_isolation = ('(forall x value, In (x,value) (V293_tcb_update_bindings newprio yn xi byn xn new) -> '
                        'exists c, get le x = Some (c,Tint8) /\\ load Tint8 M (c,0%Z) = Some value) ->')
        return {
            'five-field-write-permission-omitted-only': (header(execution,
                'V293_tcb_update_writable M bt base ->', 'True ->'), execution),
            'five-operand-tcb-isolation-omitted-only': (header(execution, operands, no_isolation), execution),
            'five-field-program-claimed-skip-only': (header(execution,
                'V293_task_prio_tcb_update ptcb newprio yn xi byn xn', 'sskip None'), execution),
            'five-final-index-claimed-mask-only': (header(execution,
                "V293_tcb_updated_loads M' bt base new /\\",
                "(V293_tcb_updated_loads M' bt base new /\\ load Tint8 M' (bt,(base+51)%Z) = "
                "Some (V293_byteval (2 ^ V293_prio_bit new))) /\\"), execution),
        }
    if event_prefix:
        execution = 'Theorem V293_task_prio_prefix_event_nonnull_execution :'
        return {
            'continuous-event-write-permission-omitted-only': (header(execution,
                'V293_event_bitmap_writable M be ebase ->', 'True ->'), execution),
            'continuous-event-ready-separation-omitted-only': (header(execution,
                'be <> br -> be <> bg ->', 'True -> be <> bg ->'), execution),
            'continuous-prefix-claimed-event-suffix-only': (header(execution,
                'V293_task_prio_prefix_event table oldprio newprio ptcb rows group yo yn xo xn byo byn pevent',
                'V293_task_prio_event ptcb pevent yo yn xo xn byo byn'), execution),
            'continuous-final-old-slot-claimed-pointer-only': (header(execution,
                'load (Tptr V293_tcb_type) Mg (b,(4*Z.of_nat old)%Z) = Some Vnull',
                'load (Tptr V293_tcb_type) Mg (b,(4*Z.of_nat old)%Z) = Some (Vptr (bt,Int.repr base))'), execution),
        }
    if event_body:
        body = 'Theorem V293_task_prio_event_then_execution :'
        row = 'Lemma V293_event_row_eval :'
        controls = 'Theorem V293_event_nonnull_physical_controls :'
        return {
            'event-body-write-permission-omitted-only': (header(body,
                'V293_event_bitmap_writable M be base ->', 'True ->'), body),
            'event-row-address-claimed-10-only': (header(row,
                'Some (Vptr (be,Int.repr (base+11+Z.of_nat y)))',
                'Some (Vptr (be,Int.repr (base+10+Z.of_nat y)))'), row),
            'event-body-claimed-skip-only': (header(body,
                'V293_task_prio_event_then pevent yo yn xo xn byo byn', 'sskip None'), body),
            'event-cross-row-old-bit-claimed-set-only': (header(controls,
                'V293_event_nonnull_observes 0 1 8 6 64 0 1',
                'V293_event_nonnull_observes 0 1 8 6 64 1 1'), controls),
        }
    if event:
        assignment = 'Theorem V293_task_prio_event_read_execution :'
        layout = 'Theorem V293_event_source_layout :'
        test = 'Theorem V293_event_test_eval :'
        controls = 'Theorem V293_prefix_event_controls :'
        return {
            'event-destination-permission-omitted-only': (header(assignment,
                'V293_bytes_writable M be 0%Z 4 ->', 'True ->'), assignment),
            'event-field-offset-claimed-24-only': (header(layout,
                'field_offset 9%Z V293_tcb_fields = Some (Int.repr 28)',
                'field_offset 9%Z V293_tcb_fields = Some (Int.repr 24)'), layout),
            'event-nonnull-test-inverted-only': (header(test,
                'Vnull => false | _ => true', 'Vnull => true | _ => false'), test),
            'event-null-exit-claimed-nonnull-only': (header(controls,
                'V293_prefix_event_observes false 16 Vnull',
                'V293_prefix_event_observes false 16 (Vptr (72%positive,Int.repr 5))'), controls),
        }
    if prefix:
        execution = 'Theorem V293_task_prio_prefix_execution :'
        controls = 'Theorem V293_prefix_physical_controls :'
        return {
            'table-tcb-separation-omitted-only': (header(execution,
                'b <> bo -> b <> bn -> b <> bc -> b <> bt ->',
                'b <> bo -> b <> bn -> b <> bc -> True ->'), execution),
            'new-local-table-separation-omitted-only': (header(execution,
                '-> c <> b /\\ c <> dy /\\ c <> dby /\\ c <> dx)',
                '-> True /\\ c <> dy /\\ c <> dby /\\ c <> dx)'), execution),
            'prefix-claimed-without-table-writes-only': (header(execution,
                'V293_task_prio_prefix table oldprio newprio ptcb rows group yo yn xo xn byo byn',
                'V293_task_prio_read_ready ptcb rows group yo yn xo xn byo byn'), execution),
            'prefix-final-old-slot-claimed-pointer-only': (header(controls,
                'V293_prefix_observes true true 80 0 1 Vnull',
                'V293_prefix_observes true true 80 0 1 (Vptr (41%positive,Int.repr 8))'), controls),
        }
    if guard:
        arithmetic = 'Theorem V293_ready_test_arithmetic :'
        continuous = 'Theorem V293_task_prio_read_ready_execution :'
        controls = 'Theorem V293_read_ready_physical_controls :'
        return {
            'ready-test-result-inverted-only': (header(arithmetic,
                '= Nat.testbit row bit.', '= negb (Nat.testbit row bit).'), arithmetic),
            'ready-false-path-claimed-update-only': (header(controls,
                'V293_read_ready_observes 16 0 2 6 false 16 0 1',
                'V293_read_ready_observes 16 0 2 6 false 80 0 1'), controls),
            'new-local-old-destination-separation-omitted-only': (header(continuous,
                '-> b <> dy /\\ b <> dby /\\ b <> dx)',
                '-> True /\\ b <> dby /\\ b <> dx)'), continuous),
            'continuous-fragment-claimed-without-reads-only': (header(continuous,
                'V293_task_prio_read_ready ptcb rows group yo yn xo xn byo byn',
                'V293_task_prio_ready_branch rows group yo yn xo xn byo byn'), continuous),
        }
    if tcb:
        field = 'Theorem V293_tcb_field_assignment :'
        execution = 'Theorem V293_task_prio_read_old_execution :'
        layout = 'Theorem V293_tcb_old_field_layout :'
        control = 'Theorem V293_tcb_read_physical_control :'
        return {
            'tcb-destination-permission-omitted-only': (header(field,
                '(exists v, get M (bd,0%Z) = Some (true,v)) ->', 'True ->'), field),
            'tcb-pointer-block-separation-omitted-only': (header(execution,
                '-> b <> bc /\\ b <> bt)', '-> True /\\ b <> bt)'), execution),
            'tcb-Y-field-offset-claimed-50-only': (header(layout,
                'field_offset 18%Z V293_tcb_fields = Some (Int.repr 52)',
                'field_offset 18%Z V293_tcb_fields = Some (Int.repr 50)'), layout),
            'tcb-BitY-readback-claimed-BitX-only': (header(control,
                "load Tint8 M' (43%positive,0%Z) = Some (V293_byteval 2)",
                "load Tint8 M' (43%positive,0%Z) = Some (V293_byteval 4)"), control),
        }
    if physical:
        rmw = 'Theorem V293_rekey_byte_rmw_execution :'
        frame = 'Lemma V293_rekey_locals_write :'
        controls = 'Theorem V293_ready_fragment_physical_controls :'
        execution = 'Theorem V293_task_prio_ready_then_execution :'
        return {
            'physical-write-permission-omitted-only': (header(rmw,
                '(exists v, get M (b,off) = Some (true,v)) ->', 'True ->'), rmw),
            'local-write-block-restriction-omitted-only': (header(frame,
                'fst a = br \/ fst a = bg ->', 'True ->'), frame),
            'physical-same-row-old-bit-restored-only': (header(controls,
                'V293_ready_fragment_observes 20 0 2 6 80 0 1',
                'V293_ready_fragment_observes 20 0 2 6 84 0 1'), controls),
            'physical-then-claimed-noop-only': (header(execution,
                'V293_task_prio_ready_then rows group yold ynew xold xnew byold bynew',
                'sskip None'), execution),
        }
    if bitmap:
        byte = 'Theorem V293_rekey_byte_arithmetic :'
        membership = 'Theorem V293_ready_rekey_membership :'
        table = 'Theorem V293_rekey_task_table_preserved :'
        controls = 'Theorem V293_ready_rekey_row_controls :'
        return {
            'byte-clear-claimed-plus-one-only': (header(byte,
                'Int.repr (Z.of_nat (Nat.clearbit row bit)) /\\',
                'Int.repr (Z.of_nat (Nat.clearbit row bit + 1)) /\\'), byte),
            'old-bit-clearing-claim-omitted-only': (header(membership,
                '(V293_bitmap_ready lo hi p /\\ p <> old)',
                'V293_bitmap_ready lo hi p'), membership),
            'new-slot-empty-omitted-only': (header(table,
                'nth new entries Vnull = Vnull ->', 'True ->'), table),
            'unused-high-row-bit-group-claimed-clear-only': (header(controls,
                'V293_ready_rekey_group 0 129 8 6 = 3',
                'V293_ready_rekey_group 0 129 8 6 = 1'), controls),
        }
    stores = 'Theorem V293_task_prio_rekey_stores :'
    execution = 'Theorem V293_OSTaskChangePrio_table_execution :'
    choice = 'Theorem V293_task_prio_rekey_ready_choice :'
    fixture = 'Theorem V293_task_prio_rekey_fixture_execution :'
    posttable = """V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) tasks ->"""
    # Each changes exactly one theorem header, retaining the entire proof suffix.
    return {
        'old-new-distinction-omitted-only': (header(stores, 'old <> new ->', 'True ->'), stores),
        'old-slot-write-permission-omitted-only': (header(execution,
            'V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->', 'True ->'), execution),
        'posttable-task-correspondence-omitted-only': (header(choice, posttable, 'True ->'), choice),
        'fixture-old-slot-claimed-nonempty-only': (header(fixture,
            'load (Tptr Tvoid) M2 (20%positive,32%Z) = Some Vnull',
            'load (Tptr Tvoid) M2 (20%positive,32%Z) = Some (Vptr (15%positive,Int.zero))'), fixture),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--bitmap', action='store_true',
                        help='check forward ready-task bitmap correspondence, not physical bitmap stores')
    modes.add_argument('--physical', action='store_true',
                       help='check physical ready THEN fragment, not outer test/TCB/full API')
    modes.add_argument('--tcb', action='store_true',
                       help='check physical TCB reads only, not outer ready/full API')
    modes.add_argument('--guard', action='store_true',
                       help='check reads -> ready if; excludes following events/full API')
    modes.add_argument('--prefix', action='store_true',
                       help='check table writes -> reads -> ready if; not events/full API')
    modes.add_argument('--event', action='store_true',
                       help='check real event-pointer read and continuous null path; non-null body/full API open')
    modes.add_argument('--event-body', action='store_true',
                       help='check actual non-null event read/if/field updates; full prefix/API/GOOD_OS open')
    modes.add_argument('--event-prefix', action='store_true',
                       help='check continuous table/TCB/ready/non-null-event path; not full API/GOOD_OS')
    modes.add_argument('--tcb-update', action='store_true',
                       help='check real five-field writes and continuous non-null prefix; full API open')
    modes.add_argument('--null-update', action='store_true',
                       help='check continuous null-event prefix and five writes; full API/GOOD_OS open')
    modes.add_argument('--nonnull-frame', action='store_true',
                       help='check continuous non-null TCB internal pointer and untouched byte frame; full API open')
    modes.add_argument('--coordinates', action='store_true',
                       help='check actual four coordinate assignments and continuous concrete migration; full API open')
    modes.add_argument('--generic-update', action='store_true',
                       help='check arbitrary-parameter coordinates through non-null migration; full API open')
    modes.add_argument('--entry', action='store_true',
                       help='check actual argument guards and 93--104 successful lookup, not critical/RESERVED/full API')
    modes.add_argument('--reserved', action='store_true',
                       help='check symbolic RESERVED equality and continuous 93--107, not critical/full API/GOOD_OS')
    modes.add_argument('--entry-update', action='store_true',
                       help='check continuous successful 93--166 non-null event path; full API/GOOD_OS open')
    modes.add_argument('--entry-null', action='store_true',
                       help='check continuous successful 93--166 NULL-event path; full API/GOOD_OS open')
    args = parser.parse_args()
    bitmap, physical, tcb, guard, prefix = args.bitmap, args.physical, args.tcb, args.guard, args.prefix
    event, event_body, event_prefix = args.event, args.event_body, args.event_prefix
    tcb_update, null_update = args.tcb_update, args.null_update
    nonnull_frame = args.nonnull_frame
    coordinates = args.coordinates
    generic_update = args.generic_update
    entry = args.entry
    reserved = args.reserved
    entry_null = args.entry_null
    entry_update = args.entry_update
    probe = 'audit/probes/V293TaskPrioEntryNullProbe.v' if entry_null else 'audit/probes/V293TaskPrioEntryUpdateProbe.v' if entry_update else 'audit/probes/V293TaskPrioReservedProbe.v' if reserved else 'audit/probes/V293TaskPrioEntryProbe.v' if entry else 'audit/probes/V293TaskPrioGenericUpdateProbe.v' if generic_update else 'audit/probes/V293TaskPrioCoordinatesProbe.v' if coordinates else 'audit/probes/V293TaskPrioNonnullFrameProbe.v' if nonnull_frame else 'audit/probes/V293TaskPrioNullUpdateProbe.v' if null_update else 'audit/probes/V293TaskPrioTCBUpdateProbe.v' if tcb_update else 'audit/probes/V293TaskPrioEventPrefixProbe.v' if event_prefix else 'audit/probes/V293TaskPrioEventBodyProbe.v' if event_body else 'audit/probes/V293TaskPrioEventProbe.v' if event else 'audit/probes/V293TaskPrioPrefixProbe.v' if prefix else 'audit/probes/V293TaskPrioGuardProbe.v' if guard else 'audit/probes/V293TaskPrioTCBProbe.v' if tcb else 'audit/probes/V293TaskPrioPhysicalProbe.v' if physical else 'audit/probes/V293TaskPrioBitmapProbe.v' if bitmap else PROBE
    root_count = 3 if entry_null else 3 if entry_update else 6 if reserved else 3 if entry else 2 if generic_update else 4 if coordinates else 3 if nonnull_frame else 4 if (tcb_update or null_update) else 3 if event_prefix else 7 if event_body else 8 if event else 7 if (prefix or guard or tcb or physical) else 8 if bitmap else ROOT_COUNT
    out = ROOT / ('audit/logs/stage26-task-prio-entry-null' if entry_null else 'audit/logs/stage26-task-prio-entry-update' if entry_update else 'audit/logs/stage26-task-prio-reserved' if reserved else 'audit/logs/stage26-task-prio-entry' if entry else 'audit/logs/stage26-task-prio-generic-update' if generic_update else
                  'audit/logs/stage26-task-prio-coordinates' if coordinates else
                  'audit/logs/stage26-task-prio-nonnull-frame' if nonnull_frame else
                  'audit/logs/stage26-task-prio-null-update' if null_update else
                  'audit/logs/stage26-task-prio-tcb-update' if tcb_update else
                  'audit/logs/stage26-task-prio-event-prefix' if event_prefix else
                  'audit/logs/stage26-task-prio-event-body' if event_body else
                  'audit/logs/stage26-task-prio-event' if event else
                  'audit/logs/stage26-task-prio-prefix' if prefix else
                  'audit/logs/stage26-task-prio-guard' if guard else
                  'audit/logs/stage26-task-prio-tcb' if tcb else
                  'audit/logs/stage26-task-prio-physical' if physical else
                  'audit/logs/stage26-task-prio-bitmap' if bitmap else
                  'audit/logs/stage26-task-prio-rekey') / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {probe, 'scripts/check-v293-task-prio-rekey.py',
                    'tests/test_task_prio_rekey_local.py',
                    *(['tests/test_task_prio_bitmap_local.py'] if bitmap else []),
                    *(['tests/test_task_prio_physical_local.py'] if physical else []),
                    *(['tests/test_task_prio_entry_null_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'docs/adr/0004-保留指针采用显式符号地址.md',
                       'audit/logs/stage26-task-prio-entry-null/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-entry-null/source-identity.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-entry-ast.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-coordinate-ast.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-reserved-ast.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-entry-null/configured-tcb-record.json'] if entry_null else []),
                    *(['tests/test_task_prio_entry_update_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'docs/adr/0004-保留指针采用显式符号地址.md',
                       'audit/logs/stage26-task-prio-entry-update/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-entry-update/source-identity.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-entry-ast.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-coordinate-ast.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-reserved-ast.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-entry-update/configured-tcb-record.json'] if entry_update else []),
                    *(['tests/test_task_prio_reserved_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-reserved/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-reserved/REPRESENTATION_DECISION.md',
                       'docs/adr/0004-保留指针采用显式符号地址.md',
                       'audit/logs/stage26-task-prio-reserved/source-identity.json',
                       'audit/logs/stage26-task-prio-reserved/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-reserved/configured-reserved-ast.json',
                       'audit/logs/stage26-task-prio-reserved/reserved-source-occurrences.json',
                       'audit/logs/stage26-task-prio-reserved/source-lines-60-108.txt'] if reserved else []),
                    *(['tests/test_task_prio_entry_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-entry/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-entry/SCOPE_REFINEMENT.md',
                       'audit/logs/stage26-task-prio-entry/ADVERSARIAL_CONTROL_REFINEMENT.md',
                       'audit/logs/stage26-task-prio-entry/source-identity.json',
                       'audit/logs/stage26-task-prio-entry/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-entry/configured-entry-ast.json',
                       'audit/logs/stage26-task-prio-entry/configured-tcb-record.json',
                       'audit/logs/stage26-task-prio-entry/source-lines-60-108.txt'] if entry else []),
                    *(['tests/test_task_prio_generic_update_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-generic-update/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-coordinates/source-identity.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-coordinate-ast.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-tcb-record.json'] if generic_update else []),
                    *(['tests/test_task_prio_coordinates_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-coordinates/source-identity.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-coordinate-ast.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-coordinates/configured-tcb-record.json',
                       'audit/logs/stage26-task-prio-coordinates/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-coordinates/source-lines-95-118.txt',
                       'audit/logs/stage26-task-prio-coordinates/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-coordinates/PROTOCOL.md'] if coordinates else []),
                    *(['tests/test_task_prio_nonnull_frame_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/source-identity.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/configured-tcb-record.json',
                       'audit/logs/stage26-task-prio-nonnull-frame/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-nonnull-frame/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-nonnull-frame/PROTOCOL.md'] if nonnull_frame else []),
                    *(['tests/test_task_prio_null_update_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-null-update/source-identity.json',
                       'audit/logs/stage26-task-prio-null-update/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-null-update/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-null-update/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-null-update/configured-tcb-record.json',
                       'audit/logs/stage26-task-prio-null-update/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-null-update/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-null-update/PROTOCOL.md'] if null_update else []),
                    *(['tests/test_task_prio_tcb_update_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-tcb-update/source-identity.json',
                       'audit/logs/stage26-task-prio-tcb-update/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-tcb-update/configured-tcb-update-ast.json',
                       'audit/logs/stage26-task-prio-tcb-update/configured-tcb-record.json',
                       'audit/logs/stage26-task-prio-tcb-update/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-tcb-update/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-tcb-update/PROTOCOL.md'] if tcb_update else []),
                    *(['tests/test_task_prio_event_prefix_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-event-prefix/source-identity.json',
                       'audit/logs/stage26-task-prio-event-prefix/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-event-prefix/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-event-prefix/configured-event-record.json',
                       'audit/logs/stage26-task-prio-event-prefix/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-event-prefix/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-event-prefix/PROTOCOL.md'] if event_prefix else []),
                    *(['tests/test_task_prio_event_body_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-event-body/source-identity.json',
                       'audit/logs/stage26-task-prio-event-body/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-event-body/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-event-body/configured-event-record.json',
                       'audit/logs/stage26-task-prio-event-body/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-event-body/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-event-body/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-event-body/SCOPE_REFINEMENT.md'] if event_body else []),
                    *(['tests/test_task_prio_event_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-event/source-identity.json',
                       'audit/logs/stage26-task-prio-event/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-event/configured-event-ast.json',
                       'audit/logs/stage26-task-prio-event/configured-event-record.json',
                       'audit/logs/stage26-task-prio-event/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-event/source-lines-119-172.txt',
                       'audit/logs/stage26-task-prio-event/PROTOCOL.md'] if event else []),
                    *(['tests/test_task_prio_prefix_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-guard/source-identity.json',
                       'audit/logs/stage26-task-prio-guard/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-guard/configured-ready-condition.json',
                       'audit/logs/stage26-task-prio-guard/source-lines-119-141.txt',
                       'audit/logs/stage26-task-prio-prefix/PROTOCOL.md'] if prefix else []),
                    *(['tests/test_task_prio_guard_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-guard/source-identity.json',
                       'audit/logs/stage26-task-prio-guard/configured-ready-condition.json',
                       'audit/logs/stage26-task-prio-guard/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-guard/source-lines-119-141.txt',
                       'audit/logs/stage26-task-prio-guard/PROTOCOL.md'] if guard else []),
                    *(['tests/test_task_prio_tcb_local.py', 'csrc/repairs/FROZEN_SOURCE.json',
                       'audit/logs/stage26-task-prio-tcb/source-identity.json',
                       'audit/logs/stage26-task-prio-tcb/configured-TCB-fields.json',
                       'audit/logs/stage26-task-prio-tcb/configured-function-identity.json',
                       'audit/logs/stage26-task-prio-tcb/clang-source-record-layouts.log',
                       'audit/logs/stage26-task-prio-tcb/PROTOCOL.md',
                       'audit/logs/stage26-task-prio-tcb/SCOPE_REFINEMENT.md'] if tcb else []),
                    'scripts/check-v293-storage-prefix.py', 'scripts/check-memory-trust.py',
                    'Makefile', '_CoqProject'})
    identity = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    report = {'scope': ('LOCAL_CONTINUOUS_ENTRY_TO_NULL_MIGRATION_93_166_NOT_CRITICAL_FULL_API_GOOD_OS' if entry_null else
                        'LOCAL_CONTINUOUS_ENTRY_TO_NONNULL_MIGRATION_93_166_NOT_CRITICAL_FULL_API_GOOD_OS' if entry_update else
                        'LOCAL_SYMBOLIC_RESERVED_EQUALITY_AND_CONTINUOUS_93_107_NOT_CRITICAL_FULL_API_GOOD_OS' if reserved else
                        'LOCAL_ARGUMENT_GUARDS_SELF_AND_REAL_TASK_LOOKUP_NOT_CRITICAL_RESERVED_FULL_API_GOOD_OS' if entry else
                        'LOCAL_GENERIC_COORDINATES_THROUGH_NONNULL_MIGRATION_NOT_FULL_API_GOOD_OS' if generic_update else
                        'LOCAL_FOUR_COORDINATE_ASSIGNMENTS_AND_CONCRETE_CONTINUOUS_MIGRATION_NOT_FULL_API_GOOD_OS' if coordinates else
                        'LOCAL_CONTINUOUS_NONNULL_TCB_INTERNAL_EVENT_AND_BYTE_FRAME_NOT_FULL_API_GOOD_OS' if nonnull_frame else
                        'LOCAL_CONTINUOUS_NULL_EVENT_PREFIX_FIVE_TCB_WRITES_NOT_FULL_API_GOOD_OS' if null_update else
                        'LOCAL_CONTINUOUS_TABLE_TCB_READS_READY_NONNULL_EVENT_FIVE_FIELD_WRITES_NOT_FULL_API_GOOD_OS' if tcb_update else
                        'LOCAL_CONTINUOUS_TABLE_READS_READY_NONNULL_EVENT_NOT_TCB_UPDATE_FULL_API_GOOD_OS' if event_prefix else
                        'LOCAL_NONNULL_EVENT_READ_IF_FIELD_UPDATES_NOT_CONTINUOUS_TABLE_PREFIX_FULL_API_GOOD_OS' if event_body else
                        'LOCAL_EVENT_READ_AND_CONTINUOUS_NULL_PATH_NOT_NONNULL_BODY_FULL_API_GOOD_OS' if event else
                        'LOCAL_TABLE_WRITES_READS_READY_IF_NOT_EVENTS_FULL_API_OR_GOOD_OS' if prefix else
                        'LOCAL_TCB_READS_THEN_READY_IF_NOT_EVENTS_FULL_API_OR_GOOD_OS' if guard else
                        'LOCAL_PHYSICAL_TCB_READS_NOT_OUTER_READY_FULL_API_OR_GOOD_OS' if tcb else
                        'LOCAL_PHYSICAL_READY_THEN_NOT_OUTER_TEST_TCB_OR_FULL_API' if physical else
                        'LOCAL_READY_VALUE_CORRESPONDENCE_NOT_BITMAP_STORES_TCB_OR_FULL_API'
                        if bitmap else 'LOCAL_TWO_TABLE_WRITES_NOT_FULL_API_BITMAP_TCB_CRITICAL_OR_GOOD_OS'),
              'kernel_GOOD_OS_proved': False, 'source_OSCtxSw_contract_discharged': False,
              'formal_function_evidence_updated': False, 'prebuilt_dependency_closure': True,
              'input_sha256': identity, 'checks': {}, 'negative_controls': {}, 'passed': False}
    coqbin = os.environ.get('COQBIN', '')

    def run(label, args, required=True):
        started = time.monotonic()
        try:
            p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=600)
        except subprocess.TimeoutExpired as error:
            output = error.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
            (out / (label + '.log')).write_text(output)
            report['checks'][label] = {'exit_code': 124, 'timeout_seconds': 600,
                                       'elapsed_seconds': time.monotonic() - started,
                                       'log': label + '.log'}
            raise
        (out / (label + '.log')).write_text(p.stdout)
        report['checks'][label] = {'exit_code': p.returncode, 'log': label + '.log',
                                   'elapsed_seconds': time.monotonic() - started}
        if required and p.returncode:
            raise ValueError(label + ' failed; inspect ' + str(out))
        return p.returncode, p.stdout

    work = None
    try:
        _, version = run('version', [coqbin + 'coqc', '--version'])
        if not re.search(r'version 8\.18\.0(?: |$)', version, re.MULTILINE):
            raise ValueError('Coq 8.18.0 required')
        for source in SOURCES:
            run(Path(source).stem, [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', source])
        _, output = run(f'{root_count}-literal-roots', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', probe])
        report['actual_assumptions_union'] = checked_assumptions(output, root_count)
        for source in [*SOURCES, probe]:
            run(Path(source).stem + '-coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                'CertiOS.' + str(Path(source).with_suffix('')).replace('/', '.')])
        work = Path(tempfile.mkdtemp(prefix='v293-task-rekey-'))
        positive = work / 'positive-same-environment'
        positive.mkdir()
        flags = ['-q', '-R', '.', 'CertiOS']
        for namespace in ['code', 'proofs']:
            (positive / namespace).mkdir()
            flags += ['-R', str(positive / namespace), 'CertiOS.certiucos.v293.' + namespace]
        for source in SOURCES:
            namespace = Path(source).parent.name
            path = positive / namespace / Path(source).name
            path.write_bytes((ROOT / source).read_bytes())
            run('positive-' + path.stem, [coqbin + 'coqc', *flags, str(path)])
        _, output = run('positive-probe', [coqbin + 'coqc', *flags, probe])
        if checked_assumptions(output, root_count) != report['actual_assumptions_union']:
            raise ValueError('positive assumptions differ')
        original = (ROOT / PROOF).read_text()
        for label, (candidate, declaration) in mutations(original, bitmap, physical, tcb, guard, prefix, event, event_body, event_prefix, tcb_update, null_update, nonnull_frame, coordinates, generic_update, entry, reserved, entry_update, entry_null).items():
            start = original.index(declaration)
            end = original.index('Proof.', start)
            candidate_end = candidate.index('Proof.', start)
            if candidate[:start] != original[:start] or candidate[candidate_end:] != original[end:]:
                raise ValueError('control changed more than designated theorem header')
            case = work / label
            case.mkdir()
            path = case / Path(PROOF).name
            path.write_text(candidate)
            (out / (label + '.candidate.v.txt')).write_text(candidate)
            code, output = run(label, [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                '-R', str(case), 'CertiOS.certiucos.v293.proofs', str(path)], False)
            report['negative_controls'][label] = CHECK.check_rejection(code, output, candidate, declaration, path)
            if entry or reserved or entry_update or entry_null:
                proof_line = candidate[:candidate.index('Proof.', candidate.index(declaration))].count('\n') + 1
                control = report['negative_controls'][label]
                control['rejection_after_proof_started'] = control['line'] > proof_line
                if not control['rejection_after_proof_started']:
                    raise ValueError('entry/reserved/entry-update control rejected before proof; not a semantic control')
        if identity != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}:
            raise ValueError('protocol inputs changed during verification')
        report['passed'] = True
    finally:
        if work is not None:
            targets = [{'path': str(p), 'size': p.stat().st_size,
                        'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in sorted(work.rglob('*')) if p.is_file()]
            (out / 'temporary-cleanup-manifest.json').write_text(json.dumps(targets, indent=2) + '\n')
            for row in targets:
                path = Path(row['path'])
                if path.stat().st_size != row['size'] or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
                    raise ValueError('temporary cleanup target changed')
            shutil.rmtree(work)
            report['temporary_cleanup'] = {'files': len(targets), 'bytes': sum(p['size'] for p in targets),
                                           'removed': not work.exists()}
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print('LOCAL CONTINUOUS ENTRY THROUGH NULL MIGRATION 93--166: PASS (critical/full API/GOOD_OS open)' if entry_null else
          'LOCAL CONTINUOUS ENTRY THROUGH NONNULL MIGRATION 93--166: PASS (critical/full API/GOOD_OS open)' if entry_update else
          'LOCAL SYMBOLIC RESERVED AND CONTINUOUS 93--107: PASS (representation obligations/critical/full API/GOOD_OS open)' if reserved else
          'LOCAL ARGUMENT GUARDS / SELF / TASK LOOKUP: PASS (critical/RESERVED/full API/GOOD_OS open)' if entry else
          'LOCAL GENERIC COORDINATES THROUGH NONNULL MIGRATION: PASS (full API/GOOD_OS open)' if generic_update else
          'LOCAL FOUR COORDINATES AND CONTINUOUS CONCRETE MIGRATION: PASS (full API/GOOD_OS open)' if coordinates else
          'LOCAL CONTINUOUS NONNULL TCB INTERNAL FRAME: PASS (full API/GOOD_OS open)' if nonnull_frame else
          'LOCAL CONTINUOUS NULL PREFIX AND FIVE TCB WRITES: PASS (full API/GOOD_OS open)' if null_update else
          'LOCAL CONTINUOUS PREFIX AND FIVE TCB WRITES: PASS (full API/GOOD_OS open)' if tcb_update else
          'LOCAL NONNULL EVENT READ / IF / FIELD UPDATES: PASS (full prefix/API/GOOD_OS open)' if event_body else
          'LOCAL EVENT READ / CONTINUOUS NULL PATH: PASS (non-null body/full API/GOOD_OS open)' if event else
          'LOCAL TABLE -> READS -> READY IF: PASS (events/full API/GOOD_OS remain open)' if prefix else
          'LOCAL READS -> READY IF: PASS (following events/full API/GOOD_OS remain open)' if guard else
          'LOCAL TCB READS: PASS (outer ready/full API/GOOD_OS remain open)' if tcb else
          'LOCAL PHYSICAL READY THEN: PASS (outer test/TCB/full API remain open)' if physical else
          'LOCAL READY CORRESPONDENCE: PASS (physical bitmap/TCB/full API remain open)' if bitmap else
          'LOCAL TABLE WRITES: PASS (full API/bitmap/TCB/GOOD_OS remain open)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
