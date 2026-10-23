#!/usr/bin/env python3
"""Supervise one fixture; retain only reconstructed, bounded diagnostic records."""

import argparse
from collections import Counter, OrderedDict, deque
import errno
import json
import os
from pathlib import Path
import re
import resource
import selectors
import signal
import subprocess
import sys
import time


MAX_LINE_BYTES = 65536
MAX_NATIVE_EVENTS = 2048
MAX_DIAGNOSTIC_EVENTS = 128
MAX_LINEAGE_FACTS = 64
MAX_OBJECTS = 4096
POST_EXIT_DRAIN_SECONDS = 2.0
CANCELLATION_GRACE_SECONDS = 2.0
SYNTHETIC_APP_IDS = frozenset((
    "krema-inplace-a", "krema-inplace-b", "krema-inplace-c",
    "krema-inplace-unpinned", "krema-inplace-unpinned-u", "krema-inplace-unpinned-v",
    "krema-inplace-a.desktop", "krema-inplace-b.desktop", "krema-inplace-c.desktop",
    "krema-inplace-unpinned.desktop", "krema-inplace-unpinned-u.desktop",
    "krema-inplace-unpinned-v.desktop",
))
TEST_CASE_NAMES = frozenset((
    "Started tasks replace their pinned launchers in place",
    "Grouped tasks preserve pinned launcher slots",
    "An explicit reorder wins over a pending launcher-slot repair",
    "A real startup notification retains its pinned slot when its window arrives",
    "Launcher-list setters distinguish pending repair from new pinned intent",
    "Real startup replacement preserves mixed-mode unpinned anchors",
))
SECTION_NAMES = frozenset((
    "The same launcher list retains the startup anchor",
    "A reordered launcher list replaces the old intent",
    "A changed launcher list replaces the old intent",
))
NUMBER = r"-?[0-9]{1,12}(?:\.[0-9]{1,8})?"
UINT = re.compile(r"[0-9]{1,10}\Z")
OBJECT = re.compile(r"(?:new id )?([a-z][a-z0-9_]*)[@#]([0-9]{1,10})\Z")
MESSAGE = re.compile(
    r"(?:\[(?P<clock>(?:[01][0-9]|2[0-3]):[0-5][0-9]:[0-5][0-9]\.[0-9]{6})\]|"
    r"\[\s*(?P<numeric>[0-9]{1,12}(?:\.[0-9]{1,8})?)\])\s*"
    r"(?:TID#[0-9]{1,10}\s*)?"
    r"(?:\{[A-Za-z0-9 _-]{1,64}\}\s*)?"
    r"(?P<discarded>discarded\s+)?(?P<direction>->\s*)?"
    r"(?P<interface>[a-z][a-z0-9_]*)[@#](?P<identifier>[0-9]{1,10})\."
    r"(?P<method>[a-z][a-z0-9_]*)\((?P<arguments>.*)\)\s*\Z"
)


def timestamp_milliseconds(match):
    value = match.group("clock")
    if value:
        hours, minutes, seconds = value.split(":")
        return (int(hours) * 3600 + int(minutes) * 60 + float(seconds)) * 1000
    return float(match.group("numeric"))


INTERFACES = frozenset((
    "wl_compositor", "wl_surface", "wl_region", "wl_seat", "wl_pointer",
    "wl_keyboard", "wl_output", "zwlr_layer_shell_v1", "zwlr_layer_surface_v1",
    "xdg_wm_base", "xdg_surface", "xdg_toplevel", "wl_callback",
    "org_kde_kwin_fake_input", "org_kde_plasma_window_management",
    "org_kde_plasma_window",
))
LINEAGE_METHODS = frozenset((
    ("wl_compositor", "create_surface"),
    ("wl_seat", "get_pointer"),
    ("wl_seat", "get_keyboard"),
    ("zwlr_layer_shell_v1", "get_layer_surface"),
    ("xdg_wm_base", "get_xdg_surface"),
    ("xdg_surface", "get_toplevel"),
    ("wl_output", "name"),
    ("wl_output", "geometry"),
    ("wl_output", "mode"),
    ("wl_output", "scale"),
))
EVENT_NAMES = frozenset((
    "press", "double-click", "release", "enter", "leave", "activate",
    "deactivate", "focus-in", "focus-out",
))
BOOL_FIELDS = frozenset((
    "focusIsLauncher", "widgetDoesNotAcceptFocus", "windowDoesNotAcceptFocus",
    "widgetTransparentForInput", "windowTransparentForInput",
    "widgetTransparentForMouse", "widgetShowWithoutActivating", "active",
    "widgetActive", "widgetVisible", "windowVisible", "exposed",
    "cachedActiveAfterGesture", "helperProxyValid",
))
INT_FIELDS = frozenset((
    "widgetFocusPolicy", "keyboardInteractivity", "helperFd", "helperDisplayError",
    "helperFdFlags", "helperFdFlagsError", "helperSocketPoll",
    "helperSocketPollError", "helperSocketRevents", "omittedEvents",
))
GEOMETRY_FIELDS = frozenset((
    "screenGeometry", "widgetGeometry", "widgetGlobalRect", "windowGeometry",
    "intendedClickRect", "intendedClick", "lastMouseGlobal", "lastMouseLocal",
))
STAGES = frozenset((
    "requesting-surface", "fake-input-device", "requesting-surface-click-rect",
    "requesting-surface-active", "launcher-index", "child-connection-wait",
    "child-accept", "child-peer-credentials", "child-peer-identity",
    "child-handshake-token-present-v1",
))
FIELD = re.compile(r"(?:^| )([A-Za-z][A-Za-z0-9]*(?:\(ret,errno\))?)=")


def split_arguments(text):
    """Parse argument boundaries; strings are discarded before any retention."""
    result = []
    offset = 0
    while offset < len(text):
        while offset < len(text) and text[offset].isspace():
            offset += 1
        if offset == len(text):
            return None
        if text[offset] == '"':
            offset += 1
            while offset < len(text):
                if text[offset] == "\\":
                    offset += 2
                elif text[offset] == '"':
                    offset += 1
                    break
                else:
                    offset += 1
            else:
                return None
            # Never retain even a known app ID or activation-token argument.
            value = None
        else:
            start = offset
            while offset < len(text) and text[offset] != ',':
                offset += 1
            value = text[start:offset].strip()
            if not value or any(char in value for char in ('"', "'", "\\")):
                return None
        result.append(value)
        while offset < len(text) and text[offset].isspace():
            offset += 1
        if offset == len(text):
            return result
        if text[offset] != ',':
            return None
        offset += 1
        if offset == len(text):
            return None
    return result


def typed_value(value, kind):
    if kind == "string":
        return "[redacted]" if value is None else None
    if value is None:
        return None
    if kind == "uint" and UINT.fullmatch(value) and int(value) <= 4294967295:
        return int(value)
    if kind == "number" and re.fullmatch(NUMBER, value):
        return float(value) if '.' in value else int(value)
    if kind == "array" and re.fullmatch(r"array\[[0-9]{1,10}\]", value):
        return "[omitted]"
    if kind.startswith("object:"):
        interface = kind.partition(':')[2]
        if value == "nil":
            return {"interface": interface, "id": 0}
        found = OBJECT.fullmatch(value)
        if found and found[1] == interface and int(found[2]) <= 4294967295:
            return {"interface": interface, "id": int(found[2])}
    return None


# Explicit signatures: no arbitrary method names, strings, arrays, key events,
# keymap descriptors, modifiers, or protocol prefixes are ever serialized.
SIGNATURES = {
    ("wl_compositor", "create_surface"): (("surface", "object:wl_surface"),),
    ("wl_compositor", "create_region"): (("region", "object:wl_region"),),
    ("wl_seat", "get_pointer"): (("pointer", "object:wl_pointer"),),
    ("wl_seat", "get_keyboard"): (("keyboard", "object:wl_keyboard"),),
    ("wl_seat", "capabilities"): (("capabilities", "uint"),),
    ("wl_output", "geometry"): (("x", "number"), ("y", "number"), ("physical_width", "number"), ("physical_height", "number"), ("subpixel", "number"), ("make", "string"), ("model", "string"), ("transform", "number")),
    ("wl_output", "mode"): (("flags", "uint"), ("width", "number"), ("height", "number"), ("refresh", "number")),
    ("wl_output", "scale"): (("factor", "number"),),
    ("wl_output", "name"): (("name", "string"),),
    ("wl_output", "done"): (),
    ("wl_pointer", "enter"): (("serial", "uint"), ("surface", "object:wl_surface"), ("x", "number"), ("y", "number")),
    ("wl_pointer", "leave"): (("serial", "uint"), ("surface", "object:wl_surface")),
    ("wl_pointer", "motion"): (("time", "uint"), ("x", "number"), ("y", "number")),
    ("wl_pointer", "button"): (("serial", "uint"), ("time", "uint"), ("button", "uint"), ("state", "uint")),
    ("wl_pointer", "frame"): (),
    ("wl_keyboard", "enter"): (("serial", "uint"), ("surface", "object:wl_surface"), ("keys", "array")),
    ("wl_keyboard", "leave"): (("serial", "uint"), ("surface", "object:wl_surface")),
    ("wl_surface", "set_input_region"): (("region", "object:wl_region"),),
    ("wl_surface", "set_opaque_region"): (("region", "object:wl_region"),),
    ("wl_surface", "commit"): (),
    ("wl_surface", "attach"): (("buffer", "object:wl_buffer"), ("x", "number"), ("y", "number")),
    ("wl_surface", "frame"): (("callback", "object:wl_callback"),),
    ("wl_callback", "done"): (("time", "uint"),),
    ("wl_region", "add"): (("x", "number"), ("y", "number"), ("width", "number"), ("height", "number")),
    ("wl_region", "subtract"): (("x", "number"), ("y", "number"), ("width", "number"), ("height", "number")),
    ("zwlr_layer_shell_v1", "get_layer_surface"): (("layer_surface", "object:zwlr_layer_surface_v1"), ("surface", "object:wl_surface"), ("output", "object:wl_output"), ("layer", "uint"), ("namespace", "string")),
    ("zwlr_layer_surface_v1", "set_keyboard_interactivity"): (("mode", "uint"),),
    ("zwlr_layer_surface_v1", "set_anchor"): (("anchor", "uint"),),
    ("zwlr_layer_surface_v1", "set_size"): (("width", "uint"), ("height", "uint")),
    ("zwlr_layer_surface_v1", "set_exclusive_zone"): (("zone", "number"),),
    ("zwlr_layer_surface_v1", "set_margin"): (("top", "number"), ("right", "number"), ("bottom", "number"), ("left", "number")),
    ("zwlr_layer_surface_v1", "configure"): (("serial", "uint"), ("width", "uint"), ("height", "uint")),
    ("zwlr_layer_surface_v1", "ack_configure"): (("serial", "uint"),),
    ("zwlr_layer_surface_v1", "closed"): (),
    ("xdg_wm_base", "get_xdg_surface"): (("xdg_surface", "object:xdg_surface"), ("surface", "object:wl_surface")),
    ("xdg_surface", "get_toplevel"): (("toplevel", "object:xdg_toplevel"),),
    ("xdg_surface", "configure"): (("serial", "uint"),),
    ("xdg_surface", "ack_configure"): (("serial", "uint"),),
    ("xdg_toplevel", "set_app_id"): (("app_id", "string"),),
    ("org_kde_plasma_window_management", "get_window"): (("window", "object:org_kde_plasma_window"), ("internal_id", "uint")),
    ("org_kde_plasma_window_management", "get_window_by_uuid"): (("window", "object:org_kde_plasma_window"), ("uuid", "string")),
    ("org_kde_plasma_window", "state_changed"): (("state", "uint"),),
    ("org_kde_plasma_window", "unmapped"): (),
    ("org_kde_plasma_window", "app_id_changed"): (("app_id", "string"),),
    ("org_kde_plasma_window", "pid_changed"): (("pid", "uint"),),
    ("org_kde_kwin_fake_input", "pointer_motion_absolute"): (("x", "number"), ("y", "number")),
    ("org_kde_kwin_fake_input", "button"): (("button", "uint"), ("state", "uint")),
}
for _interface in INTERFACES:
    SIGNATURES[(_interface, "destroy")] = ()


def diagnostic_value(key, value):
    if key in BOOL_FIELDS and value in ("true", "false", "0", "1"):
        return value in ("true", "1")
    if key in INT_FIELDS and re.fullmatch(r"-?[0-9]{1,20}", value):
        return int(value)
    if key in GEOMETRY_FIELDS:
        if re.fullmatch(r"Q(?:Rect|PointF?)\([-0-9., x]+\)", value):
            numbers = re.findall(NUMBER, value)
            if len(numbers) in (2, 4):
                return [float(item) if '.' in item else int(item) for item in numbers]
    if key in ("focusWindow", "screen", "helperDisplay"):
        if re.fullmatch(r"(?:0x[0-9a-fA-F]{1,16}|0|QWindow\(0x[0-9a-fA-F]{1,16}\))", value):
            return {"present": value not in ("0", "0x0", "QWindow(0x0)")}
    if key == "receiver" and value in ("QWidget", "QWindow", '"QWidget"', '"QWindow"'):
        return value.strip('"')
    if key == "currentScreenName":
        match = re.fullmatch(r'"Virtual-([0-9]{1,6})"', value)
        if match:
            return "Virtual-" + str(int(match[1]))
    if key == "activeTaskAppIds":
        match = re.fullmatch(r"(?:QList|QStringList)\((.*)\)", value)
        if match:
            entries = split_arguments(match[1])
            quoted = re.findall(r'"([^"\\]*)"', match[1])
            if entries is not None and len(entries) == len(quoted) and all(item is None for item in entries):
                return [item if item in SYNTHETIC_APP_IDS else "[redacted]" for item in quoted[:64]]
    if key in ("widgetFlags", "windowFlags"):
        if re.fullmatch(r"(?:0x[0-9a-fA-F]{1,16}|[0-9]{1,20})", value):
            return int(value, 16 if value.startswith("0x") else 10)
        allowed = {"Window", "Dialog", "Tool", "FramelessWindowHint", "WindowDoesNotAcceptFocus", "WindowTransparentForInput", "WindowStaysOnTopHint", "WindowStaysOnBottomHint", "NoDropShadowWindowHint", "WindowTitleHint", "WindowSystemMenuHint", "WindowMinMaxButtonsHint", "WindowCloseButtonHint", "WindowFullscreenButtonHint", "CustomizeWindowHint", "WindowMinimizeButtonHint", "WindowMaximizeButtonHint", "WindowContextHelpButtonHint", "Widget"}
        found = re.fullmatch(r"QFlags<Qt::WindowType>\(([A-Za-z|]+)\)", value)
        if found and set(found[1].split('|')) <= allowed:
            return found[1].split('|')
    if key in ("widgetMask", "windowMask"):
        if value == "QRegion(null)":
            return {"empty": True}
        if re.fullmatch(r"QRegion\([-0-9,+ x]+\)", value):
            numbers = re.findall(r"-?[0-9]+", value)
            if len(numbers) <= 256 and all(len(item) <= 13 for item in numbers):
                return {"numbers": [int(item) for item in numbers]}
    if key.endswith("Roundtrip(ret,errno)") and key in ("motionRoundtrip(ret,errno)", "pressRoundtrip(ret,errno)", "releaseRoundtrip(ret,errno)", "lastRoundtrip(ret,errno)"):
        if re.fullmatch(r"\(-?[0-9]{1,10},-?[0-9]{1,10}\)", value):
            return [int(item) for item in value[1:-1].split(',')]
    if key in ("eventDeltas", "eventTotals", "orderedEvents"):
        found = re.fullmatch(r"(?:QList|QStringList)\((.*)\)", value)
        if found:
            entries = split_arguments(found[1])
            # Validate original quoted contents against finite event vocabularies;
            # no generic quoted string is ever retained by this exception.
            if entries is not None and len(entries) <= (64 if key == "orderedEvents" else 9) and all(item is None for item in entries):
                quoted = re.findall(r'"([^"\\]*)"', found[1])
                if len(quoted) == len(entries):
                    if key == "orderedEvents":
                        result = []
                        for item in quoted:
                            match = re.fullmatch(r"([0-9]{1,20}):(QWidget|QWindow):([a-z-]+)", item)
                            if not match or match[3] not in EVENT_NAMES:
                                return None
                            result.append({"ordinal": int(match[1]), "receiver": match[2], "event": match[3]})
                        return result
                    result = {}
                    for item in quoted:
                        match = re.fullmatch(r"([a-z-]+)=([0-9]{1,20})", item)
                        if not match or match[1] not in EVENT_NAMES:
                            return None
                        result[match[1]] = int(match[2])
                    return result
    return None


def sanitize_diagnostic(line):
    text = line.strip()
    if text in TEST_CASE_NAMES:
        return {"kind": "catch-case", "name": text}
    if text in SECTION_NAMES:
        return {"kind": "catch-section", "name": text}
    match = re.fullmatch(r"(?:[A-Za-z0-9_./-]*/)?test_launch_in_place\.cpp(?::([0-9]{1,10})|\(([0-9]{1,10})\))(?:: (FAILED|PASSED):)?", text)
    if match:
        record = {"kind": "catch-location", "file": "test_launch_in_place.cpp", "line": int(match[1] or match[2])}
        if match[3]:
            record["status"] = match[3].lower()
        return record
    if text.startswith("focus-failure "):
        tail = text[len("focus-failure "):]
        result = {"kind": "focus-failure"}
        for phase in ("before-gesture", "after-failed-wait"):
            if tail.startswith(phase + ': '):
                result["phase"] = phase
                tail = tail[len(phase) + 2:]
                break
        fields = list(FIELD.finditer(tail))
        for index, match in enumerate(fields):
            end = fields[index + 1].start() if index + 1 < len(fields) else len(tail)
            value = diagnostic_value(match[1], tail[match.end():end].strip())
            if value is not None:
                result[match[1]] = value
        return result if len(result) > 1 else None
    found = re.fullmatch(r"All tests passed \(([0-9]{1,20}) assertions? in ([0-9]{1,20}) test cases?\)", text)
    if found:
        return {"kind": "catch-summary", "assertions": int(found[1]), "test_cases": int(found[2]), "passed": True}
    found = re.fullmatch(r"(test cases|assertions):\s*([0-9]{1,20})((?:\s*\|\s*[0-9]{1,20}\s+(?:passed|failed|failed as expected|skipped))*)", text)
    if found:
        result = {"kind": "catch-summary", "category": found[1], "total": int(found[2])}
        for number, status in re.findall(r"\|\s*([0-9]{1,20})\s+(passed|failed as expected|failed|skipped)", found[3]):
            result[status.replace(' ', '_')] = int(number)
        return result
    found = re.fullmatch(r"Randomness seeded to: ([0-9]{1,20})", text)
    if found:
        return {"kind": "catch-seed", "seed": int(found[1])}
    if text == "FAILED:":
        return {"kind": "catch-failure"}
    found = re.fullmatch(r"startup fixture failure stage:\s*([a-z0-9-]+)(?: errno=([0-9]{1,10}) \([^\r\n]*\))?", text)
    if found and found[1] in STAGES:
        result = {"kind": "startup-failure", "stage": found[1]}
        if found[2]:
            result["errno"] = int(found[2])
        return result
    found = re.fullmatch(r"startup observation -> map ACK: ([0-9]{1,12})ms; launch -> map ACK: ([0-9]{1,12})ms", text)
    if found:
        return {"kind": "startup-clock", "observation_to_map_ms": int(found[1]), "launch_to_map_ms": int(found[2])}
    return None


class TraceSanitizer:
    def __init__(self, mode):
        self.mode = mode
        self.counts = Counter({name: 0 for name in (
            "stdout_bytes", "stderr_bytes", "stdout_lines", "stderr_lines",
            "protocol_lines", "protocol_dropped", "native_retained",
            "diagnostic_retained", "nonallowlisted_dropped",
            "oversized_lines_dropped", "native_ring_evictions",
            "diagnostic_ring_evictions", "object_evictions",
            "post_exit_pipe_cutoffs", "output_pipe_closed",
            "lineage_facts_retained", "lineage_facts_omitted",
        )})
        self.native_counts = Counter()
        self.native = deque(maxlen=MAX_NATIVE_EVENTS)
        self.diagnostics = deque(maxlen=MAX_DIAGNOSTIC_EVENTS)
        self.lineage = []
        self.objects = OrderedDict()
        self.sequence = 0
        self.creation = 0
        self.first_fake_button_seq = None
        self.after_gesture_counts = Counter()

    def object_ref(self, interface, identifier, create=False, parent=None):
        key = (interface, identifier)
        if create or key not in self.objects:
            self.creation += 1
            value = {"interface": interface, "id": identifier, "generation": self.creation, "origin": "created" if create else "unobserved"}
            if parent is not None:
                value["parent"] = parent
            self.objects[key] = value
            if len(self.objects) > MAX_OBJECTS:
                self.objects.popitem(last=False)
                self.counts["object_evictions"] += 1
        self.objects.move_to_end(key)
        return dict(self.objects[key])

    def sanitize_line(self, line, stream):
        self.counts[stream + "_lines"] += 1
        self.sequence += 1
        match = MESSAGE.fullmatch(line)
        if match:
            self.counts["protocol_lines"] += 1
            if match.group("discarded"):
                # A discarded event is not evidence of delivered native focus.
                self.counts["protocol_discarded"] += 1
                self.counts["protocol_dropped"] += 1
                return None
            if self.mode != "on":
                self.counts["protocol_dropped"] += 1
                return None
            interface, method = match.group("interface"), match.group("method")
            argument_text = match.group("arguments")
            if interface == "wl_registry" and method == "bind":
                # Registry interface strings are retained only as finite schema
                # atoms; the original prefix/string is never passed through.
                bound = re.fullmatch(r'([0-9]{1,10}), "([a-z][a-z0-9_]*)", ([0-9]{1,10}), new id ([a-z][a-z0-9_]*|\[unknown\])[@#]([0-9]{1,10})', argument_text)
                if bound and bound[2] in INTERFACES and bound[4] in (bound[2], "[unknown]"):
                    interface_name = bound[2]
                    signature = (("global", "uint"), ("version", "uint"), ("bound", "object:" + interface_name))
                    arguments = [bound[1], bound[3], "new id " + interface_name + '@' + bound[5]]
                else:
                    self.counts["protocol_dropped"] += 1
                    return None
            else:
                signature = SIGNATURES.get((interface, method))
                arguments = split_arguments(argument_text)
            if signature is None or arguments is None or len(signature) != len(arguments):
                self.counts["protocol_dropped"] += 1
                return None
            values = {}
            for (name, kind), argument in zip(signature, arguments):
                value = typed_value(argument, kind)
                if value is None:
                    self.counts["protocol_dropped"] += 1
                    return None
                # Keyboard pressed-key array is never serialized, even its size.
                if kind != "array":
                    values[name] = value
            if (interface, method) in (("org_kde_plasma_window", "app_id_changed"), ("xdg_toplevel", "set_app_id")):
                app_id = argument_text[1:-1] if argument_text.startswith('"') and argument_text.endswith('"') else ""
                values["app_id"] = app_id if app_id in SYNTHETIC_APP_IDS else "[redacted]"
            if (interface, method) == ("wl_output", "name"):
                output_name = re.fullmatch(r'"(Virtual-[0-9]{1,10})"', argument_text)
                values["name"] = output_name[1] if output_name else "[redacted]"
            identifier = int(match.group("identifier"))
            if identifier > 4294967295:
                self.counts["protocol_dropped"] += 1
                return None
            object_ref = self.object_ref(interface, identifier)
            # Registry/callback IDs can overlap between Qt and FakePointer's
            # separate displays; the text cannot disambiguate those objects.
            connection = "unresolved" if interface in ("wl_registry", "wl_callback") else "fake-input-only" if interface == "org_kde_kwin_fake_input" else "qt-native-inferred"
            record = {"kind": "native", "seq": self.sequence, "time_ms": timestamp_milliseconds(match), "time_format": "clock_hms_us" if match.group("clock") else "legacy_ms", "direction": "request" if match.group("direction") else "event", "object": object_ref, "method": method, "values": values, "connection": connection}
            for (name, kind), argument in zip(signature, arguments):
                if kind.startswith("object:") and values[name]["id"]:
                    child = values[name]
                    created = argument.startswith("new id ")
                    values[name] = self.object_ref(child["interface"], child["id"], created, {"interface": interface, "id": identifier, "generation": object_ref["generation"]} if created else None)
            if method == "destroy":
                self.objects.pop((interface, identifier), None)
            if len(self.native) == self.native.maxlen:
                self.counts["native_ring_evictions"] += 1
            self.native.append(record)
            if (interface, method) in LINEAGE_METHODS or (
                interface == "wl_registry" and method == "bind"
                and values["bound"]["interface"] == "wl_output"
            ):
                # Preserve bootstrap identity even when later event traffic
                # evicts its constructor from the rolling native window.
                if len(self.lineage) < MAX_LINEAGE_FACTS:
                    self.lineage.append(record)
                    self.counts["lineage_facts_retained"] += 1
                else:
                    self.counts["lineage_facts_omitted"] += 1
            self.native_counts[interface + '.' + method] += 1
            if interface == "org_kde_kwin_fake_input" and method == "button" and self.first_fake_button_seq is None:
                self.first_fake_button_seq = self.sequence
            elif self.first_fake_button_seq is not None and interface in ("wl_keyboard", "wl_pointer"):
                self.after_gesture_counts[interface + '.' + method] += 1
            self.counts["native_retained"] += 1
            return None
        # Unknown prefixes and malformed protocol are not salvaged by substring.
        record = sanitize_diagnostic(line)
        if record is None:
            self.counts["nonallowlisted_dropped"] += 1
            return None
        record["seq"] = self.sequence
        if len(self.diagnostics) == self.diagnostics.maxlen:
            self.counts["diagnostic_ring_evictions"] += 1
        self.diagnostics.append(record)
        self.counts["diagnostic_retained"] += 1
        return record


class LineDrain:
    def __init__(self, sanitizer, stream):
        self.sanitizer = sanitizer
        self.stream = stream
        self.buffer = bytearray()
        self.discarding = False

    def feed(self, data, final=False):
        self.sanitizer.counts[self.stream + "_bytes"] += len(data)
        for piece in data.splitlines(keepends=True):
            # Only LF delimits messages; CR and other controls remain untrusted.
            ended = piece.endswith(b'\n')
            if not self.discarding:
                if len(self.buffer) + len(piece) > MAX_LINE_BYTES:
                    self.buffer.clear()
                    self.discarding = True
                    self.sanitizer.counts["oversized_lines_dropped"] += 1
                else:
                    self.buffer.extend(piece)
            if ended:
                if not self.discarding:
                    self.flush()
                self.discarding = False
        if final and self.buffer:
            self.flush()

    def flush(self):
        line = self.buffer.decode("utf-8", errors="replace").rstrip('\n')
        self.buffer.clear()
        record = self.sanitizer.sanitize_line(line, self.stream)
        if record is not None and not self.sanitizer.counts["output_pipe_closed"]:
            try:
                sys.stdout.write(json.dumps(record, sort_keys=True) + '\n')
                sys.stdout.flush()
            except BrokenPipeError:
                # Still drain both child streams and preserve its result.
                self.sanitizer.counts["output_pipe_closed"] += 1
                descriptor = os.open(os.devnull, os.O_WRONLY)
                try:
                    os.dup2(descriptor, sys.stdout.fileno())
                    sys.stdout.flush()
                finally:
                    os.close(descriptor)


def write_json(path, value):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, 'w', encoding='utf-8') as output:
        json.dump(value, output, sort_keys=True, indent=2)
        output.write('\n')


def run(mode, output, command):
    sanitizer = TraceSanitizer(mode)
    environment = os.environ.copy()
    environment.pop("WAYLAND_DEBUG", None)
    if mode == "on":
        environment["WAYLAND_DEBUG"] = "client"
    returncode = 125
    launch_errno = None
    supervisor_error = False
    child = None
    previous_handlers = {}
    interrupted = 0
    forwarded_signal_count = 0
    last_forwarded_signal = 0
    cancellation_escalated = 0
    cancellation_deadline = None

    def signal_owned_group(signum):
        # poll() returning None leaves this child's PID reserved even if it
        # exits immediately afterward; never signal after reaping the leader.
        if child is None or child.poll() is not None:
            return False
        try:
            os.killpg(child.pid, signum)
        except ProcessLookupError:
            return False
        return True

    try:
        # A separate process group includes shell foreground children without
        # changing the inherited login/session identity used by this fixture.
        child = subprocess.Popen(command, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, process_group=0)

        def forward_signal(signum, _frame):
            nonlocal interrupted, forwarded_signal_count, last_forwarded_signal
            nonlocal cancellation_deadline
            interrupted = 1
            if cancellation_deadline is None:
                cancellation_deadline = time.monotonic() + CANCELLATION_GRACE_SECONDS
            if signal_owned_group(signum):
                forwarded_signal_count += 1
                last_forwarded_signal = signum

        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP, signal.SIGQUIT):
            previous_handlers[signum] = signal.signal(signum, forward_signal)
        with selectors.DefaultSelector() as selector:
            for stream in ("stdout", "stderr"):
                pipe = getattr(child, stream)
                os.set_blocking(pipe.fileno(), False)
                selector.register(pipe, selectors.EVENT_READ, LineDrain(sanitizer, stream))
            exit_deadline = None
            while selector.get_map() or child.poll() is None:
                if (
                    cancellation_deadline is not None
                    and not cancellation_escalated
                    and time.monotonic() >= cancellation_deadline
                ):
                    if signal_owned_group(signal.SIGKILL):
                        cancellation_escalated = 1
                if child.poll() is not None:
                    if exit_deadline is None:
                        exit_deadline = time.monotonic() + POST_EXIT_DRAIN_SECONDS
                    if time.monotonic() >= exit_deadline:
                        sanitizer.counts["post_exit_pipe_cutoffs"] += len(selector.get_map())
                        for pending in list(selector.get_map().values()):
                            pending.data.feed(b"", final=True)
                            selector.unregister(pending.fileobj)
                            pending.fileobj.close()
                        break
                for key, _events in selector.select(timeout=0.1):
                    try:
                        data = os.read(key.fd, 65536)
                    except (InterruptedError, BlockingIOError):
                        continue
                    key.data.feed(data, final=not data)
                    if not data:
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
        returncode = child.wait()
    except OSError as error:
        if child is None:
            launch_errno = error.errno
            returncode = 127 if error.errno == errno.ENOENT else 126
        else:
            supervisor_error = True
    except Exception:
        # Exception text can include raw input, arguments, or environment data.
        supervisor_error = True
    finally:
        if child is not None:
            signal_owned_group(signal.SIGKILL)
            child.wait()
            child.stdout.close()
            child.stderr.close()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
    summary = {
        "schema_version": 1, "mode": mode, "returncode": returncode,
        "exit_code": returncode if returncode >= 0 else None,
        "signal": -returncode if returncode < 0 else None,
        "launch_errno": launch_errno, "supervisor_error": supervisor_error,
        "interrupted": interrupted,
        "forwarded_signal_count": forwarded_signal_count,
        "last_forwarded_signal": last_forwarded_signal,
        "cancellation_escalated": cancellation_escalated,
        "sanitizer_counts": dict(sanitizer.counts),
        "native_event_counts": dict(sanitizer.native_counts),
        "first_fake_input_button_seq": sanitizer.first_fake_button_seq,
        "native_events_after_first_fake_input_button": dict(sanitizer.after_gesture_counts),
        "retained_native_events": len(sanitizer.native),
        "retained_diagnostics": len(sanitizer.diagnostics),
        "retained_lineage_facts": len(sanitizer.lineage),
        "limits": {"line_bytes": MAX_LINE_BYTES, "native_events": MAX_NATIVE_EVENTS, "diagnostic_events": MAX_DIAGNOSTIC_EVENTS, "lineage_facts": MAX_LINEAGE_FACTS, "objects": MAX_OBJECTS, "post_exit_drain_seconds": POST_EXIT_DRAIN_SECONDS},
        "lineage_limit": "No universal display identity in debug text; native connection inferred from fixture ownership. Creation generations are observation-local; missing creation is explicit.",
    }
    write_json(str(output) + '.summary.json', summary)
    if returncode != 0:
        records_by_sequence = {record["seq"]: record for records in (sanitizer.lineage, sanitizer.native, sanitizer.diagnostics) for record in records}
        records = sorted(records_by_sequence.values(), key=lambda record: record["seq"])
        write_json(str(output) + '.trace.log', records)
    return returncode


class SafeArgumentParser(argparse.ArgumentParser):
    def error(self, _message):
        self.exit(2, "focus trace received invalid arguments\n")


def main():
    parser = SafeArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('off', 'on'), required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    # argparse errors can echo arbitrary command arguments; never print them.
    try:
        arguments = parser.parse_args()
    except SystemExit as error:
        return error.code
    command = arguments.command
    if command and command[0] == '--':
        command = command[1:]
    if not command or not arguments.output.is_absolute():
        sys.stdout.write('focus trace requires an absolute output prefix and a command\n')
        return 2
    try:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        returncode = run(arguments.mode, arguments.output, command)
    except OSError:
        sys.stdout.write('focus trace could not write diagnostic artifacts\n')
        return 125
    if returncode < 0:
        signum = -returncode
        # Preserve the signal without producing a core containing input buffers.
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if signum != signal.SIGKILL:
            signal.signal(signum, signal.SIG_DFL)
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signum})
        os.kill(os.getpid(), signum)
        return 128 + signum
    return returncode


if __name__ == '__main__':
    sys.exit(main())
