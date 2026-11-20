#!/usr/bin/env python3
"""Run by the launcher under both additive seccomp and genuine Landrun."""
import errno
import os
from pathlib import Path
import socket
import sys

protected = Path(sys.argv[1])
writable = Path(sys.argv[2])
assert protected.read_text() == "protected\n"
for operation in (lambda: protected.write_text("changed"), lambda: protected.unlink()):
    try:
        operation()
    except OSError as error:
        assert error.errno in (errno.EACCES, errno.EPERM), error
    else:
        raise AssertionError("Landrun permitted modifying protected source")
assert protected.read_text() == "protected\n"
writable.write_text("allowed\n")
assert writable.read_text() == "allowed\n"
writable.unlink()
for family in (socket.AF_UNIX, socket.AF_INET, socket.AF_INET6):
    try:
        socket.socket(family, socket.SOCK_STREAM)
    except OSError as error:
        assert error.errno == errno.EPERM, error
    else:
        raise AssertionError(f"Socket creation was allowed: {family}")
try:
    socket.socketpair()
except OSError as error:
    assert error.errno == errno.EPERM, error
else:
    raise AssertionError("Socketpair creation was allowed")
print("Sandbox probes passed: protected writes denied; permitted writes work; socket creation denied.")
