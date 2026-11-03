#!/usr/bin/env python3
"""storefull.py: a store on a disk that has no room.

The store is on a small file system of its own (a tmpfs, mounted with sudo; on Windows NTFS
in a virtual disk, attached by an administrator), and a file next to it takes up all but so many bytes, so that the daemon runs out of room at another place
each time: before it can say which format the store is of, when it opens its pack, in the
middle of the records, and when it seals. Each time:

  - the daemon has to build a program that prints what cargo's does, on its first build and
    after an edit;
  - it has to say that it keeps nothing, and why;
  - `rustd cache verify` has to find nothing in the store that is not what was written.

Then room is made under a running daemon, and what the next daemon compiles has to be kept
again. `rustd cache pull` into the full store has to fail with the reason and leave no part
of a pack behind, and `rustd cache gc` has to make room.

    python3 storefull.py
"""
import errno, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from storelib import Checkout, Daemon, cache, files, scratch, stats, verify

WINDOWS = os.name == "nt"
# NTFS keeps a log and a file table of its own, which do not fit in the 8 MB a tmpfs can be.
SIZE = (64 if WINDOWS else 8) << 20
# How much room the store has, in bytes, capped below what a cold build writes.
ROOMS = [0, 4096, 16 << 10, 128 << 10, 512 << 10]
SEALS = {"RUSTD_CACHE_SEAL_AT": "1", "RUSTD_CACHE_MAX": "off"}
NO_ROOM = "There is not enough space on the disk" if WINDOWS else "No space left on device"


def fail(what):
    raise SystemExit(f"FAIL: {what}")


class Disk:
    """A file system of SIZE bytes with the store in it."""

    def __init__(self, work):
        self.at = os.path.join(work, "disk")
        os.mkdir(self.at)
        self.image = os.path.join(work, "disk.vhd")
        if WINDOWS:
            self.diskpart(f'create vdisk file="{self.image}" maximum={SIZE >> 20} type=fixed', "attach vdisk",
                          "create partition primary", "format fs=ntfs quick unit=4096", f'assign mount="{self.at}"')
        else:
            self.mount()
        self.store, self.ballast = os.path.join(self.at, "store"), os.path.join(self.at, "ballast")

    def empty_store(self):
        """The store's directory, empty and the user's alone. A volume just formatted lets
        every user of a Windows machine write to what is made at its top, and rustd takes
        no store that others can write to."""
        shutil.rmtree(self.store, ignore_errors=True)
        os.mkdir(self.store)
        if WINDOWS:
            mine = f'{os.environ["USERNAME"]}:(OI)(CI)F'
            subprocess.run(["icacls", self.store, "/inheritance:r", "/grant:r", mine], check=True, capture_output=True)

    def mount(self):
        options = f"size={SIZE},uid={os.getuid()},gid={os.getgid()},mode=700"
        mounted = subprocess.run(["sudo", "-n", "mount", "-t", "tmpfs", "-o", options, "tmpfs", self.at],
                                 capture_output=True, text=True)
        if mounted.returncode != 0:
            fail(f"a small file system could not be mounted (sudo is needed): {mounted.stderr.strip()}")

    def diskpart(self, *script):
        ran = subprocess.run(["diskpart"], input="".join(line + chr(10) for line in script), capture_output=True, text=True)
        if ran.returncode != 0:
            fail(f"a small file system could not be attached (an administrator is needed): {ran.stdout[-600:]}")

    def free(self):
        return shutil.disk_usage(self.at).free

    def leave(self, room):
        """Takes up all of the disk but `room` bytes, to the block."""
        if os.path.exists(self.ballast):
            os.remove(self.ballast)
        take = self.free() - room
        if take < 0:
            fail(f"the disk has {self.free()} bytes free, fewer than {room}")
        # NTFS takes room of its own for a file this long, so the last blocks may not fit.
        chunk = 1 << 20
        with open(self.ballast, "wb", buffering=0) as ballast:
            while take:
                size = min(chunk, take)
                try:
                    ballast.write(bytes(size))
                except OSError as full:
                    if full.errno != errno.ENOSPC:
                        raise
                    if chunk == 4096:
                        break
                    chunk = 4096
                    continue
                take -= size
        return self.free()

    def unmount(self):
        if WINDOWS:
            return self.diskpart(f'select vdisk file="{self.image}"', "detach vdisk")
        subprocess.run(["sudo", "-n", "umount", self.at], capture_output=True)


def cold(checkout, disk):
    """The bytes and records a cold build writes to a store with room."""
    disk.empty_store()
    if os.path.exists(disk.ballast):
        os.remove(disk.ballast)
    daemon = Daemon(checkout, disk.store, name="cold", env=SEALS)
    checkout.check(daemon, "with room, to measure")
    daemon.kill()
    whole, numbers, out = verify(disk.store)
    if not whole or not numbers.get("records"):
        fail(f"the cold store did not keep valid records: {out}")
    size = sum(os.path.getsize(os.path.join(disk.store, name)) for name in os.listdir(disk.store))
    return size, numbers["records"]


def built_without(checkout, disk, room):
    """A daemon on a store with `room` bytes builds, and says what it could not keep."""
    disk.empty_store()
    left = disk.leave(room)
    checkout.set(room % 7)
    daemon = Daemon(checkout, disk.store, name=f"room{room}", env=SEALS)
    checkout.check(daemon, f"{room} bytes of room, the first build")
    checkout.set(room % 7 + 1)
    checkout.check(daemon, f"{room} bytes of room, after an edit")
    log = daemon.log()
    daemon.kill()
    said = [line for line in log.splitlines() if line.startswith("store:") and NO_ROOM in line]
    if not said:
        fail(f"{room} bytes of room: the daemon does not say the disk is full: {daemon.log_path}")
    if "panicked" in log:
        fail(f"{room} bytes of room: the daemon panicked: {daemon.log_path}")
    whole, numbers, out = verify(disk.store)
    if not whole:
        fail(f"{room} bytes of room: the store does not verify\n{out}")
    if files(disk.store, ".tmp"):
        fail(f"{room} bytes of room: a part of a file was left: {files(disk.store, '.tmp')}")
    not_used = any("store: not used" in line for line in said)
    print(f"  {left:>8} bytes free: built; {'store not used' if not_used else 'nothing more kept'}; "
          f"{numbers.get('packs', 0)} packs, {numbers.get('open packs', 0)} open in the store")
    return not_used


def kept_again(checkout, disk, expected, room):
    """Room is made while a daemon runs; the next build that writes the store keeps what it compiles."""
    disk.empty_store()
    disk.leave(room)
    checkout.set(11)
    daemon = Daemon(checkout, disk.store, name="again", env=SEALS)
    checkout.check(daemon, "before room is made")
    if NO_ROOM not in daemon.log():
        fail(f"the disk was not full before room was made: {daemon.log_path}")
    os.remove(disk.ballast)
    daemon.kill()
    daemon = Daemon(checkout, disk.store, name="again", env=SEALS)
    checkout.check(daemon, "after room was made")
    log = daemon.log()
    daemon.kill()
    whole, numbers, out = verify(disk.store)
    if NO_ROOM in log or not whole or numbers["records"] < expected:
        fail(f"with room again the daemon did not keep what it compiled: {daemon.log_path}\n{out}")
    daemon = Daemon(checkout, disk.store, name="again", env=SEALS)
    checkout.check(daemon, "from the store that was full")
    log = daemon.log()
    daemon.kill()
    if "store: 0 functions found" in log or "functions found" not in log:
        fail(f"nothing was found in the store that was full: {daemon.log_path}")
    print(f"  room made: {numbers['packs']} packs with {numbers['records']} records kept, and found by the next daemon")


# The remote is a directory of this user's, whose lists nobody signs.
UNSIGNED = {"RUSTD_REMOTE_UNSIGNED": "1"}


def commands(checkout, disk, work):
    """`rustd cache` on a full disk: pull fails cleanly, gc makes room."""
    remote = os.path.join(work, "remote")
    status, out = cache(disk.store, "push", remote)
    if status != 0:
        fail(f"push: {out}")
    packs = len(files(disk.store, ".pack"))
    status, out = cache(disk.store, "gc", "--max", "0")
    if status != 0 or files(disk.store, ".pack"):
        fail(f"gc --max 0: {out}")
    status, out = cache(disk.store, "pull", remote, env={"RUSTD_REMOTE_UNSIGNED": ""})
    if status == 0 or "RUSTD_REMOTE_UNSIGNED=1" not in out or files(disk.store, ".pack"):
        fail(f"pull from lists nobody signed was not refused: {out}")
    disk.leave(64 << 10)
    status, out = cache(disk.store, "pull", remote, env=UNSIGNED)
    if status == 0 or NO_ROOM not in out:
        fail(f"pull into a full store did not fail with the reason: {out}")
    whole, _, verified = verify(disk.store)
    if not whole or files(disk.store, ".tmp"):
        fail(f"pull into a full store left something behind: {os.listdir(disk.store)}\n{verified}")
    os.remove(disk.ballast)
    status, out = cache(disk.store, "pull", remote, env=UNSIGNED)
    whole, numbers, verified = verify(disk.store)
    if status != 0 or not whole or numbers["packs"] != packs:
        fail(f"pull with room: {out}\n{verified}")
    # A full disk with a store on it: collecting has to work with no room at all.
    disk.leave(0)
    status, out = cache(disk.store, "gc", "--max", "100K")
    after = stats(disk.store)
    if status != 0 or after["pack bytes"] > 100 << 10:
        fail(f"gc on a full disk: {out}")
    print(f"  commands: pull into a full store refused ({NO_ROOM}), nothing left behind; "
          f"pull with room fetched {packs} packs; gc on a full disk left {after['pack bytes']} bytes")


def main():
    start = time.time()
    work = scratch("rustd-storefull-")
    checkout = Checkout(work)
    disk = Disk(work)
    try:
        size, records = cold(checkout, disk)
        print(f"cold store: {size} bytes, {records} records")
        limit = size * 2 // 3
        rooms = sorted({min(room, limit) for room in ROOMS} | {limit})
        not_used = sum(built_without(checkout, disk, room) for room in rooms)
        kept_again(checkout, disk, records, min(128 << 10, limit))
        commands(checkout, disk, work)
    finally:
        disk.unmount()
    shutil.rmtree(work, ignore_errors=True)
    print(f"PASS: {len(rooms)} full disks built without a store or without the rest of it "
          f"({not_used} could not open it at all), in {time.time() - start:.0f}s")


if __name__ == "__main__":
    main()
