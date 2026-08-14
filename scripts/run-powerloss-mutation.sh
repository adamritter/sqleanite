#!/bin/sh
# Build the held-out missing-journal-sync mutation in an isolated worktree and
# require the power-loss harness to distinguish it from stock SQLite.
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
rounds=${1:-20}
jobs=${JOBS:-2}
work=$(mktemp -d)
checkout=$work/sqlite-mutant
cleanup() {
  if [ -d "$checkout" ]; then
    git worktree remove --force "$checkout" >/dev/null 2>&1 || true
  fi
  rm -r -- "$work"
}
trap cleanup EXIT HUP INT TERM

git worktree add --detach "$checkout" HEAD >/dev/null
git -C "$checkout" apply "$root/mutations/c-unvalidated/c-p4-skip-journal-sync.patch"
make -C "$checkout" -f Makefile.linux-generic -j"$jobs" sqlite3 \
  SHELL_OPT= LDFLAGS.readline= >/dev/null

set +e
scripts/run-powerloss-injection.sh "$checkout/sqlite3" "$rounds"
status=$?
set -e

if [ "$status" -eq 0 ]; then
  printf 'UNDETECTED: c-p4-skip-journal-sync survived %s power-loss rounds\n' \
    "$rounds" >&2
  exit 1
fi

printf 'DETECTED: c-p4-skip-journal-sync produced a torn commit\n'
